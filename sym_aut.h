//
// Created by philipp on 24/07/23.
//

#pragma once

#include <algorithm>

#include "twa/twagraph.hh"
#include "twaalgos/synthesis.hh"

#include "misc/bddlt.hh"

#include "utils.h"

using namespace spot;


/**
 * Structure containing the definition of the symbolic automaton
 * \note For simplicity, state are encoded in binary over the
 * fresh propositions.
 * It is assumed that states are "gap free and left aligned".
 * That is if there are N states, they correspond to the
 * explicit numbers [0,...,N-1].
 * The fresh proposition are currently named and stored in orig_aut.
 * This is not how it should be done, but it is good enough for a
 * demonstrations.
 */
struct sym_aut{
  bdd T = bddfalse; // Transition system (X', X, AP)
  bdd F = bddfalse; // Final states (X)
  bdd S = bddfalse; // All states (X)
  bdd I = bddfalse; // Initial state (X)
  bdd X = bddfalse; // All X vars
  bdd Xp = bddfalse; // All X' vars
  bdd P = bddfalse; // All AP
  std::unique_ptr<bddPair> X2Xp; // Replace X by X'
  std::unique_ptr<bddPair> Xp2X; // Replace X' by X
  std::vector<std::array<bdd, 2>> Xvec; // echo ~x, x in X
  std::vector<std::array<bdd, 2>> Xpvec; // echo ~x, x in X
  // Hack: ptr to the orig aut for var creation
  twa_graph_ptr aut_orig;

  // Game stuff (Reachability game!)
  bdd W = bddfalse; // Overall winning region
  std::vector<bdd> Attr; // Abstraction of an attractor
  bdd in = bddfalse; // Propositions considered as input
  bdd out = bddfalse; // Propositions considered as output
  // Attr[0] is F (Not false, but the final states
  // Attr[i+1] = cpre(W_i] \ W_i
  // These are the "freshly" attracted states (Makes it easier to extract a strategy

  /**
   * \brief Setup \a Nvars new propositions with basename \a base
   * @param Nvars Number of propositions
   * @param base propositions name is {base}XX
   */
  void setup(const unsigned Nvars, const std::string& base){
    const std::string basep = base + 'p';

    X = bddtrue;
    Xp = bddtrue;
    T = bddfalse;
    F = bddfalse;
    S = bddfalse;
    P = aut_orig->ap_vars();
    X2Xp.reset(bdd_newpair());
    Xp2X.reset(bdd_newpair());

    Xvec = std::vector<std::array<bdd, 2>>(Nvars);
    Xpvec = std::vector<std::array<bdd, 2>>(Nvars);

    for (unsigned i = 0; i < Nvars; ++i){
      auto xi = aut_orig->register_ap(base+std::to_string(i));
      auto xpi = aut_orig->register_ap(basep+std::to_string(i));
      auto x = bdd_ithvar(xi);
      auto xp = bdd_ithvar(xpi);
      Xvec[i] = {bdd_not(x), x};
      Xpvec[i] = {bdd_not(xp), xp};

      X &= x;
      Xp &= xp;

      bdd_setpair(X2Xp.get(), xi, xpi);
      bdd_setpair(Xp2X.get(), xpi, xi);
    }
  }

  /**
   * \brief Encode the state in binary over X or X'
   * (depending on \a useX)
   * @param s state number to encode
   * @param useX Whether to encode over X or X'
   * @return
   */
  inline bdd
  encode_state(unsigned s, bool useX = true) const {
    const unsigned Nvars = Xvec.size();

    const auto& XvecR = useX ? Xvec : Xpvec;

    unsigned idx = 0;
    bdd ret = bddtrue;

    for (; s; ++idx){
      ret &= Xvec[idx][s&1u];
      s >>= 1;
    }

    assert(idx <= Nvars);

    for (; idx < Nvars; ++idx)
      ret &= Xvec[idx][0];
    return ret;
  };

  /**
   * \brief Translate the symbolic automata into
   * an explicit (semi-symbolic) automaton
   * @return The corresponding automaton and possibly the associated split version
   */
  std::pair<twa_graph_ptr, twa_graph_ptr>
  to_explicit() const {
    auto aut = make_twa_graph(aut_orig->get_dict());
    aut->copy_ap_of(aut_orig);
    aut->copy_acceptance_of(aut_orig);
    aut->prop_state_acc(true);
    assert(aut_orig->is_sba());

    // Assume and make the automaton "left aligned"
    // We do this as it significantly simply checking
    // the automaton by hand
    std::vector<std::array<bdd, 2>> statevec;
    statevec.reserve(std::pow(2, Xvec.size()));
    unsigned init_state = -1u;

    {
      for (unsigned s = 0; ; ++s){
        bdd sx = encode_state(s);
        if (bdd_implies(sx, S) != 1)
          break; // This is only correct when left aligned.
        statevec.push_back({sx, bdd_replace(sx, X2Xp.get())});
        if (bdd_implies(sx, I)) {
          assert(init_state == -1u);
          init_state = s;
        }
      }
      assert(init_state != -1u);
      aut->new_states(statevec.size());
      aut->set_init_state(init_state);
    }

    auto XXp = X & Xp;
    const unsigned Nstates = aut->num_states();
    for (unsigned src = 0; src < Nstates; ++src){
      for (unsigned dst = 0; dst < Nstates; ++dst){
        bdd cond = bdd_restrict(T, statevec[src][0]&statevec[dst][1]);
        if (cond == bddfalse)
          continue;
        if (bdd_implies(statevec[src][0], F))
          aut->new_edge(src, dst, cond, {0});
        else
          aut->new_edge(src, dst, cond);
      }
    }

    twa_graph_ptr auts = nullptr;

    if (in != bddfalse){
      auto get_lvl = [&](const bdd& x){
        const unsigned N = Attr.size();
        for (unsigned idx = 0; idx < N; ++idx){
          if (bdd_implies(x, Attr[idx]))
            return idx;
        }
        throw std::runtime_error("State not attracted!");
      };
      // If there are inputs, we assume that the game was solved
      // The strategy is currently only output to cout
      // For simplicity the, the strategy is output
      // for the explicit aut
      // Loop over states
      auts = split_2step(aut, out, false);

      auto& win = *auts->get_or_set_named_prop<std::vector<bool>>("state-winner");
      win.resize(auts->num_states(), false);
      auto& strat = *auts->get_or_set_named_prop<std::vector<unsigned>>("strategy");
      strat.resize(auts->num_states(), -1u);

      // The new aut is first env states, then player states
      for (unsigned esrc = 0; esrc < Nstates; ++esrc){
        const bdd& exsrc = statevec[esrc][0];

        // Actually get a strategy
        if (bdd_implies(exsrc, W)){
          win[esrc] = true;
          // Get the attr lvl of esrc
          unsigned esrc_lvl = get_lvl(exsrc);
          if (esrc_lvl == 0){
            my_out << "State " << esrc << " : " << exsrc << " is in F\n";
            continue;
          }
          // The successors are the player states
          for (const auto& env_edge : auts->out(esrc)){
            // Now the player
            // Build a list of possible (successors, successor_lvl)
            win[env_edge.dst] = true;
            std::vector<std::array<unsigned, 2>> succ;
            for (const auto& ply_edge : auts->out(env_edge.dst)){
              assert(ply_edge.dst < Nstates);
              if (bdd_implies(statevec[ply_edge.dst][0], W))
                succ.push_back({auts->edge_number(ply_edge), get_lvl(statevec[ply_edge.dst][0])});
            }
            // We have found all possible successors -> Go the deepest
            std::sort(succ.begin(), succ.end(),
                      [](const auto& l, const auto& r){
              return l[1] <= r[1];
            });
            // Verify that valid
            assert(succ[0][1] < esrc_lvl);
            // Set strategy
            strat[env_edge.dst] = succ[0][0];
          }
        } else {
          my_out << "Player does not win " << esrc << " : " << exsrc << '\n';
        }
      }
    }
    highlight_strategy(auts);

    return {aut, auts};
  }

  /**
   * \brief Convert an explicit (semi-symbolic) automaton into
   * a (fully) symbolic one
   * @param g The automaton to convert
   * @param base Basename for the fresh variables
   * @return The corresponding symbolic one
   */
  static sym_aut
  to_symbolic(const twa_graph_ptr& g, const std::string& base){
    const unsigned Nstates = g->num_states();
    const unsigned Nvars = nbits(Nstates);

    my_out << Nvars << " variables used for " << Nstates << " states.\n";

    auto sy = sym_aut();
    sy.aut_orig = g;

    // Setup
    sy.setup(Nvars, base);

    auto s2X = std::vector<std::array<bdd,2>>(Nstates);

    for (unsigned s = 0; s < Nstates; ++s){
      auto x = sy.encode_state(s);
      auto xp = bdd_replace(x, sy.X2Xp.get());
      s2X[s] = {x,xp};
      sy.S |= x;
      if (g->state_is_accepting(s))
        sy.F |= x;
    }
    sy.I = s2X[g->get_init_state_number()][0];

    // Encode the transitions

    for (const auto& e : g->edges()){
      const auto& sx = s2X[e.src][0];
      const auto& dxp = s2X[e.dst][1];
      auto c = e.cond & sx & dxp;
      my_out << e.src << ' ' << e.cond << ' ' << e.dst << ": " << c << '\n';
      sy.T |= c;
    }

    return sy;
  }


  friend std::ostream& operator<<(std::ostream& os, const sym_aut& sa){
    os << "All states:\n " << sa.S << '\n'
       << "Initial state:\n " << sa.I << '\n'
       << "Final states:\n " << sa.F << '\n'
       << "Transitions:\n " << sa.T << '\n'
       << "All X:\n " << sa.X << '\n'
       << "All X prime:\n " << sa.Xp << '\n'
       << "All AP:\n " << sa.P << '\n';
    if (sa.in != bddfalse){
      os << "The automaton represents a game.\n Input is:\n" << sa.in << "\nOutput is:\n" << sa.out << '\n'
         << "The overall winning region is:\n" << sa.W
         << "The attractor layers are:\n";
      unsigned lvl = 0;
      for (const auto& attri : sa.Attr)
        os << "layer " << lvl++ << '\n' << attri << '\n';
    }
    return os;
  }
};