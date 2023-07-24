//
// Created by philipp on 24/07/23.
//

#include "twaalgos/product.hh"

#include "sym_aut_algos.h"

using namespace spot;

bool
dfa_contains(const twa_graph_ptr& left, const twa_graph_ptr& right){
  auto right_compl = make_twa_graph(right, twa::prop_set::all());
  right_compl->copy_acceptance_of(right);
  right_compl->copy_ap_of(right);

  for (auto& e : right_compl->edges()){
    if (e.acc)
      e.acc = {};
    else
      e.acc = {0};
  }
  //print_hoa(std::cout, right_compl);
  //my_out << '\n';
  auto p = product(left, right_compl);
  //print_hoa(std::cout, p);

  const auto N = p->num_states();
  const auto& pn = *(p->get_named_prop<std::vector<std::pair<unsigned, unsigned>>>("product-states"));
  for (unsigned s = 0; s < N; ++s){
    if (p->state_is_accepting(s)){
      std::cerr << "Failed for (" << pn[s].first << ' ' << pn[s].second << ")\n";
      return false;
    }
  }
  return true;
}

sym_aut
signature_min(const sym_aut& sy, const std::string& base){

  // The keys (bdd) represent the current signatures
  // Each signature represents an equivalent class
  // for the next iteration
  auto equiv_classes = std::unordered_map<bdd, unsigned, bdd_hash>();

  // Helper functions to structure
  auto get_class = [&equiv_classes](const bdd& c) -> unsigned {
    auto [it, ins] = equiv_classes.insert(std::make_pair(c, (unsigned) equiv_classes.size()));
    if (ins)
      my_out << "New sig " << it->second << " : " << it->first << '\n';
    return it->second;
  };
  auto reset_class = [&equiv_classes](){
    equiv_classes.clear();
  };

  // The new, minimized automaton
  // If the initial automaton is already minimal,
  // the states might still be relabeled/reordered
  auto res = sym_aut();
  res.aut_orig = sy.aut_orig;
  // We can not have more -> keep the same number of AP so we are safe
  const unsigned NvarsNew = sy.Xvec.size();

  res.setup(NvarsNew, base);
  res.T = bddfalse;

  auto cidx2C = std::vector<std::array<bdd,2>>(std::pow(2, NvarsNew));

  for (unsigned cidx = 0; cidx < std::pow(2, NvarsNew); ++cidx){
    auto c = res.encode_state(cidx);
    auto cp = bdd_replace(c, res.X2Xp.get());
    cidx2C[cidx] = {c,cp};
    my_out << "cidx " << cidx << " : " << c << '\n';
  }

  // We start off with two classes
  get_class(cidx2C[0][0]); // S\F
  get_class(cidx2C[1][0]); // F
  // Note: This approach is correct
  // for reachability AND büchi games
  // Does not take into account that
  // sba representing LTLf formulas are terminal

  // This should be optimized
  // enumerate all states
  auto all_states = std::vector<std::array<bdd, 2>>();
  all_states.reserve(std::pow(2, NvarsNew));
  {
    for (unsigned sidx = 0; sidx < std::pow(2, NvarsNew); ++sidx){
      bdd xs = sy.encode_state(sidx);
      my_out << "xs " << xs << " : " << all_states.size() << '\n';
      if (bdd_implies(xs, sy.S) == 0){
        my_out << "Break at state " << sidx << '\n';
        break; // Again, this is only correct for left-aligned automata
      }
      all_states.push_back({xs, bdd_replace(xs, sy.X2Xp.get())});
    }
  }

  // This bdd encodes which states belongs to which class
  // That is, it is true iff the pair (x', c), where c is some index of a
  // class, the state x (x') has the signature implied by c
  // Note: currently we need to "manually" loop over all states
  // which is (I assume) one of the bottlenecks.
  // By using a better layout of the variables,
  // this step can be significantly improved.
  const unsigned Nstates = all_states.size();
  bdd Cp = bddfalse;
  for (unsigned xidx = 0; xidx < Nstates; ++xidx){
    Cp |= all_states[xidx][1] & (bdd_implies(all_states[xidx][0], sy.F) ? cidx2C[1][0] : cidx2C[0][0]);
  }
  my_out << "Initial Cp is " << Cp << '\n';

  // Associate to each state a class
  // Again, this can be avoided with better ordering
  auto sidx2Cidx = std::vector<unsigned>(Nstates, -1u);

  // Main iteration
  for (unsigned outerCounter = 0; ; ++outerCounter){
    my_out << "Starting iteration i\n";
    const unsigned NclassesStart = equiv_classes.size();
    reset_class();

    // F(x, l, c) is true iff we end up at a state of class c
    // after reading l starting in x
    bdd F = bdd_relprod(sy.T, Cp, sy.Xp); // Computes F(X, AP, Classes)
    my_out << "Current F is:\n" << F << '\n';
    // Compute the new signature for each state
    // (This is the most inefficient part that...)
    // The signature is the disjunction
    // over all pairs (letter, successor class)
    bdd Cpnew = bddfalse;
    for (unsigned sidx = 0; sidx < Nstates; ++sidx){
      const auto& xs = all_states[sidx][0];
      // Fix the value of the state
      bdd sigx = bdd_restrict(F, xs);
      auto cidx = get_class(sigx);
      Cpnew |= cidx2C[cidx][0] & all_states[sidx][1];
      sidx2Cidx[sidx] = cidx;
      my_out << "sidx " << sidx  << "\nxs\n" << xs << "\nsig is\n" << sigx << " new class is " << cidx << '\n';
    }
    // Update
    Cp = Cpnew;
    // We computed the new C and all classes
    // If we have the same number of classes / signatures
    // We reached a fix point
    if (equiv_classes.size() == NclassesStart)
      break; // Fixpoint
  }
  // todo: Only recompute signatures affected by the last changes.

  const unsigned NstatesNew = equiv_classes.size();

  // We found the classes
  // -> Now we need to build the minimal aut
  my_out << "Found " << NstatesNew << " equivalence classes.\n";

  res.F = bddfalse;
  res.I = bddfalse;
  res.S = bddfalse;
  res.T = bddfalse;

  // At this point
  // Cp(Xp, \C) is a function assigning to each state xp a class \C
  // But we need it to be in \Cp
  // so that we can construct transitions (c, l, cp)
  Cp = bdd_replace(Cp, res.X2Xp.get());
  my_out << "Final Cp is\n" << Cp << '\n';

  // We also need the unprimed version
  // C(X, \C) is a function assigning to each state X a class C
  // (The same as in the primed version)
  bdd C = bdd_replace(bdd_replace(Cp, sy.Xp2X.get()), res.Xp2X.get());
  my_out << "Final C is\n" << Cp << '\n';

  // Now we can compute the new transition system
  // by applying C and Cp, then quantifying away X and Xp
  res.T = bdd_relprod(sy.T, C & Cp, sy.X & sy.Xp);
  my_out << "New T is\n" << res.T << '\n';

  // Equally we can derive F, I and S from C
  res.S = bdd_exist(C, sy.X);
  res.F = bdd_relprod(C, sy.F, sy.X);
  res.I = bdd_relprod(C, sy.I, sy.X);

  // Copy game info
  res.in = sy.in;
  res.out = sy.out;

  my_out << "Final is resulting is\n" << res << '\n';

  return res;
}

// A more "symbolic" approach

// This does not work as expected, I have to think about it
/*

template<>
struct std::hash<std::array<unsigned, 2>> {
  std::size_t operator()(const std::array<unsigned,2>& a) const noexcept {
    unsigned long long h = a[0];
    h <<= 32;
    h += a[1];
    return std::hash<unsigned long long>()(h);
  }
};

sym_aut symbolic_min(const sym_aut& sy, const std::string& base){
  // Minimize a symbolic automaton,
  // all steps are done symbolically
  // Implements a symbolic approach of hopcrofts
  // equivalence class approach

  const std::string basep = base + 'p';

  // all equivalence classes in their normal and primed version
  // Initialized with S\F and F
  auto equiv_classes = std::vector<std::array<bdd, 2>>{{sy.S - sy.F, bdd_replace(sy.S - sy.F, sy.X2Xp.get())},
                                                       {sy.F, bdd_replace(sy.F, sy.X2Xp.get())}};
  my_out << "Base equiv classes are:\n" << equiv_classes[0][0] << '\n' << equiv_classes[1][0] << '\n';
  // The conditions from i2j
  auto cond_dict = std::unordered_map<std::array<unsigned, 2>, bdd>();

  auto get_cond_ij
    = [&cond_dict, &sy, &equiv_classes, XXP = sy.X & sy.Xp](unsigned i, unsigned j) -> bdd
    {
    auto [it, ins] = cond_dict.emplace(std::piecewise_construct,
                                       std::forward_as_tuple(std::array<unsigned, 2>{i, j}),
                                       std::forward_as_tuple(bddfalse));
    ins = true; // Always recompute TODO this is somehow buggy
    if (ins){
      // We actually need to compute the conditions
      auto condij = sy.T & equiv_classes[i][0] & equiv_classes[j][1];
      //my_out << i << ", " << j << ", cond:\n" << condij << '\n';
      condij = bdd_exist(condij, XXP);
      //my_out << "cond P:\n" << condij << '\n';
      it->second = condij;
    }
    else
      my_out << "cond P ext:\n" << it->second;

    return it->second;
  };

  auto free_cond_i
    = [&cond_dict](unsigned i) -> void
    {
      std::erase_if(cond_dict, [i](const auto& el) -> bool {return (el.first[0] == i)
                                                                                          || (el.first[1] == i); });
    };

  for (unsigned outerCounter = 1; ; ++outerCounter){
    my_out << "Iteration # " << outerCounter << '\n';
    const unsigned NclassesStart = equiv_classes.size();
    for (unsigned i = 0; i < NclassesStart; ++i){
      // I think one could optimise to only test against < equiv_classes.size()
      for (unsigned j = 0; j < NclassesStart; ++j){
        auto cond_ij = get_cond_ij(i, j);
        for (unsigned k = j + 1; k < NclassesStart; ++k){
          auto cond_ik = get_cond_ij(i, k);
          auto inter = cond_ij & cond_ik;
          if (inter == bddfalse)
            continue; // Nothing to do
          // Here we need to split
          // Class i gets the part leading to k substracted
          // This part will get its own class
          auto i2k = sy.T & equiv_classes[i][0] & equiv_classes[k][1] & inter;
          // Exist away all AP and Xp
          i2k = bdd_exist(i2k, sy.Xp & sy.P); // These are the unprimed X that go from I to K under inter
          if (true || i2k == equiv_classes[i][0]){
            my_out << "\nconds\n" << cond_ij << '\n' << cond_ik << '\n' << inter << std::endl;
            std::cerr << std::endl << "what?!" << std::endl;
            auto i2j = sy.T & equiv_classes[i][0] & equiv_classes[j][1] & inter;
            i2j = bdd_exist(i2j, sy.Xp & sy.P);
            std::cerr << std::endl << "i2j is:\n" << i2j << std::endl;
            std::cerr << std::endl << "i2j and i2k is:\n" << (i2k & i2j) << std::endl;
            std::cerr << std::endl << "blub:\n" << (sy.T & equiv_classes[i][0] & equiv_classes[j][1] & equiv_classes[k][1] & inter) << std::endl;
            std::cerr << std::endl << "blib:\n" << (sy.T & equiv_classes[i][0] & equiv_classes[j][1] & inter) << std::endl;
            std::cerr << std::endl << "blob:\n" << (sy.T & equiv_classes[i][0] & equiv_classes[k][1] & inter) << std::endl;
            std::cerr << std::endl << "inter2:\n" << bdd_exist((sy.T & equiv_classes[i][0] & (equiv_classes[j][1] | equiv_classes[k][1])), sy.X & sy.Xp) << std::endl;
          }

          my_out << "Current is " << i << ' ' << j << ' ' << k << '\n'
                    << "Found refine class\n" << i2k << "\nfor class\n"
                    << equiv_classes[i][0] << "\n with conditions\n"
                    << cond_ij << '\n' << cond_ik << '\n' << inter << '\n';
          // Update i
          equiv_classes[i][0] -= i2k;
          equiv_classes[i][1] = bdd_replace(equiv_classes[i][0], sy.X2Xp.get());
          // Add the new one
          equiv_classes.push_back({i2k, bdd_replace(i2k, sy.X2Xp.get())});
          // All conditions leaving / going to i might have become incorrect -> delete
          free_cond_i(i);
        }
      }
    }
    if (equiv_classes.size() == NclassesStart){
      my_out << "computation needed " << outerCounter << " iterations\n";
      break; // No changes to the partition
    }
  }

  // Setup the new automaton
  my_out << "Found " << equiv_classes.size() << " equivalence classes.\n";
  for (unsigned idx = 0; idx < equiv_classes.size(); ++idx)
    my_out << idx << ": " << equiv_classes[idx][0] << '\n';

  auto res = sym_aut();
  res.aut_orig = sy.aut_orig;

  const unsigned NstatesNew = equiv_classes.size();
  const unsigned NvarsNew = nbits(NstatesNew);

  res.setup(NvarsNew, "xm");
  res.T = bddfalse;

  auto encode_state= [&res, NvarsNew](unsigned s) -> bdd{
    return encode_state_(s, res.Xvec, NvarsNew);
  };

  auto s2X = std::vector<std::array<bdd,2>>(NstatesNew);

  for (unsigned s = 0; s < NstatesNew; ++s){
    auto x = encode_state(s);
    auto xp = bdd_replace(x, res.X2Xp.get());
    s2X[s] = {x,xp};
    res.S |= x;
  }

  // The final sets need to be subsets of the original ones
  // The initial ones could be dispersed, however usually we have a unique
  // initial state

  // Final states
  res.F = bddfalse;
  for (unsigned s = 0; s < NstatesNew; ++s){
    if (bdd_implies(equiv_classes[s][0], sy.F))
      res.F |= s2X[s][0];
    else
      assert((equiv_classes[s][0] & sy.F) == bddfalse);
  }
  // Initial
  res.I = bddfalse;
  for (unsigned s = 0; s < NstatesNew; ++s){
    if (bdd_implies(sy.I, equiv_classes[s][0])){
      assert(res.I == bddfalse);
      res.I |= s2X[s][0];
    }
    else
      assert((equiv_classes[s][0] & sy.I) == bddfalse);
  }

  // Add the transitions between each class
  res.T = bddfalse;
  for (unsigned i = 0; i < NstatesNew; ++i){
    const auto& xi = s2X[i][0];
    for (unsigned j = 0; j < NstatesNew; ++j) {
      const auto& xj = s2X[j][1];
      auto cond_ij = get_cond_ij(i, j);
      res.T |= xi & cond_ij & xj;
    }
  }

  return res;
}
*/


// Game algos

void
solve_reachability(sym_aut& sy){
  // Solves the reachability games and set the W and Attr field

  auto& attr = sy.Attr;
  auto& W = sy.W;
  const bdd& T = sy.T;
  const bdd& out = sy.out;
  const bdd& in = sy.in;

  my_out << "In is: " << in << '\n';
  my_out << "Out is: " << out << '\n';

  W = sy.F;
  attr.push_back(sy.F);
  my_out << "initial winning:\n" << W << '\n';

  for (unsigned outerCounter = 0; ; ++outerCounter){
    // Existential quantification over outputs needs to be done before
    // the quantification over the inputs as otherwise it will not be correctly recognized

    // We do it step by step for illustration

    // Current winning region in X'
    bdd Wp = bdd_replace(W, sy.X2Xp.get());
    // All combinations (X, I&O) that lead to the winning region
    bdd Tp = bdd_relprod(T, Wp, sy.Xp);
    // There is some output ...
    bdd TpEo = bdd_exist(Tp, out);
    // ... for all inputs
    bdd TpEoAi = bdd_forall(TpEo, in);
    // These are ALL the controlled predescessors
    bdd cpre = TpEoAi;
    // But we remember only the freshly attracted ones for
    // easier strategy generation
    attr.push_back(cpre - W);
    my_out << "Iteration " << outerCounter << " attracted\n" << attr.back() << '\n';
    if (attr.back() == bddfalse){
      my_out << "Attr computation finished\n";
      attr.pop_back();
      break;
    }
    W |= cpre;
  }
  // Done
}
