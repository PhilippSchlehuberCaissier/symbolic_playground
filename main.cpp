#include <iostream>
#include <math.h>
#include <vector>
#include <array>
#include <string>
#include <memory>
#include <cassert>
#include <unordered_map>
#include <functional>
#include <algorithm>

#include "twa/twagraph.hh"
#include "twaalgos/hoa.hh"
#include "twaalgos/contains.hh"
#include "parseaut/public.hh"
#include "twaalgos/isdet.hh"
#include "twaalgos/product.hh"
#include "misc/bddlt.hh"

using namespace spot;

struct my_out_c{
  inline static bool v_ = true;
}my_out;

template<class T>
my_out_c& operator<<(my_out_c& mo, const T& t){
  if (mo.v_)
    std::cout << t;
  return mo;
}



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
  // Attr[0] is F
  // Attr[i+1] = cpre(W_i] \ W_i
  // These are the "freshly" attracted states (Makes it easier to extract a strategy

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

  friend std::ostream& operator<<(std::ostream& os, const sym_aut& sa){
    os << "All states:\n " << sa.S << '\n'
       << "Initial state:\n " << sa.I << '\n'
       << "Final states:\n " << sa.F << '\n'
       << "Transitions:\n " << sa.T << '\n'
       << "All X:\n " << sa.X << '\n'
       << "All X prime:\n " << sa.Xp << '\n'
       << "All AP:\n " << sa.P << '\n';
       return os;
  }
};

inline unsigned
nbits(unsigned n) {
  return std::max(1., std::ceil(std::log2(n)));
}


inline bdd
encode_state_(unsigned s, const std::vector<std::array<bdd, 2>>& Xvec, unsigned Nvars) {
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

sym_aut to_symbolic(const twa_graph_ptr& g, const std::string& base){
  const unsigned Nstates = g->num_states();
  const unsigned Nvars = nbits(Nstates);

  my_out << Nvars << " variables used for " << Nstates << " states.\n";

  auto sy = sym_aut();
  sy.aut_orig = g;

  // Setup
  sy.setup(Nvars, base);

  // Encode all states

  auto encode_state = [&sy, Nvars](unsigned s) -> bdd{
    return encode_state_(s, sy.Xvec, Nvars);
  };

  auto s2X = std::vector<std::array<bdd,2>>(Nstates);

  for (unsigned s = 0; s < Nstates; ++s){
    auto x = encode_state(s);
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

template<>
struct std::hash<std::array<unsigned, 2>> {
  std::size_t operator()(const std::array<unsigned,2>& a) const noexcept {
    unsigned long long h = a[0];
    h <<= 32;
    h += a[1];
    return std::hash<unsigned long long>()(h);
  }
};

sym_aut
signature_min(const sym_aut& sy, const std::string& base){
  // all equivalence classes in their normal and primed version
  // Initialized with S\F and F
  auto equiv_classes = std::unordered_map<bdd, unsigned, bdd_hash>();

  auto get_class = [&equiv_classes](const bdd& c) -> unsigned {
    auto [it, ins] = equiv_classes.insert(std::make_pair(c, (unsigned) equiv_classes.size()));
    if (ins)
      my_out << "New class " << it->second << " : " << it->first << '\n';
    return it->second;
  };
  auto reset_class = [&equiv_classes](){
    equiv_classes.clear();
  };

  auto res = sym_aut();
  res.aut_orig = sy.aut_orig;
  // We can not have more -> keep the same number of AP so we are safe
  const unsigned NvarsNew = sy.Xvec.size();

  res.setup(NvarsNew, base);
  res.T = bddfalse;

  // This encode is the class encoding
  auto encode_state= [&res, NvarsNew](unsigned s) -> bdd{
    return encode_state_(s, res.Xvec, NvarsNew);
  };

  auto cidx2C = std::vector<std::array<bdd,2>>(std::pow(2, NvarsNew));

  for (unsigned cidx = 0; cidx < std::pow(2, NvarsNew); ++cidx){
    auto c = encode_state(cidx);
    auto cp = bdd_replace(c, res.X2Xp.get());
    cidx2C[cidx] = {c,cp};
    my_out << "cidx " << cidx << " : " << c << '\n';
  }

  // We start off with two classes
  get_class(cidx2C[0][0]);
  get_class(cidx2C[1][0]);

  // This should be optimized
  // enumerate all states
  auto all_states = std::vector<std::array<bdd, 2>>();
  all_states.reserve(std::pow(2, NvarsNew));
  //for (const auto& xs : minterms_of(sy.S, sy.X)){
  //  all_states.push_back({xs, bdd_replace(xs, sy.X2Xp.get())});
  //  my_out << "xs " << xs << " : " << all_states.size() - 1 << '\n';
  //}
  {
    auto encode_state_old= [&sy, NvarsNew](unsigned s) -> bdd{
      return encode_state_(s, sy.Xvec, NvarsNew);
    };
    for (unsigned sidx = 0; sidx < std::pow(2, NvarsNew); ++sidx){
      bdd xs = encode_state_old(sidx);
      my_out << "xs " << xs << " : " << all_states.size() << '\n';
      if (bdd_implies(xs, sy.S) == 0){
        my_out << "Break at state " << sidx << '\n';
        break;
      }
      all_states.push_back({xs, bdd_replace(xs, sy.X2Xp.get())});
    }
  }

  // This bdd encodes which state belongs to which class
  const unsigned Nstates = all_states.size();
  bdd Cp = bddfalse;
  for (unsigned xidx = 0; xidx < Nstates; ++xidx){
    Cp |= all_states[xidx][1] & (bdd_implies(all_states[xidx][0], sy.F) ? cidx2C[1][0] : cidx2C[0][0]);
  }
  my_out << "Initial Cp is " << Cp << '\n';

  // Associate to each state a class
  auto sidx2Cidx = std::vector<unsigned>(Nstates, -1u);

  // Main iteration
  for (unsigned outerCounter = 0; ; ++outerCounter){
    my_out << "Starting iteration i\n";
    const unsigned NclassesStart = equiv_classes.size();
    reset_class();

    bdd F = bdd_relprod(sy.T, Cp, sy.Xp); // Computes F(X, AP, Classes)
    my_out << "Current F is:\n" << F << '\n';
    // Compute the new signature for each state (This is the part that is not cool)
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
    if (equiv_classes.size() == NclassesStart)
      break; // Fixpoint
  }

  const unsigned NstatesNew = equiv_classes.size();
  // Now we need to build it
  my_out << "Found " << NstatesNew << " equivalence classes.\n";

  res.F = bddfalse;
  res.I = bddfalse;
  res.S = bddfalse;
  res.T = bddfalse;

  // At this point
  // Cp(Xp, \C) is a function assigning to each state X a class \C
  // But we need it to be in \Cp
  Cp = bdd_replace(Cp, res.X2Xp.get());
  my_out << "Final Cp is\n" << Cp << '\n';

  // We also need the unprimed version
  // C(X, \C) is a function assigning to each state X a class C (The same as in the primed version)
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

  my_out << "Final is resulting is\n" << res << '\n';

  return res;
}

// This does not work as expected, I have to think about it
/*
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

twa_graph_ptr
to_explicit(const sym_aut& sy){
  auto aut = make_twa_graph(sy.aut_orig->get_dict());
  aut->copy_ap_of(sy.aut_orig);
  aut->copy_acceptance_of(sy.aut_orig);
  aut->prop_state_acc(true);
  assert(sy.aut_orig->is_sba());

  // We assume that states are binary encoded and "left aligned"
  auto encode_state = [&sy, Nvars=sy.Xvec.size()](unsigned s) -> bdd{
    return encode_state_(s, sy.Xvec, Nvars);
  };

  std::vector<std::array<bdd, 2>> statevec;
  statevec.reserve(std::pow(2, sy.Xvec.size()));
  unsigned init_state = -1u;

  {
    for (unsigned s = 0; ; ++s){
      bdd sx = encode_state(s);
      if (bdd_implies(sx, sy.S) != 1)
        break;
      statevec.push_back({sx, bdd_replace(sx, sy.X2Xp.get())});
      if (bdd_implies(sx, sy.I)) {
        assert(init_state == -1u);
        init_state = s;
      }
    }
    assert(init_state != -1u);
    aut->new_states(statevec.size());
    aut->set_init_state(init_state);
  }

  auto XXp = sy.X & sy.Xp;
  const unsigned Nstates = aut->num_states();
  for (unsigned src = 0; src < Nstates; ++src){
    for (unsigned dst = 0; dst < Nstates; ++dst){
      bdd cond = bdd_restrict(sy.T, statevec[src][0]&statevec[dst][1]);
      if (cond == bddfalse)
        continue;
      if (bdd_implies(statevec[src][0], sy.F))
        aut->new_edge(src, dst, cond, {0});
      else
        aut->new_edge(src, dst, cond);
    }
  }

  return aut;
}

bool dfa_contains(const twa_graph_ptr& left, const twa_graph_ptr& right){
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

bool dfa_equiv(const twa_graph_ptr& left, const twa_graph_ptr& right){
  return dfa_contains(left, right) && dfa_contains(right, left);
}

// Game algos

void
solve_reachability(sym_aut& sy){
  // Solves the reachability games and set the W and Attr field

  auto& attr = sy.Attr;
  auto& W = sy.W;
  const bdd& T = sy.T;
  const bdd& out = sy.out;
  const bdd& in = sy.in;

  std::cout << "In is: " << in << '\n';
  std::cout << "Out is: " << out << '\n';

  W = sy.F;
  std::cout << "initial winning:\n" << W << '\n';

  for (unsigned outerCounter = 0; ; ++outerCounter){
    std::cout << "Starting the " << outerCounter << " cpre loop with W\n" << W << '\n';
    bdd Wp = bdd_replace(W, sy.X2Xp.get());
    std::cout << "Wp\n" << Wp << '\n';
    bdd Tp = bdd_relprod(T, Wp, sy.Xp);
    std::cout << "Tp\n" << Tp << '\n';

    bdd TpAi = bdd_forall(Tp, in);
    std::cout << "TpAi\n" << TpAi << '\n';
    bdd TpAiEo = bdd_exist(TpAi, out);
    std::cout << "TpAiEo\n" << TpAiEo << '\n';

    bdd TpEo = bdd_exist(Tp, out);
    std::cout << "TpEo\n" << TpEo << '\n';
    bdd TpEoAi = bdd_forall(TpEo, in);
    std::cout << "TpEoAi\n" << TpEoAi << '\n'; // We need this

    bdd cpre = TpAiEo;
    attr.push_back(cpre - W);
    my_out << "Attracted:\n" << attr.back() << '\n';
    if (attr.back() == bddfalse){
      my_out << "Attr computation finished\n";
      attr.pop_back();
      break;
    }
    W |= cpre;
  }
  // Done
}

int main(int argc, char** argv) {

  auto bdddict = make_bdd_dict();
  twa_graph_ptr g;

  if (argc == 1){
    g = make_twa_graph(bdddict);

    g->set_buchi();
    g->prop_state_acc(true);

    g->new_states(6);

    auto a = bdd_ithvar(g->register_ap("a"));
    auto na = bdd_nithvar(g->register_ap("a"));

    g->new_edge(0,1,a);
    g->new_edge(0,3,na);
    g->new_edge(1,1,a);
    g->new_edge(1,2,na);
    g->new_edge(2,2,a);
    g->new_edge(2,5,na);
    g->new_edge(3,3,a);
    g->new_edge(3,4,na);
    g->new_edge(4,4,a);
    g->new_edge(4,5,na);
    g->new_edge(5,5,bddtrue, {0});
  } else if(argc == 2){
    auto p = automaton_stream_parser(argv[1]);
    auto r = p.parse(bdddict);
    g = r->aut;
  }else
    throw std::runtime_error("Expected 0 or 1 argument. The argument is expected to be a sba");

  std::cout << "Orig aut\n";
  print_hoa(std::cout, g);

  bdd g_in = bddfalse;
  bdd g_out = bddfalse;

  if (auto* out = g->get_named_prop<bdd>("synthesis-outputs")){
    g_out = *out;
    g_in = bdd_restrict(g->ap_vars(), g_out);
    std::cout << '\n'  << g->ap_vars() << '\n' << g_out << '\n' << g_in << std::endl;
  }

  if (!is_deterministic(g)){
    if (auto* out = g->get_named_prop<bdd>("synthesis-outputs"))
      std::cout << "Working on a game\n";
    else
      throw std::runtime_error("Initial DFA not deterministic!");
  }

  if (!is_complete(g))
    if (auto* out = g->get_named_prop<bdd>("synthesis-outputs"))
      std::cout << "Working on a game\n";
    else
      throw std::runtime_error("Initial DFA not complete!");

  auto g_sym = to_symbolic(g, "xo");
  std::cout << g_sym << std::endl;
  std::cout << "Transitions have " << bdd_nodecount(g_sym.T) << " nodes.\n";
  //auto g_sym_min = symbolic_min(g_sym, "xm");
  auto g_sym_min = signature_min(g_sym, "xm");
  std::cout << "Minimized transitions have " << bdd_nodecount(g_sym_min.T) << " nodes.\n";

  if (auto* out = g->get_named_prop<bdd>("synthesis-outputs")){
    std::cout << "Original aut was a game; Trying to solve it\n";
    g_sym_min.out = g_out;
    g_sym_min.in = g_in;

    solve_reachability(g_sym_min);
  }

  auto g_min = to_explicit(g_sym_min);
  std::cout << "Explicit minimal aut has " << g_min->num_states() << '\n';

  std::cout << "Minimal aut\n";
  print_hoa(std::cout, g_min);
  std::cout << '\n';

  std::cout << "Minimal aut is:\n"
            << "deterministic: " << is_deterministic(g_min) << '\n'
            << "complete: " << is_complete(g_min) << '\n';

  dfa_contains(g_min, g);
  auto isCorr = dfa_equiv(g, g_min);
  std::cout << "\nCorrect: " << isCorr << '\n';

  return 0;
}
