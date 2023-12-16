
#include <vector>
#include <array>
#include <string>
#include <memory>
#include <cassert>
#include <unordered_map>
#include <functional>
#include <algorithm>

#include "twaalgos/hoa.hh"
#include "twaalgos/dot.hh"
#include "twaalgos/contains.hh"
#include "parseaut/public.hh"
#include "twaalgos/isdet.hh"


#include "sym_aut_algos.h"

using namespace spot;




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

  auto g_sym = sym_aut::to_symbolic(g, "xo");
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

  auto [g_min, g_min_split] = g_sym_min.to_explicit();
  std::cout << "Explicit minimal aut has " << g_min->num_states() << '\n';

  std::cout << "Minimal aut\n";
  print_hoa(std::cout, g_min);
  std::cout << '\n';

  std::cout << "Minimal aut is:\n"
            << "deterministic: " << is_deterministic(g_min) << '\n'
            << "complete: " << is_complete(g_min) << '\n';

  if (g_min_split){
    // The display is not entirely correct
    // Especially for successors of F
    std::cout << "The solved game is:\n";
    print_dot(std::cout, g_min_split);
    std::cout << '\n';
  }

  dfa_contains(g_min, g);
  auto isCorr = dfa_equiv(g, g_min);
  std::cout << "\nCorrect: " << isCorr << '\n';

  return 0;
}
