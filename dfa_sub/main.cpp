#include "definitions.h"

#include "tl/formula.hh"
#include "tl/parse.hh"

#include "twaalgos/dot.hh"
#include "twaalgos/hoa.hh"

#include "nfa_helper.h"
#include "nfa_translate.h"




int main(int argc, char** argv) {
  if (argc != 2) {
    std::cerr << "Expected formula as second arg\n";
    std::cout << argc << '\n';
    for (int i = 0; i < argc; ++i)
      std::cout << argv[i] << std::endl;
    return 1;
  } else {
    std::cout << "formula is " << argv[1] << std::endl;
  }

  auto f = spot::parse_formula(argv[1]);

  auto nfa = from_ltlf(f);

  //nfa = nfa_determinize(nfa);

  spot::print_dot(std::cerr, nfa);

  auto aut2 = to_nfa(f, nfa->get_dict());

  complete_nfa(nfa);
  complete_nfa(aut2);

  auto [is_diff, word] = nfa_equal(nfa, aut2);

  if (is_diff != 0){
    std::cout << "Aut have diff lang. Word accepted by "
              << ((is_diff == 1) ? "left\n" : "right\n");
    for (const auto& c : word){
      std::cout << c << '\n';
    }
    return 1;
  }

  return 0;
}
//
//  spot::twa_graph nfa = from_ltlf(f);
//
//  auto f_graph = formula_graph();
//
//  auto waiting = std::deque<unsigned>();
//  auto s_dict = state_dict();
//
//  auto bdict = spot::make_bdd_dict();
//
//  auto f2bdd = [&](const spot::formula& f) -> bdd{
//    return spot::formula_to_bdd(f, bdict, bdict);
//  };
//
//  unsigned start = f_graph.new_state(bddtrue, spot::formula::tt(), -1u);
//  unsigned n_state = f_graph.new_state(bddtrue, spot::formula::tt(), -1u);
//  unsigned end = f_graph.new_state(bddtrue, spot::formula::tt(), -1u);
//  f_graph.new_edge(start, n_state);
//  f_graph.new_edge(n_state, end);
//
//  if (f.is_boolean())
//    f_graph.state_data(n_state).cond = f2bdd(f);
//  else{
//    f_graph.state_data(n_state).f = f;
//    waiting.push_back(n_state);
//  }
//
//  while (!waiting.empty()) {
//    rewrite(f_graph, s_dict, f2bdd, waiting, waiting.front());
//    waiting.pop_front();
//  }
//
//  unsigned ns = f_graph.num_states();
//
//  std::cout << "Map\n";
//  for (const auto& elem : s_dict){
//    std::cout << elem.second << ": ";
//    elem.first.dump(std::cout);
//    std::cout << '\n';
//  }
//
//  std::cout << "Graph\n";
//  for (unsigned s = 0; s < ns; ++s){
//    std::cout << s << "; " << f_graph.state_data(s).cond << "; " << (f_graph.state_data(s).prim_succ == -1u ? -1 : ((int) f_graph.state_data(s).prim_succ )) << "; ";
//    f_graph.state_data(s).f.dump(std::cout);
//    std::cout << '\n';
//
//    auto it = f_graph.out(s);
//    auto itb = it.begin();
//    for (;itb;++itb) {
//      const auto& e = *itb;
//      std::cout << e.dst << "; ";
//    }
//    if (it.begin() != it.end())
//      std::cout << '\n';
//
//  }
//
//
//  auto lf = linear_form();
//  to_linear_form(f_graph, lf, start);
//  std::cout << "Resulting linear form\n";
//
//  for (const auto& [cc, ff] : lf){
//    std::cout << cc << " : ";
//    ff.dump(std::cout);
//    std::cout << '\n';
//  }
//
//  bdict->unregister_all_my_variables(bdict.get());
//  return 0;
//}
