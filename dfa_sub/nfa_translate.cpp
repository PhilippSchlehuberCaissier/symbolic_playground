//
// Created by philipp on 1/1/24.
//

#include "nfa_translate.h"

#include <algorithm>
#include <array>
#include <cassert>
#include <deque>
#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "tl/formula.hh"

#include "twa/formula2bdd.hh"
#include "graph/graph.hh"
#include "twa/twagraph.hh"
#include "twaalgos/translate.hh"
#include "twaalgos/remprop.hh"
#include "tl/ltlf.hh"
#include "tl/nenoform.hh"


using namespace spot;


constexpr auto ALIVE = "__AlIvE__";

// Base translation
spot::twa_graph_ptr to_nfa(const spot::formula& f,
                           const spot::bdd_dict_ptr& bdd_dict) {
  auto tr = spot::translator(bdd_dict);
  tr.set_pref(8);
  auto aut = spot::to_finite(tr.run(spot::from_ltlf(f, ALIVE)), ALIVE);
  assert(aut->is_sba());
  assert(aut->acc().is_buchi());
  return aut;
}


// direct evaluation; delayed evaluation; primary successor
// primary succ:
// If entering node: node number of exit
// else: The implicit successor node
// -1u for no implicit successor
// A state is "accepting" if it has no successor,
// Neither explicit nor implicit
//using state_t = std::tuple<bdd, formula, unsigned>;
struct state_t {
  bdd cond;
  formula f_base;
  formula f_rewr;
  unsigned prim_succ;
};
struct edge_t {};
using formula_graph = digraph<state_t, edge_t>;

using state_dict = std::unordered_map<formula, std::array<unsigned, 2>>;

using linear_form = std::vector<std::pair<bdd, formula>>;


static void dbg_print(auto& f_graph, state_dict s_dict = state_dict()){
  unsigned ns = f_graph.num_states();

  std::cout << "Map\n";
  for (const auto& elem : s_dict){
    std::cout << elem.second[0] << ": ";
    elem.first.dump(std::cout);
    std::cout << " with " << elem.second[1] << " reusages.\n";
  }

  std::cout << "Graph\n";
  for (unsigned s = 0; s < ns; ++s){
    std::cout << s << "; " << f_graph.state_data(s).cond << "; " << (f_graph.state_data(s).prim_succ == -1u ? -1 : ((int) f_graph.state_data(s).prim_succ )) << "; ";
    f_graph.state_data(s).f_base.dump(std::cout);
    std::cout << " becomes ";
    f_graph.state_data(s).f_rewr.dump(std::cout);
    std::cout << '\n';

    auto it = f_graph.out(s);
    auto itb = it.begin();
    for (;itb;++itb) {
      const auto& e = *itb;
      std::cout << e.dst << "; ";
    }
    if (it.begin() != it.end())
      std::cout << '\n';

  }
}


// Rewrite as sum of products
static void rewrite_basic(formula_graph& f_graph,
                   state_dict& sd,
                   auto& f2bdd,
                   auto& waiting,
                   unsigned curr) {

  // If the state needs to be rewritten it can not have a
  // prime successor
  assert(f_graph.state_data(curr).prim_succ == -1u);


  formula f = f_graph.state_data(curr).f_rewr;

  // If the formula is boolean:
  // translate and put into condition field
  if (f.is_boolean()){
    f_graph.state_data(curr).cond &= f2bdd(f);
    // leave the formula as is
    //f_graph.state_data(curr).f = formula::tt();
    // Done
    return;
  }

  auto f_kind = f.kind();
  // Check trivial cases
  switch (f_kind) {
    case (op::tt):
    case (op::ff):
    case (op::X):
      // X and X[!] behave the same way here
      return;
    case (op::strong_X):
      f_graph.state_data(curr).f_rewr = f[0];// Replace strong_X by X
      return; // No further action required
    default:
      break;
  }

  // Check if the formula to rewrite already exists
  if (auto it = sd.find(f); it != sd.end()){
    ++it->second[1];
    f_graph.state_data(curr).prim_succ = it->second[0];
    return;
  }

  // We actually got work on our hands
  switch (f_kind) {
    // Boolean
    case (op::And): {
      // And : split it all up;
      // append a new state for each and
      // Combine all immediate verifications in the current state

      // First round collect all current conditions
      bdd c_cond = bddtrue;
      for (const auto& c: f) {
        if (c.is_boolean()) {
          c_cond &= f2bdd(c);
          if (c_cond == bddfalse)
            break;
        }
      }
      if (c_cond == bddfalse){
        // Formula can not be fulfilled
        sd.emplace(f, std::array<unsigned, 2>{-1u, 0u});
        // Mark this is the original node
        f_graph.state_data(curr).f_rewr = formula::ff();
        f_graph.state_data(curr).cond = bddfalse;
        break;
      }

      // Check how to avoid exploring unreachable successor (necessary?)

      // Loop again, this time taking care of non-boolean parts
      // Start should currently only be True and True
      unsigned end = f_graph.new_state(c_cond, formula::tt(), formula::tt(), -1u);
      unsigned start = f_graph.new_state(bddtrue, formula::tt(), formula::tt(), end);

      unsigned prev = start;
      for (const auto& c: f) {
        if (!c.is_boolean()) {
          unsigned ns = f_graph.new_state(bddtrue, c, c, -1u);
          waiting.push_back(ns); // Needs to be checked
          f_graph.new_edge(prev, ns);
          prev = ns;
        }
      }
      f_graph.new_edge(prev, end);

      // Save it in the dict
      sd[f] = {start, 0};
      // first points to prev (which is the last)
      f_graph.state_data(curr).prim_succ = start;

      // Delete the original formula
      f_graph.state_data(curr).f_rewr = formula::tt();
      break;
    }
    case (op::Or): {
      // Or : Make a branching
      // Thompson like construction to save transition
      // (maybe only if branching factor is large)
      unsigned end = f_graph.new_state(bddtrue, formula::tt(), formula::tt(), -1u);
      unsigned start = f_graph.new_state(bddtrue, formula::tt(), formula::tt(), end);

      for (const auto& c: f) {
        unsigned ns = -1u;
        if (c.is_boolean()) {
          bdd cond = f2bdd(c);
          if (cond != bddfalse)
            ns = f_graph.new_state(cond, c, formula::tt(), -1u);
        } else {
          ns = f_graph.new_state(bddtrue, c, c, -1u);
          waiting.push_back(ns);
        }
        // Transitions
        if (ns != -1u) {
          f_graph.new_edge(start, ns);
          f_graph.new_edge(ns, end);
        }
      }

      // Save it
      sd.emplace(f, std::array<unsigned, 2>{start, 0u});
      // Point it
      f_graph.state_data(curr).prim_succ = start;
      // Delete orig
      f_graph.state_data(curr).f_rewr = formula::tt();
      break;
    }
    case (op::Implies):{
      // a -> b
      formula a = f[0];
      formula b = f[1];
      f_graph.state_data(curr).f_rewr = formula::Or({formula::Not(a), formula::And({a,b})});
      waiting.push_back(curr);
      break;
    }
    case (op::Equiv):{
      // a <-> b
      // (a & b) | (!a & !b)
      formula a = f[0];
      formula b = f[1];
      f_graph.state_data(curr).f_rewr
          = formula::Or({formula::And({a,b}),
                               formula::And({formula::Not(a), formula::Not(b)})});
      waiting.push_back(curr);
      break;
    }
    case (op::Xor):{
      // a ^ b
      // (a & !b) | (!a & b)
      formula a = f[0];
      formula b = f[1];
      f_graph.state_data(curr).f_rewr
          = formula::Or({formula::And({a,formula::Not(b)}),
                               formula::And({formula::Not(a), b})});
      waiting.push_back(curr);
      break;
    }
    // Temporal
    case (op::F): {
      // LTLf semantics:
      // F(a) -> a || X[!](F(a))
      // However acceptance is based on formula so we can use
      // F(a) -> a || X(F(a))
      formula a = f[0];
      // Transform the formula
      f_graph.state_data(curr).f_rewr = formula::Or({a, formula::X(f)});
      // Redo
      waiting.push_back(curr);
      break;
    }
    case (op::G): {
      // G(a) -> a & X(G(a))
      formula a = f[0];
      // Transform the formula
      f_graph.state_data(curr).f_rewr = formula::And({a, formula::X(f)});
      // Redo
      waiting.push_back(curr);
      break;
    }
    case (op::U):
      // aUb -> (b or (a and X(aUb)))
      // Optim: if b is boolean then we can do
      // aUb -> (b or ((!b & a) and X(aUb)))
      {
        formula a = f[0];
        formula b = f[1];

        if (BOOL_OPTIM && b.is_boolean())
          a = formula::And({a, formula::unop(op::Not, b)});

        // Replace the current with the rewritten formula
        // and make a recursive call on it
        f_graph.state_data(curr).f_rewr = formula::Or({b,
                                                             formula::And({a, formula::X(f)})});
        //rewrite(f_graph, sd, f2bdd, waiting, curr);
        waiting.push_back(curr);
        break;
      }
    case (op::W):{
      // a W b -> (a U b) | Ga

      formula a = f[0];
      formula b = f[1];
      f_graph.state_data(curr).f_rewr = formula::Or({formula::G(a),
                                                           formula::U(a, b)});
      //rewrite(f_graph, sd, f2bdd, waiting, curr);
      waiting.push_back(curr);
      break;
    }
    default:
      throw std::runtime_error("Not supported: " + f.kindstr());
  }// switch

  return;
}

enum class task{
  enter = 0,
  firstv,
  secondv,
  done,
  unreach
};

struct node{
  unsigned s;
  bdd cond;
  formula f;
  //formula_graph::iterator it;
  unsigned n_e = -1u;
  task t = task::unreach;
  unsigned from_state = -1u;
};

void to_linear_form(formula_graph& f_graph,
                    linear_form& lf,
                    unsigned s){

  auto stack = std::deque<node>();
  //stack.reserve(1+f_graph.num_states()/10);

  auto to_edge = [&](const unsigned& e)->auto&{ return f_graph.edge_storage(e);};
  auto first_edge = [&](const unsigned& s){return f_graph.state_storage(s).succ;};
  auto to_state = [&](const unsigned& s) -> auto& {return f_graph.state_storage(s);};
  auto next_edge = [&](const unsigned& e){return to_edge(e).next_succ; };

  // Create a dictionary of entrance points
  // Which are currently on the stack
  auto entry_dict = std::unordered_set<unsigned>();

  // Get first edge

  assert(to_state(s).succ != 0);
  stack.emplace_back(s, bddtrue, formula::tt(), to_state(s).succ, task::secondv);

  while (!stack.empty()){
    //std::cout << "curr: " << stack.back().s << " " << ((int) stack.back().t) << std::endl;

    auto& cn = stack.back();

    switch(cn.t){
      case (task::enter): {
        assert(!entry_dict.count(cn.s));
        assert(cn.from_state != -1u);
        assert(cn.from_state != cn.s);
        // Update prim_succ of end
        to_state(to_state(cn.s).prim_succ).prim_succ = cn.from_state;
        // Now we will visit it
        stack.emplace_back(cn.s, cn.cond, cn.f, first_edge(cn.s), task::secondv);
        entry_dict.insert(cn.s);
        // And we will mark that we are done
        cn.t = task::done;
        break;
      }
      case (task::firstv): {
        // Four cases:
        // 1) No prime successor no actual successor -> terminal
        // 2) Prime successor but no actual successor -> second visit to prime successor (Basically looping back to it)
        // 3) No prime successor but actual successor -> second visit to this state
        // 4) Prime successor and actual successor -> Enter prime_successor EXCEPT prim_succ is already on path

        unsigned succ_e = first_edge(cn.s);
        unsigned psucc = to_state(cn.s).prim_succ;
        bool has_psucc = psucc != -1u;

        if (!has_psucc && !succ_e)
          // 1)
          lf.emplace_back(cn.cond, cn.f);
        else if (has_psucc && !succ_e)
          // 2)
          stack.emplace_back(psucc, cn.cond, cn.f, first_edge(psucc), task::secondv);
        else if (!has_psucc && succ_e)
          // 3)
          stack.emplace_back(cn.s, cn.cond, cn.f, succ_e, task::secondv);
        else if (has_psucc && succ_e)
          // 4)
          if (entry_dict.count(psucc))
            // On current stack -> Skip and go to actual visit
            stack.emplace_back(cn.s, cn.cond, cn.f, succ_e, task::secondv);
          else
            // Not on current stack
            stack.emplace_back(psucc, cn.cond, cn.f, first_edge(psucc), task::enter, cn.s);
        else
          SPOT_UNREACHABLE();
        // This task is done
        cn.t = task::done;
        break;
      }
      case (task::secondv): {

        if (cn.n_e != 0){
          //std::cout << "This succ " << to_edge(cn.n_e).dst << " for " << cn.n_e << '\n';
          // Visit the second as first visit
          // Already add the bdd and formula
          const auto& nse = to_edge(cn.n_e);
          const auto& nsd = to_state(nse.dst);
          bdd newcond = cn.cond & nsd.cond;
          if (newcond == bddfalse){
            // This does not need to be explored further
            //std::cout << "Dead transition from " << cn.s << " to " << nse.dst << "\nSkipping!\n";
            cn.n_e = next_edge(cn.n_e);
            break;
          }
          //          if (!((nsd.f == formula::tt()) || (nsd.f.kind() == op::X))){
          //            nsd.f.dump(std::cerr);
          //            dbg_print(f_graph);
          //          }
          //          assert((nsd.f == formula::tt()) || (nsd.f.kind() == op::X));

          auto& add_f = (nsd.f_rewr.kind() == op::X) ? nsd.f_rewr[0] : nsd.f_rewr;

          formula newf = (add_f == formula::tt() ? cn.f
                                                             : formula::And({cn.f, add_f}));
          stack.emplace_back(nse.dst, newcond, newf, first_edge(nse.dst), task::firstv);
          cn.n_e = next_edge(cn.n_e);
          /*
          if (cn.n_e)
            std::cout << "Next succ " << to_edge(cn.n_e).dst << " for " << cn.n_e << '\n';
          else
            std::cout << "No next succ for " << cn.n_e << '\n';
          */
        } else {
          // We are done here
          cn.t = task::done;
        }
        break;
      }
      case (task::done): {
        // Pop
        assert(&cn == &stack.back());
        //std::cout << "pop: " << cn.s << " " << ((int) cn.t) << std::endl;
        // If we pop an entrance point
        // -> set the psucc of the leaving point to -1u to mark it as free
        if (auto it = entry_dict.find(cn.s); it != entry_dict.end())
          entry_dict.erase(it);

        stack.pop_back();
        break;
      }
      case (task::unreach):
        SPOT_UNREACHABLE();
    }
  }

}

void rewrite_one(auto& f_graph, auto& s_dict, auto& f2bdd, auto& waiting, linear_form& lf,
                 const formula& f){

  // DBG
  std::cout << "rewriting:\n";
  f.dump(std::cout);
  std::cout << '\n';

  unsigned start = -1u;

  if (auto it = s_dict.find(f); it != s_dict.end()) {
    start = it->second[0];
  } else {
    unsigned end = f_graph.new_state(bddtrue, formula::tt(), formula::tt(), -1u);
    start = f_graph.new_state(bddtrue, formula::tt(), formula::tt(), end);
    unsigned n_state = f_graph.new_state(bddtrue, f, formula::tt(), -1u);
    f_graph.new_edge(start, n_state);
    f_graph.new_edge(n_state, end);

    if (f.is_boolean())
      f_graph.state_data(n_state).cond = f2bdd(f);
    else {
      f_graph.state_data(n_state).f_rewr = f;
      waiting.push_back(n_state);
    }

    while (!waiting.empty()) {
      rewrite_basic(f_graph, s_dict, f2bdd, waiting, waiting.front());
      waiting.pop_front();
      //std::cout << "Current f-graph\n";
      //dbg_print(f_graph, s_dict);
    }

    //dbg_print(f_graph, s_dict);
    // Register
    s_dict.emplace(f, std::array<unsigned, 2>{start, 0});
  }

  // dbg
  //dbg_print(f_graph, s_dict);

  to_linear_form(f_graph, lf, start);
  // dbg
  /*
  for (const auto& [ccc, fff] : lf){
    std::cout << ccc << " : ";
    fff.dump(std::cout);
    std::cout << '\n';
  }
  */
}

twa_graph_ptr from_ltlf(formula f){

  f = spot::negative_normal_form(f);

  auto nfa = make_twa_graph(make_bdd_dict());

  nfa->set_buchi();
  nfa->prop_state_acc(true);

  struct stater_ {
    state_dict& sd;
    ~stater_(){
      std::cout << "rewrite dict\n";
      for (const auto& elem : sd){
        std::cout << elem.second[0] << ": ";
        elem.first.dump(std::cout);
        std::cout << " with " << elem.second[1] << " reusages.\n";
      }
    }

  };

  // Setting up the translation
  auto rewrite_f = [&](const formula& f, linear_form& res) {
    static auto waiting = std::deque<unsigned>();
    static auto f_graph = formula_graph();
    static auto s_dict = state_dict();
    static auto st_ = stater_(s_dict);

    static auto f2bdd = [nfa, bdddict = nfa->get_dict()] (const formula& f) -> bdd{
      return formula_to_bdd(f, bdddict, nfa);
    };

    rewrite_one(f_graph, s_dict, f2bdd, waiting, res, f);
  };

  // DFS like translation
  auto nfa_waiting = std::vector<std::pair<unsigned, formula>>();
  auto nfa_sdict = state_dict();

  // The current linear form
  auto this_lf = linear_form();
  auto& nfar = *nfa;
  unsigned s0 = nfar.new_state();
  nfa_waiting.emplace_back(s0, f);
  nfa_sdict.emplace(std::piecewise_construct, std::forward_as_tuple(f), std::forward_as_tuple(std::array<unsigned, 2>{s0, 0u}));

  while (!nfa_waiting.empty()){
    auto [this_st, this_f] = std::move(nfa_waiting.back());
    nfa_waiting.pop_back();

    // rewrite this state
    this_lf.clear();
    //std::cout << "next rewrite \n";
    //this_f.dump(std::cout);
    //std::cout << " for state " << this_st << '\n';
    rewrite_f(this_f, this_lf);
    // Do some post-proc here

    // Insert the successors
    for (const auto& [cond, nxt_f] : this_lf){
      // Check if the destination state already exists
      /*
      std::cerr << cond << " < - > ";
      nxt_f.dump(std::cerr);
      std::cerr << '\n';
      */
      if (auto itf = nfa_sdict.find(nxt_f); itf != nfa_sdict.end()){

        std::cout << "Found ";
        nxt_f.dump(std::cout);
        std::cout << " at " << itf->second[0] << '\n';

        nfar.new_edge(this_st, itf->second[0], cond);
      } else {
        // We need a new state
        unsigned nxt_st = nfar.new_state();
        nfa_waiting.emplace_back(nxt_st, nxt_f);
        nfa_sdict.emplace(nxt_f, std::array<unsigned, 2>{nxt_st, 0u});
        nfar.new_edge(this_st, nxt_st, cond);

        std::cout << "Insert ";
        nxt_f.dump(std::cout);
        std::cout << " at " << nxt_st << '\n';

      }
      /*emplace
      std::cout << "Intermediat graph \n";
      print_dot(std::cout, nfa);
      */
    }

  } // waiting

  // Done translating
  /*
  std::cout << "State : associated formula\n";
  for (const auto& [f, s] : nfa_sdict) {
    std::cout << s << " : ";
    f.dump(std::cout);
    std::cout << '\n';
  }
  */

  auto mark_rec = [&](const formula& f, auto&& mark_rec_) -> bool{
    if (f.is_boolean())
      return true;

    switch (f.kind()){
      // Terminal cases
      case (op::G):
      case (op::X):
        return true;
      // Non-terminal cases
      case (op::F):
      case (op::U):
      case (op::strong_X):
        return false;
      // Conditional
      case (op::And):{
        for (const auto& c : f){
          if (!mark_rec_(c, mark_rec_))
            return false;
        }
        return true;
      }
      case (op::Or):{
        for (const auto& c : f){
          if (mark_rec_(c, mark_rec_))
            return true;
        }
        return false;
      }
      default:
        throw std::runtime_error("Operator not implemented");
    }
  };

  // Mark states
  [&](){
    for (const auto& [fs, ss] : nfa_sdict){
      if (mark_rec(fs, mark_rec)){
        bool marked = false;
        for (auto& e : nfar.out(ss[0])){
          e.acc = acc_cond::mark_t({0});
          marked = true;
        }
        if (!marked)
          nfar.new_edge(ss[0], ss[0], bddfalse, acc_cond::mark_t({0}));
      }
    }
  }();

  // Get props
  nfar.register_aps_from_dict();

  std::cout << "NFA dict\n";
  for (const auto& [k, v] : nfa_sdict){
    std::cout << v[0] << " : ";
    k.dump(std::cout);
    std::cout << '\n';
  }

  return nfa;
}