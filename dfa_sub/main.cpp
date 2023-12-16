
#define SPOT_WANT_STRONG_X

#include <algorithm>
#include <array>
#include <cassert>
#include <deque>
#include <functional>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

#include "parseaut/public.hh"
#include "tl/formula.hh"
#include "tl/nenoform.hh"
#include "tl/parse.hh"
#include "tl/unabbrev.hh"
#include "twa/formula2bdd.hh"
#include "twaalgos/contains.hh"
#include "twaalgos/dot.hh"
#include "twaalgos/hoa.hh"
#include "twaalgos/isdet.hh"

#include "sym_aut_algos.h"

using namespace spot;

static bool BOOL_OPTIM = false;

// direct evaluation; delayed evaluation; primary successor
// primary succ:
// If entering node: node number of exit
// else: The implicit successor node
// -1u for no implicit successor
// A state is "accepting" if it has no successor,
// Neither explicit nor implicit
//using state_t = std::tuple<bdd, spot::formula, unsigned>;
struct state_t {
  bdd cond;
  spot::formula f;
  unsigned prim_succ;
};
struct edge_t {};
using formula_graph = spot::digraph<state_t, edge_t>;

using state_dict = std::unordered_map<spot::formula, unsigned>;

using linear_form = std::vector<std::pair<bdd, spot::formula>>;



// Rewrite as sum of products
void rewrite(formula_graph& f_graph,
             state_dict& sd,
             auto& f2bdd,
             auto& waiting,
             unsigned curr) {

  spot::formula f = f_graph.state_data(curr).f;
  auto f_kind = f.kind();
  // Check trivial cases
  switch (f_kind) {
    case (spot::op::tt):
    case (spot::op::X):
      return;
    case (spot::op::strong_X):
      f_graph.state_data(curr).f = spot::formula::X(f[0]);// Replace strong_X by X
      return;
  }

  // Check if the formula to rewrite already exists
  if (auto it = sd.find(f); it != sd.end()){
    // Set the primary successor
    f_graph.state_data(curr).prim_succ = it->second;
    return;
  }

  // We actually got work on our hands
  switch (f_kind) {
    case (spot::op::And): {
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
        // Formula can not be fullfilled
        sd[f] = -1u;
        break;
      }

      // Check how to avoid exploring unreachable successor (necessary?)

      // Loop again, this time taking care of non-boolean parts
      unsigned end = f_graph.new_state(bddtrue, spot::formula::tt(), -1u);
      unsigned start = f_graph.new_state(c_cond, spot::formula::tt(), end);

      unsigned prev = start;
      for (const auto& c: f) {
        if (!c.is_boolean()) {
          unsigned ns = f_graph.new_state(bddtrue, c, -1u);
          waiting.push_back(ns); // Needs to be checked
          f_graph.new_edge(prev, ns);
          prev = ns;
        }
      }
      f_graph.new_edge(prev, end);

      // Save it in the dict
      sd[f] = start;
      // first points to prev (which is the last)
      f_graph.state_data(curr).prim_succ = start;

      // Delete the original formula
      f_graph.state_data(curr).f = spot::formula::tt();
      break;
    }
    case (spot::op::Or): {
      // Or : Make a branching
      // Thompson like construction to save transition
      // (maybe only if branching factor is large)
      unsigned end = f_graph.new_state(bddtrue, spot::formula::tt(), -1u);
      unsigned start = f_graph.new_state(bddtrue, spot::formula::tt(), end);

      for (const auto& c: f) {
        unsigned ns = -1u;
        if (c.is_boolean()) {
          bdd cond = f2bdd(c);
          if (cond != bddfalse)
            ns = f_graph.new_state(cond, spot::formula::tt(), -1u);
        } else {
          ns = f_graph.new_state(bddtrue, c, -1u);
          waiting.push_back(ns);
        }
        // Transitions
        if (ns != -1u) {
          f_graph.new_edge(start, ns);
          f_graph.new_edge(ns, end);
        }
      }

      // Save it
      sd[f] = start;
      // Point it
      f_graph.state_data(curr).prim_succ = start;
      // Delete orig
      f_graph.state_data(curr).f = spot::formula::tt();
      break;
    }
    case (spot::op::F):
      // LTLf semantics:
      // F(a) -> a & X[!](F(a))
      // However acceptance is based on formula so we can use
      // F(a) -> a & X(F(a))
      // So it behaves like G
      SPOT_FALLTHROUGH;
    case (spot::op::G): {
      // G(a) -> a & X(G(a))
      formula a = f[0];
      // If a is boolean we can simply add it to the first term
      // Otherwise we need to append it
      if (a.is_boolean())
        f_graph.state_data(curr).cond = f2bdd(a) & f_graph.state_data(curr).cond;
      else {
        // We need a new state
        unsigned na = f_graph.new_state(bddtrue, a, -1u);
        waiting.push_back(na);
        // All successor of current become successors of new
        for (const auto& e: f_graph.out(curr))
          f_graph.new_edge(na, e.dst);
        // Erase current edges and make one new
        auto erase = f_graph.out_iteraser(curr);
        while (erase)
          erase.erase();
        f_graph.new_edge(curr, na);
      }
      // Push the current to the future
      f_graph.state_data(curr).f = spot::formula::X(f);
      break;
    }
    case (spot::op::U):
      // aUb -> (b or (a and X(aUb)))
      // Optim: if b is boolean then we can do
      // aUb -> (b or ((!b & a) and X(aUb)))
      {
        formula a = f[0];
        formula b = f[1];

        if (BOOL_OPTIM && b.is_boolean())
          a = spot::formula::And({a, spot::formula::unop(spot::op::Not, b)});

        // Replace the current with the rewritten formula
        // and make a recursive call on it
        assert(f_graph.state_data(curr).prim_succ = -1u);
        f_graph.state_data(curr).f = spot::formula::Or({b,
                                            spot::formula::And({a, spot::formula::X(f)})});
        rewrite(f_graph, sd, f2bdd, waiting, curr);
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
  done
};

struct node{
  unsigned s;
  bdd cond;
  spot::formula f;
  formula_graph::iterator it;
  task t;
  unsigned from_state = -1u;
};

void to_linear_form(formula_graph& f_graph,
                    linear_form& lf,
                    unsigned s){

  auto stack = std::vector<node>();
  //stack.reserve(1000+1+f_graph.num_states()/10);

  assert(f_graph.state_data(s).prim_succ == -1u);
  stack.emplace_back(s, bddtrue, spot::formula::tt(), f_graph.out(s).begin(), task::secondv);

  while (!stack.empty()){
    std::cout << "curr: " << stack.back().s << " " << ((int) stack.back().t) << std::endl;

    auto& cn = stack.back();

    switch(cn.t){
      case (task::enter): {
        assert(cn.from_state != -1u);
        assert(cn.from_state != cn.s);
        // Update prim_succ of end
        f_graph.state_data(f_graph.state_data(cn.s).prim_succ).prim_succ = cn.from_state;
        // Now we will visit it
        stack.emplace_back(cn.s, cn.cond, cn.f, f_graph.out(cn.s).begin(), task::secondv);
        // And we will mark that we are done
        cn.t = task::done;
        break;
      }
      case (task::firstv): {
        // Four cases:
        // 1) No prime successor no actual successor -> terminal
        // 2) Prime successor but no actual successor -> second visit to prime successor (Basically looping back to it)
        // 3) No prime successor but actual successor -> second visit to this state
        // 4) Prime successor and actual successor -> Enter prime_successor

        auto itb = f_graph.out(cn.s).begin();
        unsigned psucc = f_graph.state_data(cn.s).prim_succ;
        bool has_psucc = psucc != -1u;

        if (!has_psucc && !itb)
          // 1)
          lf.emplace_back(cn.cond, cn.f);
        else if (has_psucc && !itb)
          // 2)
          stack.emplace_back(psucc, cn.cond, cn.f, f_graph.out(psucc).begin(), task::secondv);
        else if (!has_psucc && itb)
          // 3)
          stack.emplace_back(cn.s, cn.cond, cn.f, itb, task::secondv);
        else if (has_psucc && itb)
          // 4)
          stack.emplace_back(psucc, cn.cond, cn.f, f_graph.out(psucc).end(), task::enter, cn.s);
        else
          SPOT_UNREACHABLE();
        // This task is done
        cn.t = task::done;
        break;
      }
      case (task::secondv): {

        if (cn.it){
          std::cout << "This succ " << cn.it->dst << " for " << &cn.it << '\n';
          // Visit the second as first visit
          // Already add the bdd and formula
          const auto& nsd = f_graph.state_data(cn.it->dst);
          bdd newcond = cn.cond & nsd.cond;
          spot::formula newf = (nsd.f == spot::formula::tt() ? cn.f
                                                             : spot::formula::And({cn.f, nsd.f}));
          stack.emplace_back(cn.it->dst, newcond, newf, f_graph.out(cn.it->dst).end(), task::firstv);
          ++cn.it;
          if (cn.it)
            std::cout << "Next succ " << cn.it->dst << " for " << &cn.it << '\n';
          else
            std::cout << "No next succ for " << &cn.it << '\n';
        }else
          // We are done here
          cn.t = task::done;
        break;
      }
      case (task::done): {
        // Pop
        assert(&cn == &stack.back());
        std::cout << "pop: " << cn.s << " " << ((int) cn.t) << std::endl;
        stack.pop_back();
        break;
      }
    }
  }





}


int main(int argc, char** argv) {
  if (argc != 2) {
    std::cerr << "Expected formula as second arg\n";
    return 1;
  }

  auto f = spot::negative_normal_form(spot::parse_formula(argv[1]));

  f.dump(std::cout);
  std::cout << std::endl;
  std::cout << f.kindstr() << std::endl;

  auto f_graph = formula_graph();

  auto waiting = std::deque<unsigned>();
  auto s_dict = state_dict();

  auto bdict = spot::make_bdd_dict();

  auto f2bdd = [&](const spot::formula& f) -> bdd{
    return spot::formula_to_bdd(f, bdict, bdict);
  };

  unsigned start = f_graph.new_state(bddtrue, spot::formula::tt(), -1u);
  unsigned n_state = f_graph.new_state(bddtrue, spot::formula::tt(), -1u);
  unsigned end = f_graph.new_state(bddtrue, spot::formula::tt(), -1u);
  f_graph.new_edge(start, n_state);
  f_graph.new_edge(n_state, end);

  if (f.is_boolean())
    f_graph.state_data(n_state).cond = f2bdd(f);
  else{
    f_graph.state_data(n_state).f = f;
    waiting.push_back(n_state);
  }

  while (!waiting.empty()) {
    rewrite(f_graph, s_dict, f2bdd, waiting, waiting.front());
    waiting.pop_front();
  }

  unsigned ns = f_graph.num_states();

  std::cout << "Map\n";
  for (const auto& elem : s_dict){
    std::cout << elem.second << ": ";
    elem.first.dump(std::cout);
    std::cout << '\n';
  }

  std::cout << "Graph\n";
  for (unsigned s = 0; s < ns; ++s){
    std::cout << s << "; " << f_graph.state_data(s).cond << "; " << (f_graph.state_data(s).prim_succ == -1u ? -1 : ((int) f_graph.state_data(s).prim_succ )) << "; ";
    f_graph.state_data(s).f.dump(std::cout);
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

  bdict->unregister_all_my_variables(bdict.get());

  auto lf = linear_form();
  to_linear_form(f_graph, lf, start);
  std::cout << "Resulting linear form\n";

  for (const auto& [cc, ff] : lf){
    std::cout << cc << " : ";
    ff.dump(std::cout);
    std::cout << '\n';
  }

  return 0;
}
