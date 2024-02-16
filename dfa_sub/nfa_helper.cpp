//
// Created by philipp on 12/27/23.
//

#include "nfa_helper.h"
#include "misc/hash.hh"
#include "twaalgos/complement.hh"
#include "misc/partitioned_relabel.hh"
#include "twaalgos/hoa.hh"


#include <array>
#include <deque>
#include <unordered_set>


void complete_nfa(spot::twa_graph_ptr& aut) {

  auto& autr = *aut;

  auto get_sink = [&]() {
    static unsigned sink = -1u;
    if (sink == -1u) {
      sink = autr.new_state();
      autr.new_edge(sink, sink, bddtrue);
    }
    return sink;
  };

  const unsigned N = autr.num_states();

  for (unsigned s = 0; s < N; ++s) {
    bdd rem = bddtrue;
    for (const auto& e: autr.out(s))
      rem -= e.cond;
    if (rem != bddfalse)
      autr.new_edge(s, get_sink(), rem);
  }
  // Done
}


std::pair<int, std::vector<bdd>> nfa_equal(const spot::const_twa_graph_ptr& left,
                                            const spot::const_twa_graph_ptr& right) {
  {
    auto rc = spot::complement(right);
    auto res1 = nfa_intersect(left, rc);
    if (res1.size())
      return std::make_pair(1, std::move(res1));
  }
  {
    auto lc = spot::complement(left);
    auto res2 = nfa_intersect(right, lc);
    if (res2.size())
      return std::make_pair(-1, std::move(res2));
  }
  return std::make_pair(0, std::vector<bdd>{});
}

std::vector<bdd> nfa_intersect(const spot::const_twa_graph_ptr& left,
                               const spot::const_twa_graph_ptr& right){

  for (const auto& a: {left, right}) {
    assert(a->is_sba());
    assert(a->acc().is_buchi());
  }

  auto& lr = *left;
  auto& rr = *right;
  auto& lg = lr.get_graph();
  auto& rg = rr.get_graph();

  auto seen = std::unordered_set<std::pair<unsigned, unsigned>, spot::pair_hash>();
  seen.reserve(lr.num_states() * rr.num_states());

  struct node {
    unsigned ls;    // left state, -1u -> dead
    unsigned rs;    // right state, -1u -> dead
    unsigned le = 0;// left edge
    unsigned re = 0;// right edge
  };

  auto stack = std::deque<node>();

  auto add_node = [&](unsigned ls, unsigned rs) {
    if (const auto& [_, ins] = seen.emplace(ls, rs); ins) {
      stack.emplace_back(ls, rs, lg.state_storage(ls).succ, rg.state_storage(rs).succ);
      assert(stack.back().le != 0);
      assert(stack.back().re != 0);
      return true;
    }
    return false;
  };

  add_node(lr.get_init_state_number(), rr.get_init_state_number());

  while (!stack.empty()) {
    auto& current = stack.back();
    // Check if current node (and stack)
    // represent a violation
    if (lr.state_is_accepting(current.ls)
        && rr.state_is_accepting(current.rs)){

      auto word = std::vector<bdd>();
      word.reserve(stack.size());

      for (const auto& node : stack) {
        word.push_back(lr.edge_storage(node.le).cond & rr.edge_storage(node.re).cond);
        assert(word.back() != bddfalse);
      }
      return word;
    }


    if ((current.le == 0) && (current.re == 0)) {
      // All successor explored, back track
      stack.pop_back();
      break;
    }
    // Search for next possible successor
    while (true) {
      if (current.re == 0) {
        current.le = lg.edge_storage(current.le).next_succ;
        if (current.le == 0)
          break;// We ran out of transitions
        current.re = rg.state_storage(current.rs).succ;
      } else {
        current.re = rg.edge_storage(current.re).next_succ;
      }

      // Check if the current combination yields a successor
      const auto& le = lr.edge_storage(current.le);
      const auto& re = rr.edge_storage(current.re);
      if (bdd_have_common_assignment(le.cond, re.cond)) {
        if (add_node(le.dst, re.dst))
          break;// Pushed a new successor
      }
    }
  }
  return std::vector<bdd>{};
}

spot::twa_graph_ptr nfa_determinize(spot::const_twa_graph_ptr aut){

  assert(aut->is_sba());
  assert(aut->acc().is_buchi());

  assert(([&](){
    const unsigned N = aut->num_states();
    for (unsigned s = 0; s < N; ++s){
      bdd rem = bddtrue;
      for (const auto& e : aut->out(s)){
        rem -= e.cond;
        if (rem == bddfalse)
          break;
      }
      if (rem != bddfalse)
        return s;
    }
    return -1u;
  }() == -1u) && "Aut is no complete");

  auto res = spot::make_twa_graph(aut->get_dict());
  res->set_buchi();
  res->prop_state_acc(true);
  for (const auto& ap : aut->ap())
    res->register_ap(ap);
  // Which one
  //res->get_dict()->register_all_variables_of(aut, res);


  auto& resr = *res;
  auto& autr = *aut;

  using set = std::vector<unsigned>;
  // Hash the set
  auto v_hash = [](const set& s) -> size_t{
    size_t h1 = spot::fnv_hash(s.cbegin(), s.cend());
    // Last op was mult with prime -> we can xor with hashed size
    return h1 ^ (spot::wang32_hash(s.size()));
  };
  // Set of original states -> new state
  // todo use bidirectional dict
  using dict_t = std::unordered_map<set, unsigned, decltype(v_hash)>;

  auto dict = dict_t();
  dict.reserve(2*autr.num_states());
  auto waiting = std::deque<set>{};

  auto get_state = [&](const set& s){
    auto [it, ins] = dict.emplace(s, resr.num_states());
    if (ins){
      waiting.push_back(it->first);
      unsigned ns = resr.new_state();
      assert(ns == it->second);
    }
    return it->second;
  };

  get_state(set{autr.get_init_state_number()});

  auto current_part = spot::bdd_partition(autr.get_dict(), autr.ap(), autr.ap_vars());
  // Assign to each leave of the implication graph, associate a new set (of old states)
  auto current_succ = std::unordered_map<unsigned, set>();

  auto insert_if = [](auto& v, const auto& e){
    if (std::find(v.cbegin(), v.cend(), e) == v.cend())
      v.push_back(e);
  };

  while (!waiting.empty()){
    set current_old = std::move(waiting.front());
    waiting.pop_front();
    // Get the corresponding new_state
    unsigned current_new = get_state(current_old);

    // Collect all conditions of all old states and partition them
    current_part.reset();
    for (unsigned s_old : current_old)
      for (const auto& e : autr.out(s_old))
        current_part.add_condition(e.cond);
    // This is neither flat nor ordered
    // Get the implication graph
    auto& c_ig = current_part.get_graph();
    // Traverse it and add the states
    current_succ.clear();
    auto traverse = [&](unsigned sig, unsigned dst, auto&& traverse_) -> void{
      auto itb = c_ig.out(sig).begin();
      if (itb){
        for (; itb; ++itb)
          traverse_(itb->dst, dst, traverse_);
      } else {
        auto [it, _] = current_succ.emplace(sig, set{});
        insert_if(it->second, dst);
      }
    };
    // Traverse and build the new dict
    for (unsigned s_old : current_old)
      for (const auto& e : autr.out(s_old))
        traverse(current_part.orig_conditions().at(e.cond), e.dst, traverse);

    // we need to sort all the sets, then we can construct the transitions
    for (auto& [_, s] : current_succ)
      std::sort(s.begin(), s.end());

    // Now construct all the transitions
    for (const auto& [leaf, succset] : current_succ)
      // Get the corresponding condition and state
      resr.new_edge(current_new, get_state(succset), c_ig.state_data(leaf).orig_label);
  }

  // Mark the accepting states
  auto has_common = [](const auto& s1, const auto& s2) -> bool{
    auto it1 = s1.cbegin();
    auto it2 = s2.cbegin();
    auto it1e = s1.cend();
    auto it2e = s2.cend();

    while((it1 != it1e) && (it2 != it2e)){
      if (*it1 == *it2)
        return true;
      if (*it1 < *it2)
        ++it1;
      else
        ++it2;
    }
    return false;
  };

  // Get a list of accepting states of the original
  auto acc_old = std::vector<unsigned>{};
  const unsigned Nold = autr.num_states();
  for (unsigned s = 0; s < Nold; ++s)
    if (autr.state_is_accepting(s))
      acc_old.push_back(s);

  // Mark all sets that intercept as accepting
  for (const auto& [olds, news] : dict){
    if (has_common(olds, acc_old)){
      auto it = resr.out(news).begin();
      if (!it)
        resr.new_edge(news, news, bddfalse, {0});
      else {
        for (; it; ++it)
          it->acc = spot::acc_cond::mark_t({0});
      }
    }
  }

  spot::print_hoa(std::cout, res);

  //assert(nfa_equal(aut, res).first == 0);

  return res;
}

spot::twa_graph_ptr dfa_complement(const spot::const_twa_graph_ptr& dfa){
  auto res = spot::make_twa_graph(dfa, spot::twa::prop_set::all());
  res->copy_acceptance_of(dfa);
  res->copy_ap_of(dfa);

  auto& rr = *res;

  const unsigned N = rr.num_states();

  auto get_sink = [&rr](){
    static unsigned s = -1u;
    if (s == -1u){
      s = rr.new_state();
      rr.new_edge(s, s, bddfalse);
    }
    return s;
  };

  for (unsigned s = 0; s < N; ++s){
    bool isacc = rr.state_is_accepting(s); // Accepting before -> Non-accepting after
    bdd rem = bddtrue;
    auto m = isacc ? spot::acc_cond::mark_t()
                   : spot::acc_cond::mark_t({0});
    for (auto& e : rr.out(s)){
      rem -= e.cond; // Mark conditions as treated
      e.acc = m; // invert acceptance
    }
    if (isacc && (rem != bddfalse))
      // Goto sink
      rr.new_edge(s, get_sink(), rem, {});
    else if (rem != bddfalse)
      // If it was not accepting before, but is
      // accepting now, we can simply loop
      // on the accepting state with all remaining
      rr.new_edge(s, s, rem, {0});
  }
  // Done
  return res;
}
