#define CATCH_CONFIG_MAIN
#include <catch2/catch_all.hpp>

#include "../nfa_translate.h"
#include "../nfa_helper.h"

TEST_CASE("Testing boolean binary") {

}

TEST_CASE("Testing all unary base operators") {
  for (std::string op : {""})
  REQUIRE(nfa_equal().first == 0);
  REQUIRE((2 + 2) == 4);
  REQUIRE((-1 + 1) == 0);
}
