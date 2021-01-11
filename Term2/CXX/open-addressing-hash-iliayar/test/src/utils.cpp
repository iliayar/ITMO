#include "utils.h"

namespace test_utils {

std::size_t ConstructionAware::constructor_calls = 0;
std::size_t ConstructionAware::copy_constructor_calls = 0;
std::size_t ConstructionAware::move_constructor_calls = 0;
std::size_t ConstructionAware::copy_assignment_calls = 0;
std::size_t ConstructionAware::move_assignment_calls = 0;

} // test_utils namespace
