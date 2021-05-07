#include "lib.hpp"

#include <iostream>

template <typename f, int n>
using map = S<f, P<n>>;

using const1 = S<N, Z>;
using plus2 = S<N, N>;
using plus3 = S<N, plus2>;
using sum = R<P<1>, map<N, 2>>;
using times2 = S<sum, P<1>, P<1>>;

template <typename expr, int... xs>
void print() {
    using _expr = typename expr::eval<xs...>;
    std::cout << _expr::value << std::endl;
}

int main() {
    print<times2, 100>();
    return 0;
}
