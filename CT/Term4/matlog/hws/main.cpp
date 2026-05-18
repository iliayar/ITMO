#include "lib.hpp"

#include <iostream>

template <typename f, int... ns>
using map = S<f, P<ns>...>;

using const1 = S<N, Z>;
using plus2 = S<N, N>;
using plus3 = S<N, plus2>;
using sum = R<P<1>, map<N, 2>>;
using times2 = S<sum, P<1>, P<1>>;

using mult = R<Z, map<sum, 2, 3>>;
using dec = S<R<Z, P<1>>, P<1>, Z>;
using sub = S<R<P<1>, S<dec, P<2>>>, P<2>, P<1>>;

template<int i, int j>
using subS = S<R<P<1>, S<dec, P<2>>>, P<j>, P<i>>;

using divS = S<R<Z, S<N, divS>>, subS<3, 4>, subS<3, 4>, P<4>>
// using div = S<divS, P<1>, Z, P<1>, P<2>>

template <typename expr, int... xs>
void print() {
    using _expr = typename expr::template eval<xs...>;
    std::cout << _expr::value << std::endl;
}

int main() {
    print<sub, 23, 5>();
    return 0;
}
