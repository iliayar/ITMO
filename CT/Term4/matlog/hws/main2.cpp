#include "lib2.hpp"

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
using div = S<divS, P<1>, Z, P<1>, P<2>>

// divR' = S (R Z (S N [divR'])) [subR' 3 4, subR' 3 4, P 4]
// divR = S divR' [P 1, Z, P 1, P 2]

int main() {
    std::cout << div::eval(32, 3) << std::endl;
    return 0;
}
