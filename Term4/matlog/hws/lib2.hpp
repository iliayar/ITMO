#pragma once

#include <type_traits>

template <int a, int b> struct equals { static constexpr bool value = a == b; };

struct Z {
  static int eval(int x) { return 0; }
};

struct N {
  static int eval(int x) { return x + 1; }
};

template <typename g, typename... f> struct S {
  template <typename... Args> static int eval(Args... xs) {
    return g::eval(f::eval(xs...)...);
  }
};

template <int l> struct P {

  template <int i, typename... Args>
  static typename std::enable_if<!equals<l, i>::value, int>::type
  get_ith(int x, Args... xs) {
    return get_ith<i + 1>(xs...);
  }

  template <int i, typename... Args>
  static typename std::enable_if<equals<l, i>::value, int>::type
  get_ith(int x, Args... xs) {
    return x;
  }

  template <typename... Args> static int eval(Args... xs) {
    return get_ith<1>(xs...);
  }
};

template <typename f, typename g> struct R {
  template <typename... Args> static int eval(int y, Args... xs) {
    if (y == 0) {
      return f::eval(xs...);
    } else {
      return g::eval(y - 1, R<f, g>::eval(y - 1, xs...), xs...);
    }
  }
};
