#pragma once

struct Z {
  template <int _ = 0> struct eval {
    enum { value = 0 };
  };
};

struct N {
  template <int x> struct eval {
    enum { value = x + 1 };
  };
};

template <typename g, typename... fs> struct S {

  template <int... xs> using _g = typename g::eval<xs...>;

  template <typename f, int... xs> using _f = typename f::eval<xs...>;

  template <int... xs> struct eval {
    enum { value = _g<_f<fs, xs...>::value...>::value };
  };
};

template <int l> struct P {

  template <int i, int x, int... xs> struct eval_impl {
    enum { value = eval_impl<i + 1, xs...>::value };
  };

  template <int x, int... xs> struct eval_impl<l, x, xs...> {
    enum { value = x };
  };

  template <int... xs> struct eval {
    enum { value = eval_impl<1, xs...>::value };
  };
};

template <typename f, typename g> struct R {

  template <int... xs> using _g = typename g::eval<xs...>;

  template <int... xs> using _f = typename f::eval<xs...>;

  template <int y, int... xs> struct eval {
    enum {
      value = _g<y - 1, R<f, g>::eval<y - 1, xs...>::value, xs...>::value
    };
  };

  template <int... xs> struct eval<0, xs...> {
    enum { value = _f<xs...>::value };
  };
};
