// BUG: WA 2
#pragma GCC optimize("Ofast")
#pragma GCC optimize("no-stack-protector")
#pragma GCC optimize("unroll-loops")
#pragma GCC optimize("fast-math")

#include <algorithm>
#include <array>
#include <bit>
#include <bitset>
#include <iomanip>
#include <iostream>
#include <optional>
#include <random>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#ifdef DEBUG
#define IS_DEBUG true
#define DBG_OPT(name, enabled)                                                 \
  if (enabled)                                                                 \
  std::cout << "DBG[" #name "]: "
#else
#define IS_DEBUG false
#define DBG_OPT(name, enabled)                                                 \
  if (false)                                                                   \
  std::cout
#endif

#define DBG(name) DBG_OPT(name, true)

#define PARAM(expr) #expr "=" << (expr) << ", "

#define INF 1000000

template <typename K, typename V> struct map_pair {
  K k;
  V v;
};

template <typename T> class Join;

template <typename A, typename B, typename C>
std::ostream &operator<<(std::ostream &out, std::tuple<A, B, C> const &t) {
  auto [e1, e2, e3] = t;
  out << "(" << e1 << ", " << e2 << ", " << e3 << ")";
  return out;
}

template <typename A, typename B>
std::ostream &operator<<(std::ostream &out, std::tuple<A, B> const &t) {
  auto [f, s] = t;
  out << "(" << f << ", " << s << ")";
  return out;
}

template <typename A>
std::ostream &operator<<(std::ostream &out, std::tuple<A> const &t) {
  std::vector v{std::get<0>(t)};
  out << "(" << Join(v, ", ") << ")";
  return out;
}

template <typename K>
std::ostream &operator<<(std::ostream &out, std::unordered_set<K> const &s) {
  out << "{" << Join(s, ", ") << "}";
  return out;
}

template <typename T>
std::ostream &operator<<(std::ostream &out, std::vector<T> const &v) {
  out << "[" << Join(v, ", ") << "]";
  return out;
}

template <typename T, unsigned long n>
std::ostream &operator<<(std::ostream &out, std::array<T, n> const &arr) {
  out << "[" << Join(arr, ", ") << "]";
  return out;
}

template <typename T, typename K>
std::ostream &operator<<(std::ostream &out, std::pair<T, K> const &p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

template <typename K, typename V>
std::ostream &operator<<(std::ostream &out, std::unordered_map<K, V> const &m) {
  std::vector<map_pair<K, V>> v;
  std::transform(m.begin(), m.end(), std::back_inserter(v),
                 [](std::pair<K, V> const &p) {
                   return map_pair<K, V>{p.first, p.second};
                 });
  out << "{" << Join(v, ", ") << "}";
  return out;
}

template <typename K, typename V>
std::ostream &operator<<(std::ostream &out, map_pair<K, V> const &m) {
  out << m.k << ": " << m.v;
  return out;
}

template <typename T> class Join {
  T const &v;
  std::string const &separator;

public:
  Join(T const &v, std::string const &separator) : v(v), separator(separator) {}

  friend std::ostream &operator<<(std::ostream &out, Join<T> const &join) {
    for (auto it = join.v.cbegin(); it != join.v.cend(); ++it) {
      if (it != join.v.cbegin())
        out << join.separator;
      out << *it;
    }
    return out;
  }
};

#define assert(cond, msg)                                                      \
  if (!(cond)) {                                                               \
    std::cerr << "assertion (" << #cond << ") failed: " << msg << std::endl;   \
    exit(1);                                                                   \
  }

#ifdef DEBUG
#define DBG_ASSERT(c, msg) assert((c), (msg));
#else
#define DBG_ASSERT(c, msg)
#endif

struct GenericFF {
  int v_;
};

auto operator""_f(unsigned long long v) -> GenericFF {
  return {static_cast<int>(v)};
}

template <int n> class FF {
public:
  explicit FF<n>(int v) : v_(v % n) {}
  FF<n>(GenericFF v) : v_(v.v_) {
    assert(v.v_ < n, "implicitly constructing finite field item out of range");
  }

  auto operator+(FF<n> rhs) -> FF<n> { return FF<n>(v_ + rhs.v_); }

  auto operator*(FF<n> rhs) const -> FF<n> { return FF<n>(v_ * rhs.v_); }

  auto pow(int q) const -> FF<n> { return FF<n>(std::pow(v_, q)); }

  auto operator==(FF<n> const &other) const -> bool { return v_ == other.v_; }
  auto operator!=(FF<n> const &other) const -> bool {
    return !(*this == other);
  }

  friend auto operator<<(std::ostream &out, FF<n> rhs) -> std::ostream & {
    auto max_len = std::to_string(n).length();
    out << std::setfill(' ') << std::setw(max_len) << rhs.v_;
    return out;
  }

  friend auto operator>>(std::istream &in, FF<n> &rhs) -> std::istream & {
    int v;
    in >> v;
    rhs.v_ = v % n;
    return in;
  }

  friend auto std::hash<FF<n>>::operator()(FF<n> const &v) const -> std::size_t;

private:
  int v_;
};

template <int n> struct std::hash<FF<n>> {
  auto operator()(FF<n> const &v) const -> std::size_t { return v.v_; }
};

template <typename T, typename V> class vec_mixin {
public:
  virtual auto shape() const -> std::tuple<int> = 0;
  virtual auto get(int i) const -> T = 0;

  auto operator+(V const &other) const -> V {
    auto [s] = shape();
    auto [n] = other.shape();
    assert(s == n, "cannot add vectors with different size");
    auto res = V::zero(s);
    for (int i = 0; i < s; ++i) {
      res.set(i, get(i) + other.get(i));
    }
    return res;
  }

  auto operator*(V const &other) const -> V {
    auto [s] = shape();
    auto [n] = other.shape();
    assert(s == n, "cannot multiply vectors with different size");

    auto res = V::zero(s);
    for (int i = 0; i < s; ++i) {
      res.set(i, get(i) * other.get(i));
    }
    return res;
  }

  auto operator==(V const &other) const -> bool {
    auto [n] = shape();
    for (int i = 0; i < n; i++) {
      if (get(i) != other.get(i))
        return false;
    }
    return true;
  }
  auto operator!=(V const &other) const -> bool { return !(*this == other); }

  friend auto operator<<(std::ostream &out, V const &v) -> std::ostream & {
    auto [n] = v.shape();
    out << "|";
    for (int i = 0; i < n; ++i) {
      out << v.get(i);
      if (i != n - 1)
        out << " ";
    }
    out << "|";
    return out;
  }

  friend auto operator>>(std::istream &in, V &v) -> std::istream & {
    auto [n] = v.shape();
    for (int i = 0; i < n; ++i) {
      T n = T(0);
      in >> n;
      v.set(i, n);
    }
    return in;
  }
};

template <typename T> class vec : public vec_mixin<T, vec<T>> {
public:
  explicit vec(std::vector<T> data)
      : data_(std::move(data)), size_(data_.size()) {}

  static auto zero(int size, T zero_val = T(0)) -> vec {
    std::vector<T> data(size, zero_val);
    return vec(std::move(data));
  }

  static auto one(int size, T one_val = T(1)) -> vec {
    std::vector<T> data(size, one_val);
    return vec(std::move(data));
  }

  auto shape() const -> std::tuple<int> { return {size_}; }

  auto get(int i) const -> T { return data_[i]; }

  auto set(int i, T v) { data_[i] = v; }

  friend auto std::hash<vec<T>>::operator()(vec<T> const &v) const
      -> std::size_t;

private:
  std::vector<T> data_;
  int size_;
};

template <typename T> struct std::hash<vec<T>> {
  auto operator()(vec<T> const &v) const -> std::size_t {
    auto [n] = v.shape();
    std::size_t res = 0;
    for (int i = 0; i < n; ++i) {
      res += std::hash<T>()(v.get(i));
    }
    return res;
  }
};

class bitvec;
namespace std {
template <> struct hash<bitvec> {
  auto operator()(bitvec const &v) const -> std::size_t;
};
} // namespace std

class bitvec : public vec_mixin<FF<2>, bitvec> {
public:
  // static constexpr int SIZE = 1024;
  // using Inner = std::bitset<SIZE>;

  using Inner = std::int64_t;
  static constexpr int SIZE = sizeof(Inner) * 8;

  explicit bitvec(Inner data, int size) : data_(data), size_(size) {
    DBG_OPT("bitvec::bitvec", false) << PARAM(size_) << std::endl;
    assert(size_ < SIZE, "Size too large for inner type");
  }
  static auto zero(int size, FF<2> zero = 0_f) -> bitvec {
    DBG_OPT("bitvec::zero", false) << PARAM(size) << std::endl;
    return bitvec(Inner(0), size);
  }
  static auto one(int size, FF<2> one = 1_f) -> bitvec {
    // return bitvec(~Inner(0), size);
    return bitvec(~Inner(0) & ((Inner(1) << size) - 1), size);
  }

  static auto from_vec(vec<FF<2>> vec) -> bitvec {
    auto [n] = vec.shape();
    auto r = bitvec::zero(n);
    for (int i = 0; i < n; ++i) {
      r.set(i, vec.get(i));
    }
    return r;
  };

  auto to_vec() -> vec<FF<2>> {
    auto [n] = shape();
    auto r = vec<FF<2>>::zero(n);
    for (int i = 0; i < n; ++i) {
      r.set(i, get(i));
    }
    return r;
  }

  auto inner() const -> Inner { return data_; }

  auto shape() const -> std::tuple<int> { return {size_}; }

  auto get(int i) const -> FF<2> {
    assert(i < size_, "bitvec out of range");
    // return FF<2>(data_[i]);
    return FF<2>((data_ >> i) & 1);
  }

  void set(int i, FF<2> val) {
    assert(i < size_, "bitvec out of range");
    if (val == 0_f) {
      // data_[i] = 0;
      data_ &= ~((Inner(1)) << i);
    } else {
      // data_[i] = 1;
      data_ |= Inner(1) << i;
    }
  }

  friend struct std::hash<bitvec>;

  auto operator==(bitvec const &other) const -> bool {
    return size_ == other.size_ && inner() == other.inner();
  }
  auto operator!=(bitvec const &other) const -> bool {
    return !(*this == other);
  }

  friend auto std::hash<bitvec>::operator()(bitvec const &v) const
      -> std::size_t;

private:
  Inner data_;
  int size_;
};

auto std::hash<bitvec>::operator()(bitvec const &v) const -> std::size_t {
  return std::hash<bitvec::Inner>()(v.data_);
}

///////////////////////////////////////////////////////////////

struct symb;
namespace std {
template <> struct hash<symb> {
  auto operator()(symb const &v) const -> std::size_t;
};
} // namespace std

struct symb {
  explicit symb(char c) : c_(c) {}

  auto operator==(symb const &other) const -> bool { return c_ == other.c_; }
  auto operator!=(symb const &other) const -> bool { return !(*this == other); }

  friend auto operator<<(std::ostream &out, symb const &s) -> std::ostream & {
    out << s.c_;
    return out;
  }

  friend auto std::hash<symb>::operator()(symb const &v) const -> std::size_t;

  char c_;
};

auto std::hash<symb>::operator()(symb const &v) const -> std::size_t {
  return v.c_;
}

template <typename V> auto find_largest_one(V v, int max = -1) -> int {
  auto [n] = v.shape();
  int res = 0;
  for (int i = 0; i < n; ++i) {
    if (v.get(i) != 0_f) {
      res = i;
    }
  }
  return res;
}

// template <>
// auto find_largest_one<bitvec::Inner>(bitvec::Inner v, int max) -> int {
//   int res = 0;
//   int lim = max == -1 ? v.size() : std::max(v.size(), std::size_t(max));
//   for (int i = 0; i < lim; ++i) {
//     if (v[i] != 0) {
//       res = i;
//     }
//   }
//   return res;
// }
//

double sgn(double x) {
  if (x > 0)
    return 1.;
  if (x < 0)
    return -1.;
  if (x == 0)
    return 0;
}

template <>
auto find_largest_one<bitvec::Inner>(bitvec::Inner v, int max) -> int {
  if (v == 0)
    return 0;
  return sizeof(bitvec::Inner) * 8 - std::__countl_zero(v) - 2;
}

template <typename T> struct Factory {
  virtual auto one() const -> T = 0;
  virtual auto zero() const -> T = 0;
  virtual auto var() const -> T = 0;
};

template <int n> struct FFFactory : Factory<FF<n>> {
  auto one() const -> FF<n> { return 1_f; }
  auto zero() const -> FF<n> { return 0_f; }
  auto var() const -> FF<n> { assert(false, "unimplemented"); }
};

struct PrimitiveFactory {};

template <typename T> struct vpoly {

  explicit vpoly(vec<T> data, symb s, int deg, Factory<T> *factory)
      : data_(std::move(data)), s_(s), deg_(deg), factory_(factory) {}

  static auto from_vec(vec<T> v, symb s, Factory<T> *factory) -> vpoly {
    auto [n] = v.shape();
    DBG_ASSERT(find_largest_one(v) == n - 1,
               "Vector size is larger then actual degree");
    return vpoly(std::move(v), s, n - 1, factory);
  }

  static auto zero(symb s, Factory<T> *factory) -> vpoly {
    auto v = vec<T>::zero(1, factory->zero());
    return vpoly(std::move(v), s, 0, factory);
  }

  static auto one(symb s, Factory<T> *factory) -> vpoly {
    auto v = vec<T>::one(1, factory->one());
    return vpoly(std::move(v), s, 0, factory);
  }

  static auto var(symb s, Factory<T> *factory) -> vpoly {
    auto v = vec<T>::zero(2, factory->zero());
    v.set(1, factory->one());
    return vpoly(std::move(v), s, 1, factory);
  }

  auto get(int i) const -> T { return data_.get(i); }

  auto deg() const -> int { return deg_; }
  auto var() const -> symb { return s_; }

  auto subst(symb s) -> vpoly {
    auto res = *this;
    res.s_ = s;
    return res;
  }

  auto operator*(vpoly const &rhs) const -> vpoly {
    assert(s_ == rhs.s_, "Multipling polynoms with different symbols");

    auto z = factory_->zero();

    auto ld = deg();
    auto rd = rhs.deg();

    auto res = vec<T>::zero(ld + rd + 1, factory_->zero());
    auto res_d = 0;
    for (int i = 0; i <= ld; i++) {
      if (data_.get(i) == z)
        continue;
      for (int j = 0; j <= rd; j++) {
        if (rhs.data_.get(j) == z)
          continue;
        auto v = res.get(i + j) + data_.get(i) * rhs.data_.get(j);
        res.set(i + j, v);

        if (v != z) {
          res_d = std::max(res_d, i + j);
        }
      }
    }

    return vpoly(std::move(res), s_, res_d, factory_);
  }

  auto multiply_mod(vpoly const &rhs, vpoly const &mod) const -> vpoly {
    return (*this * rhs).rem(mod);
  }

  friend auto operator*(T const &lhs, vpoly const &rhs) -> vpoly {
    auto d = rhs.deg();
    auto res = vec<T>::zero(d + 1, rhs.factory_->zero());
    auto res_d = 0;
    for (int i = 0; i <= d; ++i) {
      auto v = rhs.data_.get(i) * lhs;
      res.set(i, v);

      if (v != rhs.factory_->zero())
        res_d = i;
    }
    return vpoly(std::move(res), rhs.s_, res_d, rhs.factory_);
  }

  auto operator+(vpoly const &rhs) const -> vpoly {
    auto d = std::max(deg(), rhs.deg());
    auto res = vec<T>::zero(d + 1, factory_->zero());
    auto res_d = 0;
    for (int i = 0; i <= d; ++i) {
      T v1 = factory_->zero();
      T v2 = factory_->zero();
      if (i <= deg()) {
        v1 = data_.get(i);
      }
      if (i <= rhs.deg()) {
        v2 = rhs.data_.get(i);
      }
      auto v = v1 + v2;
      res.set(i, v);

      if (v != factory_->zero())
        res_d = i;
    }
    return vpoly(std::move(res), s_, res_d, factory_);
  }

  auto pow(int p) const -> vpoly {
    assert(p >= 0, "pow works only with non negatives");

    auto b = *this;
    auto res = vpoly::one(s_, factory_);

    while (p != 0) {
      if (p % 2 != 0) {
        res = res * b;
      }
      b = b * b;
      p /= 2;
    }

    return res;
  }

  auto pow_mod(int p, vpoly const &mod) const -> vpoly {
    return pow(p).rem(mod);
  }

  auto rem(vpoly const &div) const -> vpoly {
    if (div == vpoly::one(s_, factory_)) {
      return vpoly::zero(s_, factory_);
    }

    auto res = *this;
    auto px = vpoly::var(s_, factory_);

    while (res.deg() >= div.deg()) {
      DBG_OPT("vpoly::rem", false)
          << PARAM(res.deg()) << PARAM(div.deg()) << std::endl;
      res = res + div * px.pow(res.deg() - div.deg());
    }

    return res;
  }

  auto eval(T const &x) const -> T {
    auto z = factory_->zero();
    auto res = factory_->zero();

    for (int i = 0; i <= deg_; ++i) {
      if (data_.get(i) == z)
        continue;
      res = res + data_.get(i) * x.pow(i);
    }

    return res;
  }

  auto operator==(vpoly const &other) const -> bool {
    if (deg_ != other.deg_)
      return false;
    if (s_ != other.s_)
      return false;

    for (int i = 0; i <= deg_; ++i) {
      if (data_.get(i) != other.data_.get(i))
        return false;
    }

    return true;
  }

  friend auto operator<<(std::ostream &out, vpoly const &p) -> std::ostream & {
    auto deg = p.deg();
    assert(p.data_.get(deg) != p.factory_->zero() || deg == 0,
           "Polynom degree is inconsistent");
    auto was = false;
    for (int i = deg; i >= 0; --i) {
      if (p.data_.get(i) != p.factory_->zero()) {
        was = true;
        if (i != deg)
          out << " + ";

        if (i == 0) {
          out << p.data_.get(i);
        } else {
          if (p.data_.get(i) != p.factory_->one())
            out << "(" << p.data_.get(i) << ")"
                << "*";
          out << p.var();

          if (i > 1) {
            out << "^" << i;
          }
        }
      }
    }

    if (!was)
      out << "0";

    return out;
  }

  friend auto std::hash<vpoly<T>>::operator()(vpoly<T> const &v) const
      -> std::size_t;

  static auto from_vec2(vec<FF<2>> v, symb s, Factory<T> *factory) -> vpoly<T> {
    auto [n] = v.shape();
    auto res = vec<T>::zero(n, factory->zero());
    auto res_d = 0;
    for (int i = 0; i < n; ++i) {
      if (v.get(i) == 1_f) {
        res.set(i, factory->one());
        res_d = i;
      }
    }
    return vpoly(std::move(res), s, res_d, factory);
  }

  auto to_vec2(int n = -1) -> vec<FF<2>> {
    if (n == -1)
      n = deg() + 1;
    assert(n >= deg(), "out of bounds to_vec2");

    auto res = vec<FF<2>>::zero(n);
    for (int i = 0; i <= deg_; ++i) {
      if (data_.get(i) == factory_->one()) {
        res.set(i, 1_f);
      } else if (data_.get(i) == factory_->zero()) {
        res.set(i, 0_f);
      } else {
        assert(false, "Must be either 1 or 0 to convert to vec2");
      }
    }

    return res;
  }

  vec<T> data_;
  symb s_;
  int deg_;
  Factory<T> *factory_;
};

template <typename T> struct std::hash<vpoly<T>> {
  auto operator()(vpoly<T> const &p) const -> std::size_t {
    return std::hash<vec<T>>()(p.data_);
  }
};

struct bitpoly;
namespace std {
template <> struct hash<bitpoly> {
  auto operator()(bitpoly const &p) const -> std::size_t;
};
} // namespace std

struct bitpoly {

  explicit bitpoly(bitvec data, symb s, int deg, Factory<FF<2>> *factory)
      : data_(std::move(data)), s_(s), deg_(deg), factory_(factory) {}

  static auto from_vec(bitvec v, symb s, Factory<FF<2>> *factory) -> bitpoly {
    auto [n] = v.shape();
    DBG_ASSERT(find_largest_one(v) == n - 1,
               "Vector size is larger then actual degree");
    return bitpoly(std::move(v), s, n - 1, factory);
  }

  static auto zero(symb s, Factory<FF<2>> *factory) -> bitpoly {
    auto v = bitvec::zero(1, factory->zero());
    return bitpoly(std::move(v), s, 0, factory);
  }

  static auto one(symb s, Factory<FF<2>> *factory) -> bitpoly {
    auto v = bitvec::zero(1, factory->one());
    v.set(0, 1_f);
    return bitpoly(std::move(v), s, 0, factory);
  }

  static auto var(symb s, Factory<FF<2>> *factory) -> bitpoly {
    auto v = bitvec::zero(2, factory->zero());
    v.set(1, factory->one());
    return bitpoly(std::move(v), s, 1, factory);
  }

  auto get(int i) const -> FF<2> { return data_.get(i); }

  auto deg() const -> int { return deg_; }
  auto var() const -> symb { return s_; }

  auto subst(symb s) -> bitpoly {
    auto res = *this;
    res.s_ = s;
    return res;
  }

  auto multiply_mod(bitpoly const &rhs, bitpoly const &mod) const -> bitpoly {
    assert(s_ == rhs.s_, "Multipling polynoms with different symbols");

    auto md = mod.deg();

    auto mi = mod.data_.inner();
    auto lhsi = data_.inner();
    auto rhsi = rhs.data_.inner();
    bitvec::Inner res(0);

    auto prev_rd = rhs.deg();
    while (lhsi != 0) {
      if (lhsi & 1) {
        res ^= rhsi;
      }

      lhsi >>= 1;
      rhsi <<= 1;
      prev_rd += 1;

      if (prev_rd == md) {
        rhsi ^= mi;
        prev_rd = find_largest_one(rhsi, md);
      }
    }

    auto res_d = find_largest_one(res, md);

    auto v = bitvec(res, res_d + 1);
    return bitpoly(v, s_, res_d, factory_);
  }

  friend auto operator*(FF<2> const &lhs, bitpoly const &rhs) -> bitpoly {
    auto d = rhs.deg();
    auto res = bitvec::zero(d + 1, rhs.factory_->zero());
    auto res_d = 0;
    for (int i = 0; i <= d; ++i) {
      auto v = rhs.data_.get(i) * lhs;
      res.set(i, v);

      if (v != rhs.factory_->zero())
        res_d = i;
    }
    return bitpoly(std::move(res), rhs.s_, res_d, rhs.factory_);
  }

  auto operator*(bitpoly const &rhs) const -> bitpoly {
    assert(s_ == rhs.s_, "Multipling polynoms with different symbols");

    auto ld = deg();
    auto rd = rhs.deg();

    auto lhsi = data_.inner();
    auto rhsi = rhs.data_.inner();
    bitvec::Inner res(0);

    int i = 0;
    while (rhsi != 0) {
      if (rhsi & 1) {
        res ^= lhsi << i;
      }
      rhsi >>= 1;
      i += 1;
    }

    // auto max_d = find_largest_one(res);
    DBG_OPT("bitpoly::operator* 1", false) << PARAM(ld + rd + 1) << std::endl;
    auto v = bitvec(res, ld + rd + 1);
    // DBG_OPT("bitpoly::operator* 2", false)
    //     << PARAM(ld + rd + 1) << PARAM(max_d) << std::endl;
    return bitpoly(v, s_, ld + rd, factory_);
  }

  auto operator+(bitpoly const &rhs) const -> bitpoly {
    auto d = std::max(deg(), rhs.deg());

    auto ld = deg();
    auto rd = rhs.deg();

    auto lhsi = data_.inner();
    auto rhsi = rhs.data_.inner();
    bitvec::Inner res = lhsi ^ rhsi;

    auto max_d = find_largest_one(res, d + 1);
    auto v = bitvec(res, max_d + 1);
    return bitpoly(v, s_, max_d, factory_);
  }

  auto pow(int p) const -> bitpoly {
    auto res = bitpoly::one(s_, factory_);
    auto b = *this;
    while (p != 0) {
      if (p % 2 != 0) {
        res = res * b;
      }
      b = b * b;
      p /= 2;
    }
    return res;
  }

  auto pow_mod(int p, bitpoly const &mod) const -> bitpoly {
    auto res = bitpoly::one(s_, factory_);
    auto b = *this;
    while (p != 0) {
      if (p % 2 != 0) {
        res = res.multiply_mod(b, mod);
      }
      b = b.multiply_mod(b, mod);
      p /= 2;
    }
    return res;
  }

  auto rem_impl(bitvec::Inner si, bitpoly const &div) const
      -> std::tuple<bitvec::Inner, int> {
    auto dd = div.deg();
    auto divi = div.data_.inner();

    auto prev_d = deg();
    while (true) {
      auto idx = find_largest_one(si, prev_d + 1);
      prev_d = idx;

      if (idx < dd)
        break;

      si ^= divi << (idx - dd);
    }

    return {si, prev_d};
  }

  auto rem(bitpoly const &div) const -> bitpoly {
    auto [si, d] = rem_impl(data_.inner(), div);

    return bitpoly(bitvec(si, d + 1), s_, d, factory_);
  }

  auto eval(FF<2> const &x) const -> FF<2> {
    auto res = factory_->zero();

    for (int i = 0; i <= deg_; ++i) {
      res = res + data_.get(i) * x.pow(i);
    }

    return res;
  }

  auto operator==(bitpoly const &other) const -> bool {
    if (deg_ != other.deg_)
      return false;
    if (s_ != other.s_)
      return false;

    if (data_ != other.data_) {
      return false;
    }

    return true;
  }

  friend auto operator<<(std::ostream &out, bitpoly const &p)
      -> std::ostream & {
    auto deg = p.deg();
    assert(p.data_.get(deg) != p.factory_->zero() || deg == 0,
           "Polynom degree is inconsistent");
    auto was = false;
    for (int i = deg; i >= 0; --i) {
      if (p.data_.get(i) != p.factory_->zero()) {
        was = true;
        if (i != deg)
          out << " + ";

        if (i == 0) {
          out << p.data_.get(i);
        } else {
          if (p.data_.get(i) != p.factory_->one())
            out << "(" << p.data_.get(i) << ")"
                << "*";
          out << p.var();

          if (i > 1) {
            out << "^" << i;
          }
        }
      }
    }

    if (!was)
      out << "0";

    return out;
  }

  friend auto std::hash<bitpoly>::operator()(bitpoly const &v) const
      -> std::size_t;

  static auto from_vec2(vec<FF<2>> v, symb s, Factory<FF<2>> *factory)
      -> bitpoly {
    auto [n] = v.shape();
    auto res = bitvec::zero(n, factory->zero());
    auto res_d = 0;
    for (int i = 0; i < n; ++i) {
      if (v.get(i) == 1_f) {
        res.set(i, factory->one());
        res_d = i;
      }
    }
    return bitpoly(std::move(res), s, res_d, factory);
  }

  auto to_vec2(int n = -1) -> vec<FF<2>> {
    if (n == -1)
      n = deg() + 1;
    assert(n >= deg(), "out of bounds to_vec2");

    auto res = vec<FF<2>>::zero(n);
    for (int i = 0; i <= deg_; ++i) {
      if (data_.get(i) == factory_->one()) {
        res.set(i, 1_f);
      } else if (data_.get(i) == factory_->zero()) {
        res.set(i, 0_f);
      } else {
        assert(false, "Must be either 1 or 0 to convert to vec2");
      }
    }

    return res;
  }

  bitvec data_;
  symb s_;
  int deg_;
  Factory<FF<2>> *factory_;
};

auto std::hash<bitpoly>::operator()(bitpoly const &p) const -> std::size_t {
  return std::hash<bitvec>()(p.data_);
}

template <typename T> struct PolyFactory : Factory<vpoly<T>> {
  explicit PolyFactory(symb s, Factory<T> *inner_factory)
      : s_(s), inner_factory_(inner_factory) {}

  auto one() const -> vpoly<T> { return vpoly<T>::one(s_, inner_factory_); }
  auto zero() const -> vpoly<T> { return vpoly<T>::zero(s_, inner_factory_); }
  auto var() const -> vpoly<T> { return vpoly<T>::var(s_, inner_factory_); }

  symb s_;
  Factory<T> *inner_factory_;
};

struct BitPolyFactory : Factory<bitpoly> {
  explicit BitPolyFactory(symb s, Factory<FF<2>> *inner_factory)
      : s_(s), inner_factory_(inner_factory) {}

  auto one() const -> bitpoly { return bitpoly::one(s_, inner_factory_); }
  auto zero() const -> bitpoly { return bitpoly::zero(s_, inner_factory_); }
  auto var() const -> bitpoly { return bitpoly::var(s_, inner_factory_); }

  symb s_;
  Factory<FF<2>> *inner_factory_;
};

struct unchecked_t {};
static unchecked_t unchecked;

template <int n, typename P = vpoly<FF<n>>> class GF {
public:
  explicit GF<n, P>(P poly, P primitive_poly)
      : prim_(primitive_poly.subst(poly.var())), poly_(poly.rem(prim_)) {}

  explicit GF<n, P>(P poly, P primitive_poly, unchecked_t)
      : prim_(primitive_poly.subst(poly.var())), poly_(poly) {}

  // GF<T>(GenericFF v, symb s, P primitive_poly) {
  //   // TODO:
  // }

  auto operator+(GF<n, P> const &rhs) const -> GF<n, P> {
    DBG_ASSERT(rhs.prim_ == prim_, "operator+: Primitve polynoms don't match");
    return GF<n, P>((poly_ + rhs.poly_), prim_, unchecked);
  };

  auto operator*(GF<n, P> const &rhs) const -> GF<n, P> {
    DBG_OPT("GF::operator* 1", false)
        << PARAM(poly_) << PARAM(rhs.poly_) << std::endl;
    DBG_ASSERT(rhs.prim_ == prim_, "operator*: Primitve polynoms don't match");
    // return GF<n, P>((poly_ * rhs.poly_).rem(prim_), prim_);
    return GF<n, P>(poly_.multiply_mod(rhs.poly_, prim_), prim_, unchecked);
  }

  auto pow(int a) const -> GF<n, P> {
    // return GF<n, P>(poly_.pow(a).rem(prim_), prim_);
    return GF<n, P>(poly_.pow_mod(a, prim_), prim_, unchecked);
  }

  auto inv() const -> GF<n, P> {
    auto res = GF<n, P>(poly_.pow_mod(std::pow(n, prim_.deg()) - 2, prim_),
                        prim_, unchecked);
    DBG_OPT("GF<n>::inv", false)
        << PARAM(*this) << PARAM(res) << PARAM(*this * res) << std::endl;
    return res;
  }

  auto operator==(GF<n, P> const &other) const -> bool {
    return prim_ == other.prim_ && poly_ == other.poly_;
  };

  auto operator!=(GF<n, P> const &other) const -> bool {
    return !(*this == other);
  }

  friend auto operator<<(std::ostream &out, GF<n, P> rhs) -> std::ostream & {
    out << rhs.poly_;
    return out;
  }

  friend auto std::hash<GF<n, P>>::operator()(GF<n, P> const &v) const
      -> std::size_t;

private:
  P prim_;
  P poly_;
};

template <int n, typename P> struct std::hash<GF<n, P>> {
  auto operator()(GF<n, P> const &f) const -> std::size_t {
    return std::hash<P>()(f.poly_);
  }
};

template <int n, typename P = vpoly<FF<n>>>
struct GFFactory : Factory<GF<n, P>> {
  GFFactory(P primitive_poly, Factory<P> *poly_factory)
      : primitive_poly_(primitive_poly), poly_factory_(poly_factory) {}

  auto one() const -> GF<n, P> {
    return GF<n, P>(poly_factory_->one(), primitive_poly_);
  }

  auto zero() const -> GF<n, P> {
    return GF<n, P>(poly_factory_->zero(), primitive_poly_);
  }

  auto var() const -> GF<n, P> {
    return GF<n, P>(poly_factory_->var(), primitive_poly_);
  }

  P primitive_poly_;
  Factory<P> *poly_factory_;
};

void setup() {
  std::ios_base::sync_with_stdio(0);
  std::cin.tie(0);
  std::cerr.tie(0);
  std::cout.tie(0);
  freopen("input.txt", "r", stdin);
  if (!IS_DEBUG) {
    freopen("output.txt", "w", stdout);
  }
}

using F2 = FF<2>;
using F2_F = Factory<F2>;

using VF2 = vec<F2>;

// using PF2 = vpoly<F2>;
using PF2 = bitpoly;
using PF2_F = Factory<PF2>;

using GF2 = GF<2, PF2>;
using GF2_F = Factory<GF2>;

using PGF2 = vpoly<GF2>;
using PGF2_F = Factory<PGF2>;

auto log2(int n) -> int {
  int i = 0;
  while (true) {
    n /= 2;
    if (n == 0)
      break;
    i += 1;
  }
  return i;
}

//////////////////////////////////////////////

auto random_generator() -> auto & {
  static std::random_device rd;
  static std::mt19937 gen(rd());

  return gen;
}

template <typename T> auto rand_int_uniform_vec(int size) -> vec<T> {
  auto &gen = random_generator();
  static std::uniform_int_distribution distr;

  auto res = vec<T>::zero(size);
  for (int i = 0; i < size; ++i) {
    res.set(i, T(distr(gen)));
  }

  return res;
}

////////////////////////////////////////////////

template <typename Encoder, typename Decoder, typename ChannelFactory>
void handle_commands(Encoder const &encoder, Decoder const &decoder,
                     ChannelFactory const &channel_factory) {
  std::string line;
  while (std::getline(std::cin, line)) {
    std::stringstream ss(line);

    std::string cmd;
    ss >> cmd;

    if (cmd == "Encode") {
      auto v = vec<typename Encoder::ValueType>::zero(encoder.length());
      ss >> v;
      auto enc = encoder.encode(v);
      for (int i = 0; i < std::get<0>(enc.shape()); ++i) {
        std::cout << enc.get(i) << " ";
      }
      std::cout << std::endl;
    } else if (cmd == "Decode") {
      auto v = vec<typename Decoder::ValueType>::zero(decoder.length());
      ss >> v;
      auto w = decoder.decode(v, std::nullopt);
      for (int i = 0; i < std::get<0>(w.shape()); ++i) {
        std::cout << w.get(i) << " ";
      }
      std::cout << std::endl;
    } else if (cmd == "Simulate") {
      typename ChannelFactory::ParamType p;
      ss >> p;
      int max_iterations, max_errors;
      ss >> max_iterations >> max_errors;

      int total = 0, errors = 0;
      auto channel = channel_factory.create(p);

      for (; total < max_iterations && errors < max_errors; ++total) {
        auto w =
            rand_int_uniform_vec<typename Encoder::ValueType>(encoder.length());
        auto c = encoder.encode(w);
        DBG_OPT("handle_commands Simulate 1", false)
            << PARAM(w) << PARAM(c) << std::endl;
        auto r = channel.send(c);
        DBG_OPT("handle_commands Simulate 2", false) << PARAM(r) << std::endl;
        auto d = decoder.decode(r, p);
        DBG_OPT("handle_commands Simulate 3", false) << PARAM(d) << std::endl;
        if (d != c) {
          errors++;
        }
      }

      double error_rate = static_cast<double>(errors) / total;
      std::cout << error_rate << std::endl;
    }
  }
}

/////////////////////////////////////////////////////////////////

auto get_probs(double p, int m, int k) -> std::vector<double> {
  std::vector<std::vector<double>> probs;
  probs.push_back({p});

  for (int i = 1; i <= m; ++i) {
    int n = 1 << i;
    std::vector<double> cprobs(n);
    for (int j = 0; j < n; ++j) {
      if (j % 2 == 0)
        cprobs[j] = 1 - std::pow(1 - probs[i - 1][j / 2], 2);
      else
        cprobs[j] = std::pow(probs[i - 1][j / 2], 2);
    }
    probs.push_back(cprobs);
  }
  return probs[m];
}

auto get_freeze(double p, int m, int k) -> std::vector<int> {
  auto probs = get_probs(p, m, k);
  DBG_OPT("get_freeze 1", false) << PARAM(probs) << std::endl;

  std::vector<std::tuple<double, int>> probs_idxs;
  probs_idxs.reserve(1 << m);
  for (int i = 0; i < (1 << m); ++i) {
    probs_idxs.emplace_back(probs[i], i);
  }
  DBG_OPT("get_freeze 2", false) << PARAM(probs_idxs) << std::endl;
  std::sort(probs_idxs.begin(), probs_idxs.end(),
            [](const auto &r, const auto &l) {
              auto &[pr, ir] = r;
              auto &[pl, il] = l;
              return pr > pl;
            });
  DBG_OPT("get_freeze 3", false) << PARAM(probs_idxs) << std::endl;

  std::vector<int> res((1 << m) - k);
  for (int i = 0; i < res.size(); ++i) {
    res[i] = std::get<1>(probs_idxs[i]);
  }

  DBG_OPT("get_freeze 4", false) << PARAM(res) << std::endl;
  return res;
}

using Freeze = std::unordered_set<int>;

auto is_freeze(Freeze const &F, int i) -> bool { return F.find(i) != F.end(); }

struct PolarEncoder {
  using ValueType = F2;

  auto length() const -> int { return k_; }

  auto mk_u(VF2 &u, int l, int r) const {
    if (r - l == 1)
      return;
    int m = (r + l) / 2;
    mk_u(u, l, m);
    mk_u(u, m, r);
    for (int i = 0; i < (r - l) / 2; ++i) {
      u.set(l + i, u.get(l + i) + u.get(m + i));
    }
    DBG_OPT("mk_u", false) << PARAM(u) << std::endl;
  }

  auto encode(VF2 x) const -> VF2 {
    auto u = VF2::zero(n_);
    for (int i = 0, j = 0; i < n_; ++i) {
      if (!is_freeze(F_, i)) {
        u.set(i, x.get(j++));
      }
    }

    DBG_OPT("encode", false) << PARAM(x) << PARAM(u) << std::endl;
    mk_u(u, 0, n_);

    return u;
  }

  int n_, k_, m_;
  Freeze F_;
};

/////////////////////////////////////////////////////////////

#define SZ(la) (1 << (m_ - (la)))

struct ListDecoder {
  using ValueType = double;

  auto length() const -> int { return n_; }

  auto assignInitialPath() const -> int {
    auto l = inactivePathIndices.back();
    inactivePathIndices.pop_back();

    activePath[l] = true;
    for (int la = 0; la <= m_; la++) {
      auto s = inactiveArrayIndices[la].back();
      inactiveArrayIndices[la].pop_back();
      pathIndexToArrayIndex[la][l] = s;
      arrayReferenceCount[la][s] = 1;
    }

    return l;
  }

  auto getArrayPointer_P(int la, int l) const
      -> std::vector<std::array<double, 2>> & {
    auto s = pathIndexToArrayIndex[la][l];
    int sp;

    if (arrayReferenceCount[la][s] == 1) {
      sp = s;
    } else {
      DBG_ASSERT(arrayReferenceCount[la][s] > 1, "Using array with trash");
      sp = inactiveArrayIndices[la].back();
      inactiveArrayIndices[la].pop_back();

      arrayPointer_P[la][sp].assign(arrayPointer_P[la][s].begin(),
                                    arrayPointer_P[la][s].end());
      arrayPointer_C[la][sp].assign(arrayPointer_C[la][s].begin(),
                                    arrayPointer_C[la][s].end());
      arrayReferenceCount[la][s]--;
      arrayReferenceCount[la][sp] = 1;
      pathIndexToArrayIndex[la][l] = sp;
    }

    return arrayPointer_P[la][sp];
  }

  auto getArrayPointer_C(int la, int l) const
      -> std::vector<std::array<int, 2>> & {
    auto s = pathIndexToArrayIndex[la][l];
    int sp;

    if (arrayReferenceCount[la][s] == 1) {
      sp = s;
    } else {
      DBG_ASSERT(arrayReferenceCount[la][s] > 1, "Using array with trash");
      sp = inactiveArrayIndices[la].back();
      inactiveArrayIndices[la].pop_back();

      arrayPointer_P[la][sp].assign(arrayPointer_P[la][s].begin(),
                                    arrayPointer_P[la][s].end());
      arrayPointer_C[la][sp].assign(arrayPointer_C[la][s].begin(),
                                    arrayPointer_C[la][s].end());
      arrayReferenceCount[la][s]--;
      arrayReferenceCount[la][sp] = 1;
      pathIndexToArrayIndex[la][l] = sp;
    }

    return arrayPointer_C[la][sp];
  }

  void recursivelyCalcP(int la, int phi) const {
    if (la == 0)
      return;

    auto psi = phi / 2;

    if (phi % 2 == 0) {
      recursivelyCalcP(la - 1, psi);
    }

    double sigma = 0;
    for (int l = 0; l < L_; ++l) {
      if (pathIndexInactive(l)) {
        continue;
      }

      auto &P_la = getArrayPointer_P(la, l);
      auto &P_la1 = getArrayPointer_P(la - 1, l);
      auto &C_la = getArrayPointer_C(la, l);

      for (int b = 0; b < SZ(la); ++b) {
        if (phi % 2 == 0) {
          for (int up = 0; up < 2; ++up) {
            for (int upp = 0; upp < 2; ++upp) {
              P_la[b][up] += P_la1[b][up ^ upp] * P_la1[SZ(la) + b][upp] / 2.;
            }
            sigma = std::max(sigma, P_la[b][up]);
          }
        } else {
          auto up = C_la[b][0];
          for (int upp = 0; upp < 2; ++upp) {
            P_la[b][upp] = P_la1[b][up ^ upp] * P_la1[SZ(la) + b][upp] / 2.;
            sigma = std::max(sigma, P_la[b][upp]);
          }
        }
      }
    }

    for (int l = 0; l < L_; ++l) {
      if (pathIndexInactive(l)) {
        continue;
      }

      auto &P_la = getArrayPointer_P(la, l);
      for (int b = 0; b < SZ(la); ++b) {
        for (int u = 0; u < 2; ++u) {
          P_la[b][u] = P_la[b][u] / sigma;
        }
      }
    }
  }

  void continuePaths_FrozenBit(int phi) const {
    for (int l = 0; l < L_; ++l) {
      if (pathIndexInactive(l)) {
        continue;
      }

      auto &C_m = getArrayPointer_C(m_, l);
      C_m[0][phi % 2] = 0; // Frozen value of u_phi is 0
    }
  }

  void continuePaths_UnfrozenBit(int phi) const {
    int i = 0;

    probsRating.clear();

    for (int l = 0; l < L_; ++l) {
      if (pathIndexInactive(l)) {
        probForks[l][0] = -1;
        probForks[l][1] = -1;
      } else {
        auto &P_m = getArrayPointer_P(m_, l);
        probForks[l][0] = P_m[0][0];
        probForks[l][1] = P_m[0][1];

        probsRating.push_back({l, 0});
        probsRating.push_back({l, 1});

        i++;
      }
    }

    auto rho = std::min(2 * i, L_);

    std::sort(probsRating.begin(), probsRating.end(),
              [&](auto const &lhs, auto const &rhs) {
                auto &[ll, bl] = lhs;
                auto &[lr, br] = rhs;
                return probForks[ll][bl] > probForks[lr][br];
              });

    for (int l = 0; l < L_; ++l) {
      for (int b = 0; b < 2; ++b) {
        contForks[l][b] = false;
      }
    }

    assert(rho <= probsRating.size(), "rho is less then probs");
    for (int i = 0; i < rho; ++i) {
      auto &[l, b] = probsRating[i];
      contForks[l][b] = true;
    }

    for (int l = 0; l < L_; ++l) {
      if (pathIndexInactive(l)) {
        continue;
      }

      if (!contForks[l][0] && !contForks[l][1]) {
        killPath(l);
      }
    }

    for (int l = 0; l < L_; ++l) {
      if (!contForks[l][0] && !contForks[l][1]) {
        continue;
      }

      auto &C_m = getArrayPointer_C(m_, l);
      if (contForks[l][0] && contForks[l][1]) {
        C_m[0][phi % 2] = 0;
        auto lp = clonePath(l);
        auto &C_m = getArrayPointer_C(m_, lp);
        C_m[0][phi % 2] = 1;
      } else {
        if (contForks[l][0]) {
          C_m[0][phi % 2] = 0;
        } else {
          C_m[0][phi % 2] = 1;
        }
      }
    }
  }

  void killPath(int l) const {
    activePath[l] = false;
    inactivePathIndices.push_back(l);
    for (int la = 0; la <= m_; ++la) {
      auto s = pathIndexToArrayIndex[la][l];
      arrayReferenceCount[la][s]--;
      if (arrayReferenceCount[la][s] == 0) {
        inactiveArrayIndices[la].push_back(s);
      }
    }
  }

  auto clonePath(int l) const -> int {
    auto lp = inactivePathIndices.back();
    inactivePathIndices.pop_back();

    activePath[lp] = true;

    for (int la = 0; la <= m_; ++la) {
      auto s = pathIndexToArrayIndex[la][l];
      pathIndexToArrayIndex[la][lp] = s;
      arrayReferenceCount[la][s]++;
    }

    return lp;
  }

  auto pathIndexInactive(int l) const -> bool { return !activePath[l]; }

  void recursivelyUpdateC(int la, int phi) const {
    assert(phi % 2 == 1, "phi must be odd");

    auto psi = phi / 2;
    for (int l = 0; l < L_; ++l) {
      if (pathIndexInactive(l)) {
        continue;
      }

      auto &C_la = getArrayPointer_C(la, l);
      auto &C_la1 = getArrayPointer_C(la - 1, l);
      for (int b = 0; b < SZ(la); ++b) {
        C_la1[b][psi % 2] = C_la[b][0] ^ C_la[b][1];
        C_la1[SZ(la) + b][psi % 2] = C_la[b][1];
      }
    }

    if (psi % 2 == 1) {
      recursivelyUpdateC(la - 1, psi);
    }
  }

  auto findMostProbablePath() const -> int {
    int lp = 0;
    double pp = 0.;

    for (int l = 0; l < L_; ++l) {
      if (pathIndexInactive(l)) {
        continue;
      }

      auto &C_m = getArrayPointer_C(m_, l);
      auto &P_m = getArrayPointer_P(m_, l);

      if (pp < P_m[0][C_m[0][1]]) {
        lp = l;
        pp = P_m[0][C_m[0][1]];
      }
    }

    return lp;
  }

  auto getW(vec<double> y, int b, int c) const
      -> double {
    auto sigma = std::sqrt((0.5 * k_ / n_) * std::pow(10., -2. / 10.));
    return std::exp(-std::pow(y.get(b) - (c == 0 ? 1 : -1), 2.) *
                    (2. * sigma * sigma)) *
           std::sqrt(2 * M_PI * sigma * sigma);
  }

  auto getCW(int l, int la = 0, int s = 0) const -> VF2 {
    auto &C0 = getArrayPointer_C(la, l);
    auto ch = VF2::zero(SZ(la));
    for (int b = 0; b < SZ(la); ++b) {
      ch.set(b, C0[b][s] == 0 ? 0_f : 1_f);
    }
    return ch;
  }

  auto decode(vec<double> y, std::optional<double> param) const -> VF2 {
    initializeDataStructures();
    auto l = assignInitialPath();
    auto &P0 = getArrayPointer_P(0, l);

    for (int b = 0; b < n_; ++b) {
      P0[b][0] = getW(y, b, 0);
      P0[b][1] = getW(y, b, 1);
    }

    for (int phi = 0; phi < n_; ++phi) {
      recursivelyCalcP(m_, phi);
      if (is_freeze(F_, phi)) {
        continuePaths_FrozenBit(phi);
      } else {
        continuePaths_UnfrozenBit(phi);
      }

      if (phi % 2 == 1) {
        recursivelyUpdateC(m_, phi);
      }
    }

    l = findMostProbablePath();
    return getCW(l);
  }

  auto init() {
    inactivePathIndices.reserve(L_);
    activePath.resize(L_, false);
    arrayPointer_P.resize(m_ + 1,
                          std::vector<std::vector<std::array<double, 2>>>(L_));
    arrayPointer_C.resize(m_ + 1,
                          std::vector<std::vector<std::array<int, 2>>>(L_));
    pathIndexToArrayIndex.resize(m_ + 1, std::vector<int>(L_));
    inactiveArrayIndices.resize(m_ + 1);
    arrayReferenceCount.resize(m_ + 1, std::vector<int>(L_));

    for (int la = 0; la <= m_; ++la) {
      for (int s = 0; s < L_; ++s) {
        arrayPointer_P[la][s] =
            std::vector<std::array<double, 2>>(1 << (m_ - la));
        arrayPointer_C[la][s] = std::vector<std::array<int, 2>>(1 << (m_ - la));
      }
      inactiveArrayIndices[la].reserve(L_);
    }

    probForks.resize(L_);
    contForks.resize(L_);

    probsRating.reserve(L_ * 2);
  }

  void initializeDataStructures() const {
    inactivePathIndices.clear();

    for (int la = 0; la <= m_; ++la) {
      inactiveArrayIndices[la].clear();
      for (int s = 0; s < L_; ++s) {
        arrayReferenceCount[la][s] = 0;
        inactiveArrayIndices[la].push_back(s);
      }
    }

    for (int l = 0; l < L_; ++l) {
      activePath[l] = false;
      inactivePathIndices.push_back(l);
    }
  }

  int n_, k_, m_, L_;
  Freeze F_;

  mutable std::vector<int> inactivePathIndices;
  mutable std::vector<bool> activePath;
  mutable std::vector<std::vector<std::vector<std::array<double, 2>>>>
      arrayPointer_P;
  mutable std::vector<std::vector<std::vector<std::array<int, 2>>>>
      arrayPointer_C;
  mutable std::vector<std::vector<int>> pathIndexToArrayIndex;
  mutable std::vector<std::vector<int>> inactiveArrayIndices;
  mutable std::vector<std::vector<int>> arrayReferenceCount;

  mutable std::vector<std::array<double, 2>> probForks;
  mutable std::vector<std::array<bool, 2>> contForks;
  mutable std::vector<std::tuple<int, int>> probsRating;
};

//////////////////////////////////////////////////////////

struct BinWhiteNoiseChannel {
  auto send(VF2 in) -> vec<double> {
    auto &gen = random_generator();
    auto [n] = in.shape();
    auto res = vec<double>::zero(n);
    for (int i = 0; i < n; ++i) {
      res.set(i, (in.get(i) == 1_f ? -1. : 1.) + distr_(gen));
    }
    return res;
  }

  std::normal_distribution<double> distr_;
};

struct BinWhiteNoiseChannelF {
  using ParamType = double;
  BinWhiteNoiseChannel create(double p) const {
    double s = sqrt((0.5 * n_ / k_) * pow(10., -p / 10.));
    std::normal_distribution<double> distr(0, s);
    return BinWhiteNoiseChannel{.distr_ = distr};
  }

  int n_, k_;
};

////////////////////////////////////////////////////////////////////

int main() {
  setup();

  int n, k, L;
  double p;
  std::cin >> n >> k >> p >> L;
  int m = log2(n);

  auto freeze = get_freeze(p, m, k);
  std::unordered_set<int> F(freeze.begin(), freeze.end());

  for (int i = 0; i < n; ++i) {
    if (is_freeze(F, i)) {
      std::cout << i << " ";
    }
  }
  std::cout << std::endl;

  auto encoder = PolarEncoder{
      .n_ = n,
      .k_ = k,
      .m_ = m,
      .F_ = F,
  };
  auto decoder = ListDecoder{
      .n_ = n,
      .k_ = k,
      .m_ = m,
      .L_ = L,
      .F_ = F,
  };
  decoder.init();
  auto channel_factory = BinWhiteNoiseChannelF{.n_ = n, .k_ = k};
  handle_commands(encoder, decoder, channel_factory);

  return 0;
}
