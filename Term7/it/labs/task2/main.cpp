#pragma GCC optimize("Ofast")
#pragma GCC optimize("no-stack-protector")
#pragma GCC optimize("unroll-loops")
#pragma GCC optimize("fast-math")

#include <algorithm>
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

#define PARAM(expr) #expr "=" << expr << ", "

#define INF 1000000

template <typename K, typename V> struct map_pair {
  K k;
  V v;
};

template <typename T> class Join;

template <typename A, typename B>
std::ostream &operator<<(std::ostream &out, std::tuple<A, B> t) {
  std::vector v{std::get<0>(t), std::get<1>(t)};
  out << "(" << Join(v, ", ") << ")";
  return out;
}

template <typename A>
std::ostream &operator<<(std::ostream &out, std::tuple<A> t) {
  std::vector v{std::get<0>(t)};
  out << "(" << Join(v, ", ") << ")";
  return out;
}

template <typename K>
std::ostream &operator<<(std::ostream &out, std::unordered_set<K> s) {
  out << "{" << Join(s, ", ") << "}";
  return out;
}

template <typename T> class Join {
  T const &v;
  std::string const &separator;

public:
  Join(T const &v, std::string const &separator) : v(v), separator(separator) {}

  friend std::ostream &operator<<(std::ostream &out, Join<T> join) {
    for (auto it = join.v.cbegin(); it != join.v.cend(); ++it) {
      if (it != join.v.cbegin())
        out << join.separator;
      out << *it;
    }
    return out;
  }
};

template <typename T>
std::ostream &operator<<(std::ostream &out, std::vector<T> v) {
  out << "[" << Join(v, ", ") << "]";
  return out;
}

template <typename T, typename K>
std::ostream &operator<<(std::ostream &out, std::pair<T, K> p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

template <typename K, typename V>
std::ostream &operator<<(std::ostream &out, std::unordered_map<K, V> m) {
  std::vector<map_pair<K, V>> v;
  std::transform(m.begin(), m.end(), std::back_inserter(v),
                 [](std::pair<K, V> const &p) {
                   return map_pair<K, V>{p.first, p.second};
                 });
  out << "{" << Join(v, ", ") << "}";
  return out;
}

template <typename K, typename V>
std::ostream &operator<<(std::ostream &out, map_pair<K, V> m) {
  out << m.k << ": " << m.v;
  return out;
}

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

    auto ld = deg();
    auto rd = rhs.deg();

    auto res = vec<T>::zero(ld + rd + 1, factory_->zero());
    auto res_d = 0;
    for (int i = 0; i <= ld; i++) {
      for (int j = 0; j <= rd; j++) {
        auto v = res.get(i + j) + data_.get(i) * rhs.data_.get(j);
        res.set(i + j, v);

        if (v != factory_->zero()) {
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
    auto res = vpoly::one(s_, factory_);
    for (int i = 0; i < p; ++i) {
      res = *this * res;
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
    for (int i = 0; i < p; ++i) {
      res = *this * res;
    }
    return res;
  }

  auto pow_mod(int p, bitpoly const &mod) const -> bitpoly {
    auto res = bitpoly::one(s_, factory_);
    for (int i = 0; i < p; ++i) {
      res = multiply_mod(res, mod);
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

    for (int i = 0; i <= deg_; ++i) {
      if (data_.get(i) != other.data_.get(i))
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

void test() {
  auto a = symb('a');
  auto x = symb('x');

  auto ff_factory = new FFFactory<2>();
  auto poly_ff_factory = new PolyFactory<F2>(a, ff_factory);

  auto pax = poly_ff_factory->var();
  auto pa1 = poly_ff_factory->one();

  auto prime_poly = pax.pow(4) + pax + pa1;

  std::cout << prime_poly << std::endl;

  auto gf_factory = new GFFactory<2>(prime_poly, poly_ff_factory);

  auto gfa = gf_factory->var();
  auto gf1 = gf_factory->one();

  std::cout << gfa.pow(4) + gfa + gf1 << std::endl;

  auto poly_gf_factory = new PolyFactory<GF<2>>(x, gf_factory);

  auto gaa = gf_factory->var();
  auto ga1 = gf_factory->one();

  auto pxx = poly_gf_factory->var();
  auto px1 = poly_gf_factory->one();

  // (x - a) * (x - a^2) * (x - a - 1) * (x - a^2 - 1)
  std::cout << (pxx + gaa * px1) * (pxx + gaa.pow(2) * px1) *
                   (pxx + (gaa + ga1) * px1) * (pxx + (gaa.pow(2) + ga1) * px1)
            << std::endl;
}

auto log2(int n) -> int {
  int i = 0;
  while (n != 0) {
    n /= 2;
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
    res.get(i) = T(distr(gen));
  }

  return res;
}

/////////////////////////////////////////////

struct CyclicEncoder {
  using ValueType = F2;

  CyclicEncoder(int n, PGF2 g) : n_(n), g_(g) {}

  auto length() const -> int { return n_ - g_.deg(); }

  auto encode(VF2 v) const -> VF2 {
    auto p = PGF2::from_vec2(v, g_.var(), gf_factory_);
    DBG_OPT("CyclicEncoder::encode 0", false)
        << PARAM(p) << PARAM(g_) << PARAM(p * g_) << std::endl;
    auto x = pgf_factory_->var();
    auto pt = x.pow(g_.deg()) * p;
    DBG_OPT("CyclicEncoder::encode 1", false) << PARAM(pt) << std::endl;
    auto pe = pt + pt.rem(g_);
    DBG_OPT("CyclicEncoder::encode 2", false)
        << PARAM(pt.rem(g_)) << PARAM(pe) << std::endl;

    if (false) {
      auto a = gf_factory_->var();
      for (int i = 1; i <= g_.deg(); ++i) {
        DBG("CyclicEncoder X1")
            << PARAM(i) << PARAM(pe.eval(a.pow(i))) << std::endl;
      }
    }

    auto pev = pe.to_vec2(n_);
    DBG_OPT("CyclicEncoder::encode 2", false) << PARAM(pev) << std::endl;
    return pev;
  }

  int n_;
  PGF2 g_;

  GF2_F *gf_factory_;
  PGF2_F *pgf_factory_;
};

//////////////////////////////////////////////////////////////

PF2 poly_from_int(int n, PF2_F *factory) {
  auto x = factory->var();

  auto res = factory->zero();

  int i = 0;
  while (n != 0) {
    if (n % 2 == 1) {
      res = res + x.pow(i);
    }

    n /= 2;
    i += 1;
  }

  return res;
}

PGF2 get_min_poly(GF2 b, PGF2_F *pgf_f) {
  auto x = pgf_f->var();
  auto one = pgf_f->one();

  auto res = pgf_f->one();
  auto v = b;
  for (int i = 0;;) {
    res = res * (x + v * one);

    i += 1;
    v = v.pow(2);
    if (v == b)
      break;
  }

  return res;
}

PGF2 get_gen_poly(int b, int d, GF2_F *gf_f, PGF2_F *pgf_f) {
  auto a = gf_f->var();

  std::unordered_set<PGF2> min_polies;

  for (int i = b; i <= b + d - 2; ++i) {
    auto min_poly = get_min_poly(a.pow(i), pgf_f);

    min_polies.insert(min_poly);
  }

  auto res = pgf_f->one();
  for (auto const &p : min_polies) {
    DBG_OPT("get_gen_poly 2", false) << PARAM(p) << std::endl;
    res = res * p;
  }

  return res;
}

struct BCHCode {
  BCHCode(int n, PGF2 g, int d, int b) : n_(n), g_(g), d_(d), b_(b) {}

  auto k() const -> int { return n_ - g_.deg(); }

  auto get_encoder() -> CyclicEncoder { return CyclicEncoder(n_, g_); }

  int n_;
  PGF2 g_;

  int d_;
  int b_;
};

///////////////////////////////////////////////

struct BinarySymmetricChannel {
  auto send(VF2 in) -> VF2 {
    auto &gen = random_generator();
    auto [n] = in.shape();
    auto res = in;

    for (int i = 0; i < n; ++i) {
      double v = distr_(gen);
      if (v <= p_) {
        res.set(i, res.get(i) + 1_f);
      }
    }

    return res;
  }

  double p_;
  std::uniform_real_distribution<> distr_;
};

struct BinarySymmetricChannelF {
  using ParamType = double;
  BinarySymmetricChannel create(double p) const {
    static std::uniform_real_distribution<> distr(0., 1.);
    return BinarySymmetricChannel{.p_ = p, .distr_ = distr};
  }
};

/////////////////////////////////////////////

struct BKDecoder {
  using ValueType = F2;

  BKDecoder(BCHCode code) : code_(code) {}

  auto length() const -> int { return code_.n_; }

  auto calc_syndroms(PGF2 y) const -> PGF2 {
    PGF2 res = pgf_f_->zero();
    auto x = pgf_f_->var();
    auto a = gf_f_->var();
    DBG_OPT("BKDecode::calc_syndroms 1", false)
        << PARAM(code_.b_) << PARAM(code_.d_) << std::endl;
    for (int i = code_.b_; i < code_.b_ + code_.d_ - 1; ++i) {
      auto s = y.eval(a.pow(i));
      DBG_OPT("BKDecode::calc_syndroms 2", false)
          << PARAM(i) << PARAM(s) << std::endl;
      res = res + s * x.pow(i - code_.b_);
    }

    return res;
  }

  auto decode(VF2 enc) const -> VF2 {
    auto y = PGF2::from_vec2(enc, code_.g_.var(), gf_f_);
    DBG_OPT("BKDecode::decode 0", false) << PARAM(enc) << PARAM(y) << std::endl;
    auto S = calc_syndroms(y);
    DBG_OPT("BKDecode::decode 1", false) << PARAM(S) << std::endl;

    auto x = pgf_f_->var();

    auto La = pgf_f_->one();
    auto B = pgf_f_->one();
    int L = 0;
    int m = 1;
    auto b = gf_f_->one();

    for (int r = 0; r <= S.deg(); ++r) {
      auto d = S.get(r);
      for (int j = 1; j <= L; ++j) {
        d = d + La.get(j) * S.get(r - j);
      }

      if (d == gf_f_->zero()) {
        m = m + 1;
      } else {
        auto T = La;
        La = La + (d * b.inv()) * x.pow(m) * B;
        if (2 * L <= r) {
          L = r + 1 - L;
          B = T;
          b = d;
          m = 1;
        } else {
          m = m + 1;
        }
      }
    }

    DBG_OPT("BKDecoder 10", false) << PARAM(L) << PARAM(La) << std::endl;

    auto a = gf_f_->var();
    auto res = enc;
    for (int i = 0; i < code_.n_; ++i) {
      auto e = La.eval(a.inv().pow(i));
      if (e == gf_f_->zero()) {
        res.set(i, res.get(i) + 1_f);
      }
      DBG_OPT("BKDecoder X1", false)
          << PARAM(i) << PARAM(La.eval(a.inv().pow(i))) << std::endl;
    }

    return res;
  }

  BCHCode code_;
  GF2_F *gf_f_;
  PGF2_F *pgf_f_;
};

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
      auto w = decoder.decode(v);
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
        auto r = channel.send(c);
        auto d = decoder.decode(r);
        if (d != c) {
          errors++;
        }
      }

      double error_rate = static_cast<double>(errors) / total;
      std::cout << error_rate << std::endl;
    }
  }
}

int main() {
  setup();

  // DBG_OPT("main X", false) << PARAM(find_largest_one(bitvec::Inner(5)))
  //                          << std::endl;

  DBG_OPT("Main X1", false) << PARAM(bitvec::one(10)) << std::endl;

  int n, pn, d;
  std::cin >> n >> pn >> d;
  int m = log2(n + 1);

  auto ff_factory = new FFFactory<2>();
  // auto poly_ff_factory = new PolyFactory(symb('a'), ff_factory);
  auto poly_ff_factory = new BitPolyFactory(symb('a'), ff_factory);

  auto prim_poly = poly_from_int(pn, poly_ff_factory);

  DBG("main") << PARAM(prim_poly) << std::endl;

  auto gf_factory = new GFFactory<2, bitpoly>(prim_poly, poly_ff_factory);
  // auto gf_factory = new GFFactory<2>(prim_poly, poly_ff_factory);
  auto poly_gf_factory = new PolyFactory<GF2>(symb('x'), gf_factory);

  auto g = get_gen_poly(1, d, gf_factory, poly_gf_factory);
  DBG("main") << PARAM(g) << std::endl;

  auto code = BCHCode(n, g, d, 1);

  std::cout << code.k() << std::endl;
  auto gv = g.to_vec2();
  for (int i = 0; i < std::get<0>(gv.shape()); ++i) {
    std::cout << gv.get(i) << " ";
  }
  std::cout << std::endl;

  auto encoder = code.get_encoder();
  encoder.gf_factory_ = gf_factory;
  encoder.pgf_factory_ = poly_gf_factory;
  auto decoder = BKDecoder(code);
  decoder.gf_f_ = gf_factory;
  decoder.pgf_f_ = poly_gf_factory;
  auto channel_factory = BinarySymmetricChannelF{};

  handle_commands(encoder, decoder, channel_factory);

  return 0;
}
