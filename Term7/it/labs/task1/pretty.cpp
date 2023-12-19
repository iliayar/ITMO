#include <algorithm>
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

#define LOG_DEBUG

#ifdef LOG_DEBUG
#define DBG(name) std::cout << "DBG[" #name "]: "
#else
#define DBG(name) constexpr if (false) std::cout
#endif

#define PARAM(expr) #expr "=" << expr << ", "

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

template <typename T = void *>
auto assert(bool val, const char *msg = "assertion failed") -> T {
  if (!val) {
    std::cerr << msg << std::endl;
    exit(1);
  }
  return *(T *)0xdeadbeef;
}

template <typename T> class matrix;

template <typename T> class vector {
public:
  explicit vector(std::vector<T> data)
      : data_(std::move(data)), size_(data_.size()) {}

  static auto zero(int size, T zero_val = T(0)) -> vector {
    std::vector<T> data(size, zero_val);
    return vector(std::move(data));
  }

  static auto one(int size, T one_val = T(1)) -> vector {
    std::vector<T> data(size, one_val);
    return vector(std::move(data));
  }

  auto shape() const -> std::tuple<int> { return {size_}; }

  auto get(int i) const -> T const & { return data_[i]; }

  auto get(int i) -> T & { return data_[i]; }

  auto begin() -> typename std::vector<T>::iterator { return data_.begin(); }
  auto begin() const -> typename std::vector<T>::const_iterator {
    return data_.begin();
  }

  auto end() -> typename std::vector<T>::iterator { return data_.end(); }
  auto end() const -> typename std::vector<T>::const_iterator {
    return data_.end();
  }

  auto operator+=(vector<T> const &other) -> vector<T> & {
    assert(size_ == other.size_, "cannot add vectors with different size");
    for (int i = 0; i < size_; ++i) {
      data_[i] += other.data_[i];
    }
    return *this;
  }

  auto operator*=(vector<T> const &other) -> vector<T> & {
    assert(size_ == other.size_, "cannot multiply vectors with different size");
    for (int i = 0; i < size_; ++i) {
      data_[i] *= other.data_[i];
    }
    return *this;
  }

  auto operator+(vector<T> const &other) const -> vector<T> {
    assert(size_ == other.size_, "cannot add vectors with different size");
    vector<T> res = vector<T>::zero(size_);
    res += other;
    res += *this;
    return res;
  }

  auto operator*(vector<T> const &other) const -> vector<T> {
    assert(size_ == other.size_, "cannot multiply vectors with different size");
    vector<T> res = vector<T>::one(size_);
    res *= other;
    res *= *this;
    return res;
  }

  auto operator*(matrix<T> const &m) const -> vector<T> {
    auto [n, k] = m.shape();
    assert(n == size_, "multiply to matrix of invalid shape");

    vector<T> res = vector<T>::zero(k);
    for (int i = 0; i < k; ++i) {
      for (int j = 0; j < size_; ++j) {
        res.get(i) += m.get(j, i) * data_[j];
      };
    }

    return res;
  }

  auto operator==(vector<T> const &other) const -> bool {
    return data_ == other.data_;
  }
  auto operator!=(vector<T> const &other) const -> bool {
    return !(*this == other);
  }

  friend auto operator<<(std::ostream &out, vector const &v) -> std::ostream & {
    auto [n] = shape();
    out << "|";
    for (int i = 0; i < n; ++i) {
      out << v.get(i);
      if (i != n - 1)
        out << " ";
    }
    out << "|";
    return out;
  }

  friend auto operator>>(std::istream &in, vector &v) -> std::istream & {
    for (int i = 0; i < v.size_; ++i) {
      in >> v.data_[i];
    }
    return in;
  }

private:
  std::vector<T> data_;
  int size_;
};

struct all_t {};
static all_t all;

template <typename T> class matrix {
public:
  explicit matrix(std::vector<std::vector<T>> data)
      : data_(std::move(data)), ncols_(data_[0].size()), nrows_(data_.size()) {}

  static auto zero(int nrows, int ncols, T zero_val = T(0)) -> matrix {
    std::vector<std::vector<T>> data(nrows, std::vector<T>(ncols, zero_val));
    return matrix(std::move(data));
  }

  static auto one(int nrows, int ncols, T zero_val = T(0), T one_val = T(1))
      -> matrix {
    assert(ncols == nrows, "identity matrix should be square");
    auto m = matrix<T>::zero(nrows, ncols, zero_val);
    for (int i = 0; i < ncols; ++i)
      m.data_[i][i] = one_val;
    return m;
  }

  auto mult(matrix rhs) const -> matrix {
    assert(ncols_ == rhs.nrows_,
           "cannot multiply matrices, has wrong dimensions");
    assert(false, "not implemented");
  }

  auto get(int row, int col) -> T & {
    assert(col < ncols_ && row < nrows_, "out of bounds get");
    return data_[row][col];
  }

  auto get(int row, int col) const -> T const & {
    assert(col < ncols_ && row < nrows_, "out of bounds get");
    return data_[row][col];
  }

  struct matrix_col {
    void add(matrix_col const &other) {
      assert(&m_ == &other.m_, "cannot add col of different matrix");
      for (int i = 0; i < m_.nrows_; i++) {
        m_.get(i, col_) += m_.get(i, other.col_);
      }
    }

    auto operator+=(matrix_col const &other) -> matrix_col & {
      add(other);
      return *this;
    }

    void swap(matrix_col const &other) {
      assert(&m_ == &other.m_, "cannot swap col of different matrix");
      for (int i = 0; i < m_.nrows_; i++) {
        std::swap(m_.get(i, col_), m_.get(i, other.col_));
      }
    }

    auto get(int row) -> T & { return m_.get(row, col_); }

    auto get(int row) const -> T const & { return m_.get(row, col_); }

    auto vec() -> vector<T> {
      auto res = vector<T>::zero(m_.nrows_);
      for (int i = 0; i < m_.nrows_; i++) {
        res.get(i) = m_.get(i, col_);
      }
      return res;
    };

    matrix &m_;
    int col_;
  };

  auto get(all_t, int col) -> matrix_col { return {*this, col}; }

  struct matrix_row {
    void add(matrix_row const &other) {
      assert(&m_ == &other.m_, "cannot add row of different matrix");
      for (int i = 0; i < m_.ncols_; i++) {
        m_.get(row_, i) += m_.get(other.row_, i);
      }
    }

    void swap(matrix_row const &other) {
      assert(&m_ == &other.m_, "cannot add row of different matrix");
      for (int i = 0; i < m_.ncols_; i++) {
        std::swap(m_.get(row_, i), m_.get(other.row_, i));
      }
    }

    auto operator+=(matrix_row const &other) -> matrix_row & {
      add(other);
      return *this;
    }

    auto get(int col) -> T & { return m_.get(row_, col); }

    auto get(int col) const -> T const & { return m_.get(row_, col); }

    auto vec() -> vector<T> {
      auto res = vector<T>::zero(m_.ncols_);
      for (int i = 0; i < m_.ncols_; i++) {
        res.get(i) = m_.get(row_, i);
      }
      return res;
    };

    matrix &m_;
    int row_;
  };

  auto get(int row, all_t) -> matrix_row { return {*this, row}; }

  auto shape() const -> std::tuple<int, int> {
    return std::make_tuple(nrows_, ncols_);
  }

  struct elems_iterator {
    elems_iterator(matrix<T> &m, int row, int col)
        : m_(m), row_(row), col_(col) {}

    void operator++() {
      auto [rows, cols] = m_.shape();
      if (col_ == cols - 1) {
        assert(row_ < rows - 1, "matrix elem iterator out of bounds");

        col_ = 0;
        row_++;
      } else {
        col_++;
      }
    }

    struct Elem {
      int row;
      int col;
      T value;
    };

    auto operator*() -> Elem { return Elem{row_, col_, m_.get(row_, col_)}; }

    auto operator==(elems_iterator &other) -> bool {
      return row_ == other.row_ && col_ == other.col_;
    }

  private:
    matrix<T> &m_;
    int row_, col_;
  };

  auto begin() -> elems_iterator { return elems_iterator(*this, 0, 0); }

  auto end() -> elems_iterator {
    return elems_iterator(*this, nrows_ - 1, ncols_ - 1);
  }

  auto operator*(vector<T> const &v) const -> vector<T> {
    auto [n] = v.shape();
    assert(n == ncols_, "multiply to vector of invalid shape");

    vector<T> res = vector<T>::zero(nrows_);
    for (int i = 0; i < nrows_; ++i) {
      for (int j = 0; j < ncols_; ++j) {
        res.get(i) += data_[i][j] * v.get(j);
      };
    }

    return res;
  }

  friend auto operator<<(std::ostream &out, matrix const &m) -> std::ostream & {
    auto [nrows, ncols] = m.shape();
    for (int i = 0; i < nrows; i++) {
      out << "|";
      for (int j = 0; j < ncols; j++) {
        out << m.get(i, j);
        if (j != ncols - 1)
          out << " ";
      }
      out << "|";
      if (i != nrows - 1)
        out << std::endl;
    }
    return out;
  }

  friend auto operator>>(std::istream &in, matrix &m) -> std::istream & {
    auto [nrows, ncols] = m.shape();
    int v;
    for (int i = 0; i < nrows; i++) {
      for (int j = 0; j < ncols; j++) {
        in >> v;
        m.get(i, j) = T(v);
      }
    }
    return in;
  }

private:
  std::vector<std::vector<T>> data_;
  int ncols_, nrows_;
};

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
  auto operator+=(FF<n> rhs) -> FF<n> & {
    v_ = (v_ + rhs.v_) % n;
    return *this;
  }

  auto operator*(FF<n> rhs) const -> FF<n> { return FF<n>(v_ * rhs.v_); }
  auto operator*=(FF<n> rhs) -> FF<n> & {
    v_ = (v_ * rhs.v_) % n;
    return *this;
  }

  auto operator==(FF<n> const &other) const -> bool { return v_ == other.v_; }
  auto operator!=(FF<n> const &other) const -> bool { return !(*this == other); }

  void swap(FF<n> &&other) { std::swap(v_, other.v_); }

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

  auto as_int() const -> int { return v_; };

private:
  int v_;
};

template <int n> struct std::hash<FF<n>> {
  auto operator()(FF<n> const &v) const -> std::size_t { return v.as_int(); }
};

template <int n> struct std::hash<::vector<FF<n>>> {
  auto operator()(::vector<FF<n>> const &v) const -> std::size_t {
    std::size_t res = 0;
    auto hash = std::hash<FF<n>>();
    for (auto const &f : v) {
      res = res * n + hash(f);
    }
    return res;
  }
};

template <int n> void increment(vector<FF<n>> &v) {
  auto [m] = v.shape();
  for (int i = m - 1; i >= 0; --i) {
    v.get(i) += 1_f;
    if (v.get(i) != 0_f)
      break;
  }
}

using F2 = FF<2>;
using mF2 = matrix<FF<2>>;

std::tuple<int, int> find_span(mF2 const &m, int row) {
  auto [_, k] = m.shape();

  int begin = -1, end = -1;
  for (int i = 0; i < k; ++i) {
    if (m.get(row, i) != 0_f) {
      if (begin == -1) {
        begin = i;
      }

      end = i;
    }
  }

  return {begin, end};
}

mF2 make_min_span_form(mF2 m) {
  auto [n, k] = m.shape();

  std::vector<std::tuple<int, int>> spans;

  for (int i = 0; i < n; ++i) {
    auto [begin, end] = find_span(m, i);
    spans.emplace_back(begin, end);
  }

  while (true) {
    bool changed = false;
    for (int i = 0; i < spans.size(); ++i) {
      for (int j = 0; j < spans.size(); ++j) {
        if (i == j)
          continue;

        auto [b1, e1] = spans[i];
        auto [b2, e2] = spans[j];

        auto r = [&]() -> std::optional<std::tuple<int, int>> {
          if (b1 == b2) {
            if (e1 <= e2) {
              return {{i, j}};
            } else {
              return {{j, i}};
            }
          } else if (e1 == e2) {
            if (b1 <= b2) {
              return {{i, j}};
            } else {
              return {{j, i}};
            }
          } else {
            return {};
          }
        }();

        if (!r)
          continue;

        auto [t, f] = *r;
        m.get(t, all) += m.get(f, all);
        changed = true;

        spans[t] = find_span(m, t);
      }
    }

    if (!changed)
      break;
  }

  return m;
}

template <typename T> struct Edge { T v; };

template <typename T>
auto operator<<(std::ostream &out, Edge<T> const &e) -> std::ostream & {
  out << "(" << e.v << ")";
  return out;
}

using vF2 = vector<FF<2>>;

template <typename T>
using Layer = std::unordered_map<vF2, std::unordered_map<vF2, Edge<T>>>;

template <typename T> using Trellis = std::vector<Layer<T>>;

using LF2 = Layer<FF<2>>;
using TF2 = Trellis<FF<2>>;
using EF2 = Edge<FF<2>>;

using Spans = std::vector<std::tuple<int, int>>;

using Idxs = std::unordered_set<int>;

auto weight(vF2 const &v) -> int {
  auto [n] = v.shape();
  int res;
  for (int i = 0; i < n; ++i) {
    if (v.get(i) == 1_f)
      res += 1;
  }
  return res;
}

template <int n> auto sum(vector<FF<n>> const &v) -> FF<n> {
  auto [m] = v.shape();
  FF<n> res = 0_f;
  for (int i = 0; i < m; ++i) {
    res += v.get(i);
  }
  return res;
}

auto get_active_rows(Spans const &spans, int i) -> Idxs {
  Idxs res;
  for (int j = 0; j < spans.size(); ++j) {
    auto [begin, end] = spans[j];
    if (begin == end && begin == i || i >= begin && i < end) {
      res.insert(j);
    }
  }
  return res;
}

auto projection(vF2 const &v, Idxs const &idxs) -> vF2 {
  auto [n] = v.shape();
  int m = idxs.size();

  vF2 res = vF2::zero(m);

  for (int i = 0, j = 0; i < n; ++i) {
    if (idxs.find(i) != idxs.end()) {
      res.get(j++) = v.get(i);
    }
  }

  return res;
}

auto extend_zeros(vF2 const &v, int n, Idxs const &idxs) -> vF2 {
  vF2 res = vF2::zero(n);

  for (int i = 0, j = 0; i < n; ++i) {
    if (idxs.find(i) != idxs.end()) {
      res.get(i) = v.get(j++);
    }
  }

  return res;
}

auto make_trellis(mF2 mat) -> TF2 {
  mat = make_min_span_form(std::move(mat));
  auto [n, k] = mat.shape();

  Spans spans;
  for (int i = 0; i < n; ++i) {
    spans.push_back(find_span(mat, i));
  }

  std::vector<Idxs> active_rows;
  active_rows.push_back({});
  for (int i = 0; i < k; ++i) {
    active_rows.push_back(get_active_rows(spans, i));
  }

  TF2 res = TF2(k + 1, LF2{});

  for (int i = 0; i < k; ++i) {
    auto te = active_rows[i];
    auto ten = active_rows[i + 1];
    te.merge(ten);

    auto c = vF2::zero(te.size());
    auto ce = c;
    do {
      increment(c);
      auto t = extend_zeros(c, n, te);
      auto vp = projection(t, active_rows[i]);
      auto vi = projection(t, active_rows[i + 1]);
      res[i][vp].insert_or_assign(vi, EF2{
                                          .v = sum(mat.get(all, i).vec() * t),
                                      });
    } while (c != ce);
  }

  return res;
}

void setup() {
  std::ios_base::sync_with_stdio(0);
  std::cin.tie(0);
  std::cerr.tie(0);
  std::cout.tie(0);
  freopen("input.txt", "r", stdin);
  freopen("output.txt", "w", stdout);
}

auto count_nodes(TF2 const &trellis, int layer) -> int {
  std::unordered_set<vF2> nodes;
  if (layer > 0) {
    for (auto const &[v, tos] : trellis[layer - 1]) {
      for (auto const &[vto, _] : tos) {
        nodes.insert(vto);
      }
    }
  }
  for (auto const &[v, _] : trellis[layer]) {
    nodes.insert(v);
  }
  return nodes.size();
}

template <typename T> class LinearEncoder {
public:
  using ValueType = T;

  LinearEncoder(matrix<T> m) : m_(m) {}

  auto length() const -> int {
    auto [n, k] = m_.shape();
    return n;
  }

  auto encode(vector<T> v) const -> vector<T> { return v * m_; }

private:
  matrix<T> m_;
};

template <typename T> class SoftTrellisDecoder {
public:
  using ValueType = double;

  SoftTrellisDecoder(Trellis<T> trellis) : trellis_(std::move(trellis)) {}

  auto length() const -> int { return trellis_.size() - 1; }

  struct Route {
    vector<T> from;
    T value;

    friend auto operator<<(std::ostream &out, Route const &r)
        -> std::ostream & {
      out << r.from << " (" << r.value << ")";
      return out;
    }
  };

  auto decode(vector<ValueType> enc) const -> vector<T> {
    std::vector<std::unordered_map<::vector<T>, double>> cost(trellis_.size());
    std::vector<std::unordered_map<::vector<T>, Route>> path(trellis_.size());

    for (const auto &[from, _] : trellis_[0]) {
      cost[0].insert_or_assign(from, 0);
    }

    for (int i = 1; i < trellis_.size(); ++i) {
      double wa = enc.get(i - 1);
      for (const auto &[from, tos] : trellis_[i - 1]) {
        for (const auto &[to, e] : tos) {
          double w = e.v == 1_f ? -wa : wa;
          if (cost[i].find(to) == cost[i].end() ||
              cost[i][to] < cost[i - 1][from] + w) {
            cost[i].insert_or_assign(to, cost[i - 1][from] + w);
            path[i].insert_or_assign(to, Route{.from = from, .value = e.v});
          }
        }
      }
    }

    auto s = vector<T>::zero(0);
    auto dec = vector<T>::zero(path.size() - 1);
    for (int i = 0; i < path.size() - 1; ++i) {
      auto &r = path[path.size() - i - 1].at(s);
      dec.get(path.size() - i - 2) = r.value;
      s = r.from;
    }

    return dec;
  }

private:
  Trellis<T> trellis_;
};

auto random_generator() -> auto & {
  static std::random_device rd;
  static std::mt19937 gen(rd());

  return gen;
}

template <typename T> auto rand_int_uniform_vec(int size) -> vector<T> {
  auto &gen = random_generator();
  std::uniform_int_distribution distr;

  auto res = vector<T>::zero(size);
  for (int i = 0; i < size; ++i) {
    res.get(i) = T(distr(gen));
  }

  return res;
}

auto rand_float_normal(double m, double s) {
  auto &gen = random_generator();
  std::normal_distribution<double> distr(m, s);
  return distr(gen);
}

struct BinWhiteNoiseChannel {
  auto send(vector<F2> in) -> vector<double> {
    auto [n] = in.shape();
    auto res = vector<double>::zero(n);
    for (int i = 0; i < n; ++i) {
      res.get(i) =
          (in.get(i) == 1_f ? -1. : 1.) + rand_float_normal(0., sigma_);
    }
    return res;
  }

  double sigma_;
};

struct BinWhiteNoiseChannelF {
  using ParamType = double;
  BinWhiteNoiseChannel create(double p) const {
    double s = sqrt((0.5 * k_ / n_) * pow(10., -p / 10.));
    return BinWhiteNoiseChannel{.sigma_ = s};
  }

  int n_, k_;
};

template <typename Encoder, typename Decoder, typename ChannelFactory>
void handle_commands(Encoder const &encoder, Decoder const &decoder,
                     ChannelFactory const &channel_factory) {
  std::string line;
  while (std::getline(std::cin, line)) {
    std::stringstream ss(line);

    std::string cmd;
    ss >> cmd;

    if (cmd == "Encode") {
      auto v = vector<typename Encoder::ValueType>::zero(encoder.length());
      ss >> v;
      auto enc = encoder.encode(v);
      for (int i = 0; i < std::get<0>(enc.shape()); ++i) {
        std::cout << enc.get(i) << " ";
      }
      std::cout << std::endl;
    } else if (cmd == "Decode") {
      auto v = vector<typename Decoder::ValueType>::zero(decoder.length());
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

  int n, k;
  std::cin >> k >> n;

  mF2 m = mF2::zero(n, k);
  std::cin >> m;

  auto trellis = make_trellis(m);

  for (int i = 0; i < trellis.size(); ++i) {
    std::cout << count_nodes(trellis, i) << " ";
  }
  std::cout << std::endl;

  LinearEncoder encoder(m);
  SoftTrellisDecoder decoder(std::move(trellis));
  handle_commands(encoder, decoder, BinWhiteNoiseChannelF{.n_ = n, .k_ = k});
}
