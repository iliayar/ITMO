
// Generated at 2022-05-03 01:07:59.737646 
// By iliayar
#define _USE_MATH_DEFINES
#pragma comment(linker, "/STACK:36777216")
#include <iterator>
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cmath>
#include <cstdio>
#include <map>
#include <unordered_set>
#include <ctime>
#include <cstdlib>
#include <queue>
#include <set>
#include <deque>
#include <list>
#include <sstream>
#include <numeric>
#include <optional>
#include <variant>
#include <functional>

using namespace std;

#define ON 1
#define OFF 0

#define int long long
#ifdef LOCAL
#define DBG_VAR true
#define DBG_CODE(x) x
#else
#define DBG_VAR false
#define DBG_CODE(x)
#endif

#define DBG() if (DBG_VAR) cout << "DBG: "

#define INF 1e+18
#define ALL(a) a.begin(), a.end()

using vint = vector<int>;
using vint2 = vector<vint>;

template <typename K, typename V>
struct map_pair {
    K k;
    V v;
};

template<typename T>
class Join {
  T& v;
  string const& separator;
  
public:
  
  Join(T v, string const& separator)
    : v(v), separator(separator)
  {}

  friend ostream& operator<<(ostream& out, Join<T> join) {
    for(auto it = join.v.cbegin(); it != join.v.cend(); ++it) {
      if(it != join.v.cbegin()) out << join.separator;
      out << *it;
    }
    return out;
  }
};

template <typename T>
ostream &operator<<(ostream &out, vector<T> v) {
  out << "[" << Join(v, ", ") << "]";
  return out;
}

template <typename T, typename K>
ostream &operator<<(ostream &out, pair<T, K> p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

template <typename K, typename V>
ostream &operator<<(ostream &out, map<K, V> m) {
  vector<map_pair<K, V>> v;
  transform(m.begin(), m.end(), back_inserter(v), [](pair<K, V> const& p){return map_pair<K, V>{p.first, p.second};});
  out << "{" << Join(v, ", ") << "}";
  return out;
}

template <typename K, typename V>
ostream &operator<<(ostream &out, map_pair<K, V> m) {
  out << m.k << ": " << m.v;
  return out;
}

template <typename K>
ostream &operator<<(ostream &out, set<K> s) {
  out << "{" << Join(s, ", ") << "}";
  return out;
}

//##################CODE BEGIN#############
using matrix = vector<vector<double>>;
using tensor = vector<matrix>;

matrix matrix_of(int r, int c, double v) {
  return matrix(r, vector<double>(c, v));
}

tensor tensor_of(int d, int r, int c, double v) {
  return tensor(d, matrix_of(r, c, v));
}

tensor zeros(int d, int r, int c) { return tensor_of(d, r, c, 0); }

tensor ones(int d, int r, int c) { return tensor_of(d, r, c, 1); }

tuple<int, int, int> shape(tensor const &m) {
  return {m.size(), m[0].size(), m[0][0].size()};
}
tuple<int, int> shape(matrix const &m) { return {m.size(), m[0].size()}; }

istream &operator>>(istream &in, tensor &m) {
  auto [d, r, c] = shape(m);
  for (int di = 0; di < d; ++di) {
    for (int ri = 0; ri < r; ++ri) {
      for (int ci = 0; ci < c; ++ci) {
        in >> m[di][ri][ci];
      }
    }
  }
  return in;
}

ostream &operator<<(ostream &out, tensor &m) {
  auto [d, r, c] = shape(m);
  for (int di = 0; di < d; ++di) {
    for (int ri = 0; ri < r; ++ri) {
      for (int ci = 0; ci < c; ++ci) {
        out << m[di][ri][ci] << " ";
      }
    }
  }
  return out;
}

struct Layer {
  optional<tensor> input;
  optional<tensor> output;

  Layer() : input(nullopt), output(nullopt) {}

  void save_input(tensor const &t) { input = t; }

  tensor const &get_input() { return input.value(); }

  void save_output(tensor const &t) { output = t; }

  tensor const &get_output() { return output.value(); }

  virtual tensor forward(tensor const &input) = 0;
  virtual tensor backward(tensor const &diff) = 0;

  virtual void print_params(ostream &out) = 0;
};

struct ReLU : Layer {

  int alpha_inv;

  ReLU(int alpha_inv) : Layer(), alpha_inv(alpha_inv) {}

  tensor forward(tensor const &input) override {
    save_input(input);

    auto [d, r, c] = shape(input);
    tensor res = zeros(d, r, c);
    for (int di = 0; di < d; ++di) {
      for (int ri = 0; ri < r; ++ri) {
        for (int ci = 0; ci < c; ++ci) {
          auto inp = input[di][ri][ci];
          res[di][ri][ci] = inp < 0 ? inp / alpha_inv : inp;
        }
      }
    }
    return res;
  }

  tensor backward(tensor const &diff) override {
    auto const &input = get_input();
    auto [d, r, c] = shape(input);
    tensor res = zeros(d, r, c);
    for (int di = 0; di < d; ++di) {
      for (int ri = 0; ri < r; ++ri) {
        for (int ci = 0; ci < c; ++ci) {
          auto inp = input[di][ri][ci];
          res[di][ri][ci] = (inp < 0 ? 1. / alpha_inv : 1.) * diff[di][ri][ci];
        }
      }
    }
    return res;
  }

  void print_params(ostream &out) override {}
};

struct Pool : Layer {
  int s;

  Pool(int s) : Layer(), s(s) {}

  tensor forward(tensor const &input) override {
    save_input(input);

    auto [d, r, c] = shape(input);
    double nd = d, nr = r / s, nc = c / s; // FIXME
    tensor res = zeros(nd, nr, nc);
    for (int di = 0; di < nd; ++di) {
      for (int ri = 0; ri < nr; ++ri) {
        for (int ci = 0; ci < nc; ++ci) {
          double v = -INF; // FIXME
          for (int sri = 0; sri < s; ++sri) {
            for (int sci = 0; sci < s; ++sci) {
              v = max(v, input[di][ri * s + sri][ci * s + sci]);
            }
          }
          res[di][ri][ci] = v;
        }
      }
    }
    save_output(res);
    return res;
  }

  tensor backward(tensor const &diff) override {
    auto const &input = get_input();
    auto const &output = get_output();
    auto [d, r, c] = shape(input);
    auto [nd, nr, nc] = shape(output);
    tensor res = zeros(d, r, c);
    for (int di = 0; di < nd; ++di) {
      for (int ri = 0; ri < nr; ++ri) {
        for (int ci = 0; ci < nc; ++ci) {
          for (int sri = 0; sri < s; ++sri) {
            for (int sci = 0; sci < s; ++sci) {
              if (input[di][ri * s + sri][ci * s + sci] == output[di][ri][ci]) {
                res[di][ri * s + sri][ci * s + sci] = diff[di][ri][ci];
              }
            }
          }
        }
      }
    }

    return res;
  }

  void print_params(ostream &out) override {}
};

struct Bias : Layer {
  vector<double> bs;

  Bias(vector<double> bs) : Layer(), bs(std::move(bs)) {}

  tensor forward(tensor const &input) override {
    auto [d, r, c] = shape(input);
    tensor res = zeros(d, r, c);
    for (int di = 0; di < d; ++di) {
      for (int ri = 0; ri < r; ++ri) {
        for (int ci = 0; ci < c; ++ci) {
          res[di][ri][ci] = input[di][ri][ci] + bs[di];
        }
      }
    }
    return res;
  }

  tensor backward(tensor const &diff) override {
    auto [d, r, c] = shape(diff);
    for (int di = 0; di < d; ++di) {
      bs[di] = 0;
      for (int ri = 0; ri < r; ++ri) {
        for (int ci = 0; ci < c; ++ci) {
          bs[di] += diff[di][ri][ci];
        }
      }
    }
    return diff;
  }

  void print_params(ostream &out) override {
    for (auto b : bs) {
      out << b << " ";
    }
    out << endl;
  }
};

struct Position {
  static constexpr char T = 1;
  static constexpr char B = 2;
  static constexpr char L = 4;
  static constexpr char R = 8;
};

struct Conv : Layer {

  int s;
  int p;
  vector<tensor> kernels;

  Conv(int s, int p, vector<tensor> kernels)
      : Layer(), s(s), p(p), kernels(std::move(kernels)) {}

  tensor forward(tensor const &not_padded_input) override {
      auto input = make_padding(not_padded_input);
      save_input(input);

      auto [d, r, c] = shape(input);
      auto [_d, kr, kc] = shape(kernels[0]);
      auto res = zeros(kernels.size(), (r - kr) / s + 1, (c - kc) / s + 1);
      auto [nd, nr, nc] = shape(res);
      for (int di = 0; di < nd; ++di) {
        for (int odi = 0; odi < d; ++odi) {
          for (int ri = 0; ri < nr; ++ri) {
            for (int ci = 0; ci < nc; ++ci) {
              for (int kri = 0; kri < kr; ++kri) {
                for (int kci = 0; kci < kc; ++kci) {
                  res[di][ri][ci] += input[odi][ri * s + kri][ci * s + kci] *
                                     kernels[di][odi][kri][kci];
                }
              }
            }
          }
        }
      }
      return res;
  }

  tensor backward(tensor const &without_kern_padded_diff) override {
      // DBG() << "Conv backward: make_diff_kern" << endl;
      auto padded_diff = make_diff_kern(without_kern_padded_diff);
      // DBG() << "Conv backward: update_params" << endl;
      update_params(without_kern_padded_diff);
      // DBG() << "Conv backward: remove_padding" << endl;
      return remove_padding(padded_diff);
  }

  tensor make_padding(tensor const &input) {
    auto [d, r, c] = shape(input);
    tensor res = zeros(d, r + 2 * p, c + 2 * p);
    auto [nd, nr, nc] = shape(res);
    for (int di = 0; di < nd; ++di) {
      for (int ri = 0; ri < nr; ++ri) {
        for (int ci = 0; ci < nc; ++ci) {
          if (!get_position(input[di], ri, ci)) {
            res[di][ri][ci] = input[di][ri - p][ci - p];
          } else {
            auto [ori, oci] = get_padding_at(input[di], ri, ci);
            res[di][ri][ci] = input[di][ori][oci];
          }
        }
      }
    }
    return res;
  }

  tensor make_diff_kern(tensor const &diff) {
    auto [d, r, c] = shape(get_input());
    tensor res = zeros(d, r, c);
    auto [nd, nr, nc] = shape(diff);
    auto [_d, kr, kc] = shape(kernels[0]);
    for (int di = 0; di < nd; ++di) {
      for (int odi = 0; odi < d; ++odi) {
        for (int ri = 0; ri < nr; ++ri) {
          for (int ci = 0; ci < nc; ++ci) {
            for (int kri = 0; kri < kr; ++kri) {
              for (int kci = 0; kci < kc; ++kci) {
                res[odi][ri * s + kri][ci * s + kci] +=
                    kernels[di][odi][kri][kci] * diff[di][ri][ci];
              }
            }
          }
        }
      }
    }
    return res;
  }

  tensor remove_padding(tensor const &diff) {
    auto [d, r, c] = shape(diff);
    tensor res = zeros(d, r - 2 * p, c - 2 * p);
    auto [nd, nr, nc] = shape(res);
    for (int di = 0; di < d; ++di) {
      for (int ri = 0; ri < r; ++ri) {
        for (int ci = 0; ci < c; ++ci) {
          if (!get_position(res[di], ri, ci)) {
            res[di][ri - p][ci - p] += diff[di][ri][ci];
          } else {
            auto [ori, oci] = get_padding_at(res[di], ri, ci);
            res[di][ori][oci] += diff[di][ri][ci];
          }
        }
      }
    }

    return res;
  }

  void update_params(tensor const &diff) {
    auto const& input = get_input();
    auto [d, r, c] = shape(input);
    auto [nd, nr, nc] = shape(diff);
    auto [_d, kr, kc] = shape(kernels[0]);
    kernels = vector<tensor>(nd, zeros(d, kr, kc));
    for (int di = 0; di < nd; ++di) {
      for (int odi = 0; odi < d; ++odi) {
        for (int ri = 0; ri < nr; ++ri) {
          for (int ci = 0; ci < nc; ++ci) {
            for (int kri = 0; kri < kr; ++kri) {
              for (int kci = 0; kci < kc; ++kci) {
                kernels[di][odi][kri][kci] +=
                    input[odi][ri * s + kri][ci * s + kci] * diff[di][ri][ci];
              }
            }
          }
        }
      }
    }
  }

  char get_position(matrix const &t, int r, int c) {
    auto [rt, ct] = shape(t);
    char res = 0;
    if (r < p) {
      res |= Position::T;
    }
    if (r >= p + rt) {
      res |= Position::B;
    }
    if (c < p) {
      res |= Position::L;
    }
    if (c >= p + ct) {
      res |= Position::R;
    }
    return res;
  }

  void print_params(ostream &out) override {
      for (auto& kernel : kernels) {
          cout << kernel;
      }
      cout << endl;
  }

  virtual tuple<int, int> get_padding_at(matrix const &orig, int r, int c) = 0;
};

struct Cnvm : Conv {
    using Conv::Conv;

    tuple<int, int> get_padding_at(matrix const& orig, int r, int c) override {
        auto [rs, cs] = shape(orig);
        auto pos = get_position(orig, r, c);

        int ro = r - p, co = c - p;
        if (pos & Position::T) {
            ro = p - r;
        }
        if (pos & Position::B) {
            ro = p - r + 2 * (rs - 1);
        }
        if (pos & Position::L) {
            co = p - c;
        }
        if (pos & Position::R) {
            co = p - c + 2 * (cs - 1);
        }

        return {ro, co};
    }

};

struct Cnve : Conv {
    using Conv::Conv;

    tuple<int, int> get_padding_at(matrix const& orig, int r, int c) override {
        auto [rs, cs] = shape(orig);
        auto pos = get_position(orig, r, c);

        int ro = r - p, co = c - p;
        if (pos & Position::T) {
            ro = 0;
        }
        if (pos & Position::B) {
            ro = rs - 1;
        }
        if (pos & Position::L) {
            co = 0;
        }
        if (pos & Position::R) {
            co = rs - 1;
        }

        return {ro, co};
    }

};

struct Cnvc : Conv {
    using Conv::Conv;

    tuple<int, int> get_padding_at(matrix const& orig, int r, int c) override {
        auto [rs, cs] = shape(orig);
        auto pos = get_position(orig, r, c);

        int ro = r - p, co = c - p;
        if (pos & Position::T) {
            ro = rs - (p - r);
        }
        if (pos & Position::B) {
            ro = r - p - rs;
        }
        if (pos & Position::L) {
            co = cs - (p - c);
        }
        if (pos & Position::R) {
            co = c - p - cs;
        }

        return {ro, co};
    }

};

// entry
void sol() {
  cout.precision(12);
  cout << fixed;

  int n0, d0;
  cin >> n0 >> d0;
  tensor input = zeros(d0, n0, n0);
  cin >> input;

  vector<Layer *> layers;
  int l;
  cin >> l;
  auto [id, ir, ic] = shape(input);
  for (int i = 0; i < l; ++i) {
    string name;
    cin >> name;
    Layer *layer = nullptr;
    if (name == "relu") {
      int alpha_inv;
      cin >> alpha_inv;
      layer = new ReLU(alpha_inv);
    } else if (name == "pool") {
      int s;
      cin >> s;
      layer = new Pool(s);

      ir /= s;
      ic /= s;
    } else if (name == "bias") {
      vector<double> bs;
      for (int j = 0; j < id; ++j) {
        double b;
        cin >> b;
        bs.push_back(b);
      }
      layer = new Bias(std::move(bs));
    } else {
        int h, k, s, p;
        cin >> h >> k >> s >> p;
        vector<tensor> kernels;
        for (int i = 0; i < h; ++i) {
            tensor kernel = zeros(id, k, k);
            cin >> kernel;
            kernels.push_back(kernel);
        }

        id = h;
        ir = (ir + 2 * p - k) / s + 1;
        ic = (ic + 2 * p - k) / s + 1;

        if (name == "cnvm") {
            layer = new Cnvm(s, p, std::move(kernels));
        } else if (name == "cnve") {
            layer = new Cnve(s, p, std::move(kernels));
        } else if (name == "cnvc") {
            layer = new Cnvc(s, p, std::move(kernels));
        }

    }
    layers.push_back(layer);
  }

  for (int i = 0; i < l; ++i) {
    input = layers[i]->forward(input);
  }

  cout << input << endl;

  auto [d, r, c] = shape(input);
  tensor diff = zeros(d, r, c);
  cin >> diff;

  vector<tensor> diffs;
  for (int i = l - 1; i >= 0; --i) {
    diff = layers[i]->backward(diff);
  }

  cout << diff << endl;

  for (auto layer : layers) {
    layer->print_params(cout);
  }
}
//##################CODE END###############
#ifdef LOCAL
#undef FILE_IO
#undef FILENAME
#define FILE_IO ON
#define FILENAME "local"
#endif

signed main() {
    ios_base::sync_with_stdio(0);
    cin.tie(0); cout.tie(0);
    #if FILE_IO == ON
    freopen(FILENAME".in", "r", stdin);
    freopen(FILENAME".out", "w", stdout);
    #endif
    #ifdef LOCAL
    auto start = std::chrono::high_resolution_clock::now();
    #endif

    sol();

    #ifdef LOCAL
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << duration.count() << " microseconds" << endl;
    #endif
}
