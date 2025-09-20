
// Generated at 2022-05-01 20:11:14.362730 
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

matrix matrix_of(int r, int c, double v) {
  return vector<vector<double>>(r, vector<double>(c, v));
}

matrix zeros(int r, int c) { return matrix_of(r, c, 0); }

matrix ones(int r, int c) { return matrix_of(r, c, 1); }

pair<int, int> shape(matrix const &m) { return {m.size(), m[0].size()}; }

istream &operator>>(istream &in, matrix &m) {
  auto [r, c] = shape(m);
  for (int i = 0; i < r; ++i) {
    for (int j = 0; j < c; ++j) {
      in >> m[i][j];
    }
  }
  return in;
}

ostream &operator<<(ostream &out, matrix &m) {
  auto [r, c] = shape(m);
  for (int i = 0; i < r; ++i) {
    for (int j = 0; j < c; ++j) {
      out << m[i][j] << " ";
    }
    out << endl;
  }
  return out;
}

struct Node {
  vector<Node *> m_to;
  vector<Node *> m_from;

  optional<matrix> m_output;
  optional<matrix> m_diff;

  optional<vector<matrix>> m_saved_inputs;

  Node()
      : m_to(0), m_from(0), m_output(nullopt), m_diff(nullopt),
        m_saved_inputs(nullopt) {}

  virtual matrix forward(vector<matrix> const &inputs) = 0;
  virtual vector<matrix> backward(matrix const &grads) = 0;

  virtual string get_name() = 0;

  void add_diff(matrix const &diff) {
    if (!m_diff) {
      m_diff = diff;
      return;
    }

    auto &cdiff = m_diff.value();
    auto [r, c] = shape(diff);
    for (int i = 0; i < r; ++i) {
      for (int j = 0; j < c; ++j) {
        cdiff[i][j] += diff[i][j];
      }
    }
  }

  void compute_output() {
    vector<matrix> inputs;
    for (auto from : m_from) {
      inputs.push_back(from->m_output.value());
    }
    m_output = forward(inputs);
  }

  void compute_diff() {
    auto diffs = backward(m_diff.value());
    for (int i = 0; i < diffs.size(); ++i) {
      m_from[i]->add_diff(diffs[i]);
    }
  }

  matrix const &get_output() { return m_output.value(); }

  void save_inputs(vector<matrix> const &inputs) { m_saved_inputs = inputs; }

  matrix const &get_input(int i) { return (*m_saved_inputs)[i]; }
};

// void compute_forward(vector<Node *> inputs) {
//   queue<Node *> nodes;
//   for (auto node : inputs) {
//     nodes.push(node);
//   }
//   while (nodes.size()) {
//     auto node = nodes.front();
//     nodes.pop();

//     if (node->m_output) continue;

//     for (auto from_node : node->m_from) {
//       if (!from_node->m_output) {
//         nodes.push(node);
//         continue;
//       }
//     }

//     DBG() << "Computing node " << node->get_name() << endl;
//     node->compute_output();
//     for (auto to_node : node->m_to) {
//       nodes.push(to_node);
//     }
//   }
// }

// void compute_backward(vector<Node *> outputs) {
//   queue<Node *> nodes;
//   for (auto node : outputs) {
//     nodes.push(node);
//   }
//   while (nodes.size()) {
//     auto node = nodes.front();
//     nodes.pop();

//     if (!node->m_diff) {
//       nodes.push(node);
//       continue;
//     }

//     node->compute_diff();
//     for (auto from_node : node->m_from) {
//       nodes.push(from_node);
//     }
//   }
// }

struct Var : Node {
  int r, c;
  matrix input;

  Var(int r, int c) : Node(), r(r), c(c), input(zeros(r, c)) {}

  string get_name() override { return "Var"; }

  matrix forward(vector<matrix> const &inputs) override { return input; }

  vector<matrix> backward(matrix const &diffs) override { return {}; }
};

struct Tnh : Node {

  Tnh() : Node() {}

  string get_name() override { return "Tnh"; }

  matrix forward(vector<matrix> const &inputs) override {
    auto output = inputs[0];
    auto [r, c] = shape(output);
    for (int i = 0; i < r; ++i) {
      for (int j = 0; j < c; ++j) {
        output[i][j] = tanh(output[i][j]);
      }
    }
    return output;
  }

  vector<matrix> backward(matrix const &diff) override {
    auto const &output = get_output();
    auto [r, c] = shape(output);
    auto res = diff;

    for (int i = 0; i < r; ++i) {
      for (int j = 0; j < c; ++j) {
        res[i][j] *= (1. - output[i][j] * output[i][j]);
      }
    }

    return {res};
  }
};

struct Rlu : Node {
  double alpha_inv;

  Rlu(int alpha_inv) : Node(), alpha_inv(alpha_inv) {}

  string get_name() override { return "Rlu"; }

  matrix forward(vector<matrix> const &inputs) override {
    save_inputs(inputs);

    auto output = inputs[0];
    auto [r, c] = shape(output);

    for (int i = 0; i < r; ++i) {
      for (int j = 0; j < c; ++j) {
        if (output[i][j] < 0) {
          output[i][j] /= alpha_inv;
        }
      }
    }

    return output;
  }

  vector<matrix> backward(matrix const &diff) override {
    auto const &input = get_input(0);
    auto [r, c] = shape(input);
    auto res = diff;

    for (int i = 0; i < r; ++i) {
      for (int j = 0; j < c; ++j) {
        res[i][j] /= (input[i][j] < 0 ? alpha_inv : 1.);
      }
    }

    return {res};
  }
};

struct Mul : Node {
  Mul() : Node() {}

  string get_name() override { return "Mul"; }

  matrix forward(vector<matrix> const &inputs) override {
    save_inputs(inputs);

    auto const &a = inputs[0];
    auto const &b = inputs[1];

    auto [ar, ac] = shape(a);
    auto [br, bc] = shape(b);

    matrix res = zeros(ar, bc);
    for (int i = 0; i < ar; ++i) {
      for (int j = 0; j < bc; ++j) {
        for (int k = 0; k < ac; ++k) {
          res[i][j] += a[i][k] * b[k][j];
        }
      }
    }

    return res;
  }

  vector<matrix> backward(matrix const &diff) override {
    auto const &a = get_input(0);
    auto const &b = get_input(1);
    auto [ar, ac] = shape(a);
    auto [br, bc] = shape(b);
    matrix da = zeros(ar, ac);
    matrix db = zeros(ac, bc);

    for (int i = 0; i < ar; ++i) {
      for (int j = 0; j < ac; ++j) {
        for (int k = 0; k < bc; ++k) {
          da[i][j] += diff[i][k] * b[j][k];
          db[j][k] += diff[i][k] * a[i][j];
        }
      }
    }

    return {da, db};
  }
};

struct Sum : Node {
  Sum() : Node() {}

  string get_name() override { return "Sum"; }

  matrix forward(vector<matrix> const &inputs) override {
    auto [r, c] = shape(inputs[0]);
    auto res = zeros(r, c);

    for (auto const &input : inputs) {
      for (int i = 0; i < r; ++i) {
        for (int j = 0; j < c; ++j) {
          res[i][j] += input[i][j];
        }
      }
    }

    return res;
  }

  vector<matrix> backward(matrix const &diff) override {
    return vector<matrix>(m_from.size(), diff);
  }
};

struct Had : Node {
  Had() : Node() {}

  string get_name() override { return "Had"; }

  matrix forward(vector<matrix> const &inputs) override {
    save_inputs(inputs);

    auto [r, c] = shape(inputs[0]);
    auto res = ones(r, c);

    for (auto const &input : inputs) {
      for (int i = 0; i < r; ++i) {
        for (int j = 0; j < c; ++j) {
          res[i][j] *= input[i][j];
        }
      }
    }

    return res;
  }

  vector<matrix> backward(matrix const &diff) override {
    auto [r, c] = shape(get_input(0));
    vector<matrix> res(m_from.size(), zeros(r, c));

    for (int i = 0; i < r; ++i) {
      for (int j = 0; j < c; ++j) {
        for (int k = 0; k < res.size(); ++k) {
          double p = 1;
          for (int l = 0; l < res.size(); ++l) {
            p *= l == k ? 1. : get_input(l)[i][j];
          }
          res[k][i][j] += p * diff[i][j];
        }
      }
    }

    return res;
  }
};

// entry
void sol() {
  cout.precision(12);
  cout << fixed;

  int n, m, k;
  cin >> n >> m >> k;
  vector<Node *> nodes;

  auto add_node = [&nodes](int x, Node *node) {
    node->m_from.push_back(nodes[x - 1]);
    nodes[x - 1]->m_to.push_back(node);
  };

  for (int i = 0; i < n; ++i) {
    string name;
    cin >> name;
    Node* node = nullptr;
    if (name == "var") {
      int r, c;
      cin >> r >> c;
      node = new Var(r, c);
    } else if (name == "tnh") {
      int x;
      cin >> x;
      node = new Tnh();
      add_node(x, node);
    } else if (name == "rlu") {
      int alpha_inv, x;
      cin >> alpha_inv >> x;
      node = new Rlu(alpha_inv);
      add_node(x, node);
    } else if (name == "mul") {
      int a, b;
      cin >> a >> b;
      node = new Mul();
      add_node(a, node);
      add_node(b, node);
    } else if (name == "sum") {
      int l;
      cin >> l;
      node = new Sum();
      for (int i = 0; i < l; ++i) {
        int x;
        cin >> x;
        add_node(x, node);
      }
    } else if (name == "had") {
      int l;
      cin >> l;
      node = new Had();
      for (int i = 0; i < l; ++i) {
        int x;
        cin >> x;
        add_node(x, node);
      }
    }
    nodes.push_back(node);
  }

  for (int i = 0; i < m; ++i) {
    Var *node = static_cast<Var *>(nodes[i]);
    cin >> node->input;
  }

  for (int i = 0; i < n; ++i) {
      // DBG() << "Computing output of " << nodes[i]->get_name() << endl;
      nodes[i]->compute_output();
  }

  for (int i = 0; i < n; ++i) {
    if (!nodes[i]->m_output)
      continue;
    auto [r, c] = shape(nodes[i]->get_output());
    nodes[i]->m_diff = zeros(r, c);
  }

  for (int i = n - k; i < n; ++i) {
    auto [r, c] = shape(nodes[i]->get_output());
    cin >> nodes[i]->m_diff.value();
  }

  for (int i = n - 1; i >= 0; --i) {
      // DBG() << "Computing diff of " << nodes[i]->get_name() << endl;
      nodes[i]->compute_diff();
  }

  for (int i = n - k; i < n; ++i) {
    cout << nodes[i]->m_output.value();
  }

  for (int i = 0; i < m; ++i) {
    cout << nodes[i]->m_diff.value();
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
