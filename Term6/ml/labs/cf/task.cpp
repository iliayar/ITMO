
// Generated at 2022-04-17 21:39:26.853585 
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
struct Obj {
    vector<double> x;
    int y;

    Obj(Obj const&) = delete;
    Obj & operator=(Obj const&) = delete;

    Obj(Obj&&) = default;
    Obj & operator=(Obj&&) = default;
};

struct Node {
    Node* left;
    Node* right;

    int cls;
    int fi;
    double thresh;

    int id;

    Node(int id, int cls)
        : left(nullptr), right(nullptr), cls(cls), fi(-1), thresh(0), id(id) {}
    Node(int id, int fi, double thresh, Node *left, Node *right)
        : left(left), right(right), cls(-1), fi(fi), thresh(thresh), id(id) {}

    bool is_leaf() { return left == nullptr && right == nullptr; }
};

template <typename T>
T sum(vector<T> a) {
    return accumulate(a.begin(), a.end(), 0);
}

bool check_same_classes(vector<Obj> const &objs) {
    int last_cls = -1;
    for (auto const& obj : objs) {
        if (last_cls != -1 && obj.y != last_cls) {
            return false;
        }
        last_cls = obj.y;
    }
    return true;
}

template <typename T>
double entropy(vector<T> a) {
    T n = sum(a);
    double res = 0;
    for (auto x : a) {
        if (x > 0) {
            res -= (1. * x / n) * log(1. * x / n);
        }
    }
    return res;
}

struct DT {
  int max_depth;
  int nclasses;
  int nfeats;
  Node *root;

  int nnodes;

  DT(int max_depth, int nclasses, int nfeats)
      : max_depth(max_depth), nclasses(nclasses), nfeats(nfeats), root(nullptr),
        nnodes(0) {}

  int find_major_class(vector<Obj> const &objs) {
      vector<int> nc(nclasses, 0);
      for (auto const& obj : objs) {
          nc[obj.y]++;
      }
      return max_element(ALL(nc)) - nc.begin();
  }

  optional<pair<double, int>> find_thresh_by(
      function<optional<pair<double, pair<double, int>>>(int, vector<Obj> const &)> f,
      vector<Obj> &objs) {
    optional<double> bsc;
    optional<pair<double, int>> br;
    for (int i = 0; i < nfeats; ++i) {
      // sort(ALL(objs),
      //      [i](auto const &a, auto const &b) { return a.x[i] < b.x[i]; });
        bool hflag = false;
        double p = -1;
        for (auto const& obj : objs) {
            if (p != obj.x[i]) {
                hflag = true;
                break;
            }
            p = obj.x[i];
        }
        if (!hflag) {
            continue;
        }

      // if (objs.front().x[i] == objs.back().x[i]) {
      //   continue;
      // }

      auto res = f(i, objs);
      if (res) {
          if (!bsc || *bsc > res->first) {
              bsc = res->first;
              br = res->second;
          }
      }
    }
    return br;
  }

  optional<pair<double, int>> find_thresh_by_entropy(vector<Obj> &objs) {
    return find_thresh_by(
        [this](int fi, vector<Obj> const& objs) {
          optional<double> bsc;
          optional<pair<double, int>> br;
          vint lc(nclasses, 0);
          vint rc(nclasses, 0);

          for (auto const &obj : objs) {
            rc[obj.y]++;
          }

          int pxi = -1;
          for (int i = 0; i < objs.size(); ++i) {
            auto const &obj = objs[i];
            if (i != 0 && obj.x[fi] != pxi) {
              double sc = entropy(lc) * sum(lc) + entropy(rc) * sum(rc);
              if (!bsc || *bsc > sc) {
                br = {(pxi + obj.x[fi]) / 2., fi};
                bsc = sc;
              }
            }
            rc[obj.y]--;
            lc[obj.y]++;
            pxi = obj.x[fi];
          }

          return bsc ? optional(make_pair(*bsc, *br)) : nullopt;
        },
        objs);
  }

  optional<pair<double, int>> find_thresh_by_gini(vector<Obj> &objs) {
    return find_thresh_by(
        [this](int fi, vector<Obj> const& objs) {
          optional<double> bsc;
          optional<pair<double, int>> br;
          vint lc(nclasses, 0);
          vint rc(nclasses, 0);
          int ls = 0;
          int rs = 0;
          int lsum = 0;
          int rsum = 0;

          for (auto const &obj : objs) {
            rsum -= rc[obj.y] * rc[obj.y];
            rc[obj.y]++;
            rsum += rc[obj.y] * rc[obj.y];
            rs++;
          }

          int pxi = -1;
          for (int i = 0; i < objs.size(); ++i) {
            auto const &obj = objs[i];
            if (i != 0 && obj.x[fi] != pxi) {
              double sc = -1. * lsum / ls - 1. * rsum / rs;
              if (!bsc || *bsc > sc) {
                br = {(pxi + obj.x[fi]) / 2., fi};
                bsc = sc;
              }
            }
            rsum -= rc[obj.y] * rc[obj.y];
            rc[obj.y]--;
            rsum += rc[obj.y] * rc[obj.y];

            lsum -= lc[obj.y] * lc[obj.y];
            lc[obj.y]++;
            lsum += lc[obj.y] * lc[obj.y];

            rs--; ls++;
            pxi = obj.x[fi];
          }

          return bsc ? optional(make_pair(*bsc, *br)) : nullopt;
        },
        objs);
  }

  Node *make_node(vector<Obj> objs, int depth) {
    if (check_same_classes(objs) || depth == max_depth) {
      return new Node(nnodes++, find_major_class(objs));
    }

    auto br = find_thresh_by_gini(objs);
    if (br) {
        int fi = br->second;
        double thresh = br->first;
        vector<Obj> l, r;
        for (auto& obj : objs) {
            if (obj.x[fi] < thresh) {
                l.push_back(move(obj));
            } else {
                r.push_back(move(obj));
            }
        }
        DBG() << "Thresh for feat " << fi + 1 << " is " << thresh << endl;
        return new Node(nnodes++, fi, thresh, make_node(move(l), depth + 1), make_node(move(r), depth + 1));
    } else {
        return new Node(nnodes++, find_major_class(objs));
    }
  }

  void build(vector<Obj> objs) {
    root = make_node(move(objs), 0);
  }

};

ostream &operator<<(ostream &o, Node * node) {
  if (node->is_leaf()) {
      o << "C " << node->cls + 1 << endl;
  } else {
    o << "Q " << node->fi + 1 << " " << node->thresh << " "
      << node->left->id + 1 << " "
      << node->right->id + 1 << endl;
    o << node->left << node->right;
  }
  return o;
}

ostream &operator<<(ostream &o, DT &clf) {
  o << clf.nnodes << endl;
  o << clf.root;
  return o;
}

// entry
void sol() {
    int M, K, H; cin >> M >> K >> H;
    int N; cin >> N;
    vector<Obj> objs;
    for (int i = 0; i < N; ++i) {
        vector<double> x;
        for (int j = 0; j < M; ++j) {
            double xi; cin >> xi;
            x.push_back(xi);
        }
        int y; cin >> y; y--;
        objs.emplace_back(Obj{std::move(x), y});
    }

    DT clf(H, K, M);
    clf.build(move(objs));
    cout << clf;
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
