
// Generated at 2026-03-16 17:52:07.247485 
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
#include <bitset>
#include <memory>

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

#define FUNC(retTy, name, args...) std::function<retTy (args)> name = [&](args) -> retTy

using vint = vector<int>;
using vint2 = vector<vint>;

template <typename K, typename V>
struct map_pair {
    K k;
    V v;
};

template <typename T, typename K>
ostream &operator<<(ostream &out, pair<T, K> const& p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

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

std::function<void()> finish = [](){ exit(0); };

//##################CODE BEGIN#############
struct Line {
  int add;
  int x;
  int l;
  int r;
};
 
struct Node {
    int add;
    int max;
    int imax;
};
 
int n;
 
vector<Node> tree;
 
Node eval(Node a, Node b) {
    Node t;
    if(a.max > b.max) {
        t.max = a.max;
        t.add = 0;
        t.imax = a.imax;
    } else {
        t.max = b.max;
        t.add = 0;
        t.imax = b.imax;
    }
    return t;
}
 
void propagate(int v, int l, int r) {
  if (v * 2 + 1 >= tree.size()) {
    return;
  }
  if(tree[v].add == 0) return;
 
  int m = (l + r)/2;
 
  if(tree[v * 2 + 1].max == 0) {
      tree[v * 2 + 1].imax = l;
  }
  if(tree[v * 2 + 2].max == 0) {
      tree[v * 2 + 2].imax = m + 1;
  }
 
  tree[v * 2 + 1].max += tree[v].add;
  tree[v * 2 + 1].add += tree[v].add;
  tree[v * 2 + 2].max += tree[v].add;
  tree[v * 2 + 2].add += tree[v].add;
 
  tree[v].add = 0;
}
 
void tree_add(int l, int r, int x, int v, int lx, int rx) {
    if (r < l) {
        return;
    }
    propagate(v, lx, rx);
    if (l == lx && r == rx) {
        if(tree[v].max == 0) {
            tree[v].imax = lx;
        }
        tree[v].max += x;
        tree[v].add += x;
        return;
    }
    int m = (lx + rx) / 2;
    tree_add(l, min(m, r), x, v * 2 + 1, lx, m);
    tree_add(max(l, m + 1), r, x, v * 2 + 2, m + 1, rx);
    tree[v] = eval(tree[v * 2 + 1], tree[v * 2 + 2]);
}
 
void tree_print(int v, int lx, int rx) {
    if(lx == rx) {
        cout << "(" << tree[v].max << ", " << tree[v].imax << ") ";
        return;
    }
    propagate(v, lx, rx);
    int m = (lx + rx)/2;
    tree_print(v*2+1, lx ,m);
    tree_print(v*2+2, m +1, rx);
}
 
vector<Line> a;
 
 
void a_print() {
    for(int i = 0; i < a.size(); ++i) {
        cout << "(" << a[i].x << ", " << a[i].add << ", (" << a[i].l << ", " << a[i].r << "))" << endl;
    }
}
 
int log2(int n) {
    int c = 0;
    while(n > 0) {
        c++;
        n >>= 1;
    }
    return c;
}
 
// entry
void sol() {
  int m;
  cin >> m;
 
  int ma = 0, mi = 0;
 
  for (int i = 0; i < m; ++i) {
    int rx, ry, lx, ly;
    cin >> lx >> ly >> rx >> ry;
    a.push_back({1, lx, ly, ry});
    a.push_back({-1, rx + 1, ly, ry});
    ma = max(ma, max(ly, ry));
    mi = min(mi, min(ly, ry));
  }
 
  n = ma - mi;
 
  tree.resize((1 << log2(n))*2, {0, 0, -1});
 
  sort(a.begin(), a.end(), [](Line a, Line b) { if(a.x == b.x) return a.add < b.add; else return a.x < b.x;; });
  // DBG_CODE(a_print());
  ma = 0;
  int my, mx;
 
  for(int i = 0; i < a.size(); ++i) {
      tree_add(a[i].l - mi, a[i].r - mi, a[i].add, 0, 0, n);
      if(tree[0].max > ma) {
          ma = tree[0].max;
          mx = a[i].x;
          my = tree[0].imax + mi;
      }
      // DBG_CODE(tree_print(0, 0, n); cout << endl;);
  }
 
  cout << ma << endl << mx << " " << my << endl;
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
    finish = [&]() {
        auto stop = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
        cout << duration.count() << " microseconds" << endl;
        exit(0);
    };
    #endif

    sol();
    finish();
}
