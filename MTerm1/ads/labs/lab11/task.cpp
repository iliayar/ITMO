
// Generated at 2025-07-20 14:56:43.835264 
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
vint2 g;
vint2 gr;

int T = 0;
vint t;

vint c;
void dfs_t(int u) {
    if (c[u] != 0) return;
    c[u] = 1;

    for (int v : g[u]) {
        dfs_t(v);
    }

    c[u] = 2;
    t[u] = T++;
}

vint co;
vector<unordered_set<int>> gc;
void dfs_c(int u, int ci) {
    if (c[u] == 1) return;
    if (c[u] == 2) {
        if (co[u] != -1 && co[u] != ci) {
            gc[co[u]].insert(ci);
        }
        return;
    }
    c[u] = 1;
    co[u] = ci;

    for (int v : gr[u]) {
        dfs_c(v, ci);
    }

    c[u] = 2;
}

//entry
void sol() {
    int n, m; cin >> n >> m;
    g.resize(n, vint());
    gr.resize(n, vint());
    t.resize(n, -1);
    c.resize(n, 0);
    co.resize(n, -1);

    for (int i = 0; i < m; ++i) {
        int u, v; cin >> u >> v; u--; v--;
        g[u].push_back(v);
        gr[v].push_back(u);
    }

    vector<pair<int, int>> ot;
    for (int u = 0; u < n; ++u) {
        if (t[u] == -1) {
            dfs_t(u);
        }
        ot.push_back({t[u], u});
    }
    c.assign(c.size(), 0);
    sort(ALL(ot), [](auto& l, auto& r) { return l.first > r.first; });

    int cc = 0;
    for (auto [_t, u] : ot) {
        if (co[u] == -1) {
            dfs_c(u, cc);
            cc++;
            gc.push_back(unordered_set<int>());
        }
    }

    int res = 0;
    for (int u = 0; u < cc; ++u) {
        res += gc[u].size();
    }
    cout << res << endl;
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
