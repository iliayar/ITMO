
// Generated at 2026-02-20 23:13:38.052380 
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
int log2(int n) {
    int i = 0;
    while (n > 0) {
        n /= 2;
        i++;
    }
    return i;
}

struct E {
    int to;
    int w;
};

//entry
void sol() {
    int n; cin >> n;
    vector<vector<E>> g(n, vector<E>{});
    for (int i = 0; i < n - 1; ++i) {
        int u, v, w; cin >> u >> v >> w;
        g[u].emplace_back(v, w);
        g[v].emplace_back(u, w);
    }
    int log2n = log2(n);
    vint depth(n, -1);
    vint2 up(n, vint(log2n + 1, -1));
    vint2 d(n, vint(log2n + 1, 0));
    depth[0] = 0;
    up[0][0] = 0;

    FUNC(void, dfs, int u) {
        for (auto& e : g[u]) {
            if (up[e.to][0] == -1) {
                up[e.to][0] = u;
                d[e.to][0] = e.w;
                depth[e.to] = depth[u] + 1;
                dfs(e.to);
            }
        }
    };
    dfs(0);

    for (int k = 0; k < log2n; ++k) {
        for (int i = 0; i < n; ++i) {
            // DBG() << i << " " << k << " " << up[i][k] << endl;
            up[i][k + 1] = up[up[i][k]][k];
            d[i][k + 1] = d[i][k] + d[up[i][k]][k];
        }
    }

    DBG() << depth << endl;


    FUNC(int, lca, int u, int v) {
        if (depth[u] < depth[v]) swap(u, v); 
        int ud = 0, vd = 0;
        for (int i = log2n; i >= 0; --i) {
            if (depth[v] + (1 << i) <= depth[u]) {
                ud += d[u][i];
                u = up[u][i];
            }
        }

        for (int i = log2n; i >= 0; --i) {
            if (up[v][i] != up[u][i]) {
                ud += d[u][i];
                vd += d[v][i];
                v = up[v][i];
                u = up[u][i];
            }
        }

        if (u != v) {
            vd += d[v][0];
            ud += d[u][0];
        }

        return vd + ud;
    };

    int m; cin >> m;
    for (int i = 0; i < m; ++i) {
        int u, v; cin >> u >> v;
        cout << lca(u, v) << endl;
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
