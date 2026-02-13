
// Generated at 2026-02-14 16:13:50.328022 
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
struct E {
    int to;
    int w;
};

void reachable(vector<vector<E>> const& g, vint& r, int s) {
    queue<int> q;
    vint was(g.size(), false);
    q.push(s);
    was[s] = true;
    while (!q.empty()) {
        auto u = q.front(); q.pop();
        r[u] = true;
        for (auto& e : g[u]) {
            if (!was[e.to]) {
                q.push(e.to);
                was[e.to] = true;
            }
        }
    }
}

//entry
void sol() {
    int n, m; cin >> n >> m;
    vector<vector<E>> g(n, vector<E>());
    vector<vector<E>> gr(n, vector<E>());
    for (int i = 0; i < m; ++i) {
        int u, v, w; cin >> u >> v >> w; u--; v--;
        g[u].emplace_back(v, w);
        gr[v].emplace_back(u, w);
    }

    vint rs(n, false);
    vint rt(n, false);
    reachable(g, rs, 0);
    reachable(gr, rt, n - 1);

    vint d(n, INF);
    d[0] = 0;
    int c = 0;
    bool run = true;
    while (c < n && run) {
        run = false;
        for (int u = 0; u < n; ++u) {
            for (auto& e : g[u]) {
                if (d[u] == INF) continue;
                if (d[u] + (-e.w) < d[e.to]) {
                    d[e.to] = d[u] + (-e.w);
                    run = true;
                }
            }
        }
        c++;
    }

    for (int u = 0; u < n; ++u) {
        for (auto& e : g[u]) {
            if (d[u] == INF) continue;
            if (d[u] + (-e.w) < d[e.to]) {
                if (rs[e.to] && rt[e.to]) {
                    cout << ":)" << endl;
                    return;
                }
            }
        }
    }

    if (d[n-1] == INF) cout << ":(" << endl;
    else cout << -d[n - 1] << endl;
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
