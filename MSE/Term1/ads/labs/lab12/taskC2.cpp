
// Generated at 2025-07-20 17:57:54.221254 
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
    int f, t, w;
};

struct V {
    int v, d, from;
};

//entry
void sol() {
    int n, m, s, t; cin >> n >> m >> s >> t; s--; t--;
    vector<vector<E>> g(n, vector<E>());

    for (int i = 0; i < m; ++i) {
        int u, v, w; cin >> u >> v >> w; u--; v--;
        g[u].push_back({u, v, w});
        g[v].push_back({v, u, w});
    }

    vector<int> d(n, -1);
    auto cmp = [](const V& l, const V& r) { return l.d > r.d; };
    priority_queue<V, vector<V>, decltype(cmp)> q;

    vector<int> from(n, -1);

    q.push({s, 0, -1});
    while (!q.empty()) {
        auto [u, du, fr] = q.top(); q.pop();
        DBG() << u + 1 << " " << du << endl;
        if (d[u] != -1) continue;
        d[u] = du;
        from[u] = fr;

        if (u == t) break;

        for (auto e : g[u]) {
            q.push({e.t, d[u] + e.w, u});
        }
    }
    cout << d[t] << endl;
    if (d[t] != -1) {
        vector<int> p;
        for (int u = t; u != -1; u = from[u]) {
            p.push_back(u);
        }
        for (int i = 1; i <= p.size(); ++i) {
            cout << p[p.size() - i] + 1 << " ";
        }
        cout << endl;
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
