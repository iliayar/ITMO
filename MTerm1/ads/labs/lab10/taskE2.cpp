
// Generated at 2025-07-12 18:32:10.407361 
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

//##################CODE BEGIN#############
struct P {
    int x, y;
};

double dist(P& l, P& r) {
    return sqrt((double)(l.x - r.x)*(l.x - r.x) + (double)(l.y - r.y)*(l.y - r.y));
}

struct E {
    int f, t;
};

vector<vector<double>> g;
vint2 gg;

vint was;
double res = 0.0;
bool dfs(int v) {
    if (v == g.size() - 1) {
        return true;
    }
    if (was[v]) return false;
    was[v] = true;
    for (auto u : gg[v]) {
        if(dfs(u)) {
            res = max(res, g[u][v]);
            return true;
        }
    }
    return false;
}

//entry
void sol() {
    int h, n; cin >> h >> n;
    vector<P> ps(n);
    for (int i = 0; i < n; ++i) {
        cin >> ps[i].x >> ps[i].y;
    }

    int fst = -1;
    double md = INF;

    g.resize(n + 2, vector<double>(n + 2, 0));
    gg.resize(n + 2, vint{});
    was.resize(n + 2, false);
    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < n; ++j) {
            g[i][j] = dist(ps[i], ps[j]);
            if (g[i][j] < md) {
                md = g[i][j];
                fst = i;
            }
            DBG() << i << " <-> " << j << " = " << g[i][j] << endl;
        }

        g[i][n] = g[n][i] = ps[i].y;
        g[i][n + 1] = g[n + 1][i] = h - ps[i].y;
        if (max(g[i][n + 1], g[i][n]) < md) {
            md = max(g[i][n + 1], g[i][n]);
            fst = i;
        }
    }
    g[n + 1][n] = g[n][n + 1] = h;
    if (h < md) {
        md = h;
        fst = n;
    }

    auto cmp = [&](const E& l, const E& r) {
        return g[l.f][l.t] > g[r.f][r.t];
    };
    priority_queue<E, vector<E>, decltype(cmp)> q(cmp);

    vint has(n + 2, false);
    for (int i = 0; i < n + 2; ++i) {
        q.push({fst, i});
    }
    has[fst] = true;

    while (!q.empty()) {
        while (!q.empty() && has[q.top().t]) q.pop();
        if (q.empty()) break;

        auto e = q.top(); q.pop();
        has[e.t] = true;
        gg[e.t].push_back(e.f);
        gg[e.f].push_back(e.t);

        for (int i = 0; i < n + 2; ++i) {
            if (!has[i]) {
                q.push({e.t, i});
            }
        }
    }
    dfs(n);

    cout << setprecision(9) << res << endl;
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
