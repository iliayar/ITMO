
// Generated at 2026-04-25 23:59:44.654311 
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
#include <cassert>

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
ostream &operator<<(ostream &out, unordered_map<K, V> m) {
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
struct Edge {
    int c;
    int from, to;
    int f;
    int rev;
};

struct State {
    vector<vector<int>>& g;
    vector<Edge>& edges;
    int s, t;
};

int dfs(int v, int p, vint& was, State& state) {
    if (v == state.t) {
        return p;
    }
    was[v] = 1;
    for (int i = 0; i < state.g[v].size(); ++i) {
        auto& e = state.edges[state.g[v][i]];
        if (!was[e.to] && e.f < e.c) {
            auto delta = dfs(e.to, min(p, e.c - e.f), was, state);
            if (delta > 0) {
                state.edges[state.g[v][i]].f += delta;
                state.edges[e.rev].f -= delta;
                return delta;
            }
        }
    }
    return 0;
}

int ford(State& state) {
    vint was(state.g.size(), false);
    while (dfs(state.s, INF, was, state) > 0) {
        was.assign(was.size(), false);
    }
    int res = 0;
    for (int i : state.g[state.s]) {
        res += abs(state.edges[i].f);
    }
    return res;
}

bool bfs(vint& back_edge, State& state) {
    vint was(state.g.size(), false);
    queue<int> q;
    q.push(state.s);
    was[state.s] = true;

    while (!q.empty()) {
        int u = q.front(); q.pop();

        for (int i : state.g[u]) {
            auto& e = state.edges[i];
            if (!was[e.to] && e.f < e.c) {
                q.push(e.to);
                was[e.to] = true;
                back_edge[e.to] = i;
            }
        }
    }

    return was[state.t];
}

int karp(State& state) {
    vint back_edge(state.g.size(), -1);
    int res = 0;

    while (bfs(back_edge, state)) {
        // DBG() << back_edge << endl;
        int f = INF;
        int u = state.t;
        while (u != state.s) {
            auto& e = state.edges[back_edge[u]];
            f = min(f, e.c - e.f);
            u = e.from;
        }

        res += f;
        u = state.t;
        while (u != state.s) {
            auto& e = state.edges[back_edge[u]];
            e.f += f;
            state.edges[e.rev].f -= f;
            u = e.from;
        }
    }

    return res;
}

//entry
void sol() {
    int n, m; cin >> n >> m;
    vector<vint> g(n*m + 2);
    vector<Edge> edges;
    int s = n*m + 1;
    int t = n*m;
    vector<vector<char>> map(n, vector<char>(m, '\0'));

    FUNC(void, add_edge, int u, int v, int c) {
        g[u].push_back(edges.size());
        edges.emplace_back(c, u, v, 0, edges.size() + 1);
        g[v].push_back(edges.size());
        edges.emplace_back(0, v, u, 0, edges.size() - 1);
    };

    int s0 = 0, s1 = 0;

    for (int i = 0; i < n; ++i) {
        for (int j = 0; j < m; ++j) {
            char c; cin >> c;
            map[i][j] = c;
            if (c == '.') continue;
            int ca = -1;
            if (c == 'H') ca = 1;
            else if (c == 'O') ca = 2;
            else if (c == 'N') ca = 3;
            else if (c == 'C') ca = 4;

            if ((i + j) % 2 == 0) {
                if (i > 0 && map[i - 1][j] != '.') add_edge(i * m + j, (i - 1) * m + j, 1);
                if (j > 0 && map[i][j - 1] != '.') add_edge(i * m + j, i * m + (j - 1), 1);
                add_edge(s, i * m + j, ca);
                s0 += ca;
            } else {
                if (i > 0 && map[i - 1][j] != '.') add_edge((i - 1) * m + j, i * m + j, 1);
                if (j > 0 && map[i][j - 1] != '.') add_edge(i * m + (j - 1), i * m + j, 1);
                add_edge(i * m + j, t, ca);
                s1 += ca;
            }
        }
    }
    State state{g, edges, s, t};
    auto f = ford(state);
    DBG() << s0 << " " << s1 << " " << f << endl;

    if (s0 == s1 && s0 != 0 && s0 == f) {
        cout << "Valid" << endl;
    } else {
        cout << "Invalid" << endl;
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
