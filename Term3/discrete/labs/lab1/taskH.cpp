
// Generated at 2020-12-06 18:29:23.976640 
// By iliayar
#pragma comment(linker, "/STACK:36777216")
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


using namespace std;

#define ON 1
#define OFF 0

#define int long long
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl
#define DBG_CODE(x) x
#else
#define DBG(x)
#define DBG_CODE(x)
#endif

#define INF 1e+18

using vint = vector<int>;
using vint2 = vector<vint>;

template<typename T>
class Join {
  T& v;
  string& separator;
  
public:
  
  Join(T v, string separator)
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

template<typename T>
ostream& operator<<(ostream& out, vector<T> v) {
  out << Join(v, " ") << endl;
  return out;
}

template<typename T, typename K>
ostream& operator<<(ostream& out, pair<T, K> p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

//##################CODE BEGIN#############
struct Edge {
  int from;
  int to;

  friend ostream& operator<<(ostream& o, const Edge& e) {
    o << "(" << e.from << " -> " << e.to << ")";
    return o;
  }
  
};

using Graph = vector<vector<Edge>>;

Graph edge_delete(Graph g, int u, int v)
{
  for(auto it = g[u].begin(); it != g[u].end(); ++it) {
    if(it->to == v && it->from == u) {
      g[u].erase(it);
      break;
    }
  }
  for(auto it = g[v].begin(); it != g[v].end(); ++it) {
    if(it->to == u && it->from == v) {
      g[v].erase(it);
      break;
    }
  }
  return g;
}
Graph edge_contract(Graph g, int u, int v)
{
  if(u > v) swap(u, v);
  for(auto& a : g) {
    for(Edge& e : a) {
      if(e.to == v) e.to = -1;
      else if(e.to > v) e.to--;
      if(e.from > v) e.from--;
    }
  }
  vector<Edge> ve = g[v];
  g.erase(g.begin() + v);
  for(Edge& e : ve) {
    if(e.to != u) {
      int ok = 0;
      for(Edge& e1 : g[e.to]) {
	if(e1.to == u) ok = 1;
      }
      if(!ok) {
	g[u].push_back({u, e.to});
	g[e.to].push_back({e.to, u});
      }
    }
  }
  for(auto& a : g) {
    for(auto it = a.begin(); it != a.end();) {
      if(it->to == -1) {
	it = a.erase(it);
      } else {
	it++;
      }
    }
  }
  return g;
}

vint poly_sub(vint a, vint b)
{
  vint res(max(a.size(), b.size()), 0);
  for(int i = 0; i < a.size(); ++i) {
    res[i] += a[i];
  }
  for(int i = 0; i < b.size(); ++i) {
    res[i] -= b[i];
  }
  return res;
}

vint find_poly(Graph g) {
  int ok = 0;
  for(auto& a : g) {
    if(a.size() != 0) ok = 1;
  }
  if(!ok) {
    vint res(g.size() + 1, 0);
    res[g.size()] = 1;
    return res;
  }
  int u, v;
  for(auto& a : g) {
    for(Edge& e : a) {
      u = e.from;
      v = e.to;
      break;
    }
  }
  return poly_sub(find_poly(edge_delete(g, u, v)), find_poly(edge_contract(g, u, v)));
}

//entry
void sol() {

  int n, m; cin >> n >> m;
  Graph g(n, vector<Edge>{});
  for(int i = 0; i < m; ++i) {
    int u, v; cin >> u >> v; u--; v--;
    g[u].push_back({u, v});
    g[v].push_back({v, u});
  }
  vint p = find_poly(g);
  cout << p.size() - 1 << endl;
  for(int i = p.size() - 1; i >= 0; --i) {
    cout << p[i] << " ";
  }
  cout << endl;
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
