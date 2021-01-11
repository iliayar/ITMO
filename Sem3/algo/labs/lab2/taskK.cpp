
// Generated at 2020-11-18 14:04:34.852944 
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
  vector<T>& v;
  string& separator;
  
public:
  
  Join(vector<T> v, string separator)
    : v(v), separator(separator)
  {}

  friend ostream& operator<<(ostream& out, Join<T> join) {
    for(int i = 0; i < join.v.size(); ++i) {
      if(i != 0) out << join.separator;
      out << join.v[i];
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
  int i;
  friend ostream& operator<<(ostream& out, Edge e) {
    out << e.from << "->" << e.to;
    return out;
  }
};

vector<vector<Edge>> g;
vint G;
vint was;

void dfs(int u) {
  was[u] = true;
  for(Edge& e : g[u]) {
    if(!was[e.to]) {
      dfs(e.to);
      G[u] ^= G[e.to] + 1;
    }
  }
}

void dfs2(int u, int gg) {
  was[u] = true;
  for(Edge& e : g[u]) {
    if(was[e.to]) continue;
    if((gg^G[u]^(G[e.to] + 1)) == 0) {
      cout << e.i << endl;
      exit(0);
    }
    dfs2(e.to, (gg^G[u]^(G[e.to] + 1)) - 1);
  }
}

//entry
void sol() {
  int n, r; cin >> n >> r; r--;
  g.resize(n, vector<Edge>());
  G.resize(n, 0);
  was.resize(n, false);
  for(int i = 0; i < n-1; ++i) {
    int u, v; cin >> u >> v; u--; v--;
    g[u].push_back({u, v, i + 1});
    g[v].push_back({v, u, i + 1});
  }
  dfs(r);
  DBG(G);
  was.assign(n, false);
  if(G[r] == 0) cout << 2 << endl;
  else {
    cout << 1 << endl;
    dfs2(r, 0);
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
