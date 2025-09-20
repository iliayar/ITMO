
// Generated at 2020-12-06 15:08:52.109554 
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

vector<vector<Edge>> g;

//entry
void sol() {
  int n, m; cin >> n >> m;
  g.resize(n, vector<Edge>{});
  for(int i = 0; i < m; ++i) {
    int u, v; cin >> u >> v; u--; v--;
    g[u].push_back({u, v});
    g[v].push_back({v, u});
  }
  queue<int> q;
  vint was(n, 0);
  vint c(n, -1);
  int k = 0;
  q.push(0);
  int ma = 0;
  while(!q.empty()) {
    int u = q.front(); q.pop();
    was[u] = 1;
    vint a(k + 1, 0);
    ma = max(ma, (int)g[u].size());
    for(Edge& e : g[u]) {
      if(c[e.to] != -1) {
	a[c[e.to]] = 1;
      }
      if(!was[e.to]) q.push(e.to);
    }
    int j = 0;
    for(; j < a.size() && a[j]; ++j);
    k = max(k, j);
    c[u] = j;
  }
  if(ma % 2 == 0) ++ma;
  if(k % 2 == 0) ++k;
  k = max(k, ma);
  cout << k << endl;
  for(int i : c) {
    cout << i + 1 << endl;
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
