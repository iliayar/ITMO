
// Generated at 2020-11-16 02:16:39.033530 
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
  int w;
  int fake_w;
  
  friend ostream& operator<<(ostream& out, Edge& e) {
    out << e.from << "->" << e.to << "(" << e.w << ")";
    return out;
  }
};

vint bad;
vector<vector<Edge>> g;

void dfs(int u) {
  bad[u] = true;
  for(Edge& e : g[u])
    if(!bad[e.to])
      dfs(e.to);
}

//entry
void sol() {
  int n, m, s; cin >> n >> m >> s; s--;
  g.resize(n, vector<Edge>());
  bad.resize(n, false);
  for(int i = 0; i < m; ++i) {
    int u, v , w; cin >> u >> v >> w; u--; v--;
    g[u].push_back({u, v, w});
  }
  
  vint d(n, INF);
  d[s] = 0;
  for(int i = 0; i < n; i++) {
    for(int u = 0; u < n; ++u) {
      for(auto& e : g[u]) {
	if(d[e.from] < INF && d[e.to] > d[e.from] + e.w) {
	  d[e.to] = d[e.from] + e.w;
	}
      }
    }
  }
  // for(int i = 0; i < n; i++) {
    for(int u = 0; u < n; ++u) {
      for(auto& e : g[u]) {
	if(d[e.from] < INF && d[e.to] > d[e.from] + e.w) {
	  dfs(e.to);
	}
      }
    }
  // }
  for(int i = 0; i < n; ++i){
    if(bad[i]) cout << "-" << endl;
    else if(d[i] == INF) cout << "*" << endl;
    else cout << d[i] << endl;
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
