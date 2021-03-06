
// Generated at 2020-11-17 15:05:58.173293 
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
  friend ostream& operator<<(ostream& out, Edge e) {
    out << e.from << "->" << e.to;
    return out;
  }
};

vint topsort;

vint color;

int ti;

vector<vector<Edge>> g;

void sort(int u) {
  color[u] = 1;
  for(Edge e : g[u]) {
    if(color[e.to] == 1) {
      cout << "-1" << endl;
      exit(0);
    }
    if(color[e.to] == 0) sort(e.to);
  }
  color[u] = 2;
  topsort[ti] = u;
  ti--;
}

//entry
void sol() {
  int n, m; cin >> n >> m;
  g.resize(n, vector<Edge>());
  color.resize(n, 0);
  topsort.resize(n, -1);
  ti = n-1;
  for(int i = 0; i < m; ++i) {
    int u, v; cin >> u >> v; u--; v--;
    g[u].push_back({u, v});
  }
  for(int i = 0; i < n; ++i)
    if(color[i] == 0) sort(i);
  reverse(topsort.begin(), topsort.end());
  DBG(topsort);

  vint G(n, -1);
  
  for(int u : topsort) {
    int m = 0;
    set<int> a;
    for(Edge& e : g[u]) {
      a.insert(G[e.to]);
    }
    for(int i : a) {
      if(i > m) {
	break;
      } else {
	m = i + 1;
      }
    }
    G[u] = m;
  }
  cout << Join(G, "\n") << endl;;
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
