
// Generated at 2020-12-05 18:43:01.586283 
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
  int n; cin >> n;
  g.resize(n, vector<Edge>{});
  vint c(n, 0);
  for(int i = 0; i < n - 1; ++i) {
    int u, v; cin >> u >> v; u--; v--;
    g[u].push_back({u, v});
    g[v].push_back({v, u});
    c[u]++;
    c[v]++;
  }
  priority_queue<int, vector<int>, greater<int>> q;
  vint was(n, 0);
  int cnt = n;
  for(int i = 0; i < n; ++i) {
    if(c[i] == 1) {
      q.push(i);
      // DBG(i);
    }
  }
  while(cnt > 2) {
    int u = q.top(); q.pop();
    Edge e;
    for(Edge& ee : g[u]) {
      if(!was[ee.to]) e = ee;
    }
    was[u] = 1;
    cnt--;
    cout << e.to + 1 << " ";
    c[e.to]--;
    if(c[e.to] == 1) {
      q.push(e.to);
    }
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
