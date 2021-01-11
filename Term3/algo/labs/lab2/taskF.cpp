
// Generated at 2020-11-17 00:50:55.201896 
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

struct Element {
  int u;
  int w;
};

vector<vector<Edge>> g;

//entry
void sol() {
  int n, m; cin >> n >> m;
  g.resize(n, vector<Edge>());
  for(int i = 0; i < m; ++i) {
    int u, v , w; cin >> u >> v >> w; u--; v--;
    g[u].push_back({u, v, w});
    g[v].push_back({v, u, w});
  }
  vint s(3);
  vint sr(n);
  for(int i = 0; i < 3; ++i) {
    cin >> s[i];
    s[i]--;
    sr[s[i]] = i;
  }

  auto cmp = [](Element& lhs, Element& rhs) { return lhs.w > rhs.w; };
  vint2 d(3, vint(n, INF));
  for(int i = 0; i < 3; ++i) {
    priority_queue<Element, vector<Element>, decltype(cmp)> ds(cmp);
    vint A(n, false);
    d[i][s[i]] = 0;
    ds.push({s[i], 0});
    while(!ds.empty()) {
      Element el = ds.top(); ds.pop();
      if(A[el.u]) continue;
      A[el.u] = true;
      for(Edge& e : g[el.u])
	if(d[i][e.to] > d[i][e.from] + e.w) {
	    ds.push({e.to, d[i][e.from] + e.w});
	    d[i][e.to] = d[i][e.from] + e.w;
	  }
    }
  }
  DBG(Join(d, ""));
  sort(s.begin(), s.end());
  int mi = INF;
  do {
    int sum = 0;
    DBG(s);
    for(int i = 1; i < 3; ++i) {
      if(d[sr[s[i - 1]]][s[i]] == INF) {
	sum = INF;
	break;
      }
      sum += d[sr[s[i - 1]]][s[i]];
    }
    mi = min(sum, mi);
  } while(next_permutation(s.begin(), s.end()));
  if(mi == INF) cout << -1;
  else cout << mi;
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
