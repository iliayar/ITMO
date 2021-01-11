
// Generated at 2020-11-17 16:38:20.258182 
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


//entry
void sol() {
  int n, m;
  while(cin >> n >> m){
    vector<vector<Edge>> g;
    vector<vector<Edge>> gr;
    g.resize(n, vector<Edge>());
    gr.resize(n, vector<Edge>());
    for(int i = 0; i < m; ++i) {
      int u, v; cin >> u >> v; u--; v--;
      g[u].push_back({u, v});
      gr[v].push_back({u, v});
    }
    vint win(n, 0);
    queue<int> q;
    for(int i = 0; i < n; ++i) {
      if(g[i].size() == 0) {
	win[i] = -1;
	for(Edge& e : gr[i]) {
	  q.push(e.from);
	}
      }
    }
    while(!q.empty()) {
      int u = q.front(); q.pop();
      int ok = true;
      for(Edge& e : g[u]) {
	if(win[e.to] == -1) {
	  win[e.from] = 1;
	  ok = false;
	  break;
	} else if(win[e.to] == 0) {
	  ok = false;
	}
      }
      if(ok) {
	win[u] = -1;
      }
      if(win[u] != 0) {
	for(Edge& e : gr[u]) {
	  if(win[e.from] == 0) {
	    q.push(e.from);
	  }
	}
      }
    }
    for(int w : win) {
      if(w == 0) cout << "DRAW" << endl;
      else if (w == 1) cout << "FIRST" << endl;
      else cout << "SECOND" << endl;
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
    #endif

    sol();

    #ifdef LOCAL
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << duration.count() << " microseconds" << endl;
    #endif
}
