
// Generated at 2020-10-14 20:38:41.657213 
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

using vint = vector<int>;
using vint2 = vector<vint>;

//##################CODE BEGIN#############
struct EdgeTo {
  int v;
  int id;
};

vector<vector<EdgeTo>> g;

vint up;
vint in;

vint was;

int T = 0;

vint comp{};
int compn = 0;
deque<int> d{};

void dfs(int u, int from = -1) {
  was[u] = 1;
  up[u] = in[u] = T++;
  d.push_back(u);
  for(EdgeTo e : g[u]) {
    if(e.id == from) continue;
    if(!was[e.v]) {
      dfs(e.v, e.id);
      up[u] = min(up[u], up[e.v]);
      if(up[e.v] == in[e.v]) {
	compn++;
	while(d.back() != e.v) {
	  comp[d.back()] = compn;
	  DBG("Marking " << d.back() << " as " << compn); 
	  d.pop_back();
	}
	comp[d.back()] = compn;
	d.pop_back();
      }
    } else {
      up[u] = min(up[u], in[e.v]);
    }
  }
}

//entry
void sol() {
  int n, m; cin >> n >> m;
  g.resize(n, vector<EdgeTo>());
  up.resize(n, -1);
  in.resize(n, -1);
  was.resize(n, 0);
  comp.resize(n, -1);
  for(int i = 0; i < m; ++i) {
    int u, v; cin >> u >> v; u--; v--;
    g[u].push_back({v, i});
    g[v].push_back({u, i});
  }
  for(int i = 0; i < n; ++i) {
    if(!was[i]) {
      dfs(i);
      compn++;
      while(!d.empty()) {
	comp[d.back()] = compn;
	d.pop_back();
      }
    }
  }
  cout << compn << endl;
  for(int u : comp) {
    cout << u << " ";
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
