
// Generated at 2020-10-11 03:58:25.470460 
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

vint res{};

void dfs(int u, int from) {
  was[u] = 1;
  up[u] = in[u] = T++;
  int c = 0;
  for(EdgeTo e : g[u]) {
    if(e.v == from) continue;
    if(!was[e.v]) {
      dfs(e.v, u);
      up[u] = min(up[u], up[e.v]);
      if(up[e.v] >= in[u]) {
	c++;
      }
    } else {
      up[u] = min(up[u], in[e.v]);
    }
  }
  if(c > 0) {
    if(from == -1 && c > 1) {
      res.push_back(u + 1);
    } else if(from != -1) {
      res.push_back(u + 1);
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
  for(int i = 0; i < m; ++i) {
    int u, v; cin >> u >> v; u--; v--;
    g[u].push_back({v, i});
    g[v].push_back({u, i});
  }
  for(int i = 0; i < n; ++i) {
    if(!was[i]) dfs(i, -1);
  }
  sort(res.begin(), res.end());
  cout << res.size() << endl;
  for(int e : res) {
    cout << e << " ";
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
