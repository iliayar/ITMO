
// Generated at 2020-10-10 19:41:32.363394 
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

vint2 g;

vint topsort;

vint color;

int ti;

void sort(int u) {
  color[u] = 1;
  for(int v : g[u]) {
    if(color[v] == 1) {
      cout << "-1" << endl;
      exit(0);
    }
    if(color[v] == 0) sort(v);
  }
  color[u] = 2;
  topsort[ti] = u + 1;
  ti--;
}

//entry
void sol() {
  int n, m; cin >> n >> m;
  g.resize(n, vint());
  topsort.resize(n, -1);
  color.resize(n, 0);
  ti = n - 1;
  for(int i = 0; i < m; ++i) {
    int u, v; cin >> u >> v; u--; v--;
    g[u].push_back(v);
  }
  for(int i = 0; i < n; ++i) {
    if(color[i] == 0) sort(i);
  }
  for(int u : topsort) {
    cout << u <<  " ";
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
