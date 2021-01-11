
// Generated at 2020-11-13 03:42:45.862620 
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

using vint = vector<int>;
using vint2 = vector<vint>;

template<typename T>
ostream& operator<<(ostream& out, vector<T> v) {
  for(T e : v) out << e << " ";
  return out;
}

//##################CODE BEGIN#############
//entry
void sol() {
  int n, m; cin >> n >> m;
  vector<vector<pair<int,int>>> g(n, vector<pair<int, int>>());
  for(int i = 0; i < m; ++i) {
    int u, v , w; cin >> u >> v >> w; u--; v--;
    g[u].push_back(make_pair(v, w));
    g[v].push_back(make_pair(u, w));
  }

  vint d(n, 1e+9);
  d[0] = 0;
  while(true) {
    bool ok = true;
    for(int u = 0; u < n; ++u) {
      for(auto& p : g[u]) {
	if(d[p.first] > d[u] + p.second) {
	  d[p.first] = d[u] + p.second;
	  ok = false;
	}
      }
    }
    if(ok) {
      break;
    }
  }
  for(int i = 0; i < n; ++i) {
    cout << d[i] << " ";
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
