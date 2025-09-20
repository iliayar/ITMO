
// Generated at 2020-11-14 22:33:29.576125 
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
vint2 g;
vint from;
vint was;
vint res;

void dfs(int u) {
  if(was[u]) {
    return;
  }
  was[u] = true;
  dfs(from[u]);
  res.push_back(u);
}

//entry
void sol() {
  int n; cin >> n;
  const int INF = 1e+9;
  from.resize(n, -1);
  was.resize(n, 0);
  g.resize(n, vint(n, 0));
  for(int i = 0; i < n; ++i) {
    for(int j = 0; j < n; ++j) {
      cin >> g[i][j];
    }
  }

  for(int start = 0; start < n; ++start) {
    from.assign(n, -1);
    was.assign(n, 0);
    vint d(n, INF);
    d[start] = 0;
    int bad;
    for (int k = 0; k < n; ++k) {
      bad = -1;
      for (int u = 0; u < n; ++u) {
	for (int v = 0; v < n; ++v) {
	  if (g[u][v] == 1e+5)
	    continue;
	  if (d[v] > d[u] + g[u][v]) {
	    d[v] = max(-INF, d[u] + g[u][v]);
	    DBG(u << " " << v << " " << d[v] << " " << d[u]);
	    from[v] = u;
	    bad = v;
	  }
	}
      }
    }
    if (bad != -1) {
      dfs(bad);
      cout << "YES" << endl;
      cout << res.size() << endl;
      for (int u : res)
        cout << u + 1 << " ";
      cout << endl;
      exit(0);
    }
  }
  cout << "NO" << endl;
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
