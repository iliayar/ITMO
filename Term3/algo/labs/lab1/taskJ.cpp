// Generated at 2020-10-19 12:16:05.418524 
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
struct Edge {
  int u;
  int v;
  int w;
};

vector<Edge> E;
vint dsf;
vint sz;
int res = 0;

int get(int x) {
  if(dsf[x] == -1) return x;
  return get(dsf[x]);
}
void merge(int x, int y) {
  int xp = get(x);
  int yp = get(y);
  if(sz[xp] > sz[yp]) {
    dsf[yp] = xp;
    sz[xp] += sz[yp];
  } else {
    dsf[xp] = yp;
    sz[yp] += sz[xp];
  }
}

//entry
void sol() {
  int n, m; cin >> n >> m;
  E.resize(m, {});
  dsf.resize(n, -1);
  sz.resize(n, 1);
  for(Edge& e : E) {
    cin >> e.u >> e.v >> e.w;
    e.u--; e.v--;
  }
  sort(E.begin(), E.end(), [](Edge& a, Edge& b) { return a.w < b.w; });
  for(Edge& e : E) {
    if(get(e.u) != get(e.v)) {
      res += e.w;
      merge(e.u, e.v);
    }
  }
  cout << res << endl;
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
