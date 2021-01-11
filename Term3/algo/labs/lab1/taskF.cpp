
// Generated at 2020-10-18 00:24:30.166319 
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
struct Node {
  Node() : to(), from() {}
  vint to;
  vint from;
};

using Graph = vector<Node>;

Graph g;
Graph cond;
deque<int> p;
vint comp;
vint was;

int c = 0;

int compn = 0;

int res = 0;

void add_unique(int u, int v) {
  for(int w : cond[u].to) {
    if(w == v) return;
  }
  cond[u].to.push_back(v);
}

void dfs1(int v) {
  if(was[v]) return;
  was[v] = 1;
  for(int u : g[v].to) {
    dfs1(u);
  }
  p.push_back(v);
}

void dfs2(int v) {
  if(comp[v] != -1) return;
  comp[v] = c;
  for(int u : g[v].from) {
    dfs2(u);
  }
}

void dfs3(int v) {
  was[v] = 1;
  for(int u : g[v].to) {
    if(comp[v] != comp[u]) add_unique(comp[v], comp[u]);
    if(!was[u]) dfs3(u);
  }
}

//entry
void sol() {
  int n, m; cin >> n >> m;
  g.resize(n, Node());
  comp.resize(n, -1);
  was.resize(n, 0);
  for(int i = 0; i < m; ++i) {
    int u, v; cin >> u >> v; u--; v--;
    g[u].to.push_back(v);
    g[v].from.push_back(u);
  }
  for(int i = 0; i < n; ++i) {
    dfs1(i);
  }
  for(int i = n - 1; i >= 0; --i) {
    if(comp[p[i]] == -1) {
      dfs2(p[i]);
      c++;
    }
  }
  cond.resize(c, Node());
  was.assign(n, 0);
  for(int i = 0; i < n; ++i) {
    if(!was[i]) dfs3(i);
  }
  for(Node u : cond) {
    res += u.to.size();
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
