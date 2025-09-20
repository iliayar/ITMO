
// Generated at 2020-10-20 19:36:30.359619 
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
#define FILE_IO ON
#define FILENAME "avia"

struct Edge {
  int u;
  int v;
  int w;
};
struct Node {
  vector<Edge> to;
  vector<Edge> from;
};
using Graph = vector<Node>;
Graph G;

int n;
int lim;

vector<int> p;
vint comp;
vint was;
 
int c = 0;
 
void dfs1(int v) {
  if(was[v]) return;
  was[v] = 1;
  for(Edge e : G[v].to) {
    if(e.w > lim) continue;
    dfs1(e.v);
  }
  p.push_back(v);
}
void dfs2(int v) {
  if(comp[v] != -1) return;
  comp[v] = c;
  for(Edge e : G[v].from) {
    if(e.w > lim) continue;
    dfs2(e.u);
  }
}
int check() {
  was.assign(n, 0);
  comp.assign(n, -1);
  p.clear();
  c = 0;
  for(int i = 0; i < n; ++i) {
    dfs1(i);
  }
  for(int i = n - 1; i >= 0; --i) {
    if(comp[p[i]] == -1) {
      dfs2(p[i]);
      c++;
    }
  }
  DBG(c << " " << lim);
  return c == 1;
}
//entry
void sol() {
  cin >> n;
  int r = 0;
  int l = 0;
  G.resize(n, {});
  was.resize(n, 0);
  comp.resize(n, -1);
  for(int i = 0; i < n; ++i) {
    for(int j = 0; j < n; ++j) {
      int w; cin >> w;
      r = max(r, w);
      if(i == j) continue;
      G[i].to.push_back({i, j , w});
      G[j].from.push_back({i, j, w});
    }
  }
  while(r - l > 1) {
    lim = (l + r)/2;
    if(check()) {
      r = lim;
    } else {
      l = lim;
    }
  }
  lim = l;
  if(!check()) lim = r;
  cout << lim << endl;
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
