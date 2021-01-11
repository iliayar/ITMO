
// Generated at 2020-10-21 02:27:01.349912 
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
#define INF 1e+9 + 1

struct Edge {
  int from;
  int to;
  int w;
  int id;
  bool operator==(Edge& other) {
    return other.from == from && other.to == to && other.w == w;
  }
  bool operator!=(Edge& other) {
    return !(other == *this);
  }
};

struct Node {
  vector<Edge> from;
  vector<Edge> to;
};

vector<Node> Gc;
vector<Edge> Ec;
vector<Edge> En;
deque<int> p;
vint comp;
vint was;
vint zeroEdges;
vint minEdges;
int root = 0;
 
int c = 0;
int n, m;

void print_Gc() {
  for(int i = 0; i < Gc.size(); ++i) {
    for(Edge e : Gc[i].to) {
      cout << e.from << " -> " << e.to << endl;
    }
  }
}
 
void dfs1(int v) {
  if(was[v]) return;
  was[v] = 1;
  for(Edge e : Gc[v].to) {
    if(zeroEdges[e.id]) {
      dfs1(e.to);
    }
  }
  p.push_back(v);
}
 
void dfs2(int v) {
  if(comp[v] != -1) return;
  comp[v] = c;
  for(Edge e : Gc[v].from) {
    if(zeroEdges[e.id]) {
      dfs2(e.from);
    }
  }
}

void condensation() {
  comp.assign(Gc.size(), -1);
  was.assign(Gc.size(), 0);
  p.clear();
  c = 0;
  for(int i = 0; i < Gc.size(); ++i) {
    dfs1(i);
  }
  for(int i = Gc.size() - 1; i >= 0; --i) {
    if(comp[p[i]] == -1) {
      dfs2(p[i]);
      c++;
    }
  }
  Gc.clear();
  Gc.resize(c, {});
  root = comp[root];
}

vint was_check;

void dfs(int u) {
  was_check[u] = 1;
  for(Edge e : Gc[u].to) {
    if(!was_check[e.to] && zeroEdges[e.id]) {
      dfs(e.to);
    }
  }
}

int check() {
  was_check.assign(Gc.size(), 0);
  dfs(root);
  for(int i = 0; i < Gc.size(); ++i) {
    if(!was_check[i]) return 0;
  }
  return 1;
}

int findMST() {
  DBG("findMST");
  DBG_CODE(print_Gc());
  int res = 0;
  minEdges.assign(Gc.size(), INF);
  for(Edge e : Ec) {
    minEdges[e.to] = min(e.w, minEdges[e.to]);
  }
  for(int v = 0; v < Gc.size(); ++v) {
    if(v == root) continue;
    res += minEdges[v];
  }
  zeroEdges.assign(Ec.size(), 0);
  for(Edge e : Ec) {
    if(e.w == minEdges[e.to]) {
      zeroEdges[e.id] = 1;
    }
  }
  if(check()) return res;
  condensation();
  En.clear();
  for(Edge e : Ec) {
    if(comp[e.to] != comp[e.from]) {
      Edge ne = {comp[e.from], comp[e.to], e.w - minEdges[e.to], En.size()};
      Gc[comp[e.from]].to.push_back(ne);
      Gc[comp[e.to]].from.push_back(ne);
      En.push_back(ne);
    }
  }
  swap(Ec, En);
  if(Ec.empty()) {
    cout << "NO" << endl;
    exit(0);
  }
  return res + findMST();
}

//entry
void sol() {
  cin >> n >> m;
  Gc.resize(n, {});
  comp.resize(n, -1);
  was.resize(n, 0);
  was_check.resize(n, 0);
  zeroEdges.resize(m, 1);
  minEdges.resize(n, INF);
  for(int i = 0; i < m; ++i) {
    int u, v, w; cin >> u >> v >> w;
    u--; v--;
    Edge ne = {u, v, w, i};
    Gc[u].to.push_back(ne);
    Gc[v].from.push_back(ne);
    Ec.push_back(ne);
  }
  if(!check()) {
    cout << "NO" << endl;
    return;
  }
  int res = findMST();
  cout << "YES" << endl;
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
