
// Generated at 2020-10-20 23:20:39.977837 
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
struct Node {
  Node() : to(), from(), is_neg(false) {}
  vint to;
  vint from;
  bool is_neg;
};

vector<Node> G;

map<string, int> names;

vector<Node> Gc;
vector<int> p;
vint comp;
vint was;
 
int c = 0;

vint topsort;
vint color;
int ti;

vint res;
vint res1;
 
 
string get_name(int u) {
  int isp = 1;
  if(u >= names.size()) {
    u-=names.size();
    isp = 0;
  }
  for(auto p : names) {
    if(p.second == u) {
      if(isp) return "+" + p.first;
      return '-' + p.first;
    }
  }
  return "NONE";
}

void print_graph() {
  cout << "Initial: " << endl;
  for(int i = 0; i < G.size(); ++i) {
    for(int t : G[i].to) {
      cout << get_name(i) << " => " << get_name(t) << endl;
    }
  }
  cout << endl << "Condeced: " << endl;
  for(int i = 0; i < Gc.size(); ++i) {
    cout << "[ ";
    for(int j = 0; j < names.size()*2; ++j) {
      if(comp[j] == i) cout << get_name(j) << " ";
    }
    cout << "]" << endl; 
  }
  for(int i = 0; i < Gc.size(); ++i) {
    for(int t : Gc[i].to) {
      cout << "[ ";
      for(int j = 0; j < names.size()*2; ++j) {
	if(comp[j] == i) cout << get_name(j) << " ";
      }
      cout << "] => [ ";
      for(int j = 0; j < names.size()*2; ++j) {
	if(comp[j] == t) cout << get_name(j) << " ";
      }
      cout << "]" << endl;
    }
  }
  cout << "Topsort: " << endl;
  for(int u : topsort) {
    cout << res[u] << " [ ";
    for(int j = 0; j < names.size()*2; ++j) {
      if(comp[j] == u) cout << get_name(j) << " ";
    }
    cout << "]" << endl; 
  }
}


int get_id(string s) {
  return names[s.substr(1, s.length() - 1)] + (s[0] == '-' ? names.size() : 0);
}
int invert_id(int u) {
  if(u >= names.size()) return u - names.size();
  return u + names.size();
}

void add_unique(int u, int v) {
  for(int w : Gc[u].to) {
    if(w == v) return;
  }
  Gc[u].to.push_back(v);
}
 
void dfs1(int v) {
  if(was[v]) return;
  was[v] = 1;
  for(int u : G[v].to) {
    dfs1(u);
  }
  p.push_back(v);
}
 
void dfs2(int v) {
  if(comp[v] != -1) return;
  comp[v] = c;
  for(int u : G[v].from) {
    dfs2(u);
  }
}
 
void dfs3(int v) {
  was[v] = 1;
  for(int u : G[v].to) {
    if(comp[v] != comp[u]) add_unique(comp[v], comp[u]);
    if(!was[u]) dfs3(u);
  }
}
 
//entry
void condence() {
  int n = names.size()*2;
  was.resize(n, 0);
  comp.resize(n, -1);
  for(int i = 0; i < n; ++i) {
    dfs1(i);
  }
  for(int i = n - 1; i >= 0; --i) {
    if(comp[p[i]] == -1) {
      dfs2(p[i]);
      c++;
    }
  }
  Gc.resize(c, {});
  was.assign(n, 0);
  for(int i = 0; i < n; ++i) {
    if(!was[i]) dfs3(i);
  }
}
void sort(int u) {
  color[u] = 1;
  for(int v : Gc[u].to) {
    if(color[v] == 1) exit(1);
    if(color[v] == 0) sort(v);
  }
  color[u] = 2;
  topsort[ti] = u;
  ti--;
}

//entry
void sol() {
  int n, m; cin >> n >> m;
  G.resize(n*2, {});
  for(int i = 0; i < n; ++i) {
    string s; cin >> s;
    names[s] = i;
  }
  for(int i = 0; i < m; ++i) {
    string us, vs; cin >> us >> vs >> vs;
    int u = get_id(us);
    int v = get_id(vs);
    G[u].to.push_back(v);
    G[v].from.push_back(u);
    G[invert_id(u)].from.push_back(invert_id(v));
    G[invert_id(v)].to.push_back(invert_id(u));
  }
  condence();
  topsort.resize(c, -1);
  color.resize(c, 0);
  ti = c - 1;
  for(int i = 0; i < c; ++i) {
    if(color[i] == 0) sort(i);
  }
  for(int i = 0; i < n*2; ++i) {
    if(comp[i] == comp[invert_id(i)]) {
      cout << "-1" << endl;
      exit(0);
    }
  }
  res.resize(Gc.size(), -1);
  for(int u : topsort) {
    if(res[u] != -1) continue;
    for(int i = 0; i < n*2; ++i) {
      if(comp[i] == u) {
	res[u] = 0;
	res[comp[invert_id(i)]] = 1;
      }
    }
  }
  DBG_CODE(print_graph());
  res1.resize(n, -1);
  for(int i = 0; i < c; ++i) {
    for(int j = 0; j < n; ++j) {
      if(comp[j] == i) {
	if(res1[j] != -1) exit(1);
	res1[j] = res[i];
      }
    }
  }
  int res2 = 0;
  for(int e : res1) {
    if(e) res2++;
  }
  cout << res2 << endl;
  for(auto p : names) {
    if(res1[p.second]) cout << p.first << endl;
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
