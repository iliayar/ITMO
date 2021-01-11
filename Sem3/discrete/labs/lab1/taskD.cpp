
// Generated at 2020-12-05 03:15:50.985689 
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

#define INF 1e+18

using vint = vector<int>;
using vint2 = vector<vint>;

template<typename T>
class Join {
  vector<T>& v;
  string& separator;
  
public:
  
  Join(vector<T> v, string separator)
    : v(v), separator(separator)
  {}

  friend ostream& operator<<(ostream& out, Join<T> join) {
    for(int i = 0; i < join.v.size(); ++i) {
      if(i != 0) out << join.separator;
      out << join.v[i];
    }
    return out;
  }
};

template<typename T>
ostream& operator<<(ostream& out, vector<T> v) {
  out << Join(v, " ") << endl;
  return out;
}

template<typename T, typename K>
ostream& operator<<(ostream& out, pair<T, K> p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

//##################CODE BEGIN#############
struct Edge {
  int from;
  int to;

  friend ostream& operator<<(ostream& o, Edge& e) {
    o << "(" << e.from << " -> " << e.to << ")";
    return o;
  }
  
};

vector<vector<Edge>> g;
vector<vector<Edge>> gr;

//entry
void sol() {
  int n; cin >> n;
  g.resize(n, vector<Edge>{});
  gr.resize(n, vector<Edge>{});
  
  for (int i = 0; i < n; ++i) {
    for (int j = 0; j < i; ++j) {
      char c; cin >> c; c -= '0';
      if(c) {
	g[i].push_back({i, j});
	gr[j].push_back({i, j});
      } else {
	g[j].push_back({j, i});
	gr[i].push_back({j, i});
      }
    }
  }
  DBG(g);

  vint p;
  for(int i = 0; i < n; ++i) {
    vint a(n, 0);
    for(Edge& e : gr[i]) {
      a[e.from] = 1;
    }
    int j = 0;
    while(j < i && a[p[j]] == 1) j++;
    p.insert(p.begin() + j, i);
  }
  DBG(p);

  int k = n - 1;
  vint c;
  for(; k >= 2; --k) {
    int ok = 0;
    for(Edge& e : g[p[k]]) {
      if(e.to == p[0]) ok = 1;
    }
    if(ok) {
      break;
    }
  }
  k++;
  for (int i = 0; i < k; ++i) {
    c.push_back(p[i]);
  }

  DBG(c);

  int l = k;
  for(int i = k; i < n; ++i) {
    vint a(n, 0);
    for (Edge& e : g[p[i]]) {
      a[e.to] = 1;
    }
    int j = 0;
    for(; j < c.size(); ++j) {
      if(a[c[j]]) break;
    }
    if(j != c.size()) {
      for (; l <= i; ++l, ++j) {
	c.insert(c.begin() + j, p[l]);
      }
      DBG(c);
    }
  }
  
  for(int u : c) cout << u + 1 << " ";

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
