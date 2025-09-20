
// Generated at 2020-12-03 19:18:38.956648 
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
vint2 g;

//entry
void sol() {
  int n; cin >> n;
  g.resize(n, vint(n, 0));
  
  for (int i = 0; i < n; ++i) {
    for (int q = 0; q < i; ++q) {
      char c; cin >> c; c -= '0';
      g[i][q] = c;
      g[q][i] = c;
    }
  }
  DBG(g);
  
  deque<int> q;
  for (int i = 0; i < n; ++i) {
    q.push_back(i);
  }
  for (int i = 0; i < n*(n - 1); ++i) {
    if(!g[q[0]][q[1]]) {
      int j = 2;
      for(; !g[q[0]][q[j]] || !g[q[1]][q[j+1]]; ++j);
      reverse(q.begin() + 1, q.begin() + j + 1);
    }
    q.push_back(q[0]);
    q.erase(q.begin());
  }
  for(int u : q) cout << u + 1 << " ";
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
