
// Generated at 2020-11-12 21:24:58.571930 
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
  
  int n; cin >> n;

  vint2 d(n, vint(n, 0));
  
  for(int i = 0; i < n; ++i) {
    for(int j = 0; j < n; ++j) {
      int w; cin >> w;
      d[i][j] = w;
    }
  }


  for(int k = 0; k < n; ++k) {
    for(int u = 0; u < n; ++u) {
      for(int v = 0; v < n; ++v) {
	d[u][v] = min(d[u][v], d[u][k] + d[k][v]);
      }
    }
  }

  for(int i = 0; i < n; ++i) {
    for(int j = 0; j < n; ++j) {
      cout << d[i][j] << " ";
    }
    cout << endl;
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
