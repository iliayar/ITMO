
// Generated at 2020-10-20 20:38:38.065174 
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
struct Edge {
  int u;
  int v;
  double w;
};

vector<pair<double, double>> P;
double res = 0;
vint A;

double dist(int u, int v) {
  return sqrt((P[u].first - P[v].first) * (P[u].first - P[v].first) +
	      (P[u].second - P[v].second) * (P[u].second - P[v].second));
}

//entry
void sol() {
  int n; cin >> n;
  P.resize(n, {0, 0});
  A.resize(n, 0);
  for(pair<double, double>& p : P) cin >> p.first >> p.second;
  A[0] = 1;
  vector<Edge> Q(n, {-1, -1, 1e+9 });
  for(int i = 0; i < n; ++i) {
    Q[i].u = i;
    Q[i].w = min(Q[i].w, dist(0, i));
  }
  // TODO: Fill heap
  for(int i = 1; i < n; ++i) {
    Edge e = {-1, -1, 1e+9};
    for(int i = 0; i < n; ++i) {
      if(A[Q[i].u]) continue;
      if(e.w > Q[i].w) {
	e = Q[i];
      }
    }
    if(A[e.v] && A[e.u]) exit(1);
    if(A[e.u]) exit(1);
    res += e.w;
    A[e.u] = 1;
    for(int i = 0; i < n; ++i) {
      if(A[Q[i].u]) continue;
      if(Q[i].w > dist(i, e.u)) {
	Q[i].w = dist(i, e.u);
      }
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
