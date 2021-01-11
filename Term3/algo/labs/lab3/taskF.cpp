
// Generated at 2020-12-10 20:44:50.685660 
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
  T& v;
  string& separator;
  
public:
  
  Join(T v, string separator)
    : v(v), separator(separator)
  {}

  friend ostream& operator<<(ostream& out, Join<T> join) {
    for(auto it = join.v.cbegin(); it != join.v.cend(); ++it) {
      if(it != join.v.cbegin()) out << join.separator;
      out << *it;
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
const int M = 1e+9;
const int B = 31;


vector<string> ss;
vint2 hs;

int maxL = 0;

int pow(int base, int raise, int mod) {
  if(raise == 0) return 1;
  int n = raise;
  int res = 1;
  while(n > 0) {
    if(n % 2 == 0){
      base = (base * base) % mod;
      n /= 2;
    } else {
      res = (res * base) % mod;
      n -= 1;
    }
  }
  return res;
}

int sub_hash(int s, int l, int r, int n = -1) {
  if(n == -1) n = 0;
  else {
    if(l > n) exit(1);
    n = n - ss[s].length() + l;
  }
  if(l == 0) return hs[s][r]*pow(B, n, M) % M;
  return (hs[s][r] - hs[s][l - 1] + M)*pow(B, n, M) % M;
} 

void init_hash(int s) {
  hs[s].resize(ss[s].length(), 0);
  for(int i = 0; i < ss[s].length(); ++i) {
    hs[s][i] = pow(B, ss[s].length() - i - 1, M)*ss[s][i] % M;
  }
  for(int i = 1; i < ss[s].length(); ++i) {
    hs[s][i] += hs[s][i - 1];
    hs[s][i] %= M;
  }
}

set<int> check_bs(int l) {
  set<int> hh;
  for(int i = 0; i + l - 1 < ss[0].length(); ++i) {
    hh.insert(sub_hash(0, i, i + l - 1, maxL));
  }
  for(int i = 1; i < ss.size(); ++i) {
    set<int> hhn;
    for(int j = 0; j + l - 1 < ss[i].length(); ++j) {
      int hhh = sub_hash(i, j, j + l - 1, maxL);
      if(hh.find(hhh) != hh.end()) {
	hhn.insert(hhh);
      }
    }
    hh = move(hhn);
  }
  return hh;
}

//entry
void sol() {
  int n; cin >> n;
  hs.resize(n, vint{});
  ss.resize(n, "");
  int r = INF;
  for(int i = 0; i < n; ++i) {
    cin >> ss[i];
    init_hash(i);
    maxL = max(maxL, (int)ss[i].length());
    r = min(r, (int)ss[i].length());
  }
  int l = 0;
  while(r - l > 1) {
    int m = (r + l)/2;
    set<int> hh = check_bs(m);
    if(hh.size() == 0) {
      r = m;
    } else {
      l = m;
    }
  }
  if(check_bs(r).size() != 0) l = r;
  set<int> hh = check_bs(l);
  for(int h : hh) {
    for(int i = 0; i + l - 1 < ss[0].length(); ++i) {
      if(sub_hash(0, i, i + l - 1, maxL) == h) {
	cout << ss[0].substr(i, l) << endl;
	exit(0);
      }
    }
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
