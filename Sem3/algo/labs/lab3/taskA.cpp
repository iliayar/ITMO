
// Generated at 2020-12-08 17:12:43.759791 
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

vint h;
string s;

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

int sub_hash(int l, int r) {
  if(l == 0) return h[r];
  return (h[r] - h[l - 1] + M) % M;
} 

int check(int l1, int r1, int l2, int r2) {
  if(r1 - l1 != r2 - l2) return false;
  if(r1 > r2) {
    swap(l1, l2);
    swap(r1, r2);
  }
  DBG(sub_hash(l1, r1));
  DBG(sub_hash(l2, r2)*pow(B, r2 - r1, M) % M);
  if(sub_hash(l1, r1) == (sub_hash(l2, r2)*pow(B, r2 - r1, M) % M)) {
    // for(int i = l1, j = l2; i <= r1; ++i, ++j) {
    //   if(s[i] != s[j]) return false;
    // }
    return true;
  }
  return false;
}

//entry
void sol() {
  cin >> s;
  h.resize(s.length(), 0);
  for(int i = 0; i < s.length(); ++i) {
    h[i] = pow(B, s.length() - i - 1, M)*s[i] % M;
  }
  for(int i = 1; i < s.length(); ++i) {
    h[i] += h[i - 1];
    h[i] %= M;
  }
  DBG(h);
  int n; cin >> n;
  for(int i = 0; i < n; ++i) {
    int l1, r1, l2, r2; cin >> l1 >> r1 >> l2 >> r2;
    l1--; r1--; l2--; r2--;
    DBG(sub_hash(l1, r1));
    DBG(sub_hash(l2, r2));
    if(check(l1, r1, l2, r2)) cout << "Yes";
    else cout << "No"; cout << endl;
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
