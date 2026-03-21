
// Generated at 2026-03-22 01:35:49.201587 
// By iliayar
#define _USE_MATH_DEFINES
#pragma comment(linker, "/STACK:36777216")
#include <iterator>
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
#include <sstream>
#include <numeric>
#include <optional>
#include <variant>
#include <functional>
#include <bitset>
#include <memory>

using namespace std;

#define ON 1
#define OFF 0

#define int long long
#ifdef LOCAL
#define DBG_VAR true
#define DBG_CODE(x) x
#else
#define DBG_VAR false
#define DBG_CODE(x)
#endif

#define DBG() if (DBG_VAR) cout << "DBG: "

#define INF 1e+18
#define ALL(a) a.begin(), a.end()

#define FUNC(retTy, name, args...) std::function<retTy (args)> name = [&](args) -> retTy

using vint = vector<int>;
using vint2 = vector<vint>;

template <typename K, typename V>
struct map_pair {
    K k;
    V v;
};

template <typename T, typename K>
ostream &operator<<(ostream &out, pair<T, K> const& p) {
  out << "(" << p.first << ", " << p.second << ")";
  return out;
}

template<typename T>
class Join {
  T& v;
  string const& separator;
  
public:
  
  Join(T v, string const& separator)
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

template <typename T>
ostream &operator<<(ostream &out, vector<T> v) {
  out << "[" << Join(v, ", ") << "]";
  return out;
}

template <typename K, typename V>
ostream &operator<<(ostream &out, map<K, V> m) {
  vector<map_pair<K, V>> v;
  transform(m.begin(), m.end(), back_inserter(v), [](pair<K, V> const& p){return map_pair<K, V>{p.first, p.second};});
  out << "{" << Join(v, ", ") << "}";
  return out;
}

template <typename K, typename V>
ostream &operator<<(ostream &out, map_pair<K, V> m) {
  out << m.k << ": " << m.v;
  return out;
}

template <typename K>
ostream &operator<<(ostream &out, set<K> s) {
  out << "{" << Join(s, ", ") << "}";
  return out;
}

std::function<void()> finish = [](){ exit(0); };

//##################CODE BEGIN#############
constexpr int M = 1000000007;
int B = rand() % M;

int powmod(int base, int exp) {
    int res = 1;
    while (exp) {
        if (exp & 1) {
            res = (res * base) % M;
        }
        exp /= 2;
        base = (base * base) % M;
    }
    return res;
}

//entry
void sol() {
    string a, b; cin >> a >> b;
    vint ha(a.length() + 1);
    vint hb(b.length() + 1);

    FUNC(void, hinit, vint& h, string s) {
        for (int i = 1; i <= s.length(); ++i) {
            h[i] = (((h[i - 1] * B) % M) + s[i - 1]) % M;
        }
    };

    FUNC(bool, hcmp, int l1, int r1, int l2, int r2) {
        if (r1 - l1 != r2 - l2) return false;
        int xp = powmod(B, r1 - l1);
        int h1 = (ha[r1] - ((ha[l1] * xp) % M) + M) % M;
        int h2 = (hb[r2] - ((hb[l2] * xp) % M) + M) % M;
        // DBG() << h1 << " " << h2 << endl;
        if (h1 != h2) return false;
        // for (int i = 0; i < r1 - l1; ++i) {
        //     if (s[l1 + i] != s[l2 + i]) return false;
        // }
        return true;
    };

    hinit(ha, a);
    hinit(hb, b);

    vint res;
    for (int i = 0; i < a.length() - b.length() + 1; ++i) {
        if (hcmp(i, i + b.length(), 0, b.length())) {
            res.push_back(i + 1);
        }
    }
    cout << res.size() << endl;
    for (int i : res) {
        cout << i << " ";
    }
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
    finish = [&]() {
        auto stop = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
        cout << duration.count() << " microseconds" << endl;
        exit(0);
    };
    #endif

    sol();
    finish();
}
