
// Generated at 2026-03-25 19:12:50.371686 
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
ostream &operator<<(ostream &out, unordered_map<K, V> m) {
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
constexpr int M = 1217846177;
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

template <typename F> std::pair<int, int> bs(int l, int r, F pred) {
  while (r - l > 1) {
    int m = (l + r) / 2;
    if (pred(m)) {
      l = m;
    } else {
      r = m;
    }
  }

  if (!pred(l)) {
    l--;
    r--;
  }

  return {l, r};
}

//entry
void sol() {
    srand(1);
    int n; cin >> n;
    vector<string> s(n);
    vector<vint> h;
    int ml = INF;
    for (int i = 0; i < n; ++i) {
        cin >> s[i];
        h.emplace_back(s[i].length() + 1);
        for (int j = 1; j <= s[i].length(); ++j) {
            h.back()[j] = (((h.back()[j - 1] * B) % M) + s[i][j - 1]) % M;
        }
        ml = min(ml, (int)s[i].length());
    }

    FUNC(int, get_hash, vint& h, int l1, int r1) {
        int xp = powmod(B, r1 - l1);
        return (h[r1] - ((h[l1] * xp) % M) + M) % M;
    };

    FUNC(int, get_common, int l) {
        unordered_map<int, int> m;
        for (int i = 0; i + l <= s[0].length(); ++i) {
            m[get_hash(h[0], i, i + l)] = i;
        }

        // DBG() << "get_common " << l << endl << m << endl;
        for (int j = 1; j < n; ++j) {
            unordered_map<int, int> mn;
            for (int i = 0; i + l <= s[j].length(); ++i) {
                if (auto it = m.find(get_hash(h[j], i, i + l)); it != m.end()) {
                    if (string_view(s[0]).substr(it->second, l) == string_view(s[j]).substr(i, l)) {
                        mn[it->first] = it->second;
                    }
                }
            }
            swap(mn, m);
            // DBG() << m << endl;
        }

        if (m.empty()) return -1;
        return m.begin()->second;
    };

    auto [l, r] = bs(1, ml, [&](int l) { return get_common(l) != -1; });
    if (get_common(r) != -1) l = r;
    if (l == 0) exit(-1);

    int i = get_common(l);
    cout << s[0].substr(i, l) << endl;
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
