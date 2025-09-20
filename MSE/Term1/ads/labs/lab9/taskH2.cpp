
// Generated at 2025-07-08 20:13:52.752993 
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

//##################CODE BEGIN#############
struct S {
    int i = -1, cnt = 0, l = -1, r = -1;
};

//entry
void sol() {
    string s; cin >> s;

    vint cc(26, 0);
    for (char c : s) {
        cc[c - 'a']++;

    }

    vector<S> r;
    auto cmp = [&](int i, int j) { return r[i].cnt > r[j].cnt; };
    auto h = std::priority_queue<int, std::vector<int>, decltype(cmp)>(cmp);

    int total = 0;
    vint rev;
    for (int i = 0; i < 26; ++i) {
        if (cc[i] != 0) {
            int j = (int)r.size();
            r.push_back({
                .i = j,
                .cnt = cc[i],
            });
            h.push(j);
            rev.push_back(i);
            total++;
        }
    }

    while (h.size() >= 2) {
        int li = h.top(); h.pop();
        int ri = h.top(); h.pop();

        int i = (int)r.size();
        r.push_back({
            .i = i,
            .cnt = r[li].cnt + r[ri].cnt,
            .l = li,
            .r = ri,
        });
        h.push(i);
        DBG() << i << " -> " << li << ", " << ri << endl;
    }

    vector<string> res(26);
    std::queue<std::pair<int, std::string>> q;
    q.push({r.size() - 1, ""});
    while (!q.empty()) {
        auto [i, s] = q.front(); q.pop();
        if (r[i].l == -1 && r[i].r == -1) {
            res[rev[i]] = s.empty() ? "0" : s;
        } else {
            q.push({r[i].l, s + "0"});
            q.push({r[i].r, s + "1"});
        }
    }

    string dec;
    for (char c : s) {
        dec += res[c - 'a'];
    }

    cout << total << " " << dec.length() << endl;
    for (int i = 0; i < res.size(); ++i) {
        if (!res[i].empty()) {
            cout << (char)('a' + i) << ": " << res[i] << endl;
        }
    }
    cout << dec << endl;
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
