
// Generated at 2025-06-07 16:15:04.672626 
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

//##################CODE BEGIN#############
template <typename Comparator = std::less<int>>
class intheap {
public:
    intheap(size_t max, Comparator cmp = Comparator{}) 
        : data()
        , cmp(std::move(cmp))
        , rev(max + 1)
        , has(max + 1, false) {}

    void push(int x) {
        if (has[x]) exit(1);
        data.push_back(x);
        push_upd();
    }
    
    int pop() {
        if (data.empty()) exit(1);
        swap(0, data.size() - 1);
        int r = std::move(data.back());
        data.pop_back();
        prop_down(0);
        has[r] = false;
        return r;
    }
    
    int peek() {
        if (data.empty()) exit(1);
        return data.front();
    }

    bool contains(int x) {
        if (x >= has.size()) exit(1);
        return has[x];
    }

    void remove(int x) {
        if (x >= has.size()) exit(1);
        if (!has[x]) exit(1);
        has[x] = false;
        auto i = rev[x];
        // DBG() << "remove " << i << " " << data.size() << endl;
        swap(i, data.size() - 1);
        data.pop_back();
        prop_down(prop_up(i));
    }

    bool empty() {
        return data.empty();
    }
private:
    void push_upd() {
        if (data.back() >= rev.size()) exit(1);
        rev[data.back()] = data.size() - 1;
        has[data.back()] = true;
        prop_up(data.size() - 1);
    }

    size_t prop_up(size_t i) {
        while (i > 0) {
            if (cmp(data[i], data[(i - 1) / 2])) {
                swap(i, (i - 1) / 2);
                i = (i - 1) / 2;
            } else {
                break;
            }
        }
        return i;
    }
    
    void prop_down(size_t i) {
        while (true) {
            // DBG() << "prop_down " << i << endl;
            bool f = false;
            size_t ni = 0;
            if (i*2 + 1 < data.size() && cmp(data[i*2 + 1], data[i])) {
                ni = i*2 + 1;
                f = true;
            }
            if (i*2 + 2 < data.size() && 
                cmp(data[i*2 + 2], data[i]) && 
                cmp(data[i*2 + 2], data[i*2 + 1])) {
                ni = i*2 + 2;
                f = true;
            }
            if (!f) {
                break;
            }
            swap(i, ni);
            i = ni;
        }
    }

    void swap(size_t i, size_t j) {
        if (i == j) return;
        std::swap(data[i], data[j]);
        rev[data[i]] = i;
        rev[data[j]] = j;
    }

private:
    vint data;
    Comparator cmp;

    // map<T, size_t>
    vector<size_t> rev;
    vector<bool> has;
};

struct S {
    int i;
    int x;

    bool operator<(const S& other) {
        return x < other.x;
    }
};

//entry
void sol() {
    int n, k, m; cin >> n >> k >> m;

    vector<S> xs;
    vint cs(m);

    for (int i = 0; i < m; ++i) {
        int c, l, r; cin >> c >> l >> r;
        xs.push_back({i, l});
        xs.push_back({i, r + 1});
        cs[i] = c;
    }

    sort(ALL(xs));

    int pi = -1;
    int px = -1;
    vint r(k + 1, 0);
    intheap h(m - 1, std::greater<int>{});
    for (int i = 0; i < xs.size(); ++i) { 
        // DBG() << i << " " << xs[i].i << " " << xs[i].x << endl;
        if (pi != -1) {
            if (px == -1) exit(1);
            r[cs[pi]] += xs[i].x - px;
        }
        if (h.contains(xs[i].i)) {
            h.remove(xs[i].i);
        } else {
            h.push(xs[i].i);
        }
        pi = h.empty() ? -1 : h.peek();
        px = xs[i].x;
    }

    for (int i = 1; i <= k; ++i) {
        cout << r[i] << " ";
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
    #endif

    sol();

    #ifdef LOCAL
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << duration.count() << " microseconds" << endl;
    #endif
}
