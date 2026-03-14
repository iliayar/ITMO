
// Generated at 2026-03-16 03:38:17.243940 
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
// template <typename T> struct PtrData {
//     int pool_idx;
//     int counter;
//     std::optional<T> obj;
//
//     PtrData(int pool_idx) : pool_idx(pool_idx), counter(0), obj(std::nullopt) {}
// };
//
// template <typename T> struct Ptr {
//     int idx;
//
//     static std::vector<PtrData<T>> pool;
//     static std::vector<int> pool_free;
//
//     Ptr(std::nullptr_t = nullptr) : idx(-1) {}
//     explicit Ptr(int idx) : idx(idx) {}
//
//     void increment() {
//         if (idx != -1)
//             pool[idx].counter += 1;
//     }
//
//     void decrement() {
//         if (idx == -1) return;
//
//         int old_idx = idx;
//         idx = -1;
//
//         pool[old_idx].counter -= 1;
//         if (pool[old_idx].counter == 0) {
//             pool[old_idx].obj = std::nullopt;
//             pool_free.push_back(old_idx);
//         }
//     }
//
//     Ptr(const Ptr &other) : idx(other.idx) {
//         increment();
//     }
//
//     Ptr(Ptr &&other) noexcept : idx(other.idx) {
//         other.idx = -1;
//     }
//
//     Ptr &operator=(const Ptr &other) {
//         if (this == &other) return *this;
//
//         int new_idx = other.idx;
//         if (new_idx != -1)
//             pool[new_idx].counter += 1;
//
//         decrement();
//         idx = new_idx;
//         return *this;
//     }
//
//     Ptr &operator=(Ptr &&other) noexcept {
//         if (this == &other) return *this;
//
//         int new_idx = other.idx;
//         other.idx = -1;
//
//         decrement();
//         idx = new_idx;
//         return *this;
//     }
//
//     T *operator->() {
//         if (idx == -1) return nullptr;
//         return &pool[idx].obj.value();
//     }
//
//     const T *operator->() const {
//         if (idx == -1) return nullptr;
//         return &pool[idx].obj.value();
//     }
//
//     ~Ptr() {
//         decrement();
//     }
//
//     explicit operator bool() const {
//         return idx != -1;
//     }
// };
//
// template <typename T>
// std::vector<PtrData<T>> Ptr<T>::pool{};
//
// template <typename T>
// std::vector<int> Ptr<T>::pool_free{};
//
// template <typename T, typename... Args>
// Ptr<T> make_ptr(Args&&... args) {
//     T tmp(std::forward<Args>(args)...);   // consume args first
//
//     int idx;
//     if (Ptr<T>::pool_free.empty()) {
//         idx = (int)Ptr<T>::pool.size();
//         Ptr<T>::pool.emplace_back(idx);
//     } else {
//         idx = Ptr<T>::pool_free.back();
//         Ptr<T>::pool_free.pop_back();
//     }
//
//     auto& slot = Ptr<T>::pool[idx];
//     slot.obj.emplace(std::move(tmp));
//     slot.counter = 1;
//     return Ptr<T>(idx);
// }

// template <typename T>
// using Ptr = shared_ptr<T>;
//
// template <typename T, typename... Args>
// Ptr<T> make_ptr(Args&& ...args) {
//     return make_shared<T>(std::forward<Args>(args)...);
// }

template <typename T>
using Ptr = T*;

template <typename T, typename... Args>
Ptr<T> make_ptr(Args&& ...args) {
    return new T(std::forward<Args>(args)...);
}

struct Node {
    int sum;
    Ptr<Node> left;
    Ptr<Node> right;
};

int sum(Ptr<Node> node) {
    if (node) return node->sum;
    return 0;
}

Ptr<Node> update(Ptr<Node> node, int i, int x, int lx, int rx) {
    if(rx - lx == 1) {
        return make_ptr<Node>(x, nullptr, nullptr);
    }
    int m = (lx + rx)/2;
    if (i < m) {
        auto n = update(node->left, i, x, lx, m);
        return make_ptr<Node>(sum(n) + sum(node->right), n, node->right);
    } else {
        auto n = update(node->right, i, x, m, rx);
        return make_ptr<Node>(sum(node->left) + sum(n), node->left, n);
    }
}

Ptr<Node> build(int lx, int rx) {
    if (rx - lx == 1) {
        return make_ptr<Node>(0, nullptr, nullptr);
    }
    int m = (lx + rx) / 2;
    auto ln = build(lx, m);
    auto rn = build(m, rx);
    return make_ptr<Node>(ln->sum + rn->sum, ln, rn);
}

int sum(Ptr<Node> node, int l, int r, int lx, int rx) {
    if (r <= l) return 0;
    if (l == lx && r == rx) return node->sum;
    int m = (lx + rx) / 2;
    return sum(node->left, l, min(m, r), lx, m) + sum(node->right, max(m, l), r, m, rx);
}

int log2(int n) {
    int i = 0;
    while (n != 0) {
        i += 1;
        n /= 2;
    }
    return i;
}

//entry
void sol() {
    int n, m; cin >> n >> m;
    // Ptr<Node>::pool.reserve(n * pow(log2(n), 1));
    // Ptr<Node>::pool_free.reserve(n * pow(log2(n), 1));
    vector<Ptr<Node>> ns;
    ns.push_back(build(0, n));
    for (int i = 0; i < n; ++i) {
        int x; cin >> x;
        ns.push_back(update(ns.back(), x - 1, 1, 0, n));
    }

    for (int i = 0; i < m; ++i) {
        int x, y, k, l; cin >> x >> y >> k >> l;
        cout << sum(ns[y], k - 1, l, 0, n) - sum(ns[x - 1], k - 1, l, 0, n) << endl;
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
