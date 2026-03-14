
// Generated at 2026-03-16 23:45:52.495638 
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
// template <typename T>
// using Ptr = T*;
//
// template <typename T, typename... Args>
// Ptr<T> make_ptr(Args&& ...args) {
//     return new T(std::forward<Args>(args)...);
// }

// template <typename T>
// using Ptr = shared_ptr<T>;
//
// template <typename T, typename... Args>
// Ptr<T> make_ptr(Args&& ...args) {
//     return make_shared<T>(std::forward<Args>(args)...);
// }

template <typename T> struct PtrData {
    int pool_idx;
    int counter;
    std::optional<T> obj;

    PtrData(int pool_idx) : pool_idx(pool_idx), counter(0), obj(std::nullopt) {}
};

template <typename T> struct Ptr {
    int idx;

    static std::vector<PtrData<T>> pool;
    static std::vector<int> pool_free;

    Ptr(std::nullptr_t = nullptr) : idx(-1) {}
    explicit Ptr(int idx) : idx(idx) {}

    void increment() {
        if (idx != -1)
            pool[idx].counter += 1;
    }

    void decrement() {
        if (idx == -1) return;

        int old_idx = idx;
        idx = -1;

        pool[old_idx].counter -= 1;
        if (pool[old_idx].counter == 0) {
            pool[old_idx].obj = std::nullopt;
            pool_free.push_back(old_idx);
        }
    }

    Ptr(const Ptr &other) : idx(other.idx) {
        increment();
    }

    Ptr(Ptr &&other) noexcept : idx(other.idx) {
        other.idx = -1;
    }

    Ptr &operator=(const Ptr &other) {
        if (this == &other) return *this;

        int new_idx = other.idx;
        if (new_idx != -1)
            pool[new_idx].counter += 1;

        decrement();
        idx = new_idx;
        return *this;
    }

    Ptr &operator=(Ptr &&other) noexcept {
        if (this == &other) return *this;

        int new_idx = other.idx;
        other.idx = -1;

        decrement();
        idx = new_idx;
        return *this;
    }

    T *operator->() {
        if (idx == -1) return nullptr;
        return &pool[idx].obj.value();
    }

    const T *operator->() const {
        if (idx == -1) return nullptr;
        return &pool[idx].obj.value();
    }

    ~Ptr() {
        decrement();
    }

    explicit operator bool() const {
        return idx != -1;
    }
};

template <typename T>
std::vector<PtrData<T>> Ptr<T>::pool{};

template <typename T>
std::vector<int> Ptr<T>::pool_free{};

template <typename T, typename... Args>
Ptr<T> make_ptr(Args&&... args) {
    T tmp(std::forward<Args>(args)...);

    int idx;
    if (Ptr<T>::pool_free.empty()) {
        idx = (int)Ptr<T>::pool.size();
        Ptr<T>::pool.emplace_back(idx);
    } else {
        idx = Ptr<T>::pool_free.back();
        Ptr<T>::pool_free.pop_back();
    }

    auto& slot = Ptr<T>::pool[idx];
    slot.obj.emplace(std::move(tmp));
    slot.counter = 1;
    return Ptr<T>(idx);
}

vint psum;
vint arr;

struct Node {
  int lx;
  int rx;
  Ptr<Node> left = nullptr;
  Ptr<Node> right = nullptr;
  int size = rx - lx;
  int sum = psum[rx] - psum[lx];
  int y = rand();
};

void debug_print(ostream& out, Ptr<Node> node, int depth) {
    if (!node) return;
    debug_print(out, node->right, depth+1);
    out << string("  ", depth) << "[" << node->lx << " " << node->rx << ") sum=" << node->sum << endl;
    debug_print(out, node->left, depth+1);
}

ostream& operator<<(ostream& out, Ptr<Node> node) {
    debug_print(out, node, 0);
    return out;
}

int len(Ptr<Node> node) { return node ? node->rx - node->lx : 0; }
int size(Ptr<Node> node) { return node ? node->size : 0; }
int sum(Ptr<Node> node) { return node ? node->sum : 0; }

void fix_node(Ptr<Node>& node) {
  if (!node)
    return;
  node->size = len(node) + size(node->left) + size(node->right);
  node->sum = psum[node->rx] - psum[node->lx] + sum(node->left) + sum(node->right);
}

Ptr<Node> create_node(int lx, int rx, Ptr<Node> const& left, Ptr<Node> const& right) {
  if (lx == rx) return nullptr;
  auto node = make_ptr<Node>(lx, rx, left, right);
  fix_node(node);
  return node;
}

Ptr<Node> create_node(Ptr<Node> orig, Ptr<Node> left, Ptr<Node> right) {
  auto node = make_ptr<Node>(orig->lx, orig->rx, left, right);
  fix_node(node);
  return node;
}

Ptr<Node> join(Ptr<Node> left, Ptr<Node> right) {
  if (!left)
    return right;
  if (!right)
    return left;

  if (left->y < right->y) {
    return create_node(right, join(left, right->left), right->right);
  } else {
    return create_node(left, left->left, join(left->right, right));
  }
}

std::tuple<Ptr<Node>, Ptr<Node>> split(Ptr<Node> const& node, int i) {
  if (!node)
    return {nullptr, nullptr};

  if (i < size(node->left)) {
    auto [left, right] = split(node->left, i);
    return {left, create_node(node, right, node->right)};
  } else if (i > size(node->left) + len(node)) {
    auto [left, right] = split(node->right, i - size(node->left) - len(node));
    return {create_node(node, node->left, left), right};
  }

  int lsz = i - size(node->left);
  // DBG() << "splitting " << node->lx << " " << node->lx + lsz << " " << node->rx
  //       << endl;
  return {
      join(node->left, create_node(node->lx, node->lx + lsz, nullptr, nullptr)),
      join(create_node(node->lx + lsz, node->rx, nullptr, nullptr),
           node->right)};
}

// int prefix_sum(Ptr<Node> node, int i) {
//   if (!node)
//     return 0;
//   if (size(node->left) == i)
//     return sum(node->left) + get_psum(node->lx, node->rx);
//   if (i < size(node->left))
//     return prefix_sum(node->left, i);
//   if (size(node->left) < i)
//     return sum(node->left) + get_psum(node->lx, node->rx) +
//            prefix_sum(node->right, i - size(node->left) - 1);
//   return 0;
// }

// int sum(Ptr<Node> node, int l, int r) {
//     auto [tmp, right] = split(node, r);
//     // DBG() << "sum split " << r << endl << tmp << "=======" << endl << right;
//     auto [left, mid] = split(tmp, l);
//     // DBG() << "sum split " << l << endl << left << "=======" << endl << mid;
//     return sum(mid);
// }

int prefix_sum(Ptr<Node> node, int i) {
    if (!node) return 0;
    if (i < size(node->left)) {
        return prefix_sum(node->left, i);
    } else if (i >= size(node->left) + len(node)) {
      return prefix_sum(node->right, i - size(node->left) - len(node)) +
             sum(node->left) + psum[node->rx] - psum[node->lx];
    }

    int lsz = i - size(node->left);
    return sum(node->left) + psum[node->lx + lsz] - psum[node->lx];
}

int sum(Ptr<Node> node, int l, int r) {
    return prefix_sum(node, r) - prefix_sum(node, l);
}

Ptr<Node> copy(Ptr<Node> node, int a, int b, int l) {
    // DBG() << "copy " << a << " " << b << " " << l << endl;
    auto [a_left, a_tmp] = split(node, a);
    auto [a_chunk, a_right] = split(a_tmp, l);

    // DBG() << "a_chunk " << endl << a_chunk << endl;

    auto [b_left, b_tmp] = split(node, b);
    auto [b_chunk, b_right] = split(b_tmp, l);

    // DBG() << "b_left " << endl << b_left << endl;
    // DBG() << "b_right " << endl << b_right << endl;

    // DBG() << "copy " << a_chunk->lx << " " << a_chunk->rx << endl;
    return join(b_left, join(a_chunk, b_right));
}


void print(ostream& out, Ptr<Node> node, int l, int r) {
    if (!node) return;

    int diff = size(node->left) + len(node);
    if (l < size(node->left)) {
        print(out, node->left, l, r);
    }
    if (l < size(node->left) + len(node) && r > size(node->left)) {
      for (int i = max(0ll, l - size(node->left));
           i < min(len(node), r - size(node->left)); ++i) {
        out << arr[node->lx + i] << " ";
      }
    }
    if (r > size(node->left) + len(node)) {
        print(out, node->right, l - diff, r - diff);
    }
}

//entry
void sol() {
    // constexpr int POOL_SIZE = (512 << 20) / (sizeof(PtrData<Node>) + sizeof(int)) / 2;
    // Ptr<Node>::pool.reserve(POOL_SIZE);
    // Ptr<Node>::pool_free.reserve(POOL_SIZE);
    srand(2);
    int n; cin >> n; 
    arr.resize(n);
    psum.resize(n + 1);

    int X1, A, B, M; cin >> X1 >> A >> B >> M;
    for (int i = 0; i < n; ++i) {
        arr[i] = X1;
        psum[i + 1] = psum[i] + X1;
        X1 = ((A * X1) % M + B) % M;
    }

    Ptr<Node> root = create_node(0, n, nullptr, nullptr);

    int k; cin >> k;
    for (int i = 0; i < k; ++i) {
        string cmd; cin >> cmd;
        if (cmd == "out") {
            int l, r; cin >> l >> r; l--; r--;
            print(cout, root, l, r + 1); cout << endl;
        } else if (cmd == "cpy") {
            int a, b, l; cin >> a >> b >> l; a--; b--;
            root = copy(root, a, b, l);
        } else if (cmd == "sum") {
            int l, r; cin >> l >> r; l--; r--;
            cout << sum(root, l, r + 1) << endl;
        }
        // DBG() << endl << root << endl;
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
