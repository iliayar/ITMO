
// Generated at 2026-03-08 14:35:05.720894 
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
using Elem = int;

struct Node {
    Elem value;
    int y = rand();
    int size = 1;
    Node* left;
    Node* right;
};

void dbg_print(ostream& out, Node* node, int depth = 0) {
    if (!node) return;
    dbg_print(out, node->left, depth + 1);
    out << string(depth*2, ' ') << "value=" << node->value << " y=" << node->y << " size=" << node->size << endl;
    dbg_print(out, node->right, depth + 1);
}

ostream& operator<<(ostream& out, Node* node) {
    dbg_print(out, node);
    return out;
}

int size(Node* node) {
    return node ? node->size : 0;
}

void fix_node(Node* node) {
    if (!node) return;
    node->size = 1 + size(node->left) + size(node->right);
}

Node* join(Node* left, Node* right) {
    if (!left) return right;
    if (!right) return left;

    if (left->y < right->y) {
        right->left = join(left, right->left);
        fix_node(right);
        return right;
    } else {
        left->right = join(left->right, right);
        fix_node(left);
        return left;
    }
}

std::tuple<Node*, Node*> split(Node* node, int i) {
    if (!node) return {nullptr, nullptr};

    if (size(node->left) == i) {
        auto left = node->left;
        node->left = nullptr;
        fix_node(node);
        return {left, node};
    } else if (size(node->left) > i) {
        auto [left, right] = split(node->left, i);
        node->left = right;
        fix_node(node);
        return {left, node};
    } else {
        auto [left, right] = split(node->right, i - size(node->left) - 1);
        node->right = left;
        fix_node(node);
        return {node, right};
    }
}

Node* insert(Node* node, int i, Elem value) {
    auto [left, right] = split(node, i);
    return join(left, join(new Node(value), right));
}

// Node* find(Node* node, int x) {
//     if (!node) return nullptr;
//     if (node->x == x) return node;
//     else if (node->x < x) return find(node->right, x);
//     else return find(node->left, x);
// }

// Node* remove(Node* node, int x) {
//     if (!node) return nullptr;
//     if (node->x == x) {
//         auto res = join(node->left, node->right);
//         delete node;
//         return res;
//     } else if (node->x < x) {
//         node->right = remove(node->right, x);
//         fix_node(node);
//         return node;
//     } else {
//         node->left = remove(node->left, x);
//         fix_node(node);
//         return node;
//     }
// }

// Node* upper_bound(Node* node, int x) {
//     if (!node) return nullptr;
//     if (node->x > x) {
//         auto node_left = upper_bound(node->left, x);
//         return node_left ? node_left : node;
//     }
//     return upper_bound(node->right, x);
// }
//
// Node* lower_bound(Node* node, int x) {
//     if (!node) return nullptr;
//     if (node->x < x) {
//         auto node_right = lower_bound(node->right, x);
//         return node_right ? node_right : node;
//     }
//     return lower_bound(node->left, x);
// }
//
// Node* kth(Node* node, int k) {
//     if (!node) return nullptr;
//     if (k < size(node->left)) {
//         return kth(node->left, k);
//     } else if (k == size(node->left)) {
//         return node;
//     } else {
//         return kth(node->right, k - size(node->left) - 1);
//     }
// }
//
//
// Node* kth_max(Node* node, int k) {
//     if (!node) return nullptr;
//     if (k == size(node->right)) {
//         return node;
//     } else if (k > size(node->right)) {
//         return kth_max(node->left, k - size(node->right) - 1);
//     } else {
//         return kth_max(node->right, k);
//     }
// }

void print(Node* node) {
    if (!node) return;
    print(node->left);
    cout << node -> value << " ";
    print(node->right);
}

//entry
void sol() {
    int i, x;
    Node* root = nullptr;
    while (cin >> i >> x) {
        root = insert(root, i, x);
    }
    print(root); cout << endl;
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
