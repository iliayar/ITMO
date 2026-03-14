
// Generated at 2026-03-14 22:08:21.716257 
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
    int count = 1;
    Node* left = nullptr;
    Node* right = nullptr;
    Node* parent = nullptr;
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
    node->size = node->count + size(node->left) + size(node->right);

    if (node->left) {
        node->left->parent = node;
    }
    if (node->right) {
        node->right->parent = node;
    }
}

void propagate_node(Node* node) {
    // nothing
}

Node* join(Node* left, Node* right) {
    if (!left) return right;
    if (!right) return left;

    propagate_node(left);
    propagate_node(right);

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

std::tuple<Node*, Node*, Node*> split(Node* node, Elem value) {
    if (!node) return {nullptr, nullptr, nullptr};
    propagate_node(node);

    if (node->value == value) {
        auto right = node->right;
        node->right = nullptr;
        fix_node(node);
        node->parent = nullptr;
        return {node, right, node};
    } else if (node->value > value) {
        auto [left, right, found] = split(node->left, value);
        node->left = right;
        fix_node(node);
        node->parent = nullptr;
        return {left, node, found};
    } else {
        auto [left, right, found] = split(node->right, value);
        node->right = left;
        fix_node(node);
        node->parent = nullptr;
        return {node, right, found};
    }
}


void update(Node* node) {
    while (node) {
        fix_node(node);
        node = node->parent;
    }
}

// entry
void sol() {
  int n;
  while (cin >> n) {
    std::vector res(n, 0);
    Node *root = nullptr;
    for (int i = 0; i < n; ++i) {
      int x, y;
      cin >> x >> y;

      auto [left, right, found] = split(root, x);
      res[size(left)]++;
      if (found) {
        found->count++;
        update(found);
        root = join(left, right);
      } else {
        root = join(left, join(new Node(x), right));
      }
    }

    for (int i = 0; i < n; ++i) {
      cout << res[i] << endl;
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
