
// Generated at 2026-03-08 15:20:30.048083 
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
    Elem min = value;
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

Elem node_min(Node* node) {
    if (!node) return INF;
    return node->min;
}

void fix_node(Node* node) {
    if (!node) return;
    node->size = 1 + size(node->left) + size(node->right);
    node->min = min(min(node->value, node_min(node->left)), node_min(node->right));
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

Node* remove(Node* node, int i) {
    auto [left, right] = split(node, i);
    auto [_, rightNew] = split(right, 1);
    return join(left, rightNew);
}

void print(Node* node) {
    if (!node) return;
    print(node->left);
    cout << node -> value << " ";
    print(node->right);
}

Elem min(Node* node, int l, int r) {
    if (l >= r || !node) return INF;
    if (l == 0 && size(node) == r) return node->min;

    Elem res = INF;
    if (l < size(node->left)) {
        res = min(res, min(node->left, l, min(size(node->left), r)));
    }
    if (l <= size(node->left) && r > size(node->left)) {
        res = min(res, node->value);
    }
    if (r > size(node->left) + 1) {
        res = min(res, min(node->right, max(0ll, l - size(node->left) - 1), r - size(node->left) - 1));
    }
    return res;
}

//entry
void sol() {
    int n; cin >> n;
    Node* root = nullptr;
    for (int j = 0; j < n; ++j) {
        string cmd; cin >> cmd;
        if (cmd == "+") {
            int i, x; cin >> i >> x;
            root = insert(root, i, x);
        } else if (cmd == "?") {
            int i, j; cin >> i >> j;
            cout << min(root, i - 1, j) << endl;
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
