
// Generated at 2026-03-08 19:16:32.552999 
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
    Elem sum = value;
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

Elem node_sum(Node* node) {
    if (!node) return 0;
    return node->sum;
}

void fix_node(Node* node) {
    if (!node) return;
    node->size = 1 + size(node->left) + size(node->right);
    node->sum = node->value + node_sum(node->left) + node_sum(node->right);

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

std::tuple<Node*, Node*> split(Node* node, int i) {
    if (!node) return {nullptr, nullptr};
    propagate_node(node);

    if (size(node->left) == i) {
        auto left = node->left;
        node->left = nullptr;
        fix_node(node);
        if (left) left->parent = nullptr;
        node->parent = nullptr;
        return {left, node};
    } else if (size(node->left) > i) {
        auto [left, right] = split(node->left, i);
        node->left = right;
        fix_node(node);
        if (left) left->parent = nullptr;
        node->parent = nullptr;
        return {left, node};
    } else {
        if (node->right) node->right->parent = nullptr;
        auto [left, right] = split(node->right, i - size(node->left) - 1);
        node->right = left;
        fix_node(node);
        if (right) right->parent = nullptr;
        node->parent = nullptr;
        return {node, right};
    }
}

void print(Node* node) {
    if (!node) return;
    propagate_node(node);
    print(node->left);
    cout << node -> value << " ";
    print(node->right);
}

Node* get_root(Node* node) {
    if (!node) return nullptr;
    while (node->parent) {
        node = node->parent;
    }
    return node;
}

void update(Node* node, Elem value) {
    if (!node) return;
    node->value = value;
    while (node) {
        fix_node(node);
        node = node->parent;
    }
}

//entry
void sol() {
    int n, m; cin >> n >> m;
    vector<Node*> boys(n, nullptr);
    for (int i = 0; i < n; ++i) {
        boys[i] = new Node(i + 1);
    }
    for (int i = 0; i < m; ++i) {
        string cmd; cin >> cmd;
        if (cmd == "link") {
            int a, b; cin >> a >> b; a--; b--;
            auto aRoot = get_root(boys[a]);
            auto bRoot = get_root(boys[b]);
            if (aRoot != bRoot) {
                join(aRoot, bRoot);
            }
        } else if (cmd == "split") {
            int a, k; cin >> a >> k; a--;
            auto aRoot = get_root(boys[a]);
            auto [left, right] = split(aRoot, k);
            // if (left->parent != nullptr || right->parent != nullptr) exit(69);
        } else if (cmd == "interest") {
            int a, x; cin >> a >> x; a--;
            update(boys[a], x);
        } else if (cmd == "sum") {
            int a; cin >> a; a--;
            cout << node_sum(get_root(boys[a])) << endl;
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
