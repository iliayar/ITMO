
// Generated at 2020-04-08 23:33:54.920838 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>
#include <map>
#include <ctime>
#include <cstdlib>


using namespace std;

#define ON 1
#define OFF 0

#define int long long
#define vint vector<int>
#ifdef LOCAL
#define DBG(x) cout << "DBG: " << x << endl
#define DBG_CODE(x) x
#else
#define DBG(x)
#define DBG_CODE(x)
#endif

//##################CODE BEGIN#############
struct Node {
    int value;
    int h;
    int size;
    Node * left;
    Node * right;

    Node(int value, int h = 1)
        : value(value), h(h), size(1), left(nullptr), right(nullptr) {}
};

Node * root = nullptr;

const int INF = 1000000001;

int h_get(Node *v) { return v == nullptr ? 0 : v->h; }

int h_diff(Node *v) { return h_get(v->right) - h_get(v->left); }

void h_upd(Node * v) { v->h = max(h_get(v->left), h_get(v->right)) + 1; }

void size_upd(Node *v) {
    v->size = (v->left == nullptr ? 0 : v->left->size) +
              (v->right == nullptr ? 0 : v->right->size) +
        1;
  // DBG("sum_upd " << v->value << " " << v->sum);
}

int size(Node * v) {
    return v == nullptr ? 0 : v->size;
}

Node *l_rotate(Node *a) {
  Node *b = a->right;
  a->right = b->left;
  b->left = a;
  h_upd(a);
  h_upd(b);
  size_upd(a);
  size_upd(b);
  return b;
}
Node *r_rotate(Node *a) {
  Node *b = a->left;
  a->left = b->right;
  b->right = a;
  h_upd(a);
  h_upd(b);
  size_upd(a);
  size_upd(b);
  return b;
}

Node * balance(Node * v) {
    if(v == nullptr) return v;
    h_upd(v);
    size_upd(v);
    if(h_diff(v) <= -2) {
        if(h_diff(v->left) >= 1) {
          v->left = l_rotate(v->left);
        }
        return r_rotate(v);
    } else if(h_diff(v) >= 2) {
        if(h_diff(v->right) <= -1) {
          v->right = r_rotate(v->right);
        }
        return l_rotate(v);
    }
    return v;
}


Node * find(int x, Node * v)
{
    if(v == nullptr) return nullptr;
    if(v->value == x) return v;
    if(x < v->value) return find(x, v->left);
    else return find(x, v->right);
}


Node * insert(int x, Node * v)
{
    if(v == nullptr) {
        return new Node(x);
    } else if(x < v->value) {
        v->left = insert(x, v->left);
    } else if(x > v->value) {
        v->right = insert(x, v->right);
    }
    return balance(v);
}

Node * min(Node * v)
{
    if(v->left == nullptr)
        return v;
    return min(v->left);
}

Node * max(Node * v)
{
    if(v->right == nullptr)
        return v;
    return min(v->right);
}

Node * next(int x, Node * v, Node * min = nullptr)
{
    if(v == nullptr) return min;
    if(v->value > x) return next(x, v->left, v);
    else return next(x, v->right, min);
}

Node * prev(int x, Node * v, Node * max = nullptr)
{
    if(v == nullptr) return max;
    if(v->value < x) return prev(x, v->right, v);
    else return prev(x, v->left, max);
}


Node * remove(int x, Node * v) {
    if(v == nullptr)
        return v;
    if(x < v->value) {
        v->left = remove(x, v->left);
    } else if(x > v->value) {
        v->right = remove(x, v->right);
    } else if(v->left != nullptr && v->right != nullptr) {
        v->value = next(v->value, root)->value;
        v->right = remove(v->value, v->right);
    } else {
        if(v->left != nullptr) {
            v = v->left;
        } else if(v->right != nullptr) {
            v = v->right;
        } else {
            v = nullptr;
        }
    }
    return balance(v);
}

Node * kth_max(int k, Node * v) {
    if(size(v->right) == k) return v;
    if(size(v->right) > k) return kth_max(k, v->right);
    return kth_max(k - size(v->right) - 1, v->left);
}


//entry
void sol() {
    int n; cin >> n;
    for(int i = 0; i < n; ++i) {
        string op; cin >> op;
        DBG(op);
        if(op == "+1" || op == "1") {
            int t; cin >> t;
            root = insert(t, root);
        } else if(op == "-1") {
            int t; cin >> t;
            root = remove(t, root);
        } else {
            int t; cin >> t; t--;
            Node * x = kth_max(t, root);
            cout << x->value << endl;
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
    #endif

    sol();

    #ifdef LOCAL
    auto stop = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(stop - start);
    cout << duration.count() << " microseconds" << endl;
    #endif
}
