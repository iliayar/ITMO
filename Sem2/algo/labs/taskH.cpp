
// Generated at 2020-04-10 23:29:02.624562 
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

//##################CODE BEGIN##############include <algorithm>

struct Node {
    int value;
    int size;
    int y;
    bool has_zero;
    bool reverse;
    Node * right;
    Node * left;

    Node(int value) :
        value(value), size(1), y(rand()), has_zero(false), reverse(false), right(nullptr), left(nullptr)
    {}
};


int y_max = 1000000000;


Node * root = nullptr;

int size(Node *x) { return x == nullptr ? 0 : x->size; }

Node * propagate(Node * v)
{
    if(v != nullptr && v->reverse) {
        v->reverse = false;
        swap(v->left, v->right);
        if(v->left != nullptr)
            v->left->reverse = !v->left->reverse;
        if(v->right != nullptr)
            v->right->reverse = !v->right->reverse;

    }
    return v;
}

Node *update(Node *x) {
    if (x == nullptr)
        return x;
    x->size = size(x->left) + size(x->right) + 1;
    x->has_zero = (x->value == 0 || (x->left != nullptr && x->left->has_zero) ||
                   (x->right != nullptr && x->right->has_zero));
    return x;
}

Node * merge(Node * a, Node * b) {
    if(a == nullptr) return b;
    if(b == nullptr) return a;
    a = propagate(a);
    b = propagate(b);
    if (a->y > b->y) {
        a->right = merge(a->right, b);
        return update(a);
    } else {
        b->left = merge(a, b->left);
        return update(b);
    }
}


pair<Node*, Node*> split(Node * v, int k) {
    if(v == nullptr) return make_pair(nullptr, nullptr);
    v = propagate(v);
    if(size(v->left) >= k) {
        auto p = split(v->left, k);
        v->left = p.second;
        return make_pair(p.first, update(v));
    } else {
        auto p = split(v->right, k - size(v->left) - 1);
        v->right = p.first;
        return make_pair(update(v), p.second);
    }
}

Node *get(int k, Node *v) {
    if(v == nullptr) return v;
    if (size(v->left) == k)
        return v;
    if (size(v->left) > k) {
        return get(k, v->left);
    } else {
        return get(k - size(v->left) - 1, v->right);
    }
}

Node * insert(Node * x, Node * v, int k) {
    auto p = split(v, k);
    return merge(merge(p.first, x), p.second);
}

int next(Node * v, int k) {
    if(v == nullptr) return -1;
    if(size(v) < k) return -1;
    int t = -1;
    if(v->left != nullptr && v->left->has_zero) t = next(v->left, k);
    if(t != -1) return t;
    if(size(v->left) >= k && v->value == 0) return size(v->left);
    if(v->right != nullptr && v->right->has_zero) t = next(v->right, k - size(v->left) - 1);
    if(t != -1) return t + size(v->left) + 1;
    return -1;
}

void print(Node * v, int k, ostream & out) {
    if(v == nullptr) return;
    propagate(v);
    if(k <= 0) return;
    print(v->left, k, out);
    if(size(v->left) < k) out << v->value << " ";
    print(v->right, k - size(v->left) - 1, out);
}

Node * remove_min(Node * v) {
    if(v->left == nullptr) return v->right;
    v->left = remove_min(v->left);
    return update(v);
}

Node * remove(Node * v, int k) {
    auto p = split(v, k);
    if(p.second == nullptr) return p.first;
    return merge(p.first, remove_min(p.second));
}

Node * move_to_front(Node * v, int l, int r)
{
    auto p1 = split(v, r);
    auto p2 = split(p1.first, l);
    return merge(p2.second, merge(p2.first, p1.second));
}

Node * reverse(Node * v, int l, int r)
{
    auto p1 = split(v, r);
    auto p2 = split(p1.first, l);
    if(p2.second != nullptr)
        p2.second->reverse = !p2.second->reverse;
    return merge(p2.first, merge(p2.second, p1.second));
}

//entry
void sol() {
    int n, m; cin >> n >> m;
    for(int i = 0; i < n; ++i)
        root = insert(new Node(i + 1), root, size(root));
    for(int i = 0; i < m; ++i) {
        int l, r; cin >> l >> r;
        root = reverse(root, l-1, r);
    }
    print(root, size(root), cout);
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
