
// Generated at 2020-04-19 21:14:47.202285 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>
#include <map>
#include <ctime>
#include <cstdlib>
#include <queue>


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
    int size;
    int y;
    bool has_zero;
    bool reverse;
    bool loop;
    Node * right;
    Node * left;
    Node * parent;

    Node(int value) :
        value(value), size(1), y(rand()), has_zero(false), reverse(false), loop(false), right(nullptr), left(nullptr), parent(nullptr)
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
            v->left->reverse ^= 1;
        if(v->right != nullptr)
            v->right->reverse ^= 1;

    }
    return v;
}

Node *update(Node *x) {
    if (x == nullptr)
        return x;
    if(x->left != nullptr) x->left->parent = x;
    if(x->right != nullptr) x->right->parent = x;
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
        if(a->right != nullptr) a->right->parent = a;
        return update(a);
    } else {
        b->left = merge(a, b->left);
        if(b->left != nullptr) b->left->parent = b;
        return update(b);
    }
}


pair<Node*, Node*> split(Node * v, int k) {
    if(v == nullptr) return make_pair(nullptr, nullptr);
    v = propagate(v);
    if(size(v->left) >= k) {
        auto p = split(v->left, k);
        v->left = p.second;
        if(p.second != nullptr) p.second->parent = v;
        if(p.first != nullptr) p.first->parent = nullptr;
        return make_pair(p.first, update(v));
    } else {
        auto p = split(v->right, k - size(v->left) - 1);
        v->right = p.first;
        if(p.second != nullptr) p.second->parent = nullptr;
        if(p.first != nullptr) p.first->parent = v;
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

vector<Node*> b;

pair<Node *, int> locate(Node * v) {
    int res = size(v->left);
    while(v->parent != nullptr) {
        if(v->parent->right == v) res += size(v->parent->left) + 1;
        if(v->parent->reverse) res = size(v->parent) - res - 1;
        v = v->parent;
    }
    // if(v->reverse) res = size(v) - res - 1;
    // res += size(v->left);
    return make_pair(v, res);
}

void print(Node * v, int k, ostream & out) {
    if(v == nullptr) return;
    // propagate(v);
    if(k <= 0) return;
    print(v->left, k, out);
    if(size(v->left) < k) out << v->value + 1 << "[" << locate(b[v->value]).second << "] ";
    print(v->right, k - size(v->left) - 1, out);
}

void add_road(int c, int d) {
    DBG("add_road " << c + 1 << " " << d + 1);
    auto pc = locate(b[c]);
    auto pd = locate(b[d]);
    if(pc.first == pd.first) {
        pc.first->loop = true;
        DBG_CODE(print(pc.first, size(pc.first), cout); cout << endl);
        return;
    }
    if(pc.second == 0) swap(pc,pd);
    if(pd.second != 0) swap(pc,pd);
    if(pc.second == 0) {
        pc.first->reverse ^= 1;
    }
    if(pd.second != 0) {
        pd.first->reverse ^= 1;
    }
    pc.first = merge(pc.first, pd.first);
    DBG_CODE(print(pc.first, size(pc.first), cout); cout << endl);
}

void delete_road(int c, int d) {
    auto pc = locate(b[c]);
    auto pd = locate(b[d]);
    DBG("delete_road " << c + 1 << " " << d + 1 << " " << pc.first->loop);
    if(pc.second > pd.second) swap(pc, pd);
    auto p = split(pc.first, pc.second + 1);
    if(pc.first->loop) {
        DBG_CODE(print(p.first, size(p.first), cout); cout << endl);
        DBG_CODE(print(p.second, size(p.second), cout); cout << endl);
        pc.first->loop = false;
        if(pc.second == 0 && pd.second != pc.second + 1)
            pc.first = merge(p.first, p.second);
        else
            pc.first = merge(p.second, p.first);
        DBG_CODE(print(pc.first, size(pc.first), cout); cout << endl);
    } else {
        pc.first = p.first;
        pd.first = p.second;
        DBG_CODE(print(pc.first, size(pc.first), cout); cout << endl);
        DBG_CODE(print(pd.first, size(pd.first), cout); cout << endl);
    }
}

int get_distance(int c, int d) {
    DBG("get_distance " << c + 1<< " " << d + 1);
    auto pc = locate(b[c]);
    auto pd = locate(b[d]);
    if(pc.first != pd.first) return -1;
    if(pc.second > pd.second) swap(pc, pd);
    if(pc.first->loop) {
        return max(min(pd.second - pc.second - 1, size(pc.first) - pd.second + pc.second - 1), static_cast<const long long>(0));
    } else {
        return max(pd.second - pc.second - 1, static_cast<const long long>(0));
    }
}

//entry
void sol() {
    int n, m, q;
    cin >> n >> m >> q;
    b.resize(n);
    for(int i = 0; i < n; ++i) {
        b[i] = new Node(i);
    }
    for (int i = 0; i < m; ++i) {
        int c, d; cin >> c >> d; c--; d--;
        add_road(c, d);
    }
    for(int i = 0; i < q; ++i) {
        string op; cin >> op;
        DBG(op);
        int c, d; cin >> c >> d; c--; d--;
        if(op == "?") {
            cout << get_distance(c, d) << endl;
        } else if(op == "+") {
            add_road(c, d);
        } else {
            delete_road(c, d);
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
