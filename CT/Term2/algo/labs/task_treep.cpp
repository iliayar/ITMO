
// Generated at 2020-04-05 20:04:57.785283 
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

//##################CODE BEGIN##############include <cstdlib>
#include <utility>


struct Node {
    int x;
    int y;
    Node * right;
    Node * left;
    Node * parent;

    Node(int x, int y, Node * parent = nullptr) :
        x(x), y(y), parent(parent), left(nullptr), right(nullptr)
    {}
};


int y_max = 1000000000;


Node * root = nullptr;

Node * find(int x, Node * v)
{
    if(v == nullptr) return nullptr;
    if(v->x == x) return v;
    if(x < v->x) return find(x, v->left);
    else return find(x, v->right);
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
    if(v->x > x) return next(x, v->left, v);
    else return next(x, v->right, min);
}

Node * prev(int x, Node * v, Node * max = nullptr)
{
    if(v == nullptr) return max;
    if(v->x < x) return prev(x, v->right, v);
    else return prev(x, v->left, max);
}

Node * merge(Node * a, Node * b)
{
    if(a == nullptr) return b;
    if(b == nullptr) return a;
    if(a->y > b->y)  {
        a->right = merge(a->right, b);
        return a;
    } else {
        b->left = merge(a, b->left);
        return b;
    }
}

pair<Node*,Node*> split(int x, Node * a)
{
    if(a == nullptr) return make_pair(nullptr, nullptr);
    if(a->x < x) {
        auto p = split(x, a->right);
        a->right = p.first;
        return make_pair(a, p.second);
    } else {
        auto p = split(x, a->left);
        a->left = p.second;
        return make_pair(p.first, a);
    }
}

Node * insert(Node * x, Node * a) {
    if(a == nullptr) return x;
    if(a->x == x->x) return a;
    if(x->y > a->y) {
        auto p = split(x->x, a);
        x->left = p.first;
        x->right = p.second;
        return x;
    } else {
        if(x->x < a->x) {
            a->left = insert(x, a->left);
        } else {
            a->right = insert(x, a->right);
        }
        return a;
    }
}

Node * remove(int x, Node * a) {
    if(a == nullptr) return a;
    if(x == a->x) {
        return merge(a->left, a->right);
    }
    if(x < a->x) {
        a->left = remove(x, a->left);
    } else {
        a->right = remove(x, a->right);
    }
    return a;
}

//entry
void sol() {
    srand(time(nullptr));
    string op;
    while(cin >> op) {
        int t; cin >> t;
        if(op == "insert") {
            root = insert(new Node(t, t), root);
        } else if(op == "delete") {
            root = remove(t, root);
        } else if(op == "exists") {
            if(find(t, root) != nullptr)
                cout << "true" << endl;
            else
                cout << "false" << endl;
        } else if(op == "next") {
            Node * r = next(t, root);
            if(r == nullptr)
                cout << "none" << endl;
            else
                cout << r->x << endl;
        } else if(op == "prev") {
            Node * r = prev(t, root);
            if(r == nullptr)
                cout << "none" << endl;
            else
                cout << r->x << endl;
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
