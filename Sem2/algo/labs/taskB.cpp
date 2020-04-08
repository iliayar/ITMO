
// Generated at 2020-04-07 00:32:55.148378 
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
    Node * left;
    Node * right;
    Node * parent;

    Node(int value, Node * parent = nullptr, int h = 1)
        : value(value), h(h), parent(parent), left(nullptr), right(nullptr) {}
};

Node * root = nullptr;

inline int h_get(Node *v) { return v == nullptr ? 0 : v->h; }

inline int h_diff(Node *v) { return h_get(v->right) - h_get(v->left); }

inline void h_upd(Node * v) { v->h = max(h_get(v->left), h_get(v->right)) + 1; }


inline bool is_left(Node * v) {
    return v->parent->left == v;
}
inline bool is_right(Node * v) {
    return v->parent->right == v;
}

Node *l_rotate(Node * a) {
    DBG("l_rotate " << a->value);
    Node * b = a->right;
    if(a->parent != nullptr) {
        if(is_left(a))
            a->parent->left = b;
        else
            a->parent->right = b;
    }
    if(b->left != nullptr)
        b->left->parent = a;
    b->parent = a->parent;
    a->parent = b;
    a->right = b->left;
    b->left = a;
    h_upd(a);
    h_upd(b);
    return b;
}
Node *r_rotate(Node * a) {
    DBG("r_rotate " << a->value);
    Node * b = a->left;
    if(a->parent != nullptr) {
        if(is_left(a))
            a->parent->left = b;
        else
            a->parent->right = b;
    }
    if(b->right != nullptr)
        b->right->parent = a;
    b->parent = a->parent;
    a->parent = b;
    a->left = b->right;
    b->right = a;
    h_upd(a);
    h_upd(b);
    return b;
}


Node * find(int x, Node * v)
{
    if(v == nullptr) return nullptr;
    if(v->value == x) return v;
    if(x < v->value) return find(x, v->left);
    else return find(x, v->right);
}


Node * splay(Node * v) {
    // DBG("splay " << " " << v->value);
    // if(v->parent == nullptr) return v;
    // Node * p = v->parent;
    // if(is_left(v))
    //     v = r_rotate(p);
    // else
    //     v = l_rotate(p);
    // if(p->parent == nullptr) {
    //     if(is_left(v)) {
    //         r_rotate(p);
    //     } else {
    //         l_rotate(p);
    //     }
    // } else {
    //     Node * g = p->parent;
    //     if((is_left(v) && is_left(p))) {
    //         r_rotate(g);
    //         r_rotate(p);
    //     } else if((is_right(v) && is_right(p))) {
    //         l_rotate(g);
    //         l_rotate(p);
    //     } else if((is_left(v) && is_right(p))) {
    //         r_rotate(p);
    //         l_rotate(g);
    //     } else if((is_right(v) && is_left(p))) {
    //         l_rotate(p);
    //         r_rotate(g);
    //     }
    // }
    // return splay(v);
    while(v->parent != nullptr && v->parent->parent != nullptr &&
    v->parent->parent->parent != nullptr) {
        Node * p = v->parent;
        Node * g = p->parent;
        if((is_left(v) && is_left(p))) {
            p = r_rotate(g);
            v = r_rotate(p);
        } else if((is_right(v) && is_right(p))) {
            p = l_rotate(g);
            v = l_rotate(p);
        } else if((is_left(v) && is_right(p))) {
            v = r_rotate(p);
            v = l_rotate(g);
        } else if((is_right(v) && is_left(p))) {
            v = l_rotate(p);
            v = r_rotate(g);
        }
    }
    while(v->parent != nullptr && v->parent->parent != nullptr) {
        if(is_left(v)) {
            v = r_rotate(v->parent);
        } else {
            v = l_rotate(v->parent);
        }
    }
    if(root->left != nullptr && root->left == v) {
        return r_rotate(root);
    } else if(root->right != nullptr) {
        return l_rotate(root);
    }
    return root;
}


void insert(Node * x, Node * v)
{
    if(root == nullptr) {
        root = x;
        return;
    }
    if(x->value == v->value) return;
    if(x->value < v->value) {
        if(v->left == nullptr) {
            v->left = x;
            x->parent = v;
        } else {
            insert(x, v->left);
        }
    } else {
        if(v->right == nullptr) {
            v->right = x;
            x->parent = v;
        } else {
            insert(x, v->right);
        }
    }
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



void remove(int x)
{
    Node *v = find(x, root);
    if (v == nullptr)
        return;
    if (v->left != nullptr && v->right != nullptr) {
        Node *n = next(x, root);
        if(n->parent != nullptr) {
            if (n->parent->left == n)
                n->parent->left = n->right;
            else
                n->parent->right = n->right;
        }
        v->value = n->value;
        if(n->right != nullptr) {
            n->right->parent = n->parent;
        }
        delete n;
    } else if (v->left != nullptr) {
        if(v->parent != nullptr) {
            if (v->parent->left == v) {
                v->parent->left = v->left;
            } else {
                v->parent->right = v->left;
            }
            v->left->parent = v->parent;
        } else {
            root = v->left;
            v->left->parent = nullptr;
        }
        delete v;
    } else if (v->right != nullptr) {
        if(v->parent != nullptr) {
            if (v->parent->left == v) {
                v->parent->left = v->right;
            } else {
                v->parent->right = v->right;
            }
            v->right->parent = v->parent;
        } else {
            root = v->right;
            v->right->parent = nullptr;
        }
        delete v;
    } else {
        if(v->parent != nullptr) {
            if (v->parent->left == v) {
                v->parent->left = nullptr;
            } else {
                v->parent->right = nullptr;
            }
        } else {
            root = nullptr;
        }
        delete v;
    }
}

//entry
void sol() {
    string op;
    while(cin >> op) {
        int t; cin >> t;
        DBG(op);
        if(op == "insert") {
            Node * x = new Node(t);
            insert(x, root);
            root = splay(x);
            DBG("root " << root->value << " " << root->parent);
        } else if(op == "delete") {
            remove(t);
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
                cout << r->value << endl;
        } else if(op == "prev") {
            Node * r = prev(t, root);
            if(r == nullptr)
                cout << "none" << endl;
            else
                cout << r->value << endl;
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
