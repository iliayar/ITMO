
// Generated at 2020-04-05 16:35:36.124280 
// By iliayar
#include <iostream>
#include <vector>
#include <chrono>
#include <algorithm>
#include <cstdio>
#include <map>


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
    Node * left;
    Node * right;
    Node * parent;

    Node(int value, Node * parent) :
        value(value), parent(parent), right(nullptr), left(nullptr)
    {}
    Node(int value) :
        value(value), parent(nullptr), right(nullptr), left(nullptr)
    {}

};


Node * root = nullptr;

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
    return v;
}

// void insert(int x, Node * v)
// {
//     if(root == nullptr) {
//         root = new Node(x, nullptr);
//         return;
//     }
//     if(x == v->value) return;
//     if(x < v->value) {
//         if(v->left == nullptr) {
//             v->left = new Node(x, v);
//         } else {
//             insert(x, v->left);
//         }
//     } else {
//         if(v->right == nullptr) {
//             v->right = new Node(x, v);
//         } else {
//             insert(x, v->right);
//         }
//     }
// }


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

// void remove(int x)
// {
//     Node *v = find(x, root);
//     if (v == nullptr)
//         return;
//     if (v->left != nullptr && v->right != nullptr) {
//         Node *n = next(x, root);
//         if(n->parent != nullptr) {
//             if (n->parent->left == n)
//                 n->parent->left = n->right;
//             else
//                 n->parent->right = n->right;
//         }
//         v->value = n->value;
//         if(n->right != nullptr) {
//             n->right->parent = n->parent;
//         }
//         delete n;
//     } else if (v->left != nullptr) {
//         if(v->parent != nullptr) {
//             if (v->parent->left == v) {
//                 v->parent->left = v->left;
//             } else {
//                 v->parent->right = v->left;
//             }
//             v->left->parent = v->parent;
//         } else {
//             root = v->left;
//             v->left->parent = nullptr;
//         }
//         delete v;
//     } else if (v->right != nullptr) {
//         if(v->parent != nullptr) {
//             if (v->parent->left == v) {
//                 v->parent->left = v->right;
//             } else {
//                 v->parent->right = v->right;
//             }
//             v->right->parent = v->parent;
//         } else {
//             root = v->right;
//             v->right->parent = nullptr;
//         }
//         delete v;
//     } else {
//         if(v->parent != nullptr) {
//             if (v->parent->left == v) {
//                 v->parent->left = nullptr;
//             } else {
//                 v->parent->right = nullptr;
//             }
//         } else {
//             root = nullptr;
//         }
//         delete v;
//     }
// }

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
    return v;
}

//entry
void sol() {
    string op;
    while(cin >> op) {
        int t; cin >> t;
        if(op == "insert") {
            root = insert(t, root);
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
