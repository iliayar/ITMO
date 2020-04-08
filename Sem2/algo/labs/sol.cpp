#include "template.cpp"

struct Node {
    int value;
    int h;
    int sum;
    Node * left;
    Node * right;

    Node(int value, int h = 1)
        : value(value), h(h), sum(value), left(nullptr), right(nullptr) {}
};

Node * root = nullptr;

int h_get(Node *v) { return v == nullptr ? 0 : v->h; }

int h_diff(Node *v) { return h_get(v->right) - h_get(v->left); }

void h_upd(Node * v) { v->h = max(h_get(v->left), h_get(v->right)) + 1; }

void sum_upd(Node * v) {
    v->sum = (v->left == nullptr ? 0 : v->left->sum) +
        (v->right == nullptr ? 0 : v->right->sum) + v->value;
    // DBG("sum_upd " << v->value << " " << v->sum);
}

Node *l_rotate(Node *a) {
  Node *b = a->right;
  a->right = b->left;
  b->left = a;
  h_upd(a);
  h_upd(b);
  sum_upd(a);
  sum_upd(b);
  return b;
}
Node *r_rotate(Node *a) {
  Node *b = a->left;
  a->left = b->right;
  b->right = a;
  h_upd(a);
  h_upd(b);
  sum_upd(a);
  sum_upd(b);
  return b;
}

Node * balance(Node * v) {
    if(v == nullptr) return v;
    h_upd(v);
    sum_upd(v);
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

int sum(int l, int r, int lx, int rx, Node * v) {
    if(v == nullptr) return 0;
    if(r < l) return 0;
    if(l <= lx && rx <= r) return v->sum;
    return sum(l, min(r, v->value), lx, v->value, v->left) +
        sum(max(l, v->value), r, v->value, rx, v->right) +
        ((l <= v->value && v->value <= r) ? v->value : 0);
}

const int MOD = 1000000000;

//entry
void sol() {
    int n; cin >> n;
    int a = 0;
    int lx = MOD + 1, rx = -1;
    for(int i = 0; i < n; ++i) {
        string op; cin >> op;
        if(op == "+") {
            int t; cin >> t;
            root = insert((t + a) % MOD, root);
            lx = min(lx, (t + a) % MOD);
            rx = max(rx, (t + a) % MOD);
            a = 0;
        } else {
            int l, r; cin >> l >> r;
            a = sum(l, r, lx, rx, root);
            cout << a << endl;
        }
        DBG(root->sum);
    }
}
