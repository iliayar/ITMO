#include "template.cpp"

struct E {
    int min = INF;
    int max = -INF;
};

ostream& operator<<(ostream& out, E const& e) {
    cout << "{" << e.min << ", " << e.max << "}";
    return out;
}

E mconcat(E const& lhs, E const& rhs) {
    return E{.min = min(lhs.min, rhs.min), .max = max(lhs.max, rhs.max)};
}

E msingleton(int x) {
    return E{.min = x, .max = x};
}

E mzero() {
    return E{};
}

vector<E> tree;
 
E st_update(int i, int v, int x, int lx, int rx) {
    if(lx > i || rx <= i) {
        return tree[x];
    }
    if(rx - lx == 1) {
        tree[x] = msingleton(v);
        return tree[x];
    }
    int m = (lx + rx)/2;
    tree[x] = mconcat(st_update(i, v, x*2 + 1, lx, m), st_update(i, v, x*2 + 2, m, rx));
    return tree[x];
}
 
E st_get(int l, int r, int x, int lx, int rx) {
    // DBG() << "st_get [" << l << "; " << r << ") " << x << " [" << lx << "; " << rx << ")" << endl;
    if(r <= l) {
        return mzero();
    }
    if(l == lx && r == rx) {
        return tree[x];
    }
    int m = (lx+rx)/2;
    return mconcat(st_get(l,min(m,r),x*2 + 1, lx, m), st_get(max(l,m),r,x*2+2,m,rx));
 
}
 
//entry
void sol() {
    int N = 10;
    tree.resize(N * 4, E{});
    for (int i = 1; i <= N; ++i) {
        int v = ((i * i) % 12345) + ((i * i * i) % 23456);
        st_update(i - 1, v, 0, 0, N);
    }
    // DBG() << tree << endl;
    int k; cin >> k;
    for (int i = 0; i < k; ++i) {
        int x, y; cin >> x >> y;
        if (x > 0) {
            auto e = st_get(x - 1, y, 0, 0, N);
            // DBG() << e.max << " " << e.min << endl;
            cout << e.max - e.min << endl;
        } else {
            x = -x;
            st_update(x - 1, y, 0, 0, N);
        }
    }
}
