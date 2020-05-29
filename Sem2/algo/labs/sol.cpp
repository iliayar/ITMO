#include "template.cpp"

int n;
vint2 to;
vint res;
vint w;

void count_w(int u, int from) {
    w[u] = 1;
    for(int v : to[u]) {
        if(v == from || res[v] != -1) continue;
        count_w(v, u);
        w[u] += w[v];
    }
}

int find_centroid(int u, int from, int s) {
    while(true) {
        bool flag = true;
        for(int v : to[u]) {
            if(v == from || res[v] != -1) continue;
            if(w[v] > (s + 1)/2) {
                flag = false;
                from = u;
                u = v;
                break;
            }
        }
        if(flag) break;
    }
    return u;
}

void decompose(int u, int from) {
    count_w(u, from);
    u = find_centroid(u, from, w[u]);
    res[u] = from;
    for(int v : to[u]) {
        if(res[v] != -1) continue;
        decompose(v, u);
    }
}

//entry
void sol() {
    cin >> n; n++;
    res.resize(n, -1);
    w.resize(n);
    to.resize(n, {});
    for(int i = 1; i < n - 1; ++i) {
        int u, v; cin >> u >> v;
        to[u].push_back(v);
        to[v].push_back(u);
    }
    decompose(1, 0);
    for(int i = 1; i < n; ++i) {
        cout << res[i] << " ";
    }
    cout << endl;
}
