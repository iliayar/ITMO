#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cmath>
 
#define int long long
 
using namespace std;
 
struct Info {
    int sum;
    int cnt;
};
 
vector<int> g;
 
vector<Info> inf;
 
int find(int x) {
    while(g[x] != x) {
        x = g[x];
    }
    return x;
}
 
 
void unite(int a, int b) {
    int aRoot = find(a);
    int bRoot = find(b);
 
    if(aRoot == bRoot)
        return;
    if(inf[aRoot].cnt < inf[bRoot].cnt) {
        inf[aRoot].sum -= inf[bRoot].sum;
        inf[bRoot].cnt = inf[bRoot].cnt + inf[aRoot].cnt;
        g[aRoot] = bRoot;
    } else {
        inf[bRoot].sum -= inf[aRoot].sum;
        inf[aRoot].cnt = inf[bRoot].cnt + inf[aRoot].cnt;
        g[bRoot] = aRoot;
    }
}

void add(int x, int s) {
    x = find(x);
    inf[x].sum += s;
}

int get(int x) {
    if(g[x] == x)
        return inf[x].sum;
    return get(g[x]) + inf[x].sum;
}
 
signed main(){
    int n, m; cin >> n >> m;
    inf.resize(n + 1);
    g.resize(n + 1);
 
    for(int i = 0; i <= n; ++i) {
        g[i] = i;
        inf[i].sum = 0;
        inf[i].cnt = 1;
    }
 
    for(int i = 0; i < m; ++i) {
        string op; cin >> op;
        if(op == "join") {
            int a, b; cin >> a >> b;
            unite(a,b);
        } else if(op == "add"){
            int x, v; cin >> x >> v;
            add(x,v);
        } else {
            int x; cin >> x;
            cout << get(x) << endl;
        }
    }
    return 0;
}
