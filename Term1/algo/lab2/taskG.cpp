#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cmath>

#define int long long

using namespace std;

struct Info {
    int min;
    int max;
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
        inf[bRoot].min = min(inf[bRoot].min,inf[aRoot].min);
        inf[bRoot].max = max(inf[bRoot].max,inf[aRoot].max);
        inf[bRoot].cnt = inf[bRoot].cnt + inf[aRoot].cnt;
        g[aRoot] = bRoot;
    } else {
        inf[aRoot].min = min(inf[bRoot].min,inf[aRoot].min);
        inf[aRoot].max = max(inf[bRoot].max,inf[aRoot].max);
        inf[aRoot].cnt = inf[bRoot].cnt + inf[aRoot].cnt;
        g[bRoot] = aRoot;
    }
}

signed main(){
    int n; cin >> n;
    inf.resize(n + 1);
    g.resize(n + 1);

    for(int i = 0; i <= n; ++i) {
        g[i] = i;
        inf[i].max = i;
        inf[i].min = i;
        inf[i].cnt = 1;
    }

    string op;
    while(cin >> op){
        if(op == "union") {
            int a, b; cin >> a >> b;
            unite(a,b);
        } else {
            int a; cin >> a; a = find(a);
            cout << inf[a].min << " " << inf[a].max << " " << inf[a].cnt << endl;
        }
    }
    return 0;
}
