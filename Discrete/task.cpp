#include <iostream>
//#include <bits/stdc++.h>
#include <vector>
#include <climits>
#define int long long
#ifndef LOCAL
#define filename "huffman"
#else
#define filename "test"
#endif

#define INF LLONG_MAX

using namespace std;

struct Node {
    int parent;
    int n;
    int left;
    int right;
};

unsigned int res = 0;
vector<Node> g;

void cnt(int i, int h) {
    if(g[i].left == -1 || g[i].right == -1) {
        res += h*g[i].n;
//        cout <<  "Leaf: " << h << " " << i + 1 << " " << g[i].n << endl;
        return;
    }
//    cout << h << " " << i + 1 << " " << g[i].n << endl;
    cnt(g[i].left,h + 1);
    cnt(g[i].right,h + 1);
}

signed main() {
    freopen(filename".in", "r", stdin);
    freopen(filename".out", "w", stdout);
    int n; cin >> n;
    g.resize(2*n);
    for(int i = 0; i < n; ++i) {
        int t; cin >> t;
        g[i].n = t;
    }
    for(int i = 0; i < 2*n; ++i) {
        g[i].parent = -1;
        g[i].left = -1;
        g[i].right = -1;
        if(i >= n) {
            g[i].n = INF;
        }
    }
    for(int i = n; i < 2*n; ++i) {
        int imin1, imin2;
        int min = INF;
        for(int j = 0; j < 2*n; ++j) {
            if(g[j].parent != -1) continue;
            if(min > g[j].n) {
                min = g[j].n;
                imin1 = j;
            }
        }
        min = INF;
        for(int j = 0; j < 2*n; ++j) {
            if(j == imin1 || g[j].parent != -1) continue;
            if(min > g[j].n) {
                min = g[j].n;
                imin2 = j;
            }
        }
        g[i].left = imin1;
        g[i].right = imin2;
        g[i].n = g[imin1].n + g[imin2].n;
        g[imin1].parent = i;
        g[imin2].parent = i;
    }
    cnt(2*n - 2, 0);
    cout << res << endl;
    fclose(stdout);
    fclose(stdin);
    return 0;
}
