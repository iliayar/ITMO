#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cmath>

#define int long long

using namespace std;

vector<int> a;

int m = 0;

void push(int x) {
    a[m++] = x;
}

int pop() {
    return a[--m];
}

int top() {
    return a[m-1];
}

signed main(){
    int n; cin >> n;
    vector<int> b(n);
    a.resize(n);
    for(int i = 0; i < n; ++i) {
        cin >> a[i];
    }
    
    return 0;
}
