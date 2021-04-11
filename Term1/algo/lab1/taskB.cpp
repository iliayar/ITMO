#include <iostream>
#include <bits/stdc++.h>

using namespace std;

int a[200000];
int b[101];

int main() {

    for(int i = 0; i < 101; ++i) {
        b[i] = 0;
    }

    int n;
    while(cin >> n) {
        b[n]++;
    }

    n = 0;
    for(int i = 0; i < 101; ++i) {
        while(b[i] > 0) {
            a[n] = i;
            n++;
            b[i]--;
        }
    }

    for(int i = 0; i < n; ++i) {
        cout << a[i] << " ";
    }
    cout << endl;

    return 0;
}
