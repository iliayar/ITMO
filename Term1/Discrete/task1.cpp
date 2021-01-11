#include <iostream>
#include <algorithm>
#include <cmath>
#include <vector>
#include <string>

using namespace std;

vector<unsigned int> b;
vector<bool> was;
vector<unsigned int> c;

int getBit(int n, int k) {
    unsigned int mask = 1 << k;
    return mask & n;
}

void printBits(int n, int k) {
    for(int i = k-1; i >= 0; --i) {
        cout << (1 & n>>i);
    }
}

int foo(int n) {
    if(was[n])
        return c[n];
    c[n] = b[n];
    for(int i = 0; i < n; ++i) {
        if((i & n) == i) {
            c[n] ^= foo(i);
        }
    }
    was[n] = true;
    return c[n];

}

signed main() {
    int n; cin >> n;

    b.resize(pow(2,n));
    c.resize(pow(2,n));
    was.resize(pow(2,n),false);

    for(int i = 0; i < b.size(); ++i) {
        for(int j = n - 1; j >= 0; --j) {
            char t; cin >> t;
        }
        cin >> b[i];
    }

    c[0] = b[0];
    foo(pow(2,n)-1);
    for(int i = 0; i < b.size(); ++i) {
        printBits(i,n);
        cout << " " << c[i] << endl;
    }

    return 0;
}
