#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cmath>

#define int long long

using namespace std;

struct Ball {
    int c;
    int l;
    Ball (int c, int l) {
        this->c = c;
        this->l = l;
    }
    Ball() {
        this->c = -1;
        this->l = 0;
    }
};

Ball b[100001];

int nb = 0;

int res = 0;

Ball c;

void push_b(Ball x) {
    b[nb++] = x;
}

Ball pop_b() {
    return b[--nb];
}

signed main(){
    int x;
    while(cin >> x) {
        if(c.c != x) {
            if(c.l >= 3) {
                res += c.l;
                c = pop_b();
            }
            if(c.c != x) {
                push_b(c);
                c = Ball(x,0);
            }
        }
        c.l++;
    }
    if(c.l >= 3)  {
        res += c.l;
    }
    cout << res << endl;
    return 0;
}
