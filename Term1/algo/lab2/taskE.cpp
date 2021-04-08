#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cmath>

#define int long long

using namespace std;

int a[501];
int n = 0;

void push(int x){
    a[n++] = x;
}

int pop() {
    return a[--n];
}

int calc(char op, int a, int b) {
    switch(op) {
        case '+':
            return a + b;
        case '-':
            return a - b;
        case '*':
            return a*b;
    }
    return 0;
}


signed main(){
    char t;
    while(cin >> t) {
        if(!isdigit(t)) {
            int b = pop();
            int a = pop();
            int c = calc((char)t,a,b);
            push(c);
        } else {
            push(t-'0');
        }
    }
    cout << pop() << endl;
    return 0;
}
