#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cmath>

#define int long long

using namespace std;

int id[100001];
int b[100001];

int head = 0;
int tail = 0;

void push(int x) {
    id[x] = head;
    b[head++] = x;
}

int pop() {
    return b[tail++];
}

int pop_head() {
    return b[--head];
}

void print_queue() {
    cout << "Queue: ";
    for(int i = tail; i < head; ++i) {
        cout << b[i] << " ";
    }
    cout << endl;
}

signed main(){
    int n; cin >> n;
    for(int i = 0; i < n; ++i) {
        int t; cin >> t;
//    int t;
//    while(cin >> t) {
        if(t == 1) {
             int x; cin >> x;
             push(x);
        } else if(t == 2) {
            pop();
        } else if(t == 3) {
            pop_head();
        } else if(t == 4) {
            int q; cin >> q;
            cout << id[q] - tail << endl;
        } else {
            cout << b[tail] << endl;
        }
//        print_queue();
    }
    
    return 0;
}
