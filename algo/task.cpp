#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <cmath>

#define int long long

using namespace std;

struct Gnome {
    int id;
    Gnome* next;
    Gnome* prev;
    Gnome() {
        this->id = -1;
        this->prev = NULL;
        this->next = NULL;
    }
    Gnome(int id, Gnome *next, Gnome *prev) {
        this->id = id;
        this->next = next;
        this->prev = prev;
    }
};

int m = 0;

Gnome *mid;
Gnome *head = new Gnome();
Gnome *tail = new Gnome();

void push_normal(int x) {
    Gnome* a = new Gnome(x,tail->next,tail);
    tail->next->prev = a;
    tail->next = a;
    if(m == 0) {
        mid = a;
    } else if(m%2 == 0) {
        mid = mid->prev;
    }
    m++;
}

void push_CHAD(int x) {
    Gnome* a = new Gnome(x, mid, mid->prev);
    mid->prev->next = a;
    mid->prev = a;
    if(m%2 == 1) {
        mid = a;
    }
    m++;
}

int pop() {
    Gnome *res = head->prev;
    res->prev->next = head;
    head->prev = res->prev;
    if(m%2 == 1) {
        mid = mid->next;
    }
    m--;
    return res->id;
}

void print_stack() {
    Gnome *i = head->prev;
    //while(i->id != -1) {
    //    cout << i->id << " ";
    //    i = i->prev;
    //}
    cout << i->id;
    cout << endl;
}

signed main(){
    head->prev = tail;
    tail->next = head;
//    int n; cin >> n;
//    for(int i = 0; i < n; ++i) {
//        char t; cin >> t;
    char t;
    while(cin >> t) {
        if(t == '+') {
            int x; cin >> x;
            push_normal(x);
        } else if(t == '*') {
            int x; cin >> x;
            push_CHAD(x);
        } else {
            cout << pop() << endl;
        }
    }

    return 0;
}
