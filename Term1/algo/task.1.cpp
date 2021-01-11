#include <iostream>
#include <fstream>
#include <string>
using namespace std;
struct Elem{
    int data;
    int line;
};
int N = 0;
Elem heap[1000001];
int line_pos[1000001];
void push(Elem* x, int n){
    heap[n] = *x;
    line_pos[heap[n].line] = n;
    if (n != 0) {
        while (heap[n].data < heap[(n-1)/2].data) {
            swap(heap[n], heap[(n-1)/2]);
            swap(line_pos[heap[n].line], line_pos[heap[(n-1)/2].line]);
            n = (n-1)/2;
        }
    }
    N++;
}
void extract_min(int n){
    int numb_out = heap[0].data;
    if (n == 0){
        cout << '*' << endl;
        return;
    }
    swap(heap[0], heap[n-1]);
    swap(line_pos[heap[0].line], line_pos[heap[n/2].line]);
    N--;
    int i = 0;
    while(2*i + 1 <= N - 1){
        if(2*i + 2 <= N - 1){
            if(heap[i].data > min(heap[2*i + 1].data, heap[2*i + 2].data)){
                if (heap[2*i + 1].data < heap[2*i + 2].data){
                    swap(heap[2*i + 1], heap[i]);
                    swap(line_pos[heap[2*i + 1].line], line_pos[heap[i].line]);
                    i = 2*i + 1;
                }else {
                    swap(heap[2 * i + 2], heap[i]);
                    swap(line_pos[heap[2 * i + 2].line], line_pos[heap[i].line]);
                    i = 2 * i + 2;
                }
            }else{
                break;
            }
        }else{
            if(heap[i].data > heap[2*i + 1].data){
                swap(heap[i], heap[2*i + 1]);
                swap(line_pos[heap[i].line], line_pos[heap[2*i + 1].line]);
                i = 2*i + 1;
            }else{
                break;
            }
        }
    }
    cout << numb_out << endl;
    return ;
}
void decrease_key(int x, int y){  // строка, на какое значение уменьшать, индекс с которым мы работаем.
    heap[line_pos[x]].data = y;
    int index = line_pos[x];
    if (index != 0) {
        while (heap[index].data < heap[index / 2].data) {
            swap(heap[index], heap[index / 2]);
            swap(line_pos[heap[index].line], line_pos[heap[index / 2].line]);
            index /= 2;
        }
    }
}
int main(){
    //ifstream cin("priorityqueue.in");z
    //ofstream cout("priorityqueue.out");
    int line_in = 0;
    string command;
    while(cin >> command){
        if (command == "push"){
            Elem x;
            cin >> x.data;
            x.line = line_in++;
            push(&x, N);
        }
        if (command == "extract-min"){
            extract_min(N);
            line_in++;
        }
 
        if (command == "decrease-key"){
            int x, y;
            cin >> x;
            cin >> y;
            decrease_key(x - 1, y);
            line_in++;
        }
    }
    return 0;
}