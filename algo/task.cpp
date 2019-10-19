#include <iostream>
#include <fstream>


using namespace std;

int arr[3000001];

int q_sort(int left, int right, int knumb){
    int  center = arr[(left + right) / 2];
    int i = left;
    int j = right - 1;
    while (i <= j){
        while (arr[i] < center){
            i++;
        }
        while (arr[j] > center){
            j--;
        }
        if (i <= j){
            swap(arr[i], arr[j]);
            i++;
            j--;

        }

    }
    if (i == knumb) return arr[i];
    if (i > knumb){
        return q_sort(left, i, knumb);
    }else{
        return q_sort(i, right, knumb);
    }
}

int main(){
    //ifstream cin("kth.in");
    //ofstream cout("kth.out");
    int a, b, c, n, k;
    cin >> n >> k >> a >> b >> c;
    cin >> arr[0] >> arr[1];
    for (int i = 2; i < n; i++){
        arr[i] = a * arr[i - 2] + b * arr[i - 1] + c;
    }
    
    cout << q_sort(0, n, k - 1) << endl;
    return 0;
}
