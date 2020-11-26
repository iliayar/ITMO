#include "hash_set.h"

#include <iostream>

int main()
{
    HashSet<int> set;
    while (std::cin) {
        int x;
        std::cin >> x;
        if (set.contains(x)) {
            std::cout << "*\n";
        }
        else {
            std::cout << "-\n";
        }
        set.insert(x);
    }
}
