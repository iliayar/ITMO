#include "searcher.h"

#include <fstream>
#include <iostream>
#include <iterator>
#include <sstream>

int
main(int argc, char** argv)
{
    Searcher s;
    for (int i = 1; i < argc; ++i) {
        std::ifstream f(argv[i]);
        s.add_document(argv[i], f);
    }
    std::stringstream ss("a_single_word");
    s.add_document("stringstream", ss);

    // for (int i = 1; i < argc; ++i) {
    //     s.remove_document(argv[i]);
    // }

    std::string line;
    while (std::getline(std::cin, line)) {
        const auto [begin, end] = s.search(line);
        std::ostream_iterator<Searcher::Filename> out(std::cout, ", ");
        std::cout << std::distance(begin, end) << std::endl;
        std::copy(begin, end, out);
        std::cout << std::endl;
    }
}
