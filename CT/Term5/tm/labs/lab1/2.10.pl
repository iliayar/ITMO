use warnings;
use strict;

while(<>) {
    s/(aa|a([^a]|a(?!a))*a){2}(aa|a([^a])*a)/bad/g;
    print;
}
