use warnings;
use strict;

while(<>) {
    s/\([^\)]*\)/\(\)/g;
    print;
}
