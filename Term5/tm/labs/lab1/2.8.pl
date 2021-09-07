use warnings;
use strict;

while(<>) {
    s/\b([1-9][0-9]*)0\b/\1/g;
    print;
}
