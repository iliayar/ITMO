use warnings;
use strict;

while(<>) {
    s/([0-9]+)0/\1/g;
    print;
}
