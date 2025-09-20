use warnings;
use strict;

while(<>) {
    s/([a-zA-Z])(\1)/\1/g;
    print;
}
