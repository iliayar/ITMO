use warnings;
use strict;

while(<>) {
    s/\b(\w)(\w)(\w*)\b/\2\1\3/g;
    print;
}
