use warnings;
use strict;

while(<>) {
    print if /\([^()]*\b\w+\b[^()]*\)/
}
