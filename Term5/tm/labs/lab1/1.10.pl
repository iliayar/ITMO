use warnings;
use strict;

while(<>) {
    print if /\b(\w+)\g1\b/
}
