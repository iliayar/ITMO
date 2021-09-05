use warnings;
use strict;

while(<>) {
    print if /\W\((\w+\W*)+\)\W/
}
