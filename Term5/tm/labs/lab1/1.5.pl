use warnings;
use strict;

while(<>) {
    print if /[xyz].{5,17}[xyz]/
}
