use warnings;
use strict;

while(<>) {
    s/\ba+\b/argh/gi;
    print;
}
