use warnings;
use strict;

while(<>) {
    print if /^(0|(1(01*0)*1))*$/
}
