use warnings;
use strict;

local $/;
$_ = <STDIN>;
s/<[^>]*>//g;

s/ *([\n^]) */\n/g; # Trailing/Leeding spaces
s/^\n*//g; # Leeding empty lines
s/\n*$//g; # Trailing empty lines
s/\n{2,}/\n\n/g; # multiple consequnt empty lines
print;
