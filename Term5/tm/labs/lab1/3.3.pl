use warnings;
use strict;

local $/;
my $input = <STDIN>;
my @links = ();

while($input =~ /<a\s*href="([a-zA-Z0-9]+:\/\/)?([.a-zA-Z0-9]*)((:\d+)*)?[^"]*"\s*>/g) {
    push @links, $2;
}

my @unique = ();
my %was = ();

foreach my $e (@links) {
    next if $was{ $e }++;
    push @unique, $e;
}

@unique = sort @unique;

print join("\n", @unique), "\n";
