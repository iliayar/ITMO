use warnings;
use strict;

local $/;
my $input = <STDIN>;
my @links = ();

while($input =~ /<a.*href\s*=\s*"(([a-zA-Z0-9+.-]+:)?\/\/)?((\w+)(:\w+)?@)?([.a-zA-Z0-9-]+\.[a-zA-Z0-9]+)(:\d+)?[^"]*".*>/g) {
    push @links, $6;
}

my @unique = ();
my %was = ();

foreach my $e (@links) {
    next if $was{ $e }++;
    push @unique, $e;
}

@unique = sort @unique;

print join("\n", @unique), "\n";
