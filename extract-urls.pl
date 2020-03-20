#!/usr/bin/env perl

use feature qw<say unicode_strings>;
use strict;
use Encode qw<decode from_to FB_CROAK>;
use Getopt::Std;
use JSON qw<to_json>;

our $opt_j;
our $linestart = 0;

getopts("j");

binmode(STDOUT, ':utf8');

while (<>) {
  my $linelen = length $_;
  my $codec = 'r';
  eval { $_ = decode 'UTF-8', $_, FB_CROAK; $codec='u'; };
  eval { $_ = decode 'ISO-8859-1', $_, FB_CROAK; $codec='i'; } if $@;

  while (/((?:https?|ftp):\/\/(?:[,.!?]*(?:[^\s\[\]()<>{},.?!\x{a0}]+|\([^\s()*]*?\)|\[[^\s\[\]]*?\]|<[^\s<>]*?>|\{[^\s{}]*?\}))*)/g) {
    if ($opt_j) {
      say to_json(+{ u => $1, c => $codec, l => $., f => $ARGV, s => $linestart, b => $-[0], e => $+[0]});
    } else {
      say $1;
    }
  }
  $linestart += $linelen;
} continue {
  if (eof) {
    close ARGV;
    $linestart = 0;
  }
}
