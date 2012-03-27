#!/usr/bin/perl

# (C) 2008 James C. Deikun <james@place.org>
#
# This file is released under the canonical MIT X11 license.

#
# patmv - rename or move files according to a regexp pattern
#
# Usage: patmv [-g] [-v] <file>* <pattern>:<replacement>
#
# <pattern> is a perl-style regexp, and <replacement> behaves like the
# right-hand side of a perl s/// construct.  If there are ':' characters
# in <pattern> they can be escaped with backslashes.  (Watch out for the
# shell eating the backslashes, though!)
#
# In each of the <file>s where the <pattern> matches the path as given on
# the command line, the file will be mv'd to the path obtained by replacing
# <pattern> with <replacement>.  If the option -g was given, ALL occurrences
# of <pattern> will be replaced.
#
# The option -v, if given, will be passed on to mv.  mv is always called with
# the option -i.
#
# If the option -n is given, no changes will be made, but patmv will print
# the commands it would have run on standard output.
#
# EXAMPLES:
#
#   patmv fooly cooly foo:bar
#
#     Does 'mv -i fooly barly'
#
#   patmv *~ '~$:.bak'
#
#     Changes final '~' to a '.bak' extension.
#
#   patmv * '^(?=.*-(\d\d\d\d)-(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec))-:reports/$1/$2/'
#
#     Sorts out reports by year and month.  (Directories must already exist.)
#
#   patmv -g -- * '(^-|[^-\w.]):%${\(sprintf "%02x", ord($1))}'
#
#     URL-encodes inconvenient filenames.
#

use strict;
use warnings qw<all>;
use Getopt::Std;

our $opt_g;
our $opt_n;
our $opt_v;

sub split_esc ($;$$) {
  my($pattern, $data, $n) = @_;
  $n = 0 unless defined $n;

  my @raw_parts = split(/(\\*$pattern)/, $data, -1);
  my @matches;

  my @parts;
  my $glue = 0;
  my $m = 0;
  for my $i (0..@raw_parts-1) {
    if (@matches = $raw_parts[$i] =~ /\A((?:\\\\)*\\$pattern)\z/) {
      $parts[-1] .= $matches[0];
      $i += @matches;
      $glue = 1;
    } elsif (@matches = $raw_parts[$i] =~ /\A((?:\\\\)*)($pattern)\z/) {
      $parts[-1] .= $matches[0];
      if ($m >= $n and $n > 0) {
        $parts[-1] .= $matches[1];
        $i += @matches - 1;
        next;
      }
      push @parts, $raw_parts[$i+1..$i+@matches-2] if @matches > 2;
      $i += @matches - 1;
      $glue = 0;
    } elsif ($glue or $m >= $n and $n > 0) {
      $parts[-1] .= $raw_parts[$i];
    } else {
      push @parts, $raw_parts[$i];
      $m++;
    }
  }
  if ($n == 0) {
    pop @parts while $parts[-1] eq '';
  }
  return @parts;
}

getopts("gnv");

if (!@ARGV) {
  die "Usage: $0 <files> <pattern>:<replacement>";
}

my($pattern, $repl) = split_esc qr/:/, pop(@ARGV), 2;

die "no replacement given" unless defined $repl;

my $mv = `which mv`;
chomp $mv;
$pattern = qr/$pattern/;

die "couldn't find mv" unless length($mv);

my @mv = ($mv, "-i");
push @mv, "-v" if $opt_v;
push @mv, "--";

for (@ARGV) {
  my $from = $_;
  if ($opt_g) {
    next unless s/$pattern/"qq(".$repl.")"/eeg;
  } else {
    next unless s/$pattern/"qq(".$repl.")"/ee;
  }
  if ($opt_n) {
    # piping this output to /bin/sh is not recommended, but i'm sure someone
    #   will want to try it ...
    print join(" ", @mv, map { "\Q$_\E" } $from, $_), "\n";
    next;
  }
  system @mv, $from, $_;
}
