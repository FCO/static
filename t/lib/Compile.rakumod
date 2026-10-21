unit module Compile;
sub compile(Str $source, Str :$mode = 'fail-on-mismatch', Str :$options = '' --> List) is export {
    my $program = "use static; CHECK {$mode}($options);\n" ~ $source;
    my $proc = run $*EXECUTABLE, '-Ilib', '-It/fixtures', '-c', '-e', $program, :out, :err;
    my $out = $proc.out.slurp(:close);
    my $err = $proc.err.slurp(:close);
    ($proc.exitcode, $out ~ $err).List
}
