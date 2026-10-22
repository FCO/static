BEGIN die 'static requires Rakudo 2026.09 or newer'
    if $*RAKU.compiler.version < v2026.09;
use static::Analyzer;
unit module static;

class CheckFailure does X::Comp is export(:types) {
    has @.diagnostics;
    method message() { @!diagnostics.join("\n") }
}

sub check-unit($cu, Bool :$strict, Bool :$fatal, Bool :$external-signatures, Bool :$check-methods, Bool :$check-unreachable --> List) is hidden-from-backtrace {
    die 'static must be called in CHECK with a RakuAST::CompUnit (normally $*CU)'
        unless $cu ~~ RakuAST::CompUnit:D;
    my @diagnostics = static::Analyzer.new(:$external-signatures, :$check-methods, :$check-unreachable).analyze($cu)
        .grep({ $strict || .category eq any(<mismatch unreachable>) });
    if $fatal && @diagnostics {
        # Throwing out of CHECK gets wrapped at the phaser's source location.
        # Register a compiler diagnostic instead, then locate it at the first
        # incompatible expression rather than at the invocation of this pass.
        my $error = CheckFailure.new(:@diagnostics);
        $cu.add-sorry($error);
        with @diagnostics[0].origin -> $origin {
            my $match = $origin.as-match;
            my $position = $origin.^can('locus') ?? $origin.locus !! $origin.from;
            my $excerpt = $origin.source.prepost-of-pos($position);
            $error.SET_FILE_LINE($match.file, $match.line);
            $error.SET_PRE_POST($excerpt[0], $excerpt[1]);
        }
        return @diagnostics.List;
    }
    @diagnostics.map(sub ($diagnostic) is hidden-from-backtrace {
        warn $diagnostic.Str;
    }).sink;
    @diagnostics.List
}

sub warn-on-mismatch($cu = $*CU, Bool :$external-signatures = True, Bool :$check-methods = True, Bool :$check-unreachable = True --> List) is export is hidden-from-backtrace {
    check-unit($cu, :!strict, :!fatal, :$external-signatures, :$check-methods, :$check-unreachable)
}
sub fail-on-mismatch($cu = $*CU, Bool :$external-signatures = True, Bool :$check-methods = True, Bool :$check-unreachable = True --> List) is export is hidden-from-backtrace {
    check-unit($cu, :!strict, :fatal, :$external-signatures, :$check-methods, :$check-unreachable)
}
sub warn-on-unverifiable($cu = $*CU, Bool :$external-signatures = True, Bool :$check-methods = True, Bool :$check-unreachable = True --> List) is export is hidden-from-backtrace {
    check-unit($cu, :strict, :!fatal, :$external-signatures, :$check-methods, :$check-unreachable)
}
sub fail-on-unverifiable($cu = $*CU, Bool :$external-signatures = True, Bool :$check-methods = True, Bool :$check-unreachable = True --> List) is export is hidden-from-backtrace {
    check-unit($cu, :strict, :fatal, :$external-signatures, :$check-methods, :$check-unreachable)
}
