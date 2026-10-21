use static;

# Register against the importing unit, without changing its source text.
sub EXPORT($policy = 'fail-on-mismatch', $external = '1', $methods = '1') {
    my $cu = $*CU;
    my %policies =
        'fail-on-mismatch' => &fail-on-mismatch,
        'warn-on-mismatch' => &warn-on-mismatch,
        'fail-on-unverifiable' => &fail-on-unverifiable,
        'warn-on-unverifiable' => &warn-on-unverifiable;
    die "Unknown static policy: $policy" unless %policies{$policy}:exists;
    my &check = %policies{$policy};
    $cu.add-check-code({ check($cu,
        :external-signatures($external eq '1'), :check-methods($methods eq '1')) });
    Map.new
}
