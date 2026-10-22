use nqp;
unit module static::Types;

sub same(Mu $a, Mu $b --> Bool) is export {
    so nqp::eqaddr(nqp::decont($a), nqp::decont($b))
}

# Facts describe possible runtime values. Unknown is distinct from nominal Mu/Any.
class Fact is export {
    has Mu $.type = Mu;
    has Int $.definite = -1;
    has Bool $.exact = False;
    has Str $.reason = '';
    has Bool $.bottom = False;
    has Str $.exit-kind = '';
    has Mu $.exception;
    has Bool $.sequence = False;
    has Bool $.finite = False;
    has Int $.cardinality = -1;
    has Bool $.infinite = False;
    has @.items;
    has @.alternatives;
    has Mu $.element;
    has Bool $.has-value = False;
    has Mu $.value;
    has Mu $.key-type = Mu;
    has Bool $.constrained-elements = False;
    # Container identity is attached at argument sites, never inferred from
    # the nominal type of a value (a literal Int is not a writable Scalar).
    has Int $.writable = -1;
    has Str $.identity = '';
    has @.dependencies;
    has @.shape;
    has Mu $.payload;
    has Mu $.callable;
    has Mu $.body;
    has Mu $.owner;
    has %.named;
    has Mu $.lower;
    has Mu $.upper;
    method label() {
        return '<no value>' if $!bottom;
        return "unknown ($!reason)" if $!reason && same($!type, Mu);
        $!type.^name ~ ($!definite == 1 ?? ':D' !! $!definite == 0 ?? ':U' !! '')
    }
    method key() {
        (nqp::objectid($!type), $!definite, +$!exact, $!reason, +$!bottom, $!exit-kind,
         $!exception.defined ?? $!exception.key !! '',
         +$!sequence, +$!finite, $!cardinality, +$!infinite, @!items.map(*.key).join(';'),
         @!alternatives.map(*.key).sort.join('|'),
         $!has-value ?? $!value.raku !! '', nqp::objectid($!key-type), +$!constrained-elements,
         $!writable, $!identity, @!dependencies.sort.join(';'), @!shape.join(','), $!payload.defined ?? $!payload.key !! '', nqp::objectid($!callable), nqp::objectid($!body), nqp::objectid($!owner), %!named.keys.sort.map({ $_ ~ '=' ~ %!named{$_}.key }).join(';'),
         $!lower.defined ?? $!lower.Str !! '', $!upper.defined ?? $!upper.Str !! '').join('/')
    }
}

sub unknown(Str $reason --> Fact) is export { Fact.new(:$reason) }
sub bottom(Str :$exit-kind = '', Fact :$exception = Fact --> Fact) is export {
    Fact.new(:bottom, :$exit-kind, :$exception)
}
sub primitive(Mu $value --> Bool) is export {
    so (Int, Rat, FatRat, Num, Str, Bool).grep({ same($value.WHAT, $_) }).elems
}
sub constant(Mu $value --> Fact) is export {
    return unknown('non-primitive constant') unless primitive($value);
    Fact.new(:type($value.WHAT), :definite(1), :exact, :has-value, :$value)
}
sub known(Mu $type, Int :$definite = -1, Bool :$exact = False --> Fact) is export {
    if $type.HOW.^name.ends-with('DefiniteHOW') {
        return Fact.new(:type($type.^base_type), :definite(+$type.^definite), :$exact);
    }
    my $fact = Fact.new(:$type, :$definite, :$exact);
    # Nil assigned to a scalar means "reset to default" in Raku. Bind the
    # metadata so that the Nil type itself survives in a fact.
    nqp::bindattr(nqp::decont($fact), Fact, '$!type', nqp::decont($type));
    $fact
}
sub merge(*@facts --> Fact) is export {
    my @live = @facts.grep({ $_ ~~ Fact && !.bottom });
    unless @live {
        my @dead = @facts.grep(* ~~ Fact);
        # The initial fixed-point bottom carries no exit information. It must
        # not erase a subsequently established terminating routine summary.
        my @kinds = @dead.map(*.exit-kind).grep(*.chars).unique;
        my @exceptions = @dead.map(*.exception).grep(*.defined);
        return bottom(:exit-kind(@kinds == 1 ?? @kinds[0] !! @kinds ?? 'abrupt' !! ''),
            :exception(@exceptions ?? merge(|@exceptions) !! Fact));
    }
    my @alts = @live.map({ .alternatives ?? .alternatives.List !! ($_,).List }).flat;
    @alts = @alts.unique(:as(*.key));
    return @alts[0] if @alts == 1;
    # Use Raku's own ancestor inference, retaining alternatives for checks.
    my @types = @alts.map(*.type);
    my Mu $type = @types.are;
    my @defs = @alts.map(*.definite).unique;
    Fact.new(:$type, :definite(@defs == 1 ?? @defs[0] !! -1),
        :alternatives(@alts), :reason(@alts.map(*.reason).grep(*.chars).unique.join('; ')))
}

sub nominal(Mu $type --> Mu) is export {
    given $type.HOW.^name {
        when /DefiniteHOW$/ { nominal($type.^base_type) }
        when /SubsetHOW$/ { nominal($type.^refinee) }
        when /CoercionHOW$/ { nominal($type.^target_type) }
        default { $type }
    }
}

# No ACCEPTS/smartmatch on user types: those may execute arbitrary predicates.
sub relation(Fact $actual, Mu $expected --> Str) is export {
    return 'ok' if $actual.bottom;
    if $actual.alternatives {
        my @results = $actual.alternatives.map({ relation($_, $expected) }).unique;
        return @results == 1 ?? @results[0] !! 'unverifiable';
    }
    return 'ok' if same($expected, Mu);
    return 'unverifiable' if $actual.reason;
    return 'ok' if same($actual.type, $expected);
    return 'unverifiable' if $expected.^archetypes.generic || $actual.type.^archetypes.generic;
    my $how = $expected.HOW.^name;
    if $how.ends-with('DefiniteHOW') {
        my $base = relation($actual, $expected.^base_type);
        return $base unless $base eq 'ok';
        return 'unverifiable' if $actual.definite < 0;
        return $actual.definite == +$expected.^definite ?? 'ok' !! 'mismatch';
    }
    if $how.ends-with('SubsetHOW') {
        return 'ok' if same($actual.type, $expected);
        return relation($actual, $expected.^refinee) eq 'mismatch' ?? 'mismatch' !! 'unverifiable';
    }
    if $how.ends-with('CoercionHOW') {
        return 'ok' if relation($actual, $expected.^target_type) eq 'ok';
        return relation($actual, $expected.^constraint_type) eq 'mismatch' ?? 'mismatch' !! 'unverifiable';
    }
    return nqp::istype(Nil, $expected) ?? 'ok' !! 'mismatch' if same($actual.type, Nil);
    my Mu $source = nominal($actual.type);
    # Native storage conversions also impose range/representation constraints.
    if $expected.HOW.^name.ends-with('NativeHOW') {
        my Mu $boxed = $expected.^name.starts-with('int') || $expected.^name.starts-with('uint') ?? Int
            !! $expected.^name.starts-with('num') ?? Num !! $expected.^name.starts-with('str') ?? Str !! Mu;
        my $status = relation($actual, $boxed);
        return $status eq 'ok' && $actual.definite == 1 ?? 'ok'
            !! $status eq 'mismatch' ?? 'mismatch' !! 'unverifiable';
    }
    if $source.HOW.^name.ends-with('NativeHOW') {
        $source = $source.^name.starts-with('int') || $source.^name.starts-with('uint') ?? Int
            !! $source.^name.starts-with('num') ?? Num !! $source.^name.starts-with('str') ?? Str !! Mu;
    }
    return 'ok' if nqp::istype($source, $expected);
    return 'unverifiable' if nqp::istype($expected, $source) && !$actual.exact;
    return 'unverifiable' if !$actual.exact
        && ($source.HOW.^name.contains('Role') || $expected.HOW.^name.contains('Role'));
    'mismatch'
}

class Diagnostic is export {
    has Str $.category is required;
    has Str $.location is required;
    has Str $.context is required;
    has Str $.expected = '';
    has Str $.actual = '';
    has Str $.reason = '';
    has Mu $.origin = Mu;
    method Str() {
        "[static:$!category] $!location: $!context"
        ~ ($!expected ?? "; expected $!expected, got $!actual" !! '')
        ~ ($!reason ?? "; $!reason" !! '')
    }
    method gist() { self.Str }
}
