use nqp;
use static::Types;
unit module static::Predicates;

# An interpreter for a deliberately bounded, pure subset of expressions.
# It never invokes a routine/regex/coercion from the inspected program.
sub core-operator($op --> Bool) is export {
    so $op ~~ RakuAST::Lookup && $op.is-resolved
        && $op.resolution ~~ RakuAST::Declaration::External::Setting
}

# Smartmatch against a nominal type is only a type test when ACCEPTS is a
# known CORE implementation. Inspect metadata; never call that method.
sub nominal-matcher(Mu $type --> Bool) is export {
    return False if $type.HOW.^name.contains('Subset') || $type.^archetypes.generic
        || !$type.HOW.^can('find_method');
    my $method = $type.HOW.find_method($type, 'ACCEPTS');
    so (Mu, Any, Cool, Numeric, Real, Int, Rat, FatRat, Num, Str, Bool)
        .grep({ same($method, $_.HOW.find_method($_, 'ACCEPTS')) }).elems
}

# Bounds are inclusive and restricted to primitive integer arithmetic.
sub interval-operation(Str $op, @args --> Fact) {
    return unknown('no integer interval rule') unless @args == 2
        && @args.grep({ !same(.type, Int) || .reason }).elems == 0;
    my @lo = @args.map({ .has-value ?? .value !! .lower });
    my @hi = @args.map({ .has-value ?? .value !! .upper });
    return unknown('interval budget exceeded') if (|@lo, |@hi).grep({ .defined && .base(2).chars > 4096 });
    if $op eq any('<', '<=', '>', '>=', '==', '!=') {
        my $yes = False;
        my $no = False;
        given $op {
            when '<' { $yes = @hi[0].defined && @lo[1].defined && @hi[0] < @lo[1]; $no = @lo[0].defined && @hi[1].defined && @lo[0] >= @hi[1] }
            when '<=' { $yes = @hi[0].defined && @lo[1].defined && @hi[0] <= @lo[1]; $no = @lo[0].defined && @hi[1].defined && @lo[0] > @hi[1] }
            when '>' { $yes = @lo[0].defined && @hi[1].defined && @lo[0] > @hi[1]; $no = @hi[0].defined && @lo[1].defined && @hi[0] <= @lo[1] }
            when '>=' { $yes = @lo[0].defined && @hi[1].defined && @lo[0] >= @hi[1]; $no = @hi[0].defined && @lo[1].defined && @hi[0] < @lo[1] }
            when '==' | '!=' {
                $no = @hi[0].defined && @lo[1].defined && @hi[0] < @lo[1]
                    || @hi[1].defined && @lo[0].defined && @hi[1] < @lo[0];
                $yes = @lo[0].defined && @hi[0].defined && @lo[1].defined && @hi[1].defined
                    && @lo[0] == @hi[0] == @lo[1] == @hi[1];
                ($yes, $no) = ($no, $yes) if $op eq '!=';
            }
        }
        return constant(True) if $yes;
        return constant(False) if $no;
    }
    if $op eq '*' {
        for 0,1 -> $i {
            next unless @args[$i].has-value;
            my $k = @args[$i].value;
            my $other = 1-$i;
            return constant(0) if $k == 0;
            my $lo = $k >= 0 ?? @lo[$other] !! @hi[$other];
            my $hi = $k >= 0 ?? @hi[$other] !! @lo[$other];
            return Fact.new(:type(Int), :definite(1),
                :lower($lo.defined ?? $lo*$k !! Mu), :upper($hi.defined ?? $hi*$k !! Mu));
        }
    }
    if $op eq any('+', '-') {
        my $lower = $op eq '+'
            ?? (@lo[0].defined && @lo[1].defined ?? @lo[0]+@lo[1] !! Mu)
            !! (@lo[0].defined && @hi[1].defined ?? @lo[0]-@hi[1] !! Mu);
        my $upper = $op eq '+'
            ?? (@hi[0].defined && @hi[1].defined ?? @hi[0]+@hi[1] !! Mu)
            !! (@hi[0].defined && @lo[1].defined ?? @hi[0]-@lo[1] !! Mu);
        return Fact.new(:type(Int), :definite(1), :$lower, :$upper) if $lower.defined || $upper.defined;
    }
    unknown('integer interval is inconclusive')
}

sub primitive-method(Str $name, Fact $receiver, @args --> Fact) is export {
    return unknown('dynamic method operands') if @args.grep({!.has-value || !primitive(.value)});
    return unknown('method constant budget exceeded') if @args.grep({same(.type, Str) && .value.chars > 4096});
    if $receiver.has-value && same($receiver.type, Str) && $receiver.value.chars <= 4096 {
        my $s = $receiver.value;
        if !@args {
            return constant($s.chars) if $name eq 'chars';
            return constant(1) if $name eq 'elems';
            return constant($s.lc) if $name eq 'lc';
            return constant($s.uc) if $name eq 'uc';
            return constant($s.trim) if $name eq 'trim';
        }
        if @args == 1 && same(@args[0].type, Str) {
            return constant($s.starts-with(@args[0].value)) if $name eq 'starts-with';
            return constant($s.ends-with(@args[0].value)) if $name eq 'ends-with';
            return constant($s.contains(@args[0].value)) if $name eq 'contains';
        }
        if $name eq 'substr' && 1 <= @args.elems <= 2
            && @args.grep({!same(.type, Int) || .value < 0}).elems == 0
            && @args[0].value <= $s.chars {
            return constant(@args == 1 ?? $s.substr(@args[0].value) !! $s.substr(@args[0].value, @args[1].value));
        }
    }
    if $receiver.has-value && primitive($receiver.value) && $receiver.value ~~ Real && !@args {
        return constant($receiver.value.abs) if $name eq 'abs';
        return constant($receiver.value.floor) if $name eq 'floor';
        return constant($receiver.value.ceiling) if $name eq 'ceiling';
        return constant($receiver.value.sign) if $name eq 'sign';
    }
    if $receiver.finite && !@args {
        return constant($receiver.items.elems) if $name eq 'elems';
        if $name eq any(<sum min max>) && $receiver.items.grep({!.has-value || !primitive(.value) || .value !~~ Real}).elems == 0 {
            my @values = $receiver.items.map(*.value);
            return constant(@values.sum) if $name eq 'sum';
            return constant(@values.min) if $name eq 'min';
            return constant(@values.max) if $name eq 'max';
        }
    }
    return constant($receiver.cardinality) if $name eq 'elems' && !@args && $receiver.cardinality >= 0;
    unknown('method outside primitive allowlist')
}

sub operation(Str $op, @args --> Fact) is export {
    return interval-operation($op, @args) unless @args && @args.grep({ !.has-value }).elems == 0;
    return unknown('non-primitive operands') if @args.grep({ !primitive(.value) });
    my @v = @args.map(*.value);
    my $numeric = @v.grep({ $_ !~~ Numeric }).elems == 0;
    my $strings = @v.grep({ $_ !~~ Str }).elems == 0;
    # Put explicit bounds on operations that can manufacture huge constants.
    return unknown('constant exceeds analysis budget') if @v.grep({ $_ ~~ Int && .base(2).chars > 4096 });
    return unknown('constant exceeds analysis budget') if @v.grep({ $_ ~~ Str && .chars > 4096 });
    my $result;
    try {
        if @v == 1 {
            $result = do given $op {
                when '!' | 'not' { constant(!@v[0]) }
                when '?' | 'so' { constant(?@v[0]) }
                when '+' { $numeric ?? constant(+@v[0]) !! unknown('numeric conversion') }
                when '-' { $numeric ?? constant(-@v[0]) !! unknown('numeric conversion') }
                default { unknown('unsupported constant prefix') }
            };
        }
        elsif @v == 2 {
            my ($a, $b) = @v;
            $result = do given $op {
                when '&&' | 'and' { constant($a && $b) }
                when '||' | 'or' { constant($a || $b) }
                when '//' { constant($a // $b) }
                when '~' { constant($a ~ $b) }
                when 'eq' { $strings ?? constant($a eq $b) !! unknown('string comparison') }
                when 'ne' { $strings ?? constant($a ne $b) !! unknown('string comparison') }
                when 'lt' { $strings ?? constant($a lt $b) !! unknown('string comparison') }
                when 'le' { $strings ?? constant($a le $b) !! unknown('string comparison') }
                when 'gt' { $strings ?? constant($a gt $b) !! unknown('string comparison') }
                when 'ge' { $strings ?? constant($a ge $b) !! unknown('string comparison') }
                default {
                    if $numeric {
                        do given $op {
                            when '+' { constant($a + $b) }
                            when '-' { constant($a - $b) }
                            when '*' { constant($a * $b) }
                            when '/' { $b == 0 ?? unknown('division by zero') !! constant($a / $b) }
                            when 'div' { $b == 0 ?? unknown('division by zero') !! constant($a div $b) }
                            when '%' | 'mod' { $b == 0 ?? unknown('division by zero') !! constant($a mod $b) }
                            when '%%' { $b == 0 ?? unknown('division by zero') !! constant($a %% $b) }
                            when '**' { $b ~~ Int && 0 <= $b <= 64 ?? constant($a ** $b) !! unknown('exponent budget') }
                            when '==' { constant($a == $b) }
                            when '!=' { constant($a != $b) }
                            when '<' { constant($a < $b) }
                            when '<=' { constant($a <= $b) }
                            when '>' { constant($a > $b) }
                            when '>=' { constant($a >= $b) }
                            default { unknown('unsupported constant operator') }
                        }
                    }
                    else { unknown('unsupported constant operator') }
                }
            };
        }
    }
    $result // unknown('constant operation cannot be established')
}

sub unwrap($node) {
    given $node {
        when RakuAST::Block { unwrap(.body) }
        when RakuAST::Blockoid { unwrap(.statement-list) }
        when RakuAST::StatementList | RakuAST::SemiList {
            my @statements = .code-statements;
            @statements == 1 ?? unwrap(@statements[0]) !! Mu
        }
        when RakuAST::Statement::Expression {
            .condition-modifier || .loop-modifier ?? Mu !! unwrap(.expression)
        }
        when RakuAST::Circumfix::Parentheses { unwrap(.semilist) }
        default { $node }
    }
}

sub evaluate($original, Fact $topic, &type-of, &compatible, Str :$name = '', Int :$depth = 0, :%bindings = {} --> Fact) is export {
    return unknown('predicate analysis depth exceeded') if $depth > 64;
    my $node = unwrap($original);
    return unknown('predicate requires statement execution') unless $node.defined;
    given $node {
        when RakuAST::Literal { return constant(.value) }
        when RakuAST::QuotedString {
            return constant(.segments.map(*.value).join) if .segments.grep({ $_ !~~ RakuAST::StrLiteral }).elems == 0;
        }
        when RakuAST::Term::Whatever | RakuAST::VarDeclaration::Placeholder::Positional { return $topic }
        when RakuAST::WhateverCode::Argument { return .name eq '_whatever_arg_1' ?? $topic !! unknown('predicate needs more than one argument') }
        when RakuAST::Var::Lexical {
            if .is-resolved {
                my $decl = .resolution ~~ RakuAST::ParameterTarget::Var ?? .resolution.declaration !! .resolution;
                return %bindings{nqp::objectid($decl).Str} if %bindings{nqp::objectid($decl).Str}:exists;
            }
            return $topic if .name eq '$_' || ($name && .name eq $name);
            if .is-resolved && .resolution ~~ RakuAST::VarDeclaration::Constant {
                return constant(.resolution.compile-time-value);
            }
        }
        when RakuAST::Term::Enum { return constant(type-of($_)) }
        when RakuAST::ApplyPrefix {
            if core-operator(.prefix) {
                my $value = evaluate(.operand, $topic, &type-of, &compatible, :$name, :depth($depth+1), :%bindings);
                return operation(.prefix.operator, [$value]);
            }
        }
        when RakuAST::ApplyInfix {
            if core-operator(.infix) {
                my $op = .infix.operator;
                my $left = evaluate(.left, $topic, &type-of, &compatible, :$name, :depth($depth+1), :%bindings);
                if $op eq '~~' || $op eq '!~~' {
                    my $status = constraint-status(.right, $left, &type-of, &compatible, :$name, :depth($depth+1), :%bindings);
                    return constant(($status eq 'ok') ^^ ($op eq '!~~')) unless $status eq 'unverifiable';
                }
                if $op eq any('&&', 'and') && $left.has-value && !$left.value { return $left }
                if $op eq any('||', 'or') && $left.has-value && $left.value { return $left }
                my $right = evaluate(.right, $topic, &type-of, &compatible, :$name, :depth($depth+1), :%bindings);
                return operation($op, [$left, $right]);
            }
        }
        when RakuAST::ApplyPostfix {
            if .postfix ~~ RakuAST::Call::Method && .postfix.dispatch eq '' {
                my $value = evaluate(.operand, $topic, &type-of, &compatible, :$name, :depth($depth+1), :%bindings);
                my $method = .postfix.name.canonicalize;
                my @args = .postfix.args.args.map({evaluate($_, $topic, &type-of, &compatible, :$name, :depth($depth+1), :%bindings)});
                my $folded = primitive-method($method, $value, @args);
                return $folded unless $folded.reason;
                return constant($value.definite == 1) if $method eq 'defined' && $value.definite >= 0 && $value.exact
                    && same($value.type.HOW.find_method($value.type, 'defined'), Mu.^find_method('defined'));
                return constant($value.value.chars) if $method eq 'chars' && $value.has-value && same($value.type, Str);
                return constant($value.items.elems) if $method eq 'elems' && $value.finite;
            }
        }
    }
    unknown('predicate contains unsupported or dynamic code')
}

sub constraint-status($original, Fact $actual, &type-of, &compatible, Str :$name = '', Int :$depth = 0, :%bindings = {} --> Str) is export {
    return 'unverifiable' if $depth > 64 || $actual.reason;
    if $actual.alternatives {
        my @statuses = $actual.alternatives.map({ constraint-status($original, $_, &type-of, &compatible, :$name, :depth($depth+1), :%bindings) }).unique;
        return @statuses == 1 ?? @statuses[0] !! 'unverifiable';
    }
    my $node = unwrap($original);
    return 'unverifiable' unless $node.defined;
    my $callable = $original ~~ RakuAST::Block;
    if !$callable && $node ~~ RakuAST::Type {
        my Mu $type = type-of($node);
        return nominal-matcher($type) ?? compatible($actual, $type) !! 'unverifiable';
    }
    if !$callable && $node ~~ RakuAST::ApplyListInfix && core-operator($node.infix) && $node.infix.operator eq any('|', '&', '^') {
        my @statuses = $node.operands.map({ constraint-status($_, $actual, &type-of, &compatible, :$name, :depth($depth+1), :%bindings) });
        given $node.infix.operator {
            when '|' { return 'ok' if @statuses.grep(* eq 'ok'); return @statuses.grep(* eq 'unverifiable') ?? 'unverifiable' !! 'mismatch' }
            when '&' { return 'mismatch' if @statuses.grep(* eq 'mismatch'); return @statuses.grep(* eq 'unverifiable') ?? 'unverifiable' !! 'ok' }
            when '^' { return 'unverifiable' if @statuses.grep(* eq 'unverifiable'); return @statuses.grep(* eq 'ok') == 1 ?? 'ok' !! 'mismatch' }
        }
    }
    if !$callable && $node ~~ RakuAST::ApplyInfix && core-operator($node.infix) && $node.infix.operator eq any('..', '^..', '..^', '^..^') {
        my $lo = evaluate($node.left, $actual, &type-of, &compatible, :$name, :depth($depth+1), :%bindings);
        my $hi = evaluate($node.right, $actual, &type-of, &compatible, :$name, :depth($depth+1), :%bindings);
        return 'unverifiable' unless $actual.has-value && $lo.has-value && $hi.has-value;
        my $lower = operation($node.infix.operator.starts-with('^') ?? '>' !! '>=', [$actual, $lo]);
        my $upper = operation($node.infix.operator.ends-with('^') ?? '<' !! '<=', [$actual, $hi]);
        return 'unverifiable' unless $lower.has-value && $upper.has-value;
        return $lower.value && $upper.value ?? 'ok' !! 'mismatch';
    }
    my $result = evaluate($node, $actual, &type-of, &compatible, :$name, :$depth, :%bindings);
    return 'unverifiable' unless $result.has-value;
    # Literal where constraints smartmatch the candidate; a block/Whatever
    # expression is a predicate whose result is interpreted as a Bool.
    if !$callable && ($node ~~ RakuAST::Literal || $node ~~ RakuAST::QuotedString || $node ~~ RakuAST::Term::Enum) {
        return $result.value ?? 'ok' !! 'mismatch' if same($result.type, Bool);
        return 'unverifiable' unless $actual.has-value;
        my $comparison = operation(same($result.type, Str) ?? 'eq' !! '==', [$actual, $result]);
        return $comparison.has-value ?? ($comparison.value ?? 'ok' !! 'mismatch') !! 'unverifiable';
    }
    $result.value ?? 'ok' !! 'mismatch'
}
