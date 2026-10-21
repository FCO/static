use nqp;
use static::Types;
unit module static::Predicates;

# An interpreter for a deliberately bounded, pure subset of expressions.
# It never invokes a routine/regex/coercion from the inspected program.
sub core-operator($op --> Bool) {
    so $op ~~ RakuAST::Lookup && $op.is-resolved
        && $op.resolution ~~ RakuAST::Declaration::External::Setting
}

sub operation(Str $op, @args --> Fact) is export {
    return unknown('nonconstant operands') unless @args && @args.grep({ !.has-value }).elems == 0;
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

sub evaluate($original, Fact $topic, &type-of, &compatible, Str :$name = '', Int :$depth = 0 --> Fact) is export {
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
            return $topic if .name eq '$_' || ($name && .name eq $name);
            if .is-resolved && .resolution ~~ RakuAST::VarDeclaration::Constant {
                return constant(.resolution.compile-time-value);
            }
        }
        when RakuAST::Term::Enum { return constant(type-of($_)) }
        when RakuAST::ApplyPrefix {
            if core-operator(.prefix) {
                my $value = evaluate(.operand, $topic, &type-of, &compatible, :$name, :depth($depth+1));
                return operation(.prefix.operator, [$value]);
            }
        }
        when RakuAST::ApplyInfix {
            if core-operator(.infix) {
                my $op = .infix.operator;
                my $left = evaluate(.left, $topic, &type-of, &compatible, :$name, :depth($depth+1));
                if $op eq '~~' || $op eq '!~~' {
                    my $status = constraint-status(.right, $left, &type-of, &compatible, :$name, :depth($depth+1));
                    return constant(($status eq 'ok') ^^ ($op eq '!~~')) unless $status eq 'unverifiable';
                }
                if $op eq any('&&', 'and') && $left.has-value && !$left.value { return $left }
                if $op eq any('||', 'or') && $left.has-value && $left.value { return $left }
                my $right = evaluate(.right, $topic, &type-of, &compatible, :$name, :depth($depth+1));
                return operation($op, [$left, $right]);
            }
        }
        when RakuAST::ApplyPostfix {
            if .postfix ~~ RakuAST::Call::Method && .postfix.args.args.elems == 0 {
                my $value = evaluate(.operand, $topic, &type-of, &compatible, :$name, :depth($depth+1));
                my $method = .postfix.name.canonicalize;
                return constant($value.definite == 1) if $method eq 'defined' && $value.definite >= 0 && $value.exact
                    && same($value.type.HOW.find_method($value.type, 'defined'), Mu.^find_method('defined'));
                return constant($value.value.chars) if $method eq 'chars' && $value.has-value && same($value.type, Str);
                return constant($value.items.elems) if $method eq 'elems' && $value.finite;
            }
        }
    }
    unknown('predicate contains unsupported or dynamic code')
}

sub constraint-status($original, Fact $actual, &type-of, &compatible, Str :$name = '', Int :$depth = 0 --> Str) is export {
    return 'unverifiable' if $depth > 64 || $actual.reason;
    if $actual.alternatives {
        my @statuses = $actual.alternatives.map({ constraint-status($original, $_, &type-of, &compatible, :$name, :depth($depth+1)) }).unique;
        return @statuses == 1 ?? @statuses[0] !! 'unverifiable';
    }
    my $node = unwrap($original);
    return 'unverifiable' unless $node.defined;
    my $callable = $original ~~ RakuAST::Block;
    return compatible($actual, type-of($node)) if !$callable && $node ~~ RakuAST::Type;
    if !$callable && $node ~~ RakuAST::ApplyListInfix && core-operator($node.infix) && $node.infix.operator eq any('|', '&', '^') {
        my @statuses = $node.operands.map({ constraint-status($_, $actual, &type-of, &compatible, :$name, :depth($depth+1)) });
        given $node.infix.operator {
            when '|' { return 'ok' if @statuses.grep(* eq 'ok'); return @statuses.grep(* eq 'unverifiable') ?? 'unverifiable' !! 'mismatch' }
            when '&' { return 'mismatch' if @statuses.grep(* eq 'mismatch'); return @statuses.grep(* eq 'unverifiable') ?? 'unverifiable' !! 'ok' }
            when '^' { return 'unverifiable' if @statuses.grep(* eq 'unverifiable'); return @statuses.grep(* eq 'ok') == 1 ?? 'ok' !! 'mismatch' }
        }
    }
    if !$callable && $node ~~ RakuAST::ApplyInfix && core-operator($node.infix) && $node.infix.operator eq any('..', '^..', '..^', '^..^') {
        my $lo = evaluate($node.left, $actual, &type-of, &compatible, :$name, :depth($depth+1));
        my $hi = evaluate($node.right, $actual, &type-of, &compatible, :$name, :depth($depth+1));
        return 'unverifiable' unless $actual.has-value && $lo.has-value && $hi.has-value;
        my $lower = operation($node.infix.operator.starts-with('^') ?? '>' !! '>=', [$actual, $lo]);
        my $upper = operation($node.infix.operator.ends-with('^') ?? '<' !! '<=', [$actual, $hi]);
        return 'unverifiable' unless $lower.has-value && $upper.has-value;
        return $lower.value && $upper.value ?? 'ok' !! 'mismatch';
    }
    my $result = evaluate($node, $actual, &type-of, &compatible, :$name, :$depth);
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
