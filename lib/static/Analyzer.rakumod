use nqp;
use static::Types;
use static::Predicates;
unit class static::Analyzer;

has Bool $.external-signatures = True;
has Bool $.check-methods = True;
has @!routines;
has %!locals;
has %!summaries;
has %!parameters;
has %!parameter-rw;
has %!deferred-writes;
has %!binding-writable;
has %!element-aliases;
has %!shapes;
has %!declarations;
has %!parameter-asts;
has %!subsets;
has %!locations;
has %!origins;
has %!self-types;
has @!diagnostics;
has %!reported;
has %!checked-blocks;
has %!aliases;
has %!ambiguous-aliases;
has Bool $!emit = False;

sub id(Mu $object --> Str) { nqp::objectid($object).Str }
sub concrete(Mu $object --> Bool) { so nqp::isconcrete($object) }
sub children($node --> List) {
    my @children;
    $node.visit-children(-> $child { @children.push($child) if concrete($child) });
    @children.List
}
sub ast-type($node --> Mu) {
    return Mu unless concrete($node);
    # Only already-resolved compile-time metadata; never literalize/EVAL.
    return $node.resolution.compile-time-value
        if $node ~~ RakuAST::Lookup && $node.is-resolved
            && $node.resolution.^can('compile-time-value');
    return $node.compile-time-value if $node.^can('compile-time-value');
    Mu
}
sub clone-env(%env --> Hash) { %env.Hash.clone }
sub join-env(%target, *@branches) {
    for @branches.map(*.keys).flat.unique -> $key {
        my @values = @branches.map({ $_{$key}:exists ?? $_{$key} !! unknown('value not established on every path') });
        %target{$key} = merge(|@values);
    }
}

method !index($node, Str $location is copy, Mu $package is copy = Mu, Mu $inherited-origin = Mu) {
    return if %!locations{id($node)}:exists;
    %!declarations{id($node)} = $node if $node ~~ RakuAST::VarDeclaration::Simple;
    my $origin = $node.origin;
    $origin = $inherited-origin unless concrete($origin);
    if concrete($origin) {
        my $match = $origin.as-match;
        $location = $match.file ~ ':' ~ $match.line;
    }
    %!locations{id($node)} = $location;
    %!origins{id($node)} = $origin;
    $package = ast-type($node) if $node ~~ RakuAST::Package;
    %!subsets{id(ast-type($node))} = $node if $node ~~ RakuAST::Type::Subset;
    %!self-types{id($node)} = $package if $node ~~ RakuAST::Block;
    if $node ~~ RakuAST::Parameter && $node.target ~~ RakuAST::ParameterTarget::Var {
        my $param = $node.meta-object;
        %!parameter-rw{id($node.target.declaration)} = $param.rw || $param.copy
            || $node.target.name.starts-with('@') || $node.target.name.starts-with('%')
            ?? 1 !! $param.raw ?? -1 !! 0;
        %!parameter-asts{id($param)} = $node;
        %!parameters{id($node.target.declaration)} = known($param.type,
            :definite($param.modifier eq ':D' ?? 1 !! $param.modifier eq ':U' ?? 0 !! -1));
        if $node.target.name.starts-with('@') || $node.target.name.starts-with('%') {
            my Mu $element = $param.type.of;
            %!parameters{id($node.target.declaration)} = Fact.new(:type($param.type), :definite(1),
                :sequence($node.target.name.starts-with('@')), :element(known($element)),
                :constrained-elements(!same($element, Mu) && !same($element, Any)));
        }
        if $node.type-captures.elems == 1 {
            %!parameters{id($node.target.declaration)} = known($node.type-captures[0].compile-time-value);
        }
    }
    if $node ~~ RakuAST::Routine && $node.^can('body') && concrete($node.body) {
        @!routines.push($node);
        %!locals{id($node.compile-time-value)} = $node;
        %!self-types{id($node)} = $package;
        %!summaries{id($node)} = bottom;
    }
    self!index($_, $location, $package, $origin) for children($node);
}

method !report($node, Str $category, Str $context, Str :$expected = '', Str :$actual = '', Str :$reason = '') {
    return unless $!emit;
    my $location = %!locations{id($node)} // '<unknown>';
    my $key = (id($node), $category, $context, $expected, $actual, $reason).join('|');
    return if %!reported{$key}++;
    @!diagnostics.push(Diagnostic.new(:$category, :$location, :$context, :$expected, :$actual, :$reason,
        :origin(%!origins{id($node)})));
}
method !check($node, Fact $actual is copy, Mu $expected, Str $context, Bool :$nil-ok = False) {
    return if $nil-ok && same($actual.type, Nil);
    $actual = merge(|$actual.alternatives.grep({ !same(.type, Nil) })) if $nil-ok && $actual.alternatives;
    my $status = self!relation($actual, $expected);
    self!report($node, $status, $context, :expected($expected.^name), :actual($actual.label),
        :reason($status eq 'unverifiable' ?? ($actual.reason || 'compatibility depends on runtime values or dispatch') !! ''))
        unless $status eq 'ok';
}

method !predicate($ast, Fact $actual, Str :$name = '' --> Str) {
    constraint-status($ast, $actual, &ast-type,
        -> $value, Mu $type { self!relation($value, $type) }, :$name)
}

method !relation(Fact $actual, Mu $expected --> Str) {
    return 'ok' if $actual.bottom;
    if $actual.alternatives {
        my @statuses = $actual.alternatives.map({ self!relation($_, $expected) }).unique;
        return @statuses == 1 ?? @statuses[0] !! 'unverifiable';
    }
    if $expected.HOW.^name.ends-with('DefiniteHOW') {
        my $base = self!relation($actual, $expected.^base_type);
        return $base unless $base eq 'ok';
        return 'unverifiable' if $actual.definite < 0;
        return $actual.definite == +$expected.^definite ?? 'ok' !! 'mismatch';
    }
    if $expected.HOW.^name.ends-with('SubsetHOW') {
        return 'ok' if same($actual.type, $expected);
        my $base = self!relation($actual, $expected.^refinee);
        return $base unless $base eq 'ok';
        return self!predicate(%!subsets{id($expected)}.where, $actual)
            if %!subsets{id($expected)}:exists;
        return 'unverifiable';
    }
    relation($actual, $expected)
}

method !stored(Fact $value, Mu $expected --> Fact) {
    return $value unless $expected.HOW.^name.ends-with('NativeHOW');
    my $name = $expected.^name;
    if $name ~~ / ^ (u?) 'int' (\d*) $ / {
        my $unsigned = ~$0 eq 'u';
        my $bits = ~$1 eq '' ?? 64 !! +$1;
        if $value.has-value && $value.value ~~ Int && $bits <= 64 {
            my $wrapped = $value.value mod (2 ** $bits);
            $wrapped -= 2 ** $bits if !$unsigned && $wrapped >= 2 ** ($bits - 1);
            return constant($wrapped);
        }
        return known(Int, :definite(1));
    }
    $name.starts-with('num') ?? known(Num, :definite(1)) !! $name eq 'str' ?? known(Str, :definite(1)) !! unknown('native representation')
}

method analyze(RakuAST::CompUnit:D $cu --> List) {
    my $*STATIC-CONDITIONAL = False;
    my @*STATIC-YIELDS;
    my $*STATIC-YIELD-KIND = '';
    my Fact $*STATIC-TOPIC = unknown('topic outside given');
    my %*STATIC-TYPES;
    my %*STATIC-WRITTEN;
    @!routines = (); %!locals = (); %!summaries = (); %!parameters = ();
    %!parameter-rw = (); %!deferred-writes = ();
    %!binding-writable = (); %!element-aliases = (); %!shapes = (); %!declarations = ();
    %!parameter-asts = (); %!subsets = (); %!locations = (); %!origins = ();
    %!self-types = (); @!diagnostics = (); %!reported = (); %!checked-blocks = ();
    %!aliases = ();
    %!ambiguous-aliases = ();
    $!emit = False;
    self!index($cu.statement-list, $cu.fileline);
    # Monotone summaries let forward calls and recursive components converge.
    my @unstable;
    for ^32 {
        @unstable = ();
        for @!routines -> $routine {
            my $key = id($routine);
            my $next = merge(%!summaries{$key}, self!routine($routine));
            if $next.key ne %!summaries{$key}.key {
                %!summaries{$key} = $next;
                @unstable.push($key);
            }
        }
        last unless @unstable;
    }
    %!summaries{$_} = unknown('recursive return inference did not converge within 32 passes') for @unstable;
    for @!routines -> $routine {
        my $key = id($routine);
        %!summaries{$key} = unknown('recursive return has no established type') if %!summaries{$key}.bottom;
    }
    $!emit = True;
    self!routine($_) for @!routines;
    my %env;
    my @*STATIC-RETURNS;
    my Mu $*STATIC-ROUTINE = Mu;
    %!deferred-writes = ();
    self!statements($cu.statement-list, %env);
    @!diagnostics.List
}

method !routine($routine --> Fact) {
    %!deferred-writes = ();
    my %*STATIC-TYPES;
    my @*STATIC-RETURNS;
    my @*STATIC-YIELDS;
    my $*STATIC-YIELD-KIND = '';
    my Mu $*STATIC-ROUTINE = $routine;
    my %env;
    for $routine.signature.parameters -> $parameter {
        if concrete($parameter.default) {
            my $actual = self!infer($parameter.default, %env);
            my $param = $parameter.meta-object;
            my $status = self!parameter-relation($actual, $param);
            self!report($parameter, $status, 'default for parameter ' ~ $param.name,
                :expected($param.type.^name ~ ($param.constraint_list.elems ?? ' with constraint' !! '')),
                :actual($actual.label)) unless $status eq 'ok';
        }
    }
    my $fallthrough = self!infer($routine.body, %env);
    @*STATIC-RETURNS.push($fallthrough) unless $fallthrough.bottom;
    # Checking each exit preserves a useful diagnostic even if .are widens it.
    if self!has-return-contract($routine) {
        my Mu $expected = $routine.compile-time-value.signature.returns;
        for @*STATIC-RETURNS -> $exit {
            # Every possible exit must satisfy the declared contract. A valid
            # alternative must not hide an incompatible return from the body.
            for ($exit.alternatives ?? $exit.alternatives.List !! ($exit,)) -> $value {
                self!check($routine, $value, $expected,
                    'return from ' ~ $routine.name.canonicalize, :nil-ok);
            }
        }
    }
    merge(|@*STATIC-RETURNS)
}

method !has-return-contract($routine --> Bool) {
    concrete($routine.signature.returns) || !same($routine.compile-time-value.signature.returns, Mu)
}

method !declared($decl --> Fact) {
    return %!parameters{id($decl)} if %!parameters{id($decl)}:exists;
    if $decl ~~ RakuAST::ParameterTarget::Var { return self!declared($decl.declaration) }
    if $decl ~~ RakuAST::VarDeclaration::AttributeAlias { return self!declared($decl.attribute) }
    if $decl ~~ RakuAST::VarDeclaration::Simple {
        if $decl.sigil eq '@' || $decl.sigil eq '%' {
            my Mu $element = concrete($decl.type) ?? ast-type($decl.type) !! Mu;
            return Fact.new(:type($decl.return-type), :definite(1), :sequence($decl.sigil eq '@'),
                :element(known($element)), :constrained-elements(!same($element, Mu)),
                :key-type($decl.sigil eq '%' && concrete($decl.shape) ?? $decl.return-type.keyof !! Mu));
        }
        return self!stored(known($decl.return-type, :definite(1)), $decl.return-type)
            if $decl.return-type.HOW.^name.ends-with('NativeHOW');
        return known($decl.return-type);
    }
    if $decl.^can('return-type') {
        my Mu $type = $decl.return-type;
        return known($type) unless same($type, Mu);
    }
    unknown('unresolved variable contract')
}

method !constraint($decl --> Mu) {
    return %!parameters{id($decl)}.type if %!parameters{id($decl)}:exists;
    return $decl.declaration.return-type if $decl ~~ RakuAST::ParameterTarget::Var;
    return $decl.attribute.return-type if $decl ~~ RakuAST::VarDeclaration::AttributeAlias;
    return $decl.return-type if $decl.^can('return-type');
    Mu
}
method !write($target, Fact $value, %env, $site) {
    if $target ~~ RakuAST::Circumfix::Parentheses
        || ($target ~~ RakuAST::ApplyListInfix && $target.infix ~~ RakuAST::Infix && $target.infix.operator eq ',') {
        unless !$value.sequence || $value.finite {
            self!report($site, 'unverifiable', 'destructuring assignment', :reason('source length is unknown'));
            return;
        }
        my @targets = self!list-items($target);
        my @values = $value.finite ?? $value.items.List !! ($value,);
        for @targets.kv -> $i, $part {
            if $part ~~ RakuAST::Var::Lexical && $part.name.starts-with('@') {
                my @rest = @values[$i ..^ @values.elems];
                self!write($part, Fact.new(:type(List), :definite(1), :sequence, :finite,
                    :items(@rest), :element(merge(|@rest))), %env, $site);
                last;
            }
            self!write($part, $i < @values.elems ?? @values[$i] !! known(Nil, :definite(0)), %env, $site);
        }
        return;
    }
    if $target ~~ RakuAST::Var::Lexical && $target.is-resolved {
        my $decl = $target.resolution ~~ RakuAST::ParameterTarget::Var
            ?? $target.resolution.declaration !! $target.resolution;
        my $alias = $decl;
        my $binding = $site ~~ RakuAST::ApplyInfix && $site.infix ~~ RakuAST::Infix
            && $site.infix.operator eq ':=';
        if $binding {
            %!aliases{id($alias)}:delete;
            %!element-aliases{id($alias)}:delete;
            %!binding-writable{id($alias)}:delete;
            self!check($site, $value, self!constraint($alias), 'binding to ' ~ $target.name);
            if $site.right ~~ RakuAST::Var::Lexical && $site.right.is-resolved {
                %!aliases{id($alias)} = self!root($site.right.resolution);
                if $*STATIC-CONDITIONAL { %!ambiguous-aliases{id($alias)} = True }
                else { %!ambiguous-aliases{id($alias)}:delete }
            }
            else {
                self!bind-target($alias, $site.right, %env);
            }
            return;
        }
        $decl = self!root($decl);
        %*STATIC-WRITTEN{id($decl)} = True;
        if %!ambiguous-aliases{id($decl)} || %!ambiguous-aliases{id($alias)} {
            self!report($site, 'unverifiable', 'assignment through alias', :reason('binding depends on control flow'));
            return;
        }
        if $target.name.starts-with('$') && $decl ~~ RakuAST::VarDeclaration::Simple
            && $decl.sigil eq any('@', '%') {
            self!report($site, 'mismatch', 'assignment to ' ~ $target.name,
                :reason('bound aggregate value is not a writable scalar container'));
            return;
        }
        if %!parameter-rw{id($decl)}:exists {
            if %!parameter-rw{id($decl)} == 0 {
                self!report($site, 'mismatch', 'assignment to ' ~ $target.name,
                    :reason('parameter is readonly; use is rw or is copy to assign to it'));
                return;
            }
            elsif %!parameter-rw{id($decl)} < 0 {
                self!report($site, 'unverifiable', 'assignment to ' ~ $target.name,
                    :reason('raw parameter writability depends on its caller'));
            }
        }
        if %!binding-writable{id($decl)}:exists {
            if %!binding-writable{id($decl)} == 0 {
                self!report($site, 'mismatch', 'assignment to ' ~ $target.name, :reason('bound value is not writable'));
                return;
            }
        }
        if %!element-aliases{id($decl)}:exists {
            self!write(%!element-aliases{id($decl)}, $value, %env, $site);
            %env{id($decl)} = $value;
            return;
        }
        my $contract = self!declared($decl);
        $contract = $contract.clone(:shape(%!shapes{id($decl)})) if %!shapes{id($decl)}:exists;
        self!check($site, $value, self!constraint($alias), 'assignment to alias ' ~ $target.name)
            unless same($alias, $decl);
        if concrete($contract.element) && !$binding && $decl ~~ RakuAST::VarDeclaration::Simple {
            self!invalidate($target, %env);
            self!collection-init($decl, $site.right, $value, $contract, %env);
        }
        else {
            self!check($site, $value, self!constraint($decl), 'assignment to ' ~ $target.name, :nil-ok(!$binding));
        }
        # Typed collections keep their element contract after writes.
        my $retained = concrete($contract.element) && !$binding && (%env{id($decl)}:exists)
            ?? %env{id($decl)} !! $contract;
        if $contract.sequence && !$binding {
            %env{id($decl)} = $retained.clone(:finite($value.finite),
                :items($value.finite ?? $value.items !! []), :identity(id($decl)),
                :element($contract.constrained-elements ?? $contract.element
                    !! $value.finite ?? merge(|$value.items) !! unknown('collection contents after assignment')));
            return;
        }
        %env{id($decl)} = concrete($contract.element) || same($value.type, Nil) ?? $retained !! self!stored($value, self!constraint($decl));
    }
    elsif $target ~~ RakuAST::ApplyPostfix
        && ($target.postfix ~~ RakuAST::Postcircumfix::Index
            || $target.postfix ~~ RakuAST::Postcircumfix::LiteralHashIndex) {
        my $container = self!infer($target.operand, %env);
        if concrete($container.element) {
            self!check($site, $value, $container.constrained-elements ?? $container.element.type !! Mu, 'indexed assignment');
            self!index-key($target.postfix, $container, %env);
        }
        else {
            self!report($site, 'unverifiable', 'indexed assignment', :reason('collection element contract unavailable'));
        }
        self!invalidate($target.operand, %env);
    }
    elsif $target ~~ RakuAST::Var::Attribute {
        self!check($site, $value, $target.return-type, 'assignment to attribute ' ~ $target.name, :nil-ok);
    }
    else {
        self!report($site, 'unverifiable', 'assignment target', :reason('dynamic or unsupported lvalue'));
    }
}

method !root($decl) {
    my $root = $decl ~~ RakuAST::ParameterTarget::Var ?? $decl.declaration !! $decl;
    my %seen;
    while (%!aliases{id($root)}:exists) && !%seen{id($root)}++ && !%!ambiguous-aliases{id($root)} {
        $root = %!aliases{id($root)};
    }
    $root
}

method !invalidate($target, %env) {
    return unless $target ~~ RakuAST::Var::Lexical && $target.is-resolved;
    my $decl = self!root($target.resolution);
    %*STATIC-WRITTEN{id($decl)} = True;
    return unless %env{id($decl)}:exists;
    my $fact = %env{id($decl)};
    if $fact.sequence || concrete($fact.element) {
        my @keys = $fact.identity
            ?? %env.keys.grep({ %env{$_}.identity eq $fact.identity }).List !! (id($decl),);
        for @keys -> $key {
            my $old = %env{$key};
            %env{$key} = $old.clone(:finite(False), :items([]),
                :element($old.constrained-elements ?? $old.element !! unknown('collection contents may have changed')));
        }
    }
    else { %env{id($decl)} = self!declared($decl) }
}

method !effects(Mu $routine, %env, $args, %seen = {}) {
    return unless $routine ~~ Routine;
    for $routine.candidates -> $candidate {
        next if %seen{id($candidate)}++;
        my $local = %!locals{id($candidate)};
        my $rw = !$local.defined && !$!external-signatures
            || $candidate.signature.params.grep(*.rw).elems;
        for $args.args -> $arg {
            my $target = $arg ~~ RakuAST::FatArrow || $arg ~~ RakuAST::ColonPair
                ?? ($arg.^can('value') ?? $arg.value !! Mu) !! $arg;
            next unless $target ~~ RakuAST::Var::Lexical && $target.is-resolved;
            my $key = id(self!root($target.resolution));
            next unless %env{$key}:exists;
            self!invalidate($target, %env) if $rw || %env{$key}.sequence || concrete(%env{$key}.element);
        }
        next unless $local.defined;
        my &walk;
        &walk = sub ($node) {
            return if $node ~~ RakuAST::Routine;
            return if $node ~~ RakuAST::Block && !$node.is-block-statement && !$node.is-immediate-block-user-body;
            if $node ~~ RakuAST::ApplyInfix && ($node.infix ~~ RakuAST::Assignment
                || $node.infix ~~ RakuAST::MetaInfix::Assign
                || ($node.infix ~~ RakuAST::Infix && $node.infix.operator eq ':=')) {
                self!invalidate($node.left, %env);
            }
            if $node ~~ RakuAST::ApplyPostfix && ($node.postfix ~~ RakuAST::Postfix
                || $node.postfix ~~ RakuAST::Call::Method || $node.postfix ~~ RakuAST::Postcircumfix::Index) {
                self!invalidate($node.operand, %env);
            }
            if $node ~~ RakuAST::Call::Name && $node.is-resolved
                && $node.resolution.^can('compile-time-value') {
                self!effects($node.resolution.compile-time-value, %env, $node.args, %seen);
            }
            walk($_) for children($node);
        };
        walk($local.body);
    }
}

method !index-key($postfix, Fact $container, %env) {
    if $container.shape && $postfix ~~ RakuAST::Postcircumfix::ArrayIndex {
        my @indices = $postfix.index ~~ RakuAST::SemiList ?? $postfix.index.code-statements.List !! ($postfix.index,);
        if @indices.elems != $container.shape.elems {
            self!report($postfix, 'mismatch', 'array index rank', :reason('index count differs from array dimensions'));
        }
        else {
            for @indices.kv -> $i, $index {
                my $value = self!infer($index, %env);
                if $value.has-value && $value.value ~~ Int {
                    self!report($postfix, 'mismatch', 'array index bounds', :reason('index outside dimension ' ~ ($i+1)))
                        if $value.value < 0 || $value.value >= $container.shape[$i];
                }
                else { self!report($postfix, 'unverifiable', 'array index bounds', :reason('index is not a known integer')) }
            }
        }
    }
    return if same($container.key-type, Mu) || !$postfix.^can('index');
    if $postfix ~~ RakuAST::Postcircumfix::LiteralHashIndex {
        self!check($postfix, self!infer($postfix.index, %env), $container.key-type, 'hash key');
    }
    elsif $postfix ~~ RakuAST::Postcircumfix::HashIndex {
        self!check($postfix, self!infer($postfix.index, %env), $container.key-type, 'hash key');
    }
}

method !list-items($node --> List) {
    if $node ~~ RakuAST::ApplyListInfix && $node.infix ~~ RakuAST::Infix && $node.infix.operator eq ',' {
        return $node.operands.List;
    }
    if $node ~~ RakuAST::Circumfix::Parentheses { return self!list-items($node.semilist) }
    if $node ~~ RakuAST::SemiList {
        my @statements = $node.code-statements;
        return () unless @statements;
        return self!list-items(@statements[0].expression) if @statements == 1 && @statements[0] ~~ RakuAST::Statement::Expression;
    }
    ($node,).List
}

method !infer($node, %env, Bool :$immediate = False --> Fact) {
    return known(Nil, :definite(0)) unless concrete($node);
    given $node {
        when RakuAST::StatementList | RakuAST::SemiList {
            my $value = known(Nil, :definite(0));
            for .code-statements -> $statement {
                $value = self!infer($statement, %env);
                last if $value.bottom;
            }
            return $value;
        }
        when RakuAST::Statement::Expression {
            if concrete(.condition-modifier) || concrete(.loop-modifier) {
                my $*STATIC-CONDITIONAL = True;
                if concrete(.condition-modifier) { self!infer($_, %env) for children(.condition-modifier) }
                if concrete(.loop-modifier) { self!infer($_, %env) for children(.loop-modifier) }
                my %branch = clone-env(%env);
                my $result = self!infer(.expression, %branch);
                my %before = clone-env(%env);
                join-env(%env, %before, %branch);
                if concrete(.loop-modifier) {
                    for %env.keys -> $key {
                        next unless (%before{$key}:exists) && %before{$key}.key ne %env{$key}.key;
                        my @alts = %env{$key}.alternatives ?? %env{$key}.alternatives.List !! (%env{$key},);
                        %env{$key} = merge(|@alts.map({ .reason ?? $_ !! known(.type, :definite(.definite)) }));
                    }
                }
                return merge($result, known(Nil, :definite(0)));
            }
            return self!infer(.expression, %env);
        }
        when RakuAST::Routine { return known(.compile-time-value.WHAT, :definite(1)) }
        when RakuAST::Package {
            self!infer(.body, %env, :immediate);
            return known(ast-type($_), :definite(0), :exact);
        }
        when RakuAST::Blockoid { return self!statements(.statement-list, %env) }
        when RakuAST::Block {
            return self!infer(.body, %env) if $immediate || .is-block-statement;
            # Inspect a closure in a separate context. Its returns must not
            # become exits of the routine constructing that closure.
            if $!emit && !%!checked-blocks{id($_)}++ {
                my %closed;
                my @*STATIC-YIELDS;
                my $*STATIC-YIELD-KIND = '';
                my @*STATIC-RETURNS;
                my Mu $*STATIC-ROUTINE = $_;
                self!infer(.body, %closed);
            }
            return known(Block, :definite(1));
        }
        when RakuAST::Literal { return primitive(.value) ?? constant(.value) !! known(.value.WHAT, :definite(+concrete(.value)), :exact) }
        when RakuAST::QuotedString {
            return constant(.segments.map(*.value).join) if .segments.grep({ $_ !~~ RakuAST::StrLiteral }).elems == 0;
            self!infer($_, %env) for .segments.grep({ $_ !~~ RakuAST::StrLiteral });
            return known(Str, :definite(1), :exact);
        }
        when RakuAST::Type {
            return known(ast-type($_), :definite(0), :exact);
        }
        when RakuAST::Term::Name | RakuAST::Term::Enum {
            return unknown('dynamic or unresolved symbolic lookup') unless .is-resolved && !.name.is-indirect-lookup;
            my Mu $value = ast-type($_);
            return constant($value) if primitive($value) && concrete($value);
            return known($value.WHAT, :definite(+concrete($value)), :exact);
        }
        when RakuAST::Term::Self {
            return known(%!self-types{id($*STATIC-ROUTINE)}, :definite(1))
                if concrete($*STATIC-ROUTINE) && !same(%!self-types{id($*STATIC-ROUTINE)}, Mu);
            return unknown('self type unavailable');
        }
        when RakuAST::Var::Lexical {
            return unknown('unresolved lexical ' ~ .name) unless .is-resolved;
            my $decl = self!root(.resolution);
            return $*STATIC-TOPIC if .name eq '$_';
            return unknown('value may be modified by deferred or concurrent code') if %!deferred-writes{id($decl)};
            return self!infer(%!element-aliases{id($decl)}, %env) if %!element-aliases{id($decl)}:exists;
            return unknown('binding depends on control flow') if %!ambiguous-aliases{id($decl)};
            return %env{id($decl)} if %env{id($decl)}:exists;
            return self!declared($decl);
        }
        when RakuAST::Var::Attribute { return known(.return-type) }
        when RakuAST::Var::Attribute::Public {
            my @expressions = children($_);
            return self!infer(@expressions[0], %env) if @expressions;
            return unknown('attribute accessor unavailable');
        }
        when RakuAST::VarDeclaration::Simple {
            my $fact = self!declared($_);
            my @shape = .sigil eq '@' && concrete(.shape) ?? self!shape($_, %env) !! ();
            %!shapes{id($_)} = @shape.Array if @shape;
            if (.sigil eq '@' || .sigil eq '%') && !(concrete(.initializer) && .initializer.is-binding) {
                $fact = Fact.new(:type(.container-type), :definite(1), :exact,
                    :sequence(.sigil eq '@'), :element($fact.element), :key-type($fact.key-type),
                    :constrained-elements($fact.constrained-elements), :shape(@shape), :identity(id($_)));
            }
            if concrete(.initializer) && .initializer ~~ RakuAST::Initializer::Expression {
                my $value = self!infer(.initializer.expression, %env);
                if .sigil eq '@' || .sigil eq '%' {
                    if .initializer.is-binding {
                        self!check($_, $value, .return-type, 'collection binding');
                    }
                    else {
                        self!collection-init($_, .initializer.expression, $value, $fact, %env);
                        if .sigil eq '@' && $value.finite && !$fact.shape {
                            $fact = $fact.clone(:finite, :items($value.items),
                                :element($fact.constrained-elements ?? $fact.element !! merge(|$value.items)));
                        }
                    }
                }
                else {
                    self!check($_, $value, .return-type, 'initialization of ' ~ .sigil ~ .desigilname.canonicalize,
                        :nil-ok(!.initializer.is-binding));
                    $fact = self!stored($value, .return-type) unless same($value.type, Nil);
                }
            }
            elsif concrete(.initializer) {
                self!report($_, 'unverifiable', 'initializer', :reason('unsupported initializer form'));
            }
            %env{id($_)} = $fact;
            if concrete(.initializer) && .initializer.is-binding
                && .initializer ~~ RakuAST::Initializer::Expression
                && .initializer.expression ~~ RakuAST::Var::Lexical && .initializer.expression.is-resolved {
                %!aliases{id($_)} = self!root(.initializer.expression.resolution);
                %!ambiguous-aliases{id($_)} = True if $*STATIC-CONDITIONAL;
            }
            elsif concrete(.initializer) && .initializer.is-binding {
                self!bind-target($_, .initializer.expression, %env);
            }
            return $fact;
        }
        when RakuAST::VarDeclaration::Signature {
            return self!destructure($_, %env);
        }
        when RakuAST::Statement::Given {
            my Fact $*STATIC-TOPIC = self!infer(.source, %env);
            return self!given(.body.body.statement-list, %env);
        }
        when RakuAST::Statement::When | RakuAST::Statement::Default {
            return self!given(RakuAST::StatementList.new($_), %env);
        }
        when RakuAST::Statement::ExceptionHandler {
            # Handler declarations execute only when an exception is raised.
            return known(Nil, :definite(0));
        }
        when RakuAST::VarDeclaration::Constant {
            # Its value has already been established by Raku, not by this pass.
            my Mu $value = .compile-time-value;
            return primitive($value) ?? constant($value) !! known($value.WHAT, :definite(+concrete($value)), :exact);
        }
        when RakuAST::Statement::IfWith {
            my $*STATIC-CONDITIONAL = True;
            self!infer(.condition, %env);
            my @states;
            my @values;
            my %remaining = clone-env(%env);
            sub arm($branch) {
                my %branch = clone-env(%remaining);
                my $value = self!infer($branch, %branch, :immediate);
                @values.push($value);
                @states.push(%branch) unless $value.bottom;
            }
            arm(.then);
            for .elsifs -> $elsif {
                self!infer($elsif.condition, %remaining);
                arm($elsif.then);
            }
            arm(.else);
            join-env(%env, |@states) if @states;
            return merge(|@values);
        }
        when RakuAST::Statement::Unless | RakuAST::Statement::Without {
            my $*STATIC-CONDITIONAL = True;
            self!infer(.condition, %env);
            my %before = clone-env(%env);
            my %branch = clone-env(%env);
            my $value = self!infer(.body, %branch, :immediate);
            join-env(%env, %before, %branch) unless $value.bottom;
            return merge($value, known(Nil, :definite(0)));
        }
        when RakuAST::Ternary {
            my $*STATIC-CONDITIONAL = True;
            self!infer(.condition, %env);
            my %yes = clone-env(%env);
            my %no = clone-env(%env);
            my $yes = self!infer(.then, %yes, :immediate);
            my $no = self!infer(.else, %no, :immediate);
            join-env(%env, |($yes.bottom ?? () !! (%yes,)), |($no.bottom ?? () !! (%no,)));
            return merge($yes, $no);
        }
        when RakuAST::Statement::Loop | RakuAST::Statement::For {
            return self!loop($_, %env);
        }
        when RakuAST::ApplyInfix {
            my $left = self!infer(.left, %env);
            if .infix ~~ RakuAST::Infix && .infix.operator eq any('&&', '||', '//', 'and', 'or', 'orelse') {
                my $*STATIC-CONDITIONAL = True;
                my %before = clone-env(%env);
                my %rhs = clone-env(%env);
                my $right = self!infer(.right, %rhs);
                join-env(%env, %before, %rhs) unless $right.bottom;
                return self!operator(.infix, [$left, $right], $_);
            }
            my $right = self!infer(.right, %env);
            if .infix ~~ RakuAST::Assignment || (.infix ~~ RakuAST::Infix && .infix.operator eq ':=') {
                self!write(.left, $right, %env, $_);
                return $right;
            }
            if .infix ~~ RakuAST::MetaInfix::Assign {
                my $value = self!operator(.infix.infix, [$left, $right], $_);
                self!write(.left, $value, %env, $_);
                return $value;
            }
            return self!operator(.infix, [$left, $right], $_);
        }
        when RakuAST::ApplyListInfix {
            my @facts = .operands.map({ self!infer($_, %env) });
            if .infix ~~ RakuAST::Infix && .infix.operator eq ',' {
                return Fact.new(:type(List), :definite(1), :exact, :sequence, :finite, :items(@facts), :element(merge(|@facts)));
            }
            return self!operator(.infix, @facts, $_);
        }
        when RakuAST::ApplyPrefix {
            my $value = self!infer(.operand, %env);
            my $result = self!operator(.prefix, [$value], $_);
            self!write(.operand, $result, %env, $_)
                if .prefix ~~ RakuAST::Prefix && .prefix.operator eq any(<++ -->);
            return $result;
        }
        when RakuAST::ApplyPostfix {
            my $value = self!infer(.operand, %env);
            return self!postfix($_, $value, %env);
        }
        when RakuAST::Call::Name { return self!call($_, %env) }
        when RakuAST::Call::Term {
            self!infer($_, %env) for children($_);
            self!report($_, 'unverifiable', 'indirect call', :reason('call target is not statically resolved'));
            return unknown('indirect call');
        }
        when RakuAST::Circumfix::Parentheses { return self!infer(.semilist, %env) }
        when RakuAST::Circumfix::ArrayComposer {
            my @facts = self!list-items(.semilist).map({ self!infer($_, %env) });
            return Fact.new(:type(Array), :definite(1), :exact, :sequence, :finite, :identity(id($_)), :items(@facts), :element(merge(|@facts)));
        }
        when RakuAST::FatArrow | RakuAST::ColonPair {
            self!infer(.value, %env) if .^can('value');
            return known(Pair, :definite(1));
        }
        when RakuAST::StatementPrefix::Phaser {
            # The invocation of this checker is a compiler directive. Other
            # phaser statements are checked in their own evaluation context.
            self!infer(.blorst, %env, :immediate);
            return known(Nil, :definite(0));
        }
        when RakuAST::StatementPrefix::Try {
            my %before = clone-env(%env);
            my %body = clone-env(%env);
            my $value = self!infer(.blorst, %body, :immediate);
            self!forget-changed(%before, %body);
            join-env(%env, %before, %body);
            return merge($value, known(Any, :definite(0), :exact));
        }
        when RakuAST::StatementPrefix::Gather | RakuAST::StatementPrefix::Supply
            | RakuAST::StatementPrefix::Start {
            return self!producer($_, %env);
        }
        when RakuAST::StatementPrefix::Do | RakuAST::StatementPrefix::Quietly {
            return self!infer(.blorst, %env, :immediate);
        }
        when RakuAST::Statement::Use | RakuAST::Statement::Need | RakuAST::Statement::Import
            | RakuAST::Statement::LanguageVersion | RakuAST::Statement::Empty {
            return known(Nil, :definite(0));
        }
        default {
            self!infer($_, %env) for children($_);
            self!report($node, 'unverifiable', 'unsupported ' ~ $node.^name,
                :reason('no static rule for this AST construct'));
            return unknown('unsupported ' ~ $node.^name);
        }
    }
}

method !loop($node, %env --> Fact) {
    my $*STATIC-CONDITIONAL = True;
    self!infer($node.setup, %env) if $node.^can('setup');
    self!infer($node.source, %env) if $node.^can('source');
    my %initial = clone-env(%env);
    for ^16 {
        my $before = %env.keys.sort.map({ $_ ~ '=' ~ %env{$_}.key }).join('|');
        my %body = clone-env(%env);
        self!infer($node.condition, %body) if $node.^can('condition');
        self!infer($node.body, %body, :immediate);
        self!infer($node.increment, %body) if $node.^can('increment');
        join-env(%env, %initial, %body);
        # Widen changing constants to their nominal types. Retaining one more
        # literal per iteration would pretend that a bounded analysis had
        # enumerated all values of an unbounded loop.
        for %env.keys -> $key {
            next unless %initial{$key}:exists;
            next if %env{$key}.key eq %initial{$key}.key;
            my @alts = %env{$key}.alternatives ?? %env{$key}.alternatives.List !! (%env{$key},);
            %env{$key} = merge(|@alts.map({ .reason ?? $_ !! known(.type, :definite(.definite)) }));
        }
        last if $before eq %env.keys.sort.map({ $_ ~ '=' ~ %env{$_}.key }).join('|');
    }
    # Loop results depend on iteration count and gather context.
    unknown('loop result depends on runtime iteration')
}

method !collection-init($decl, $expression, Fact $value, Fact $contract, %env) {
    return if same($value.type, Nil);
    my Mu $expected = $contract.element.type;
    if $decl.sigil eq '@' {
        if $contract.shape { self!shaped-init($decl, $value, $contract.shape, $expected); return }
        if $value.finite {
            self!check($decl, $_, $expected, 'array element initialization') for $value.items;
        }
        elsif $value.sequence {
            self!check($decl, concrete($value.element) ?? $value.element !! unknown('unknown element type'),
                $expected, 'array element initialization');
        }
        else { self!check($decl, $value, $expected, 'array element initialization') }
    }
    else {
        for self!list-items($expression) -> $item {
            if $item ~~ RakuAST::FatArrow || ($item ~~ RakuAST::ColonPair && $item.^can('value')) {
                self!check($item, self!infer($item.value, %env), $expected, 'hash value initialization');
                self!check($item, constant($item.key), $contract.key-type, 'hash key initialization');
            }
            elsif $item ~~ RakuAST::ApplyInfix && $item.infix ~~ RakuAST::Infix && $item.infix.operator eq '=>' {
                self!check($item, self!infer($item.left, %env), $contract.key-type, 'hash key initialization');
                self!check($item, self!infer($item.right, %env), $expected, 'hash value initialization');
            }
            else {
                self!report($decl, 'unverifiable', 'hash initialization', :reason('hash values are not statically enumerable'));
            }
        }
    }
}

method !operator($operator, @facts, $site --> Fact) {
    if $operator ~~ RakuAST::MetaInfix::Hyper || $operator ~~ RakuAST::MetaPrefix::Hyper {
        return self!hyper-operator($operator, @facts, $site);
    }
    my $name = $operator.^can('operator') ?? $operator.operator !! '';
    # These semantic rules apply only to the CORE operator, never overloads.
    my $core = $operator ~~ RakuAST::Lookup && $operator.is-resolved
        && $operator.resolution ~~ RakuAST::Declaration::External::Setting;
    if $core {
        my $folded = operation($name, @facts);
        return $folded if $folded.has-value;
        return known(Str, :definite(1)) if $name eq '~';
        return known(Bool, :definite(1)) if $name eq any(<== != < > <= >= eq ne lt gt le ge === ! ? so not ~~ !~~>);
        return merge(|@facts) if $name eq any('&&', '||', '//', 'and', 'or', 'orelse');
        if $name eq any(<+ - * / **>) {
            my @types = @facts.map(*.type);
            if @facts && @facts.grep({ .reason || !nqp::istype(nominal(.type), Numeric) }).elems == 0 {
                my Mu $result = Numeric;
                if @types.grep({ !nqp::istype(nominal($_), Real) }).elems == 0 {
                    $result = Real;
                    if @types.grep({ nqp::istype(nominal($_), Num) }) { $result = Num }
                    elsif @types.grep({ !nqp::istype(nominal($_), Rat) && !nqp::istype(nominal($_), Int) }).elems == 0 {
                        $result = @types.grep({ nqp::istype(nominal($_), FatRat) }) ?? FatRat
                            !! $name eq '/' || @types.grep({ nqp::istype(nominal($_), Rat) }) ?? Rat !! Int;
                    }
                    $result = Real if $name eq '**';
                }
                elsif @types.grep({ nqp::istype(nominal($_), Complex) }) { $result = Complex }
                return known($result, :definite(1));
            }
        }
    }
    return self!dispatch($operator.resolution.compile-time-value, @facts, {}, $site,
        'operator ' ~ $name) if $operator ~~ RakuAST::Lookup && $operator.is-resolved
            && $operator.resolution.^can('compile-time-value');
    self!report($site, 'unverifiable', 'operator ' ~ $name, :reason('operator semantics unavailable'));
    unknown('unresolved operator ' ~ $name)
}

method !arguments($args, %env --> List) {
    my @pos;
    my %named;
    my $uncertain = False;
    for $args.args -> $arg {
        if $arg ~~ RakuAST::FatArrow || $arg ~~ RakuAST::ColonPair {
            my $value = $arg.^can('value') ?? self!argument($arg.value, %env) !! known(Bool, :definite(1));
            %named{$arg.key} = $value;
        }
        elsif $arg ~~ RakuAST::ApplyPrefix && $arg.prefix ~~ RakuAST::Prefix && $arg.prefix.operator eq '|' {
            my $spread = self!infer($arg.operand, %env);
            if $spread.finite && $spread.sequence { @pos.append($spread.items) }
            else { $uncertain = True }
        }
        else {
            my $value = self!argument($arg, %env);
            @pos.push($value);
        }
    }
    (@pos.Array, %named.Hash, $uncertain).List
}

method !call($node, %env --> Fact) {
    my $name = $node.name.canonicalize;
    # Avoid treating the checker's own CHECK-time entry point as runtime code.
    if $node.is-resolved && $node.resolution.^can('compile-time-value') {
        my Mu $routine = $node.resolution.compile-time-value;
        if $routine ~~ Routine && $routine.package.^name eq 'static'
            && $name eq any(<warn-on-mismatch fail-on-mismatch warn-on-unverifiable fail-on-unverifiable>) {
            return known(List, :definite(1));
        }
    }
    my (@pos, %named, $uncertain) := self!arguments($node.args, %env);
    my $core = $node.is-resolved && $node.resolution ~~ RakuAST::Declaration::External::Setting;
    if $core && $name eq any(<take take-rw emit>) {
        my $value = @pos == 1 ?? @pos[0] !! unknown('yield argument count');
        if ($name eq 'emit' && $*STATIC-YIELD-KIND eq 'supply')
            || ($name ne 'emit' && $*STATIC-YIELD-KIND eq 'gather') {
            @*STATIC-YIELDS.push($value);
            return known(Nil, :definite(0));
        }
        self!report($node, 'unverifiable', 'call to ' ~ $name,
            :reason('yield target is outside the statically known producer'));
        return unknown('dynamic yield target');
    }
    if $core && $name eq 'await' && @pos == 1 && @pos[0].payload.defined {
        return @pos[0].payload;
    }
    if $core && $name eq any(<return return-rw>) {
        my $value = @pos == 0 ?? known(Nil, :definite(0)) !! @pos == 1 ?? @pos[0]
            !! Fact.new(:type(List), :definite(1), :sequence, :finite, :items(@pos));
        @*STATIC-RETURNS.push($value);
        return bottom;
    }
    return bottom if $core && $name eq any(<die exit>);
    if !$node.is-resolved || !$node.resolution.^can('compile-time-value') {
        self!report($node, 'unverifiable', 'call to ' ~ $name, :reason('routine not statically resolved'));
        return unknown('unresolved call to ' ~ $name);
    }
    my $result = self!dispatch($node.resolution.compile-time-value, @pos, %named, $node, 'call to ' ~ $name, :$uncertain);
    self!effects($node.resolution.compile-time-value, %env, $node.args);
    $result
}

method !parameter-relation(Fact $actual, Parameter $param --> Str) {
    if $param.rw {
        return 'mismatch' if $actual.writable == 0;
        return 'unverifiable' if $actual.writable < 0;
    }
    if $actual.alternatives {
        my @results = $actual.alternatives.map({ self!parameter-relation($_.clone(:writable($actual.writable)), $param) }).unique;
        return @results == 1 ?? @results[0] !! 'unverifiable';
    }
    for $param.type_captures -> $name { %*STATIC-TYPES{$name} = $actual }
    my $runtime-capture = $param.type_captures.elems && !$actual.exact;
    my Mu $expected := $param.type;
    if $expected.^archetypes.generic && (%*STATIC-TYPES{$expected.^name}:exists) {
        $runtime-capture = True unless %*STATIC-TYPES{$expected.^name}.exact;
        $expected := %*STATIC-TYPES{$expected.^name}.type;
    }
    my $status = self!relation($actual, $expected);
    return $status unless $status eq 'ok';
    if $param.modifier && !$actual.bottom {
        return 'unverifiable' if $actual.definite < 0;
        return 'mismatch' if $actual.definite != ($param.modifier eq ':D' ?? 1 !! 0);
    }
    my $nested = 'ok';
    if $param.sub_signature.defined {
        $nested = $actual.finite ?? self!match($param.sub_signature, $actual.items.Array, {}) !! 'unverifiable';
        return $nested unless $nested eq 'ok';
    }
    if $param.constraint_list.elems {
        my $ast = %!parameter-asts{id($param)};
        return self!predicate($ast.where, $actual, :name($param.name)) if $ast.defined && concrete($ast.where);
        my @statuses;
        for $param.constraint_list -> Mu $constraint {
            @statuses.push($constraint.HOW.^name.ends-with('SubsetHOW')
                ?? self!relation($actual, $constraint) !! 'unverifiable');
        }
        return 'mismatch' if @statuses.grep(* eq 'mismatch');
        return @statuses.grep(* eq 'unverifiable') ?? 'unverifiable' !! 'ok';
    }
    $runtime-capture ?? 'unverifiable' !! 'ok'
}

method !match(Signature $signature, @pos, %named, Fact :$invocant --> Str) {
    my @status;
    my $position = 0;
    my %used;
    my $named-slurpy = False;
    for $signature.params -> $param {
        if $param.invocant {
            @status.push(self!parameter-relation($invocant, $param)) if $invocant.defined;
            next;
        }
        if $param.capture {
            @status.push('unverifiable') if $param.sub_signature.defined || $param.signature_constraint.defined || $param.constraint_list.elems;
            $position = @pos.elems; $named-slurpy = True; next;
        }
        if $param.named {
            if $param.slurpy {
                $named-slurpy = True;
                @status.push('unverifiable') if $param.constraint_list.elems || $param.sub_signature.defined || $param.rw;
                next;
            }
            my @names = $param.named_names;
            my $alias = @names.first({ %named{$_}:exists });
            if $alias.defined {
                %used{$alias} = True;
                @status.push(self!parameter-relation(%named{$alias}, $param));
                # Sub-signatures and rw are checked by parameter-relation.
            }
            elsif !$param.optional { return 'mismatch' }
        }
        elsif $param.slurpy {
            my Mu $element = nqp::istype($param.type, Positional) ?? $param.type.of !! Mu;
            @status.push(self!relation($_, $element)) for @pos[$position ..^ @pos.elems];
            @status.push('unverifiable') if $param.constraint_list.elems || $param.sub_signature.defined || $param.rw;
            $position = @pos.elems;
        }
        elsif $position < @pos.elems {
            @status.push(self!parameter-relation(@pos[$position++], $param));
            # Sub-signatures and rw are checked by parameter-relation.
        }
        elsif !$param.optional { return 'mismatch' }
    }
    return 'mismatch' if $position < @pos.elems || (!$named-slurpy && %named.keys.grep({ !%used{$_} }).elems);
    return 'mismatch' if @status.grep(* eq 'mismatch');
    return 'unverifiable' if @status.grep(* eq 'unverifiable');
    'ok'
}

method !dispatch(Mu $routine, @pos, %named, $site, Str $context, Bool :$uncertain = False,
    Fact :$known-return, Fact :$invocant --> Fact) {
    unless $routine ~~ Routine {
        self!report($site, 'unverifiable', $context, :reason('callable signature unavailable'));
        return unknown('callable signature unavailable');
    }
    my @candidates = $routine.candidates;
    my @possible;
    my @viable;
    my @viable-status;
    my @statuses;
    my @signatures;
    for @candidates -> $candidate {
        my %*STATIC-TYPES;
        my $local = %!locals{id($candidate)}:exists;
        if !$local && !$!external-signatures {
            @possible.push(unknown('external signatures disabled'));
            @viable.push(Mu); @viable-status.push('unverifiable');
            @statuses.push('unverifiable');
            next;
        }
        my $signature = $candidate.signature;
        @signatures.push($signature.raku);
        my $status = $uncertain ?? 'unverifiable' !! self!match($signature, @pos, %named, :$invocant);
        @statuses.push($status);
        next if $status eq 'mismatch';
        @viable.push($candidate); @viable-status.push($status);
        if $local {
            my $ast = %!locals{id($candidate)};
            @possible.push(self!specialize(self!has-return-contract($ast) ?? known($signature.returns) !! %!summaries{id($ast)}, %*STATIC-TYPES));
        }
        else {
            my Mu $returns = $signature.returns;
            @possible.push(self!specialize($known-return.defined ?? $known-return
                !! same($returns, Mu) ?? unknown('external routine has no return contract') !! known($returns), %*STATIC-TYPES));
        }
    }
    if @possible > 1 {
        my @keep = (^@possible.elems).grep(-> $i {
            !(^@possible.elems).grep(-> $j {
                $i != $j && @viable[$i].defined && @viable[$j].defined
                    && @viable-status[$j] eq 'ok'
                    && self!more-specific(@viable[$j].signature, @viable[$i].signature)
            }).elems
        });
        @possible = @possible[@keep];
        @statuses = @viable-status[@keep];
    }
    if !@possible {
        self!report($site, 'mismatch', $context, :expected(@signatures.join(' or ')),
            :actual('(' ~ @pos.map(*.label).join(', ') ~ (%named ?? '; ' ~ %named.keys.sort.join(', ') !! '') ~ ')'));
        return unknown('no compatible dispatch candidate');
    }
    if $uncertain || @statuses.grep(* eq 'unverifiable') {
        self!report($site, 'unverifiable', $context, :reason($uncertain ?? 'arguments or runtime call target are not fully known'
            !! 'signature compatibility or dispatch depends on runtime values'));
    }
    self!report($site, 'unverifiable', $context, :reason('multiple equally applicable dispatch candidates'))
        if @possible > 1;
    my $result = merge(|@possible);
    self!report($site, 'unverifiable', $context, :reason($result.reason)) if $result.reason;
    $result
}

method !more-specific(Signature $a, Signature $b --> Bool) {
    my @a = $a.params; my @b = $b.params;
    return False unless @a.elems == @b.elems;
    my $strict = False;
    for @a Z @b -> ($x, $y) {
        return False if $x.slurpy || $y.slurpy || $x.capture || $y.capture;
        return False unless $x.named == $y.named && $x.optional == $y.optional
            && $x.invocant == $y.invocant && $x.named_names.raku eq $y.named_names.raku;
        return False if $x.type.^archetypes.generic || $y.type.^archetypes.generic;
        return False unless nqp::istype(nominal($x.type), nominal($y.type));
        return False if $y.modifier && $x.modifier ne $y.modifier;
        return False if $y.constraint_list.elems && !$x.constraint_list.elems;
        $strict = True if !same($x.type, $y.type) || ($x.modifier && !$y.modifier)
            || ($x.constraint_list.elems && !$y.constraint_list.elems);
    }
    $strict
}

method !specialize(Fact $fact, %types --> Fact) {
    return merge(|$fact.alternatives.map({ self!specialize($_, %types) })) if $fact.alternatives;
    if $fact.type.^archetypes.generic {
        if (%types{$fact.type.^name}:exists) && !%types{$fact.type.^name}.exact {
            return Fact.new(:type(%types{$fact.type.^name}.type), :reason('generic capture depends on runtime subtype'));
        }
        return %types{$fact.type.^name}:exists ?? known(%types{$fact.type.^name}.type,
            :definite($fact.definite)) !! unknown('generic return contract is not fully resolved');
    }
    $fact
}

method !postfix($node, Fact $invocant, %env, $postfix = $node.postfix --> Fact) {
    if $postfix ~~ RakuAST::MetaPostfix::Hyper {
        unless $invocant.sequence {
            self!report($node, 'unverifiable', 'hyper postfix', :reason('hyper operand is not statically enumerable'));
            return unknown('hyper operand unavailable');
        }
        my @values = $invocant.finite ?? $invocant.items.List
            !! (concrete($invocant.element) ?? ($invocant.element,) !! (unknown('hyper element unavailable'),));
        my @results = @values.map({ self!postfix($node, $_, %env, $postfix.postfix) });
        return Fact.new(:type(List), :definite(1), :sequence, :finite($invocant.finite),
            :items($invocant.finite ?? @results !! []), :element(merge(|@results)));
    }
    if $invocant.payload.defined && $postfix ~~ RakuAST::Call::Method
        && ((same($invocant.type, Promise) && $postfix.name.canonicalize eq 'result')
            || (same($invocant.type, Seq) && $postfix.name.canonicalize eq 'head')) && !$postfix.args.args {
        return $invocant.payload;
    }
    if same($invocant.type, Supply) && $invocant.payload.defined
        && $postfix ~~ RakuAST::Call::Method && $postfix.name.canonicalize eq 'tap' {
        my @args = $postfix.args.args;
        if @args == 1 && @args[0] ~~ RakuAST::Block {
            self!producer($node, %env, @args[0], :kind-override<callback>);
            my $status = self!match(@args[0].meta-object.signature, [$invocant.payload], {});
            self!report($node, $status, 'supply callback', :actual($invocant.payload.label),
                :expected(@args[0].meta-object.signature.raku)) unless $status eq 'ok';
            return known(Tap, :definite(1));
        }
    }
    if $postfix ~~ RakuAST::Call::Method || $postfix ~~ RakuAST::Call::PrivateMethod {
        my $name = $postfix.name.canonicalize;
        if $invocant.sequence && $name eq 'head' && !$postfix.args.args {
            return $invocant.finite
                ?? ($invocant.items ?? $invocant.items[0] !! known(Nil, :definite(0)))
                !! (concrete($invocant.element) ?? merge($invocant.element, known(Nil, :definite(0))) !! unknown('sequence element unavailable'));
        }
        if $invocant.has-value && primitive($invocant.value) && !$postfix.args.args {
            return constant($invocant.value.chars) if $name eq 'chars' && same($invocant.type, Str);
            return constant($invocant.value.Str) if $name eq 'Str';
        }
        my (@pos, %named, $uncertain) := self!arguments($postfix.args, %env);
        my Mu $type = nominal($invocant.type);
        if $invocant.shape && $name eq any(<push append unshift prepend pop shift splice>) {
            self!report($node, 'mismatch', 'array shape mutation',
                :reason('cannot ' ~ $name ~ ' a fixed-dimension array'));
            return unknown('invalid fixed-dimension mutation');
        }
        if $name eq any(<push append unshift prepend>) && concrete($invocant.element) {
            for @pos -> $value {
                if $value.finite && $name eq any(<append prepend>) {
                    self!check($node, $_, $invocant.constrained-elements ?? $invocant.element.type !! Mu, 'collection ' ~ $name) for $value.items;
                }
                else { self!check($node, $value, $invocant.constrained-elements ?? $invocant.element.type !! Mu, 'collection ' ~ $name) }
            }
            self!invalidate($node.operand, %env);
            return unknown('collection mutation result is not modeled');
        }
        if $invocant.reason || same($type, Mu) || same($type, Any) {
            self!report($node, 'unverifiable', 'method ' ~ $name, :reason('invocant type is not sufficiently known'));
            return unknown('unresolved method ' ~ $name);
        }
        if $type.^archetypes.generic || $type.HOW.^name.contains('Role') {
            self!report($node, 'unverifiable', 'method ' ~ $name, :reason('generic or role invocant requires runtime composition'));
            return unknown('runtime role or generic method lookup');
        }
        my Mu $method = $postfix ~~ RakuAST::Call::PrivateMethod
            ?? $type.HOW.private_method_table($type){$name}
            !! $type.HOW.find_method($type, $name);
        if !concrete($method) {
            # Optional dispatch and FALLBACK may handle a missing public method.
            my $private = $postfix ~~ RakuAST::Call::PrivateMethod;
            my $dispatch = $private ?? '' !! $postfix.dispatch;
            my $fallback = !$private && concrete($type.HOW.find_method($type, 'FALLBACK'));
            my $optional = $dispatch eq any('.?', '.*');
            my $missing = $invocant.exact && !$fallback && !$optional && !$name.contains('::');
            if $!check-methods {
                self!report($node, $missing ?? 'mismatch' !! 'unverifiable', 'method ' ~ $name,
                    :reason($missing
                        ?? 'method does not exist on ' ~ $type.^name
                        !! 'method lookup requires runtime dispatch'));
            }
            return unknown('unresolved method ' ~ $name);
        }
        # No-argument CORE pick/roll select one element without executing the
        # random selection during analysis. Restrict this rule to exact built-in
        # containers so custom pick/roll/list implementations retain normal dispatch.
        if $name eq any(<pick roll>) && $postfix ~~ RakuAST::Call::Method
            && $postfix.dispatch eq '' && !$postfix.args.args
            && $invocant.exact && $invocant.sequence
            && (same($type, List) || same($type, Array))
            && same($method, List.HOW.find_method(List, $name)) {
            return $invocant.finite
                ?? ($invocant.items ?? merge(|$invocant.items) !! known(Nil, :definite(0)))
                !! (concrete($invocant.element)
                    ?? merge($invocant.element, known(Nil, :definite(0)))
                    !! unknown('collection element type unavailable'));
        }
        # CORE Mu.new/bless return the invocant class; a custom constructor
        # remains governed by its own body/return contract.
        my $constructor = $name eq any(<new bless>) && $method.package.^name eq 'Mu';
        if $constructor {
            for $type.^attributes -> $attribute {
                my $key = $attribute.name.substr(2);
                self!check($node, %named{$key}, $attribute.type, 'constructor attribute ' ~ $key)
                    if %named{$key}:exists;
            }
        }
        my $virtual = !$invocant.exact && !$constructor && $postfix !~~ RakuAST::Call::PrivateMethod;
        my $result = self!dispatch($method, @pos, %named, $node, 'method ' ~ $name,
            :uncertain($uncertain || $virtual), :$invocant,
            :known-return($constructor ?? known($type, :definite(1), :exact($invocant.exact)) !! Fact));
        self!effects($method, %env, $postfix.args);
        self!invalidate($node.operand, %env) if concrete($invocant.element)
            && !($name eq any(<elems end of keyof Bool defined item list hash keys values pairs head tail>));
        return merge($result, unknown('runtime subclass may override method ' ~ $name)) if $virtual;
        return $result;
    }
    if $postfix ~~ RakuAST::Postcircumfix::Index || $postfix ~~ RakuAST::Postcircumfix::LiteralHashIndex {
        self!infer($_, %env) for children($postfix).grep({ !($postfix.^can('assignee') && same($_, $postfix.assignee)) });
        my $element = concrete($invocant.element) ?? $invocant.element !! unknown('collection element type unavailable');
        if $postfix.^can('assignee') && concrete($postfix.assignee) {
            my $value = self!infer($postfix.assignee, %env);
            self!check($node, $value, $invocant.constrained-elements ?? $element.type !! Mu, 'indexed assignment');
            self!index-key($postfix, $invocant, %env);
            self!invalidate($node.operand, %env);
            return $value;
        }
        self!index-key($postfix, $invocant, %env);
        if $postfix ~~ RakuAST::Postcircumfix::ArrayIndex && $invocant.finite {
            my $index = self!infer($postfix.index, %env);
            if $index.has-value && $index.value ~~ Int && $index.value >= 0 {
                return $index.value < $invocant.items.elems ?? $invocant.items[$index.value] !! known(Any, :definite(0), :exact);
            }
        }
        return merge($element, known($invocant.constrained-elements ?? $element.type !! Any, :definite(0)));
    }
    if $postfix ~~ RakuAST::Postfix && $postfix.operator eq any(<++ -->) {
        my $result = self!operator($postfix, [$invocant], $node);
        self!write($node.operand, $result, %env, $node);
        return $invocant;
    }
    self!infer($_, %env) for children($postfix);
    self!report($node, 'unverifiable', 'postfix ' ~ $postfix.^name, :reason('unsupported postfix operation'));
    unknown('unsupported postfix operation')
}

# Retain types while discarding values that can be stale on exceptional paths.
method !forget-changed(%before, %after) {
    for %before.keys -> $key {
        next unless (%after{$key}:exists) && %before{$key}.key ne %after{$key}.key;
        %before{$key} = unknown('value may have changed before exceptional exit');
    }
}

method !statements($list, %env --> Fact) {
    my @handlers = $list.code-statements.grep(* ~~ RakuAST::Statement::ExceptionHandler);
    return self!infer($list, %env) unless @handlers;
    my %before = clone-env(%env);
    my $value = self!infer($list, %env);
    self!forget-changed(%before, %env);
    my @states = %env.Hash,;
    my @values = $value,;
    for @handlers -> $handler {
        my %branch = clone-env(%before);
        my Fact $*STATIC-TOPIC = known(Exception, :definite(1));
        my $handled = self!given($handler.body.body.statement-list, %branch);
        @states.push(%branch) unless $handled.bottom;
        # A handled exception exits its block with Nil, not the handler value.
        @values.push(known(Nil, :definite(0))) unless $handled.bottom;
    }
    join-env(%env, |@states);
    merge(|@values)
}

method !given($list, %env --> Fact) {
    my $*STATIC-CONDITIONAL = True;
    my %remaining = clone-env(%env);
    my @states;
    my @values;
    my $exhaustive = False;
    my $fallthrough = known(Nil, :definite(0));
    for $list.code-statements -> $statement {
        if $statement ~~ RakuAST::Statement::When || $statement ~~ RakuAST::Statement::Default {
            my $status = 'ok';
            if $statement ~~ RakuAST::Statement::When {
                my $condition = self!infer($statement.condition, %remaining);
                if $statement.condition ~~ RakuAST::Type {
                    $status = self!relation($*STATIC-TOPIC, ast-type($statement.condition));
                }
                elsif $condition.has-value && same($condition.type, Bool) {
                    $status = $condition.value ?? 'ok' !! 'mismatch';
                }
                elsif $condition.has-value && $*STATIC-TOPIC.has-value && same($condition.type, $*STATIC-TOPIC.type) {
                    my $equal = operation('eq', [$condition, $*STATIC-TOPIC]);
                    $status = $equal.has-value ?? ($equal.value ?? 'ok' !! 'mismatch') !! 'unverifiable';
                }
                else {
                    $status = 'unverifiable';
                    self!report($statement, 'unverifiable', 'when condition',
                        :reason('smartmatch condition depends on runtime semantics'));
                }
            }
            next if $status eq 'mismatch';
            my %branch = clone-env(%remaining);
            my $value = self!infer($statement.body, %branch, :immediate);
            @values.push($value);
            @states.push(%branch) unless $value.bottom;
            if $status eq 'ok' { $exhaustive = True; last }
        }
        else {
            my $value = self!infer($statement, %remaining);
            if $value.bottom { $exhaustive = True; @values.push($value); last }
            # Ordinary statements before/between when arms execute normally.
            $fallthrough = $value;
        }
    }
    unless $exhaustive {
        @states.push(%remaining);
        @values.push($fallthrough);
    }
    join-env(%env, |@states) if @states;
    merge(|@values)
}

method !producer($node, %env, $body = $node.blorst, Str :$kind-override = '' --> Fact) {
    my $kind = $kind-override || ($node ~~ RakuAST::StatementPrefix::Gather ?? 'gather'
        !! $node ~~ RakuAST::StatementPrefix::Supply ?? 'supply' !! 'start');
    my $*STATIC-YIELD-KIND = $kind;
    my @*STATIC-YIELDS;
    my @*STATIC-RETURNS;
    my Mu $*STATIC-ROUTINE = $node;
    my %*STATIC-WRITTEN;
    my %branch = clone-env(%env);
    # The caller may mutate captures before a deferred body runs. Trust the
    # container's declared contract, never its current scalar/element values.
    for %branch.keys -> $key {
        next if (%!binding-writable{$key}:exists) && %!binding-writable{$key} == 0;
        %branch{$key} = (%!declarations{$key}:exists) ?? self!declared(%!declarations{$key})
            !! unknown('mutable capture at deferred execution');
    }
    my $result = self!infer($body, %branch, :immediate);
    # Deferred/concurrent writes must not establish facts in the caller.
    for %env.keys -> $key {
        if %*STATIC-WRITTEN{$key} {
            %!deferred-writes{$key} = True;
            %env{$key} = unknown('value may be modified by deferred or concurrent code');
        }
    }
    my $payload = $kind eq 'start' ?? merge($result, |@*STATIC-RETURNS)
        !! @*STATIC-YIELDS ?? merge(|@*STATIC-YIELDS) !! unknown('producer element type unavailable');
    # Recent Rakudo lowers a single emit to the supplied expression itself.
    if $kind eq 'supply' && !@*STATIC-YIELDS
        && nqp::can($node, 'IMPL-LOWER-ONE-EMIT')
        && nqp::getattr_i(nqp::decont($node), RakuAST::StatementPrefix::Supply, '$!one-emit') {
        $payload = $result;
    }
    return Fact.new(:type(Promise), :definite(1), :exact, :$payload) if $kind eq 'start';
    return Fact.new(:type(Supply), :definite(1), :exact, :$payload) if $kind eq 'supply';
    Fact.new(:type(Seq), :definite(1), :exact, :sequence, :element($payload), :$payload)
}

method !argument($node, %env --> Fact) {
    if $node ~~ RakuAST::Circumfix::Parentheses {
        my @statements = $node.semilist.code-statements;
        if @statements == 1 && @statements[0] ~~ RakuAST::Statement::Expression {
            my $inner = @statements[0].expression;
            # A trailing comma constructs a List; it does not preserve the
            # writable identity of its single element.
            return self!argument($inner, %env) unless $inner ~~ RakuAST::ApplyListInfix;
        }
    }
    my $value = self!infer($node, %env);
    my $writable = 0;
    if $node ~~ RakuAST::Var::Lexical && $node.is-resolved {
        my $decl = self!root($node.resolution);
        $writable = $decl ~~ RakuAST::VarDeclaration::Simple && $decl.sigil eq any('@', '%') ?? 0
            !! $decl ~~ RakuAST::VarDeclaration::Constant ?? 0
            !! %!ambiguous-aliases{id($node.resolution)} ?? -1
            !! (%!binding-writable{id($decl)}:exists) ?? %!binding-writable{id($decl)}
            !! (%!parameter-rw{id($decl)}:exists) ?? %!parameter-rw{id($decl)} !! 1;
    }
    elsif $node ~~ RakuAST::ApplyPostfix && $node.postfix ~~ RakuAST::Postcircumfix::Index {
        $writable = -1; # proxy/custom indexing is not necessarily writable
        if $node.operand ~~ RakuAST::Var::Lexical && $node.operand.is-resolved {
            my $container = self!infer($node.operand, %env);
            $writable = 1 if concrete($container.element) && !$container.reason;
        }
    }
    elsif $node ~~ RakuAST::Var::Attribute { $writable = 1 }
    elsif $node ~~ RakuAST::Call || $node ~~ RakuAST::ApplyPostfix { $writable = -1 }
    $value.clone(:$writable)
}

method !destructure($node, %env --> Fact) {
    return known(Nil, :definite(0)) unless concrete($node.initializer);
    unless $node.initializer ~~ RakuAST::Initializer::Expression {
        self!report($node, 'unverifiable', 'destructuring', :reason('initializer form unavailable'));
        return unknown('destructuring initializer');
    }
    my $value = self!infer($node.initializer.expression, %env);
    if $node.signature.parameters.grep({ .meta-object.named || .meta-object.capture }) {
        self!report($node, 'unverifiable', 'destructuring', :reason('named or capture declaration binding is not statically resolved'));
        return unknown('named destructuring');
    }
    my @values = $value.finite ?? $value.items.List !! $value.sequence ?? () !! ($value,);
    unless !$value.sequence || $value.finite {
        self!report($node, 'unverifiable', 'destructuring', :reason('source length is not statically known'));
        return unknown('destructuring source length');
    }
    my @sources = self!list-items($node.initializer.expression);
    my $position = 0;
    for $node.signature.parameters -> $parameter {
        my $param = $parameter.meta-object;
        unless $parameter.target ~~ RakuAST::ParameterTarget::Var {
            self!report($node, 'unverifiable', 'destructuring', :reason('nested declaration target unavailable'));
            next;
        }
        my $decl = $parameter.target.declaration;
        my $actual;
        if $param.slurpy {
            my @rest = @values[$position ..^ @values.elems];
            $actual = Fact.new(:type(Array), :definite(1), :sequence, :finite,
                :items(@rest), :element(merge(|@rest)));
            self!check($node, $_, $param.type.of, 'destructuring element') for @rest;
            $position = @values.elems;
        }
        else {
            $actual = $position < @values.elems ?? @values[$position]
                !! concrete($parameter.default) ?? self!infer($parameter.default, %env)
                !! known($param.type, :definite(0));
            my $status = self!parameter-relation($actual.clone(:writable(1)), $param);
            self!report($node, $status, 'destructuring ' ~ $param.name,
                :expected($param.type.^name), :actual($actual.label)) unless $status eq 'ok';
            if $node.initializer.is-binding {
                my $source = @sources[$position];
                if $source ~~ RakuAST::Var::Lexical && $source.is-resolved {
                    %!aliases{id($decl)} = self!root($source.resolution);
                    %!ambiguous-aliases{id($decl)} = True if $*STATIC-CONDITIONAL;
                }
                else {
                    self!report($node, 'unverifiable', 'destructuring binding', :reason('source container is not statically resolved'));
                }
            }
            $position++;
        }
        %env{id($decl)} = $actual;
    }
    $value
}

method !shape($decl, %env --> List) {
    my @shape;
    for $decl.shape.code-statements -> $dimension {
        my $value = self!infer($dimension, %env);
        if $value.has-value && $value.value ~~ Int && $value.value >= 0 {
            @shape.push($value.value);
        }
        else {
            self!report($decl, $value.has-value ?? 'mismatch' !! 'unverifiable', 'array shape',
                :reason('dimension must be a statically known nonnegative integer'));
            return ();
        }
    }
    @shape.List
}

method !shaped-init($site, Fact $value, @shape, Mu $expected) {
    my @values = $value.finite ?? $value.items.List !! $value.sequence ?? () !! ($value,);
    if $value.sequence && !$value.finite {
        self!report($site, 'unverifiable', 'array shape initialization', :reason('source length is unknown'));
        return;
    }
    self!report($site, 'mismatch', 'array shape initialization', :reason('initializer exceeds dimension ' ~ @shape[0]))
        if @values.elems > @shape[0];
    if @shape.elems > 1 {
        for @values -> $item {
            if !$item.sequence {
                self!report($site, 'mismatch', 'array shape initialization', :reason('multidimensional assignment requires structured data'));
            }
            else { self!shaped-init($site, $item, @shape[1..*], $expected) }
        }
    }
    else { self!check($site, $_, $expected, 'array element initialization') for @values }
}

method !hyper-operator($operator, @facts, $site --> Fact) {
    my $inner = $operator ~~ RakuAST::MetaInfix::Hyper ?? $operator.infix !! $operator.prefix;
    my @sequences = @facts.grep(*.sequence);
    unless @sequences && @sequences.grep({ !.finite }).elems == 0 {
        self!report($site, 'unverifiable', 'hyper operator', :reason('operand shapes are not statically enumerable'));
        return unknown('hyper operand shape');
    }
    my @lengths = @sequences.map(*.items.elems).unique;
    if @lengths.elems > 1 {
        self!report($site, 'unverifiable', 'hyper operator', :reason('hyper extension or recycling requires runtime shape rules'));
        return unknown('hyper extension');
    }
    my @results;
    for ^@lengths[0] -> $i {
        my @args = @facts.map({ .sequence ?? .items[$i] !! $_ });
        @results.push(@args.grep(*.sequence) ?? self!hyper-operator($operator, @args, $site)
            !! self!operator($inner, @args, $site));
    }
    Fact.new(:type(List), :definite(1), :sequence, :finite, :items(@results), :element(merge(|@results)))
}

method !bind-target($decl, $source, %env) {
    my $fact = self!argument($source, %env);
    %!binding-writable{id($decl)} = $fact.writable;
    if $source ~~ RakuAST::ApplyPostfix && $source.postfix ~~ RakuAST::Postcircumfix::Index
        && $fact.writable == 1 {
        %!element-aliases{id($decl)} = $source;
        %!ambiguous-aliases{id($decl)} = True if $*STATIC-CONDITIONAL;
    }
    elsif $fact.writable < 0 {
        self!report($decl, 'unverifiable', 'binding target', :reason('binding lifetime and writability are not statically known'));
    }
}
