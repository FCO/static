#!/usr/bin/env raku

# MAIN's option parser does not accept the interpreter's attached/repeated
# forms. Extract those options, preserving -- and all remaining arguments.
my @include-options;
my @module-options;
my @remaining;
while @*ARGS {
    my $arg = @*ARGS.shift;
    if $arg eq '--' {
        @remaining.append($arg, |@*ARGS);
        last;
    }
    if $arg.starts-with('-I') || $arg.starts-with('-M') {
        my $kind = $arg.substr(1, 1);
        my $value = $arg.substr(2);
        $value = $value.substr(1) if $value.starts-with('=');
        if $value eq '' {
            unless @*ARGS && !@*ARGS[0].starts-with('-') {
                note "-$kind requires an argument";
                exit 2;
            }
            $value = @*ARGS.shift;
        }
        if $kind eq 'I' { @include-options.push('-I' ~ $value) }
        else { @module-options.push('-M' ~ $value) }
    }
    else { @remaining.push($arg) }
}
@*ARGS = @remaining;

# Compile each input in its own process: CHECK runs, the mainline does not.
sub MAIN(
    :@I, #= Module search path (repeatable; -Ipath or -I path)
    :@M, #= Module to load (repeatable; -MModule or -M Module)
    Str :$policy = 'fail-on-mismatch',
    Bool :$external-signatures = True,
    Bool :$check-methods = True,
    *@files, #= Files to check; omit or use - to read stdin
) {
    my @policies = <fail-on-mismatch warn-on-mismatch fail-on-unverifiable warn-on-unverifiable>;
    unless $policy eq any(@policies) {
        note "Unknown policy '$policy'. Choose: " ~ @policies.join(', ');
        exit 2;
    }
    my @inputs = @files.elems ?? @files !! ['-'];
    if @inputs.grep(* eq '-').elems > 1 {
        note 'stdin (-) may only be specified once';
        exit 2;
    }
    my $local-lib = $?FILE.IO.absolute.IO.parent.parent.add('lib');
    my @include = $local-lib.add('static/CLI.rakumod').f
        ?? ['-I' ~ $local-lib.Str] !! [];
    @include.append(@include-options);
    @include.append(@I.map({ '-I' ~ $_ }));
    @module-options.append(@M.map({ '-M' ~ $_ }));
    # A new interpreter does not inherit this interpreter's -I arguments.
    # Forward repository specs in search order, including custom installations.
    @include.append: $*REPO.repo-chain
        .grep({ $_ ~~ CompUnit::Repository::FileSystem
            || $_ ~~ CompUnit::Repository::Installation })
        .map({ '-I' ~ .path-spec });
    my $module = '-Mstatic::CLI ' ~ ($policy, ~$external-signatures.Int, ~$check-methods.Int)
        .map({ '"' ~ $_ ~ '"' }).join(',');
    my $failed = False;
    for @inputs -> $input {
        if $input ne '-' && !$input.IO.f {
            note "Cannot read file: $input";
            $failed = True;
            next;
        }
        my $process = run $*EXECUTABLE, |@include, $module, |@module-options,
            '-c', '--', $input.Str;
        $failed = True if $process.exitcode != 0;
    }
    exit ($failed ?? 1 !! 0);
}
