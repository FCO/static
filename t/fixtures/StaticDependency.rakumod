unit module StaticDependency;
sub internal-text() { 'bad' }
# The importing CU must not inspect this body.
sub hidden() { my Int $invalid = internal-text(); $invalid }
sub external-int(--> Int) is export { 1 }
sub external-text(--> Str) is export { 'bad' }
sub external-untyped() is export { 1 }
