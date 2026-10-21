use static;
CHECK fail-on-unverifiable;
unit module StaticChecked;
sub checked(--> Int) is export { 42 }
