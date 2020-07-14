Require Import String.
Require Import Strings.String.
Require Import Strings.Ascii.
Open Scope string_scope.

Require Import Numbers.DecimalString.
Require Import Numbers.DecimalNat.
Definition nat_to_string (n: nat) := NilZero.string_of_uint (Decimal.rev (Unsigned.to_lu n)).

Definition newline := String "010" "".