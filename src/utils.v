Require Import String.
Require Import Strings.String.
Require Import Strings.Ascii.
Open Scope string_scope.

Require Import Numbers.DecimalString.
Require Import Numbers.DecimalNat.
Definition nat_to_string (n: nat) := NilZero.string_of_uint (Decimal.rev (Unsigned.to_lu n)).

Definition newline := String "010" "".

Fixpoint mapWithIndexHelper {A B: Type} (curIndex: nat) (f: nat -> A -> B) (l: list A): list B := match l with
| nil => nil
| cons x xs => cons (f curIndex x) (mapWithIndexHelper (S curIndex) f xs)
end.

Definition mapWithIndex {A B: Type} (f: nat -> A -> B) (l: list A): list B := mapWithIndexHelper 0 f l.
