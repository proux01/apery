Require Import BinInt.
From mathcomp Require Import all_ssreflect all_algebra.
Require Import tactics rat_of_Z bigopz shift.
Require punk.

Set SsrOldRewriteGoalsOrder.  (* change Set to Unset when porting the file, then remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Inductive Inat_of_uint := INat_of_uint of Decimal.uint.
Inductive Inatmul :=
  | INatmul of Ione & Inat_of_uint
  | IOpp of Inatmul.

Definition parse (x : Number.int) : option Inatmul :=
  match x with
  | Number.IntDecimal (Decimal.Pos u) =>
      Some (INatmul IOne (INat_of_uint u))
  | Number.IntDecimal (Decimal.Neg u) =>
      Some (IOpp (INatmul IOne (INat_of_uint u)))
  | Number.IntHexadecimal _ => None
  end.

Definition print (x : Inatmul) : option Number.int :=
  match x with
  | INatmul IOne (INat_of_uint n) =>
      Some (Number.IntDecimal (Decimal.Pos n))
  | IOpp (INatmul IOne (INat_of_uint n)) =>
      Some (Number.IntDecimal (Decimal.Neg n))
  | _ => None
  end.

Arguments GRing.one {_}.
Set Warnings "-via-type-remapping,-via-type-mismatch".
Number Notation Idummy_placeholder parse print (via Inatmul
  mapping [[GRing.natmul] => INatmul, [GRing.opp] => IOpp, [GRing.one] => IOne,
           [uintn] => INat_of_uint])
  : ring_scope.
Set Warnings "via-type-remapping,via-type-mismatch".
Arguments GRing.one : clear implicits.
