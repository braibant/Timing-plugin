Require Import String.
Add LoadPath "../src/" as Timing.
Require Import Timing.

Ltac count_ltac n m :=
  match n with
    | 0 => m
    | S ?n => let m := constr:(S m) in count_ltac n m
  end.
Ltac test :=
  start_timer "my_test";
  let x := fresh in let a := count_ltac 100 100 in set (x := a);
  stop_timer "my_test".

Goal True.
  Clear Timing Profile.

  start_timer "global".
  Print Timing Profile.
  test.
  Print Timing Profile.
  do 3 test.
  Print Timing Profile.
  do 3 test.
  Print Timing Profile.
  do 10 test.
  Print Timing Profile.
  stop_timer "global".
  Print Timing Profile.
  Clear Timing Profile.
Abort.

Require Import Omega.
Goal forall n m , n + m + n <= n + m + n + m.
intros. time "omega" omega.
Print Timing Profile.
Qed.

Axiom natprod : nat -> nat -> nat.
Fixpoint twos (k : nat) (x : nat) :=
  match k with
    | 0 => x
    | S k' => twos k' (natprod x x)
  end.

Axiom x : nat.

Local Notation big := (_ = _).

Goal let k := 17 in twos k x = twos k x.
Proof.
  cbv zeta; simpl twos.
  Fail poor_mans_timeout 1 apply f_equal.
Admitted.

(* Test assert_timer_running/assert_timer_not_running *)
Goal True.
assert_timer_not_running "test1".
Fail assert_timer_running "test1".
start_timer "test1".
assert_timer_running "test1".
Fail assert_timer_not_running "test1".
stop_timer "test1".
assert_timer_not_running "test1".
Fail assert_timer_running "test1".
Abort.