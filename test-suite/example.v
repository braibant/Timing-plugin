Require Import String. 
Add Rec LoadPath "../src/" as Timing.  
Add ML Path "../src/". 
Declare ML Module "Timing_plugin". 
             
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