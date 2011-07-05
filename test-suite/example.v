Add Rec LoadPath "../src/" as Timing.  
Add ML Path "../src/". 
Declare ML Module "Timing_plugin". 
             
Ltac count_ltac n m :=
  match n with
    | 0 => m
    | S ?n => let m := constr:(S m) in count_ltac n m
  end.
  
Ltac test :=
  run_timer 1;
  let x := fresh in let a := count_ltac 100 100 in set (x := a);
  stop_timer 1. 

Goal True. 
  Print Timing Profile. 
  test. 
  Print Timing Profile. 
  Clear Timing Profile. 
  
Abort.