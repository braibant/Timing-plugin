Declare ML Module "timing_plugin".

Tactic Notation "poor_mans_timeout" int_or_var(n) tactic(tac) :=
  reset_timer "__poor_mans_timeout__";
  start_timer "__poor_mans_timeout__";
  tac;
  stop_timer "__poor_mans_timeout__";
  fail_if_timer_greater_than "__poor_mans_timeout__" n "Timeout!".
