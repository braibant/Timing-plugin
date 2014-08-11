(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

(* For [ArgArg] and [ArgVar] *)
open Glob_term
(* For [anomaly] *)
open Util
(* For pp **)
open Pp

module Section = struct
  let current () = Unix.gettimeofday ();;

  module Timer = struct

    type t =
	{
	  stack : float Stack.t ;
	  mutable total : float;
	  mutable number : int;
	  mutable mean : float;
	  mutable m2 : float
	}


    (** operations on timers *)
    let start (r : t) =
      Stack.push (current ()) r.stack

    let stop (r : t) =
      try
	let t = Stack.pop r.stack in
	let x = current () -. t in
	r.total <- r.total +. x;
	r.number <- r.number + 1;
	let delta = x -. r.mean in
	r.mean <- r.mean +. (delta /. float r.number);
	r.m2 <- r.m2 +. delta *. ( x -. r.mean)
      with
	| Stack.Empty -> () 			(* warning *)

    let zero () =
      {stack = Stack.create (); total = 0. ; number = 0; mean = 0.; m2 = 0.}

    let get (r : t) : float = r.mean

    let is_running (r : t) : bool =
      not (Stack.is_empty r.stack)

  end

  let state = Hashtbl.create 17;;

  (** operations on the mutable global state  *)

  type key = string
  let print_key fmt k = Format.fprintf fmt "%10s" k
  (** [run n] starts the timer [n], and create it if needed *)
  let start (n: key) =
    let r =
      try Hashtbl.find state n
      with
	| Not_found ->
	  let r =  Timer.zero () in
	  Hashtbl.add state n r;
	  r
    in
    Timer.start r

  (** [stop n] stop the timer [n] *)
  let stop (n : key) =
    try
      let r = Hashtbl.find state n in
      Timer.stop r
    with
      | Not_found -> ()

  let get (n : key) : float =
    try
      let r = Hashtbl.find state n in
      Timer.get r
    with
      | Not_found -> Pervasives.float_of_int 0

  let is_running (n : key) =
    try
      let r = Hashtbl.find state n in
      Timer.is_running r
    with
    | Not_found -> false

  (** [reset n] sets back a given timer to zero *)
  let reset (n : key) =
    Hashtbl.replace state n (Timer.zero ())

  (** [clear] reset all timers *)
  let clear () =
    Hashtbl.clear state

  type sort =
    Key | Total | Mean | Runs
  | Flip of sort
  | Then of sort * sort

  let sort_key : (key * Timer.t) -> (key * Timer.t) -> int = Pervasives.compare
  let sort_flip (f : (key * Timer.t) -> (key * Timer.t) -> int) : (key * Timer.t) -> (key * Timer.t) -> int =
    fun a b -> f b a
  let sort_by (f : Timer.t -> 'b) : (key * Timer.t) -> (key * Timer.t) -> int =
    fun (_,a) (_,b) -> Pervasives.compare (f a) (f b)
  let sort_then (f : 'a -> 'a -> int) (g : 'a -> 'a -> int) : 'a -> 'a -> int =
    fun a b ->
      let res = f a b in
      if res = 0 then g a b else res

  let rec sort_denote s =
    match s with
      Flip s -> sort_flip (sort_denote s)
    | Key -> sort_key
    | Total -> sort_by (fun t -> t.Timer.total)
    | Mean -> sort_by (fun t -> t.Timer.mean)
    | Runs -> sort_by (fun t -> t.Timer.number)
    | Then (s1,s2) -> sort_then (sort_denote s1) (sort_denote s2)

  let print sorter fmt () =
    let elements = Hashtbl.fold (fun key elt acc -> (key, elt) :: acc) state [] in
    let elements = List.stable_sort (sort_denote sorter) elements in
    List.iter
      (fun (key,timer) ->
	if timer.Timer.number <> 0
	then
	  begin
	    Format.fprintf fmt "%a:\t(total:%f, mean:%f, runs:%i, sigma2:%f)\n"
	      print_key key
	      timer.Timer.total
	      timer.Timer.mean
	      timer.Timer.number
	      (timer.Timer.m2 /. (float timer.Timer.number))
	  end;
	  )
      elements
end

(* [out_arg] stolen from micromega *)
let out_arg = function
  | ArgVar _ -> anomaly "Unevaluated or_var variable"
  | ArgArg x -> x

let _=Mltop.add_known_module "Timing_plugin"

let pp_print sorter () =
  let buf = Buffer.create 4 in
  let fmt = Format.formatter_of_buffer buf in
  let _ = (Format.fprintf fmt "%a\n%!" (Section.print sorter) ()) in
  (Buffer.contents buf)

let _ = Pp.msgnl (Pp.str "Loading the Timing Profiler")

let sort_for s =
  match s with
    "Mean" | "Mean+" -> Section.Mean
  | "Mean-" -> Section.Flip Section.Mean
  | "Key" | "Key+" -> Section.Key
  | "Key-" -> Section.Flip Section.Key
  | "Runs" | "Runs+" -> Section.Runs
  | "Runs-" -> Section.Flip Section.Runs
  | "Total" | "Total+" -> Section.Total
  | "Total-" -> Section.Flip Section.Total
  | _ ->
    Pp.msgerrnl (Pp.str "Unknown sorting definition:" ++ Pp.spc () ++ Pp.str s) ;
    Section.Key

open Tacexpr
open Tacinterp

TACTIC EXTEND start_timer
  | ["start_timer" string(n)] ->
    [ fun gl ->
	Section.start n;
	Tacticals.tclIDTAC gl]
END;;

TACTIC EXTEND stop_timer
  | ["stop_timer" string(n)] ->
    [fun gl ->
      Section.stop n;
      Tacticals.tclIDTAC gl]
END;;

TACTIC EXTEND reset_timer
  | ["reset_timer" string(n)] ->
    [fun gl -> Section.reset n; Tacticals.tclIDTAC gl]
END;;

TACTIC EXTEND print_current_time
  | ["print_current_time"] ->
    [fun gl -> Pp.msgnl (Pp.str (Format.sprintf "Current time: %f\n%!" (Section.current()))); Tacticals.tclIDTAC gl]
END;;

TACTIC EXTEND fail_if_timer_greater_than
  | ["fail_if_timer_greater_than" string(n) int_or_var(max_time) string(msg)  ] ->
    [
      fun gl ->
	if Pervasives.compare (Section.get n) (Pervasives.float_of_int (out_arg max_time)) <= 0
	then Tacticals.tclIDTAC gl
	else Tacticals.tclFAIL 0 (Pp.str msg) gl
    ]
END;;

TACTIC EXTEND time_tactic
  | ["time" string(n) tactic(t)] ->
    [ let tac =  Tacinterp.eval_tactic t in
      fun gl ->
	Section.start n;
	let res = tac gl in
	Section.stop n; res
    ]
END;;

TACTIC EXTEND assert_timer_running
  | ["assert_timer_running" string(n)] ->
    [fun gl ->
      if Section.is_running n then
	Tacticals.tclIDTAC gl
      else
	Tacticals.tclFAIL 0 (Pp.str "Timer" ++ Pp.spc () ++ Pp.qstring n ++ Pp.spc () ++ Pp.str " is not running!") gl ]
END;;

TACTIC EXTEND assert_timer_not_running
  | ["assert_timer_not_running" string(n)] ->
    [fun gl ->
      if Section.is_running n then
	Tacticals.tclFAIL 0 (Pp.str "Timer" ++ Pp.spc () ++ Pp.qstring n ++ Pp.spc () ++ Pp.str " is running!") gl
      else
	Tacticals.tclIDTAC gl ]
END;;

VERNAC COMMAND EXTEND PrintTimingProfile
  | ["Print" "Timing" "Profile"] ->
    [ Pp.msgnl (Pp.str (pp_print Section.Key ())) ]
  | ["Print" "Timing" "Profile" "Sort" "By" string(s) ] ->
    [ Pp.msgnl (Pp.str (pp_print (sort_for s) ())) ]
END;;

VERNAC COMMAND EXTEND ClearTimingProfile
 ["Clear" "Timing" "Profile"] ->
   [ Section.clear () ]
END;;
