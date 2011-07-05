(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

module Section = struct
  let current () = Unix.gettimeofday ();;

  module Timer = struct 

    type t =
	{
	  mutable last : float option; 
	  mutable total : float;
	}
	  
	  
    (** operations on timers *)
    let run (r : t) = 
      match r.last with
	| Some _ -> ()
	| None -> r.last <- Some (current ())
	  
	  
    let stop (r : t) = 
      match r.last with 
	| None -> () (* warning *)
	| Some t -> 
	  r.total <- r.total +. (current () -. t); 
	  r.last <- None

    let zero () =
      {last = None; total = 0.}
  end
    
  let state = Hashtbl.create 17;;

  (** operations on the mutable global state  *)	  

  (** [run n] starts the timer [n], and create it if needed *)
  let run (n: int) =
    let r = 
      try Hashtbl.find state n 
      with 
	| Not_found -> 
	  let r =  Timer.zero () in 
	  Hashtbl.add state n r;
	  r
    in
    Timer.run r

  (** [stop n] stop the timer [n] *)
  let stop (n : int) = 
    try 
      let r = Hashtbl.find state n in 
      Timer.stop r
    with 
      | Not_found -> ()
	
  (** [reset n] sets back a given timer to zero *)
  let reset (n : int) = 
    Hashtbl.replace state n (Timer.zero ())

  (** [clear] reset all timers *)
  let clear () =
    Hashtbl.clear state

  let print fmt () =
    Hashtbl.iter
      (fun key timer -> Format.fprintf fmt "%i:\t%f\n" key timer.Timer.total)
      state
end  
  
let _=Mltop.add_known_module "Timing_plugin"

let pp_print () =
  let buf = Buffer.create 4 in 
  let fmt = Format.formatter_of_buffer buf in 
  let _ = (Format.fprintf fmt "%a\n%!" Section.print ()) in 
  (Buffer.contents buf)

let _ = Pp.msgnl (Pp.str "Loading the Timing Profiler")

open Tacexpr
open Tacinterp

TACTIC EXTEND run_timer
  | ["run_timer" integer(n)] -> 
    [
      fun gl -> 
	Section.run n; 
	Tacticals.tclIDTAC gl]
END;;

TACTIC EXTEND stop_timer
  | ["stop_timer" integer(n)] -> 
    [fun gl -> 
      Section.stop n;
      Tacticals.tclIDTAC gl]
END;;

TACTIC EXTEND reset_timer
  | ["reset_timer" integer(n)] -> 
    [fun gl -> Section.reset n; Tacticals.tclIDTAC gl]
END;;

TACTIC EXTEND print_current_time
  | ["print_current_time"] -> 
    [fun gl -> Pp.msgnl (Pp.str (Format.sprintf "Current time: %f\n%!" (Section.current()))); Tacticals.tclIDTAC gl]
END;;

VERNAC COMMAND EXTEND PrintTimingProfile
 ["Print" "Timing" "Profile"] ->
   [ Pp.msgnl (Pp.str (pp_print ())) ]
END;;

VERNAC COMMAND EXTEND ClearTimingProfile
 ["Clear" "Timing" "Profile"] ->
   [ Section.clear () ]
END;;

