module L = List 

open OCanren 
open GT

module Helper = struct 
    let show_logic_int  = show(logic) (show(int))    
    let show_logic_int_list = show(Std.List.logic) show_logic_int

    let reify_list c = c#reify (Std.List.reify reify) 
  
    let print_results n result shower reifier =
      Printf.printf "------------------------------\n";
      L.iter (fun c -> Printf.printf "%s\n%!" @@ shower @@ reifier c) @@ 
              Stream.take ~n:n (result (fun c -> c))
  
    let run_list n result = 
      print_results n result show_logic_int_list reify_list 
  end 
(*  
let rec appendo xs ys out = ocanren (
    xs == [] & ys == out | 
    fresh h, t, r in 
      h :: t == xs & 
      (appendo t ys r) & 
      h :: r == out   
  ) 
 *)
(* File "appendo.ml", line 37, characters 14-16:
   Parse error: ')' expected after [ocanren_expr] (in [ocanren_embedding]) *)

let rec appendo xs ys out = ocanren (
    xs == [] & ys == out | 
    fresh h, t, r in 
      h :: t == xs & 
      appendo t ys r & 
      h :: r == out   
  )
 
let _ =                       
  Helper.run_list 1 @@ 
  run q (fun xs -> appendo xs xs xs) 


