open OCanren
open GT

module Simple =
  struct
   
    @type ('a, 'b) fa =
    | Conj of 'a * 'a
    | Disj of 'a * 'a
    | Var  of 'b with show, gmap

    @type f = (f, string logic) fa logic with show, gmap

    module F = Fmap2 (struct type ('a, 'b) t = ('a, 'b) fa let fmap f g x = gmap(fa) f g x end)

    let rec reify_f f = F.reify reify_f reify f
                  
    let conj x y = inj @@ F.distrib (Conj (x, y))
    let disj x y = inj @@ F.distrib (Disj (x, y))
    let var  x   = inj @@ F.distrib (Var x)

    let rec evalo st fm = ocanren (
      fresh x, y, v in
      || (
          fm == Conj (x, y) &  evalo st x & evalo st y;
          fm == Disj (x, y) & (evalo st x | evalo st y);
          fm == Var  (v)    & Std.List.membero st v
        )
    )

    (*let rec evalo st fm =
      fresh (x y v) (
        conde [
          fm === conj x y &&& evalo st x &&& evalo st y;
          fm === disj x y &&& (evalo st x ||| evalo st y);
          fm === var  v   &&& Std.List.membero st v
      ])
     *)
    (* File "peval.ml", line 35, characters 24-25:
       Parse error: ',' or ')' expected (in [ocanren_term']) *)
    
    let rec evalo' fm = ocanren (
         fresh x, y in 
           fm == Conj (x, y)
       )
    
      
    (* File "peval.ml", line 47, characters 11-21:
       Error: This function has type
                ('a, 'b Logic.logic) Logic.injected ->
                ('a, 'b Logic.logic) Logic.injected -> OCanren.goal
              It is applied to too many arguments; maybe you forgot a `;'. *)
      
    let rec evalo'' fm = ocanren (
         fresh x, y in 
           fm == !(conj x y)
       )
   
    
    let _ =
      Printf.printf "%d\n" @@
      List.length @@ RStream.take @@
      run qrs
        (fun q r s -> (Std.List.lengtho s (Std.nat 2)) &&& (r =/= q) &&& evalo s (disj (var r) (var q)))
        (fun q r s -> s);
  
      List.iter (fun s -> Printf.printf "%s\n" @@ show(f) (s#reify reify_f)) @@ RStream.take ~n:10 @@
      run qrs
        (fun q r s -> (r =/= q) &&& evalo (Std.(%<) r q) s)
        (fun _ _ s -> s)
  end

module Elaborated =
  struct
   
    @type ('a, 'b) fa =
    | Conj of 'a * 'a
    | Disj of 'a * 'a
    | Neg  of 'a
    | Var  of 'b 
    | FTrue 
    | FFalse 
    with show, gmap

    @type name   = X | Y | Z with show, gmap
    @type f      = (f, name logic) fa logic with show, gmap
    @type answer = ocanren ((name * bool) list) with show

    module F = Fmap2 (struct type ('a, 'b) t = ('a, 'b) fa let fmap f g x = gmap(fa) f g x end)

    let rec reify_f f = F.reify reify_f reify f
                  
    let conj   x y = inj @@ F.distrib (Conj (x, y))
    let disj   x y = inj @@ F.distrib (Disj (x, y))
    let var    x   = inj @@ F.distrib (Var x)
    let neg    x   = inj @@ F.distrib (Neg x)
    let fTrue  ()  = inj @@ F.distrib FTrue 
    let fFalse ()  = inj @@ F.distrib FFalse

    let x () = !! X
    let y () = !! Y
    let z () = !! Z
             
    open List

    let rec evalo st fm u = ocanren (
      fresh x, y, z, v, w in
      || (
          fm == Conj (x, y) & evalo st x v & evalo st y w & Std.Bool.ando v w u;
          fm == Disj (x, y) & evalo st x v & evalo st y w & Std.Bool.oro  v w u;
          fm == Neg  (x)    & evalo st x v & Std.Bool.noto v u;
          fm == Var  (z)    & Std.List.assoco z st u; 
          fm == FTrue       & true  == u; 
          fm == FFalse      & false == u 
      )
    )
      
    let runTest strRepr query = 
      Printf.printf "\n%s\n\n" strRepr;
      List.iter (fun s -> Printf.printf "%s\n" @@ show(answer) 
                                                    (s#reify (Std.List.reify (Std.Pair.reify reify reify)))
                ) @@ RStream.take ~n:10 @@
      query (fun st -> st)

    let _ =
      runTest "Conj (Neg `x) `y:" @@  
        run q (fun st -> ocanren (evalo st Conj (Neg (Var (X)), Var (Y)) true)); 
      runTest "True:" @@  
        run q (fun st -> ocanren (evalo st FTrue true)); 
      runTest "False (evaluates to true):" @@  
        run q (fun st -> ocanren (evalo st FFalse true)); 
      runTest "False: (evaluates to false):" @@  
        run q (fun st -> ocanren (evalo st FFalse false)) 
        
  end
    
         

                                                  
