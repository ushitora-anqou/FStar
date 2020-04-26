module Bug1901

let rec g (a:nat) (x:list nat)
  : Tot (nat -> Tot nat)
  = fun s ->
    match x with
    | [] -> s
    | hd::tl -> g a tl s
