Set Implicit Arguments.
Unset Strict Implicit.

Require Import String Ascii QArith.

Class Showable (T : Type) :=
  mkShowable { to_string : T -> string }.

Axiom eprint_natchar : forall (T : Type) (n : N), T -> T.
(** Raises an exception if [n >= 256]. *)
Extract Constant eprint_natchar =>
 "fun n s ->  
    let rec int_of_positive p = 
      (match p with 
         | XI p' -> 2 * (int_of_positive p') + 1
         | XO p' -> 2 * (int_of_positive p')
         | XH -> 1) in
    let int_of_N n = 
      (match n with
         | N0 -> 0
         | Npos p -> int_of_positive p) in
    Printf.eprintf ""%c"" (Char.chr (int_of_N n)); 
    flush stderr; 
    s".

Axiom eprint_Z : forall (T : Type) (z : Z), T -> T.
Extract Constant eprint_Z =>
 "fun z s -> 
    let rec length_positive p = 
      (match p with 
         | XI p' -> 1 + length_positive p' 
         | XO p' -> 1 + length_positive p' 
         | XH -> 1) in
    let length_Z z = 
      (match z with 
         | Z0 -> 1
         | Zpos p -> length_positive p
         | Zneg p -> length_positive p) in
    let rec int_of_positive p = 
      (match p with 
         | XI p' -> 2 * (int_of_positive p') + 1
         | XO p' -> 2 * (int_of_positive p')
         | XH -> 1) in
    let int_of_Z z = 
      (match z with 
         | Z0 -> 0
         | Zpos p -> int_of_positive p
         | Zneg p -> - (int_of_positive p)) in 
    (if float (length_Z z) > (log (float max_int) /. log 2.0)
     then Printf.eprintf ""INT_MAX""
     else Printf.eprintf ""%d"" (int_of_Z z));
    flush stderr;
    s".

Definition eprint_nat (T : Type) (n : nat) (t : T) : T := 
  eprint_Z (Z.of_nat n) t.

Definition eprint_ascii (T : Type) (c : ascii) (t : T) : T :=
  eprint_natchar (N_of_ascii c) t.

Fixpoint eprint_string (T : Type) (s : string) (t : T) : T := 
  match s with
  | EmptyString => t
  | String c s' =>
    let t' := eprint_ascii c t
    in eprint_string s' t'
  end.

Definition eprint_showable A T `{Showable A} (a : A) (t : T) : T :=
  eprint_string (to_string a) t.

Definition eprint_comma T (t : T) := eprint_string "," t.

Definition nl : ascii := "010".
Definition cr : ascii := "013".

Definition eprint_newline T (t : T) := eprint_string (String nl (String cr EmptyString)) t.

Definition eprint_Q T (q : Q) (t : T) : T :=
  match q with
  | Qmake n d =>
    let t1 := eprint_Z n t in
    let t2 := eprint_comma t1 in
    eprint_Z (Zpos d) t2
  end.

