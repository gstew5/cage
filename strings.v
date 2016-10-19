Set Implicit Arguments.
Unset Strict Implicit.

Require Import String Ascii QArith.

Class Showable (T : Type) :=
  mkShowable { to_string : T -> string }.

Definition eprint_natchar : forall (T : Type) (n : N), T -> T := fun T n t => t.
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

Definition eprint_Z : forall (T : Type) (z : Z), T -> T := fun T z t => t.
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

Lemma eprint_ascii_id T c (t : T) : eprint_ascii c t = t.
Proof. auto. Qed.

Fixpoint eprint_string (T : Type) (s : string) (t : T) : T := 
  match s with
  | EmptyString => t
  | String c s' =>
    let t' := eprint_ascii c t
    in eprint_string s' t'
  end.

Lemma eprint_string_id T s (t : T) : eprint_string s t = t.
Proof. induction s; auto. Qed.
       
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

Lemma eprint_Q_id T q (t : T) : eprint_Q q t = t.
Proof. unfold eprint_Q; destruct q; auto. Qed.
