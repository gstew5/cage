Set Implicit Arguments.
Unset Strict Implicit.

Require Import String Ascii QArith.

Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import dyadic.

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
    let two = Big_int.big_int_of_int 2 in
    let rec int_of_positive p = 
      (match p with 
         | XI p' -> Big_int.succ_big_int (Big_int.mult_big_int two (int_of_positive p'))
         | XO p' -> Big_int.mult_big_int two (int_of_positive p')
         | XH -> Big_int.unit_big_int) in
    let int_of_Z z = 
      (match z with 
         | Z0 -> Big_int.zero_big_int
         | Zpos p -> int_of_positive p
         | Zneg p -> Big_int.minus_big_int (int_of_positive p)) in 
    Printf.eprintf 
      ""%f"" (Big_int.float_of_big_int (int_of_Z z));
    flush stderr;
    s".

Definition eprint_ZdivPos :
  forall (T : Type) (n : Z) (p : positive), T -> T := fun T z p t => t.
Extract Constant eprint_ZdivPos =>
 "fun n p s -> 
    let two = Big_int.big_int_of_int 2 in
    let rec int_of_positive p = 
      (match p with 
         | XI p' -> Big_int.succ_big_int (Big_int.mult_big_int two (int_of_positive p'))
         | XO p' -> Big_int.mult_big_int two (int_of_positive p')
         | XH -> Big_int.unit_big_int) in
    let int_of_Z z = 
      (match z with 
         | Z0 -> Big_int.zero_big_int
         | Zpos p -> int_of_positive p
         | Zneg p -> Big_int.minus_big_int (int_of_positive p)) in 
    (*let shrink n = 
      Big_int.shift_right_big_int n (Sys.word_size*(Big_int.num_digits_big_int n - 1)) in*)
    let shrink n = n in
    let num = Big_int.float_of_big_int (shrink (int_of_Z n)) in
    let den = Big_int.float_of_big_int (shrink (int_of_positive p)) in
    (*Printf.eprintf ""%F [%F / %F]"" (num /. den) num den;*)
    Printf.eprintf ""%F"" (num /. den);
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

Definition newline : string := String nl (String cr EmptyString).

Definition eprint_newline T (t : T) := eprint_string newline t.

Definition eprint_Q T (q : Q) (t : T) : T :=
  match q with
  | Qmake n d =>
    eprint_ZdivPos n d t
  end.

Lemma eprint_Q_id T q (t : T) : eprint_Q q t = t.
Proof. unfold eprint_Q; destruct q; auto. Qed.

Section PrintQvector.
  Variable A : Type.
  Context `{Showable A}.

  Fixpoint print_Qvector T (l : list (A*Q)) (t : T) : T :=
    match l with
    | nil => t
    | cons (a, w) l' =>
      let t1 := eprint_string (to_string a) t in
      let t2 := eprint_string ", " t1 in
      let t3 := eprint_Q w t2 in
      let t4 := eprint_newline t3 in
      print_Qvector l' t4
    end.

  Lemma print_Qvector_id T l (t : T) : print_Qvector l t = t.
  Proof.
    elim: l t => //=; case => a q l IH t; rewrite IH. 
    rewrite /eprint_newline eprint_string_id.
    by rewrite eprint_Q_id 2!eprint_ascii_id eprint_string_id.
  Qed.    
End PrintQvector.

Section PrintDvector.
  Variable A : Type.
  Context `{Showable A}.

  Definition print_Dvector T (l : list (A*D)) (t : T) : T :=
    print_Qvector
      (map (fun p => (p.1, D_to_Q p.2)) l)
      t.

  Lemma print_Dvector_id T l (t : T) : print_Dvector l t = t.
  Proof. by rewrite /print_Dvector print_Qvector_id. Qed.
End PrintDvector.

Instance showable_list {A : Type} `{Showable A} : Showable (list A) :=
  mkShowable 
    (fix F l :=
       match l with
       | nil => EmptyString
       | cons x l' =>
         append (to_string x)
                (append newline
                        (F l'))
       end).

Instance showable_nat : Showable nat :=
  mkShowable
    (fun n => match n with
     | O => "0"
     | 1%nat => "1"
     | 2 => "2"
     | 3 => "3"
     | 4 => "4"
     | 5 => "5"
     | 6 => "6"
     | 7 => "7"
     | 8 => "8"
     | 9 => "9"
     | 10 => "10"
     | _ => "<nat > 10>"
     end)%string.

Instance showable_N : Showable N.t :=
  mkShowable (fun n => to_string (N.to_nat n)).



