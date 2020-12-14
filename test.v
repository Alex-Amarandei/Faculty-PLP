Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Require Import Nat.

Definition eqb_string (x y : string) : bool :=
if (string_dec x y)
then true
else false.

Definition environment := string -> nat.

Definition initialenv : environment := fun _ => 0.

Definition update (env: environment) (s: string) (v: nat) :=
fun x => if (eqb_string x s)
         then v
         else env x.

Inductive List (T: Type) : Type :=
| nil
| list (n: T) (l: List T).

Notation "[ ]" := nil.
Arguments nil {T}.
Arguments list {T} _ _.

Notation "A :: L" := (list A L) (at level 60, right associativity).

Notation "[ A >> .. >> L ]" := (list A .. (list L []) ..).

Compute (1 :: (2 :: (3 :: [ ]))).

Compute [1 >> 2 >> 3].

Definition array := string -> List nat.

Definition updatearray (env: array) (s: string) (l: List nat) :=
fun x => if (eqb_string x s)
         then l
         else env x.

Definition emptyEnv : array := fun _ => [].
Definition firstUpdate := updatearray emptyEnv "v1" [1 >> 2 >> 3].

Check firstUpdate "v2". 

Fixpoint getListElement (v: List nat) (n: nat) :=
match v with 
| nil => 3333
| list val l2 => if (eqb n 0)
                 then val
                 else getListElement l2 (n - 1)
end.

Compute (getListElement [1 >> 2 >> 3] 9).

Definition get (arrays: array) (v: string) (poz: nat) := getListElement (arrays v) poz.

Compute get firstUpdate "v1" 2.

Fixpoint appendToList (l1 l2: List nat) : List nat :=
match l1 with 
| nil => l2
| list val l1' => list val (appendToList l1' l2) 
end.

Definition list1234 := appendToList [1 >> 2 >> 3] [4].
Compute list1234.

Definition push (arrays: array) (v: string) (l: List nat) :=
updatearray arrays v (appendToList (arrays v) l).

Definition secondUpdate := push firstUpdate "v1" [4].

Compute secondUpdate "v1".

Fixpoint setListElement (l: List nat) (poz: nat) (n: nat) :=
match l with
| nil => l
| list val l2 => if (eqb poz 0)
                 then list n l2
                 else list val (setListElement l2 (poz - 1) n)
end.

Compute setListElement [1 >> 2 >> 3] 1 5.

Definition set (arrays: array) (v: string) (poz: nat) (n: nat) :=
updatearray arrays v (setListElement (arrays v) poz n).

Definition thirdUpdate:= set secondUpdate "v1" 2 8.

Compute thirdUpdate "v1".

Inductive Struct := 
| struct (name: string) (env: environment).

Check [firstUpdate >> secondUpdate >> thirdUpdate].

Definition getStructElement (str: Struct) (field: string) :=
match str with
| struct n e => e field
end.

Definition struct1 := struct "firststruct" initialenv.

Compute getStructElement struct1 "firststruct".

Definition env2 := update initialenv "secondstruct" 19.

Definition struct2 := struct "secondstruct" env2.

Compute getStructElement struct2 "secondstruct".

Definition campuriPersoana := update (update (update initialenv "varsta" 20) "greutate" 54) "anfacultate" 2.

Definition structPersoana := struct "Persoana" campuriPersoana.

Compute getStructElement structPersoana "greutate".




































