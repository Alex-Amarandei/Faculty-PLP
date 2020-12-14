(*
  LIMBAJ PLP

  Tipuri de date: nat, bool, int, string, double?

  string -> valuetype

  valuetype {
              nat 
              bool
              string
              int
              double?
            }

  Existente: ifthen, ifthenelse, while, for, assignment, sequence, declaration

  De adaugat: switch, break + continue, struct, vectori + stive + cozi, pointeri + liste

1, 2, 3, 4, 5

int a, b;
bool x, y;
nat n1, n2;

switch(exp) {
case val1: cod; break;
case val2: cod; break;
case default: cod; break;
*)

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

Inductive Nat : Type :=
| natt (n: nat)
| errnat.

Inductive Bool : Type :=
| booll (b:  bool)
| errbool.

Inductive List (T: Type) : Type :=
| nil
| list (t: T) (a: List T).

Inductive Array : Type :=
| NatArray (na: List Nat)
| BoolArray (nb: List Bool).

Inductive Field : Type :=
| nats (n: Nat)
| bools (b: Bool)
| arrays (a: Array).

Inductive Types: Type :=
| Nats (n : Nat)
| Bools (b : Bool)
| Arrays (a: Array)
| Structs (s: List Field)
| Undeclared.

Coercion natt: nat >-> Nat.
Coercion Nats: Nat >-> Types.
Coercion booll: bool >-> Bool.
Coercion Bools: Bool >-> Types.

Definition environment := string -> nat.

Definition memoryZone := nat -> Types.







Inductive State : Type :=
| currentZone (n: nat)
| memory (m: memoryZone)
| globalEnvironment (e: environment).

Definition initialMemory : memoryZone := fun _ => Undeclared.

Definition update (env: environment) (x : string) (v : Types) : environment :=
fun y => if (eqb_string x y)
         then v
         else (env y).

Definition env1 := update initial_environment "x" 7.
Definition env2 := update env1 "x" true.

Compute (env1 "x").
Compute (env2 "x").
Compute (env2 "a").














Inductive Exp :=
| anum: Nat -> Exp
| avar: string -> Exp
| aplus: Exp -> Exp -> Exp
| aminus: Exp -> Exp -> Exp
| amul: Exp -> Exp -> Exp
| adiv: Exp -> Exp -> Exp
| amod: Exp -> Exp -> Exp
| apower: Exp -> Exp -> Exp
| btrue : Exp
| bfalse : Exp
| bnot : Exp -> Exp
| band : Exp -> Exp -> Exp
| bor : Exp -> Exp -> Exp
| blessthan: Exp -> Exp -> Exp
| blessthanequal: Exp -> Exp -> Exp
| bgreaterthan: Exp -> Exp -> Exp
| bgreaterthanequal: Exp -> Exp -> Exp
| bequal: Exp -> Exp -> Exp
| bnotequal: Exp -> Exp -> Exp.

Coercion anum : Nat >-> Exp.
Coercion avar : string >-> Exp.

Infix "aplus" := (aplus) (at level 50, left associativity).
Infix "aminus" := (aminus) (at level 50, left associativity).
Infix "amul" := (amul) (at level 40, left associativity).
Infix "adiv" := (adiv) (at level 40, left associativity).
Infix "amod" := (amod) (at level 40, left associativity).
Infix "apower" := (apower) (at level 30, right associativity).

Notation "A +' B" := (A aplus B) (at level 50, left associativity).
Notation "A -' B" := (A aminus B) (at level 50, left associativity). 
Notation "A *' B" := (A amul B) (at level 40, left associativity).
Notation "A /' B" := (A adiv B) (at level 40, left associativity).
Notation "A %' B" := (A amod B) (at level 40, left associativity).
Notation "A ^' B" := (A apower B) (at level 30, right associativity).

Infix "band" := (band) (at level 80, right associativity).
Infix "bor" := (bor) (at level 85, right associativity).
Infix "blessthan" := (blessthan) (at level 70).
Infix "blessthanequal" := (blessthanequal) (at level 70).
Infix "bgreaterthan" := (bgreaterthan) (at level 70).
Infix "bgreaterthanequal" := (bgreaterthanequal) (at level 70).
Infix "bequal" := (bequal) (at level 70).
Infix "bnotequal" := (bnotequal) (at level 70).

Notation "! A" := (bnot A) (at level 75, right associativity).
Notation "A &&' B" := (A band B) (at level 80, right associativity).
Notation "A ||' B" := (A bor B) (at level 85, right associativity).
Notation "A <' B" := (A blessthan B) (at level 70).
Notation "A <=' B" := (A blessthanequal B) (at level 70).
Notation "A >' B" := (A bgreaterthan B) (at level 70).
Notation "A >=' B" := (A bgreaterthanequal B) (at level 70).
Notation "A ==' B" := (A bequal B) (at level 70).
Notation "A !=' B" := (A bnotequal B) (at level 70).

Check 2 +' 2.
Check 2 +' btrue.
Check (2 band 2).

Definition tplus (a b : Types) :=
match a, b with
| natt a, natt b => natt (a + b)
| booll a, booll b => match a, b with
                    | true, true => natt 2
                    | false, false => natt 0
                    | _, _ => natt 1
                    end
| natt a, booll b => match b with
                   | true => natt (a + 1)
                   | false => natt a
                   end
| booll a, natt b => match a with
                   | true => natt (1 + b)
                   | false => natt b
                   end
| _, _ => errnat
end.

Definition tminus (a b : Types) :=
match a, b with
| natt a, natt b => natt (a - b)
| booll a, booll b => match a, b with
                    | true, false => natt 1
                    | _, _ => natt 0
                    end
| natt a, booll b => match b with
                   | true => natt (a - 1)
                   | false => natt a
                   end
| booll a, natt b => match a with
                   | true => natt (1 - b)
                   | false => natt b
                   end
| _, _ => errnat
end.

Definition tmul (a b : Types) :=
match a, b with
| natt a, natt b => natt (a * b)
| booll a, booll b => match a, b with
                    | true, true => natt 1
                    | _, _ => natt 0
                    end
| natt a, booll b => match b with
                   | true => natt a
                   | false => natt 0
                   end
| booll a, natt b => match a with
                   | true => natt b
                   | false => natt 0
                   end
| _, _ => errnat
end.

Definition tdiv (a b : Types) :=
match a, b with
| natt a, natt b => match b with
                  | 0 => errnat
                  | _ => natt (div a b)
                  end
| booll a, booll b => match a, b with
                    | true, true => natt 1
                    | false, true => natt 0 
                    | _, _ => errnat
                    end
| natt a, booll b => match b with
                   | true => natt a
                   | false => errnat
                   end
| booll a, natt b => match a, b with
                   | _, 0 => errnat 
                   | true, _ => natt (div 1 b)
                   | false, _ => natt 0
                   end
| _, _ => errnat
end.

Definition tpow (a b : Types) :=
match a, b with
| natt a, natt b => natt (pow a b)
| booll a, booll b => match a, b with
                    | true, _ => natt 1
                    | false, true => natt 0
                    | false, false => errnat
                    end
| natt a, booll b => match b with
                   | true => natt a
                   | false => match a with
                              | 0 => errnat
                              | _ => natt 1
                              end
                   end
| booll a, natt b => match a with
                   | true => natt 1
                   | false => match b with
                              | 0 => errnat
                              | _ => natt 0
                              end
                   end
| _, _ => errnat
end.

Definition tmodulo (a b : Types) :=
match a, b with
| natt a, natt b => match b with
                  | 0 => errnat
                  | _ => natt (modulo a b)
                  end
| booll a, booll b => match a, b with
                    | true, true => natt 0
                    | false, true => natt 0 
                    | _, _ => errnat
                    end
| natt a, booll b => match b with
                   | true => natt 0
                   | false => errnat
                   end
| booll a, natt b => match a, b with
                   | _, 0 => errnat 
                   | true, _ => natt (modulo 1 b)
                   | false, _ => natt 0
                   end
| _, _ => errnat
end.

Definition tnot (b : Types) :=
match b with
| natt b => match b with
          | 0 => booll true
          | _ => booll false
          end
| booll b => match b with
           | true => booll false
           | false => booll true
           end
| _ => errbool
end.

Definition tand (a b : Types) :=
match a, b with
| natt a, natt b => match a, b with
                  | 0, _ => booll false
                  | _, 0 => booll false
                  | _, _ => booll true
                  end
| natt a, booll b => match b with
                  | false => booll false
                  | true => match a with
                            | 0 => booll false
                            | _ => booll true
                            end
                   end
| booll a, natt b => match a with
                  | false => booll false
                  | true => match b with
                            | 0 => booll false
                            | _ => booll true
                            end
                   end
| booll a, booll b => match a, b with
                    | true, true => booll true
                    | _, _ => booll false
                    end
| _, _ => errbool
end.

Definition tor (a b : Types) :=
match a, b with
| natt a, natt b => match a, b with
                  | 0, 0 => booll false
                  | _, _ => booll true
                  end
| natt a, booll b => match b with
                  | false => match a with 
                             | 0 => booll false
                             | _ => booll true
                             end
                  | true => booll true
                   end
| booll a, natt b => match a with
                  | false => match b with 
                             | 0 => booll false
                             | _ => booll true
                             end
                  | true => booll true
                   end
| booll a, booll b => match a, b with
                    | false, false => booll false
                    | _, _ => booll true
                    end
| _, _ => errbool
end.

Definition tlt (a b : Types) :=
match a, b with
| natt a, natt b => booll (ltb a b)
| natt a, booll b => match a, b with
                  | 0, true => booll true
                  | _, _ => booll false
                   end
| booll a, natt b => match a with
                  | false => booll (ltb 0 b) 
                  | true => booll (ltb 1 b)
                   end
| booll a, booll b => match a, b with
                    | false, true => booll true
                    | _, _ => booll false
                    end
| _, _ => errbool
end.

Definition tlte (a b : Types) :=
match a, b with
| natt a, natt b => booll (leb a b)
| natt a, booll b => match a, b with
                  | 0, _ => booll true
                  | 1, true => booll true
                  | _, _ => booll false
                   end
| booll a, natt b => match a with
                  | false => booll (Nat.leb 0 b) 
                  | true => booll (Nat.leb 1 b)
                   end
| booll a, booll b => match a, b with
                    | false, _ => booll true
                    | true, true => booll true
                    | true, false => booll false
                    end
| _, _ => errbool
end.

Definition tgt (a b : Types) := tnot (tlte a b).

Definition tgte (a b : Types) := tnot (tlt a b).

Definition teq (a b : Types) := 
match a, b with
| natt a, natt b => booll (eqb a b)
| booll a, booll b => match a, b with
                    | true, true => booll true
                    | false, false => booll true
                    | _, _ => booll false
                    end
| natt a, booll b => match a, b with
                   | 0, false => booll true
                   | 1, true => booll true
                   | _, _ => booll false
                   end
| booll a, natt b => match a, b with
                   | false, 0 => booll true
                   | true, 1 => booll true
                   | _, _ => booll false
                   end
| _, _ => errbool
end.

Definition tneq (a b : Types) := tnot (teq a b).

Compute tneq (tgte 2 (tplus true true)) 2.

(*
Compute (tpow (tmodulo 12 (tmul true 5)) (tdiv (tplus 7 (tmul 3 true)) (tminus true false))).
*)

Fixpoint Exp_Eval (exp : Exp) (env: environment) : Types := 
match exp with
| anum n => n
| avar v => env v
| a1 aplus a2 => tplus (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 aminus a2 => tminus (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 amul a2 => tmul (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 adiv a2 => tdiv (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 apower a2 => tpow (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 amod a2 => tmodulo (Exp_Eval a1 env) (Exp_Eval a2 env)
| btrue => true
| bfalse => false
| bnot b => tnot (Exp_Eval b env)
| b1 band b2 => tand (Exp_Eval b1 env) (Exp_Eval b2 env)
| b1 bor b2 => tor (Exp_Eval b1 env) (Exp_Eval b2 env)
| a1 blessthan a2 => tlt (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 blessthanequal a2 => tlte (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 bgreaterthan a2 => tgt (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 bgreaterthanequal a2 => tgte (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 bequal a2 => teq (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 bnotequal a2 => tneq (Exp_Eval a1 env) (Exp_Eval a2 env)
end.


(*
Inductive Array :=
| nil : Array
| array (t : Types): Types -> Array -> Array.

Inductive typp : Type :=
| Natt | Booll | Errr.

Inductive Arrray (t: Types) :=
match t with 
  | Nat => nat -> Arrray -> Arrray
  | Bool => bool -> Arrray -> Arrray
  | Err => Array.
  end.
.

Definition a1 := arrray Natt 7 nill.

Fixpoint getelement (a : Array) (p: nat) : Types :=
match a with
| nil => Err
| array var a2 => if (eqb p 0)
                  then var
                  else getelement a2 (p - 1)
end.

Compute (getelement a1 1).

Definition memory_zone := nat -> string.
Definition current_zone := nat.
Definition global_environment := update (default Err) "now" 0.
Definition variable (t: Types) := string -> t.

Inductive Statement :=
| declaration: string -> string -> Statement 
| assignment: string -> Exp -> Statement 
| sequence: Statement -> Statement -> Statement
| ifthen: Exp -> Statement -> Statement 
| ifthenelse: Exp -> Statement -> Statement -> Statement 
| whileloop: Exp -> Statement -> Statement 
| forloop: Statement -> Exp -> Statement -> Statement -> Statement
| switch: Exp -> Statement -> Statement
| break: Statement
| continue: Statement
| struct: string -> Statement -> Statement.

(*
Definition function (name: string) (commands: Statement) (env: environment) (iterations: nat): envirnoment :=
execute commands env iterations.
*)

Notation "'Var' A" := (declaration A) (at level 60).
Notation "A ::= B" := (assignment A B) (at level 70).
Notation "A ;; B" := (sequence A B) (at level 93, right associativity).
Notation "'If' ( B ) 'Then' { A } 'EndIf'" := (ifthen B A) (at level 97).
Notation "'If' ( B ) 'Then' { A } 'Else' { C } 'EndIfElse'" := (ifthenelse B A C) (at level 97).
Notation "'While' ( B ) { A } 'EndWhile'" := (whileloop B A) (at level 97).
Notation "'For' ( A '//' B '//' C ) { S } 'EndFor'" := (forloop A B C S) (at level 97).



*)










