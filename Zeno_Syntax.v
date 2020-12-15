Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Require Import Nat.

Inductive Nat : Type :=
| nrNat (n: nat)
| errNat.

Scheme Equality for Nat.

Coercion nrNat: nat >-> Nat.

Inductive Bool : Type :=
| valBool (b: bool)
| errBool.

Scheme Equality for Bool.

Coercion valBool: bool >-> Bool.

Inductive String : Type :=
| sString (s: string)
| errString.

Scheme Equality for String.

Coercion sString: string >-> String.

Inductive List (T: Type) :=
| nil
| list (t: T) (l: List T).

Scheme Equality for List.

Notation "[ ]" := nil.
Arguments nil {T}.

Notation "[ A >n .. >n B ]" := (list Nat A .. (list Nat B []) ..).
Notation "[ A >b .. >b B ]" := (list Bool A .. (list Bool B []) ..).

Inductive Array : Type :=
| natArray (na: List Nat)
| boolArray (ba: List Bool)
| stringArray (sa: List String)
| multipleArray (ma: List Array).

Inductive FieldTypes : Type :=
| natValue (n: Nat)
| boolValue (b: Bool)
| stringValue (s: String)
| arrayValue (a: Array)
| notFound.

Coercion natValue: Nat >-> FieldTypes.
Coercion boolValue: Bool >-> FieldTypes.
Coercion stringValue: String >-> FieldTypes.
Coercion arrayValue: Array >-> FieldTypes.

Inductive Field : Type := 
| field (name: string) (v: FieldTypes).

Notation "( A , B )" := (field A B).
Notation "{ A ; .. ; B }" := (list Field A .. (list Field B []) ..).

Definition getFieldName (f: Field) :=
match f with
| field name value => name
end.

Definition getFieldValue (f: Field) :=
match f with
| field name value => value
end.

Inductive Struct : Type :=
| struct (name: string) (fields: List Field).

Fixpoint getFieldListElement (l: List Field) (s: string) :=
match l with 
| nil => notFound
| list _ fld l2 => if (string_beq s (getFieldName fld))
                   then getFieldValue fld
                   else getFieldListElement l2 s
end.

Definition getStructValue (s: Struct) (n: string) :=
match s with
| struct name fieldList => getFieldListElement fieldList n
end.

Definition Varsta := ("varsta", 20).
Definition Nume := ("nume", "ioana").
Definition Persoana := struct "Persoana" {Varsta; Nume}.

Compute getStructValue Persoana "varsta".

Inductive ResultTypes : Type :=
| nrNats (n: Nat)
| valBools (b: Bool)
| arrays (a: Array)
| lists (T: Type) (l: List T)
| structs (s: Struct)
| undeclared
| unassigned
| error.

Coercion nrNats: Nat >-> ResultTypes.
Coercion valBools: Bool >-> ResultTypes.
Coercion lists: List >-> ResultTypes.
Coercion structs: Struct >-> ResultTypes.

Definition Environment := string -> ResultTypes.

Definition InitialEnvironment : Environment := fun _ => undeclared.

Definition updateEnvironment (env: Environment) (s: string) (v: ResultTypes) :=
fun x => if (string_beq x s)
         then v
         else env x.

Definition env1 := updateEnvironment InitialEnvironment "list1" [1 >n 2 >n 3].

Compute env1 "list1".

Definition listNat := [1 >n 2 >n 3].
Definition arrayNat := natArray listNat.

Definition listBool := [true >b true >b false].
Definition arrayBool := boolArray listBool.

Notation "[ A >a .. >a B ]" := (list Array A .. (list Array B []) ..).

Definition matrix := [arrayNat >a arrayBool].

Compute matrix.

Definition envMax := updateEnvironment InitialEnvironment "Persoana" Persoana.

Check envMax "Persoana".

(*Compute getStructValue (envMax "Persoana") "nume".*)

(*********************************************************)

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

Definition tplus (a b : ResultTypes) :=
match a, b with
| nrNat a, nrNat b => nrNat (a + b)
| valBool a, valBool b => match a, b with
                    | true, true => nrNat 2
                    | false, false => nrNat 0
                    | _, _ => nrNat 1
                    end
| nrNat a, valBool b => match b with
                   | true => nrNat (a + 1)
                   | false => nrNat a
                   end
| valBool a, nrNat b => match a with
                   | true => nrNat (1 + b)
                   | false => nrNat b
                   end
| _, _ => errNat
end.

Definition tminus (a b : ResultTypes) :=
match a, b with
| nrNat a, nrNat b => nrNat (a - b)
| valBool a, valBool b => match a, b with
                    | true, false => nrNat 1
                    | _, _ => nrNat 0
                    end
| nrNat a, valBool b => match b with
                   | true => nrNat (a - 1)
                   | false => nrNat a
                   end
| valBool a, nrNat b => match a with
                   | true => nrNat (1 - b)
                   | false => nrNat b
                   end
| _, _ => errNat
end.

Definition tmul (a b : ResultTypes) :=
match a, b with
| nrNat a, nrNat b => nrNat (a * b)
| valBool a, valBool b => match a, b with
                    | true, true => nrNat 1
                    | _, _ => nrNat 0
                    end
| nrNat a, valBool b => match b with
                   | true => nrNat a
                   | false => nrNat 0
                   end
| valBool a, nrNat b => match a with
                   | true => nrNat b
                   | false => nrNat 0
                   end
| _, _ => errNat
end.

Definition tdiv (a b : ResultTypes) :=
match a, b with
| nrNat a, nrNat b => match b with
                  | 0 => errNat
                  | _ => nrNat (div a b)
                  end
| valBool a, valBool b => match a, b with
                    | true, true => nrNat 1
                    | false, true => nrNat 0 
                    | _, _ => errNat
                    end
| nrNat a, valBool b => match b with
                   | true => nrNat a
                   | false => errNat
                   end
| valBool a, nrNat b => match a, b with
                   | _, 0 => errNat 
                   | true, _ => nrNat (div 1 b)
                   | false, _ => nrNat 0
                   end
| _, _ => errNat
end.

Definition tpow (a b : ResultTypes) :=
match a, b with
| nrNat a, nrNat b => nrNat (pow a b)
| valBool a, valBool b => match a, b with
                    | true, _ => nrNat 1
                    | false, true => nrNat 0
                    | false, false => errNat
                    end
| nrNat a, valBool b => match b with
                   | true => nrNat a
                   | false => match a with
                              | 0 => errNat
                              | _ => nrNat 1
                              end
                   end
| valBool a, nrNat b => match a with
                   | true => nrNat 1
                   | false => match b with
                              | 0 => errNat
                              | _ => nrNat 0
                              end
                   end
| _, _ => errNat
end.

Definition tmodulo (a b : ResultTypes) :=
match a, b with
| nrNat a, nrNat b => match b with
                  | 0 => errNat
                  | _ => nrNat (modulo a b)
                  end
| valBool a, valBool b => match a, b with
                    | true, true => nrNat 0
                    | false, true => nrNat 0 
                    | _, _ => errNat
                    end
| nrNat a, valBool b => match b with
                   | true => nrNat 0
                   | false => errNat
                   end
| valBool a, nrNat b => match a, b with
                   | _, 0 => errNat 
                   | true, _ => nrNat (modulo 1 b)
                   | false, _ => nrNat 0
                   end
| _, _ => errNat
end.

Definition tnot (b : ResultTypes) :=
match b with
| nrNat b => match b with
          | 0 => valBool true
          | _ => valBool false
          end
| valBool b => match b with
           | true => valBool false
           | false => valBool true
           end
| _ => errBool
end.

Definition tand (a b : ResultTypes) :=
match a, b with
| nrNat a, nrNat b => match a, b with
                  | 0, _ => valBool false
                  | _, 0 => valBool false
                  | _, _ => valBool true
                  end
| nrNat a, valBool b => match b with
                  | false => valBool false
                  | true => match a with
                            | 0 => valBool false
                            | _ => valBool true
                            end
                   end
| valBool a, nrNat b => match a with
                  | false => valBool false
                  | true => match b with
                            | 0 => valBool false
                            | _ => valBool true
                            end
                   end
| valBool a, valBool b => match a, b with
                    | true, true => valBool true
                    | _, _ => valBool false
                    end
| _, _ => errBool
end.

Definition tor (a b : ResultTypes) :=
match a, b with
| nrNat a, nrNat b => match a, b with
                  | 0, 0 => valBool false
                  | _, _ => valBool true
                  end
| nrNat a, valBool b => match b with
                  | false => match a with 
                             | 0 => valBool false
                             | _ => valBool true
                             end
                  | true => valBool true
                   end
| valBool a, nrNat b => match a with
                  | false => match b with 
                             | 0 => valBool false
                             | _ => valBool true
                             end
                  | true => valBool true
                   end
| valBool a, valBool b => match a, b with
                    | false, false => valBool false
                    | _, _ => valBool true
                    end
| _, _ => errBool
end.

Definition tlt (a b : ResultTypes) :=
match a, b with
| nrNat a, nrNat b => valBool (ltb a b)
| nrNat a, valBool b => match a, b with
                  | 0, true => valBool true
                  | _, _ => valBool false
                   end
| valBool a, nrNat b => match a with
                  | false => valBool (ltb 0 b) 
                  | true => valBool (ltb 1 b)
                   end
| valBool a, valBool b => match a, b with
                    | false, true => valBool true
                    | _, _ => valBool false
                    end
| _, _ => errBool
end.

Definition tlte (a b : ResultTypes) :=
match a, b with
| nrNat a, nrNat b => valBool (leb a b)
| nrNat a, valBool b => match a, b with
                  | 0, _ => valBool true
                  | 1, true => valBool true
                  | _, _ => valBool false
                   end
| valBool a, nrNat b => match a with
                  | false => valBool (Nat.leb 0 b) 
                  | true => valBool (Nat.leb 1 b)
                   end
| valBool a, valBool b => match a, b with
                    | false, _ => valBool true
                    | true, true => valBool true
                    | true, false => valBool false
                    end
| _, _ => errBool
end.

Definition tgt (a b : ResultTypes) := tnot (tlte a b).

Definition tgte (a b : ResultTypes) := tnot (tlt a b).

Definition teq (a b : ResultTypes) := 
match a, b with
| nrNat a, nrNat b => valBool (eqb a b)
| valBool a, valBool b => match a, b with
                    | true, true => valBool true
                    | false, false => valBool true
                    | _, _ => valBool false
                    end
| nrNat a, valBool b => match a, b with
                   | 0, false => valBool true
                   | 1, true => valBool true
                   | _, _ => valBool false
                   end
| valBool a, nrNat b => match a, b with
                   | false, 0 => valBool true
                   | true, 1 => valBool true
                   | _, _ => valBool false
                   end
| _, _ => errBool
end.

Definition tneq (a b : ResultTypes) := tnot (teq a b).

Compute tneq (tgte 2 (tplus true true)) 2.

(*
Compute (tpow (tmodulo 12 (tmul true 5)) (tdiv (tplus 7 (tmul 3 true)) (tminus true false))).
*)

Fixpoint Exp_Eval (exp : Exp) (env: Environment) : ResultTypes := 
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

Inductive Pair (T1 T2 : Type) :=
| pair (t1: T1) (t2: T2). 

Inductive Statement : Type :=
| declareNatVar: string -> Statement
| declareBoolVar: string -> Statement
| declareStringVar: string -> Statement

| assignNatVar: string -> Exp -> Statement
| assignBoolVar: string -> Exp -> Statement
| assignStringVar: string -> Exp -> Statement

| initializeNatVar: string -> string -> Exp -> Statement
| initializeBoolVar: string -> string -> Exp -> Statement
| initializeStringVar: string -> string -> Exp -> Statement

| initializeStruct: string -> List Field -> Statement
| getStructField: string -> string -> Statement
| setStructField: string -> string -> FieldTypes -> Statement

| ifThen: Exp -> Statement -> Statement
| ifThenElse: Exp -> Statement -> Statement -> Statement
| whileLoop: Exp -> Statement -> Statement
| forLoop: Statement -> Exp -> Statement -> Statement -> Statement
| sequence: Statement -> Statement -> Statement

| break
| continue

| switchCase: string -> List (Pair Nat Statement) -> Statement

| declareNatArray: string -> Statement
| declareBoolArray: string -> Statement
| declareStringArray: string -> Statement
| declareMultipleArray: string -> Statement

| initializeNatArray: string -> List Nat -> Statement
| initializeBoolArray: string -> List Bool -> Statement
| initializeStringArray: string -> List String -> Statement
| initializeMultipleArray: string -> List Array -> Statement

| getElementValue: string -> nat -> Statement

| setElementValueNat: string -> nat -> Nat -> Statement
| setElementValueBool: string -> nat -> Bool -> Statement
| setElementValueString: string -> nat -> String -> Statement
| setElementValueArray: string -> nat -> Array -> Statement

| pushElementValueNat: string -> Nat -> Statement
| pushElementValueBool: string -> Bool -> Statement
| pushElementValueString: string -> String -> Statement
| pushElementValueArray: string -> Array -> Statement

| popElement: string -> Statement

| concatArrays: string -> string -> Statement
.

Notation "'NVar' X" := (declareNatVar X) (at level 60).
Notation "'BVar' X" := (declareBoolVar X) (at level 60).
Notation "'SVar' X" := (declareStringVar X) (at level 60).

Notation "X '<n-' V" := (assignNatVar X V) (at level 70).
Notation "X '<b-' V" := (assignBoolVar X V) (at level 70).
Notation "X '<s-' V" := (assignStringVar X V) (at level 70).

Notation "'NLet' X '::' V" := (initializeNatVar X V) (at level 59).
Notation "'BLet' X '::' V" := (initializeBoolVar X V) (at level 59).
Notation "'SLet' X '::' V" := (initializeStringVar X V) (at level 59).

Notation "'Struct' X L" := (initializeStruct X L) (at level 60).
Notation "X './' F" := (getStructField X F) (at level 80).
Notation "X '.\' F V" := (setStructField X F V) (at level 79).

Notation "'If' '(' A ')' 'Then' '{' S '}' 'EndIfThen'" := (ifThen A S) (at level 47).
Notation "'If' '(' A ')' 'Then' '{' S1 '}' 'Else' '{' S2 '}' 'EndIfThenElse'" := (ifThenElse A S1 S2) (at level 48).
Notation "'While' ( B ) { A } 'EndWhile'" := (whileLoop B A) (at level 47).
Notation "'For' ( A '//' B '//' C ) { S } 'EndFor'" := (forLoop A B C S) (at level 48).
Notation "A ';;' B" := (sequence A B) (at level 45).

Notation "'Break'" := (break) (at level 44).
Notation "'Continue'" := (continue) (at level 44).

Definition casePair := pair Nat Statement.
Definition examplePair := casePair 3 ("X" <n- 5).

Notation "'case' X ':->' S" := (casePair X S) (at level 65).
Notation "'{\' C1 ';;/' .. ';;/' C2 '/}'" := (list casePair C1 .. (list casePair C2 []) ..) (at level 55). 
Notation "'switch' '(' X ')' C" := (switchCase X C) (at level 55).

Notation "'NArr' V" := (declareNatArray V) (at level 60).
Notation "'BArr' V" := (declareBoolArray V) (at level 60).
Notation "'SArr' V" := (declareStringArray V) (at level 60).
Notation "'MArr' V" := (declareMultipleArray V) (at level 60).

Notation "'LetNArr' V '::' L" := (initializeNatArray V L) (at level 59).
Notation "'LetBArr' V '::' L" := (initializeBoolArray V L) (at level 59).
Notation "'LetSArr' V '::' L" := (initializeStringArray V L) (at level 59).
Notation "'LetMArr' V '::' L" := (initializeMultipleArray V L) (at level 59).

Notation "X '[[' N ']]'" := (getElementValue X N) (at level 70).

Notation "X '[[' N ']]' '<n-' V" := (setElementValueNat X N V) (at level 68).
Notation "X '[[' B ']]' '<b-' V" := (setElementValueBool X B V) (at level 68).
Notation "X '[[' S ']]' '<s-' V" := (setElementValueString X S V) (at level 68).
Notation "X '[[' A ']]' '<a-' V" := (setElementValueArray X A V) (at level 68).

Notation "V '<+n' N" := (pushElementValueNat V N) (at level 67).
Notation "V '<+b' N" := (pushElementValueBool V N) (at level 67).
Notation "V '<+s' N" := (pushElementValueString V N) (at level 67).
Notation "V '<+a' N" := (pushElementValueArray V N) (at level 67).

Notation "'Pop' V" := (popElement V) (at level 65).

Notation "V1 '+>+' V2" := (concatArrays V1 V2) (at level 80).














