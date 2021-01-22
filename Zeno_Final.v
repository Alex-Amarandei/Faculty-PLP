Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Require Import Nat.

(**** Data Types ****)




(*** Basic Types ***)



(** Natural Numbers **)

Inductive Nat : Type :=
| nNat (n: nat)
| errNat.

Scheme Equality for Nat.
Coercion nNat: nat >-> Nat.

Check nNat 5.


(** Boolean Values **)

Inductive Bool : Type :=
| bBool (b: bool)
| errBool.

Scheme Equality for Bool.
Coercion bBool: bool >-> Bool.

Check bBool true.


(** Character Strings **)

Inductive String : Type :=
| sString (s: string)
| errString.

Scheme Equality for String.
Coercion sString: string >-> String.

Check sString "PLP".

Inductive Number : Type :=
| nNats (n: Nat)
| bBools (b: Bool)
| sStrings (s: String)
| errNum.

Scheme Equality for Number.
Coercion nNats: Nat >-> Number.
Coercion bBools: Bool >-> Number.
Coercion sStrings: String >-> Number.

Check nNats 4. Check bBools true. Check sString EmptyString.


(*** Complex Data Types ***)


(** Linked Lists **)

Inductive List (T: Type) :=
| nil
| list (t: T) (l: List T).

Scheme Equality for List.
Check list Nat 4 (list Nat 3 (list Nat 2 (nil Nat))).

Notation "[ ]" := (nil).
Arguments nil {T}. (* Tells Coq to infer the type of T in the case of nil based on its surroundings *)

Check list Number 4 (list Number true (list Number "" [])).

Inductive LinkedList : Type :=
| natList (l: List Nat)
| boolList (l: List Bool)
| stringList (l: List String)
| errList. 

Notation "'NL' L" := (natList L) (at level 90).
Notation "'BL' L" := (boolList L) (at level 90).
Notation "'SL' L" := (stringList L) (at level 90).

Notation "'[' A '>n' .. '>n' B ']'" := (list Nat A .. (list Nat B []) ..).
Check [1 >n 2 >n 3]. Check NL [1 >n 2 >n 3].

Notation "'[' A '>b' .. '>b' B ']'" := (list Bool A .. (list Bool B []) ..).
Check [true >b false >b true]. Check BL [true >b false >b true].

Notation "'[' A '>s' .. '>s' B ']'" := (list String A .. (list String B []) ..).
Check ["P" >s "L" >s "P"]. Check SL ["P" >s "L" >s "P"].


(** Arrays (built on lists) **)

Inductive Array : Type :=
| natArray (na: List Nat)
| boolArray (ba: List Bool)
| stringArray (sa: List String)
| multipleArray (ma: List Array)
| errArray.

Notation "'NA' L" := (natArray L) (at level 90).
Definition natArray123 := NA [1 >n 2 >n 3].
Check natArray123.

Notation "'BA' L" := (boolArray L) (at level 90).
Definition boolArrayTFT := BA [true >b false >b true].
Check boolArrayTFT.

Notation "'SA' L" := (stringArray L) (at level 90).
Definition stringArrayPLP := SA ["P" >s "L" >s "P"].
Check stringArrayPLP.

Notation "'MA' L" := (multipleArray L) (at level 90).
Definition multipleListNBS := (list Array natArray123 (list Array boolArrayTFT (list Array stringArrayPLP []))).
Definition multipleArrayNBS := MA multipleListNBS.
Check multipleArrayNBS.


(** Enums (built on lists) **)

Inductive Enum : Type :=
| enum (e: List Number).

Notation "'EN' L" := (enum L) (at level 90).
Notation "'[' A '>e' .. '>e' B ']'" := (list Number A .. (list Number B []) ..).
Check [ 4 >e true >e "PLP" ].

Definition enum0isF := EN [0 >e "is" >e false].
Check enum0isF.


(** Structs (built on lists) **)

Inductive FieldTypes : Type :=
| natValue (n: Nat)
| boolValue (b: Bool)
| stringValue (s: String)
| listValue (l: LinkedList)
| arrayValue (a: Array)
| enumValue (e: Enum)
| notFound.

Coercion natValue: Nat >-> FieldTypes.
Coercion boolValue: Bool >-> FieldTypes.
Coercion stringValue: String >-> FieldTypes.
Coercion listValue: LinkedList >-> FieldTypes.
Coercion arrayValue: Array >-> FieldTypes.
Coercion enumValue: Enum >-> FieldTypes.

Inductive Field : Type :=
| field (n: string) (v: FieldTypes).

Notation "'((' N ',' V '))'" := (field N V) (at level 80).

Definition field1 := (("age", 20)).
Check field1.

Definition field2 := (("name", "Alex")).
Check field2.

Definition field3 := (("favoriteEnum", enum0isF)).
Check field3.

Notation "'{{' A ';' .. ';' B '}}'" := (list Field A .. (list Field B []) ..).

Definition fieldList := {{field1 ; field2 ; field3}}.
Check fieldList. 

Inductive Struct : Type :=
| struct (s: List Field).

Notation "'ST' L" := (struct L) (at level 80).

Definition struct1 := ST fieldList.
Check struct1.




(**** Collective Data Type ****)




Inductive Unassigned : Type :=
| unassignedNat
| unassignedBool
| unassignedString
| unassignedNatList
| unassignedBoolList
| unassignedStringList
| unassignedNatArray
| unassignedBoolArray
| unassignedStringArray
| unassignedMultipleArray
| unassignedEnum.

Inductive ResultTypes : Type :=
| numbers (n: Number) (***********)
| lists (l: LinkedList)
| arrays (a: Array)
| enums (e: Enum)
| structs (s: Struct)
| undeclared
| unassigned (u: Unassigned)
| error.

Coercion numbers: Number >-> ResultTypes. (*************)
Coercion lists: LinkedList >-> ResultTypes.
Coercion arrays: Array >-> ResultTypes.
Coercion enums: Enum >-> ResultTypes.
Coercion structs: Struct >-> ResultTypes.
Coercion unassigned: Unassigned >-> ResultTypes.



(**** Expression Syntax ****)

Inductive Exp :=
| anum: Number -> Exp
| avar: string -> Exp
| aplus: Exp -> Exp -> Exp
| aminus: Exp -> Exp -> Exp
| amul: Exp -> Exp -> Exp
| adiv: Exp -> Exp -> Exp
| amod: Exp -> Exp -> Exp
| apower: Exp -> Exp -> Exp
| bnot: Exp -> Exp
| band: Exp -> Exp -> Exp
| bor: Exp -> Exp -> Exp
| blessthan: Exp -> Exp -> Exp
| blessthanequal: Exp -> Exp -> Exp
| bgreaterthan: Exp -> Exp -> Exp
| bgreaterthanequal: Exp -> Exp -> Exp
| bequal: Exp -> Exp -> Exp
| bnotequal: Exp -> Exp -> Exp
.

Coercion avar : string >-> Exp.
Coercion anum : Number >-> Exp.

Infix "aplus" := (aplus) (at level 50, left associativity).
Infix "aminus" := (aminus) (at level 50, left associativity).
Infix "amul" := (amul) (at level 40, left associativity).
Infix "adiv" := (adiv) (at level 40, left associativity).
Infix "amod" := (amod) (at level 20, left associativity).
Infix "apower" := (apower) (at level 30, right associativity).

Notation "A +' B" := (A aplus B) (at level 50, left associativity).
Notation "A -' B" := (A aminus B) (at level 50, left associativity). 
Notation "A *' B" := (A amul B) (at level 40, left associativity).
Notation "A /' B" := (A adiv B) (at level 40, left associativity).
Notation "A %' B" := (A amod B) (at level 20, left associativity).
Notation "A ^' B" := (A apower B) (at level 30, right associativity).

Infix "band" := (band) (at level 80, right associativity).
Infix "bor" := (bor) (at level 85, right associativity).
Infix "blessthan" := (blessthan) (at level 70).
Infix "blessthanequal" := (blessthanequal) (at level 70).
Infix "bgreaterthan" := (bgreaterthan) (at level 70).
Infix "bgreaterthanequal" := (bgreaterthanequal) (at level 70).
Infix "bequal" := (bequal) (at level 70).
Infix "bnotequal" := (bnotequal) (at level 70).

Notation "!' A" := (bnot A) (at level 75, right associativity).
Notation "A &&' B" := (A band B) (at level 80, right associativity).
Notation "A ||' B" := (A bor B) (at level 85, right associativity).
Notation "A <' B" := (A blessthan B) (at level 70).
Notation "A <=' B" := (A blessthanequal B) (at level 70).
Notation "A >' B" := (A bgreaterthan B) (at level 70).
Notation "A >=' B" := (A bgreaterthanequal B) (at level 70).
Notation "A ==' B" := (A bequal B) (at level 70).
Notation "A !=' B" := (A bnotequal B) (at level 70).

Check (2 +' 4).
Check (true ||' false).
Check ("abc" +' "def").




(**** Statement Syntax ****)



(*
Inductive Pair (T1 T2 : Type) : Type :=
| pair (t1: T1) (t2: T2).*)

(* Unmodified in Final2.v *)

Inductive Statement : Type :=
| decNatVar: string -> Statement
| decBoolVar: string -> Statement
| decStringVar: string -> Statement

| asnNatVar: string -> Exp -> Statement
| asnBoolVar: string -> Exp -> Statement
| asnStringVar: string -> Exp -> Statement

| initNatVar: string -> Exp -> Statement
| initBoolVar: string -> Exp -> Statement
| initStringVar: string -> Exp -> Statement

| decNatList: string -> Statement
| decBoolList: string -> Statement
| decStringList: string -> Statement

| initNatList: string -> LinkedList -> Statement
| initBoolList: string -> LinkedList -> Statement
| initStringList: string -> LinkedList -> Statement

| asnList: string -> LinkedList -> Statement

| insInList: string -> nat -> Exp -> Statement

| appToList: string -> Exp -> Statement

| concList: string -> string -> Statement

| delFromList: string -> nat -> Statement

| trList: string -> Statement

| decNatArray: string -> Statement
| decBoolArray: string -> Statement
| decStringArray: string -> Statement
| decMultipleArray: string -> Statement

| initNatArray: string -> Array -> Statement
| initBoolArray: string -> Array -> Statement
| initStringArray: string -> Array -> Statement
| initMultipleArray: string -> Array -> Statement

| asnArray: string -> Array -> Statement

| stArrayNumber: string -> nat -> Exp -> Statement
| stArrayArray: string -> nat -> Array -> Statement

| pshFrontArrayNumber: string -> Exp -> Statement
| pshFrontArrayArray: string -> Array -> Statement

| pshBackArrayNumber: string -> Exp -> Statement
| pshBackArrayArray: string -> Array -> Statement

| ppFrontArray: string -> Statement

| ppBackArray: string -> Statement

| decEnum: string -> Statement
| initEnum: string -> Enum -> Statement
| asnEnum: string -> Enum -> Statement

| pshFrontEnum: string -> Exp -> Statement
| pshBackEnum: string -> Exp -> Statement
| ppFrontEnum: string -> Statement
| ppBackEnum: string -> Statement

| stEnum: string -> nat -> Exp -> Statement

| initStruct: string -> Struct -> Statement

| stStructField: string -> string -> FieldTypes -> Statement

| ifThen: Exp -> Statement -> Statement
| ifThenElse: Exp -> Statement -> Statement -> Statement
| doWhileLoop: Statement -> Exp -> Statement
| whileLoop: Exp -> Statement -> Statement
| forLoop: Statement -> Exp -> Statement -> Statement -> Statement
| sequence: Statement -> Statement -> Statement

| break
| continue

| switchCase: Exp -> List Pair -> Statement
| emptyStatement
with Pair : Type :=
| caseDefault (s: Statement)
| case: Number -> Statement -> Pair.

(*** Instruction Notations ***)



(** Variables: Declare, Assign, Initialize **)

Notation "'NVar' X" := (decNatVar X) (at level 50).
Notation "'BVar' X" := (decBoolVar X) (at level 50).
Notation "'SVar' X" := (decStringVar X) (at level 50).

Notation "X '<n-' V" := (asnNatVar X V) (at level 50).
Notation "X '<b-' V" := (asnBoolVar X V) (at level 50).
Notation "X '<s-' V" := (asnStringVar X V) (at level 50).

Notation "'NLet' X ':n:' V" := (initNatVar X V) (at level 50).
Notation "'BLet' X ':b:' V" := (initBoolVar X V) (at level 50).
Notation "'SLet' X ':s:' V" := (initStringVar X V) (at level 50).


(** Lists: Declare, Initialize, Assign, Insert, Append, Delete, Trim, Get **)

Notation "'NLst' V" := (decNatList V) (at level 50).
Notation "'BLst' V" := (decBoolList V) (at level 50).
Notation "'SLst' V" := (decStringList V) (at level 50).

Notation "'LetNLst' V ':<n>:' L" := (initNatList V L) (at level 50).
Notation "'LetBLst' V ':<b>:' L" := (initBoolList V L) (at level 50).
Notation "'LetSLst' V ':<s>:' L" := (initStringList V L) (at level 50).

Notation "A ':<:' B" := (asnList A B) (at level 50).

Notation "A 'ins' <' B '> <' C '>" := (insInList A B C) (at level 50).

Notation "A '<+l' B" := (appToList A B) (at level 50).

Notation "A '+l+' B" := (concList A B) (at level 50).

Notation "A 'del' <' B '>" := (delFromList A B) (at level 50).

Notation "'trim' A" := (trList A) (at level 50).
(*
Notation "A '<<' B '>>'" := (gtFromList A B) (at level 50).
*)

(** Arrays: Declare, Initialize, Assign, Set, Push (Front/Back), Pop (Front/Back), Get **)

Notation "'NArr' V" := (decNatArray V) (at level 50).
Notation "'BArr' V" := (decBoolArray V) (at level 50).
Notation "'SArr' V" := (decStringArray V) (at level 50).
Notation "'MArr' V" := (decMultipleArray V) (at level 50).

Notation "'LetNArr' V ':[n]:' L" := (initNatArray V L) (at level 50).
Notation "'LetBArr' V ':[b]:' L" := (initBoolArray V L) (at level 50).
Notation "'LetSArr' V ':[s]:' L" := (initStringArray V L) (at level 50).
Notation "'LetMArr' V ':[a]:' L" := (initMultipleArray V L) (at level 50).

Notation "A ':[:' B" := (asnArray A B) (at level 50).

Notation "X [' N '] '<[n-' V" := (stArrayNumber X N V) (at level 50).
Notation "X [' N '] '<[a-' V" := (stArrayArray X N V) (at level 50).

Notation "V '>+n' N" := (pshFrontArrayNumber V N) (at level 50).
Notation "V '>+a' N" := (pshFrontArrayArray V N) (at level 50).

Notation "V '<+n' N" := (pshBackArrayNumber V N) (at level 50).
Notation "V '<+a' N" := (pshBackArrayArray V N) (at level 50).

Notation "'popf' V" := (ppFrontArray V) (at level 50).

Notation "'popb' V" := (ppBackArray V) (at level 50).
(*
Notation "X [[' N ']]" := (gtArrayValue X N) (at level 50).
*)

(** Enums: Declare, Initialize, Assign, Push Front/Back, Pop Front/Back, Set, Get **)

Notation "'dEnum' E" := (decEnum E) (at level 50).
Notation "'LetEnum' E :[e]: L" := (initEnum E L) (at level 50).
Notation "A ':[e:' B" := (asnEnum A B) (at level 50).

Notation "V '>+e' N" := (pshFrontEnum V N) (at level 50).
Notation "V '<+e' N" := (pshBackEnum V N) (at level 50).
Notation "V '>-e'" := (ppFrontEnum V) (at level 50).
Notation "V '<-e'" := (ppBackEnum V) (at level 50).

Notation "X [' E '] '<e-' V" := (stEnum X E V) (at level 50).
(*Notation "X '[)' N '(]'" := (gtEnum X N) (at level 50).*)


(** Structs: Initialize, Assign, Get, Set **)

Notation "'LetStruct' X :{s}: L" := (initStruct X L) (at level 50).
(*Notation "A ':{s:' B" := (asnStruct A B) (at level 50).*)
(*Notation "X '{/' F '\}'" := (gtStructField X F) (at level 50).*)
Notation "X '{\' F '/}' V" := (stStructField X F V) (at level 50).


(** Instructions: Decisional, Repetitive, Sequences, Iteration Manipulators **)

Notation "'Ift' '(' A ')' 'Then' '{' S '}' 'EndIfThen'" := (ifThen A S) (at level 50).
Notation "'If' '(' A ')' 'Then' '{' S1 '}' 'Else' '{' S2 '}' 'EndIfThenElse'" := (ifThenElse A S1 S2) (at level 55).
Notation "'Do' { S } 'WhileStill' ( C )" := (doWhileLoop S C) (at level 50).
Notation "'While' ( B ) { A } 'EndWhile'" := (whileLoop B A) (at level 50).
Notation "'For' ( A '//' B '//' C ) { S } 'EndFor'" := (forLoop A B C S) (at level 50).
Notation "A ';;' B" := (sequence A B) (at level 90, right associativity).

Notation "'Break'" := (break) (at level 45).
Notation "'Continue'" := (continue) (at level 45).


(*** Example Statements ***)



(** Variables: Declare, Assign, Initialize **)

Check (NVar "x") ;; (BVar "y") ;; (SVar "z").

Check ("x" <n- 3) ;; ("y" <b- true) ;; ("z" <s- "z").

Check (NLet "x" :n: 3) ;; (BLet "y" :b: false) ;; (SLet "z" :s: "z").


(** Lists: Declare, Initialize, Assign, Insert, Append, Delete, Trim, Get **)

Check (NLst "x") ;; (BLst "y") ;; (SLst "z").

Check (LetNLst "x" :<n>: NL [1 >n 2 >n 3]) ;; (LetBLst "y" :<b>: BL [true >b true]) ;; (LetSLst "z" :<s>: SL ["P" >s "L" >s "P"]).

Check ("x1" :<: NL [1 >n 2]) ;; ("y1" :<: BL [true >b false]) ;; ("z1" :<: SL ["1" >s "0"]).

Check ("x" ins <'0'><'1'>) ;; ("y" ins <'1'><' true '>) ;; ("z" ins <'2'><'"z"'>).

Check ("x" +l+ "x") ;; ("y" +l+ "y") ;; ("z" +l+ "z").

Check ("x" del <'1'>) ;; ("y" del <'1'>) ;; ("z" del <'1'>).

Check (trim "x") ;; (trim "y") ;; (trim "z").

(*Check ("x" << 1 >>) ;; ("y" << 1 >>) ;; ("z" << 1 >>).*)


(** Arrays: Declare, Initialize, Assign, Set, Push (Front/Back), Pop (Front/Back), Get **)

Check (NArr "x") ;; (BArr "y") ;; (SArr "z") ;; (MArr "t").

Check (LetNArr "x" :[n]: natArray123) ;; (LetBArr "y" :[b]: boolArrayTFT) ;; (LetSArr "z" :[s]: stringArrayPLP) ;; (LetMArr "t" :[a]: multipleArrayNBS).

Check ( "x1" :[: natArray123 ).

Check ("x"['2'] <[n- 3) ;; ("y"['2'] <[n- true) ;; ("z"['2'] <[n- "3") ;; ("t"['2'] <[a- natArray123).

Check ("x" >+n 1) ;; ("y" >+n true) ;; ("z" >+n "z") ;; ("t" >+a natArray123).

Check ("x" <+n 1) ;; ("y" <+n true) ;; ("z" <+n "z") ;; ("t" <+a natArray123).

Check (popf "x") ;; (popf "y") ;; (popf "z") ;; (popf "t").
Check (popb "x") ;; (popb "y") ;; (popb "z") ;; (popb "t").

(*Check ("x" [['2']]) ;; ("y" [['2']]) ;; ("z"[['2']]) ;; ("t"[['2']]).*)


(** Enums: Declare, Initialize, Assign, Push Front/Back, Pop Front/Back, Set, Get **)

Check (dEnum "e") ;; (LetEnum "d" :[e]: enum0isF ) ;; ("e" :[e: enum0isF).

Check ("e" >+e 4) ;; ("e" <+e true) ;; ("e" >-e) ;; ("e" <-e).

Check ("e"['2'] <e- 2). (* ;; ("e"[)2(]). *)


(** Structs: Initialize, Assign, Get, Set **)

Check (LetStruct "x" :{s}: struct1) (* ;; ("x1" :{s: "x2") ;; ("x" {/"f1"\}) *) ;; ("x" {\"f2"/} 7).


(**** Semantics ****)




(** Utility functions for strings **)

(* Bool Equality for strings *)

Definition eqb_string (x y : string) : bool :=
if string_dec x y 
then true 
else false.

(* Multiple concatenation of strings *)

Fixpoint strMul (a: string) (b: nat) :=
match b with
| 0 => EmptyString
| S b' => a ++ ( strMul a b' )
end. 


(** Operations **)

Definition tplus (a b: Number) : Number :=
match a, b with
| nNats a, nNats b => match a, b with
											| nNat a, nNat b => a + b
											|	_, _ => errNat
											end
| bBools a, bBools b => match a, b with
												| bBool a, bBool b => match a, b with
																							| true, true => 2
																							| false, false => 0
																							| _, _ => 1
																							end
												| _, _ => errBool
                    		end
| sStrings a, sStrings b => match a, b with
														| sString a, sString b => a ++ b
														| _, _ => errString
														end
| nNats a, bBools b => match a , b with
											 | nNat a, bBool b => match b with
											 											| true => a + 1
											 											| false => a
											 											end
											 | _, _ => errNum
											 end
| bBools a, nNats b => match a, b with
											 | bBool a, nNat b => match a with
											 											| true => b + 1
											 											| false => b
											 											end
											 | _, _ => errNum
											 end
| _, _ => errNum
end.

Compute tplus 4 5. Compute tplus true false. Compute tplus "abc" "def". 
Compute tplus 4 true. Compute tplus false 5.

Definition tminus (a b: Number) : Number :=
match a, b with
| nNats a, nNats b => match a, b with
											| nNat a, nNat b => if ltb a b
																					then errNat
																					else a - b
											|	_, _ => errNat
											end
| bBools a, bBools b => match a, b with
												| bBool a, bBool b => match a, b with
																							| true, false => 1
																							| false, true => errBool
																							| _, _ => 0
																							end
												| _, _ => errBool
                    		end
| nNats a, bBools b => match a , b with
											 | nNat a, bBool b => match b with
											 											| true => if ltb a 1
											 																then errNum
											 																else a - 1
											 											| false => a
											 											end
											 | _, _ => errNum
											 end
| bBools a, nNats b => match a, b with
											 | bBool a, nNat b => match a with
											 											| true => if ltb 1 b
											 																then errNum
											 																else 1 - b
											 											| false => match b with
											 																| 0 => 0
											 																| _ => errNum
											 																end
											 											end
											 | _, _ => errNum
											 end
| _, _ => errNum
end.

Compute tminus 7 3. Compute tminus true false. 
Compute tminus 8 true. Compute tminus true 8.

Definition tmul (a b: Number) : Number :=
match a, b with
| nNats a, nNats b => match a, b with
											| nNat a, nNat b => a * b
											| _, _ => errNat
											end
| nNats a, bBools b => match a, b with
											| nNat a, bBool b => match b with
																					 | true => a
																					 | false => 0
																					 end
											| _, _ => errNum
									 		end
| nNats a, sStrings b => match a, b with
												| nNat a, sString b => strMul b a
												| _, _ => errNum
												end
| bBools a, nNats b => match a, b with
											| bBool a, nNat b  => match a with
																					 | true => b
																					 | false => 0
																					 end
											| _, _ => errNum
	  									end
| bBools a, bBools b => match a, b with
												| bBool a, bBool b => match a, b with
																						 | true, true => 1
																						 | _, _ => 0
									 													 end
									 			| _, _ => errBool
									 			end
| sStrings a, nNats b => match a, b with
												| sString a, nNat b => strMul a b
												| _, _ => errNum
												end
| _, _ => errNum
end.

Compute tmul 3 4. Compute tmul true true. 
Compute tmul 5 true. Compute tmul 3 "abc". 
Compute tmul false 2. Compute tmul "def" 0.

Definition tdiv (a b: Number) : Number :=
match a, b with 
| nNat a, nNat b => match b with
									| 0 => errNat
									| _ => div a b
									end
| nNat a, bBool b => match b with
									 | true => a
									 | false => errNum
									 end
| bBool a, nNat b => match b with
									 | 0 => errNum
									 | _ => match a with
									 				| true => div 1 b
									 				| false => 0
									 				end
									 end
| bBool a, bBool b => match a, b with
										| true, true => 1
										| false, true => 0
										| _, false => errBool
										end
| _, _ => errNum
end.

Compute tdiv 6 3. Compute tdiv 3 8. Compute tdiv 7 0.
Compute tdiv 4 true. Compute tdiv false 8.
Compute tdiv true false.

Definition tpow (a b: Number) : Number :=
match a, b with
| nNat a, nNat b => match a, b with
									| 0, 0 => errNat
									| _, _ => pow a b
									end
| nNat a, bBool b => match b with
									 | true => a
									 | false => match a with
									 						| 0 => errNum
															| _ => 1
															end
									 end
| bBool a, nNat b => match a with 
									 | true => 1
									 | false => match b with
									 						| 0 => errNum
									 						| _ => 0
									 						end
									 end
| bBool a, bBool b => match a, b with
										| true, _ => 1
										| false, true => 0
										| false, false => errBool
										end
| sString a, nNat b => strMul a b
| _, _ => errNum
end.

Compute tpow 0 0. Compute tpow 2 10. Compute tpow true 5. Compute tpow false true. Compute tpow "a" 3.

Definition tmod (a b: Number) : Number :=
match a, b with
| nNat a, nNat b => match b with 
									| 0 => errNat
									| _ => modulo a b
									end
| nNat a, bBool b => match b with
									| true => 0
									| false => errNum
									end
| bBool a, nNat b => match b with 
									| 0 => errNum
									| _ => match a with
												 | true => modulo 1 b
												 | false => 0
												 end
									end
| bBool a, bBool b => match a, b with
										| _, true => 0
										| _, false => errBool
										end
| _, _ => errNum
end.

Compute tmod 5 3. Compute tmod 5 true. Compute tmod false 0. Compute tmod true true.


(** Boolean-ish Expressions **)


Definition tnot (a : Number) : bool :=
match a with
| nNat a => match a with 
					| 0 => true 
					| _ => false
					end
| bBool a => match a with
						| false => true
						| true => false
						end
| _ => false
end.

Compute tnot 0. Compute tnot 5. Compute tnot true. Compute tnot false. Compute tnot "false".

Definition tand (a b: Number) : bool :=
match a, b with
| nNat a, nNat b => match a, b with
									| _, 0 => false
									| 0, _ => false
									| _, _ => true
									end
| nNat a, bBool b => match a, b with
									| 0, _ => false
									| _, false => false
									| _, _ => true
									end
| nNat a, sString b => match a with
										 | 0 => false
										 | _ => true
										 end
| bBool a, nNat b => match a, b with
									| false, _ => false
									| _, 0 => false
									| _, _ => true
									end
| bBool a, bBool b => match a, b with
										| true, true => true
										| _, _ => false
										end
| bBool a, sString b => a
| sString a, nNat b => match b with
										 | 0 => false
										 | _ => true
										 end
| sString a, bBool b => b
| sString a, sString b => true
| _, _ => false
end.

Compute tand 5 6. Compute tand 3 true. Compute tand 3 "true". Compute tand false 4. Compute tand true false. Compute tand false "false". Compute tand "true" "true".

Definition tor (a b: Number) : bool :=
match a, b with
| nNat a, nNat b => match a, b with
									| 0, 0 => false
									| _, _ => true
									end
| nNat a, bBool b => match a, b with
									 | 0, false => false
									 | _, _ => true
									 end
| nNat a, sString b => true
| bBool a, nNat b => match a, b with
									| false, 0 => false
									| _, _ => true
									end
| bBool a, bBool b => match a, b with
										| false, false => false
										| _, _ => true
										end
| bBool a, sString b => true
| sString a, nNat b => true
| sString a, bBool b => true
| sString a, sString b => true
| _, _ => false
end.

Compute tor 5 6. Compute tor 3 true. Compute tor 3 "true". Compute tor false 0. Compute tor true false. Compute tor false "false". Compute tor "true" "true".

Definition tlt (a b: Number) :=
match a, b with 
| nNat a, nNat b => ltb a b
| nNat a, bBool b => match a, b with
									| 0, true => true
									| _, _ => false
									end
| bBool a, nNat b => match a, b with
									 | false, 0 => false
									 | true, 0 => false
									 | true, 1 => false
									 | _, _ => true
									 end
| bBool a, bBool b => match a, b with
										| false, true => true
										| _, _ => false
										end
| _, _ => false
end.

Compute tlt 3 7. Compute tlt 4 0. Compute tlt true 5. Compute tlt false true.

Definition teq (a b: Number) :=
match a, b with
| nNat a, nNat b => eqb a b
| nNat a, bBool b => match a, b with
									| 1, true => true
									| 0, false => true
									| _, _ => false
									end
| bBool a, nNat b => match a, b with
									| true, 1 => true
									| false, 0 => true
									| _, _ => false
									end
| bBool a, bBool b => match a, b with
										| true, true => true
										| false, false => true
										| _, _ => false
										end
| sString a, sString b => eqb_string a b
| _, _ => false
end.

Compute teq 3 3. Compute teq 1 true. Compute teq false 9. Compute teq true true. Compute teq "abc" "abc". Compute teq "abc" "abv".

Definition tlte (a b: Number) := orb (tlt a b) (teq a b).

Compute tlte 3 4. Compute tlte 0 false. Compute tlte true 7. Compute tlte true false. Compute tlte "abcd" "abcd".

Definition tgt (a b: Number) := tnot (tlte a b).

Compute tgt 3 4. Compute tgt 5 true. Compute tgt false 0. Compute tgt false true.

Definition tgte (a b: Number) := tnot (tlt a b).

Compute tgte 3 4. Compute tgte 5 true. Compute tgte false 0. Compute tgte false true.

Definition tneq (a b: Number) := tnot (teq a b).

Compute tneq 3 3. Compute tneq 1 true. Compute tneq false 9. Compute tneq true true. Compute tneq "abc" "abc". Compute tneq "abc" "abv".

Compute tneq (tgte 2 (tplus true true) ) 2.

Compute (tpow (tmod 12 (tmul true 5) ) (tdiv (tplus 7 (tmul 3 true) ) (tminus true false) ) ).

Compute (tplus "facul" (tplus (tmul "ta" 4 ) "te" ) ).




(** List Functions **)

(* List Examples *)

Definition exNatList := [1 >n 2 >n 3].
Definition exBoolList := [true >b false].
Definition exStringList := ["a" >s "l" >s "e" >s "x"].

(* List Utilities *)

Fixpoint getListLength {T: Type} (l: List T) := 
match l with
| nil => 0
| list _ v l2 => 1 + getListLength l2
end.

Compute getListLength exStringList.

(* List Getters *)

Fixpoint getNatListElement (l: List Nat) (n: nat) :=
match l with
| nil => errNat
| list _ val l' => if (eqb n 0) 
                 then val
                 else getNatListElement l' (n - 1) 
end.

Compute getNatListElement exNatList 1.

Fixpoint getBoolListElement (l: List Bool) (n: nat) :=
match l with
| nil => errBool
| list _ val l' => if (eqb n 0) 
                 then val
                 else getBoolListElement l' (n - 1) 
end.

Compute getBoolListElement exBoolList 1.

Fixpoint getStringListElement (l: List String) (n: nat) :=
match l with
| nil => errString
| list _ val l' => if (eqb n 0) 
                 then val
                 else getStringListElement l' (n - 1) 
end.

Compute getStringListElement exStringList 1.

Fixpoint getArrayListElement (l: List Array) (n: nat) :=
match l with
| nil => errArray
| list _ val l' => if (eqb n 0) 
                 then val
                 else getArrayListElement l' (n - 1) 
end.

Compute getArrayListElement multipleListNBS 1.

(* List Inserts *)

Fixpoint insertNatInList (l: List Nat) (n: nat) (v: Nat) :=
match l with 
| [] => if eqb n 0 
				then list _ v []
				else []
| list _ val l' => if eqb n 0
									 then list _ v (list _ val l')
									 else list _ val (insertNatInList l' (n - 1) v)
end.

Compute insertNatInList exNatList 0 0.

Fixpoint insertBoolInList (l: List Bool) (n: nat) (v: Bool) :=
match l with 
| [] => if eqb n 0 
				then list _ v []
				else []
| list _ val l' => if eqb n 0
									 then list _ v (list _ val l')
									 else list _ val (insertBoolInList l' (n - 1) v)
end.

Compute insertBoolInList exBoolList 1 false.

Fixpoint insertStringInList (l: List String) (n: nat) (v: String) :=
match l with 
| [] => if eqb n 0 
				then list _ v []
				else []
| list _ val l' => if eqb n 0
									 then list _ v (list _ val l')
									 else list _ val (insertStringInList l' (n - 1) v)
end.

Compute insertStringInList exStringList 4 "?".

Fixpoint insertArrayInList (l: List Array) (n: nat) (v: Array) :=
match l with 
| [] => if eqb n 0 
				then list _ v []
				else []
| list _ val l' => if eqb n 0
									 then list _ v (list _ val l')
									 else list _ val (insertArrayInList l' (n - 1) v)
end.

Compute insertArrayInList multipleListNBS 3 multipleArrayNBS.

(* List Deleters *)

Fixpoint deleteFromList {T: Type} (l: List T) (n: nat) :=
match l with 
| [] => []
| list _ val l' => if eqb n 0
									 then l'
									 else list _ val (deleteFromList l' (n - 1) )
end.

Compute deleteFromList exBoolList 1.

Definition deleteNatFromList (l: List Nat) (n: nat) := deleteFromList l n.

Compute deleteNatFromList exNatList 0.

Definition deleteBoolFromList (l: List Bool) (n: nat) := deleteFromList l n.

Compute deleteBoolFromList exBoolList 2.

Definition deleteStringFromList (l: List String) (n: nat) := deleteFromList l n.

Compute deleteStringFromList exStringList 0.

Definition deleteArrayFromList (l: List Array) (n: nat) := deleteFromList l n.

Compute deleteArrayFromList multipleListNBS 1.

(* List Appenders *)

Fixpoint concatLists {T: Type} (l1 l2: List T) :=
match l1 with
| nil => l2
| list _ v l1' => list _ v (concatLists l1' l2)
end.

Compute concatLists [1 >n 2] [3 >n 4].

Definition appendNatToList (l: List Nat) (n: Nat) := insertNatInList l (getListLength l) n.

Compute appendNatToList exNatList 4.

Definition appendBoolToList (l: List Bool) (n: Bool) := insertBoolInList l (getListLength l) n.

Compute appendBoolToList exBoolList true.

Definition appendStringToList (l: List String) (n: String) := insertStringInList l (getListLength l) n.

Compute appendStringToList exStringList "?".

Definition appendArrayToList (l: List Array) (n: Array) := insertArrayInList l (getListLength l) n.

Compute appendArrayToList multipleListNBS (NA exNatList).

(* List Trimmers *)

Definition trimNatList (l: List Nat) := deleteFromList l ( (getListLength l) - 1).

Compute trimNatList exNatList.

Definition trimBoolList (l: List Bool) := deleteFromList l ( (getListLength l) - 1).

Compute trimBoolList exBoolList.

Definition trimStringList (l: List String) := deleteFromList l ( (getListLength l) - 1).

Compute trimStringList exStringList.

Definition trimArrayList (l: List Array) := deleteFromList l ( (getListLength l) - 1).

Compute trimArrayList multipleListNBS.

(* List Setters (for Arrays) *)

Fixpoint setNatListElement (l: List Nat) (n: nat) (v: Nat) :=
match l with
| nil => nil
| list _ val l' => if (eqb n 0)
                   then (list _ v l')
                   else (list _ val (setNatListElement l' (n - 1) v) )
end.

Compute setNatListElement exNatList 1 5.

Fixpoint setBoolListElement (l: List Bool) (n: nat) (v: Bool) :=
match l with
| nil => nil
| list _ val l' => if (eqb n 0)
                   then (list _ v l')
                   else (list _ val (setBoolListElement l' (n - 1) v) )
end.

Compute setBoolListElement exBoolList 1 true.

Fixpoint setStringListElement (l: List String) (n: nat) (v: String) :=
match l with
| nil => nil
| list _ val l' => if (eqb n 0)
                   then (list _ v l')
                   else (list _ val (setStringListElement l' (n - 1) v) )
end.

Compute setStringListElement exStringList 1 "p".

Fixpoint setArrayListElement (l: List Array) (n: nat) (v: Array) :=
match l with
| nil => nil
| list _ val l' => if (eqb n 0)
                   then (list _ v l')
                   else (list _ val (setArrayListElement l' (n - 1) v) )
end.

Compute setArrayListElement multipleListNBS 1 natArray123.

(** Linked Lists Functions **)

Definition getLinkedListLength (l: LinkedList) :=
match l with 
| natList l => getListLength l
| boolList l => getListLength l
| stringList l => getListLength l
| _ => 0
end.

Compute getLinkedListLength (NL exNatList).

Definition getLinkedListElement (l: LinkedList) (n: nat) : Number :=
match l with
| natList l => getNatListElement l n
| boolList l => getBoolListElement l n
| stringList l => getStringListElement l n
| _ => errNum
end.

Compute getLinkedListElement (NL exNatList) 0.

Definition insertLinkedListElement (l: LinkedList) (n: nat) (v: Number) :=
match l, v with
| natList l, nNat v => NL (insertNatInList l n v)
| boolList l, bBool v => BL (insertBoolInList l n v)
| stringList l, sString v => SL (insertStringInList l n v)
| _, _ => l
end.

Compute insertLinkedListElement (BL exBoolList) 1 true.

Definition deleteLinkedListElement (l: LinkedList) (n: nat) :=
match l with
| natList l => NL (deleteNatFromList l n)
| boolList l => BL (deleteBoolFromList l n)
| stringList l => SL (deleteStringFromList l n)
| _ => l
end.

Compute deleteLinkedListElement (SL exStringList) 2.

Definition concatLinkedLists (l1 l2: LinkedList) :=
match l1, l2 with
| natList l1, natList l2 => NL (concatLists l1 l2)
| boolList l1, boolList l2 => BL (concatLists l1 l2)
| stringList l1, stringList l2 => SL (concatLists l1 l2)
| _, _ => l1
end.

Compute concatLinkedLists (NL exNatList) (NL exNatList).

Definition appendToLinkedList (l: LinkedList) (v: Number) :=
match l, v with
| natList l, nNat v => NL (appendNatToList l v)
| boolList l, bBool v => BL (appendBoolToList l v)
| stringList l, sString v => SL (appendStringToList l v)
| _, _ => l
end.

Compute appendToLinkedList (SL exStringList) "!". 

Definition trimLinkedList (l: LinkedList) :=
match l with
| natList l => NL (trimNatList l)
| boolList l => BL (trimBoolList l)
| stringList l => SL (trimStringList l)
| _ => l
end.

Compute trimLinkedList (NL exNatList).

(** Array Functions **)



(* Array Utilities *)

Definition getArrayLength (a: Array) :=
match a with
| natArray l => getListLength l
| boolArray l => getListLength l
| stringArray l => getListLength l
| multipleArray l => getListLength l
| _ => 0
end.

Compute getArrayLength natArray123.

(* Array Concat *)

Definition concatArrays (a1 a2: Array) :=
match a1, a2 with
| natArray l1, natArray l2 => natArray (concatLists l1 l2)
| boolArray l1, boolArray l2 => boolArray (concatLists l1 l2)
| stringArray l1, stringArray l2 => stringArray (concatLists l1 l2)
| multipleArray l1, multipleArray l2 => multipleArray (concatLists l1 l2)
| _, _ => a1
end.

Compute concatArrays boolArrayTFT boolArrayTFT.


(* Array Getter *)

Definition getArrayElement (a: Array) (n: nat) : ResultTypes :=
match a with
| natArray l => nNats (getNatListElement l n)
| boolArray l => bBools (getBoolListElement l n)
| stringArray l => sStrings (getStringListElement l n)
| multipleArray l => arrays (getArrayListElement l n)
| _ => error
end.

Compute getArrayElement multipleArrayNBS 2.

Notation "'getA' A [' B ']" := (getArrayElement A B).

(* Array Setter *)

Definition setArrayElement (a: Array) (n: nat) (v: ResultTypes) :=
match a, v with
| natArray l, nNats v => NA (setNatListElement l n v)
| boolArray l, bBools v => BA (setBoolListElement l n v)
| stringArray l, sStrings v => SA (setStringListElement l n v)
| multipleArray l, arrays v => MA (setArrayListElement l n v)
| _, _ => a
end.

Compute setArrayElement natArray123 2 4.
Compute setArrayElement multipleArrayNBS 2 boolArrayTFT.
(**********************************)

(* Array Back Pusher *)

Definition pushBackArray (a: Array) (n: ResultTypes) :=
match a, n with 
| NA l, nNats n => NA (insertNatInList l (getListLength l) n)
| BA l, bBools n => BA (insertBoolInList l (getListLength l) n)
| SA l, sStrings n => SA (insertStringInList l (getListLength l) n)
| MA l, arrays n => MA (insertArrayInList l (getListLength l) n)
| _, _ => a
end.

Compute pushBackArray boolArrayTFT false.

(* Array Front Pushers *)

Definition pushFrontArray (a: Array) (n: ResultTypes) :=
match a, n with 
| NA l, nNats n => NA (insertNatInList l 0 n)
| BA l, bBools n => BA (insertBoolInList l 0 n)
| SA l, sStrings n => SA (insertStringInList l 0 n)
| MA l, arrays n => MA (insertArrayInList l 0 n)
| _, _ => a
end.

Compute pushFrontArray stringArrayPLP "?".

(* Array Back Pop *)

Definition popBackArray (a: Array) :=
match a with 
| NA l => NA (deleteNatFromList l ( (getListLength l) - 1) )
| BA l => BA (deleteBoolFromList l ( (getListLength l) - 1) )
| SA l => SA (deleteStringFromList l ( (getListLength l) - 1) )
| MA l => MA (deleteArrayFromList l ( (getListLength l) - 1) )
| _ => a
end.

Compute popBackArray multipleArrayNBS.

(* Array Front Pop *)

Definition popFrontArray (a: Array) :=
match a with 
| NA l => NA (deleteNatFromList l 0 )
| BA l => BA (deleteBoolFromList l 0 )
| SA l => SA (deleteStringFromList l 0 )
| MA l => MA (deleteArrayFromList l 0 )
| _ => a
end.

Compute popFrontArray natArray123.

(** Enum Functions **)

(* Enum Utilities *)

Definition getEnumLength (e: Enum) :=
match e with
| EN l => getListLength l
end.


(* Enum Setter *)

Fixpoint setEnumListElement (l: List Number) (n: nat) (v: Number) :=
match l with
| nil => nil
| list _ val l' => if (eqb n 0)
                   then (list _ v l')
                   else (list _ val (setEnumListElement l' (n - 1) v) )
end.

Definition setEnumElement (e: Enum) (n: nat) (v: Number) :=
match e with
| EN l => EN (setEnumListElement l n v)
end.

(* Enum Getter *)

Fixpoint getEnumListElement (l: List Number) (n: nat) :=
match l with
| nil => error
| list _ val l' => if (eqb n 0) 
                 then val
                 else getEnumListElement l' (n - 1) 
end.

Definition getEnumElement (e: Enum) (n: nat) :=
match e with
| EN l => getEnumListElement l n
end.

(* Enum Back Push *)

Fixpoint insertEnumInList (l: List Number) (n: nat) (v: Number) :=
match l with 
| [] => if eqb n 0 
				then list _ v []
				else []
| list _ val l' => if eqb n 0
									 then list _ v (list _ val l')
									 else list _ val (insertEnumInList l' (n - 1) v)
end.

Definition pushBackEnum (e: Enum) (n: Number) :=
match e with 
| EN l => EN (insertEnumInList l (getListLength l) n)
end.


(* Enum Front Push *)

Definition pushFrontEnum (e: Enum) (n: Number) :=
match e with 
| EN l => EN (insertEnumInList l 0 n)
end.


(* Enum Back Pop *)

Definition deleteEnumFromList (l: List Number) (n: nat) := deleteFromList l n.

Definition popBackEnum (e: Enum) :=
match e with 
| EN l => EN (deleteEnumFromList l ( (getListLength l) - 1) )
end.


(* Enum Front Pop *)

Definition popFrontEnum (e: Enum) :=
match e with 
| EN l => EN (deleteEnumFromList l 0 )
end.




(** Struct Functions **)

(* Struct Setter *)

Definition matchField (f: Field) (s: string) :=
match f with
| field n v => if string_beq n s 
							 then true
							 else false
end.

Fixpoint replaceFieldValue (lf: List Field) (s: string) (v: FieldTypes) :=
match lf with 
| nil => nil
| list _ fld l' => if matchField fld s
									 then list _ (field s v) l'
									 else list _ fld (replaceFieldValue l' s v)
end.

Definition structSetElement (s: Struct) (f: string) (v: FieldTypes) := 
match s with
| struct l => struct (replaceFieldValue l f v)
end.


(* Struct Getter *)

Definition getValue (f: Field) :=
match f with
| field s v => v
end.

Fixpoint getFieldValue (lf: List Field) (s: string) :=
match lf with
| nil => notFound
| list _ fld l' => if matchField fld s 
									 then getValue fld
									 else getFieldValue l' s
end.

Definition getStructValue (s: Struct) (f: string) :=
match s with
| struct lf => getFieldValue lf f
end.









Notation "'Default' ':d' S" := (caseDefault S) (at level 60).
Notation "'Case' E ':c' S" := (case E S) (at level 60).
Notation "'Switch' 's(' E ')s' '{\' C1 ';;/' .. ';;/' C2 '/}'" := (switchCase E (list Pair C1 .. (list Pair C2 []) .. ) ) (at level 45).

Definition getPairSwitch (P : Pair) : Statement :=
match P with
| Default :d s => s
| Case x :c s => s
end.

Definition checkPairSwitch (P : Pair) (n : Number) : bool :=
match P with
| Default :d _ => true
| Case x :c s => teq x n
end.

Fixpoint getSwitchCase (n: Number) (l: List Pair) : Statement :=
match l with
| list _ v l1 => match v with
								| Default :d s => s
								| _ => if (checkPairSwitch v n)
								 			 then (getPairSwitch v)
								 			 else (getSwitchCase n l1)
								end
| _ => emptyStatement
end.


(*** Environment Setup ***)



Definition Environment := string -> ResultTypes.

Definition InitialEnvironment : Environment := fun _ => undeclared.

Definition default (x: ResultTypes) : Environment := fun _ => x.

Definition update (env: Environment) (s: string) (v: ResultTypes) :=
fun x => if (eqb_string x s)
         then v
         else env x.

Definition env1 := update InitialEnvironment "a1" natArray123.

Compute env1 "a1".

Fixpoint Exp_Eval (exp : Exp) (env: Environment) : Number := 
match exp with
| anum n => n
| avar v => match env v with
						| numbers n => n
						| _ => errNum
						end
| a1 +' a2 => tplus (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 -' a2 => tminus (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 *' a2 => tmul (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 /' a2 => tdiv (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 ^' a2 => tpow (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 %' a2 => tmod (Exp_Eval a1 env) (Exp_Eval a2 env)
| !' b => tnot (Exp_Eval b env)
| b1 &&' b2 => tand (Exp_Eval b1 env) (Exp_Eval b2 env)
| b1 ||' b2 => tor (Exp_Eval b1 env) (Exp_Eval b2 env)
| a1 <' a2 => tlt (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 <=' a2 => tlte (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 >' a2 => tgt (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 >=' a2 => tgte (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 ==' a2 => teq (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 !=' a2 => tneq (Exp_Eval a1 env) (Exp_Eval a2 env)
end.

Compute tplus 2  3.
Compute Exp_Eval (1 +' 2 *' 3 -' 4 /' 5 ^' 6) InitialEnvironment.

(** SmallStep apparently **)

Reserved Notation "E =[ S ]=> E'" (at level 60).
Inductive Exp_Eval_Prop : Exp -> Environment -> Exp -> Prop :=
| const: forall n st, anum n =[ st ]=> n
| lookup: forall x st, avar x =[ st ]=> match (st x) with
																				| nNat n => n
																				| bBool b => b
																				| sString s => s
																				| _ => errNum
																				end
(* plus *)

| plusLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' +' a2 ->
    ( a1 +' a2 ) =[ st ]=> a
| plusRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 +' a2' ->
    ( a1 +' a2 ) =[ st ]=> a
| plusCons: forall i (i1 i2: Number) st,
    i = tplus i1 i2 ->
    ( (anum i1) +' (anum i2) ) =[ st ]=> i

(* minus *)

| minusLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' -' a2 ->
    ( a1 -' a2 ) =[ st ]=> a
| minusRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 -' a2' ->
    ( a1 -' a2 ) =[ st ]=> a
| minusCons: forall i (i1 i2: Number) st,
    i = tminus i1 i2 ->
    ( (anum i1) -' (anum i2) ) =[ st ]=> i

(* mul *)

| mulLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' *' a2 ->
    ( a1 *' a2 ) =[ st ]=> a
| mulRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 *' a2' ->
    ( a1 *' a2 ) =[ st ]=> a
| mulCons: forall i (i1 i2: Number) st,
    i = tmul i1 i2 ->
    ( (anum i1) *' (anum i2) ) =[ st ]=> i

(* div *)

| divLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' /' a2 ->
    ( a1 /' a2 ) =[ st ]=> a
| divRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 /' a2' ->
    ( a1 /' a2 ) =[ st ]=> a
| divCons: forall i (i1 i2: Number) st,
    i = tdiv i1 i2 ->
    ( (anum i1) /' (anum i2) ) =[ st ]=> i

(* power *)

| powLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' ^' a2 ->
    ( a1 ^' a2 ) =[ st ]=> a
| powRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 ^' a2' ->
    ( a1 ^' a2 ) =[ st ]=> a
| powCons: forall i (i1 i2: Number) st,
    i = tpow i1 i2 ->
    ( (anum i1) ^' (anum i2) ) =[ st ]=> i

(* mod *)

| modLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' %' a2 ->
    ( a1 %' a2 ) =[ st ]=> a
| modRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 %' a2' ->
    ( a1 %' a2 ) =[ st ]=> a
| modCons: forall i (i1 i2: Number) st,
    i = tmod i1 i2 ->
    ( (anum i1) %' (anum i2) ) =[ st ]=> i

(* BOOL *)

| ptrue: forall st, true =[ st ]=> true
| pfalse: forall st, false =[ st ]=> false

(* not *)

| not: forall b b' st,
    b =[ st ]=> b' ->
    (bnot b) =[ st ]=> (bnot b')
| notTrue: forall st,
    (bnot true) =[ st ]=> false
| notFalse: forall st,
    (bnot false) =[ st ]=> true

(* and *)

| and: forall b1 b1' b2 st,
    b1 =[ st ]=> b1' ->
    (b1 &&' b2) =[ st ]=> (b1' &&' b2) 
| andTrue : forall b2 st,
    (true &&' b2) =[ st ]=> b2
| andFalse : forall b2 st,
    (false &&' b2) =[ st ]=> false

(* or *)

| or: forall b1 b1' b2 st,
    b1 =[ st ]=> b1' ->
    (b1 ||' b2) =[ st ]=> (b1' ||' b2) 
| orTrue: forall b2 st,
    (true ||' b2) =[ st ]=> true
| orFalse: forall b2 st,
    (false ||' b2) =[ st ]=> b2

(* less *)

| lessThanLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    (a1 <' a2) =[ st ]=> (a1' <' a2)
| lessThanRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    ( (anum i1) <' a2) =[ st ]=> ( (anum i1) <' a2')
| lessThan : forall b (i1 i2: Number) st,
    b = (if (tlt i1 i2) then true else false) ->
    ( (anum i1) <' (anum i2) ) =[ st ]=> b

(* less equal *)

| lessEqualThanLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    ( a1 <=' a2 ) =[ st ]=> ( a1' <=' a2 )
| lessEqualThanRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    ( (anum i1) <=' a2 ) =[ st ]=> ( (anum i1) <=' a2' )
| lessEqualThan : forall b (i1 i2: Number) st,
    b = (if (tlte i1 i2) then true else false) ->
    ( (anum i1) <=' (anum i2) ) =[ st ]=> b

(* greater *)

| greaterThanLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    (a1 >' a2) =[ st ]=> (a1' >' a2)
| greaterThanRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    ( (anum i1) >' a2) =[ st ]=> ( (anum i1) >' a2' )
| greaterThan : forall b (i1 i2: Number) st,
    b = (if (tgt i1 i2) then true else false) ->
    ( i1 >' i2 ) =[ st ]=> b

(* greater equal *)

| greaterEqualThanLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    (a1 >=' a2) =[ st ]=> (a1' >=' a2)
| greaterEqualThanRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    ( (anum i1) >=' a2) =[ st ]=> ( (anum i1) >=' a2' )
| greaterEqualThan: forall b (i1 i2: Number) st,
    b = (if (tgte i1 i2) then true else false) ->
    (i1 >=' i2) =[ st ]=> b

(* equal *)

| equalLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    (a1 ==' a2) =[ st ]=> (a1' ==' a2)
| equalRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    ( (anum i1) ==' a2 ) =[ st ]=> ( (anum i1) ==' a2' )
| equal: forall b (i1 i2: Number) st,
    b = (if (teq i1 i2) then true else false) ->
    ( (anum i1) ==' (anum i2) ) =[ st ]=> b

(* not equal *)

| notEqualLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    ( a1 !=' a2 ) =[ st ]=> ( a1' !=' a2 )
| notEqualRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    ( (anum i1) !=' a2 ) =[ st ]=> ( (anum i1) !=' a2' )
| notEqual: forall b (i1 i2: Number) st,
    b = (if (tneq i1 i2) then true else false) ->
    ( (anum i1) !=' (anum i2) ) =[ st ]=> b
where "E =[ S ]=> E'" := (Exp_Eval_Prop E S E').

Definition env2 := update (update (update InitialEnvironment "a" 13) "b" 8) "c" 5.

Example e0: avar "a" =[ env2 ]=> 13.
Proof.
eapply lookup.
Qed.

Example e1: ( ("a" -' "b") <=' "c" ) =[ env2 ]=> ( (13 -' "b") <=' "c" ).
Proof.
eapply lessEqualThanLeft. eapply minusLeft.
- eapply lookup.
- simpl. reflexivity.
Qed.

Example e2: ( (13 -' "b") <=' "c" ) =[ env2 ]=> ( (13 -' 8) <=' "c" ).
Proof.
eapply lessEqualThanLeft. eapply minusRight.
- eapply lookup.
- simpl. reflexivity.
Qed.

Example e3: ( (13 -' 8) <=' "c" ) =[ env2 ]=> ( 5 <=' "c" ).
Proof.
eapply lessEqualThanLeft. eapply minusCons. simpl. reflexivity.
Qed.

Example e4: ( 5 <=' "c" ) =[ env2 ]=> ( 5 <=' 5 ).
Proof.
eapply lessEqualThanRight. eapply lookup.
Qed.

Example e5: ( 5 <=' 5 ) =[ env2 ]=> true.
Proof.
eapply lessEqualThan. simpl. reflexivity.
Qed.

(** BigStep SOS **)

Reserved Notation "A ={ S }=> N" (at level 60).
Inductive Big_Exp_Eval_Prop : Exp -> Environment -> Number -> Prop :=
| b_const: forall n sigma, anum n ={ sigma }=> n
| b_var: forall v sigma, avar v ={ sigma }=> match (sigma v) with
																					| nNat n => n
																					| bBool b => b
																					| sString s => s
																					| _ => errNum
																					end

| b_add: forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = tplus i1 i2 ->
    a1 +' a2 ={ sigma }=> n

| b_mul: forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = tmul i1 i2 ->
    a1 *' a2 ={ sigma }=> n

| b_minus: forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = tminus i1 i2 ->
    a1 -' a2 ={ sigma }=> n

| b_div: forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = tdiv i1 i2 ->
    a1 /' a2 ={ sigma }=> n

| b_pow: forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = tpow i1 i2 ->
    a1 ^' a2 ={ sigma }=> n

| b_mod: forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = tmod i1 i2 ->
    a1 %' a2 ={ sigma }=> n

| b_not : forall a i sigma n,
 		a ={ sigma }=> i ->
    n = (tnot i) ->
    (!' a) ={ sigma }=> n

| b_and : forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = (tand i1 i2) ->
    (a1 &&' a2) ={ sigma }=> n

| b_or : forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = (tor i1 i2) ->
    (a1 ||' a2) ={ sigma }=> n

| b_lessthan : forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = (tlt i1 i2) ->
    (a1 <' a2) ={ sigma }=> n

| b_lessequalthan : forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = (tlte i1 i2) ->
    (a1 <=' a2) ={ sigma }=> n

| b_greaterthan : forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = (tgt i1 i2) ->
    (a1 >' a2) ={ sigma }=> n

| b_greaterthanequal : forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = (tgte i1 i2) ->
    (a1 >=' a2) ={ sigma }=> n

| b_equal : forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = (teq i1 i2) ->
    (a1 ==' a2) ={ sigma }=> n

| b_not_equal : forall a1 a2 i1 i2 sigma n,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    n = (tneq i1 i2) ->
    (a1 !=' a2) ={ sigma }=> n

where "a ={ sigma }=> n" := (Big_Exp_Eval_Prop a sigma n).

Definition env3 := update (update (update (default 0) "x" 12) "y" 6) "z" 3.

Example e6: ( ( "x" /' ( "z" +' true *' "y" -' ( 2^'3 /' 2 +' (!' false) ) +' 2^'3 ) ) *' "z"^'2 ) ={ env3 }=> 9.
Proof.
eapply b_mul.
- eapply b_div.
	-- eapply b_var.
	-- eapply b_add.
		--- eapply b_minus.
			---- eapply b_add.
				----- eapply b_var.
				----- eapply b_mul.
					------ eapply b_const.
					------ eapply b_var.
					------ simpl. reflexivity.
				----- simpl. reflexivity.
			---- eapply b_add.
				----- eapply b_div.
					------ eapply b_pow.
						------- eapply b_const.
						------- eapply b_const.
						------- simpl. reflexivity.
					------ eapply b_const.
					------ simpl. reflexivity.
				----- eapply b_not.
					------ eapply b_const.
					------ simpl. reflexivity.
				----- simpl. reflexivity.
			---- simpl. reflexivity.
		--- eapply b_pow.
			---- eapply b_const.
			---- eapply b_const.
			---- simpl. reflexivity.
		--- simpl. reflexivity.
	-- simpl. reflexivity.
- eapply b_pow.
	-- eapply b_var.
	-- eapply b_const.
	-- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Reserved Notation "a ~{ sigma }~> sigma'" (at level 60).
Inductive Big_Stmt_Eval_Prop : Statement -> Environment -> Environment -> Prop :=

| b_decNatVar: forall n sigma sigma',
	sigma' = (update sigma n unassignedNat) ->
 (NVar n) ~{ sigma }~> sigma'

| b_decBoolVar: forall n sigma sigma',
	sigma' = (update sigma n unassignedBool) ->
 (BVar n) ~{ sigma }~> sigma'

| b_decStringVar: forall n sigma sigma',
	sigma' = (update sigma n unassignedString) ->
 (SVar n) ~{ sigma }~> sigma'

| b_asnNatVar: forall n x (i: Nat) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = update sigma n i ->
	(n <n- x) ~{ sigma }~> sigma'

| b_asnBoolVar: forall n x (i: Bool) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = update sigma n i ->
	(n <b- x) ~{ sigma }~> sigma'

| b_asnStringVar: forall n x (i: String) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = update sigma n i ->
	(n <s- x) ~{ sigma }~> sigma'

| b_initNatVar: forall n x (i: Nat) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = update sigma n i ->
	(NLet n :n: x) ~{ sigma }~> sigma'

| b_initBoolVar: forall n x (i: Bool) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = update sigma n i ->
	(BLet n :b: x) ~{ sigma }~> sigma'

| b_initStringVar: forall n x (i: String) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = update sigma n i ->
	(SLet n :s: x) ~{ sigma }~> sigma'

| b_decNatList: forall n sigma sigma',
	sigma' = (update sigma n unassignedNatList) ->
 (NLst n) ~{ sigma }~> sigma'

| b_decBoolList: forall n sigma sigma',
	sigma' = (update sigma n unassignedBoolList) ->
 (BLst n) ~{ sigma }~> sigma'

| b_decStringList: forall n sigma sigma',
	sigma' = (update sigma n unassignedStringList) ->
 (SLst n) ~{ sigma }~> sigma'

| b_initNatList: forall n (i: LinkedList) sigma sigma',
	sigma' = match i with 
					| natList i' => update sigma n i 
					| _ => sigma 
					end ->
	(LetNLst n :<n>: i) ~{ sigma }~> sigma'

| b_initBoolList: forall n (i: LinkedList) sigma sigma',
	sigma' = match i with 
					| boolList i' => update sigma n i 
					| _ => sigma 
					end ->
	(LetBLst n :<b>: i) ~{ sigma }~> sigma'

| b_initStringList: forall n (i: LinkedList) sigma sigma',
	sigma' = match i with 
					| natList i' => update sigma n i 
					| _ => sigma 
					end ->
	(LetSLst n :<s>: i) ~{ sigma }~> sigma'

| b_asnList: forall l1 l2 sigma sigma',
	sigma' = match sigma l1, l2 with
					| natList li, natList lii => update sigma l1 l2
					| boolList li, boolList lii => update sigma l1 l2
					| stringList li, stringList lii => update sigma l1 l2
					| _, _ => sigma
					end ->
	( l1 :<: l2 ) ~{ sigma }~> sigma'

| b_insInList: forall l n (v: Number) sigma sigma',
	sigma' = match sigma l with 
					| lists l' => update sigma l (insertLinkedListElement l' n v)
					| _ => sigma
					end ->
	(l ins <' n '> <' v '> ) ~{ sigma }~> sigma'

| b_appToList: forall l a (i: Number) sigma sigma',
	a ={ sigma }=> i ->
	sigma' = match sigma l, i with 
					| lists l', _ => update sigma l (appendToLinkedList l' i)
					| unassignedNatList, nNat n => update sigma l ( NL (insertNatInList [] 0 n ) )
					| unassignedBoolList, bBool n => update sigma l ( BL (insertBoolInList [] 0 n ) )
					| unassignedStringList, sString n => update sigma l ( SL (insertStringInList [] 0 n ) )
					| _, _ => sigma
					end ->
	(l <+l a) ~{ sigma }~> sigma'

| b_concList: forall l1 l2 sigma sigma',
	sigma' = match sigma l1 with
					| lists l1' => match sigma l2 with
												| lists l2' => update sigma l1 (concatLinkedLists l1' l2')
												| _ => sigma
												end
					| _ => sigma
					end ->
	(l1 +l+ l2) ~{ sigma }~> sigma'

| b_delFromList: forall l (i: nat) sigma sigma',
	sigma' = match sigma l with
					| lists l' => update sigma l (deleteLinkedListElement l' i)
					| _ => sigma
					end ->
	( l del <' i '>) ~{ sigma }~> sigma'

| b_trList: forall l sigma sigma',
	sigma' = match sigma l with
					| lists l' => update sigma l (trimLinkedList l')
					| _ => sigma
					end ->
	( trim l ) ~{ sigma }~> sigma'

| b_decNatArray: forall n sigma sigma',
	sigma' = (update sigma n unassignedNatArray) ->
 (NArr n) ~{ sigma }~> sigma'

| b_decBoolArray: forall n sigma sigma',
	sigma' = (update sigma n unassignedBoolArray) ->
 (BArr n) ~{ sigma }~> sigma'

| b_decStringArray: forall n sigma sigma',
	sigma' = (update sigma n unassignedStringArray) ->
 (SArr n) ~{ sigma }~> sigma'

| b_decMultipleArray: forall n sigma sigma',
	sigma' = (update sigma n unassignedMultipleArray) ->
 (MArr n) ~{ sigma }~> sigma'

| b_initNatArray: forall n (i: Array) sigma sigma',
	sigma' = match i with 
					| natArray i' => update sigma n i 
					| _ => sigma 
					end ->
	(LetNArr n :[n]: i) ~{ sigma }~> sigma'

| b_initBoolArray: forall n (i: Array) sigma sigma',
	sigma' = match i with 
					| boolArray i' => update sigma n i 
					| _ => sigma 
					end ->
	(LetBArr n :[b]: i) ~{ sigma }~> sigma'

| b_initStringArray: forall n (i: Array) sigma sigma',
	sigma' = match i with 
					| stringArray i' => update sigma n i 
					| _ => sigma 
					end ->
	(LetSArr n :[s]: i) ~{ sigma }~> sigma'

| b_initMultipleArray: forall n (i: Array) sigma sigma',
	sigma' = match i with 
					| multipleArray i' => update sigma n i 
					| _ => sigma 
					end ->
	(LetMArr n :[a]: i) ~{ sigma }~> sigma'

| b_asnArray: forall a1 a2 sigma sigma',
	sigma' = match sigma a1, a2 with
					| natArray li, natArray lii => update sigma a1 a2
					| boolArray li, boolArray lii => update sigma a1 a2
					| stringArray li, stringArray lii => update sigma a1 a2
					| multipleArray li, multipleArray lii => update sigma a1 a2
					| _, _ => sigma
					end ->
	( a1 :[: a2 ) ~{ sigma }~> sigma'

| b_stArrayNumber: forall a (n: nat) x (i: Number) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = match sigma a with
					| arrays a' => update sigma a (setArrayElement a' n i)
					| _ => sigma
					end ->
	( a [' n '] <[n- x ) ~{ sigma }~> sigma'

| b_stArrayArray: forall a (n: nat) (i: Array) sigma sigma',
	sigma' = match sigma a with
					| arrays a' => update sigma a (setArrayElement a' n i)
					| _ => sigma
					end ->
	( a [' n '] <[a- i ) ~{ sigma }~> sigma'

| b_pshFrontArrayNumber: forall a x (i: Number) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = match sigma a, i with
					| arrays a', _ => update sigma a (pushFrontArray a' i)
					| unassignedNatArray, nNat n => update sigma a ( NA ( insertNatInList [] 0 n ) )
					| unassignedBoolArray, bBool n => update sigma a ( BA ( insertBoolInList [] 0 n ) )
					| unassignedStringArray, sString n => update sigma a ( SA ( insertStringInList [] 0 n ) )
					| _, _ => sigma
					end ->
	( a >+n x ) ~{ sigma }~> sigma'

| b_pshFrontArrayArray: forall a (i: Array) sigma sigma',
	sigma' = match sigma a with
					| arrays a' => update sigma a (pushFrontArray a' i)
					| _ => sigma
					end ->
	( a >+a i ) ~{ sigma }~> sigma'

| b_pshBackArrayNumber: forall a x (i: Number) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = match sigma a, i with
					| arrays a' , _ => update sigma a (pushBackArray a' i)
					| unassignedNatArray, nNat n => update sigma a ( NA ( insertNatInList [] 0 n ) )
					| unassignedBoolArray, bBool n => update sigma a ( BA ( insertBoolInList [] 0 n ) )
					| unassignedStringArray, sString n => update sigma a ( SA ( insertStringInList [] 0 n ) )
					| _, _ => sigma
					end ->
	( a <+n x ) ~{ sigma }~> sigma'

| b_pshBackArrayArray: forall a (i: Array) sigma sigma',
	sigma' = match sigma a with
					| arrays a' => update sigma a (pushBackArray a' i)
					| _ => sigma
					end ->
	( a <+a i ) ~{ sigma }~> sigma'

| b_ppFrontArray: forall a sigma sigma',
	sigma' = match sigma a with
					| arrays a' => update sigma a (popFrontArray a')
					| _ => sigma
					end ->
	( popf a ) ~{ sigma }~> sigma'

| b_ppBackArray: forall a sigma sigma',
	sigma' = match sigma a with
					| arrays a' => update sigma a (popBackArray a')
					| _ => sigma
					end ->
	( popb a ) ~{ sigma }~> sigma'

| b_decEnum: forall n sigma sigma',
	sigma' = (update sigma n unassignedEnum) ->
 (dEnum n) ~{ sigma }~> sigma'

| b_initEnum: forall n (i: Enum) sigma sigma',
	sigma' = update sigma n i ->
	(LetEnum n :[e]: i) ~{ sigma }~> sigma'

| b_pshFrontEnum: forall n x (i: Number) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = match sigma n with
					| enums e' => update sigma n (pushFrontEnum e' i)
					| unassignedEnum => update sigma n ( EN (insertEnumInList [] 0 i ) )
					| _ => sigma
					end ->
	( n >+e x ) ~{ sigma }~> sigma'

| b_pshBackEnum: forall n x (i: Number) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = match sigma n with
					| enums e' => update sigma n (pushBackEnum e' i)
					| unassignedEnum => update sigma n ( EN (insertEnumInList [] 0 i ) )
					| _ => sigma
					end ->
	( n <+e x ) ~{ sigma }~> sigma'

| b_ppFrontEnum: forall n sigma sigma',
	sigma' = match sigma n with
					| enums e' => update sigma n (popFrontEnum e')
					| _ => sigma
					end ->
	( n >-e ) ~{ sigma }~> sigma'

| b_ppBackEnum: forall n sigma sigma',
	sigma' = match sigma n with
					| enums e' => update sigma n (popBackEnum e')
					| _ => sigma
					end ->
	( n <-e ) ~{ sigma }~> sigma'

| b_stEnum: forall e (n: nat) x (i: Number) sigma sigma',
	x ={ sigma }=> i ->
	sigma' = match sigma e with
					| enums e' => update sigma e (setEnumElement e' n i)
					| _ => sigma
					end ->
	( e [' n '] <e- x ) ~{ sigma }~> sigma'

| b_initStruct: forall n (s: Struct) sigma sigma',
	sigma' = match sigma n with
					| undeclared => update sigma n s 
					| _ => sigma
					end ->
	( LetStruct n :{s}: s ) ~{ sigma }~> sigma'

| b_stStructField: forall s f (fld: FieldTypes) sigma sigma',
	sigma' = match sigma s with
					| structs s' => update sigma s (structSetElement s' f fld)
					| _ => sigma
					end ->
	( s {\ f /} fld ) ~{ sigma }~> sigma'

| true_ifThen: forall x s1 sigma sigma',
	x ={ sigma }=> true ->
	s1 ~{ sigma }~> sigma' ->
	( ifThen x s1 ) ~{ sigma }~> sigma'

| false_ifThen: forall x s1 sigma,
	x ={ sigma }=> false ->
	( ifThen x s1 ) ~{ sigma }~> sigma

| true_ifThenElse: forall x s1 s2 sigma sigma1,
	x ={ sigma }=> true ->
	s1 ~{ sigma }~> sigma1 ->
	( ifThenElse x s1 s2 ) ~{ sigma }~> sigma1

| false_ifThenElse: forall x s1 s2 sigma sigma2,
	x ={ sigma }=> false ->
	s2 ~{ sigma }~> sigma2 ->
	( ifThenElse x s1 s2 ) ~{ sigma }~> sigma2

| true_doWhileLoop: forall x s sigma sigma1 sigma2,
	s ~{ sigma }~> sigma1 ->
	x ={ sigma1 }=> true ->
	( doWhileLoop s x ) ~{ sigma1 }~> sigma2 -> 
	( doWhileLoop s x ) ~{ sigma }~> sigma2

| false_doWhileLoop: forall x s sigma sigma1,
	s ~{ sigma }~> sigma1 ->
	x ={ sigma1 }=> false -> 
	( doWhileLoop s x ) ~{ sigma }~> sigma1

| true_whileLoop: forall x s sigma sigma',
	x ={ sigma }=> true ->
	( s ;; whileLoop x s ) ~{ sigma }~> sigma' ->
	( whileLoop x s ) ~{ sigma }~> sigma'

| false_whileLoop: forall x s sigma,
	x ={ sigma }=> false ->
	( whileLoop x s ) ~{ sigma }~> sigma

| true_forLoop: forall s1 x s2 s3 sigma sigma1 sigma2,
	s1 ~{ sigma }~> sigma1 ->
	x ={ sigma1 }=> true ->
	( whileLoop x ( s3 ;; s2 ) ) ~{ sigma1 }~> sigma2 ->
	( forLoop s1 x s2 s3 ) ~{ sigma }~> sigma2

| false_forLoop: forall s1 x s2 s3 sigma sigma1,
	s1 ~{ sigma }~> sigma1 ->
	x ={ sigma1 }=> false ->
	( forLoop s1 x s2 s3 ) ~{ sigma }~> sigma1

| b_sequence: forall s1 s2 sigma sigma1 sigma2,
	s1 ~{ sigma }~> sigma1 ->
	s2 ~{ sigma1 }~> sigma2 ->
	( s1 ;; s2 ) ~{ sigma }~> sigma2

| continue_sequence1: forall s2 sigma sigma1,
	s2 ~{ sigma }~> sigma1 ->
	( Continue ;; s2 ) ~{ sigma }~> sigma

| continue_sequence2: forall s1 sigma sigma1,
	s1 ~{ sigma }~> sigma1 ->
	( s1 ;; Continue ) ~{ sigma }~> sigma1

| b_switch: forall a l sigma n v sigma',
  a ={ sigma }=> n ->
  v = (getSwitchCase n l) ->
  v ~{ sigma }~> sigma' ->
  switchCase a l ~{ sigma }~> sigma'

where "a ~{ sigma }~> sigma'" := (Big_Stmt_Eval_Prop a sigma sigma').

Definition program :=
dEnum "solution" ;; 
"solution" >+e 5 ;; 
"solution" <+e true.

Definition env00 := update ( update ( update InitialEnvironment "solution" unassignedEnum ) "solution" ( popBackEnum ( EN [5 >e true] ) ) ) "solution" ( EN [5 >e true] ).

Example e7 : program ~{ InitialEnvironment }~> env00.
Proof.
unfold program.
repeat eapply b_sequence.
	- eapply b_decEnum. reflexivity.
	- eapply b_pshFrontEnum.
		-- eapply b_const.
		-- simpl. reflexivity.
	- eapply b_pshBackEnum.
		-- eapply b_const.
		-- simpl. reflexivity.
Qed.

Example e8 : exists sigma0, program ~{ InitialEnvironment }~> sigma0 /\ sigma0 "solution" = ( EN [5 >e true] ).
Proof.
eexists. unfold program. split.
- repeat eapply b_sequence.
	-- eapply b_decEnum. reflexivity.
	-- eapply b_pshFrontEnum.
		--- eapply b_const.
		--- simpl. reflexivity.
	-- eapply b_pshBackEnum.
		--- eapply b_const.
		--- simpl. reflexivity.
- reflexivity.
Qed.

Definition programVar := 
NVar "x" ;; "x" <n- 2 ;;
BLet "y" :b: true ;;
NLet "z" :n: 3 ;;
"z" <n- ( "z" ^' ( "x" +' "y" ) ).

Example exVar : exists sigma0, programVar ~{ InitialEnvironment }~> sigma0 /\ sigma0 "z" = 27.
Proof.
eexists. split.
unfold programVar.
repeat eapply b_sequence.
eapply b_decNatVar. reflexivity.
eapply b_asnNatVar.
eapply b_const.
reflexivity.
eapply b_initBoolVar.
eapply b_const.
reflexivity.
eapply b_initNatVar.
eapply b_const.
reflexivity.
eapply b_asnNatVar.
eapply b_pow.
eapply b_var. 
eapply b_add.
eapply b_var.
eapply b_var.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Qed.

Definition programList1 :=
NLst "l123" ;; "l123" <+l 1 ;;
"l123" <+l 3 ;; "l123" ins <' 1 '> <' 2 '> ;;
LetNLst "l45" :<n>: ( NL [ 4 >n 5 ] ) ;;
"l123" +l+ "l45".

Definition programList2 := LetBLst "ltf" :<b>: ( BL [true >b false] ) ;; 
"ltf" +l+ "ltf" ;; "ltf" del <' 1 '> ;;
trim "ltf".

Example exProgramList1 : exists sigma0, programList1 ~{ InitialEnvironment }~> sigma0 /\ sigma0 "l123" = NL [1 >n 2 >n 3 >n 4 >n 5].
Proof.
eexists. split.
unfold programList1.
repeat eapply b_sequence.
- eapply b_decNatList. reflexivity.
- eapply b_appToList. 
	-- eapply b_const.
	-- reflexivity.
- eapply b_appToList. eapply b_const. reflexivity.
- eapply b_insInList. reflexivity.
- eapply b_initNatList. reflexivity.
- eapply b_concList; reflexivity.
- reflexivity.
Qed.

Example exProgramList2 : exists sigma0, programList2 ~{ InitialEnvironment }~> sigma0 /\ sigma0 "ltf" = BL [true >b true].
Proof.
eexists. split. unfold programList2.
repeat eapply b_sequence.
- eapply b_initBoolList. reflexivity.
- eapply b_concList. reflexivity.
- eapply b_delFromList. reflexivity.
- eapply b_trList. reflexivity.
- reflexivity.
Qed.

(*Definition programArray1 :=
NArr "v1" ;; "v1" >+n 1 ;;
"v1" <+n 3 ;; "v1" <+n 3 ;;
"v1" [' 1 '] <[n- 2 ;; 
popf "v1" ;; popb "v1".*)

(*Example exProgramArray1 : exists sigma0, programArray1 ~{ InitialEnvironment }~> sigma0 /\ sigma0 "v1" = NA (list Nat 2 [] ).
Proof.
eexists. split. unfold programArray1.
repeat eapply b_sequence.
- eapply b_decNatArray. reflexivity.
- eapply b_pshFrontArrayNumber.
	-- eapply b_const.
	-- reflexivity.
- eapply b_pshBackArrayNumber.
	-- eapply b_const.
	-- reflexivity.
- eapply b_pshBackArrayNumber.
	-- eapply b_const.
	-- reflexivity.
- eapply b_stArrayNumber.
	-- eapply b_const.
	-- reflexivity.
- eapply b_ppFrontArray. reflexivity.
- eapply b_ppBackArray. reflexivity.
reflexivity.
Qed.*)

Definition programArray1 :=
NArr "v1" ;; "v1" >+n 1 ;;
"v1" <+n 3 ;; "v1" <+n 3 ;;
"v1" [' 1 '] <[n- 2.

Example exProgramArray1 : exists sigma0, programArray1 ~{ InitialEnvironment }~> sigma0 /\ sigma0 "v1" = ( NA [1 >n 2 >n 3] ).
Proof.
eexists. split. unfold programArray1.
repeat eapply b_sequence.
- eapply b_decNatArray. reflexivity.
- eapply b_pshFrontArrayNumber.
	-- eapply b_const.
	-- reflexivity.
- eapply b_pshBackArrayNumber.
	-- eapply b_const.
	-- reflexivity.
- eapply b_pshBackArrayNumber.
	-- eapply b_const.
	-- reflexivity.
- eapply b_stArrayNumber.
	-- eapply b_const.
	-- reflexivity.
- reflexivity.
Qed.

Definition programArray2 :=
LetMArr "v2" :[a]: multipleArrayNBS ;;
"v2" [' 0 '] <[a- ( BA [true >b true >b true] ).

Example exProgramArray2 : exists sigma0, programArray2 ~{ InitialEnvironment }~> sigma0 /\ sigma0 "v2" = MA (list Array ( BA [true >b true >b true] ) (list Array boolArrayTFT (list Array stringArrayPLP [] ) ) ).
Proof. 
eexists. split. unfold programArray2.
repeat eapply b_sequence.
- eapply b_initMultipleArray. reflexivity.
- eapply b_stArrayArray. reflexivity.
- reflexivity.
Qed.

Definition programEnum :=
dEnum "solution" ;; 
"solution" >+e 5 ;; 
"solution" <+e true.

Example exProgramEnum : exists sigma0, programEnum ~{ InitialEnvironment }~> sigma0 /\ sigma0 "solution" = ( EN [5 >e true] ).
Proof.
eexists. unfold program. split.
- repeat eapply b_sequence.
	-- eapply b_decEnum. reflexivity.
	-- eapply b_pshFrontEnum.
		--- eapply b_const.
		--- simpl. reflexivity.
	-- eapply b_pshBackEnum.
		--- eapply b_const.
		--- reflexivity.
- reflexivity.
Qed.

Definition programStruct :=
LetStruct "om1" :{s}: ( ST {{ (( "nume", "alex" )) ; (( "varsta", 20 )) ; (( "viu", true )) }} ) ;;
"om1" {\ "varsta" /} 21.

Example exProgramStruct : exists sigma0, programStruct ~{ InitialEnvironment }~> sigma0 /\ sigma0 "om1" = ( ST {{ (( "nume", "alex" )) ; (( "varsta", 21 )) ; (( "viu", true )) }} ).
Proof.
eexists. split. unfold programStruct.
- eapply b_sequence. 
	-- eapply b_initStruct. reflexivity.
	-- eapply b_stStructField. reflexivity.
- reflexivity.
Qed.

Definition programInstructions :=
NVar "prodi" ;; "prodi" <n- 1 ;; 
NLet "prodp" :n: 1 ;;
NLet "sumi" :n: 0 ;; NLet "sump" :n: 0 ;;

For (NVar "i" ;; "i" <n- 1 // "i" <=' 3 // "i" <n- ( "i" +' 1 ) ) {
  If ("i" %' 2 ==' 0)
  Then {"sump" <n- ( "sump" +' "i" ) }
  Else {"sumi" <n- ( "sumi" +' "i" ) }
  EndIfThenElse
} EndFor ;;

While ("sump" >' 0) {
  Ift ( ("sump" %' 10) %' 2 ==' 1)
  Then { "prodi" <n- "prodi" *' ("sump" %' 10) }
  EndIfThen ;;

  "sump" <n- "sump" /' 10  
} EndWhile ;;

While ("sumi" >' 0) {
  Ift ( ("sumi" %' 10) %' 2 ==' 0)
  Then { "prodp" <n- "prodp" *' ("sumi" %' 10) }
  EndIfThen ;;

  "sumi" <n- "sumi" /' 10  
} EndWhile ;;

NVar "final" ;; "final" <n- ( ( "prodp" +' "prodi" ) -' ("prodp" -' "prodi") ) ^' 2.

Example exProgramInstructions: exists sigma0, programInstructions ~{ InitialEnvironment }~> sigma0 /\ sigma0 "final" = 4.
Proof.
eexists. split. unfold programInstructions.
- repeat eapply b_sequence.
	-- eapply b_decNatVar. reflexivity.
	-- eapply b_asnNatVar.
		--- eapply b_const. 
		--- reflexivity.
	-- eapply b_initNatVar.
		--- eapply b_const.
		--- reflexivity.
	-- eapply b_initNatVar.
		--- eapply b_const.
		--- reflexivity.
	-- eapply b_initNatVar.
		--- eapply b_const.
		--- reflexivity.
	-- eapply true_forLoop.
		--- repeat eapply b_sequence.
			---- eapply b_decNatVar. reflexivity.
			---- eapply b_asnNatVar.
				----- eapply b_const.
				----- reflexivity.
		--- eapply b_lessequalthan.
			---- eapply b_var.
			---- eapply b_const.
			---- reflexivity.
		--- eapply true_whileLoop.
			---- eapply b_lessequalthan.
				----- eapply b_var.
				----- eapply b_const.
				----- reflexivity.
			---- repeat eapply b_sequence.
					 eapply false_ifThenElse.
					 eapply b_equal. eapply b_mod.
					 eapply b_var. eapply b_const.
					 reflexivity. eapply b_const.
					 reflexivity.
					 eapply b_asnNatVar.
					 eapply b_add. eapply b_var. eapply b_var.
					 reflexivity. reflexivity.
					 eapply b_asnNatVar.
					 eapply b_add. eapply b_var. eapply b_const.
					 reflexivity. reflexivity.
					 eapply true_whileLoop.
					 eapply b_lessequalthan.
					 eapply b_var. eapply b_const.
					 reflexivity.
					 repeat eapply b_sequence.
					 eapply true_ifThenElse.
					 eapply b_equal. eapply b_mod.
					 eapply b_var. eapply b_const.
					 reflexivity. eapply b_const.
					 reflexivity.
					 eapply b_asnNatVar.
					 eapply b_add. eapply b_var. eapply b_var.
					 reflexivity. reflexivity.
					 eapply b_asnNatVar.
					 eapply b_add. eapply b_var. eapply b_const.
					 reflexivity. reflexivity.
					 eapply true_whileLoop.
					 eapply b_lessequalthan.
					 eapply b_var. eapply b_const.
					 reflexivity.
					 repeat eapply b_sequence.
					 eapply false_ifThenElse.
					 eapply b_equal. eapply b_mod.
					 eapply b_var. eapply b_const.
					 reflexivity. eapply b_const.
					 reflexivity.
					 eapply b_asnNatVar.
					 eapply b_add. eapply b_var. eapply b_var.
					 reflexivity. reflexivity.
					 eapply b_asnNatVar.
					 eapply b_add. eapply b_var. eapply b_const.
					 reflexivity. reflexivity.
					 eapply false_whileLoop.
					 eapply b_lessequalthan.
					 eapply b_var. eapply b_const.
					 reflexivity.
	-- eapply true_whileLoop.
		 eapply b_greaterthan. 
		 eapply b_var. eapply b_const.
		 reflexivity.
		 repeat eapply b_sequence.
		 eapply false_ifThen.
		 eapply b_equal.
		 eapply b_mod. eapply b_mod. 
		 eapply b_var. eapply b_const.
		 reflexivity. eapply b_const.
		 reflexivity. eapply b_const.
		 reflexivity.
		 eapply b_asnNatVar. eapply b_div.
		 eapply b_var. eapply b_const.
		 reflexivity. reflexivity.
		 eapply false_whileLoop.
		 eapply b_greaterthan. 
		 eapply b_var. eapply b_const.
		 reflexivity.
	-- eapply true_whileLoop.
		 eapply b_greaterthan. 
		 eapply b_var. eapply b_const.
		 reflexivity.
		 repeat eapply b_sequence.
		 eapply true_ifThen.
		 eapply b_equal.
		 eapply b_mod. eapply b_mod. 
		 eapply b_var. eapply b_const.
		 reflexivity. eapply b_const.
		 reflexivity. eapply b_const.
		 reflexivity.
		 eapply b_asnNatVar. eapply b_mul.
		 eapply b_var. eapply b_mod. 
		 eapply b_var. eapply b_const.
		 reflexivity. reflexivity. reflexivity.
		 eapply b_asnNatVar. eapply b_div.
		 eapply b_var. eapply b_const.
		 reflexivity. reflexivity.
		 eapply false_whileLoop.
		 eapply b_greaterthan. 
		 eapply b_var. eapply b_const.
		 reflexivity.
	-- eapply b_decNatVar. reflexivity.
	-- eapply b_asnNatVar.
		 eapply b_pow. eapply b_minus.
		 eapply b_add.
		 eapply b_var. eapply b_var.
		 reflexivity. eapply b_minus.
		 eapply b_var. eapply b_var.
		 reflexivity. reflexivity.
		 eapply b_const. 
		 reflexivity. reflexivity.
- reflexivity.
Qed.

Definition programSwitch :=
NLet "x" :n: 2 ;;
Switch s( "x" )s {\
	Case 1 :c "x" <n- 7 ;;/
	Case 2 :c "x" <n- 5 ;;/
	Default :d "x" <n- 3
/}.

Example exProgramSwitch: exists sigma0, programSwitch ~{ InitialEnvironment }~> sigma0 /\ sigma0 "x" = 5.
Proof.
eexists. split. unfold programSwitch.
repeat eapply b_sequence.
	- eapply b_initNatVar. eapply b_const. reflexivity.
	- eapply b_switch.
		-- eapply b_var.
		-- reflexivity.
		-- simpl. eapply b_asnNatVar.
			--- eapply b_const.
			--- reflexivity.
	- reflexivity.
Qed.

Definition programDoWhile :=
NLet "i" :n: ( 0 +' false ) ;;
Do {
	"i" <n- ( "i" +' 1 )
} WhileStill ( "i" <=' 2 ).

Example exProgramDoWhile : exists sigma0, programDoWhile ~{ InitialEnvironment }~> sigma0 /\ sigma0 "i" = 3.
Proof.
eexists. split. unfold programDoWhile.
repeat eapply b_sequence.
	- eapply b_initNatVar.
		-- eapply b_add.
			--- eapply b_const.
			--- eapply b_const.
			--- reflexivity.
		-- reflexivity.
	- eapply true_doWhileLoop.
		-- eapply b_asnNatVar.
			--- eapply b_add.
				---- eapply b_var.
				---- eapply b_const.
				---- reflexivity.
			--- reflexivity.
		-- eapply b_lessequalthan.
			--- eapply b_var.
			--- eapply b_const.
			--- reflexivity.
		-- eapply true_doWhileLoop.
			--- eapply b_asnNatVar.
				---- eapply b_add.
					----- eapply b_var.
					----- eapply b_const.
					----- reflexivity.
				---- reflexivity.
			--- eapply b_lessequalthan.
				---- eapply b_var.
				---- eapply b_const.
				---- reflexivity.
			--- eapply false_doWhileLoop.
				---- eapply b_asnNatVar.
					----- eapply b_add.
						------ eapply b_var.
						------ eapply b_const.
						------ reflexivity.
					----- reflexivity.
				---- eapply b_lessequalthan.
					----- eapply b_var.
					----- eapply b_const.
					----- reflexivity.
	- reflexivity.
Qed.

Definition programContinue :=
NVar "x" ;;
BLet "true" :b: (1 &&' 2) ;;
Do {
	"x" <n- 2 ;;
	Continue ;;
	"x" <n- 3
} WhileStill ( "true" ==' false ).

Example exProgramContinue: exists sigma0, programContinue ~{ InitialEnvironment }~> sigma0 /\ sigma0 "x" = 2.
Proof.
eexists. split. unfold programContinue.
	- repeat eapply b_sequence.
		-- eapply b_decNatVar. reflexivity.
		-- eapply b_initBoolVar.
			--- eapply b_and.
				---- eapply b_const.
				---- eapply b_const.
				---- reflexivity.
			--- reflexivity.
		-- eapply false_doWhileLoop.
			--- eapply b_sequence.
				---- eapply b_asnNatVar. eapply b_const. reflexivity.
				---- eapply continue_sequence1. eapply b_asnNatVar.
						 eapply b_const. reflexivity. 
			--- eapply b_equal. eapply b_var. eapply b_const. reflexivity.
	- reflexivity.
Qed.










