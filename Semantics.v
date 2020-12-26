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
| nrNat (n: nat)
| errNat.

Scheme Equality for Nat.
Coercion nrNat: nat >-> Nat.

Check nrNat 5.


(** Boolean Values **)

Inductive Bool : Type :=
| valBool (b: bool)
| errBool.

Scheme Equality for Bool.
Coercion valBool: bool >-> Bool.

Check valBool true.


(** Character Strings **)

Inductive String : Type :=
| sString (s: string)
| errString.

Scheme Equality for String.
Coercion sString: string >-> String.

Check sString "PLP".


(*** Complex Data Types ***)


(** Linked Lists **)

Inductive List (T: Type) :=
| nil
| list (t: T) (l: List T).

Scheme Equality for List.
Check list Nat 4 (list Nat 3 (list Nat 2 (nil Nat))).

Notation "[ ]" := (nil).
Arguments nil {T}. (* Tells Coq to infer the type of T in the case of nil based on its surroundings *)

(*
Notation "'[' A '>>' T B ']'" := (list T A B) (at level 30, left associativity, T at level 10).
Notation "'[' A '/' T '\' B ']'" := (list T A B) (at level 30, left associativity).
Check [4 >> Nat [5 >> Nat [6 >> Nat [ ]]]].*)
Check list Nat 4 (list Nat 5 (list Nat 6 [])).

Notation "'[' A '>n' .. '>n' B ']'" := (list Nat A .. (list Nat B []) ..).
Check [1 >n 2 >n 3].

Notation "'[' A '>b' .. '>b' B ']'" := (list Bool A .. (list Bool B []) ..).
Check [true >b false >b true].

Notation "'[' A '>s' .. '>s' B ']'" := (list String A .. (list String B []) ..).
Check ["P" >s "L" >s "P"].


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
Definition multipleArrayNBS := MA (list Array natArray123 (list Array boolArrayTFT (list Array stringArrayPLP []))).
Check multipleArrayNBS.


(** Enums (built on lists) **)

Inductive EnumTypes : Type :=
| natEnum (n: Nat)
| boolEnum (b: Bool)
| stringEnum (s: String)
| errEnum.

Coercion natEnum: Nat >-> EnumTypes.
Coercion boolEnum: Bool >-> EnumTypes.
Coercion stringEnum: String >-> EnumTypes.

Inductive Enum : Type :=
| enum (e: List EnumTypes).

Notation "'EN' L" := (enum L) (at level 90).
Notation "'[[' A '>e' .. '>e' B ']]'" := (list EnumTypes A .. (list EnumTypes B []) ..).
Check [[ 4 >e true >e "PLP" ]].

Definition enum0isF := EN [[0 >e "is" >e false]].
Check enum0isF.


(** Structs (built on lists) **)

Inductive FieldTypes : Type :=
| natValue (n: Nat)
| boolValue (b: Bool)
| stringValue (s: String)
| arrayValue (a: Array)
| enumValue (e: Enum)
| notFound.

Coercion natValue: Nat >-> FieldTypes.
Coercion boolValue: Bool >-> FieldTypes.
Coercion stringValue: String >-> FieldTypes.
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
| unassignedList
| unassignedArray
| unassignedEnum
.

Inductive ResultTypes : Type :=
| nrNats (n: Nat)
| valBools (b: Bool)
| sStrings (s: String)
| lists (T: Type) (l: List T)
| arrays (a: Array)
| enums (e: Enum)
| structs (s: Struct)
| undeclared
| unassigned (u: Unassigned)
| error.

Coercion nrNats: Nat >-> ResultTypes.
Coercion valBools: Bool >-> ResultTypes.
Coercion sStrings: String >-> ResultTypes.
Coercion lists: List >-> ResultTypes.
Coercion arrays: Array >-> ResultTypes.
Coercion enums: Enum >-> ResultTypes.
Coercion structs: Struct >-> ResultTypes.
Coercion unassigned: Unassigned >-> ResultTypes.



(**** Expression Syntax ****)

Inductive Exp :=
| anum: Nat -> Exp
| avar: string -> Exp
| aplus: Exp -> Exp -> Exp
| aminus: Exp -> Exp -> Exp
| amul: Exp -> Exp -> Exp
| adiv: Exp -> Exp -> Exp
| amod: Exp -> Exp -> Exp
| apower: Exp -> Exp -> Exp
| bval: Bool -> Exp
| btrue: Exp
| bfalse: Exp
| bnot: Exp -> Exp
| band: Exp -> Exp -> Exp
| bor: Exp -> Exp -> Exp
| blessthan: Exp -> Exp -> Exp
| blessthanequal: Exp -> Exp -> Exp
| bgreaterthan: Exp -> Exp -> Exp
| bgreaterthanequal: Exp -> Exp -> Exp
| bequal: Exp -> Exp -> Exp
| bnotequal: Exp -> Exp -> Exp
| sstr: String -> Exp
| splus: Exp -> Exp -> Exp
| smul: Exp -> Exp -> Exp
.

Coercion anum : Nat >-> Exp.
Coercion avar : string >-> Exp.
Coercion bval: Bool >-> Exp.
Coercion sstr: String >-> Exp.

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

Infix "splus" := (splus) (at level 50, left associativity).
Infix "smul" := (smul) (at level 40, left associativity).

Notation "A ++' B" := (A splus B) (at level 50, left associativity).
Notation "A *+' B" := (A smul B) (at level 40, left associativity).

Check (2 +' 4).
Check (true ||' false).
Check ("abc" ++' "def").




(**** Statement Syntax ****)




Inductive Pair (T1 T2 : Type) : Type :=
| pair (t1: T1) (t2: T2).

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

| initNatList: string -> List Nat -> Statement
| initBoolList: string -> List Bool -> Statement
| initStringList: string -> List String -> Statement

| asnNatList: string -> string -> Statement
| asnBoolList: string -> string -> Statement
| asnStringList: string -> string -> Statement

| insNatInList: string -> nat -> Exp -> Statement
| insBoolInList: string -> nat -> Exp -> Statement
| insStringInList: string -> nat -> Exp -> Statement

| appNatToList: string -> List Nat -> Statement
| appBoolToList: string -> List Bool -> Statement
| appStringToList: string -> List String -> Statement

| delNatFromList: string -> nat -> Statement
| delBoolFromList: string -> nat -> Statement
| delStringFromList: string -> nat -> Statement

| trNatList: string -> Statement
| trBoolList: string -> Statement
| trStringList: string -> Statement

| gtFromList: string -> nat -> Statement

| decNatArray: string -> Statement
| decBoolArray: string -> Statement
| decStringArray: string -> Statement
| decMultipleArray: string -> Statement

| initNatArray: string -> Array -> Statement
| initBoolArray: string -> Array -> Statement
| initStringArray: string -> Array -> Statement
| initMultipleArray: string -> Array -> Statement

| asnNatArray: string -> string -> Statement
| asnBoolArray: string -> string -> Statement
| asnStringArray: string -> string -> Statement
| asnMultipleArray: string -> string -> Statement

| stArrayNat: string -> nat -> Exp -> Statement
| stArrayBool: string -> nat -> Exp -> Statement
| stArrayString: string -> nat -> Exp -> Statement
| stArrayArray: string -> nat -> Array -> Statement

| pshFrontArrayNat: string -> Exp -> Statement
| pshFrontArrayBool: string -> Exp -> Statement
| pshFrontArrayString: string -> Exp -> Statement
| pshFrontArrayArray: string -> Array -> Statement

| pshBackArrayNat: string -> Exp -> Statement
| pshBackArrayBool: string -> Exp -> Statement
| pshBackArrayString: string -> Exp -> Statement
| pshBackArrayArray: string -> Array -> Statement

| ppFrontArrayNat: string -> Statement
| ppFrontArrayBool: string -> Statement
| ppFrontArrayString: string -> Statement
| ppFrontArrayArray: string -> Statement

| ppBackArrayNat: string -> Statement
| ppBackArrayBool: string -> Statement
| ppBackArrayString: string -> Statement
| ppBackArrayArray: string -> Statement

| gtArrayValue: string -> nat -> Statement

| decEnum: string -> Statement
| initEnum: string -> Enum -> Statement
| asnEnum: string -> string -> Statement

| pshFrontEnum: string -> EnumTypes -> Statement
| pshBackEnum: string -> EnumTypes -> Statement
| ppFrontEnum: string -> Statement
| ppBackEnum: string -> Statement

| stEnum: string -> nat -> EnumTypes -> Statement
| gtEnum: string -> nat -> Statement

| initStruct: string -> Struct -> Statement
|	asnStruct: string -> string -> Statement

| gtStructField: string -> string -> Statement
| stStructField: string -> string -> FieldTypes -> Statement

| ifThen: Exp -> Statement -> Statement
| ifThenElse: Exp -> Statement -> Statement -> Statement
| doWhileLoop: Statement -> Exp -> Statement
| whileLoop: Exp -> Statement -> Statement
| forLoop: Statement -> Exp -> Statement -> Statement -> Statement
| sequence: Statement -> Statement -> Statement

| break
| continue

| switchCase: string -> List (Pair Nat Statement) -> Statement
.




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

Notation "A ':<n:' B" := (asnNatList A B) (at level 50).
Notation "A ':<b:' B" := (asnBoolList A B) (at level 50).
Notation "A ':<s:' B" := (asnStringList A B) (at level 50).

Notation "A 'insNat' <' B '> <' C '>" := (insNatInList A B C) (at level 50).
Notation "A 'insBool' <' B '> <' C '>" := (insBoolInList A B C) (at level 50).
Notation "A 'insString' <' B '> <' C '>" := (insStringInList A B C) (at level 50).

Notation "A '+n+' B" := (appNatToList A B) (at level 50).
Notation "A '+b+' B" := (appBoolToList A B) (at level 50).
Notation "A '+s+' B" := (appStringToList A B) (at level 50).

Notation "A 'delNat' <' B '>" := (delNatFromList A B) (at level 50).
Notation "A 'delBool' <' B '>" := (delNatFromList A B) (at level 50).
Notation "A 'delString' <' B '>" := (delNatFromList A B) (at level 50).

Notation "A 'trNat'" := (trNatList A) (at level 50).
Notation "A 'trBool'" := (trBoolList A) (at level 50).
Notation "A 'trString'" := (trStringList A) (at level 50).

Notation "A '<<' B '>>'" := (gtFromList A B) (at level 50).


(** Arrays: Declare, Initialize, Assign, Set, Push (Front/Back), Pop (Front/Back), Get **)

Notation "'NArr' V" := (decNatArray V) (at level 50).
Notation "'BArr' V" := (decBoolArray V) (at level 50).
Notation "'SArr' V" := (decStringArray V) (at level 50).
Notation "'MArr' V" := (decMultipleArray V) (at level 50).

Notation "'LetNArr' V ':[n]:' L" := (initNatArray V L) (at level 50).
Notation "'LetBArr' V ':[b]:' L" := (initBoolArray V L) (at level 50).
Notation "'LetSArr' V ':[s]:' L" := (initStringArray V L) (at level 50).
Notation "'LetMArr' V ':[a]:' L" := (initMultipleArray V L) (at level 50).

Notation "A ':[n:' B" := (asnNatArray A B) (at level 50).
Notation "A ':[b:' B" := (asnBoolArray A B) (at level 50).
Notation "A ':[s:' B" := (asnStringArray A B) (at level 50).
Notation "A ':[a:' B" := (asnMultipleArray A B) (at level 50).

Notation "X [' N '] '<n-' V" := (stArrayNat X N V) (at level 50).
Notation "X [' B '] '<b-' V" := (stArrayBool X B V) (at level 50).
Notation "X [' S '] '<s-' V" := (stArrayString X S V) (at level 50).
Notation "X [' A '] '<a-' V" := (stArrayArray X A V) (at level 50).

Notation "V '>+n' N" := (pshFrontArrayNat V N) (at level 50).
Notation "V '>+b' N" := (pshFrontArrayBool V N) (at level 50).
Notation "V '>+s' N" := (pshFrontArrayString V N) (at level 50).
Notation "V '>+a' N" := (pshFrontArrayArray V N) (at level 50).

Notation "V '<+n' N" := (pshBackArrayNat V N) (at level 50).
Notation "V '<+b' N" := (pshBackArrayBool V N) (at level 50).
Notation "V '<+s' N" := (pshBackArrayString V N) (at level 50).
Notation "V '<+a' N" := (pshBackArrayArray V N) (at level 50).

Notation "V '>-n'" := (ppFrontArrayNat V) (at level 50).
Notation "V '>-b'" := (ppFrontArrayBool V) (at level 50).
Notation "V '>-s'" := (ppFrontArrayString V) (at level 50).
Notation "V '>-a'" := (ppFrontArrayArray V) (at level 50).

Notation "V '<-n'" := (ppBackArrayNat V) (at level 50).
Notation "V '<-b'" := (ppBackArrayBool V) (at level 50).
Notation "V '<-s'" := (ppBackArrayString V) (at level 50).
Notation "V '<-a'" := (ppBackArrayArray V) (at level 50).

Notation "X [[' N ']]" := (gtArrayValue X N) (at level 50).


(** Enums: Declare, Initialize, Assign, Push Front/Back, Pop Front/Back, Set, Get **)

Notation "'dEnum' E" := (decEnum E) (at level 50).
Notation "'LetEnum' E :[e]: L" := (initEnum E L) (at level 50).
Notation "A ':[e:' B" := (asnEnum A B) (at level 50).

Notation "V '>+e' N" := (pshFrontEnum V N) (at level 50).
Notation "V '<+e' N" := (pshBackEnum V N) (at level 50).
Notation "V '>-e'" := (ppFrontEnum V) (at level 50).
Notation "V '<-e'" := (ppBackEnum V) (at level 50).

Notation "X [' E '] '<e-' V" := (stEnum X E V) (at level 50).
Notation "X '[)' N '(]'" := (gtEnum X N) (at level 50).


(** Structs: Initialize, Assign, Get, Set **)

Notation "'LetStruct' X :{s}: L" := (initStruct X L) (at level 50).
Notation "A ':{s:' B" := (asnStruct A B) (at level 50).
Notation "X '{/' F '\}'" := (gtStructField X F) (at level 50).
Notation "X '{\' F '/}' V" := (stStructField X F V) (at level 50).


(** Instructions: Decisional, Repetitive, Sequences, Iteration Manipulators **)

Notation "'If' '(' A ')' 'Then' '{' S '}' 'EndIfThen'" := (ifThen A S) (at level 50).
Notation "'If' '(' A ')' 'Then' '{' S1 '}' 'Else' '{' S2 '}' 'EndIfThenElse'" := (ifThenElse A S1 S2) (at level 55).
Notation "'Do' { S } 'WhileStill' ( C )" := (doWhileLoop S C) (at level 50).
Notation "'While' ( B ) { A } 'EndWhile'" := (whileLoop B A) (at level 50).
Notation "'For' ( A '//' B '//' C ) { S } 'EndFor'" := (forLoop A B C S) (at level 50).
Notation "A ';;' B" := (sequence A B) (at level 45).

Notation "'Break'" := (break) (at level 45).
Notation "'Continue'" := (continue) (at level 45).

Definition casePair := pair Nat Statement.

Notation "'case' X ':->' S" := (casePair X S) (at level 45).
Notation "'{\' C1 ';;/' .. ';;/' C2 '/}'" := (list casePair C1 .. (list casePair C2 []) ..) (at level 45). 
Notation "'switch' '(' X ')' C" := (switchCase X C) (at level 50).


(*** Example Statements ***)



(** Variables: Declare, Assign, Initialize **)

Check (NVar "x") ;; (BVar "y") ;; (SVar "z").

Check ("x" <n- 3) ;; ("y" <b- true) ;; ("z" <s- "z").

Check (NLet "x" :n: 3) ;; (BLet "y" :b: false) ;; (SLet "z" :s: "z").


(** Lists: Declare, Initialize, Assign, Insert, Append, Delete, Trim, Get **)

Check (NLst "x") ;; (BLst "y") ;; (SLst "z").

Check (LetNLst "x" :<n>: [1 >n 2 >n 3]) ;; (LetBLst "y" :<b>: [true >b true]) ;; (LetSLst "z" :<s>: ["P" >s "L" >s "P"]).

Check ("x1" :<n: "x2") ;; ("y1" :<b: "y2") ;; ("z1" :<s: "z2").

Check ("x" insNat<'0'><'1'>) ;; ("y" insBool<'1'><' true '>) ;; ("z" insString<'2'><'"z"'>).

Check ("x" +n+ [1 >n 2]) ;; ("y" +b+ [true >b false]) ;; ("z" +s+ ["1" >s "0"]).

Check ("x" delNat <'1'>) ;; ("y" delBool <'1'>) ;; ("z" delString <'1'>).

Check ("x" trNat) ;; ("y" trBool) ;; ("z" trString).

Check ("x" << 1 >>) ;; ("y" << 1 >>) ;; ("z" << 1 >>).


(** Arrays: Declare, Initialize, Assign, Set, Push (Front/Back), Pop (Front/Back), Get **)

Check (NArr "x") ;; (BArr "y") ;; (SArr "z") ;; (MArr "t").

Check (LetNArr "x" :[n]: natArray123) ;; (LetBArr "y" :[b]: boolArrayTFT) ;; (LetSArr "z" :[s]: stringArrayPLP) ;; (LetMArr "t" :[a]: multipleArrayNBS).

Check ("x1" :[n: "x2") ;; ("y1" :[b: "y2") ;; ("z1" :[s: "z2") ;; ("t1" :[a: "t2").

Check ("x"['2'] <n- 3) ;; ("y"['2'] <b- true) ;; ("z"['2'] <s- "3") ;; ("t"['2'] <a- natArray123).

Check ("x" >+n 1) ;; ("y" >+b true) ;; ("z" >+s "z") ;; ("t" >+a natArray123).

Check ("x" <+n 1) ;; ("y" <+b true) ;; ("z" <+s "z") ;; ("t" <+a natArray123).

Check ("x" >-n) ;; ("y" >-b) ;; ("z" >-s) ;; ("t" >-a).
Check ("x" <-n) ;; ("y" <-b) ;; ("z" <-s) ;; ("t" <-a).

Check ("x" [['2']]) ;; ("y" [['2']]) ;; ("z"[['2']]) ;; ("t"[['2']]).


(** Enums: Declare, Initialize, Assign, Push Front/Back, Pop Front/Back, Set, Get **)

Check (dEnum "e") ;; (LetEnum "d" :[e]: enum0isF ) ;; ("e" :[e: "d").

Check ("e" >+e 4) ;; ("e" <+e true) ;; ("e" >-e) ;; ("e" <-e).

Check ("e"['2'] <e- 2) ;; ("e"[)2(]).


(** Structs: Initialize, Assign, Get, Set **)

Check (LetStruct "x" :{s}: struct1) ;; ("x1" :{s: "x2") ;; ("x" {/"f1"\}) ;; ("x" {\"f2"/} 7).




(**** Semantics ****)


(** Operations **)

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

Definition tneq (a b: ResultTypes) := tnot (teq a b).

Definition tsplus (a b: ResultTypes) := 
match a, b with
| sString a, sString b => sString (a ++ b)
| _, _ => errString
end.

Fixpoint strMul (a: string) (b: nat) :=
match b with
| 0 => EmptyString
| S b' => a ++ ( strMul a b' )
end. 

Compute strMul "abc" 3.

Definition tsmul (a b: ResultTypes) := 
match a, b with
| sString a, nrNat b => sString (strMul a b )
| nrNat a, sString b => sString (strMul b a )
| _, _ => errString
end.

Compute tneq (tgte 2 (tplus true true) ) 2.

Compute (tpow (tmodulo 12 (tmul true 5) ) (tdiv (tplus 7 (tmul 3 true) ) (tminus true false) ) ).

Compute (tsplus "facul" (tsplus (tsmul "ta" 3 ) "te" ) ). 




(** List Functions **)


(* List Utilities *)

Fixpoint getListLength {T: Type} (l: List T) := 
match l with
| nil => 0
| list _ v l2 => 1 + getListLength l2
end.


(* List Getters *)

Fixpoint getNatListElement (l: List Nat) (n: nat) :=
match l with
| nil => error
| list _ val l' => if (eqb n 0) 
                 then val
                 else getNatListElement l' (n - 1) 
end.

Fixpoint getBoolListElement (l: List Bool) (n: nat) :=
match l with
| nil => error
| list _ val l' => if (eqb n 0) 
                 then val
                 else getBoolListElement l' (n - 1) 
end.

Fixpoint getStringListElement (l: List String) (n: nat) :=
match l with
| nil => error
| list _ val l' => if (eqb n 0) 
                 then val
                 else getStringListElement l' (n - 1) 
end.

Fixpoint getArrayListElement (l: List Array) (n: nat) :=
match l with
| nil => error
| list _ val l' => if (eqb n 0) 
                 then val
                 else getArrayListElement l' (n - 1) 
end.


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

Fixpoint insertBoolInList (l: List Bool) (n: nat) (v: Bool) :=
match l with 
| [] => if eqb n 0 
				then list _ v []
				else []
| list _ val l' => if eqb n 0
									 then list _ v (list _ val l')
									 else list _ val (insertBoolInList l' (n - 1) v)
end.

Fixpoint insertStringInList (l: List String) (n: nat) (v: String) :=
match l with 
| [] => if eqb n 0 
				then list _ v []
				else []
| list _ val l' => if eqb n 0
									 then list _ v (list _ val l')
									 else list _ val (insertStringInList l' (n - 1) v)
end.

Fixpoint insertArrayInList (l: List Array) (n: nat) (v: Array) :=
match l with 
| [] => if eqb n 0 
				then list _ v []
				else []
| list _ val l' => if eqb n 0
									 then list _ v (list _ val l')
									 else list _ val (insertArrayInList l' (n - 1) v)
end.


(* List Deleters *)

Fixpoint deleteFromList {T: Type} (l: List T) (n: nat) :=
match l with 
| [] => []
| list _ val l' => if eqb n 0
									 then l'
									 else list _ val (deleteFromList l' (n - 1) )
end.

Definition deleteNatFromList (l: List Nat) (n: nat) := deleteFromList l n.

Definition deleteBoolFromList (l: List Bool) (n: nat) := deleteFromList l n.

Definition deleteStringFromList (l: List String) (n: nat) := deleteFromList l n.

Definition deleteArrayFromList (l: List Array) (n: nat) := deleteFromList l n.


(* List Appenders *)

Fixpoint concatLists {T: Type} (l1 l2: List T) :=
match l1 with
| nil => l2
| list _ v l1' => list _ v (concatLists l1' l2)
end.

Definition appendNatToList (l1 l2: List Nat) := concatLists l1 l2.

Definition appendBoolToList (l1 l2: List Bool) := concatLists l1 l2.

Definition appendStringToList (l1 l2: List String) := concatLists l1 l2.

Definition appendArrayToList (l1 l2: List Array) := concatLists l1 l2.


(* List Trimmers *)

Definition trimNatList (l: List Nat) := deleteFromList l ( (getListLength l) - 1).

Definition trimBoolList (l: List Bool) := deleteFromList l ( (getListLength l) - 1).

Definition trimStringList (l: List String) := deleteFromList l ( (getListLength l) - 1).

Definition trimArrayList (l: List Array) := deleteFromList l ( (getListLength l) - 1).


(* List Setters (for Arrays) *)

Fixpoint setNatListElement (l: List Nat) (n: nat) (v: Nat) :=
match l with
| nil => nil
| list _ val l' => if (eqb n 0)
                   then (list _ v l')
                   else (list _ val (setNatListElement l' (n - 1) v) )
end.

Fixpoint setBoolListElement (l: List Bool) (n: nat) (v: Bool) :=
match l with
| nil => nil
| list _ val l' => if (eqb n 0)
                   then (list _ v l')
                   else (list _ val (setBoolListElement l' (n - 1) v) )
end.

Fixpoint setStringListElement (l: List String) (n: nat) (v: String) :=
match l with
| nil => nil
| list _ val l' => if (eqb n 0)
                   then (list _ v l')
                   else (list _ val (setStringListElement l' (n - 1) v) )
end.

Fixpoint setArrayListElement (l: List Array) (n: nat) (v: Array) :=
match l with
| nil => nil
| list _ val l' => if (eqb n 0)
                   then (list _ v l')
                   else (list _ val (setArrayListElement l' (n - 1) v) )
end.




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


(* Array Concat *)

Definition concatArrays (a1 a2: Array) :=
match a1, a2 with
| natArray l1, natArray l2 => natArray (concatLists l1 l2)
| boolArray l1, boolArray l2 => boolArray (concatLists l1 l2)
| stringArray l1, stringArray l2 => stringArray (concatLists l1 l2)
| multipleArray l1, multipleArray l2 => multipleArray (concatLists l1 l2)
| _, _ => errArray
end.


(* Array Getter *)

Definition getArrayElement (a: Array) (n: nat) :=
match a with
| natArray l => getNatListElement l n
| boolArray l => getBoolListElement l n
| stringArray l => getStringListElement l n
| multipleArray l => getArrayListElement l n
| _ => error
end.


(* Array Setters *)

Definition setNatArrayElement (a: Array) (n: nat) (v: Nat) :=
match a with
| natArray l => NA (setNatListElement l n v)
| _ => a
end.

Definition setBoolArrayElement (a: Array) (n: nat) (v: Bool) :=
match a with
| boolArray l => BA (setBoolListElement l n v)
| _ => a
end.

Definition setStringArrayElement (a: Array) (n: nat) (v: String) :=
match a with
| stringArray l => SA (setStringListElement l n v)
| _ => a
end.

Definition setMultipleArrayElement (a: Array) (n: nat) (v: Array) :=
match a with
| multipleArray l => MA (setArrayListElement l n v)
| _ => a
end.


(* Array Back Pushers *)

Definition pushBackNatArray (a: Array) (n: Nat) :=
match a with 
| NA l => NA (insertNatInList l (getListLength l) n)
| _ => a
end.

Definition pushBackBoolArray (a: Array) (n: Bool) :=
match a with 
| BA l => BA (insertBoolInList l (getListLength l) n)
| _ => a
end.

Definition pushBackStringArray (a: Array) (n: String) :=
match a with 
| SA l => SA (insertStringInList l (getListLength l) n)
| _ => a
end.

Definition pushBackMultipleArray (a: Array) (n: Array) :=
match a with 
| MA l => MA (insertArrayInList l (getListLength l) n)
| _ => a
end.


(* Array Front Pushers *)

Definition pushFrontNatArray (a: Array) (n: Nat) :=
match a with 
| NA l => NA (insertNatInList l 0 n)
| _ => a
end.

Definition pushFrontBoolArray (a: Array) (n: Bool) :=
match a with 
| BA l => BA (insertBoolInList l 0 n)
| _ => a
end.

Definition pushFrontStringArray (a: Array) (n: String) :=
match a with 
| SA l => SA (insertStringInList l 0 n)
| _ => a
end.

Definition pushFrontMultipleArray (a: Array) (n: Array) :=
match a with 
| MA l => MA (insertArrayInList l 0 n)
| _ => a
end.


(* Array Back Pop *)

Definition popBackArray (a: Array) :=
match a with 
| NA l => NA (deleteNatFromList l ( (getListLength l) - 1) )
| BA l => BA (deleteBoolFromList l ( (getListLength l) - 1) )
| SA l => SA (deleteStringFromList l ( (getListLength l) - 1) )
| MA l => MA (deleteArrayFromList l ( (getListLength l) - 1) )
| _ => a
end.


(* Array Front Pop *)

Definition popFrontArray (a: Array) :=
match a with 
| NA l => NA (deleteNatFromList l 0 )
| BA l => BA (deleteBoolFromList l 0 )
| SA l => SA (deleteStringFromList l 0 )
| MA l => MA (deleteArrayFromList l 0 )
| _ => a
end.


(* Array Concat Operator *)

Definition tarrplus (a b: ResultTypes) :=
match a, b with
| arrays a, arrays b => arrays (concatArrays a b)
| _, _ => error
end.




(** Enum Functions **)

(* Enum Utilities *)

Definition getEnumLength (e: Enum) :=
match e with
| EN l => getListLength l
end.


(* Enum Setter *)

Fixpoint setEnumListElement (l: List EnumTypes) (n: nat) (v: EnumTypes) :=
match l with
| nil => nil
| list _ val l' => if (eqb n 0)
                   then (list _ v l')
                   else (list _ val (setEnumListElement l' (n - 1) v) )
end.

Definition setEnumElement (e: Enum) (n: nat) (v: EnumTypes) :=
match e with
| EN l => EN (setEnumListElement l n v)
end.

(* Enum Getter *)

Fixpoint getEnumListElement (l: List EnumTypes) (n: nat) :=
match l with
| nil => error
| list _ val l' => if (eqb n 0) 
                 then match val with
                 			| natEnum n => nrNats n
                 			| boolEnum b => valBools b
                 			| stringEnum s => sStrings s
                 			| _ => error
                 			end
                 else getEnumListElement l' (n - 1) 
end.

Definition getEnumElement (e: Enum) (n: nat) :=
match e with
| EN l => getEnumListElement l n
end.

(* Enum Back Push *)

Fixpoint insertEnumInList (l: List EnumTypes) (n: nat) (v: EnumTypes) :=
match l with 
| [] => if eqb n 0 
				then list _ v []
				else []
| list _ val l' => if eqb n 0
									 then list _ v (list _ val l')
									 else list _ val (insertEnumInList l' (n - 1) v)
end.

Definition pushBackEnum (e: Enum) (n: EnumTypes) :=
match e with 
| EN l => EN (insertEnumInList l (getListLength l) n)
end.


(* Enum Front Push *)

Definition pushFrontEnum (e: Enum) (n: EnumTypes) :=
match e with 
| EN l => EN (insertEnumInList l 0 n)
end.


(* Enum Back Pop *)

Definition deleteEnumFromList (l: List EnumTypes) (n: nat) := deleteFromList l n.

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




(*** Environment Setup ***)



Definition Environment := string -> ResultTypes.

Definition InitialEnvironment : Environment := fun _ => undeclared.

Definition update (env: Environment) (s: string) (v: ResultTypes) :=
fun x => if (string_beq x s)
         then v
         else env x.

Definition env1 := update InitialEnvironment "a1" natArray123.

Compute env1 "a1".

Definition unpack (env: Environment) (s: string) :=
match env s with
| arrays a => a
| _ => errArray
end.

Compute popBackArray (unpack env1 "a1").



(*** Exp Evaluation ***)

Fixpoint Exp_Eval (exp : Exp) (env: Environment) : ResultTypes := 
match exp with
| anum n => n
| avar v => env v
| a1 +' a2 => tplus (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 -' a2 => tminus (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 *' a2 => tmul (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 /' a2 => tdiv (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 ^' a2 => tpow (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 %' a2 => tmodulo (Exp_Eval a1 env) (Exp_Eval a2 env)
| bval b => b
| btrue => true
| bfalse => false
| bnot b => tnot (Exp_Eval b env)
| b1 &&' b2 => tand (Exp_Eval b1 env) (Exp_Eval b2 env)
| b1 ||' b2 => tor (Exp_Eval b1 env) (Exp_Eval b2 env)
| a1 <' a2 => tlt (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 <=' a2 => tlte (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 >' a2 => tgt (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 >=' a2 => tgte (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 ==' a2 => teq (Exp_Eval a1 env) (Exp_Eval a2 env)
| a1 !=' a2 => tneq (Exp_Eval a1 env) (Exp_Eval a2 env)
| sstr s => s
| s1 splus s2 => tsplus (Exp_Eval s1 env) (Exp_Eval s2 env)
| a smul b => tsmul (Exp_Eval a env) (Exp_Eval b env)
end.

Reserved Notation "E =[ S ]=> E'" (at level 60).

Definition typeOf (x: ResultTypes) : Type :=
match x with
| nrNats n => Nat
| valBools b => Bool
| sStrings s => String
| lists T l => List T
| arrays a => Array
| enums e => Enum
| structs s => Struct
| _ => ResultTypes
end.



Definition sameType (t1 t2: Type) : bool :=
match t1, t2 with
| Nat, Nat => true
end.
(*
Fixpoint execute (s: Statement) (env: Environment) (gas: nat) : Environment :=
match gas with
| 0 => env
| S gas' => match s with
						| decNatVar v => update env v unassignedNat
						| decBoolVar v => update env v unassignedBool
						| decStringVar v => update env v unassignedString

						| asnNatVar v e => update env v e
						| asnBoolVar v e => update env v e
						| asnStringVar v e => update env v e

						| initNatVar v e => update env v e
						| initBoolVar v e => update env v e
						| initStringVar v e => update env v e

						| decNatList v => update env v unassignedList
						| decBoolList v => update env v unassignedList
						| decStringList v => update env v unassignedList

						| initNatList v e => update env v e
						| initBoolList v e => update env v e
						| initStringList v e => update env v e

						| asnNatList v e => update env v e
						| asnBoolList v e => update env v e
						| asnStringList v e => update env v e

						| insNatInList l n v => update env l (insertNatInList (env l) n v)
						| insBoolInList l n v => update env l (insertBoolInList (env l) n v)
						| insStringInList l n v => update env l (insertStringInList (env l) n v)

						| appNatToList l1 l2 => update env l1 (appendNatToList (env l1) (env l2))
						| appBoolToList l1 l2 => update env l1 (appendNatToList (env l1) (env l2))
						| appStringToList l1 l2 => update env l1 (appendNatToList (env l1) (env l2))

						| delNatFromList l n => update env l (deleteNatFromList (env l) n)
						| delBoolFromList l n => update env l (deleteBoolFromList (env l) n)
						| delStringFromList l n => update env l (deleteStringFromList (env l) n)
(* work in progress *)
						| trNatList: string -> Statement
						| trBoolList: string -> Statement
						| trStringList: string -> Statement

						| gtFromList: string -> nat -> Statement

						| decNatArray: string -> Statement
						| decBoolArray: string -> Statement
						| decStringArray: string -> Statement
						| decMultipleArray: string -> Statement

						| initNatArray: string -> Array -> Statement
						| initBoolArray: string -> Array -> Statement
						| initStringArray: string -> Array -> Statement
						| initMultipleArray: string -> Array -> Statement

						| asnNatArray: string -> string -> Statement
						| asnBoolArray: string -> string -> Statement
						| asnStringArray: string -> string -> Statement
						| asnMultipleArray: string -> string -> Statement

						| stArrayNat: string -> nat -> Nat -> Statement
						| stArrayBool: string -> nat -> Bool -> Statement
						| stArrayString: string -> nat -> String -> Statement
						| stArrayArray: string -> nat -> Array -> Statement

						| pshFrontArrayNat: string -> Nat -> Statement
						| pshFrontArrayBool: string -> Bool -> Statement
						| pshFrontArrayString: string -> String -> Statement
						| pshFrontArrayArray: string -> Array -> Statement

						| pshBackArrayNat: string -> Nat -> Statement
						| pshBackArrayBool: string -> Bool -> Statement
						| pshBackArrayString: string -> String -> Statement
						| pshBackArrayArray: string -> Array -> Statement

						| ppFrontArrayNat: string -> Statement
						| ppFrontArrayBool: string -> Statement
						| ppFrontArrayString: string -> Statement
						| ppFrontArrayArray: string -> Statement

						| ppBackArrayNat: string -> Statement
						| ppBackArrayBool: string -> Statement
						| ppBackArrayString: string -> Statement
						| ppBackArrayArray: string -> Statement

						| gtArrayValue: string -> nat -> Statement

						| decEnum: string -> Statement
						| initEnum: string -> Enum -> Statement
						| asnEnum: string -> string -> Statement

						| pshFrontEnum: string -> EnumTypes -> Statement
						| pshBackEnum: string -> EnumTypes -> Statement
						| ppFrontEnum: string -> Statement
						| ppBackEnum: string -> Statement

						| stEnum: string -> nat -> EnumTypes -> Statement
						| gtEnum: string -> nat -> Statement

						| initStruct: string -> Struct -> Statement
						|	asnStruct: string -> string -> Statement

						| gtStructField: string -> string -> Statement
						| stStructField: string -> string -> FieldTypes -> Statement

						| ifThen: Exp -> Statement -> Statement
						| ifThenElse: Exp -> Statement -> Statement -> Statement
						| doWhileLoop: Statement -> Exp -> Statement
						| whileLoop: Exp -> Statement -> Statement
						| forLoop: Statement -> Exp -> Statement -> Statement -> Statement
						| sequence: Statement -> Statement -> Statement

						| break
						| continue

						| switchCase: string -> List (Pair Nat Statement) -> Statement
end.

Inductive Exp_Eval_Prop : Exp -> Environment -> ResultTypes -> Prop :=
| const: forall n st, anum n =[ st ]=> n
| lookup: forall x st, avar x =[ st ]=> (st x)
(* plus *)
| plusLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' +' a2 ->
    a1 +' a2 =[ st ]=> a
| plusRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 +' a2' ->
    a1 +' a2 =[ st ]=> a
| plusCons: forall i i1 i2 st,
    i = i1 + i2 ->
    anum i1 +' anum i2 =[ st ]=> i
(* minus *)
| minusLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' -' a2 ->
    a1 -' a2 =[ st ]=> a
| minusRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 -' a2' ->
    a1 -' a2 =[ st ]=> a
| minusCons: forall i i1 i2 st,
    i = i1 - i2 ->
    anum i1 -' anum i2 =[ st ]=> i
(* mul *)
| mulLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' *' a2 ->
    a1 *' a2 =[ st ]=> a
| mulRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 *' a2' ->
    a1 *' a2 =[ st ]=> a
| mulCons: forall i i1 i2 st,
    i = i1 * i2 ->
    anum i1 *' anum i2 =[ st ]=> i
(* div *)
| divLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' /' a2 ->
    a1 /' a2 =[ st ]=> a
| divRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 /' a2' ->
    a1 /' a2 =[ st ]=> a
| divCons: forall i i1 i2 st,
    i = div i1 i2 ->
    anum i1 /' anum i2 =[ st ]=> i
(* power *)
| powLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' ^' a2 ->
    a1 ^' a2 =[ st ]=> a
| powRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 ^' a2' ->
    a1 ^' a2 =[ st ]=> a
| powCons: forall i i1 i2 st,
    i = pow i1 i2 ->
    anum i1 ^' anum i2 =[ st ]=> i
(* div *)
| modLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' %' a2 ->
    a1 %' a2 =[ st ]=> a
| modRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 %' a2' ->
    a1 %' a2 =[ st ]=> a
| modCons: forall i i1 i2 st,
    i = modulo i1 i2 ->
    anum i1 %' anum i2 =[ st ]=> i

(* BOOL *)

| true: forall st, btrue =[ st ]=> btrue
| false: forall st, bfalse =[ st ]=> bfalse
(* not *)
| not: forall b b' st,
    b =[ st ]=> b' ->
    (bnot b) =[ st ]=> (bnot b')
| notTrue: forall st,
    (bnot btrue) =[ st ]=> bfalse
| notFalse: forall st,
    (bnot bfalse) =[ st ]=> btrue
(* and *)
| and: forall b1 b1' b2 st,
    b1 =[ st ]=> b1' ->
    (b1 &&' b2) =[ st ]=> (b1' &&' b2) 
| andTrue : forall b2 st,
    (btrue &&' b2) =[ st ]=> b2
| andFalse : forall b2 st,
    (bfalse &&' b2) =[ st ]=> bfalse
(* or *)
| or: forall b1 b1' b2 st,
    b1 =[ st ]=> b1' ->
    (b1 ||' b2) =[ st ]=> (b1' ||' b2) 
| orTrue: forall b2 st,
    (btrue &&' b2) =[ st ]=> btrue
| orFalse: forall b2 st,
    (bfalse &&' b2) =[ st ]=> b2
(* less *)
| lessThanLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    a1 <' a2 =[ st ]=> a1' <' a2
| lessThanRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    (anum i1) <' a2 =[ st ]=> (anum i1) <' a2'
| lessThan : forall b i1 i2 st,
    b = (if (Nat.ltb i1 i2) then btrue else bfalse) ->
    (anum i1) <' (anum i2) =[ st ]=> b
(* less equal *)
| lessEqualThanLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    a1 <=' a2 =[ st ]=> a1' <=' a2
| lessEqualThanRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    (anum i1) <=' a2 =[ st ]=> (anum i1) <=' a2'
| lessEqualThan : forall b i1 i2 st,
    b = (if (Nat.leb i1 i2) then btrue else bfalse) ->
    (anum i1) <=' (anum i2) =[ st ]=> b
(* greater *)
| greaterThanLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    a1 >' a2 =[ st ]=> a1' >' a2
| greaterThanRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    (anum i1) >' a2 =[ st ]=> (anum i1) >' a2'
| greaterThan : forall b i1 i2 st,
    b = (if negb (Nat.leb i1 i2) then btrue else bfalse) ->
    (anum i1) >' (anum i2) =[ st ]=> b

(* greater equal *)

| greaterEqualThanLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    a1 >=' a2 =[ st ]=> a1' >=' a2
| greaterEqualThanRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    (anum i1) >=' a2 =[ st ]=> (anum i1) >=' a2'
| greaterEqualThan: forall b i1 i2 st,
    b = (if negb (Nat.ltb i1 i2) then btrue else bfalse) ->
    (anum i1) >=' (anum i2) =[ st ]=> b

(* equal *)

| equalLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    a1 ==' a2 =[ st ]=> a1' ==' a2
| equalRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    (anum i1) ==' a2 =[ st ]=> (anum i1) ==' a2'
| equal: forall b i1 i2 st,
    b = (if (Nat.eqb i1 i2) then btrue else bfalse) ->
    (anum i1) ==' (anum i2) =[ st ]=> b

(* equal *)

| notEqualLeft: forall a1 a1' a2 st,
    a1 =[ st ]=> a1' -> 
    a1 !=' a2 =[ st ]=> a1' !=' a2
| notEqualRight: forall i1 a2 a2' st,
    a2 =[ st ]=> a2' ->
    (anum i1) !=' a2 =[ st ]=> (anum i1) !=' a2'
| notEqual: forall b i1 i2 st,
    b = (if negb (Nat.eqb i1 i2) then btrue else bfalse) ->
    (anum i1) !=' (anum i2) =[ st ]=> b

(* STRING *)

| str: forall s st, sstr s =[ st ]=> s

(* plus *)

| strPlusLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' ++' a2 ->
    a1 ++' a2 =[ st ]=> a
| strPlusRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 ++' a2' ->
    a1 ++' a2 =[ st ]=> a
| strPlusCons: forall i i1 i2 st,
    i = i1 ++ i2 ->
    (sstr i1) ++' (sstr i2) =[ st ]=> i

(* mul string nat *)

| snMulLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' *+' a2 ->
    a1 *+' a2 =[ st ]=> a
| snMulRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 *+' a2' ->
    a1 *+' a2 =[ st ]=> a
| snMulCons: forall i i1 i2 st,
    i = strMul i1 i2 ->
    (sstr i1) *+' (anum i2) =[ st ]=> i

(* mul nat string *)

| nsMulLeft: forall a1 a1' a2 a st,
    a1 =[ st ]=> a1' ->
    a = a1' *+' a2 ->
    a1 *+' a2 =[ st ]=> a
| nsMulRight: forall a1 a2 a2' a st,
    a2 =[ st ]=> a2' ->
    a = a1 *+' a2' ->
    a1 *+' a2 =[ st ]=> a
| nsMulCons: forall i i1 i2 st,
    i = strMul i2 i1 ->
    (anum i1) *+' (sstr i2) =[ st ]=> i

where "E =[ S ]=> E'" := (Exp_Eval_Prop E S E').

*)







