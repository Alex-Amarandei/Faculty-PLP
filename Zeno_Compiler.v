Require Import Ascii.
Require Import Bool.
Require Import Coq.Strings.Byte.
Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.
Require Import Nat.
Require Import List.
Import ListNotations.


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
| S b' => append a ( strMul a b' )
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

Compute tplus 4 5. Compute tplus true false.
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
| sString a, sString b => string_beq a b
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

Definition Environment := string -> Number.

Definition default (x: Number) : Environment := fun _ => x.

Definition update (env: Environment) (s: string) (v: Number) :=
fun x => if (eqb_string x s)
         then v
         else env x.

Fixpoint Exp_Eval (exp : Exp) (env: Environment) : Number := 
match exp with
| anum n => n
| avar v => env v
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


(*
((76 + (2^2) * (100 + (7 * true) + 13 * (7^false) / true) / (1308 - 28 * 46)) / 10) * "--plp"

((76 + 4 * (100 + 7 + 13 * 1 / true) / (1308 - 1288)) / 10) * "--plp"

((76 + 4 * 120 / 20) / 10) * "--plp"

(100 / 10) * "--plp"

--plp--plp--plp--plp--plp--plp--plp--plp--plp--plp

*)

Definition newEnv := update (update (default 2) "x" 7) "t" 13.

Compute tmul ( Exp_Eval ( ( 76 +' ( "y" ^' "z" ) *' ( 100 +' ( "x" *' true) +' "t" *' ( "x" ^' false ) /' true ) /' ( 1308 -' 28 *' 46) ) /' 10) newEnv ) "--plp".

Inductive Instruction :=
| push_num (n: Number)
| push_var (x: string)
| i_add | i_min
| i_mul | i_div
| i_pow | i_mod
| i_not | i_and | i_or
| i_lt  | i_lte | i_gt  | i_gte
| i_eq  | i_neq.

Compute push_num 6. Compute push_var "x".
Compute i_add. Compute i_min.
Compute i_mul. Compute i_div.
Compute i_pow. Compute i_mod.
Compute i_not. Compute i_and. Compute i_or.
Compute i_lt . Compute i_lte. Compute i_gt. Compute i_gte.
Compute i_eq . Compute i_neq.

Definition NumberOnlyEnvironment := string -> Number.

Definition Stack := list Number.

Definition runOne (i : Instruction) (env: NumberOnlyEnvironment) (stack : Stack) : Stack :=
match i with
| push_num n => n :: stack
| push_var x => (env x) :: stack
| i_add => match stack with
					| n1 :: n2 :: stack' => (tplus n1 n2) :: stack'
					| _ => stack
					end
| i_min => match stack with
					| n1 :: n2 :: stack' => (tminus n1 n2) :: stack'
					| _ => stack
					end
| i_mul => match stack with
					| n1 :: n2 :: stack' => (tmul n1 n2) :: stack'
					| _ => stack
					end
| i_div => match stack with
					| n1 :: n2 :: stack' => (tdiv n1 n2) :: stack'
					| _ => stack
					end
| i_pow => match stack with
					| n1 :: n2 :: stack' => (tpow n1 n2) :: stack'
					| _ => stack
					end
| i_mod => match stack with
					| n1 :: n2 :: stack' => (tmod n1 n2) :: stack'
					| _ => stack
					end
| i_not => match stack with
					| n :: stack' => bBools (tnot n) :: stack'
					| _ => stack
					end
| i_and => match stack with
					| n1 :: n2 :: stack' => bBools (tand n1 n2) :: stack'
					| _ => stack
					end
| i_or => match stack with
					| n1 :: n2 :: stack' => bBools (tor n1 n2) :: stack'
					| _ => stack
					end
| i_lt => match stack with
					| n1 :: n2 :: stack' => bBools (tlt n1 n2) :: stack'
					| _ => stack
					end
| i_lte => match stack with
					| n1 :: n2 :: stack' => bBools (tlte n1 n2) :: stack'
					| _ => stack
					end
| i_gt => match stack with
					| n1 :: n2 :: stack' => bBools (tgt n1 n2) :: stack'
					| _ => stack
					end
| i_gte => match stack with
					| n1 :: n2 :: stack' => bBools (tgte n1 n2) :: stack'
					| _ => stack
					end
| i_eq => match stack with
					| n1 :: n2 :: stack' => bBools (teq n1 n2) :: stack'
					| _ => stack
					end
| i_neq => match stack with
					| n1 :: n2 :: stack' => bBools (tneq n1 n2) :: stack'
					| _ => stack
					end
end.

Compute (runOne (push_num 53) (default 0) []).
Compute (runOne (push_var "x") (default 0) []).
Compute (runOne i_add (default 0) [nNats 10; nNats 12; nNats 20]).
Compute (runOne i_mul (default 0) [nNats 10; nNats 12; nNats 20]).

Fixpoint runAll (is' : list Instruction) (env : Environment) (stack : Stack) : Stack :=
match is' with
| [] => stack
| i :: is'' => runAll is'' env (runOne i env stack)
end.

Definition ex1 := [
                    push_num 21 ;
                    push_var "x"
                  ].
Compute runAll ex1 (default 5) [].

Definition ex2 := [
										push_var "x";
                    push_num 21 ;
                    push_var "x" ;
                    i_mul;
                    i_min
                  ].
Compute runAll ex2 (default 5) [].

Fixpoint compile (e : Exp) : list Instruction :=
match e with
| anum c => [push_num c]
| avar x => [push_var x]
| e1 +' e2 => (compile e2) ++ (compile e1) ++ [i_add]
| e1 -' e2 => (compile e2) ++ (compile e1) ++ [i_min]
| e1 *' e2 => (compile e2) ++ (compile e1) ++ [i_mul]
| e1 /' e2 => (compile e2) ++ (compile e1) ++ [i_div]
| e1 ^' e2 => (compile e2) ++ (compile e1) ++ [i_pow]
| e1 %' e2 => (compile e2) ++ (compile e1) ++ [i_mod]
| !' e => (compile e) ++ [i_not]
| e1 &&' e2 => (compile e2) ++ (compile e1) ++ [i_and]
| e1 ||' e2 => (compile e2) ++ (compile e1) ++ [i_or]
| e1 <' e2 => (compile e2) ++ (compile e1) ++ [i_lt]
| e1 <=' e2 => (compile e2) ++ (compile e1) ++ [i_lte]
| e1 >' e2 => (compile e2) ++ (compile e1) ++ [i_gt]
| e1 >=' e2 => (compile e2) ++ (compile e1) ++ [i_gte]
| e1 ==' e2 => (compile e2) ++ (compile e1) ++ [i_eq]
| e1 !=' e2 => (compile e2) ++ (compile e1) ++ [i_neq]
end.

Compute compile (5 +' "x").
Compute compile (5 +' "x" *' 3).
Compute compile (5 *' "x" +' 3).

Compute Exp_Eval (5 *' "x" +' 3) (default 5).
Compute runAll (compile (5 *' "x" +' 3)) (default 5) [].

Theorem tplus_comm: forall a b,
tplus a b = tplus b a.
Proof.
intros a b.
induction a. destruct b.
- unfold tplus.
-- induction n.
--- induction n0.
---- rewrite PeanoNat.Nat.add_comm. reflexivity.
---- reflexivity.
--- induction n0. reflexivity. reflexivity.
- unfold tplus.
-- induction n.
--- induction b.
---- reflexivity.
---- reflexivity.
--- induction b. reflexivity. reflexivity.
- unfold tplus. reflexivity.
- simpl. reflexivity.
- unfold tplus.
-- induction b.
--- induction n.
---- induction b0. reflexivity. reflexivity.
---- induction b0. reflexivity. reflexivity.
--- induction b0.
---- induction b.
----- induction b. reflexivity. reflexivity.
----- reflexivity.
---- induction b. reflexivity. reflexivity.
--- reflexivity.
--- reflexivity.
- unfold tplus.
-- induction b. reflexivity. reflexivity.
--- induction s. induction s0.
reflexivity. reflexivity. reflexivity.
--- reflexivity.
- simpl.
-- unfold tplus.
--- induction b.
reflexivity. reflexivity. reflexivity. reflexivity.
Qed.

Theorem tmul_comm: forall a b,
tmul a b = tmul b a.
Proof.
intros a b.
induction a. destruct b.
- unfold tmul.
-- induction n.
--- induction n0.
---- rewrite PeanoNat.Nat.mul_comm. reflexivity.
---- reflexivity.
--- induction n0. reflexivity. reflexivity.
- unfold tmul.
-- induction n.
--- induction b.
---- reflexivity.
---- reflexivity.
--- induction b. reflexivity. reflexivity.
- unfold tmul.
-- induction n.
--- induction s. reflexivity. reflexivity.
--- induction s. reflexivity. reflexivity.
- simpl. reflexivity.
- unfold tmul.
-- induction b.
--- induction n.
---- induction b0. reflexivity. reflexivity.
---- induction b0. reflexivity. reflexivity.
--- induction b0.
---- induction b.
----- induction b. reflexivity. induction b0.
			reflexivity. reflexivity.
----- reflexivity. 
---- induction b. reflexivity. reflexivity.
--- reflexivity.
--- reflexivity.
- unfold tmul.
-- induction b.
--- induction s.
---- induction n. reflexivity. reflexivity.
---- induction n. reflexivity. reflexivity.
--- reflexivity.
--- reflexivity.
--- reflexivity.
- simpl.
-- unfold tmul.
--- induction b.
reflexivity. reflexivity. reflexivity. reflexivity.
Qed.

Theorem tand_comm: forall a b, tand a b = tand b a.
Proof.
intros a b.
induction a. destruct b.
- unfold tand.
-- induction n. induction n0. induction n. induction n0.
--- reflexivity.
--- reflexivity.
--- reflexivity.
--- reflexivity.
--- induction n0. reflexivity. reflexivity.
- unfold tand.
-- induction n.
--- induction b. induction n. induction b.
---- reflexivity.
---- reflexivity.
---- reflexivity.
---- reflexivity.
--- induction b. reflexivity. reflexivity.
- unfold tand.
-- induction n.
--- induction s. reflexivity. reflexivity.
--- induction s. reflexivity. reflexivity.
- simpl. induction n. reflexivity. reflexivity.
- unfold tand.
-- induction b. induction b0. induction n. induction b. induction n. reflexivity. reflexivity. induction n. reflexivity. reflexivity. reflexivity. induction n. reflexivity. reflexivity.
--- induction b. induction b0. induction b0.
---- reflexivity.
---- induction b. reflexivity. reflexivity.
---- reflexivity.
---- induction b0. reflexivity. reflexivity.
--- induction b0. induction s. reflexivity. reflexivity.
---- induction s. reflexivity. reflexivity.
--- induction b0. reflexivity. reflexivity.
- unfold tand. induction b. induction s. induction n.
-- reflexivity. 
-- reflexivity.
-- induction n. reflexivity. reflexivity.
-- induction s. induction b. reflexivity. reflexivity.
	 induction b. reflexivity. reflexivity.
-- induction s. induction s0. reflexivity. reflexivity.
	 induction s0. reflexivity. reflexivity.
-- induction s. reflexivity. reflexivity.
- simpl. induction b.
-- induction n. induction n.
--- simpl. reflexivity.
--- simpl. reflexivity.
--- simpl. reflexivity.
-- simpl. induction b. reflexivity. reflexivity.
-- simpl. induction s. reflexivity. reflexivity.
-- simpl. reflexivity.
Qed.

Theorem tor_comm: forall a b,
tor a b = tor b a.
Proof.
intros a b.
induction a. destruct b.
- unfold tor.
-- induction n. induction n0. induction n. induction n0.
--- reflexivity.
--- reflexivity.
--- induction n0. reflexivity. reflexivity.
--- reflexivity. 
--- induction n0. reflexivity. reflexivity.
- unfold tor.
-- induction n.
--- induction b. induction n. induction b.
---- reflexivity.
---- reflexivity.
---- induction b. reflexivity. reflexivity.
---- reflexivity.
--- induction b. reflexivity. reflexivity.
- unfold tor.
-- induction n.
--- induction s. reflexivity. reflexivity.
--- induction s. reflexivity. reflexivity.
- simpl. induction n. reflexivity. reflexivity.
- unfold tor.
-- induction b. induction b0. induction n. induction b. induction n. reflexivity. reflexivity. induction n. reflexivity. reflexivity. reflexivity. induction n. reflexivity. reflexivity.
--- induction b. induction b0. induction b0.
---- induction b. reflexivity. reflexivity.
---- reflexivity.
---- reflexivity.
---- induction b0. reflexivity. reflexivity.
--- induction b0. induction s. reflexivity. reflexivity.
---- induction s. reflexivity. reflexivity. 
--- induction b0. reflexivity. reflexivity.
- unfold tor. induction b. induction s. induction n.
-- reflexivity. 
-- reflexivity.
-- induction n. reflexivity. reflexivity.
-- induction s. induction b. reflexivity. reflexivity.
	 induction b. reflexivity. reflexivity.
-- induction s. induction s0. reflexivity. reflexivity.
	 induction s0. reflexivity. reflexivity.
-- induction s. reflexivity. reflexivity.
- simpl. induction b.
-- induction n. induction n.
--- simpl. reflexivity.
--- simpl. reflexivity.
--- simpl. reflexivity.
-- simpl. induction b. reflexivity. reflexivity.
-- simpl. induction s. reflexivity. reflexivity.
-- simpl. reflexivity.
Qed.

Lemma soundness_helper :
  forall e env stack is',
    runAll (compile e ++ is') env stack =
    runAll is' env ((Exp_Eval e env) :: stack).
Proof.
  induction e; intros; simpl; trivial.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite IHe.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
  - rewrite <- app_assoc.
    rewrite <- app_assoc.
    rewrite IHe2.
    rewrite IHe1.
    simpl.
    reflexivity.
Qed.

Theorem soundness :
  forall e env,
    runAll (compile e) env [] =
    [Exp_Eval e env].
Proof.
  intros.
  rewrite <- app_nil_r with (l := (compile e)).
  rewrite soundness_helper.
  simpl. trivial.
Qed.
















