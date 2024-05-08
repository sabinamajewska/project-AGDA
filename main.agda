module main where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open Eq using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (List; _++_; []; _∷_; [_])
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

-- Define the data type for arithmetic expressions
data Expr : Set where
  Const : ℕ → Expr
  Add   : Expr → Expr → Expr
  Mult  : Expr → Expr → Expr

-- Define the semantics function for evaluating arithmetic expressions
s1 : Expr → ℕ
s1 (Const n) = n
s1 (Add e1 e2) = s1 e1 + s1 e2
s1 (Mult e1 e2) = s1 e1 * s1 e2