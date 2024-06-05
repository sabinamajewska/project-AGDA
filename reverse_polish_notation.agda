module reverse_polish_notation where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≡ᵇ_; _∸_)
open import Data.Bool using (true; false)
open Eq using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (List; _++_; []; _∷_; [_])
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

-- Jezyk 1 - stale, dodawanie i mnozenie
data Expr : Set where
  Const : ℕ → Expr
  Add   : Expr
  Mult  : Expr

-- semantyka jezyka 1
s1 : List ℕ → List Expr → ℕ
s1 vs ((Const n) ∷ ls) = s1 (n ∷ vs) ls
s1 (x ∷ y ∷ l) (Add ∷ ls) = s1 ((x + y) ∷ l) ls
s1 (x ∷ y ∷ l) (Mult ∷ ls) = s1 ((x * y) ∷ l) ls
s1 _ _ = 0


-- Jezyk 2 - prosty assembler z pamiecia, operacje ustawienia akumulatora, wczytania z pamieci, zapisu do pamieci, dodawania i mnozenia
data Opper : Set where
  SetOp : ℕ → Opper
  Load  : ℕ → Opper
  Store : ℕ → Opper
  Add   : ℕ → Opper
  Mul   : ℕ → Opper


-- przypisanie do komorki wartosci - mozna dodac aliasy, zeby było wiadomo o co chodzi odrazu
data Assignment : Set where
  _to_ : ℕ → ℕ → Assignment


-- kontekst - lista przypisan
data Context : Set where
  empty : Context
  _:+:_ : Assignment → Context → Context

infixr 5 _:+:_

-- Stan calego programu, stan akumulatora i calej pamieci
record MachineState : Set where
  field
    accumulator : ℕ
    memory      : Context
open MachineState public

-- pusty stan
initState : MachineState
initState = record { accumulator = 0; memory = empty }


-- funkcja pomocnicza do pobierania wartosci z kontekstu
retrieve : ℕ → Context → ℕ
retrieve _ empty = 0
retrieve x (y to v :+: c) with x ≡ᵇ y
... | true = v
... | false = retrieve x c

-- funkcja pomocnicza do dodawania przypisan do kontekstu
store : ℕ → MachineState → Context
store x state = x to accumulator state :+: memory state


-- semantyka dla jezyka 2 - co sie dzieje ze stanem jak wykonujemy pewna operacje
opperSemantics : Opper → MachineState → MachineState
opperSemantics (SetOp n) state = record state { accumulator = n }
opperSemantics (Load x) state = record state { accumulator = retrieve x (memory state) }
opperSemantics (Store x) state = record state { memory = store x state }
opperSemantics (Add x) state = record state { accumulator = accumulator state + retrieve x (memory state) }
opperSemantics (Mul x) state = record state { accumulator = accumulator state * retrieve x (memory state) }

-- jak wykonuje sie caly program - po kolei komendy, ale zaczynamy od pustego stanu - nie konczymy na pustej pamieci, a moze powinnismy?
s2 : List Opper → MachineState
s2 l = (go initState l)
  where
    go : MachineState → List Opper → MachineState
    go state [] = state
    go state (op ∷ ops) = go (opperSemantics op state) ops

-- dodac jakis przyklad, 3 operacje

-- zamiana jezyka 1 na 2
c' : Expr → ℕ → List Opper
c' (Const n) i = [ SetOp n ] ++ [ Store (i + 1) ]
c' Add i = [ Load (i ∸ 1) ] ++ [ Add i ] ++ [ Store (i ∸ 1) ]
c' Mult i = [ Load (i ∸ 1) ] ++ [ Mul i ] ++ [ Store (i ∸ 1) ]

go : List Expr → ℕ → List Opper
go [] _ = []
go ((Const n) ∷ es) i = c' (Const n) i ++ go es (i + 1)
go (Add ∷ es) i = c' Add i ++ go es (i ∸ 1)
go (Mult ∷ es) i = c' Mult i ++ go es (i ∸ 1)

c : List Expr → List Opper
c l = go l 0

-- w tresci zadania , nie ma nic w pamieci, a w akumulatorze jest n
t : ℕ → MachineState
t n = record { accumulator = n; memory = empty }


-- To chcemy udowodnic `t * s1 = s2 * c`?
proof : (l : List Expr) → ( i : ℕ ) → (accumulator (s2 (c l))) ≡ (s1 [] l)
proof ((Const x) ∷ ls) i = {!   !}
  where
    thes : (i : ℕ) → (accumulator (s2 (c ls))) ≡ (s1 [] ls)
    thes i = {!   !}
    thes2 : s1 [] ((Const x) ∷ ls) ≡ x
    thes2 = {!   !}
    thes3 : (accumulator (s2 [ SetOp x ])) ≡ x
    thes3 = {!   !}
    thes4 : (accumulator (s2 [ SetOp x ])) ≡ (s1 [] ((Const x) ∷ ls))
    thes4 = {!   !}
proof (Add ∷ ls) i = {!   !}
proof (Mult ∷ ls) i = {!   !} 
proof [] _ = refl