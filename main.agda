module main where

import Relation.Binary.PropositionalEquality as Eq
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open Eq using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Data.List using (List; _++_; []; _∷_; [_])
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


-- Jezyk 1 - stale, dodawanie i mnozenie
data Expr : Set where
  Const : ℕ → Expr
  Add   : Expr → Expr → Expr
  Mult  : Expr → Expr → Expr

-- semantyka jezyka 1
s1 : Expr → ℕ
s1 (Const n) = n
s1 (Add e1 e2) = s1 e1 + s1 e2
s1 (Mult e1 e2) = s1 e1 * s1 e2


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

-- porownywanie liczb naturalnych
rownoscDlaN : ∀ {x y : ℕ} → Dec (x ≡ y)
rownoscDlaN {zero} {zero} = yes refl
rownoscDlaN {zero} {suc y} = no (λ())
rownoscDlaN {suc x} {zero} = no (λ ())
rownoscDlaN {suc x} {suc y} with (rownoscDlaN {x} {y})
... | yes x=y = yes (cong suc x=y)
... | no x≠y = no (lemat x≠y) 
      where
        lemat : ¬ x ≡ y → suc x ≡ suc y → ⊥
        lemat p1 refl = p1 refl

-- typ dzięki ktoremu jestesmy w stanie wywnioskować czy dane przypisanie jest w kontekście - moze sie okazac niepotrzebne
data _contains_ : Context → Assignment → Set where
  top : ∀ { a : Assignment } → ∀ { c : Context }
    →  (a :+: c) contains a
  tail : ∀ { x y } → ∀ { m n } → ∀ { c : Context  }
    → ( c contains ( x to n ) )
    → ¬ ( x ≡ y ) -- dodatkowo zakładamy, że jeśli sprawdzamy, czy zmienna jest dalej w ciągu, to upewniamy się,
                  -- że nie jest na pierwszej pozycji
    → ( y to m :+: c ) contains (x to n)


-- funkcja pomocnicza do sprawdzania czy przypisanie jest w kontekście
_contains?_ : (c : Context) → (a : Assignment) → Dec (c contains a)
_contains?_ empty _ = no (λ ())
_contains?_ (x to n :+: c) (y to m) with rownoscDlaN {x} {y}
... | yes x=y with rownoscDlaN {n} {m}
...    | yes n=m = yes (lemma x=y n=m) 
       where 
          lemma : ∀ {x y n m} → ∀ { c : Context } → x ≡ y → n ≡ m → (( x to n ) :+: c) contains (y to m)
          lemma refl refl = top
...    | no n≠m = no (lemma x=y n≠m)
       where 
          lemma : ∀ {x y n m} → ∀ { c : Context } → x ≡ y → ¬ (n ≡ m) → ¬ ((( x to n ) :+: c) contains (y to m))
          lemma refl n≠m top = n≠m refl
          lemma refl n≠m (tail c x≠y) = x≠y refl
_contains?_ (x to n :+: c) (y to m) | no x≠y with _contains?_ c (y to m)
...    | yes yinc = yes (tail yinc (lemma x≠y))
        where 
            lemma : ¬ x ≡ y → ¬ (y ≡ x)
            lemma x≠y refl = x≠y refl
...    | no ynotinc = no ((lemma x≠y ynotinc))
       where 
          lemma : ∀ {x y n m} → ¬ x ≡ y → ¬ (c contains (y to m)) → ¬ ((x to n :+: c) contains (y to m))
          lemma x≠y ynotinc top = x≠y refl
          lemma x≠y ynotinc (tail yinxc x) = ynotinc yinxc

-- funkcja pomocnicza do pobierania wartosci z kontekstu
retrieve : ℕ → Context → ℕ
retrieve _ empty = 0
retrieve x (y to v :+: c) with rownoscDlaN {x} {y}
... | yes _ = v
... | no _ = retrieve x c

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

-- zamiana jezyka 1 na 2
c : Expr → ℕ → List Opper
c (Const n) i = [ SetOp n ] ++ [ Store i ]
c (Add e1 e2) i = c e1 i ++ c e2 (1 + i) ++ [ Load (1 + i) ] ++ [ Add i ] ++ [ Store i ]
c (Mult e1 e2) i = c e1 i ++ c e2 (1 + i) ++ [ Load (1 + i) ] ++ [ Mul i ] ++ [ Store i ]

-- w tresci zadania , nie ma nic w pamieci, a w akumulatorze jest n
t : ℕ → MachineState
t n = record { accumulator = n; memory = empty }


addEval : ∀ (e1 e2 : Expr) → s1 (Add e1 e2) ≡ s1 e1 + s1 e2
addEval e1 e2 = refl

mulEval : ∀ (e1 e2 : Expr) → s1 (Mult e1 e2) ≡ s1 e1 * s1 e2
mulEval e1 e2 = refl

postulate addSemantics : ∀ (e1 e2 : Expr) → (i : ℕ) → (accumulator (s2 (c (Add e1 e2) i))) ≡ (accumulator (s2 (c e1 i))) + (accumulator (s2 (c e2 (i + 1))))

postulate multSemantics : ∀ (e1 e2 : Expr) → (i : ℕ) → (accumulator (s2 (c (Mult e1 e2) i))) ≡ (accumulator (s2 (c e1 i))) * (accumulator (s2 (c e2 (i + 1))))

-- To chcemy udowodnic `t * s1 = s2 * c`?
proof : (e : Expr) → ( i : ℕ ) → (accumulator (s2 (c e i))) ≡ s1 e
proof (Const x) _ = refl
proof (Add e1 e2) i = begin
      accumulator (s2 (c (Add e1 e2) i))
      ≡⟨ addSemantics e1 e2 i ⟩ accumulator (s2 (c e1 i)) + accumulator (s2 (c e2 (i + 1)))
      ≡⟨ cong (λ x → x + accumulator (s2 (c e2 (i + 1)))) (proof1) ⟩ s1 e1 + accumulator (s2 (c e2 (i + 1)))
      ≡⟨ cong (λ x → s1 e1 + x) (proof2) ⟩ s1 e1 + s1 e2
      ≡⟨ addEval e1 e2 ⟩ s1 e1 + s1 e2
      ≡⟨ sym (addEval e1 e2) ⟩ s1 (Add e1 e2)
      ∎
  where 
    proof1 : (accumulator (s2 (c e1 i))) ≡ s1 e1
    proof1 = proof e1 i
    proof2 : (accumulator (s2 (c e2 (i + 1)))) ≡ s1 e2
    proof2 = proof e2 (i + 1)
proof (Mult e1 e2) i = begin
      accumulator (s2 (c (Mult e1 e2) i))
      ≡⟨ multSemantics e1 e2 i ⟩ accumulator (s2 (c e1 i)) * accumulator (s2 (c e2 (i + 1)))
      ≡⟨ cong (λ x → x * accumulator (s2 (c e2 (i + 1)))) (proof1) ⟩ s1 e1 * accumulator (s2 (c e2 (i + 1)))
      ≡⟨ cong (λ x → s1 e1 * x) (proof2) ⟩ s1 e1 * s1 e2
      ≡⟨ sym (mulEval e1 e2) ⟩ s1 (Mult e1 e2)
      ∎
  where 
    proof1 : (accumulator (s2 (c e1 i))) ≡ s1 e1
    proof1 = proof e1 i
    proof2 : (accumulator (s2 (c e2 (i + 1)))) ≡ s1 e2
    proof2 = proof e2 (i + 1)
