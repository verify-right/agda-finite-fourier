{-# OPTIONS --safe --without-K #-}
open import Agda.Builtin.Nat using (Nat)
module Algebra.ModuloRing (k : Nat) where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (zero; suc; _+_; _-_; _*_; _==_; mod-helper)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as ℕ
import Data.Nat.DivMod as DivMod
open import Data.Product using (_,_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (sym; trans; cong; cong₂)
open import Algebra.Bundles using (CommutativeRing)

-- Natural-number representatives; equality compares residues modulo k + 2.
modulus : Nat
modulus = 2 + k

normalize : Nat → Nat
normalize x = mod-helper 0 (1 + k) x (1 + k)

negative : Nat → Nat
negative x = modulus - normalize x

private
  p : Nat
  p = modulus

infix 4 _≈_
_≈_ : Nat → Nat → Set
x ≈ y = normalize x ≡ normalize y

-- The implementation's normalize is definitionally stdlib's remainder.
-- The two distributivity lemmas below are imported, not reproved.
remainder-idem : (x : Nat) → normalize (normalize x) ≡ normalize x
remainder-idem x = DivMod.m%n%n≡m%n x p

add-remainder : (x y : Nat) → normalize (x + y) ≡ normalize (normalize x + normalize y)
add-remainder x y = DivMod.%-distribˡ-+ x y p

mul-remainder : (x y : Nat) → normalize (x * y) ≡ normalize (normalize x * normalize y)
mul-remainder x y = DivMod.%-distribˡ-* x y p

+-cong : {x x' y y' : Nat} → x ≈ x' → y ≈ y' → (x + y) ≈ (x' + y')
+-cong {x} {x'} {y} {y'} hx hy =
  trans (add-remainder x y)
    (trans (cong₂ (λ a b → normalize (a + b)) hx hy) (sym (add-remainder x' y')))

*-cong : {x x' y y' : Nat} → x ≈ x' → y ≈ y' → (x * y) ≈ (x' * y')
*-cong {x} {x'} {y} {y'} hx hy =
  trans (mul-remainder x y)
    (trans (cong₂ (λ a b → normalize (a * b)) hx hy) (sym (mul-remainder x' y')))

-- Reducing only the left operand does not change the sum's residue.
reduce-add-left : (x y : Nat) → normalize (x + y) ≡ normalize (normalize x + y)
reduce-add-left x y = trans (add-remainder x y)
  (sym (trans (add-remainder (normalize x) y)
    (cong (λ a → normalize (a + normalize y)) (remainder-idem x))))

inverseʳ : (x : Nat) → (x + negative x) ≈ 0
inverseʳ x = trans (reduce-add-left x (negative x))
  (trans (cong (normalize) (ℕ.m+[n∸m]≡n bound)) (DivMod.n%n≡0 p))
  where
  bound : normalize x ≤ p
  bound = ℕ.<⇒≤ (DivMod.m%n<n x p)

inverseˡ : (x : Nat) → (negative x + x) ≈ 0
inverseˡ x = trans (cong (normalize) (ℕ.+-comm (negative x) x)) (inverseʳ x)

neg-cong : {x y : Nat} → x ≈ y → negative x ≈ negative y
neg-cong h = cong (λ a → normalize (p - a)) h

equivalence : IsEquivalence _≈_
equivalence = record { refl = refl ; sym = sym ; trans = trans }

open import Algebra.Structures _≈_ using (IsMagma; IsSemigroup; IsMonoid; IsGroup; IsAbelianGroup; IsRing; IsCommutativeRing)

+-magma : IsMagma _+_
+-magma = record { isEquivalence = equivalence ; ∙-cong = λ {x} {y} {u} {v} hx hy → +-cong {x} {y} {u} {v} hx hy }

+-semigroup : IsSemigroup _+_
+-semigroup = record { isMagma = +-magma ; assoc = λ x y z → cong (normalize) (ℕ.+-assoc x y z) }

+-monoid : IsMonoid _+_ 0
+-monoid = record
  { isSemigroup = +-semigroup
  ; identity = (λ x → cong (normalize) (ℕ.+-identityˡ x)) , (λ x → cong (normalize) (ℕ.+-identityʳ x))
  }

+-group : IsGroup _+_ 0 (negative)
+-group = record { isMonoid = +-monoid ; inverse = inverseˡ , inverseʳ ; ⁻¹-cong = λ {x} {y} h → neg-cong {x} {y} h }

+-abelian : IsAbelianGroup _+_ 0 (negative)
+-abelian = record { isGroup = +-group ; comm = λ x y → cong (normalize) (ℕ.+-comm x y) }

*-magma : IsMagma _*_
*-magma = record { isEquivalence = equivalence ; ∙-cong = λ {x} {y} {u} {v} hx hy → *-cong {x} {y} {u} {v} hx hy }

*-semigroup : IsSemigroup _*_
*-semigroup = record { isMagma = *-magma ; assoc = λ x y z → cong (normalize) (ℕ.*-assoc x y z) }

*-monoid : IsMonoid _*_ 1
*-monoid = record
  { isSemigroup = *-semigroup
  ; identity = (λ x → cong (normalize) (ℕ.*-identityˡ x)) , (λ x → cong (normalize) (ℕ.*-identityʳ x))
  }

isRing : IsRing _+_ _*_ (negative) 0 1
isRing = record
  { +-isAbelianGroup = +-abelian
  ; *-cong = λ {x} {y} {u} {v} hx hy → *-cong {x} {y} {u} {v} hx hy
  ; *-assoc = λ x y z → cong (normalize) (ℕ.*-assoc x y z)
  ; *-identity = (λ x → cong (normalize) (ℕ.*-identityˡ x)) , (λ x → cong (normalize) (ℕ.*-identityʳ x))
  ; distrib = (λ x y z → cong (normalize) (ℕ.*-distribˡ-+ x y z)) ,
              (λ x y z → cong (normalize) (ℕ.*-distribʳ-+ x y z))
  }

isCommutativeRing : IsCommutativeRing _+_ _*_ (negative) 0 1
isCommutativeRing = record { isRing = isRing ; *-comm = λ x y → cong (normalize) (ℕ.*-comm x y) }

commutativeRing : CommutativeRing _ _
commutativeRing = record
  { Carrier = Nat
  ; _≈_ = _≈_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = negative
  ; 0# = 0
  ; 1# = 1
  ; isCommutativeRing = isCommutativeRing
  }

-- Equivalent representatives may differ by an entire modulus.
modulus-shift : (x : Nat) → x ≈ (p + x)
modulus-shift x = sym (trans (cong (normalize) (ℕ.+-comm p x))
  (DivMod.[m+n]%n≡m%n x p))
