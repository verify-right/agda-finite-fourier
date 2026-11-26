{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing; AbelianGroup)
open import Level using (0ℓ)
module Fourier.Characters (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as E using (_≢_)
open import Relation.Nullary.Decidable using (yes; no)
open import Algebra.FiniteSums R
open import Fourier.Reindex R
open import Fourier.Enumeration
import Algebra.Properties.Ring ring as RP
import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as M

record Character {n : ℕ} (G : Group n) : Set where
  field
    value : Fin n → Carrier
    trivial-at-e : value (Group.e G) ≈ 1#
    mult : ∀ t i → value (Group._∙_ G t i) ≈ value t * value i
open Character public

Regular : Carrier → Set
Regular d = ∀ s → d * s ≈ 0# → s ≈ 0#

unit-regular : ∀ d u → u * d ≈ 1# → Regular d
unit-regular d u unit s h = trans (sym (*-identityˡ s))
  (trans (*-cong (sym unit) refl) (trans (*-assoc u d s)
    (trans (*-cong refl h) (zeroʳ u))))

-- Several differences can have trivial common annihilator even when none is regular.
Separates : ∀ {n} → (Fin n → Carrier) → Set
Separates q = ∀ s → (∀ t → (q t + (- 1#)) * s ≈ 0#) → s ≈ 0#

witness : ∀ {n} (q : Fin n → Carrier) t → Regular (q t + (- 1#)) → Separates q
witness q t reg s h = reg s (h t)

annihilates-sum : ∀ {n} (G : Group n) (c : Character G) t →
  (value c t + (- 1#)) * sum n (value c) ≈ 0#
annihilates-sum {n} G c t = trans (distribʳ s (q t) (- 1#))
  (trans (+-cong fixed (RP.-1*x≈-x s)) (-‿inverseʳ s))
  where
  q = value c
  s = sum n q
  fixed = trans (sym (sum-mulˡ n (q t) q))
    (trans (sum-cong n _ _ (λ i → sym (mult c t i))) (translate-sum G t q))

character-zero : ∀ {n} (G : Group n) (c : Character G) →
  Separates (value c) → sum n (value c) ≈ 0#
character-zero G c sep = sep _ (annihilates-sum G c)

product : ∀ {n} {G : Group n} → Character G → Character G → Character G
value (product a b) i = value a i * value b i
trivial-at-e (product a b) = trans (*-cong (trivial-at-e a) (trivial-at-e b)) (*-identityˡ 1#)
mult (product a b) t i = trans (*-cong (mult a t i) (mult b t i))
  (M.medial (value a t) (value a i) (value b t) (value b i))

opposite : ∀ {n} {G : Group n} → Character G → Character G
opposite {G = G} c = record
  { value = λ x → value c (Group.neg G x)
  ; trivial-at-e = E.subst (λ z → value c z ≈ 1#) (E.sym P.ε⁻¹≈ε) (trivial-at-e c)
  ; mult = λ x y → E.subst (λ z → value c z ≈ _)
      (P.⁻¹-∙-comm x y) (mult c (Group.neg G x) (Group.neg G y)) }
  where
  A : AbelianGroup 0ℓ 0ℓ
  A = record { isAbelianGroup = Group.laws G }
  import Algebra.Properties.AbelianGroup A as P

reciprocal : ∀ {n} {G : Group n} (c : Character G) t →
  value (opposite c) t * value c t ≈ 1#
reciprocal {G = G} c t = trans (sym (mult c (Group.neg G t) t))
  (E.subst (λ z → value c z ≈ 1#) (E.sym (Group.inverseˡ G t)) (trivial-at-e c))

order : ℕ → Carrier
order n = sum n (λ _ → 1#)

-- Indices of characters need no group structure for this one direction.
gram : ∀ {m n} (G : Group m) (U V : Fin n → Character G) →
  (∀ x k → value (U x) k * value (V x) k ≈ 1#) →
  (∀ x y → x ≢ y → Separates (value (product (U x) (V y)))) →
  ∀ x y → sum m (value (product (U x) (V y))) ≈ order m * delta x y
gram {m} G U V diag sep x y with x ≟ y
... | yes E.refl = trans (sum-cong m _ _ (diag x))
  (sym (trans (*-cong refl (diagonal x)) (*-identityʳ (order m))))
... | no neq = trans (character-zero G (product (U x) (V y)) (sep x y neq))
  (sym (trans (*-cong refl (off x y neq)) (zeroʳ (order m))))
