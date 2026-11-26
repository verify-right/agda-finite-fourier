{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.Filters (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality as E using (_≡_; _≢_)
open import Algebra.FiniteSums R
open import Fourier.Reindex R
open import Fourier.Characters R
open import Fourier.Enumeration
open import Fourier.Pairing R
open import Fourier.Inversion R
import Fourier.QuotientFilter R as Q

open import Fourier.Duality R using (Linear; matrix-linear)
import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as M

module Filter {n} (H G : Group n) (B : Bicharacter H G) where
  open Table H G B

  -- c is the outside normalization; w is its value times the FULL dual size.
  module Id = Q.Quotient G G H
    (λ x → x) (λ x → x)
    (λ _ → E.refl) E.refl (λ _ _ → E.refl) B

  point-filter : Columns → ∀ c w → c * order n ≈ w → ∀ x y →
    c * sum n (λ k → L x k * K k y) ≈ w * delta x y
  point-filter = Id.scaled-coset

  module OnSet {m} (embed : Fin m → Fin n) where
    spectrum : Fin n → Carrier
    spectrum k = sum m (λ j → K k (embed j))
    -- Multiplicities are allowed here.
    count : Fin n → Carrier
    count x = sum m (λ j → delta x (embed j))

    weighted-count : Columns → ∀ c w → c * order n ≈ w → ∀ x →
      c * transform L spectrum x ≈ w * count x
    weighted-count cols c w factor x = trans (*-cong refl (sum-cong n _ _ (λ k →
      sym (sum-mulˡ m (L x k) (λ j → K k (embed j))))))
      (trans (*-cong refl (sum-swap n m (λ k j → L x k * K k (embed j))))
      (trans (sym (sum-mulˡ m c (λ j → sum n (λ k → L x k * K k (embed j)))))
      (trans (sum-cong m _ _ (λ j → point-filter cols c w factor x (embed j)))
        (sum-mulˡ m w _))))

    -- In the finite character comparison, v is the inverse inertia size,
    -- c is the inverse half-group size, and w = 2.
    average-filter : Columns → ∀ c w v → c * order n ≈ w → ∀ x →
      c * transform L (λ k → v * spectrum k) x ≈ (v * w) * count x
    average-filter cols c w v factor x =
      trans (*-cong refl (Linear.scales (matrix-linear L) v spectrum x))
      (trans (M.x∙yz≈y∙xz c v (transform L spectrum x))
      (trans (*-cong refl (weighted-count cols c w factor x)) (sym (*-assoc v w (count x)))))

    filter-count : Columns → (u : Carrier) → u * order n ≈ 1# → ∀ x →
      u * transform L spectrum x ≈ count x
    filter-count cols u unit x = trans (weighted-count cols u 1# unit x) (*-identityˡ (count x))

    absent : Columns → ∀ u → u * order n ≈ 1# → ∀ x →
      (∀ j → x ≢ embed j) → u * transform L spectrum x ≈ 0#
    absent cols u unit x miss = trans (filter-count cols u unit x)
      (trans (sum-cong m _ _ (λ j → off x (embed j) (miss j))) (sum-zero m))

    present : Columns → ∀ u → u * order n ≈ 1# →
      (∀ i j → embed i ≡ embed j → i ≡ j) → ∀ i →
      u * transform L spectrum (embed i) ≈ 1#
    present cols u unit inj i = trans (filter-count cols u unit (embed i))
      (trans (sum-cong m _ _ term) (select m i (λ _ → 1#)))
      where
      term : ∀ j → delta (embed i) (embed j) ≈ delta i j * 1#
      term j with i ≟ j
      ... | yes E.refl = trans (diagonal (embed i))
        (trans (sym (diagonal i)) (sym (*-identityʳ _)))
      ... | no neq = trans (off _ _ (λ eq → neq (inj i j eq)))
        (trans (sym (off i j neq)) (sym (*-identityʳ _)))

-- The image of a homomorphism enumerates a subgroup. Injectivity is needed
-- only to interpret its enumeration as counting each member once.
module Coset {n m} (G : Group n) (S : Group m) (h : Fin m → Fin n)
  (h-e : h (Group.e S) ≡ Group.e G)
  (h-mul : ∀ a b → h (Group._∙_ S a b) ≡ Group._∙_ G (h a) (h b))
  (χ : Character G) (t : Fin n) where
  restrict : Character S
  value restrict a = value χ (h a)
  trivial-at-e restrict = E.subst (λ x → value χ x ≈ 1#) (E.sym h-e) (trivial-at-e χ)
  mult restrict a b = E.subst (λ x → value χ x ≈ _) (E.sym (h-mul a b)) (mult χ (h a) (h b))

  total = sum m (λ a → value χ (Group._∙_ G t (h a)))
  factors : total ≈ value χ t * sum m (value restrict)
  factors = trans (sum-cong m _ _ (λ a → mult χ t (h a))) (sum-mulˡ m _ _)

  vanishes : Separates (value restrict) → total ≈ 0#
  vanishes sep = trans factors (trans (*-cong refl (character-zero S restrict sep)) (zeroʳ _))

  survives : (∀ a → value restrict a ≈ 1#) → total ≈ value χ t * order m
  survives trivial = trans factors (*-cong refl (sum-cong m _ _ trivial))
