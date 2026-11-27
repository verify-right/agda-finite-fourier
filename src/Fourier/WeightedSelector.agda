{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.WeightedSelector (R : CommutativeRing 0ℓ 0ℓ) where
open CommutativeRing R
open import Data.Fin.Base using (Fin)
open import Fourier.Enumeration
open import Fourier.Characters R
open import Algebra.FiniteSums R
open import Algebra.WeightedSums R
import Algebra.Properties.CommutativeSemigroup *-commutativeSemigroup as M
import Fourier.Filters R as Filters
import Relation.Binary.PropositionalEquality as E

module Bias {n m} (G : Group n) (h : Fin m → Fin n) (b s : Carrier) where
  weight = λ x → b + s * count h x
  coeff : Character G → Carrier
  coeff c = moment weight (value c)

  split : ∀ c → coeff c ≈ b * sum n (value c) + s * sum m (λ j → value c (h j))
  split c = trans (two-level b s (count h) (value c))
    (+-cong refl (*-cong refl (integrate-count h (value c))))

  principal : ∀ c → (∀ x → value c x ≈ 1#) → coeff c ≈ b * order n + s * order m
  principal c one = trans (split c) (+-cong (*-cong refl (sum-cong n _ _ one))
    (*-cong refl (sum-cong m _ _ (λ j → one (h j)))))

  module Sub (H : Group m) (he : h (Group.e H) E.≡ Group.e G)
    (hm : ∀ x y → h (Group._∙_ H x y) E.≡ Group._∙_ G (h x) (h y))
    (c : Character G) (sep : Separates (value c)) where
    module C = Filters.Coset G H h he hm c (Group.e G)
    reduced : coeff c ≈ s * sum m (value C.restrict)
    reduced = trans (split c) (trans (+-cong
      (trans (*-cong refl (character-zero G c sep)) (zeroʳ b)) refl) (+-identityˡ _))
    retained : (∀ j → value c (h j) ≈ 1#) → coeff c ≈ s * order m
    retained one = trans reduced (*-cong refl (sum-cong m _ _ one))
    discarded : Separates (value C.restrict) → coeff c ≈ 0#
    discarded z = trans reduced (trans (*-cong refl (character-zero H C.restrict z)) (zeroʳ s))

  -- Move each character's translate outside the average of an arbitrary expansion.
  translate : ∀ {k} (cs : Fin k → Character G) (a : Fin k → Carrier) (f : Fin n → Carrier) →
    (∀ x → f x ≈ sum k (λ j → a j * value (cs j) x)) → ∀ u →
    moment weight (λ x → f (Group._∙_ G u x)) ≈
    sum k (λ j → (a j * value (cs j) u) * coeff (cs j))
  translate {k} cs a f expansion u = trans (sum-cong n _ _ λ x →
    trans (*-cong refl (expansion (Group._∙_ G u x))) (sym (sum-mulˡ k (weight x) _)))
    (trans (sum-swap n k _) (sum-cong k _ _ λ j → trans
      (sum-cong n _ _ λ x → trans (*-cong refl (*-cong refl (mult (cs j) u x)))
        (trans (*-cong refl (sym (*-assoc _ _ _))) (M.x∙yz≈y∙xz _ _ _)))
      (sum-mulˡ n _ _)))

  -- Give the statement for every signal by building its expansion from a
  -- one-sided Gram identity. No law on frequency indices is required.
  open import Fourier.Inversion R
  module Analysis (cs : Fin n → Character G) (analysis : Fin n → Fin n → Carrier)
    (gram-law : OrthogonalPair n (order n) analysis (λ x j → value (cs j) x))
    (v : Carrier) (length-unit : v * order n ≈ 1#) where

    fourier : (Fin n → Carrier) → Fin n → Carrier
    fourier f j = v * transform analysis f j

    expand : ∀ f x → f x ≈ sum n (λ j → fourier f j * value (cs j) x)
    expand f x = trans (sym (normalized-inversion gram-law length-unit f x))
      (trans (sym (sum-mulˡ n v _)) (sum-cong n _ _ λ j →
        trans (*-cong refl (*-comm _ _)) (sym (*-assoc _ _ _))))

    -- mu is the inverse total mass for a probability-normalized selector;
    -- the superposition formula itself permits any scale.
    weighted-selector : ∀ mu f u →
      mu * moment weight (λ x → f (Group._∙_ G u x)) ≈
      sum n (λ j → (fourier f j * value (cs j) u) * (mu * coeff (cs j)))
    weighted-selector mu f u = trans (*-cong refl (translate cs (fourier f) f (expand f) u))
      (trans (sym (sum-mulˡ n mu _)) (sum-cong n _ _ λ j → M.x∙yz≈y∙xz _ _ _))

-- Clear the denominator of the retained multiplier without dividing by |H|.
retained-ratio : ∀ b s o N h mu → N ≈ o * h →
  mu * (b * N + s * h) ≈ 1# → (mu * (s * h)) * (b * o + s) ≈ s
retained-ratio b s o N h mu card unit =
  trans (*-cong (M.x∙yz≈y∙xz mu s h) refl)
  (trans (*-assoc s (mu * h) _) (trans (*-cong refl inner) (*-identityʳ s)))
  where
  inner : (mu * h) * (b * o + s) ≈ 1#
  inner = trans (*-assoc mu h _) (trans (*-cong refl
    (trans (*-comm h _) (trans (distribʳ h _ _)
      (+-cong (trans (*-assoc b o h) (*-cong refl (sym card))) refl)))) unit)

unit-excess-ratio : ∀ b o N h mu → N ≈ o * h →
  mu * (b * N + 1# * h) ≈ 1# → (mu * (1# * h)) * (b * o + 1#) ≈ 1#
unit-excess-ratio b = retained-ratio b 1#
