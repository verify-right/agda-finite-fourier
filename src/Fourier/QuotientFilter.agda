{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.QuotientFilter (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Fin.Base using (Fin)
open import Data.Product.Base using (Σ; _,_)
import Relation.Binary.PropositionalEquality as E
open import Fourier.Characters R
open import Algebra.FiniteSums R
open import Fourier.Pairing R
open import Fourier.Enumeration
open import Fourier.Inversion R

module Quotient {m n} (G : Group m) (Q D : Group n)
  (π : Fin m → Fin n) (s : Fin n → Fin m) (section-law : ∀ a → π (s a) E.≡ a)
  (map-e : π (Group.e G) E.≡ Group.e Q)
  (map-op : ∀ x y → π (Group._∙_ G x y) E.≡ Group._∙_ Q (π x) (π y))
  (B : Bicharacter D Q) where
  module G = Group G
  module Q = Group Q
  open Table D Q B

  Kernel = λ x → π x E.≡ Q.e
  Trivial : Character G → Set
  Trivial c = ∀ x → Kernel x → value c x ≈ 1#
  pull : Character Q → Character G
  value (pull c) x = value c (π x)
  trivial-at-e (pull c) = E.subst (λ z → value c z ≈ 1#) (E.sym map-e) (trivial-at-e c)
  mult (pull c) x y = E.subst (λ z → value c z ≈ _) (E.sym (map-op x y)) (mult c (π x) (π y))
  pull-trivial : ∀ c → Trivial (pull c)
  pull-trivial c x m = E.subst (λ z → value c z ≈ 1#) (E.sym m) (trivial-at-e c)

  module Descend (c : Character G) (triv : Trivial c) where
    constant : ∀ x y → π x E.≡ π y → value c x ≈ value c y
    constant x y eq = trans (sym (*-identityʳ _)) (trans (*-cong refl (sym (triv diff kernel)))
      (trans (sym (mult c x diff)) (E.subst (λ z → value c (x G.∙ diff) ≈ value c z) simplify refl)))
      where
      diff = G.neg x G.∙ y
      simplify = E.trans (E.sym (G.assoc x (G.neg x) y))
        (E.trans (E.cong (G._∙ y) (G.inverseʳ x)) (G.identityˡ y))
      kernel = E.trans (map-op (G.neg x) y) (E.trans (E.cong (π (G.neg x) Q.∙_) (E.sym eq))
        (E.trans (E.sym (map-op (G.neg x) x)) (E.trans (E.cong π (G.inverseˡ x)) map-e)))

    descended : Character Q
    value descended a = value c (s a)
    trivial-at-e descended = triv _ (section-law Q.e)
    mult descended a b = trans (constant _ _ (E.trans (section-law (a Q.∙ b))
      (E.sym (E.trans (map-op (s a) (s b)) (E.cong₂ Q._∙_ (section-law a) (section-law b))))))
      (mult c (s a) (s b))

    factors : ∀ x → value c x ≈ value (pull descended) x
    factors x = constant x (s (π x)) (E.sym (section-law (π x)))

  all-trivial : (∀ d → Σ _ (λ k → ∀ a → value d a ≈ K k a)) →
    ∀ c → Trivial c → Σ _ (λ k → ∀ x → value c x ≈ K k (π x))
  all-trivial complete c triv with complete (Descend.descended c triv)
  ... | k , eq = k , λ x → trans (Descend.factors c triv x) (eq (π x))

  coset-sum : Columns → ∀ a x → sum n (λ k → L (π a) k * K k (π x)) ≈ order n * delta (π a) (π x)
  coset-sum cols a x = OrthogonalPair.orthogonal (left-gram cols) (π a) (π x)

  sum-trivial : Columns → ∀ x → sum n (λ k → K k (π x)) ≈ order n * delta Q.e (π x)
  sum-trivial cols x = trans (sum-cong n _ _ (λ k → sym (trans
    (*-cong (row-e (Group.neg D k)) refl) (*-identityˡ _))))
    (OrthogonalPair.orthogonal (left-gram cols) Q.e (π x))

  average : Columns → ∀ u → u * order n ≈ 1# → ∀ x →
    u * sum n (λ k → K k (π x)) ≈ delta Q.e (π x)
  average cols u unit x = trans (*-cong refl (sum-trivial cols x)) (trans (sym (*-assoc _ _ _))
    (trans (*-cong unit refl) (*-identityˡ _)))

  distinct-pulls : (∀ i j → (∀ q → K i q ≈ K j q) → i E.≡ j) →
    ∀ i j → (∀ x → K i (π x) ≈ K j (π x)) → i E.≡ j
  distinct-pulls unique i j equal = unique i j (λ q →
    E.subst (λ t → K i t ≈ K j t) (section-law q) (equal (s q)))

  scaled-coset : Columns → ∀ c w → c * order n ≈ w → ∀ a x →
    c * sum n (λ k → L (π a) k * K k (π x)) ≈ w * delta (π a) (π x)
  scaled-coset cols c w scaled a x = trans (*-cong refl (coset-sum cols a x))
    (trans (sym (*-assoc _ _ _)) (*-cong scaled refl))

  -- A caller decides whether its residue is a unit and supplies the unit index.
  open import Data.Maybe.Base using (Maybe; just; nothing)
  extended : Fin n → Maybe (Fin m) → Carrier
  extended k nothing = 0#
  extended k (just x) = K k (π x)
  indicator : Maybe (Fin m) → Carrier
  indicator nothing = 0#
  indicator (just x) = delta Q.e (π x)
  average-extended : Columns → ∀ u → u * order n ≈ 1# → ∀ x →
    u * sum n (λ k → extended k x) ≈ indicator x
  average-extended cols u unit nothing = trans (*-cong refl (sum-zero n)) (zeroʳ u)
  average-extended cols u unit (just x) = average cols u unit x
