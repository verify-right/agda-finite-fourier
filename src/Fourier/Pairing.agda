{-# OPTIONS --safe --without-K #-}
open import Algebra.Bundles using (CommutativeRing)
open import Level using (0ℓ)
module Fourier.Pairing (R : CommutativeRing 0ℓ 0ℓ) where

open CommutativeRing R
open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Fourier.Enumeration
open import Fourier.Characters R
open import Fourier.Inversion R
import Fourier.Convolution R as Conv

record Bicharacter {m n : ℕ} (H : Group m) (G : Group n) : Set where
  field
    K : Fin m → Fin n → Carrier
    row-e : ∀ k → K k (Group.e G) ≈ 1#
    row-mul : ∀ k x y → K k (Group._∙_ G x y) ≈ K k x * K k y
    col-e : ∀ x → K (Group.e H) x ≈ 1#
    col-mul : ∀ x k l → K (Group._∙_ H k l) x ≈ K k x * K l x

  row : Fin m → Character G
  row k = record { value = K k ; trivial-at-e = row-e k ; mult = row-mul k }

  col : Fin n → Character H
  col x = record { value = λ k → K k x ; trivial-at-e = col-e x ; mult = col-mul x }

  L : Fin n → Fin m → Carrier
  L x k = K (Group.neg H k) x

module Table {n} (H G : Group n) (B : Bicharacter H G) where
  open Bicharacter B public

  Columns Rows : Set
  Columns = ∀ x y → x ≢ y → Separates (λ k → L x k * K k y)
  Rows = ∀ k l → k ≢ l → Separates (λ x → K k x * L x l)

  left-gram : Columns → OrthogonalPair n (order n) K L
  OrthogonalPair.orthogonal (left-gram sep) = gram H (λ x → opposite (col x)) col
    (λ x t → reciprocal (col x) t) sep

  right-gram : Rows → OrthogonalPair n (order n) L K
  OrthogonalPair.orthogonal (right-gram sep) = gram G row (λ k → row (Group.neg H k))
    (λ k x → trans (*-comm (K k x) (L x k)) (reciprocal (col x) k)) sep

  diagonalizes = Conv.convolution-hom (Group._∙_ G) K row-mul
