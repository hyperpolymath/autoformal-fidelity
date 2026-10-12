{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Fidelity of a crossing (source document → formal artefact), in fibre
-- terms.  Pre-registered 2026-10-12 as an application of the type family
-- to the autoformalisation problem; see docs/pre-registration.adoc.
--
--   round-trip (back ∘ fwd ≡ id)  detects COLLAPSES   (Theorem 1)
--   round-trip is BLIND to ADDITIONS                  (Theorem 2, computed)
--   coverage (every target element has a fibre) is the other half
--   both together make the crossing a bijection       (Theorem 3)
--   fidelity is mutual access between the two standpoints (Theorem 4)
module Fidelity.Crossing where

open import ResourceAlgebra.Prelude

infixr 2 _×_
_×_ : Set → Set → Set
P × Q = Σ P (λ _ → Q)

record Crossing (S T : Set) : Set where
  field
    fwd  : S → T      -- the translation
    back : T → S      -- the back-translation
open Crossing public

module _ {S T : Set} (c : Crossing S T) where

  RoundTrip : Set
  RoundTrip = ∀ s → back c (fwd c s) ≡ s

  -- The fibre over a target element: what in the source produced it.
  Fibre : T → Set
  Fibre y = Σ S (λ s → fwd c s ≡ y)

  -- "Sans fibre": present in the artefact, produced by nothing.
  SansFibre : T → Set
  SansFibre y = ¬ Fibre y

  Covered : Set
  Covered = ∀ y → Fibre y

  Collapse : Set
  Collapse = Σ S (λ s → Σ S (λ s' → (fwd c s ≡ fwd c s') × (s ≢ s')))

  -- Theorem 1: a passing round trip rules out collapses (fwd is injective).
  roundtrip-injective : RoundTrip → ∀ s s' → fwd c s ≡ fwd c s' → s ≡ s'
  roundtrip-injective rt s s' e = trans (sym (rt s)) (trans (cong (back c) e) (rt s'))

  roundtrip-no-collapse : RoundTrip → ¬ Collapse
  roundtrip-no-collapse rt (s , s' , e , ne) = ne (roundtrip-injective rt s s' e)

  -- Theorem 3: round trip plus coverage is a bijection (back is a two-sided
  -- inverse), i.e. the crossing is faithful in both directions.
  Faithful : Set
  Faithful = RoundTrip × Covered

  faithful-back : Faithful → ∀ y → fwd c (back c y) ≡ y
  faithful-back (rt , cov) y with cov y
  ... | s , e = trans (cong (fwd c) (trans (cong (back c) (sym e)) (rt s))) e

----------------------------------------------------------------------
-- Theorem 2, computed: round trip passes while the artefact contains an
-- element with no fibre.  One source element; two target elements, one of
-- them a phantom.  The back-translation never looks at the phantom, so the
-- translator's test cannot see it.
data Two : Set where
  real phantom : Two

blindspot : Crossing ⊤ Two
blindspot = record { fwd = λ _ → real ; back = λ _ → tt }

blindspot-roundtrips : RoundTrip blindspot
blindspot-roundtrips tt = refl

blindspot-adds : SansFibre blindspot phantom
blindspot-adds (tt , ())

----------------------------------------------------------------------
-- Theorem 4: the two standpoints.  Worlds carry a source reading; the
-- target standpoint reads the translation of it.  "q sees at least what p
-- sees" is the access preorder of choreographic-types' Transport.
module Standpoints {W S T : Set} (c : Crossing S T) (readₛ : W → S) where

  readₜ : W → T
  readₜ w = fwd c (readₛ w)

  _~ₛ_ _~ₜ_ : W → W → Set
  w ~ₛ w' = readₛ w ≡ readₛ w'
  w ~ₜ w' = readₜ w ≡ readₜ w'

  -- The source side always sees at least what the target side sees:
  -- translation can only conflate.
  source-sees-target : ∀ w w' → w ~ₛ w' → w ~ₜ w'
  source-sees-target w w' e = cong (fwd c) e

  -- The target side sees at least what the source side sees exactly when
  -- the round trip passes: fidelity as mutual access.
  target-sees-source : RoundTrip c → ∀ w w' → w ~ₜ w' → w ~ₛ w'
  target-sees-source rt w w' e = roundtrip-injective c rt (readₛ w) (readₛ w') e
