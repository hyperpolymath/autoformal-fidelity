{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Ladder A, rungs 5 to 7: additions need the target standpoint
-- (pre-registered statement 1) and what agreement between provers is
-- worth (pre-registered statement 5).
--
-- Standpoints in Crossing.agda fixes the target reading to fwd ∘ readₛ,
-- which cannot add.  Here the two readings of a world are independent.
--
--   A-5  an addition pair is two worlds the source reads alike and the
--        target reads apart.  It is invisible from the source standpoint
--        by definition, and it refutes "the target sees no more".
--   A-6  the target sees no more than the source exactly when the target
--        reading factors through the source reading (given that every
--        source value is read from some world).
--   A-7  two provers that each pass the round trip always induce the same
--        partition of the worlds.  Agreement of partitions is therefore
--        implied by the structural check and adds no evidence about
--        meaning (Meaning.agda, C-1, gives two that agree and differ).
module Fidelity.Additions where

open import ResourceAlgebra.Prelude
open import Fidelity.Crossing

module TwoReadings {W S T : Set} (readₛ : W → S) (readₜ : W → T) where

  _~ₛ_ _~ₜ_ : W → W → Set
  w ~ₛ w' = readₛ w ≡ readₛ w'
  w ~ₜ w' = readₜ w ≡ readₜ w'

  NoAddition : Set                   -- the target sees no more
  NoAddition = ∀ w w' → w ~ₛ w' → w ~ₜ w'

  NoLoss : Set                       -- the target sees no less
  NoLoss = ∀ w w' → w ~ₜ w' → w ~ₛ w'

  AdditionPair : Set
  AdditionPair = Σ W (λ w → Σ W (λ w' → (w ~ₛ w') × (¬ (w ~ₜ w'))))

  LossPair : Set
  LossPair = Σ W (λ w → Σ W (λ w' → (w ~ₜ w') × (¬ (w ~ₛ w'))))

  -- A-5
  addition-invisible-from-source :
    (p : AdditionPair) → fst p ~ₛ fst (snd p)
  addition-invisible-from-source (_ , _ , e , _) = e

  addition-visible-from-target :
    (p : AdditionPair) → ¬ (fst p ~ₜ fst (snd p))
  addition-visible-from-target (_ , _ , _ , ne) = ne

  addition-pair-refutes : AdditionPair → ¬ NoAddition
  addition-pair-refutes (w , w' , e , ne) na = ne (na w w' e)

  loss-pair-refutes : LossPair → ¬ NoLoss
  loss-pair-refutes (w , w' , e , ne) nl = ne (nl w w' e)

  -- A-6
  Factors : Set
  Factors = Σ (S → T) (λ f → ∀ w → readₜ w ≡ f (readₛ w))

  factors-no-addition : Factors → NoAddition
  factors-no-addition (f , p) w w' e =
    trans (p w) (trans (cong f e) (sym (p w')))

  no-addition-factors : (sec : S → W) → (∀ s → readₛ (sec s) ≡ s)
                      → NoAddition → Factors
  no-addition-factors sec secp na =
    (λ s → readₜ (sec s)) ,
    (λ w → na w (sec (readₛ w)) (sym (secp (readₛ w))))

----------------------------------------------------------------------
-- A-5, computed: the worlds are the two artefact elements of the
-- blindspot; the source reads both as the one source element.
open TwoReadings {W = Two} {S = ⊤} {T = Two} (λ _ → tt) (λ w → w)
  using () renaming (AdditionPair to BlindspotAdditionPair)

blindspot-addition-pair : BlindspotAdditionPair
blindspot-addition-pair = real , phantom , refl , (λ ())

----------------------------------------------------------------------
-- A-7
module TwoProvers {W S T₁ T₂ : Set} (readₛ : W → S)
                  (c₁ : Crossing S T₁) (c₂ : Crossing S T₂) where

  private
    module P₁ = Standpoints c₁ readₛ
    module P₂ = Standpoints c₂ readₛ

  agree-₁₂ : RoundTrip c₁ → ∀ w w' → w P₁.~ₜ w' → w P₂.~ₜ w'
  agree-₁₂ rt w w' e =
    P₂.source-sees-target w w' (P₁.target-sees-source rt w w' e)

  agree-₂₁ : RoundTrip c₂ → ∀ w w' → w P₂.~ₜ w' → w P₁.~ₜ w'
  agree-₂₁ rt w w' e =
    P₁.source-sees-target w w' (P₂.target-sees-source rt w w' e)
