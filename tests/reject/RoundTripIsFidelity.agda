{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module RoundTripIsFidelity where
open import ResourceAlgebra.Prelude
open import Fidelity.Crossing

-- Must fail: a passing round trip does not cover the artefact.  Claiming
-- it does is the translator's fallacy; the phantom has no fibre.
invalid : ∀ {S T : Set} (c : Crossing S T) → RoundTrip c → Covered c
invalid c rt y = back c y , refl
