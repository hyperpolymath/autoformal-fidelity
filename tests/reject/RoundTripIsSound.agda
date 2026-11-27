{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module RoundTripIsSound where
open import ResourceAlgebra.Prelude
open import Fidelity.Crossing
open import Fidelity.Meaning

-- Must fail: a passing round trip does not make the translation mean what
-- the source means.  The swap crossing round-trips and mistranslates
-- everything (Meaning.agda, C-1).
invalid : ∀ {S : Set} (c : Crossing S S) → RoundTrip c
        → FwdSound (λ s → s) (λ s → s) c
invalid c rt s = rt s
