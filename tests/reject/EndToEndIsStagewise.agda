{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module EndToEndIsStagewise where
open import ResourceAlgebra.Prelude
open import Fidelity.Crossing
open import Fidelity.Pipeline

-- Must fail: end-to-end coverage says nothing about the first stage.  A
-- phantom added at stage one can be collapsed away at stage two
-- (Pipeline.agda, E-4).
invalid : ∀ {S T U : Set} (c : Crossing S T) (d : Crossing T U)
        → Covered (c ⨾ d) → Covered c
invalid c d cov y = cov y
