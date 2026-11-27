{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0 AND CC-BY-SA-4.0
-- MPL-2.0 (code) and CC-BY-SA-4.0 (prose)
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module CoveredUpToIsCovered where
open import ResourceAlgebra.Prelude
open import Fidelity.Crossing
open import Fidelity.Pipeline
open import Fidelity.Cut

-- Must fail: stage one covered up to what stage two tells apart is not
-- stage one covered.  The cancelling pipeline is covered up to stage two
-- while stage one adds a phantom (Cut.agda, E-7).
invalid : ∀ {S T U : Set} (c : Crossing S T) (d : Crossing T U)
        → CoveredUpTo c d → Covered c
invalid c d cu y = cu y
