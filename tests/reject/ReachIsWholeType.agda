{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0 AND CC-BY-SA-4.0
-- MPL-2.0 (code) and CC-BY-SA-4.0 (prose)
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module ReachIsWholeType where
open import ResourceAlgebra.Prelude
open import Fidelity.Crossing
open import Fidelity.Pipeline
open import Fidelity.Cut

-- Must fail: no collapse of stage two on the image of stage one says
-- nothing about stage two on the rest of its source.  The cancelling
-- pipeline has no reach collapse while stage two collapses (Cut.agda,
-- E-7).
invalid : ∀ {S T U : Set} (c : Crossing S T) (d : Crossing T U)
        → ¬ ReachCollapse c d → ¬ Collapse d
invalid c d nr cd = nr cd
