{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module CommittedReadingIsComplete where
open import ResourceAlgebra.Prelude
open import Fidelity.Crossing
open import Fidelity.Simultaneous

-- Must fail: a joint solution does not complete whichever admissible
-- reading was committed to first.  The solution's term means the
-- solution's reading, not the committed one (Simultaneous.agda, D-2).
invalid : ∀ {S T M : Set} (semS : S → M) (semT : T → M)
          (A : S → Set) (W : T → Set)
        → Solution semS semT A W → ∀ s → A s → Forward semS semT A W s
invalid semS semT A W (s' , t , (a' , w) , m) s a = t , w , m
