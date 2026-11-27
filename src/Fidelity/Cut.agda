{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0 AND CC-BY-SA-4.0
-- MPL-2.0 (code) and CC-BY-SA-4.0 (prose)
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Ladder E, rungs 5 to 7: the cut.  The zero-loss case of pre-registered
-- statement 2 (stage accounting), tested against E-4.
--
-- E-4 (Pipeline.agda) shows that whole-type audits of the stages do not
-- compose: stage one adds a phantom, stage two collapses it, the whole is
-- faithful.  Here each stage is audited only on what the other stage
-- leaves visible, and the audit becomes exact.
--
--   E-5  forward cut.  The composite is free of collapses exactly when
--        stage one is, and stage two is on the image of stage one.
--   E-6  backward cut.  The composite is covered exactly when stage two
--        is, and stage one is covered up to what stage two tells apart.
--   E-7  E-4 under the cut-relative reading: neither stage has a defect.
--        The whole-type defects of E-4 are still there; the cut-relative
--        audit does not count them, so it does not imply the whole-type
--        audit of either stage (both converses refuted).
--
-- Only the zero-loss case.  Grading a stage in resource-algebra's Loss
-- instance is not defined here (PROOF-LADDERS.adoc, open rung 1).
module Fidelity.Cut where

open import ResourceAlgebra.Prelude
open import Fidelity.Crossing
open import Fidelity.Pipeline

module _ {S T U : Set} (c : Crossing S T) (d : Crossing T U) where

  -- E-5.  Stage two's collapses, read only on the image of stage one.
  ReachCollapse : Set
  ReachCollapse =
    Σ S (λ s → Σ S (λ s' →
      (fwd d (fwd c s) ≡ fwd d (fwd c s')) × (fwd c s ≢ fwd c s')))

  collapse-first : Collapse c → Collapse (c ⨾ d)
  collapse-first (s , s' , e , ne) = s , s' , cong (fwd d) e , ne

  collapse-reach : ReachCollapse → Collapse (c ⨾ d)
  collapse-reach (s , s' , e , ne) = s , s' , e , (λ p → ne (cong (fwd c) p))

  no-collapse-join : ¬ Collapse c → ¬ ReachCollapse → ¬ Collapse (c ⨾ d)
  no-collapse-join nc nr (s , s' , e , ne) =
    nr (s , s' , e , (λ p → nc (s , s' , p , ne)))

  no-collapse-split : ¬ Collapse (c ⨾ d) → (¬ Collapse c) × (¬ ReachCollapse)
  no-collapse-split n =
    (λ x → n (collapse-first x)) , (λ x → n (collapse-reach x))

  -- E-6.  Stage one's additions, read only up to what stage two can tell
  -- apart: every target of stage one is reached up to stage two.
  CoveredUpTo : Set
  CoveredUpTo = ∀ t → Σ S (λ s → fwd d (fwd c s) ≡ fwd d t)

  covered-split : Covered (c ⨾ d) → Covered d × CoveredUpTo
  covered-split cov = end-to-end-last-covered c d cov , (λ t → cov (fwd d t))

  covered-join : Covered d → CoveredUpTo → Covered (c ⨾ d)
  covered-join cd cu u with cd u
  ... | t , e with cu t
  ...   | s , e' = s , trans e' e

----------------------------------------------------------------------
-- E-7, computed.  The cancelling pipeline of E-4 has no cut-relative
-- defect at either stage.
e4-no-reach-collapse : ¬ ReachCollapse blindspot forgetful
e4-no-reach-collapse (tt , tt , e , ne) = ne refl

e4-covered-up-to : CoveredUpTo blindspot forgetful
e4-covered-up-to t = tt , refl

-- So the cut-relative audit is strictly weaker than the whole-type audit
-- of each stage: it passes where the whole-type audit fails.
e4-reach-misses-whole-type-collapse :
  (¬ ReachCollapse blindspot forgetful) × Collapse forgetful
e4-reach-misses-whole-type-collapse =
  e4-no-reach-collapse , stage-two-collapses

e4-up-to-misses-whole-type-addition :
  CoveredUpTo blindspot forgetful × SansFibre blindspot phantom
e4-up-to-misses-whole-type-addition = e4-covered-up-to , stage-one-adds

-- The general converses are false, not merely unproven: each is refuted
-- by the cancelling pipeline.  Their proof attempts are also kept as
-- expected rejections (tests/reject: ReachIsWholeType,
-- CoveredUpToIsCovered).
reach-converse-false :
  (∀ {S T U : Set} (c : Crossing S T) (d : Crossing T U)
       → ¬ ReachCollapse c d → ¬ Collapse d) → ⊥
reach-converse-false claim =
  claim blindspot forgetful e4-no-reach-collapse stage-two-collapses

up-to-converse-false :
  (∀ {S T U : Set} (c : Crossing S T) (d : Crossing T U)
       → CoveredUpTo c d → Covered c) → ⊥
up-to-converse-false claim =
  stage-one-adds (claim blindspot forgetful e4-covered-up-to phantom)
