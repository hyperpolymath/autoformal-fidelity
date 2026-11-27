{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Ladder E: stages.  Crossings compose; what an end-to-end check says
-- about the stages is limited, and the limit is exact.
--
--   E-1  round trip composes; coverage composes.
--   E-2  an end-to-end round trip certifies only the FIRST stage free of
--        collapses.
--   E-3  end-to-end coverage certifies only the LAST stage free of
--        additions.
--   E-4  cancellation, computed: a pipeline that is faithful end to end
--        while its first stage adds a phantom and its second stage
--        collapses it away.  Counts of defects are not additive.
module Fidelity.Pipeline where

open import ResourceAlgebra.Prelude
open import Fidelity.Crossing

infixr 9 _⨾_
_⨾_ : {S T U : Set} → Crossing S T → Crossing T U → Crossing S U
c ⨾ d = record { fwd  = λ s → fwd d (fwd c s)
               ; back = λ u → back c (back d u) }

module _ {S T U : Set} (c : Crossing S T) (d : Crossing T U) where

  -- E-1
  roundtrip-⨾ : RoundTrip c → RoundTrip d → RoundTrip (c ⨾ d)
  roundtrip-⨾ rc rd s = trans (cong (back c) (rd (fwd c s))) (rc s)

  covered-⨾ : Covered c → Covered d → Covered (c ⨾ d)
  covered-⨾ cc cd u with cd u
  ... | t , e with cc t
  ...   | s , e' = s , trans (cong (fwd d) e') e

  -- E-2
  end-to-end-first-injective :
    RoundTrip (c ⨾ d) → ∀ s s' → fwd c s ≡ fwd c s' → s ≡ s'
  end-to-end-first-injective rt s s' e =
    roundtrip-injective (c ⨾ d) rt s s' (cong (fwd d) e)

  end-to-end-first-no-collapse : RoundTrip (c ⨾ d) → ¬ Collapse c
  end-to-end-first-no-collapse rt (s , s' , e , ne) =
    ne (end-to-end-first-injective rt s s' e)

  -- E-3
  end-to-end-last-covered : Covered (c ⨾ d) → Covered d
  end-to-end-last-covered cov u with cov u
  ... | s , e = fwd c s , e

----------------------------------------------------------------------
-- E-4, computed.  Stage one is the blindspot crossing of Crossing.agda;
-- stage two forgets which of the two it was given.
forgetful : Crossing Two ⊤
forgetful = record { fwd = λ _ → tt ; back = λ _ → real }

cancelling : Crossing ⊤ ⊤
cancelling = blindspot ⨾ forgetful

cancelling-faithful : Faithful cancelling
cancelling-faithful = (λ { tt → refl }) , (λ { tt → tt , refl })

stage-one-adds : SansFibre blindspot phantom
stage-one-adds = blindspot-adds

stage-two-collapses : Collapse forgetful
stage-two-collapses = real , phantom , refl , (λ ())

-- So the converses of E-2 and E-3 for the other stage are false: the
-- end-to-end round trip does not make stage two collapse-free, and
-- end-to-end coverage does not make stage one covered.
end-to-end-roundtrip-misses-last-collapse :
  RoundTrip cancelling × Collapse forgetful
end-to-end-roundtrip-misses-last-collapse =
  fst cancelling-faithful , stage-two-collapses

end-to-end-coverage-misses-first-addition :
  Covered cancelling × SansFibre blindspot phantom
end-to-end-coverage-misses-first-addition =
  snd cancelling-faithful , stage-one-adds
