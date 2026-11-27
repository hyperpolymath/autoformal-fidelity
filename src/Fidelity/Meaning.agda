{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Ladder C: meaning.  Both sides are read into one meaning space M
-- (semS : S → M, semT : T → M).  A crossing is SOUND when translation
-- preserves the reading.
--
--   C-1  structure is blind to meaning: a crossing can be faithful
--        (round trip and coverage both pass) and unsound at every element.
--   C-2  two sound directions round-trip up to meaning.
--   C-3  warrant transfer: a round trip that passes up to meaning makes
--        the forward direction exactly as sound as the back direction.
--        The translator's test moves trust; it does not create it.
--   C-4  when the target reading is injective, a sound forward direction
--        is unique.  Meaning pins the crossing; structure does not.
module Fidelity.Meaning where

open import ResourceAlgebra.Prelude
open import Fidelity.Crossing
open import Fidelity.Interface

module _ {S T M : Set} (semS : S → M) (semT : T → M) where

  FwdSound : Crossing S T → Set
  FwdSound c = ∀ s → semT (fwd c s) ≡ semS s

  BackSound : Crossing S T → Set
  BackSound c = ∀ t → semS (back c t) ≡ semT t

  -- The round trip, judged in M and not by equality in S.
  RoundTripUpToMeaning : Crossing S T → Set
  RoundTripUpToMeaning c = ∀ s → semS (back c (fwd c s)) ≡ semS s

  SectionUpToMeaning : Crossing S T → Set
  SectionUpToMeaning c = ∀ t → semT (fwd c (back c t)) ≡ semT t

  module _ (c : Crossing S T) where

    -- A strict round trip is a round trip up to meaning.
    roundtrip-up-to-meaning : RoundTrip c → RoundTripUpToMeaning c
    roundtrip-up-to-meaning rt s = cong semS (rt s)

    -- C-2
    sound-roundtrip : FwdSound c → BackSound c → RoundTripUpToMeaning c
    sound-roundtrip f b s = trans (b (fwd c s)) (f s)

    sound-section : FwdSound c → BackSound c → SectionUpToMeaning c
    sound-section f b t = trans (f (back c t)) (b t)

    -- C-3, both directions.
    transfer-fwd : BackSound c → RoundTripUpToMeaning c → FwdSound c
    transfer-fwd b rtm s = trans (sym (b (fwd c s))) (rtm s)

    transfer-back : FwdSound c → SectionUpToMeaning c → BackSound c
    transfer-back f secm t = trans (sym (f (back c t))) (secm t)

  -- C-4
  sound-unique : (∀ {t t'} → semT t ≡ semT t' → t ≡ t')
               → (c d : Crossing S T) → FwdSound c → FwdSound d
               → ∀ s → fwd c s ≡ fwd d s
  sound-unique inj c d fc fd s = inj (trans (fc s) (sym (fd s)))

----------------------------------------------------------------------
-- C-1, computed.  Two symbols, read as themselves on both sides.  The
-- crossing that swaps them passes the round trip and covers the target,
-- so it is Faithful in the sense of Crossing.agda; it mistranslates both.
data Bit : Set where
  o i : Bit

flip : Bit → Bit
flip o = i
flip i = o

flip-flip : ∀ b → flip (flip b) ≡ b
flip-flip o = refl
flip-flip i = refl

i≢o : i ≢ o
i≢o ()

o≢i : o ≢ i
o≢i ()

same : Bit → Bit
same b = b

swap : Crossing Bit Bit
swap = record { fwd = flip ; back = flip }

swap-faithful : Faithful swap
swap-faithful = flip-flip , (λ y → flip y , flip-flip y)

swap-unsound : ¬ FwdSound same same swap
swap-unsound f = i≢o (f o)

swap-unsound-everywhere : ∀ b → fwd swap b ≢ b
swap-unsound-everywhere o = i≢o
swap-unsound-everywhere i = o≢i

-- The honest crossing over the same two sides is faithful too, so the
-- structural checks cannot tell the two apart.
keep : Crossing Bit Bit
keep = record { fwd = same ; back = same }

keep-faithful : Faithful keep
keep-faithful = (λ s → refl) , (λ y → y , refl)

keep-sound : FwdSound same same keep
keep-sound s = refl

-- The swap is sound for the swapped reading: soundness is a property of
-- the crossing AND the two readings, never of the crossing alone.
swap-sound-for-flipped-reading : FwdSound same flip swap
swap-sound-for-flipped-reading = flip-flip
