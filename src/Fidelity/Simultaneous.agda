{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Ladder D: solving both sides at once.
--
-- The task has two sides.  The source side offers readings of an informal
-- text, some admissible (A).  The target side offers formal terms, some
-- well formed (W).  A SOLUTION is a reading and a term, each acceptable on
-- its own side, that mean the same thing.  Neither is chosen first.
--
--   D-1  the joint problem is symmetric: a solution is a forward
--        completion of some admissible reading, and equally a backward
--        completion of some well-formed term.
--   D-2  committing to a reading before consulting the target is
--        incomplete: a solution exists and the committed reading has no
--        completion.  Computed.
--   D-3  the mirror image: committing to a term first is incomplete.
--   D-4  the meaning relation is functional when the target reading is
--        injective, and injective when the source reading is.
--   D-5  capstone: when the meaning relation is one-to-one it yields a
--        crossing that is faithful AND sound in both directions.
module Fidelity.Simultaneous where

open import ResourceAlgebra.Prelude
open import Fidelity.Crossing
open import Fidelity.Interface
open import Fidelity.Meaning

module _ {S T M : Set} (semS : S → M) (semT : T → M) where

  -- The interface: reading and term mean the same.
  Means : Corr S T
  Means s t = semS s ≡ semT t

  module _ (A : S → Set) (W : T → Set) where

    Solution : Set
    Solution = Σ S (λ s → Σ T (λ t → (A s × W t) × Means s t))

    -- What is left to solve once one side has been fixed.
    Forward : S → Set
    Forward s = Σ T (λ t → W t × Means s t)

    Backward : T → Set
    Backward t = Σ S (λ s → A s × Means s t)

    -- D-1
    forward-solves : ∀ s → A s → Forward s → Solution
    forward-solves s a (t , w , m) = s , t , (a , w) , m

    backward-solves : ∀ t → W t → Backward t → Solution
    backward-solves t w (s , a , m) = s , t , (a , w) , m

    solution-forward : Solution → Σ S (λ s → A s × Forward s)
    solution-forward (s , t , (a , w) , m) = s , a , t , w , m

    solution-backward : Solution → Σ T (λ t → W t × Backward t)
    solution-backward (s , t , (a , w) , m) = t , w , s , a , m

    -- The target prunes the source and the source prunes the target: a
    -- reading or a term that appears in a solution has a completion.
    Viable : S → Set
    Viable s = A s × Forward s

    Realisable : T → Set
    Realisable t = W t × Backward t

    solution-viable : (x : Solution) → Viable (fst x)
    solution-viable (s , t , (a , w) , m) = a , t , w , m

    solution-realisable : (x : Solution) → Realisable (fst (snd x))
    solution-realisable (s , t , (a , w) , m) = w , s , a , m

  -- D-4
  means-functional : (∀ {t t'} → semT t ≡ semT t' → t ≡ t')
                   → Functional Means
  means-functional inj m m' = inj (trans (sym m) m')

  means-injective : (∀ {s s'} → semS s ≡ semS s' → s ≡ s')
                  → Injective Means
  means-injective inj m m' = inj (trans m (sym m'))

  -- D-5
  module _ (o : OneToOne Means) where

    solved : Crossing S T
    solved = crossing-of Means o

    solved-faithful : Faithful solved
    solved-faithful = crossing-of-faithful Means o

    solved-fwd-sound : FwdSound semS semT solved
    solved-fwd-sound s = sym (snd (entire o s))

    solved-back-sound : BackSound semS semT solved
    solved-back-sound t = snd (onto o t)

----------------------------------------------------------------------
-- D-2, computed.  The text has two admissible readings.  The target has
-- one well-formed term, and it means the second reading.
All : {X : Set} → X → Set
All _ = ⊤

term-means : ⊤ → Two
term-means tt = phantom

real≢phantom : real ≢ phantom
real≢phantom ()

joint-solution : Solution (λ r → r) term-means All All
joint-solution = phantom , tt , (tt , tt) , refl

-- The first reading is admissible, and no term completes it.
commit-reading-fails : ¬ Forward (λ r → r) term-means All All real
commit-reading-fails (tt , _ , ())

----------------------------------------------------------------------
-- D-3, computed.  The mirror image: two well-formed terms, one reading.
reading-means : ⊤ → Two
reading-means tt = phantom

joint-solution' : Solution reading-means (λ r → r) All All
joint-solution' = tt , phantom , (tt , tt) , refl

commit-term-fails : ¬ Backward reading-means (λ r → r) All All real
commit-term-fails (tt , _ , ())
