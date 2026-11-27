{-# OPTIONS --safe --without-K --cubical-compatible #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Ladder B: the interface as a correspondence.
--
-- A Crossing is a pair of functions, so one side is always solved first.
-- A correspondence R : S → T → Set privileges neither side.  It has four
-- defects, in two mirror pairs:
--
--   omission  (a source element related to nothing)   | addition
--   collapse  (two source elements on one target)     | split
--
-- The converse correspondence swaps each pair (B-1).  A function-pair
-- crossing can express only two of the four (B-2).  A correspondence with
-- none of the four is exactly a faithful crossing (B-3, B-4).  The
-- AGREEMENT relation of a crossing, where both directions hold at once, is
-- always a partial one-to-one correspondence; its only possible defects
-- are omissions and additions (B-5).
module Fidelity.Interface where

open import ResourceAlgebra.Prelude
open import Fidelity.Crossing

Corr : Set → Set → Set₁
Corr S T = S → T → Set

-- The same interface read from the other side.
_˘ : {S T : Set} → Corr S T → Corr T S
(R ˘) t s = R s t

module _ {S T : Set} (R : Corr S T) where

  Entire : Set                       -- no omission
  Entire = ∀ s → Σ T (λ t → R s t)

  Onto : Set                         -- no addition
  Onto = ∀ t → Σ S (λ s → R s t)

  Injective : Set                    -- no collapse
  Injective = ∀ {s s' t} → R s t → R s' t → s ≡ s'

  Functional : Set                   -- no split
  Functional = ∀ {s t t'} → R s t → R s t' → t ≡ t'

  Omitted : S → Set
  Omitted s = ¬ Σ T (λ t → R s t)

  Added : T → Set
  Added t = ¬ Σ S (λ s → R s t)

  Collapsed : Set
  Collapsed = Σ S (λ s → Σ S (λ s' → Σ T (λ t → (R s t × R s' t) × (s ≢ s'))))

  Split : Set
  Split = Σ S (λ s → Σ T (λ t → Σ T (λ t' → (R s t × R s t') × (t ≢ t'))))

  -- Each positive condition refutes its defect.
  entire-no-omission : Entire → ∀ s → ¬ Omitted s
  entire-no-omission e s o = o (e s)

  onto-no-addition : Onto → ∀ t → ¬ Added t
  onto-no-addition o t a = a (o t)

  injective-no-collapse : Injective → ¬ Collapsed
  injective-no-collapse inj (s , s' , t , (r , r') , ne) = ne (inj r r')

  functional-no-split : Functional → ¬ Split
  functional-no-split fun (s , t , t' , (r , r') , ne) = ne (fun r r')

  record OneToOne : Set where
    field
      entire     : Entire
      onto       : Onto
      injective  : Injective
      functional : Functional
  open OneToOne public

----------------------------------------------------------------------
-- B-1: the two sides are mirror images.  Addition is the omission of the
-- opposite direction; split is its collapse.  All four hold by definition.
module _ {S T : Set} (R : Corr S T) where

  onto-is-entire˘ : Onto R → Entire (R ˘)
  onto-is-entire˘ o = o

  entire-is-onto˘ : Entire R → Onto (R ˘)
  entire-is-onto˘ e = e

  functional-is-injective˘ : Functional R → Injective (R ˘)
  functional-is-injective˘ f = f

  injective-is-functional˘ : Injective R → Functional (R ˘)
  injective-is-functional˘ i = i

  one-to-one˘ : OneToOne R → OneToOne (R ˘)
  one-to-one˘ o = record
    { entire = onto o ; onto = entire o
    ; injective = functional o ; functional = injective o }

----------------------------------------------------------------------
-- B-2: the graph of a crossing.  It is entire and functional whatever the
-- crossing is, so a function-pair crossing cannot express an omission or
-- a split at all.  Round trip buys injectivity; coverage buys onto.
module _ {S T : Set} (c : Crossing S T) where

  Graph : Corr S T
  Graph s t = fwd c s ≡ t

  graph-entire : Entire Graph
  graph-entire s = fwd c s , refl

  graph-functional : Functional Graph
  graph-functional e e' = trans (sym e) e'

  graph-injective : RoundTrip c → Injective Graph
  graph-injective rt {s} {s'} e e' =
    roundtrip-injective c rt s s' (trans e (sym e'))

  graph-onto : Covered c → Onto Graph
  graph-onto cov = cov

  -- B-3: a faithful crossing has a one-to-one graph.
  faithful-one-to-one : Faithful c → OneToOne Graph
  faithful-one-to-one (rt , cov) = record
    { entire = graph-entire ; onto = graph-onto cov
    ; injective = graph-injective rt ; functional = graph-functional }

----------------------------------------------------------------------
-- B-4: a one-to-one correspondence is a faithful crossing, and the
-- crossing's graph is the correspondence it came from.
module _ {S T : Set} (R : Corr S T) (o : OneToOne R) where

  crossing-of : Crossing S T
  crossing-of = record { fwd = λ s → fst (entire o s)
                       ; back = λ t → fst (onto o t) }

  crossing-of-roundtrip : RoundTrip crossing-of
  crossing-of-roundtrip s =
    injective o (snd (onto o (fst (entire o s)))) (snd (entire o s))

  crossing-of-covered : Covered crossing-of
  crossing-of-covered t =
    fst (onto o t) ,
    functional o (snd (entire o (fst (onto o t)))) (snd (onto o t))

  crossing-of-faithful : Faithful crossing-of
  crossing-of-faithful = crossing-of-roundtrip , crossing-of-covered

  graph-to-corr : ∀ {s t} → Graph crossing-of s t → R s t
  graph-to-corr {s} e = subst (R s) e (snd (entire o s))

  corr-to-graph : ∀ {s t} → R s t → Graph crossing-of s t
  corr-to-graph {s} r = functional o (snd (entire o s)) r

----------------------------------------------------------------------
-- B-5: agreement.  s and t agree when each direction sends one to the
-- other: both sides hold at once.  Agreement is injective and functional
-- for every crossing, with no hypothesis.  It is entire exactly when the
-- round trip passes, and onto exactly when the other round trip passes.
module _ {S T : Set} (c : Crossing S T) where

  Agree : Corr S T
  Agree s t = (fwd c s ≡ t) × (back c t ≡ s)

  Section : Set                      -- the round trip started from T
  Section = ∀ t → fwd c (back c t) ≡ t

  agree-injective : Injective Agree
  agree-injective (_ , b) (_ , b') = trans (sym b) b'

  agree-functional : Functional Agree
  agree-functional (f , _) (f' , _) = trans (sym f) f'

  roundtrip-agree-entire : RoundTrip c → Entire Agree
  roundtrip-agree-entire rt s = fwd c s , refl , rt s

  agree-entire-roundtrip : Entire Agree → RoundTrip c
  agree-entire-roundtrip e s with e s
  ... | t , f , b = trans (cong (back c) f) b

  section-agree-onto : Section → Onto Agree
  section-agree-onto sec t = back c t , sec t , refl

  agree-onto-section : Onto Agree → Section
  agree-onto-section o t with o t
  ... | s , f , b = trans (cong (fwd c) b) f

  agree-one-to-one : RoundTrip c → Section → OneToOne Agree
  agree-one-to-one rt sec = record
    { entire = roundtrip-agree-entire rt ; onto = section-agree-onto sec
    ; injective = agree-injective ; functional = agree-functional }
