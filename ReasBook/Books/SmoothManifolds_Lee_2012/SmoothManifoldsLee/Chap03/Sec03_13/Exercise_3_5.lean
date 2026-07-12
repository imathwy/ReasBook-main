import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap03.Sec03_13.Lemma_3_4

-- Declarations for this item will be appended below by the statement pipeline.

/-
Exercise 3.5 is recall-only.
Source-facing layer: the two statement-level lemmas already formalized in `Lemma_3_4`.
Core owner abstraction: `PointDerivation I p`, with derived API coming from
`Derivation.map_algebraMap` and `Derivation.leibniz`.
This file therefore recalls the upstream lemmas directly instead of duplicating them locally.
-/
recall tangent_vector_apply_const

recall tangent_vector_mul_eq_zero_of_vanish_at
