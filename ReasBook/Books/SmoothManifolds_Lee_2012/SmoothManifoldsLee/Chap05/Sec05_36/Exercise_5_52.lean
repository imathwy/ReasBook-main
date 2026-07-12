import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Theorem_5_51

/-
Exercise 5.52 asks for the proof of Theorem 5.51. The source-facing predicate is
`Set.SatisfiesLocalSliceConditionWithBoundary`, and the canonical owner result is the local-slice
criterion `local_slice_criterion_for_embedded_submanifold_with_boundary`.
-/
recall local_slice_criterion_for_embedded_submanifold_with_boundary
