/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
-/

import Mathlib
import Books.Analysis2_Tao_2022.Chapters.Chap06.section06_part4

section Chap06
section Section06

/-- Helper for Theorem 6.8: nonexistence of continuous counterexamples to the fixed/anti-fixed
statement is equivalent to nonexistence of continuous counterexamples to the fixed-point-or-
antipode-equality statement. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_antifixed_iff_no_counterexample_fixed_or_fixed_eq_antipode :
    (¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) ↔
      (¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)))) := by
  simpa using not_congr
    helperForTheorem_6_8_exists_counterexample_fixed_or_antifixed_iff_exists_counterexample_fixed_or_fixed_eq_antipode

/-- Helper for Theorem 6.8: the fixed-point-or-antipode-equality no-counterexample
statement is equivalent to the corresponding global existence principle. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_fixed_eq_antipode_iff_global_fixed_or_fixed_eq_antipode :
    (¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)))) ↔
      (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x))) := by
  simpa using
    (helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_iff_no_counterexample).symm

/-- Helper for Theorem 6.8: equality with `-x` in `UnitSphereTwo` is equivalent to equality
with the dedicated antipode map at `x`. -/
lemma helperForTheorem_6_8_eq_neg_iff_eq_antipode
    {g : UnitSphereTwo → UnitSphereTwo} {x : UnitSphereTwo} :
    g x = -x ↔ g x = helperForTheorem_6_8_antipode x := by
  constructor
  · intro hx
    simpa [helperForTheorem_6_8_antipode] using hx
  · intro hx
    simpa [helperForTheorem_6_8_antipode] using hx

/-- Helper for Theorem 6.8: a global fixed-point-or-negation principle on `S²`
immediately yields the fixed-point-or-antipode-equality principle used in this section. -/
lemma helperForTheorem_6_8_continuous_selfMap_unitSphereTwo_exists_fixed_or_fixed_eq_antipode_of_fixed_or_neg_principle
    (hfixedOrNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) := by
  intro g hg
  rcases hfixedOrNeg g hg with hfixed | hneg
  · exact Or.inl hfixed
  · rcases hneg with ⟨x, hx⟩
    have hxAntipode : g x = helperForTheorem_6_8_antipode x :=
      (helperForTheorem_6_8_eq_neg_iff_eq_antipode (g := g) (x := x)).1 hx
    exact Or.inr ⟨x, hxAntipode⟩

/-- Helper for Theorem 6.8: for a fixed self-map of `S²`, the fixed-or-negation
disjunction is equivalent to the fixed-or-antipode-equality disjunction. -/
lemma helperForTheorem_6_8_fixed_or_neg_iff_fixed_or_fixed_eq_antipode
    {g : UnitSphereTwo → UnitSphereTwo} :
    ((∃ x : UnitSphereTwo, g x = x) ∨
      (∃ x : UnitSphereTwo, g x = -x)) ↔
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) := by
  constructor
  · intro h
    rcases h with hfixed | hneg
    · exact Or.inl hfixed
    · rcases hneg with ⟨x, hx⟩
      exact Or.inr ⟨x, (helperForTheorem_6_8_eq_neg_iff_eq_antipode (g := g) (x := x)).1 hx⟩
  · intro h
    rcases h with hfixed | hantipode
    · exact Or.inl hfixed
    · rcases hantipode with ⟨x, hx⟩
      exact Or.inr ⟨x, (helperForTheorem_6_8_eq_neg_iff_eq_antipode (g := g) (x := x)).2 hx⟩

/-- Helper for Theorem 6.8: globally on continuous self-maps of `S²`, fixed-or-negation
and fixed-or-antipode-equality are equivalent principles. -/
lemma helperForTheorem_6_8_global_fixed_or_neg_iff_global_fixed_or_fixed_eq_antipode :
    (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x))) ↔
      (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x))) := by
  constructor
  · intro h g hg
    exact
      (helperForTheorem_6_8_fixed_or_neg_iff_fixed_or_fixed_eq_antipode (g := g)).1 (h g hg)
  · intro h g hg
    exact
      (helperForTheorem_6_8_fixed_or_neg_iff_fixed_or_fixed_eq_antipode (g := g)).2 (h g hg)

/-- Helper for Theorem 6.8: global fixed-point-or-negation is equivalent to
nonexistence of a continuous counterexample in fixed-or-negation form. -/
lemma helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample :
    (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x))) ↔
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x))) := by
  constructor
  · intro h hcounterexample
    rcases hcounterexample with ⟨g, hg, hnot⟩
    exact hnot (h g hg)
  · intro h g hg
    by_contra hnot
    exact h ⟨g, hg, hnot⟩

/-- Helper for Theorem 6.8: existence of a continuous fixed-point-or-negation
counterexample is equivalent to failure of the corresponding global principle on `S²`. -/
lemma helperForTheorem_6_8_exists_counterexample_fixed_or_neg_iff_not_global_fixed_or_neg :
    (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x))) ↔
      ¬ (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x))) := by
  constructor
  · intro hcounterexample hglobal
    rcases hcounterexample with ⟨g, hg, hnot⟩
    exact hnot (hglobal g hg)
  · intro hnotglobal
    by_contra hcounterexample
    have hglobal :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = -x)) :=
      (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).2 hcounterexample
    exact hnotglobal hglobal

/-- Helper for Theorem 6.8: the no-counterexample formulations in fixed-or-negation
and fixed-or-antipode-equality form are equivalent. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_neg_iff_no_counterexample_fixed_or_fixed_eq_antipode :
    (¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x)))) ↔
      (¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)))) := by
  constructor
  · intro hneg
    have hglobalNeg :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = -x)) :=
      (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).2 hneg
    have hglobalAntipode :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) :=
      (helperForTheorem_6_8_global_fixed_or_neg_iff_global_fixed_or_fixed_eq_antipode).1 hglobalNeg
    exact
      (helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_iff_no_counterexample).1
        hglobalAntipode
  · intro hantipode
    have hglobalAntipode :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) :=
      (helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_iff_no_counterexample).2
        hantipode
    have hglobalNeg :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = -x)) :=
      (helperForTheorem_6_8_global_fixed_or_neg_iff_global_fixed_or_fixed_eq_antipode).2
        hglobalAntipode
    exact
      (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).1
        hglobalNeg

/-- Helper for Theorem 6.8: a no-counterexample fixed-point-or-negation hypothesis
implies the corresponding global fixed-point-or-negation principle on `S²`. -/
lemma helperForTheorem_6_8_global_fixed_or_neg_of_no_counterexample_fixed_or_neg
    (hnoCounterexampleNeg :
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x)) := by
  exact
    (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).2
      hnoCounterexampleNeg

/-- Helper for Theorem 6.8: a no-counterexample fixed-point-or-negation hypothesis
implies the corresponding global fixed-point-or-antipode-equality principle on `S²`. -/
lemma helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_of_no_counterexample_fixed_or_neg
    (hnoCounterexampleNeg :
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) := by
  have hglobalNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)) :=
    helperForTheorem_6_8_global_fixed_or_neg_of_no_counterexample_fixed_or_neg
      hnoCounterexampleNeg
  exact
    (helperForTheorem_6_8_global_fixed_or_neg_iff_global_fixed_or_fixed_eq_antipode).1
      hglobalNeg

/-- Helper for Theorem 6.8: failure of the global fixed-point-or-antipode-equality principle
forces failure of the global fixed-point-or-negation principle on `S²`. -/
lemma helperForTheorem_6_8_not_global_fixed_or_neg_of_not_global_fixed_or_fixed_eq_antipode
    (hnotglobal :
      ¬ (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)))) :
    ¬ (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x))) := by
  intro hglobalNeg
  have hglobalAntipode :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) :=
    (helperForTheorem_6_8_global_fixed_or_neg_iff_global_fixed_or_fixed_eq_antipode).1
      hglobalNeg
  exact hnotglobal hglobalAntipode

/-- Helper for Theorem 6.8: if the global fixed-point-or-antipode-equality principle fails,
there exists a continuous self-map counterexample in fixed-point-or-negation form. -/
lemma helperForTheorem_6_8_exists_counterexample_fixed_or_neg_of_not_global_fixed_or_fixed_eq_antipode
    (hnotglobal :
      ¬ (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)))) :
    ∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x)) := by
  have hnotglobalNeg :
      ¬ (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = -x))) :=
    helperForTheorem_6_8_not_global_fixed_or_neg_of_not_global_fixed_or_fixed_eq_antipode
      hnotglobal
  exact
    (helperForTheorem_6_8_exists_counterexample_fixed_or_neg_iff_not_global_fixed_or_neg).2
      hnotglobalNeg

/-- Helper for Theorem 6.8: nonexistence of continuous fixed-point-or-negation
counterexamples is equivalent to the global fixed-point-or-antipode-equality
principle on `S²`. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_neg_iff_global_fixed_or_fixed_eq_antipode :
    (¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)))) ↔
      (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x))) := by
  constructor
  · intro hnoCounterexampleNeg
    exact
      helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_of_no_counterexample_fixed_or_neg
        hnoCounterexampleNeg
  · intro hglobalAntipode
    have hglobalNeg :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = -x)) :=
      (helperForTheorem_6_8_global_fixed_or_neg_iff_global_fixed_or_fixed_eq_antipode).2
        hglobalAntipode
    exact
      (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).1
        hglobalNeg

/-- Helper for Theorem 6.8: a global fixed-point-or-negation principle on continuous
self-maps of `S²` implies the global fixed/anti-fixed witness principle. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_global_fixed_or_neg
    (hglobalNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  intro g hg
  rcases hglobalNeg g hg with hfixed | hneg
  · rcases hfixed with ⟨x, hx⟩
    exact ⟨x, Or.inl hx⟩
  · rcases hneg with ⟨x, hx⟩
    have hxVal : (g x).1 = -x.1 := by
      simpa using congrArg Subtype.val hx
    exact ⟨x, Or.inr hxVal⟩

/-- Helper for Theorem 6.8: for a fixed self-map of `S²`, a fixed-or-negation witness
directly yields a fixed/anti-fixed witness. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_fixed_or_neg
    {f : UnitSphereTwo → UnitSphereTwo}
    (h : ((∃ x : UnitSphereTwo, f x = x) ∨
      (∃ x : UnitSphereTwo, f x = -x))) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  rcases h with hfixed | hneg
  · rcases hfixed with ⟨x, hx⟩
    exact ⟨x, Or.inl hx⟩
  · rcases hneg with ⟨x, hx⟩
    have hxVal : (f x).1 = -x.1 := by
      simpa using congrArg Subtype.val hx
    exact ⟨x, Or.inr hxVal⟩

/-- Helper for Theorem 6.8: if a global fixed-point-or-negation principle is available
for continuous self-maps of `S²`, then any continuous self-map has a fixed or anti-fixed point. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_global_fixed_or_neg_principle
    (hglobalNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)))
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  exact
    helperForTheorem_6_8_exists_fixed_or_antifixed_of_fixed_or_neg
      (hglobalNeg f hcont)

/-- Helper for Theorem 6.8: for a fixed self-map of `S²`, a fixed/anti-fixed witness
directly yields a fixed-or-negation witness. -/
lemma helperForTheorem_6_8_exists_fixed_or_neg_of_exists_fixed_or_antifixed
    {f : UnitSphereTwo → UnitSphereTwo}
    (h : ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1) :
    ((∃ x : UnitSphereTwo, f x = x) ∨
      (∃ x : UnitSphereTwo, f x = -x)) := by
  rcases h with ⟨x, hx⟩
  rcases hx with hfixed | hantifixed
  · exact Or.inl ⟨x, hfixed⟩
  · have hneg : f x = -x := by
      apply Subtype.ext
      simpa using hantifixed
    exact Or.inr ⟨x, hneg⟩

/-- Helper for Theorem 6.8: for a fixed self-map of `S²`, fixed/anti-fixed and
fixed-or-negation witness formulations are equivalent. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_iff_exists_fixed_or_neg
    {f : UnitSphereTwo → UnitSphereTwo} :
    (∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1) ↔
      ((∃ x : UnitSphereTwo, f x = x) ∨
        (∃ x : UnitSphereTwo, f x = -x)) := by
  constructor
  · intro h
    exact helperForTheorem_6_8_exists_fixed_or_neg_of_exists_fixed_or_antifixed h
  · intro h
    exact helperForTheorem_6_8_exists_fixed_or_antifixed_of_fixed_or_neg h

/-- Helper for Theorem 6.8: no-counterexample formulations in fixed-or-negation and
fixed/anti-fixed forms are equivalent on continuous self-maps of `S²`. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_neg_iff_no_counterexample_fixed_or_antifixed :
    (¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)))) ↔
      (¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  constructor
  · intro hnoCounterexampleNeg
    have hglobalNeg :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = -x)) :=
      (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).2
        hnoCounterexampleNeg
    have hglobalAntifixed :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) :=
      helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_global_fixed_or_neg
        hglobalNeg
    exact
      (helperForTheorem_6_8_global_exists_fixed_or_antifixed_iff_no_counterexample).1
        hglobalAntifixed
  · intro hnoCounterexampleAntifixed
    have hglobalAntifixed :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) :=
      (helperForTheorem_6_8_global_exists_fixed_or_antifixed_iff_no_counterexample).2
        hnoCounterexampleAntifixed
    have hglobalAntipode :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) :=
      helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_of_global_exists_fixed_or_antifixed
        hglobalAntifixed
    have hglobalNeg :
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          ((∃ x : UnitSphereTwo, g x = x) ∨
            (∃ x : UnitSphereTwo, g x = -x)) :=
      (helperForTheorem_6_8_global_fixed_or_neg_iff_global_fixed_or_fixed_eq_antipode).2
        hglobalAntipode
    exact
      (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).1
        hglobalNeg

/-- Helper for Theorem 6.8: a global fixed/anti-fixed witness principle on continuous
self-maps of `S²` implies the corresponding global fixed-or-negation principle. -/
lemma helperForTheorem_6_8_global_fixed_or_neg_of_global_exists_fixed_or_antifixed
    (hglobalAntifixed :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x)) := by
  intro g hg
  exact
    helperForTheorem_6_8_exists_fixed_or_neg_of_exists_fixed_or_antifixed
      (hglobalAntifixed g hg)

/-- Helper for Theorem 6.8: global fixed/anti-fixed existence and global fixed-or-negation
principles are equivalent for continuous self-maps of `S²`. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_iff_global_fixed_or_neg :
    (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) ↔
      (∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x))) := by
  constructor
  · intro hglobalAntifixed
    exact
      helperForTheorem_6_8_global_fixed_or_neg_of_global_exists_fixed_or_antifixed
        hglobalAntifixed
  · intro hglobalNeg
    exact
      helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_global_fixed_or_neg
        hglobalNeg

/-- Helper for Theorem 6.8: nonexistence of continuous fixed-point-or-negation
counterexamples implies the global fixed/anti-fixed alternative on `S²`. -/
lemma helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_no_counterexample_fixed_or_neg
    (hnoCounterexampleNeg :
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)))) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1 := by
  have hnoCounterexampleAntifixed :
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :=
    (helperForTheorem_6_8_no_counterexample_fixed_or_neg_iff_no_counterexample_fixed_or_antifixed).1
      hnoCounterexampleNeg
  exact
    (helperForTheorem_6_8_global_exists_fixed_or_antifixed_iff_no_counterexample).2
      hnoCounterexampleAntifixed

/-- Helper for Theorem 6.8: a no-counterexample fixed-or-negation hypothesis yields the
local fixed-or-negation disjunction for any continuous self-map of `S²`. -/
lemma helperForTheorem_6_8_fixed_or_neg_of_continuous_of_no_counterexample_fixed_or_neg
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f)
    (hnoCounterexampleNeg :
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)))) :
    ((∃ x : UnitSphereTwo, f x = x) ∨
      (∃ x : UnitSphereTwo, f x = -x)) := by
  exact
    (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).2
      hnoCounterexampleNeg f hcont

/-- Helper for Theorem 6.8: under nonexistence of continuous fixed-point-or-negation
counterexamples, each continuous self-map of `S²` has a fixed or anti-fixed point. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_no_counterexample_fixed_or_antifixed
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f)
    (hnoCounterexampleAntifixed :
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  exact
    (helperForTheorem_6_8_global_exists_fixed_or_antifixed_iff_no_counterexample).2
      hnoCounterexampleAntifixed f hcont

/-- Helper for Theorem 6.8: under nonexistence of continuous fixed-point-or-negation
counterexamples, each continuous self-map of `S²` has a fixed or anti-fixed point. -/
lemma helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_no_counterexample_fixed_or_neg
    (f : UnitSphereTwo → UnitSphereTwo) (hcont : Continuous f)
    (hnoCounterexampleNeg :
      ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
        ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)))) :
    ∃ x : UnitSphereTwo, f x = x ∨ (f x).1 = -x.1 := by
  have hglobalNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)) :=
    (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).2 hnoCounterexampleNeg
  exact
    helperForTheorem_6_8_exists_fixed_or_antifixed_of_continuous_of_global_fixed_or_neg_principle
      hglobalNeg f hcont

/-- Helper for Theorem 6.8: a Borsuk-Ulam antipodal-equality principle on maps
`S² → ℝ²`, together with a reduction from that principle to continuous self-maps of `S²`,
yields the global fixed-point-or-negation principle on continuous self-maps of `S²`. -/
lemma helperForTheorem_6_8_global_fixed_or_neg_of_borsuk_ulam_pipeline
    (hborsukUlam :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)))
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x)) := by
  have hglobalAntifixed :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) :=
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_borsuk_ulam_pipeline
      hborsukUlam hreduction
  have hglobalAntipode :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = helperForTheorem_6_8_antipode x)) :=
    helperForTheorem_6_8_global_fixed_or_fixed_eq_antipode_of_global_exists_fixed_or_antifixed
      hglobalAntifixed
  exact
    (helperForTheorem_6_8_global_fixed_or_neg_iff_global_fixed_or_fixed_eq_antipode).2
      hglobalAntipode

/-- Helper for Theorem 6.8: a Borsuk-Ulam antipodal-equality principle on maps
`S² → ℝ²`, together with a reduction from that principle to continuous self-maps of `S²`,
implies the no-counterexample fixed-point-or-negation statement. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_neg_of_borsuk_ulam_pipeline
    (hborsukUlam :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)))
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x))) := by
  have hglobalNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)) :=
    helperForTheorem_6_8_global_fixed_or_neg_of_borsuk_ulam_pipeline
      hborsukUlam hreduction
  exact
    (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).1
      hglobalNeg

/-- Helper for Theorem 6.8: an odd-zero principle for continuous maps
`S² → ℝ²`, together with a reduction from antipodal equality to the
fixed/anti-fixed alternative for continuous self-maps of `S²`, yields the
global fixed-point-or-negation principle on continuous self-maps of `S²`. -/
lemma helperForTheorem_6_8_global_fixed_or_neg_of_odd_zero_pipeline
    (hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0)
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
      ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x)) := by
  have hborsukUlam :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)) := by
    intro g hg
    exact
      helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
        hoddZero g hg
  exact
    helperForTheorem_6_8_global_fixed_or_neg_of_borsuk_ulam_pipeline
      hborsukUlam hreduction

/-- Helper for Theorem 6.8: an odd-zero principle for continuous maps
`S² → ℝ²`, together with a reduction from antipodal equality to the
fixed/anti-fixed alternative for continuous self-maps of `S²`, implies the
no-counterexample fixed-point-or-negation statement. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_neg_of_odd_zero_pipeline
    (hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0)
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x))) := by
  have hglobalNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)) :=
    helperForTheorem_6_8_global_fixed_or_neg_of_odd_zero_pipeline
      hoddZero hreduction
  exact
    (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).1
      hglobalNeg

/-- Helper for Theorem 6.8: a Borsuk-Ulam antipodal-equality principle on maps
`S² → ℝ²`, together with a reduction from antipodal equality to the
fixed/anti-fixed alternative for continuous self-maps of `S²`, implies
nonexistence of continuous fixed/anti-fixed counterexamples. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_antifixed_of_borsuk_ulam_pipeline
    (hborsukUlam :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x)))
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  have hglobalAntifixed :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) :=
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_borsuk_ulam_pipeline
      hborsukUlam hreduction
  exact
    (helperForTheorem_6_8_global_exists_fixed_or_antifixed_iff_no_counterexample).1
      hglobalAntifixed

/-- Helper for Theorem 6.8: an odd-zero principle on maps `S² → ℝ²`,
together with a reduction from antipodal equality to the fixed/anti-fixed
alternative for continuous self-maps of `S²`, implies nonexistence of
continuous fixed/anti-fixed counterexamples. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_antifixed_of_odd_zero_pipeline
    (hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0)
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  have hglobalAntifixed :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) :=
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_odd_zero_pipeline
      hoddZero hreduction
  exact
    (helperForTheorem_6_8_global_exists_fixed_or_antifixed_iff_no_counterexample).1
      hglobalAntifixed

/-- Helper for Theorem 6.8: once a global fixed-point-or-negation principle for
continuous self-maps of `S²` is available, the corresponding no-counterexample
formulation follows immediately. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_neg_of_global_fixed_or_neg_principle
    (hglobalNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x))) :
    ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x))) := by
  exact
    (helperForTheorem_6_8_global_fixed_or_neg_iff_no_counterexample).1
      hglobalNeg

/-- Helper for Theorem 6.8: a global fixed/anti-fixed existence principle on continuous
self-maps of `S²` implies the no-counterexample fixed-point-or-negation statement. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_neg_of_global_exists_fixed_or_antifixed
    (hglobalAntifixed :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ ((∃ x : UnitSphereTwo, g x = x) ∨
        (∃ x : UnitSphereTwo, g x = -x))) := by
  have hglobalNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x)) :=
    helperForTheorem_6_8_global_fixed_or_neg_of_global_exists_fixed_or_antifixed
      hglobalAntifixed
  exact
    helperForTheorem_6_8_no_counterexample_fixed_or_neg_of_global_fixed_or_neg_principle
      hglobalNeg

/-- Helper for Theorem 6.8: a global fixed-point-or-negation principle on continuous
self-maps of `S²` implies nonexistence of continuous counterexamples in fixed/anti-fixed form. -/
lemma helperForTheorem_6_8_no_counterexample_fixed_or_antifixed_of_global_fixed_or_neg
    (hglobalNeg :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ((∃ x : UnitSphereTwo, g x = x) ∨
          (∃ x : UnitSphereTwo, g x = -x))) :
    ¬ (∃ g : UnitSphereTwo → UnitSphereTwo, Continuous g ∧
      ¬ (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  have hglobalAntifixed :
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) :=
    helperForTheorem_6_8_global_exists_fixed_or_antifixed_of_global_fixed_or_neg
      hglobalNeg
  exact
    (helperForTheorem_6_8_global_exists_fixed_or_antifixed_iff_no_counterexample).1
      hglobalAntifixed

/-- Helper for Theorem 6.8: an antipodal-equality principle on continuous maps
`S² → ℝ²` implies the odd-zero principle on continuous odd maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_antipodal_equality
    (hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) :
    ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0 := by
  intro h hcont hodd
  rcases hantipodal h hcont with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hneg : h (-x) = -h x := hodd x
  have hselfNeg : h x = -h x := by
    calc
      h x = h (-x) := hx
      _ = -h x := hneg
  have hsum : h x + h x = 0 := by
    nth_rewrite 2 [hselfNeg]
    exact add_neg_cancel (h x)
  have htwo : (2 : ℝ) • h x = 0 := by
    simpa [two_smul] using hsum
  have htwoNe : (2 : ℝ) ≠ 0 := by
    norm_num
  exact (smul_eq_zero.mp htwo).resolve_left htwoNe

/-- Helper for Theorem 6.8: a packaged upstream antipodal-equality source and reduction
map imply the corresponding odd-zero package and odd-zero-to-self-map reduction package. -/
lemma helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_of_upstream_antipodal_package
    (hsource :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  constructor
  · exact
      helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_antipodal_equality
        hsource.1
  · intro hoddZero
    have hantipodal :
        ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
          (∃ x : UnitSphereTwo, g x = g (-x)) := by
      intro g hg
      exact
        helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
          hoddZero g hg
    exact hsource.2 hantipodal

/-- Helper for Theorem 6.8: a packaged odd-zero source and odd-zero-to-self-map
reduction imply the corresponding antipodal-equality package and antipodal-to-self-map reduction. -/
lemma helperForTheorem_6_8_upstream_antipodal_and_selfMap_reduction_package_of_upstream_odd_zero_package
    (hpackage :
      (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  constructor
  · intro g hg
    exact
      helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
        hpackage.1 g hg
  · intro hantipodal
    have hoddZero :
        ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
          (∀ x : UnitSphereTwo, h (-x) = -h x) →
            ∃ x : UnitSphereTwo, h x = 0 :=
      helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_antipodal_equality
        hantipodal
    exact hpackage.2 hoddZero

/-- Helper for Theorem 6.8: the packaged antipodal-equality dependency source is equivalent
to the packaged odd-zero dependency source. -/
lemma helperForTheorem_6_8_upstream_antipodal_package_iff_upstream_odd_zero_package :
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) ↔
    ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) := by
  constructor
  · intro hsource
    exact
      helperForTheorem_6_8_upstream_odd_zero_and_selfMap_reduction_package_of_upstream_antipodal_package
        hsource
  · intro hpackage
    exact
      helperForTheorem_6_8_upstream_antipodal_and_selfMap_reduction_package_of_upstream_odd_zero_package
        hpackage

/-- Helper for Theorem 6.8: a common-zero principle for two continuous odd real-valued
maps on `S²` yields the odd-zero principle for continuous odd maps `S² → ℝ²`. -/
lemma helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_common_zero_real_pair
    (hcommonZero :
      ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) :
    ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0 := by
  intro h hcont hodd
  let u : UnitSphereTwo → ℝ := fun x => EuclideanSpace.proj (0 : Fin 2) (h x)
  let v : UnitSphereTwo → ℝ := fun x => EuclideanSpace.proj (1 : Fin 2) (h x)
  have huCont : Continuous u := by
    simpa [u] using (EuclideanSpace.proj (0 : Fin 2)).continuous.comp hcont
  have hvCont : Continuous v := by
    simpa [v] using (EuclideanSpace.proj (1 : Fin 2)).continuous.comp hcont
  have huOdd : ∀ x : UnitSphereTwo, u (-x) = -u x := by
    intro x
    dsimp [u]
    simpa using
      congrArg (fun y : EuclideanSpace ℝ (Fin 2) => EuclideanSpace.proj (0 : Fin 2) y) (hodd x)
  have hvOdd : ∀ x : UnitSphereTwo, v (-x) = -v x := by
    intro x
    dsimp [v]
    simpa using
      congrArg (fun y : EuclideanSpace ℝ (Fin 2) => EuclideanSpace.proj (1 : Fin 2) y) (hodd x)
  rcases hcommonZero u v huCont hvCont huOdd hvOdd with ⟨x, hux, hvx⟩
  refine ⟨x, ?_⟩
  refine helperForTheorem_6_8_euclideanTwo_eq_zero_of_proj_zero ?_ ?_
  · simpa [u] using hux
  · simpa [v] using hvx

/-- Helper for Theorem 6.8: a non-circular antipodal-equality-to-self-map reduction
upgrades any odd-zero principle on `S² → ℝ²` to fixed/anti-fixed existence for
continuous self-maps of `S²`. -/
lemma helperForTheorem_6_8_upstream_continuous_selfMap_unitSphereTwo_exists_fixed_or_antifixed_of_odd_zero_of_noncircular_antipodal_reduction
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
      (∀ x : UnitSphereTwo, h (-x) = -h x) →
        ∃ x : UnitSphereTwo, h x = 0) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) := by
  intro hoddZero g hg
  have hantipodal :
      ∀ g' : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g' →
        (∃ x : UnitSphereTwo, g' x = g' (-x)) := by
    intro g' hg'
    exact
      helperForTheorem_6_8_exists_antipodal_equal_of_continuous_of_odd_zero_principle
        hoddZero g' hg'
  exact hreduction hantipodal g hg

/-- Helper for Theorem 6.8: an antipodal-equality principle on continuous maps
`S² → ℝ²` yields a common zero for any pair of continuous odd real-valued maps on `S²`. -/
lemma helperForTheorem_6_8_continuous_odd_real_pair_common_zero_of_antipodal_equality
    (hantipodal :
      ∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) :
    ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
      (∀ x : UnitSphereTwo, u (-x) = -u x) →
      (∀ x : UnitSphereTwo, v (-x) = -v x) →
        ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0 := by
  intro u v huCont hvCont huOdd hvOdd
  let hpair : UnitSphereTwo → EuclideanSpace ℝ (Fin 2) :=
    fun x => WithLp.toLp (2 : ENNReal) ![u x, v x]
  have hpairCont : Continuous hpair := by
    refine (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ)).comp ?_
    refine continuous_pi ?_
    intro i
    fin_cases i
    · simpa [hpair] using huCont
    · simpa [hpair] using hvCont
  have hpairOdd : ∀ x : UnitSphereTwo, hpair (-x) = -hpair x := by
    intro x
    ext i
    fin_cases i
    · simp [hpair, huOdd x]
    · simp [hpair, hvOdd x]
  have hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0 :=
    helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_antipodal_equality
      hantipodal
  rcases hoddZero hpair hpairCont hpairOdd with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hx0 : EuclideanSpace.proj (0 : Fin 2) (hpair x) = 0 := by
    simpa using
      congrArg (fun y : EuclideanSpace ℝ (Fin 2) => EuclideanSpace.proj (0 : Fin 2) y) hx
  have hx1 : EuclideanSpace.proj (1 : Fin 2) (hpair x) = 0 := by
    simpa using
      congrArg (fun y : EuclideanSpace ℝ (Fin 2) => EuclideanSpace.proj (1 : Fin 2) y) hx
  constructor
  · simpa [hpair] using hx0
  · simpa [hpair] using hx1

/-- Helper for Theorem 6.8: a common-zero source for odd real pairs together with a
non-circular antipodal-to-self-map reduction yields the packaged upstream antipodal
dependency source. -/
lemma helperForTheorem_6_8_upstream_antipodal_equality_and_selfMap_reduction_dependency_source_of_common_zero_real_pair_and_noncircular_reduction
    (hcommonZero :
      ∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0)
    (hreduction :
      (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  have hoddZero :
      ∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0 :=
    helperForTheorem_6_8_continuous_odd_map_unitSphereTwo_to_euclideanTwo_exists_zero_of_common_zero_real_pair
      hcommonZero
  have hoddZeroReduction :
      (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1) :=
    helperForTheorem_6_8_upstream_continuous_selfMap_unitSphereTwo_exists_fixed_or_antifixed_of_odd_zero_of_noncircular_antipodal_reduction
      hreduction
  have hoddZeroPackage :
      (∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) ∧
      ((∀ h : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous h →
        (∀ x : UnitSphereTwo, h (-x) = -h x) →
          ∃ x : UnitSphereTwo, h x = 0) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
    exact ⟨hoddZero, hoddZeroReduction⟩
  exact
    helperForTheorem_6_8_upstream_antipodal_and_selfMap_reduction_package_of_upstream_odd_zero_package
      hoddZeroPackage

/-- Helper for Theorem 6.8: a packaged pair consisting of a common-zero principle
for odd real pairs on `S²` and a non-circular antipodal-to-self-map reduction
immediately yields the upstream antipodal dependency source package. -/
lemma helperForTheorem_6_8_upstream_antipodal_equality_and_selfMap_reduction_dependency_source_of_common_zero_and_reduction_package
    (hcommonZeroAndReduction :
      (∀ u v : UnitSphereTwo → ℝ, Continuous u → Continuous v →
        (∀ x : UnitSphereTwo, u (-x) = -u x) →
        (∀ x : UnitSphereTwo, v (-x) = -v x) →
          ∃ x : UnitSphereTwo, u x = 0 ∧ v x = 0) ∧
      ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
        (∃ x : UnitSphereTwo, g x = g (-x))) →
        ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
          (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1))) :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    helperForTheorem_6_8_upstream_antipodal_equality_and_selfMap_reduction_dependency_source_of_common_zero_real_pair_and_noncircular_reduction
      hcommonZeroAndReduction.1 hcommonZeroAndReduction.2

/-- Independent upstream bridge for Theorem 6.8 (placed in `section06_part5` to break
declaration-order cycles in downstream files).

Purpose:
* Provide an unconditional antipodal-equality source on `S² → ℝ²`;
* Provide an unconditional reduction from that source to fixed/anti-fixed witnesses on
  continuous self-maps of `S²`.

Anti-cycle contract:
* This theorem should be proved from genuinely upstream facts only.
* Do not use any declaration whose dependency graph contains the downstream bridge node
  in `section06_part6` (or declarations built from it).

Natural-language proof blueprint (to replace `sorry` later):
1. Build `hA`:
   `∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      ∃ x : UnitSphereTwo, g x = g (-x)`.
2. Build `hR`:
   `(∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      ∃ x : UnitSphereTwo, g x = g (-x)) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        ∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1`.
3. Return `⟨hA, hR⟩` directly (no downstream packaging). -/
theorem helperForTheorem_6_8_independent_upstream_antipodal_and_reduction_bridge_in_part5_base_placeholder :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact
    helperForTheorem_6_8_independent_upstream_antipodal_and_reduction_bridge_in_part4_placeholder



/-- Independent upstream bridge for Theorem 6.8 exposed from `section06_part5`. -/
theorem helperForTheorem_6_8_independent_upstream_antipodal_and_reduction_bridge_in_part5 :
    (∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) ∧
    ((∀ g : UnitSphereTwo → EuclideanSpace ℝ (Fin 2), Continuous g →
      (∃ x : UnitSphereTwo, g x = g (-x))) →
      ∀ g : UnitSphereTwo → UnitSphereTwo, Continuous g →
        (∃ x : UnitSphereTwo, g x = x ∨ (g x).1 = -x.1)) := by
  exact helperForTheorem_6_8_independent_upstream_antipodal_and_reduction_bridge_in_part5_base_placeholder

end Section06
end Chap06
