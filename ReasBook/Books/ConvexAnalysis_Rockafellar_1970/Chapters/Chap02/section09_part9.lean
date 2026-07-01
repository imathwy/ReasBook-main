/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part10

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace

section Chap02
section Section09

/-- The relative interior of the effective domain of a finite sum is the intersection
of the relative interiors. -/
lemma ri_effectiveDomain_sum_eq_iInter
    {n m : Nat} {f : Fin m → (Fin n → Real) → EReal}
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i)) :
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let fSum : (Fin n → Real) → EReal := fun x => Finset.univ.sum (fun i => f i x)
    (⋂ i,
        euclideanRelativeInterior n
          (Set.image e.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)))).Nonempty →
    euclideanRelativeInterior n
        (Set.image e.symm (effectiveDomain (Set.univ : Set (Fin n → Real)) fSum)) =
      ⋂ i,
        euclideanRelativeInterior n
          (Set.image e.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i))) := by
  classical
  intro e fSum hri
  have hnotbot : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal) := by
    intro i x
    exact (hproper i).2.2 _ (by simp)
  have hdom :
      effectiveDomain (Set.univ : Set (Fin n → Real)) fSum =
        ⋂ i, effectiveDomain (Set.univ : Set (Fin n → Real)) (f i) :=
    effectiveDomain_sum_eq_iInter_univ (f := f) hnotbot
  have hconv_i :
      ∀ i,
        Convex Real
          (Set.image e.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i))) := by
    intro i
    have hconv_dom :
        Convex Real (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f i) (hproper i).1
    simpa using hconv_dom.linear_image (e.symm.toLinearMap)
  have himage :
      Set.image e.symm (effectiveDomain (Set.univ : Set (Fin n → Real)) fSum) =
        ⋂ i, Set.image e.symm
          (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)) := by
    calc
      Set.image e.symm (effectiveDomain (Set.univ : Set (Fin n → Real)) fSum) =
          Set.image e.symm (⋂ i, effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)) := by
        simp [hdom]
      _ = ⋂ i, Set.image e.symm
          (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)) := by
        simpa using
          (Set.image_iInter (f := e.symm)
            (s := fun i => effectiveDomain (Set.univ : Set (Fin n → Real)) (f i))
            (hf := e.symm.toLinearEquiv.bijective))
  calc
    euclideanRelativeInterior n
        (Set.image e.symm (effectiveDomain (Set.univ : Set (Fin n → Real)) fSum)) =
        euclideanRelativeInterior n
          (⋂ i, Set.image e.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i))) := by
      simp [himage]
    _ = ⋂ i,
        euclideanRelativeInterior n
          (Set.image e.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i))) := by
      simpa using
        (euclideanRelativeInterior_iInter_eq_iInter_relativeInterior_of_finite n
          (C := fun i =>
            Set.image e.symm
              (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)))
          (hC := hconv_i) (hri := hri))

/-- A finite sum of closed proper convex functions is closed. -/
lemma closedConvexFunction_sum_of_closed
    {n m : Nat} {f : Fin m → (Fin n → Real) → EReal}
    (hclosed : ∀ i : Fin m, ClosedConvexFunction (f i))
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i)) :
    ClosedConvexFunction (fun x => Finset.univ.sum (fun i => f i x)) := by
  classical
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x => Finset.univ.sum (fun i => f i x)) := by
    have hconv :=
      convexFunctionOn_linearCombination_of_proper (f := f) (lam := fun _ => (1 : Real))
        (hlam := by intro i; exact zero_le_one) (hf := hproper)
    simpa [one_mul] using hconv
  have hconv : ConvexFunction (fun x => Finset.univ.sum (fun i => f i x)) := by
    simpa [ConvexFunction] using hconv_on
  have hls_term : ∀ i : Fin m, LowerSemicontinuous (f i) := by
    intro i
    exact (hclosed i).2
  have hnotbot_term : ∀ i : Fin m, ∀ x, f i x ≠ (⊥ : EReal) := by
    intro i x
    exact (hproper i).2.2 _ (by simp)
  have hnotbot_sum' :
      ∀ s : Finset (Fin m), ∀ x, s.sum (fun i => f i x) ≠ (⊥ : EReal) := by
    intro s x
    refine finset_sum_ne_bot_of_forall (s := s) (f := fun i => f i x) ?_
    intro a ha
    exact hnotbot_term a x
  have hls :
      LowerSemicontinuous (fun x => Finset.univ.sum (fun i => f i x)) := by
    classical
    refine Finset.induction_on (s := (Finset.univ : Finset (Fin m))) ?_ ?_
    · simpa using
        (lowerSemicontinuous_const :
          LowerSemicontinuous (fun _ : Fin n → Real => (0 : EReal)))
    · intro a s ha hs
      have hls_a : LowerSemicontinuous (f a) := hls_term a
      have hcont :
          ∀ x,
            ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
              (f a x, s.sum (fun i => f i x)) := by
        intro x
        have hnotbot_a : f a x ≠ (⊥ : EReal) := hnotbot_term a x
        have hnotbot_s : s.sum (fun i => f i x) ≠ (⊥ : EReal) := hnotbot_sum' s x
        exact EReal.continuousAt_add (h := Or.inr hnotbot_s) (h' := Or.inl hnotbot_a)
      have hls_add :
          LowerSemicontinuous
            (fun x => f a x + s.sum (fun i => f i x)) :=
        LowerSemicontinuous.add' hls_a hs hcont
      simpa [Finset.sum_insert, ha] using hls_add
  exact ⟨hconv, hls⟩

/-- A finite sum of proper convex functions is proper if it is finite somewhere. -/
lemma properConvexFunctionOn_sum_of_exists_ne_top
    {n m : Nat} {f : Fin m → (Fin n → Real) → EReal}
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i))
    (hexists : ∃ x : Fin n → Real, Finset.univ.sum (fun i => f i x) ≠ (⊤ : EReal)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
      (fun x => Finset.univ.sum (fun i => f i x)) := by
  classical
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x => Finset.univ.sum (fun i => f i x)) := by
    have hconv :=
      convexFunctionOn_linearCombination_of_proper (f := f) (lam := fun _ => (1 : Real))
        (hlam := by intro i; exact zero_le_one) (hf := hproper)
    simpa [one_mul] using hconv
  have hnotbot_sum :
      ∀ x : Fin n → Real, Finset.univ.sum (fun i => f i x) ≠ (⊥ : EReal) := by
    intro x
    refine finset_sum_ne_bot_of_forall (s := (Finset.univ : Finset (Fin m)))
      (f := fun i => f i x) ?_
    intro a ha
    exact (hproper a).2.2 _ (by simp)
  have hne_dom :
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin n → Real))
          (fun x => Finset.univ.sum (fun i => f i x))) := by
    rcases hexists with ⟨x, hx⟩
    have hx_sum :
        Finset.univ.sum (fun i => f i x) < (⊤ : EReal) := (lt_top_iff_ne_top).2 hx
    refine ⟨x, ?_⟩
    have hx_dom :
        x ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧
          Finset.univ.sum (fun i => f i x) < (⊤ : EReal)} :=
      ⟨by simp, hx_sum⟩
    simpa [effectiveDomain_eq] using hx_dom
  refine
    (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
      (S := (Set.univ : Set (Fin n → Real)))
      (f := fun x => Finset.univ.sum (fun i => f i x))).2 ?_
  refine ⟨hconv_on, hne_dom, ?_⟩
  intro x hx
  have hbot : Finset.univ.sum (fun i => f i x) ≠ (⊥ : EReal) := hnotbot_sum x
  have htop :
      Finset.univ.sum (fun i => f i x) ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → Real)))
      (f := fun x => Finset.univ.sum (fun i => f i x)) (x := x) hx
  exact ⟨hbot, htop⟩

/-- Under a common relative-interior point, the closure of a finite sum is the sum of closures. -/
lemma convexFunctionClosure_sum_eq_sum_closure
    {n m : Nat} {f : Fin m → (Fin n → Real) → EReal}
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i)) :
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let fSum : (Fin n → Real) → EReal := fun x => Finset.univ.sum (fun i => f i x)
    (∃ x : EuclideanSpace Real (Fin n),
      ∀ i : Fin m,
        x ∈
          euclideanRelativeInterior n
            (Set.image e.symm
              (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)))) →
    convexFunctionClosure fSum =
      fun x => Finset.univ.sum (fun i => convexFunctionClosure (f i) x) := by
  classical
  intro e fSum hri
  rcases hri with ⟨x0, hx0⟩
  have hx0_inter :
      x0 ∈ ⋂ i,
        euclideanRelativeInterior n
          (Set.image e.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i))) := by
    refine Set.mem_iInter.2 ?_
    intro i
    exact hx0 i
  have hri_nonempty :
      (⋂ i,
          euclideanRelativeInterior n
            (Set.image e.symm
              (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)))).Nonempty :=
    ⟨x0, hx0_inter⟩
  have hri_eq :
      euclideanRelativeInterior n
          (Set.image e.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) fSum)) =
        ⋂ i,
          euclideanRelativeInterior n
            (Set.image e.symm
              (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i))) :=
    by
      simpa [e, fSum] using
        (ri_effectiveDomain_sum_eq_iInter (f := f) hproper) hri_nonempty
  have hx0_sum :
      x0 ∈
        euclideanRelativeInterior n
          (Set.image e.symm
            (effectiveDomain (Set.univ : Set (Fin n → Real)) fSum)) := by
    simpa [hri_eq] using hx0_inter
  have hx0_dom :
      ∀ i : Fin m, e x0 ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) (f i) := by
    intro i
    have hx0_mem :
        x0 ∈ Set.image e.symm
          (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)) :=
      (euclideanRelativeInterior_subset_closure n
        (Set.image e.symm
          (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)))).1 (hx0 i)
    rcases hx0_mem with ⟨y, hy, rfl⟩
    simpa using hy
  have hnot_top_term : ∀ i : Fin m, f i (e x0) ≠ (⊤ : EReal) := by
    intro i
    exact mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → Real))) (f := f i) (x := e x0) (hx0_dom i)
  have hnot_top_sum :
      fSum (e x0) ≠ (⊤ : EReal) := by
    have hsum_ne_top :
        Finset.univ.sum (fun i => f i (e x0)) ≠ (⊤ : EReal) := by
      refine finset_sum_ne_top_of_forall (s := (Finset.univ : Finset (Fin m)))
        (f := fun i => f i (e x0)) ?_
      intro a ha
      exact hnot_top_term a
    simpa [fSum] using hsum_ne_top
  have hproper_sum :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fSum := by
    have hexists : ∃ x : Fin n → Real, fSum x ≠ (⊤ : EReal) := ⟨e x0, hnot_top_sum⟩
    simpa [fSum] using
      (properConvexFunctionOn_sum_of_exists_ne_top (f := f) hproper hexists)
  funext y
  let yE : EuclideanSpace Real (Fin n) := e.symm y
  have hx0_sum' :
      x0 ∈
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) fSum) := by
    simpa [ContinuousLinearEquiv.image_symm_eq_preimage] using hx0_sum
  have hlim_sum :
      Filter.Tendsto
          (fun t : Real => fSum ((1 - t) • x0 + t • yE))
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
          (𝓝 (convexFunctionClosure fSum y)) :=
    by
      have hlim :=
        (convexFunctionClosure_eq_limit_along_segment (f := fSum) (x := x0) hx0_sum').1
          hproper_sum yE
      simpa [yE, e] using hlim
  have hlim_i :
      ∀ i : Fin m,
        Filter.Tendsto
            (fun t : Real => f i ((1 - t) • x0 + t • yE))
            (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
            (𝓝 (convexFunctionClosure (f i) y)) := by
    intro i
    have hx0_i :
        x0 ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)) := by
      simpa [ContinuousLinearEquiv.image_symm_eq_preimage] using hx0 i
    have hlim :=
      (convexFunctionClosure_eq_limit_along_segment (f := f i) (x := x0) hx0_i).1
        (hproper i) yE
    simpa [yE, e] using hlim
  have hnotbot_closure :
      ∀ i : Fin m, convexFunctionClosure (f i) y ≠ (⊥ : EReal) := by
    intro i
    have hproper_cl :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
          (convexFunctionClosure (f i)) :=
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := f i) (hproper i)).1.2
    exact hproper_cl.2.2 y (by simp)
  have hnotbot_sum_closure :
      ∀ s : Finset (Fin m),
        s.sum (fun i => convexFunctionClosure (f i) y) ≠ (⊥ : EReal) := by
    intro s
    refine finset_sum_ne_bot_of_forall (s := s)
      (f := fun i => convexFunctionClosure (f i) y) ?_
    intro a ha
    exact hnotbot_closure a
  have hlim_sum' :
      Filter.Tendsto
          (fun t : Real =>
            Finset.univ.sum (fun i => f i ((1 - t) • x0 + t • yE)))
          (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
          (𝓝 (Finset.univ.sum (fun i => convexFunctionClosure (f i) y))) := by
    classical
    refine Finset.induction_on (s := (Finset.univ : Finset (Fin m))) ?_ ?_
    · simp
    · intro a s ha hs
      have hcont :
          ContinuousAt (fun p : EReal × EReal => p.1 + p.2)
            (convexFunctionClosure (f a) y,
              s.sum (fun i => convexFunctionClosure (f i) y)) := by
        have hnotbot_a : convexFunctionClosure (f a) y ≠ (⊥ : EReal) := hnotbot_closure a
        have hnotbot_s :
            s.sum (fun i => convexFunctionClosure (f i) y) ≠ (⊥ : EReal) :=
          hnotbot_sum_closure s
        exact EReal.continuousAt_add (h := Or.inr hnotbot_s) (h' := Or.inl hnotbot_a)
      have hpair :
          Filter.Tendsto
              (fun t : Real =>
                (f a ((1 - t) • x0 + t • yE),
                  s.sum (fun i => f i ((1 - t) • x0 + t • yE))))
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
              (𝓝 (convexFunctionClosure (f a) y,
                s.sum (fun i => convexFunctionClosure (f i) y))) := by
        simpa [nhds_prod_eq] using (hlim_i a).prodMk hs
      have hsum :
          Filter.Tendsto
              (fun t : Real =>
                f a ((1 - t) • x0 + t • yE) +
                  s.sum (fun i => f i ((1 - t) • x0 + t • yE)))
              (nhdsWithin (1 : Real) (Set.Iio (1 : Real)))
              (𝓝 (convexFunctionClosure (f a) y +
                s.sum (fun i => convexFunctionClosure (f i) y))) :=
        by
          simpa [Function.comp] using hcont.tendsto.comp hpair
      simpa [Finset.sum_insert, ha] using hsum
  have hEq :
      convexFunctionClosure fSum y =
        Finset.univ.sum (fun i => convexFunctionClosure (f i) y) :=
    tendsto_nhds_unique hlim_sum (by simpa [fSum] using hlim_sum')
  exact hEq

/-- Theorem 9.3. Let `f₁, …, fₘ` be proper convex functions on `ℝ^n`. If every `f_i` is
closed and `f₁ + ··· + fₘ` is not identically `+∞`, then the sum is a closed proper convex
function and `(f₁ + ··· + fₘ)0^+ = f₁ 0^+ + ··· + fₘ 0^+`. If the `f_i` are not all closed,
but there exists a point common to every `ri (dom f_i)`, then
`cl (f₁ + ··· + fₘ) = cl f₁ + ··· + cl fₘ`. -/
theorem sum_closed_proper_convex_recession_and_closure
    {n m : Nat} {f f0_plus : Fin m → (Fin n → Real) → EReal}
    (hproper : ∀ i : Fin m, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i)) :
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let fSum : (Fin n → Real) → EReal := fun x => Finset.univ.sum (fun i => f i x)
    let fSum0_plus : (Fin n → Real) → EReal := fun y => Finset.univ.sum (fun i => f0_plus i y)
    ((∀ i : Fin m, ClosedConvexFunction (f i)) →
        (∃ x : Fin n → Real, fSum x ≠ (⊤ : EReal)) →
        ClosedConvexFunction fSum ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fSum ∧
          fSum0_plus = fun y => Finset.univ.sum (fun i => f0_plus i y)) ∧
      ((∃ x : EuclideanSpace Real (Fin n),
          ∀ i : Fin m,
            x ∈
              euclideanRelativeInterior n
                (Set.image e.symm
                  (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)))) →
        convexFunctionClosure fSum =
          fun x => Finset.univ.sum (fun i => convexFunctionClosure (f i) x)) := by
  classical
  intro e fSum fSum0_plus
  constructor
  · intro hclosed hfinite
    have hclosed_sum : ClosedConvexFunction fSum := by
      simpa [fSum] using
        (closedConvexFunction_sum_of_closed (f := f) hclosed hproper)
    have hproper_sum : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fSum := by
      simpa [fSum] using
        (properConvexFunctionOn_sum_of_exists_ne_top (f := f) hproper hfinite)
    refine ⟨hclosed_sum, hproper_sum, ?_⟩
    rfl
  · intro hri
    simpa [e, fSum] using
      (convexFunctionClosure_sum_eq_sum_closure (f := f) hproper hri)

/-- The pointwise supremum of closed convex functions is closed. -/
lemma closedConvexFunction_iSup_of_closed
    {n : Nat} {I : Type _} {f : I → (Fin n → Real) → EReal}
    (hclosed : ∀ i, ClosedConvexFunction (f i)) :
    ClosedConvexFunction (fun x => iSup (fun i => f i x)) := by
  classical
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x => iSup (fun i => f i x)) := by
    refine convexFunctionOn_iSup (f := f) ?_
    intro i
    simpa [ConvexFunction] using (hclosed i).1
  have hconv : ConvexFunction (fun x => iSup (fun i => f i x)) := by
    simpa [ConvexFunction] using hconv_on
  have hls :
      LowerSemicontinuous (fun x => iSup (fun i => f i x)) := by
    refine lowerSemicontinuous_iSup ?_
    intro i
    exact (hclosed i).2
  exact ⟨hconv, hls⟩

/-- A pointwise supremum of proper convex functions is proper if it is finite somewhere. -/
lemma properConvexFunctionOn_iSup_of_exists
    {n : Nat} {I : Type _} {f : I → (Fin n → Real) → EReal}
    (hproper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i)) :
    let fSup : (Fin n → Real) → EReal := fun x => iSup (fun i => f i x)
    (∃ x : Fin n → Real, fSup x ≠ (⊤ : EReal) ∧ fSup x ≠ (⊥ : EReal)) →
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fSup := by
  classical
  intro fSup hexists
  rcases hexists with ⟨x0, hx0_top, hx0_bot⟩
  have hconv_on :
      ConvexFunctionOn (Set.univ : Set (Fin n → Real)) fSup := by
    simpa [fSup] using
      (convexFunctionOn_iSup (f := f) (hf := fun i => (hproper i).1))
  have hI : Nonempty I := by
    by_contra hI
    have hI' : IsEmpty I := not_nonempty_iff.mp hI
    haveI := hI'
    have hbot : fSup x0 = (⊥ : EReal) := by
      simp [fSup]
    exact hx0_bot hbot
  obtain ⟨i0⟩ := hI
  have hnotbot : ∀ x : Fin n → Real, fSup x ≠ (⊥ : EReal) := by
    intro x hbot
    have hle : f i0 x ≤ fSup x := le_iSup (fun i => f i x) i0
    have hle' : f i0 x ≤ (⊥ : EReal) := by
      simpa [hbot] using hle
    have hbot_i0 : f i0 x = (⊥ : EReal) := le_antisymm hle' bot_le
    exact (hproper i0).2.2 x (by simp) hbot_i0
  have hne_dom :
      Set.Nonempty
        (effectiveDomain (Set.univ : Set (Fin n → Real)) fSup) := by
    have hxlt : fSup x0 < (⊤ : EReal) := (lt_top_iff_ne_top).2 hx0_top
    refine ⟨x0, ?_⟩
    have hx_dom :
        x0 ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ fSup x < (⊤ : EReal)} :=
      ⟨by simp, hxlt⟩
    simpa [effectiveDomain_eq] using hx_dom
  refine
    (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
      (S := (Set.univ : Set (Fin n → Real))) (f := fSup)).2 ?_
  refine ⟨hconv_on, hne_dom, ?_⟩
  intro x hx
  have hbot : fSup x ≠ (⊥ : EReal) := hnotbot x
  have htop :
      fSup x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top
      (S := (Set.univ : Set (Fin n → Real))) (f := fSup) (x := x) hx
  exact ⟨hbot, htop⟩

/-- A common relative-interior point yields a point in all `ri (epi f i)` above the supremum. -/
lemma mem_iInter_riEpigraph_of_common_ri_dom
    {n : Nat} {I : Type _} {f : I → (Fin n → Real) → EReal}
    (hconv : ∀ i : I, ConvexFunction (f i)) :
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let fSup : (Fin n → Real) → EReal := fun x => iSup (fun i => f i x)
    ∀ {x0 : EuclideanSpace Real (Fin n)},
      (∀ i : I,
        x0 ∈
          euclideanRelativeInterior n
            (Set.image e.symm
              (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)))) →
      fSup (e.symm x0) ≠ (⊤ : EReal) →
      fSup (e.symm x0) ≠ (⊥ : EReal) →
      (appendAffineEquiv n 1
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0),
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
              (fun _ : Fin 1 => (fSup (e.symm x0)).toReal + 1)))
        ∈ ⋂ i, riEpigraph (f i) := by
  classical
  intro e fSup x0 hx0 htop hbot
  have htop' : fSup ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0) ≠ (⊤ : EReal) := by
    simpa using htop
  have hbot' : fSup ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0) ≠ (⊥ : EReal) := by
    simpa using hbot
  set μ : Real := (fSup ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0)).toReal + 1
  have hle_sup :
      fSup ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0) ≤
        (fSup ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0)).toReal := by
    exact EReal.le_coe_toReal htop'
  have hlt_real :
      (fSup ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0)).toReal < μ := by
    simp [μ]
  have hlt_coe :
      ((fSup ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0)).toReal : EReal) <
        (μ : EReal) := by
    exact (EReal.coe_lt_coe_iff).2 hlt_real
  have hlt_sup :
      fSup ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0) < (μ : EReal) :=
    lt_of_le_of_lt hle_sup hlt_coe
  have hx0_pre :
      ∀ i : I,
        x0 ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)) := by
    intro i
    simpa [ContinuousLinearEquiv.image_symm_eq_preimage] using hx0 i
  have hmem_i :
      ∀ i : I,
        (appendAffineEquiv n 1
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0),
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => μ))) ∈ riEpigraph (f i) := by
    intro i
    have hxri :
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0) ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)) := by
      simpa using (hx0_pre i)
    have hle_i :
        f i ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0) ≤
          fSup ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0) :=
      le_iSup (fun j => f j ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0)) i
    have hlt_i :
        f i ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0) < (μ : EReal) :=
      lt_of_le_of_lt hle_i hlt_sup
    exact
      (riEpigraph_mem_iff (n := n) (f := f i) (hconv i)
        (x := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0) (μ := μ)).2
        ⟨hxri, hlt_i, riEpigraph_mu_lt_top μ⟩
  exact Set.mem_iInter.2 hmem_i

/-- Theorem 9.4. Let `f_i` be a proper convex function on `ℝ^n` for `i ∈ I`, and let
`f = sup { f_i | i ∈ I }`. If `f` is finite somewhere and every `f_i` is closed, then
`f` is closed and proper and `f0^+ = sup { f_i0^+ | i ∈ I }`. If the `f_i` are not all
closed, but there exists a point common to every `ri (dom f_i)` such that `f` is finite
there, then `cl f = sup { cl f_i | i ∈ I }`. -/
theorem iSup_closed_proper_convex_recession_and_closure
    {n : Nat} {I : Type _} {f f0_plus : I → (Fin n → Real) → EReal}
    (hproper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (f i)) :
    let e := (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n))
    let fSup : (Fin n → Real) → EReal := fun x => iSup (fun i => f i x)
    let fSup0_plus : (Fin n → Real) → EReal := fun y => iSup (fun i => f0_plus i y)
    ((∀ i : I, ClosedConvexFunction (f i)) →
        (∃ x : Fin n → Real, fSup x ≠ (⊤ : EReal) ∧ fSup x ≠ (⊥ : EReal)) →
        ClosedConvexFunction fSup ∧
          ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fSup ∧
          fSup0_plus = fun y => iSup (fun i => f0_plus i y)) ∧
      ((∃ x : EuclideanSpace Real (Fin n),
          (∀ i : I,
            x ∈
              euclideanRelativeInterior n
                (Set.image e.symm
                  (effectiveDomain (Set.univ : Set (Fin n → Real)) (f i)))) ∧
          fSup (e.symm x) ≠ (⊤ : EReal) ∧ fSup (e.symm x) ≠ (⊥ : EReal)) →
        convexFunctionClosure fSup =
          fun x => iSup (fun i => convexFunctionClosure (f i) x)) := by
  classical
  intro e fSup fSup0_plus
  constructor
  · intro hclosed hfinite
    have hclosed_sup : ClosedConvexFunction fSup := by
      simpa [fSup] using
        (closedConvexFunction_iSup_of_closed (f := f) hclosed)
    have hproper_sup :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) fSup := by
      simpa [fSup] using
        (properConvexFunctionOn_iSup_of_exists (f := f) hproper hfinite)
    refine ⟨hclosed_sup, hproper_sup, ?_⟩
    rfl
  · intro hri
    rcases hri with ⟨x0, hx0, hx0_top, hx0_bot⟩
    have hconv_i : ∀ i : I, ConvexFunction (f i) := by
      intro i
      simpa [ConvexFunction] using (hproper i).1
    have hI : Nonempty I := by
      by_contra hI
      have hI' : IsEmpty I := not_nonempty_iff.mp hI
      haveI := hI'
      have hbot : fSup (e.symm x0) = (⊥ : EReal) := by
        simp [fSup]
      exact hx0_bot hbot
    obtain ⟨i0⟩ := hI
    have hnotbot_fSup : ∀ x : Fin n → Real, fSup x ≠ (⊥ : EReal) := by
      intro x hbot
      have hle : f i0 x ≤ fSup x := le_iSup (fun i => f i x) i0
      have hle' : f i0 x ≤ (⊥ : EReal) := by
        simpa [hbot] using hle
      have hbot_i0 : f i0 x = (⊥ : EReal) := le_antisymm hle' bot_le
      exact (hproper i0).2.2 x (by simp) hbot_i0
    let g : (Fin n → Real) → EReal :=
      fun x => iSup (fun i => convexFunctionClosure (f i) x)
    have hclosed_g : ClosedConvexFunction g := by
      have hclosed_i :
          ∀ i : I, ClosedConvexFunction (convexFunctionClosure (f i)) := by
        intro i
        exact
          (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
            (f := f i) (hproper i)).1.1
      simpa [g] using (closedConvexFunction_iSup_of_closed (f := fun i => convexFunctionClosure (f i)) hclosed_i)
    have hnotbot_g : ∀ x : Fin n → Real, g x ≠ (⊥ : EReal) := by
      intro x hbot
      have hproper_cl :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
            (convexFunctionClosure (f i0)) :=
        (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
          (f := f i0) (hproper i0)).1.2
      have hle : convexFunctionClosure (f i0) x ≤ g x := by
        exact le_iSup (fun i => convexFunctionClosure (f i) x) i0
      have hle' : convexFunctionClosure (f i0) x ≤ (⊥ : EReal) := by
        simpa [hbot] using hle
      have hbot_i0 : convexFunctionClosure (f i0) x = (⊥ : EReal) :=
        le_antisymm hle' bot_le
      exact hproper_cl.2.2 x (by simp) hbot_i0
    have hri_point :
        (⋂ i : I, riEpigraph (f i)).Nonempty := by
      refine ⟨?_, ?_⟩
      · exact
          (appendAffineEquiv n 1
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm
                ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) x0),
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => (fSup (e.symm x0)).toReal + 1)))
      ·
        exact
          (mem_iInter_riEpigraph_of_common_ri_dom (f := f) hconv_i
            (x0 := x0) hx0 hx0_top hx0_bot)
    -- embedded epigraph sets
    let C : I → Set (EuclideanSpace Real (Fin (n + 1))) := fun i =>
      (appendAffineEquiv n 1) ''
        ((fun p : (Fin n → Real) × Real =>
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
              (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm
                (fun _ : Fin 1 => p.2))) ''
          epigraph (S := (Set.univ : Set (Fin n → Real))) (f i))
    let ψ :
        (Fin n → Real) × Real →
          EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1) := fun p =>
      ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm p.1,
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm (fun _ : Fin 1 => p.2))
    let φ : (Fin n → Real) × Real → EuclideanSpace Real (Fin (n + 1)) :=
      fun p => (appendAffineEquiv n 1) (ψ p)
    have hC_eq :
        ∀ i : I,
          C i =
            φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) := by
      intro i
      simpa [C, φ, ψ, Function.comp] using
        (Set.image_image (f := ψ) (g := appendAffineEquiv n 1)
          (s := epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)))
    have hconv_C : ∀ i : I, Convex Real (C i) := by
      intro i
      simpa [C] using
        (convex_embedded_epigraph (n := n) (f := f i) (hconv_i i))
    have hbij_phi : Function.Bijective φ := by
      -- composition of affine equivalences is bijective
      let eN : (Fin n → Real) ≃ᵃ[Real] EuclideanSpace Real (Fin n) :=
        (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm.toLinearEquiv.toAffineEquiv
      let e1 : Real ≃ᵃ[Real] EuclideanSpace Real (Fin 1) :=
        ((ContinuousLinearEquiv.funUnique (ι := Fin 1) (R := Real) (M := Real)).symm.toLinearEquiv.trans
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)).symm.toLinearEquiv).toAffineEquiv
      let g_aff :
          (Fin n → Real) × Real ≃ᵃ[Real]
            (EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin 1)) :=
        AffineEquiv.prodCongr eN e1
      have hbij_g : Function.Bijective (fun p => (appendAffineEquiv n 1) (g_aff p)) :=
        (appendAffineEquiv n 1).bijective.comp g_aff.bijective
      exact hbij_g
    have hphi_image :
        ∀ s : Set ((Fin n → Real) × Real),
          (appendAffineEquiv n 1) '' (ψ '' s) = φ '' s := by
      intro s
      simpa [φ, Function.comp] using
        (Set.image_image (f := ψ) (g := appendAffineEquiv n 1) (s := s))
    have hcl_iInter :
        closure (⋂ i, C i) = ⋂ i, closure (C i) :=
      euclidean_closure_iInter_eq_iInter_closure_of_common_relativeInterior
        (n := n + 1) (I := I) (C := C) hconv_C hri_point
    have hC_iInter :
        (⋂ i, C i) =
          φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) fSup := by
      have himage :
          φ '' (⋂ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) =
            ⋂ i, φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) := by
        simpa [φ] using
          (Set.image_iInter (f := φ)
            (s := fun i => epigraph (S := (Set.univ : Set (Fin n → Real))) (f i))
            (hf := hbij_phi))
      have hsup :
          epigraph (S := (Set.univ : Set (Fin n → Real))) fSup =
            ⋂ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) := by
        simpa [fSup] using (epigraph_iSup_eq_iInter_univ (f := f))
      have hC_iInter' :
          (⋂ i, C i) = ⋂ i, φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) := by
        refine Set.iInter_congr ?_
        intro i
        exact (hC_eq i)
      calc
        (⋂ i, C i) = ⋂ i, φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) (f i) :=
          hC_iInter'
        _ = φ '' (⋂ i, epigraph (S := (Set.univ : Set (Fin n → Real))) (f i)) := by
          symm
          exact himage
        _ = φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) fSup := by
          simp [hsup]
    have hcl_C :
        closure (⋂ i, C i) =
          φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
      have hnotbot_i : ∀ i : I, ∀ x, f i x ≠ (⊥ : EReal) := by
        intro i x
        exact (hproper i).2.2 x (by simp)
      have hcl_i :
          ∀ i : I,
            closure (C i) =
              φ '' epigraph (S := (Set.univ : Set (Fin n → Real)))
                (convexFunctionClosure (f i)) := by
        intro i
        have hcl_i' :
            closure (C i) =
              (appendAffineEquiv n 1) ''
                (ψ '' epigraph (S := (Set.univ : Set (Fin n → Real)))
                  (convexFunctionClosure (f i))) := by
          simpa [C] using
            (closure_embedded_epigraph_eq_convexFunctionClosure (n := n) (f := f i)
              (hnotbot_i i))
        calc
          closure (C i) =
              (appendAffineEquiv n 1) ''
                (ψ '' epigraph (S := (Set.univ : Set (Fin n → Real)))
                  (convexFunctionClosure (f i))) := by
            exact hcl_i'
          _ =
              φ '' epigraph (S := (Set.univ : Set (Fin n → Real)))
                (convexFunctionClosure (f i)) := by
            simpa using
              (hphi_image
                (s := epigraph (S := (Set.univ : Set (Fin n → Real)))
                  (convexFunctionClosure (f i))))
      have hcl_iInter' :
          (⋂ i, closure (C i)) =
            ⋂ i, φ '' epigraph (S := (Set.univ : Set (Fin n → Real)))
              (convexFunctionClosure (f i)) := by
        refine Set.iInter_congr ?_
        intro i
        exact (hcl_i i)
      have hC_iInter' :
          (⋂ i, φ '' epigraph (S := (Set.univ : Set (Fin n → Real)))
            (convexFunctionClosure (f i))) =
            φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
        have himage :
            φ '' (⋂ i,
              epigraph (S := (Set.univ : Set (Fin n → Real)))
                (convexFunctionClosure (f i))) =
              ⋂ i, φ '' epigraph (S := (Set.univ : Set (Fin n → Real)))
                (convexFunctionClosure (f i)) := by
          simpa [φ] using
            (Set.image_iInter (f := φ)
              (s := fun i =>
                epigraph (S := (Set.univ : Set (Fin n → Real)))
                  (convexFunctionClosure (f i)))
              (hf := hbij_phi))
        have hsup :
            epigraph (S := (Set.univ : Set (Fin n → Real))) g =
              ⋂ i,
                epigraph (S := (Set.univ : Set (Fin n → Real)))
                  (convexFunctionClosure (f i)) := by
          simpa [g] using
            (epigraph_iSup_eq_iInter_univ (f := fun i => convexFunctionClosure (f i)))
        calc
          (⋂ i, φ '' epigraph (S := (Set.univ : Set (Fin n → Real)))
              (convexFunctionClosure (f i))) =
              φ '' (⋂ i,
                epigraph (S := (Set.univ : Set (Fin n → Real)))
                  (convexFunctionClosure (f i))) := by
            symm
            exact himage
          _ = φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
            simp [hsup]
      calc
        closure (⋂ i, C i) = ⋂ i, closure (C i) := hcl_iInter
        _ = ⋂ i, φ '' epigraph (S := (Set.univ : Set (Fin n → Real)))
            (convexFunctionClosure (f i)) := hcl_iInter'
        _ = φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g := hC_iInter'
    have hcl_embedded :
        closure (φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) fSup) =
          closure (φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
      have hcl_fSup :
          closure (φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) fSup) =
            closure (⋂ i, C i) := by
        simp [hC_iInter]
      have hcl_g :
          closure (φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g) =
            φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
        have hbot_g : ∀ x, g x ≠ (⊥ : EReal) := hnotbot_g
        have hcl_g' :=
          (closure_embedded_epigraph_eq_convexFunctionClosure (n := n) (f := g) hbot_g)
        have hconv_cl : convexFunctionClosure g = g := by
          exact convexFunctionClosure_eq_of_closedConvexFunction (f := g) hclosed_g hbot_g
        have hcl_g'' :
            closure
                ((appendAffineEquiv n 1) ''
                  (ψ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g)) =
              (appendAffineEquiv n 1) ''
                (ψ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
          simpa [hconv_cl] using hcl_g'
        have hphi_g :
            (appendAffineEquiv n 1) ''
                (ψ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g) =
              φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
          simpa using
            (hphi_image
              (s := epigraph (S := (Set.univ : Set (Fin n → Real))) g))
        simpa [hphi_g] using hcl_g''
      calc
        closure (φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) fSup) =
            closure (⋂ i, C i) := hcl_fSup
        _ = φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g := hcl_C
        _ = closure (φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
            symm
            exact hcl_g
    have hcl_epi :
        closure (epigraph (S := (Set.univ : Set (Fin n → Real))) fSup) =
          closure (epigraph (S := (Set.univ : Set (Fin n → Real))) g) := by
      have hphi_fSup :
          (appendAffineEquiv n 1) ''
              (ψ '' epigraph (S := (Set.univ : Set (Fin n → Real))) fSup) =
            φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) fSup := by
        simpa [φ, Function.comp] using
          (Set.image_image (f := ψ) (g := appendAffineEquiv n 1)
            (s := epigraph (S := (Set.univ : Set (Fin n → Real))) fSup))
      have hphi_g :
          (appendAffineEquiv n 1) ''
              (ψ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g) =
            φ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g := by
        simpa [φ, Function.comp] using
          (Set.image_image (f := ψ) (g := appendAffineEquiv n 1)
            (s := epigraph (S := (Set.univ : Set (Fin n → Real))) g))
      have hcl_embedded' :
          closure
              ((appendAffineEquiv n 1) ''
                (ψ '' epigraph (S := (Set.univ : Set (Fin n → Real))) fSup)) =
            closure
              ((appendAffineEquiv n 1) ''
                (ψ '' epigraph (S := (Set.univ : Set (Fin n → Real))) g)) := by
        simpa [hphi_fSup, hphi_g] using hcl_embedded
      exact
        (closure_epigraph_eq_of_embedded_closure_eq (n := n) (f := fSup) (g := g)
          hcl_embedded')
    have hEq :
        convexFunctionClosure fSup = g := by
      have hcf :
          convexFunctionClosure fSup = convexFunctionClosure g := by
        exact
          (convexFunctionClosure_eq_of_epigraph_closure_eq (n := n) (f := fSup) (g := g)
            hnotbot_fSup hnotbot_g hcl_epi)
      have hcg : convexFunctionClosure g = g := by
        exact convexFunctionClosure_eq_of_closedConvexFunction (f := g) hclosed_g hnotbot_g
      simpa [hcg] using hcf
    simpa [g] using hEq

end Section09
end Chap02
