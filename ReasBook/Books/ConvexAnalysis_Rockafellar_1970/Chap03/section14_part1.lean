/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section08_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section08_part2

section Chap03
section Section14

open scoped Pointwise
open scoped Topology
open scoped RealInnerProductSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

-- The weak topology on the algebraic dual induced by evaluation (see `section14_part3`).
noncomputable local instance section14_instTopologicalSpace_dualWeak_part1 :
    TopologicalSpace (Module.Dual ℝ E) :=
  WeakBilin.instTopologicalSpace
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

/-- Text 14.0.1: The polar of a non-empty convex cone `K` is the set
`Kᵒ = {x★ | ∀ x ∈ K, ⟪x, x★⟫ ≤ 0}`.

In this formalization, we interpret `x★` as a linear functional `Module.Dual ℝ E`
and the pairing `⟪x, x★⟫` as evaluation `x★ x`. -/
def polarCone (K : Set E) : Set (Module.Dual ℝ E) :=
  (PointedCone.dual (R := ℝ) (-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) K : Set _)

/-- The barrier cone of a set `C` is the set of all linear functionals `φ` that are bounded above
on `C`, i.e. there exists `β` with `φ x ≤ β` for every `x ∈ C`. -/
def Set.barrierCone (C : Set E) : Set (Module.Dual ℝ E) :=
  {φ : Module.Dual ℝ E | ∃ β : ℝ, ∀ x ∈ C, φ x ≤ β}

/-- An `EReal`-valued indicator function: `0` on a set and `⊤` off it. -/
noncomputable def erealIndicator (K : Set E) : E → EReal := by
  classical
  exact fun x => if x ∈ K then 0 else ⊤

/-- The (Fenchel–Legendre) conjugate of an `EReal`-valued function with respect to a bilinear
pairing `p`, defined as `sup_x (p x y - f x)`. -/
noncomputable def fenchelConjugateBilin {F : Type*} [AddCommGroup F] [Module ℝ F]
    (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) : F → EReal :=
  fun y => sSup (Set.range fun x => (p x y : EReal) - f x)

/-- Membership in the dual cone `ProperCone.dual (-p) K` is exactly the inequality
`p x y ≤ 0` for all `x ∈ K`. -/
lemma mem_dual_neg_iff {F : Type*}
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [Module ℝ F]
    [ContinuousSMul ℝ F]
    (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [(-p).IsContPerfPair] (K : ProperCone ℝ E) {y : F} :
    y ∈ ProperCone.dual (-p) (K : Set E) ↔ ∀ x ∈ (K : Set E), p x y ≤ 0 := by
  constructor
  · intro hy x hx
    have hneg : 0 ≤ (-p) x y := hy hx
    have hneg' : 0 ≤ -(p x y) := by simpa using hneg
    exact (neg_nonneg).1 hneg'
  · intro hy x hx
    have h : p x y ≤ 0 := hy x hx
    have hneg : 0 ≤ -(p x y) := (neg_nonneg).2 h
    simpa using hneg

/-- The Fenchel conjugate of the `EReal`-indicator of a cone is `0` at points in the dual cone. -/
lemma fenchelConjugate_erealIndicator_eq_zero_of_mem_dual {F : Type*}
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [Module ℝ F]
    [ContinuousSMul ℝ F]
    (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [(-p).IsContPerfPair] (K : ProperCone ℝ E) {y : F}
    (hy : y ∈ ProperCone.dual (-p) (K : Set E)) :
    fenchelConjugateBilin p (erealIndicator (K : Set E)) y = 0 := by
  classical
  unfold fenchelConjugateBilin
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ (K : Set E)
    · have hpy : p x y ≤ 0 := (mem_dual_neg_iff (p := p) K).1 hy x hx
      have hpy' : (p x y : EReal) ≤ (0 : EReal) := EReal.coe_le_coe hpy
      simpa [erealIndicator, hx] using hpy'
    · simp [erealIndicator, hx]
  · refine le_sSup ?_
    refine ⟨0, ?_⟩
    simp [erealIndicator]

/-- The Fenchel conjugate of the `EReal`-indicator of a cone is `⊤` at points outside the dual
cone. -/
lemma fenchelConjugate_erealIndicator_eq_top_of_not_mem_dual {F : Type*}
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [Module ℝ F]
    [ContinuousSMul ℝ F]
    (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [(-p).IsContPerfPair] (K : ProperCone ℝ E) {y : F}
    (hy : y ∉ ProperCone.dual (-p) (K : Set E)) :
    fenchelConjugateBilin p (erealIndicator (K : Set E)) y = ⊤ := by
  classical
  have hy' : ¬ ∀ x, x ∈ (K : Set E) → p x y ≤ 0 := by
    intro h
    exact hy <| (mem_dual_neg_iff (p := p) K).2 (by intro x hx; exact h x hx)
  push_neg at hy'
  rcases hy' with ⟨x₀, hx₀K, hx₀pos⟩
  unfold fenchelConjugateBilin
  refine (sSup_eq_top).2 ?_
  intro b hb
  -- `b < ⊤` means `b` is either `⊥` or a real number
  induction b using EReal.rec with
  | bot =>
      refine ⟨(0 : EReal), ⟨0, by simp [erealIndicator]⟩, by simp⟩
  | coe r =>
      obtain ⟨n : ℕ, hn⟩ : ∃ n : ℕ, r / (p x₀ y) < n := exists_nat_gt (r / (p x₀ y))
      have hr : r < (n : ℝ) * p x₀ y := by
        have : r / (p x₀ y) < (n : ℝ) := by simpa using hn
        exact (div_lt_iff₀ hx₀pos).1 this
      have hxmem : ((n : ℝ) • x₀) ∈ (K : Set E) :=
        K.smul_mem hx₀K (by exact_mod_cast (Nat.cast_nonneg n))
      refine ⟨(p ((n : ℝ) • x₀) y : EReal) - erealIndicator (K : Set E) ((n : ℝ) • x₀), ?_, ?_⟩
      · exact ⟨(n : ℝ) • x₀, rfl⟩
      · have : (r : EReal) < ((n : ℝ) * p x₀ y : EReal) := EReal.coe_lt_coe hr
        simpa [erealIndicator, hxmem, mul_assoc] using this
  | top =>
      cases (lt_irrefl (⊤ : EReal) hb)

/-- The Fenchel conjugate of the `EReal`-indicator of a proper cone is the indicator of the dual
cone. -/
lemma fenchelConjugate_erealIndicator_properCone {F : Type*}
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [Module ℝ F]
    [ContinuousSMul ℝ F]
    (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [(-p).IsContPerfPair] (K : ProperCone ℝ E) :
    fenchelConjugateBilin p (erealIndicator (K : Set E)) =
      erealIndicator (ProperCone.dual (-p) (K : Set E) : Set F) := by
  classical
  funext y
  by_cases hy : y ∈ ProperCone.dual (-p) (K : Set E)
  · simpa [erealIndicator, hy] using
      (fenchelConjugate_erealIndicator_eq_zero_of_mem_dual (p := p) K (y := y) hy)
  · simpa [erealIndicator, hy] using
      (fenchelConjugate_erealIndicator_eq_top_of_not_mem_dual (p := p) K (y := y) hy)

/-- Theorem 14.1: If `K` is a non-empty closed convex cone, then its polar `Kᵒ` is also a non-empty
closed convex cone and the bipolar identity `Kᵒᵒ = K` holds. Moreover, the indicator functions of
`K` and `Kᵒ` are Fenchel–Legendre conjugates of each other. -/
theorem polarCone_polar_polar_eq_and_indicator_conjugate {F : Type*}
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F]
    [Module ℝ F] [ContinuousSMul ℝ F]
    (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [(-p).IsContPerfPair] (K : ProperCone ℝ E) :
    ((ProperCone.dual (-p) (K : Set E) : Set F).Nonempty ∧
        IsClosed (ProperCone.dual (-p) (K : Set E) : Set F) ∧
        Convex ℝ (ProperCone.dual (-p) (K : Set E) : Set F)) ∧
      ProperCone.dual (-p).flip (ProperCone.dual (-p) (K : Set E) : Set F) = K ∧
      fenchelConjugateBilin p (erealIndicator (K : Set E)) =
          erealIndicator (ProperCone.dual (-p) (K : Set E) : Set F) ∧
        fenchelConjugateBilin p.flip
            (erealIndicator (ProperCone.dual (-p) (K : Set E) : Set F)) =
          erealIndicator (K : Set E) := by
  refine ⟨?_, ?_⟩
  · refine ⟨(ProperCone.dual (-p) (K : Set E)).nonempty, ?_, ?_⟩
    · simpa using (ProperCone.dual (-p) (K : Set E)).isClosed
    · simpa using (ProperCone.dual (-p) (K : Set E)).convex
  · refine ⟨?_, ?_⟩
    · simp
    · refine ⟨?_, ?_⟩
      · simpa using (fenchelConjugate_erealIndicator_properCone (p := p) K)
      ·
        haveI : (-p.flip).IsContPerfPair := by
          simpa using (inferInstance : (-p).flip.IsContPerfPair)
        have h :=
          (fenchelConjugate_erealIndicator_properCone (E := F) (F := E) (p := p.flip)
              (K := ProperCone.dual (-p) (K : Set E)))
        have hdual :
            ProperCone.dual (-p.flip) (ProperCone.dual (-p) (K : Set E) : Set F) = K := by
          change
            ProperCone.dual (-p).flip (ProperCone.dual (-p) (K : Set E) : Set F) = K
          exact ProperCone.dual_flip_dual (p := (-p)) (C := K)
        have hdualSet :
            (ProperCone.dual (-p.flip) (ProperCone.dual (-p) (K : Set E) : Set F) : Set E) =
              (K : Set E) := by
          simpa using congrArg (fun C : ProperCone ℝ E => (C : Set E)) hdual
        -- Rewrite the resulting dual cone using the bipolar identity.
        simpa [hdualSet] using h

/-- Membership in `polarCone` is exactly the pointwise inequality `φ x ≤ 0` on the set. -/
lemma mem_polarCone_iff (K : Set E) (φ : Module.Dual ℝ E) :
    φ ∈ polarCone (E := E) K ↔ ∀ x, x ∈ K → φ x ≤ 0 := by
  constructor
  · intro h x hx
    have h' :
        ∀ ⦃x⦄,
          x ∈ K →
            0 ≤
              (-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) x φ := by
      simpa [polarCone] using h
    have : 0 ≤ -(φ x) := by
      simpa [LinearMap.neg_apply, LinearMap.applyₗ] using (h' hx)
    exact (neg_nonneg).1 this
  · intro h
    have h' :
        ∀ ⦃x⦄,
          x ∈ K →
            0 ≤
              (-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) x φ := by
      intro x hx
      have : 0 ≤ -(φ x) := (neg_nonneg).2 (h x hx)
      simpa [LinearMap.neg_apply, LinearMap.applyₗ] using this
    simpa [polarCone] using h'

/-- For a submodule `K`, the polar cone coincides with the dual annihilator. -/
lemma mem_polarCone_submodule_iff_mem_dualAnnihilator (K : Submodule ℝ E) (φ : Module.Dual ℝ E) :
    φ ∈ polarCone (E := E) (K : Set E) ↔ φ ∈ K.dualAnnihilator := by
  constructor
  · intro h
    have hle : ∀ x, x ∈ (K : Set E) → φ x ≤ 0 :=
      (mem_polarCone_iff (E := E) (K := (K : Set E)) (φ := φ)).1 h
    refine (Submodule.mem_dualAnnihilator (W := K) (φ := φ)).2 ?_
    intro x hx
    have hnonpos : φ x ≤ 0 := hle x hx
    have hnonneg : 0 ≤ φ x := by
      have hneg : φ (-x) ≤ 0 := hle (-x) (by simpa using K.neg_mem hx)
      have hneg' : -(φ x) ≤ 0 := by simpa using hneg
      exact (neg_nonpos).1 hneg'
    exact le_antisymm hnonpos hnonneg
  · intro h
    have hzero : ∀ x, x ∈ K → φ x = 0 :=
      (Submodule.mem_dualAnnihilator (W := K) (φ := φ)).1 h
    refine (mem_polarCone_iff (E := E) (K := (K : Set E)) (φ := φ)).2 ?_
    intro x hx
    have : φ x = 0 := hzero x (by simpa using hx)
    simp [this]

/-- Text 14.0.2: If `K` is a subspace of `ℝ^n`, then its polar equals its orthogonal complement:
`Kᵒ = Kᗮ = {x★ ∈ ℝ^n | ∀ x ∈ K, ⟪x, x★⟫ = 0}`.

In this file we interpret `Kᵒ` as `polarCone (K : Set E)` (a subset of the dual space
`Module.Dual ℝ E`), and the orthogonal complement as the dual annihilator
`K.dualAnnihilator = {x★ | ∀ x ∈ K, x★ x = 0}`. -/
theorem polarCone_submodule_eq_dualAnnihilator (K : Submodule ℝ E) :
    polarCone (K : Set E) = (K.dualAnnihilator : Set (Module.Dual ℝ E)) := by
  ext φ
  exact (mem_polarCone_submodule_iff_mem_dualAnnihilator (E := E) (K := K) (φ := φ))

/-- The convex cone of points where a linear functional is nonpositive. -/
def nonposCone (φ : Module.Dual ℝ E) : ConvexCone ℝ E where
  carrier := {x : E | φ x ≤ 0}
  add_mem' := by
    intro x hx y hy
    simpa [map_add] using add_nonpos hx hy
  smul_mem' := by
    intro c hc x hx
    -- `φ (c • x) = c * φ x` and `c ≥ 0`, `φ x ≤ 0`.
    have hc' : 0 ≤ c := le_of_lt hc
    simpa [LinearMap.map_smul, smul_eq_mul] using (mul_nonpos_of_nonneg_of_nonpos hc' hx)

@[simp] lemma mem_nonposCone_iff (φ : Module.Dual ℝ E) (x : E) :
    x ∈ nonposCone (E := E) φ ↔ φ x ≤ 0 :=
  Iff.rfl

/-- If a linear functional is nonpositive on a generating set, it is nonpositive on the cone hull. -/
lemma hull_le_nonposCone_of_forall_range {I : Type*} (a : I → E) (φ : Module.Dual ℝ E)
    (h : ∀ i, φ (a i) ≤ 0) :
    ConvexCone.hull ℝ (Set.range a) ≤ nonposCone (E := E) φ := by
  refine (ConvexCone.hull_le_iff (C := nonposCone (E := E) φ) (s := Set.range a)).2 ?_
  rintro _ ⟨i, rfl⟩
  simpa [mem_nonposCone_iff] using h i

/-- If a linear functional is nonpositive on each generator `a i`, it is nonpositive on the hull. -/
lemma le_zero_on_hull_of_le_zero_on_generators {I : Type*} (a : I → E) (φ : Module.Dual ℝ E)
    (h : ∀ i, φ (a i) ≤ 0) :
    ∀ x, x ∈ (ConvexCone.hull ℝ (Set.range a) : Set E) → φ x ≤ 0 := by
  intro x hx
  have hx' : x ∈ (nonposCone (E := E) φ : Set E) :=
    (hull_le_nonposCone_of_forall_range (a := a) (φ := φ) h) hx
  simpa [mem_nonposCone_iff] using hx'

/-- Text 14.0.3: If `K` is the convex cone generated by a non-empty vector collection
`{a_i | i ∈ I}`, then `K` consists of all non-negative linear combinations of the `a_i`.
Consequently, the polar cone satisfies
`Kᵒ = {x★ | ∀ x ∈ K, x★ x ≤ 0} = {x★ | ∀ i ∈ I, x★ (a i) ≤ 0}`. -/
theorem polarCone_convexConeGenerated_range_eq {I : Type*} [Nonempty I] (a : I → E) :
    polarCone (Set.insert (0 : E) ((ConvexCone.hull ℝ (Set.range a) : ConvexCone ℝ E) : Set E)) =
      {φ : Module.Dual ℝ E | ∀ i : I, φ (a i) ≤ 0} := by
  classical
  let K : Set E := ((ConvexCone.hull ℝ (Set.range a) : ConvexCone ℝ E) : Set E)
  ext φ
  constructor
  · intro hφ i
    have hle : ∀ x, x ∈ Set.insert (0 : E) K → φ x ≤ 0 :=
      (mem_polarCone_iff (E := E) (K := Set.insert (0 : E) K) (φ := φ)).1 hφ
    have haK : a i ∈ K := by
      have : a i ∈ Set.range a := ⟨i, rfl⟩
      exact (ConvexCone.subset_hull (s := Set.range a)) this
    exact hle (a i) (Set.mem_insert_of_mem _ haK)
  · intro hφ
    refine (mem_polarCone_iff (E := E) (K := Set.insert (0 : E) K) (φ := φ)).2 ?_
    intro x hx
    rcases (Set.mem_insert_iff).1 hx with rfl | hxK
    · simp
    ·
      exact
        le_zero_on_hull_of_le_zero_on_generators (E := E) (a := a) (φ := φ) hφ x (by
          simpa [K] using hxK)

/-- Membership in the polar of `polarCone K`, expressed as a pointwise inequality. -/
lemma mem_polarCone_polar_iff (K : Set E) (x : E) :
    x ∈
        PointedCone.dual (R := ℝ)
          ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip (polarCone (E := E) K) ↔
      ∀ φ : Module.Dual ℝ E, (∀ y, y ∈ K → φ y ≤ 0) → φ x ≤ 0 := by
  constructor
  · intro hx φ hφ
    have hx' :
        ∀ ⦃ψ : Module.Dual ℝ E⦄,
          ψ ∈ polarCone (E := E) K →
            0 ≤
              ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip ψ x := by
      simpa [PointedCone.mem_dual] using hx
    have hφmem : φ ∈ polarCone (E := E) K :=
      (mem_polarCone_iff (E := E) (K := K) (φ := φ)).2 hφ
    have : 0 ≤
        ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip φ x := hx' hφmem
    have : 0 ≤ -(φ x) := by
      simpa [LinearMap.neg_apply, LinearMap.applyₗ] using this
    exact (neg_nonneg).1 this
  · intro hx
    refine (PointedCone.mem_dual (p :=
      ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip)
      (s := polarCone (E := E) K) (y := x)).2 ?_
    intro φ hφ
    have hφ' : ∀ y, y ∈ K → φ y ≤ 0 :=
      (mem_polarCone_iff (E := E) (K := K) (φ := φ)).1 hφ
    have hxle : φ x ≤ 0 := hx φ hφ'
    have : 0 ≤ -(φ x) := (neg_nonneg).2 hxle
    simpa [LinearMap.neg_apply, LinearMap.applyₗ] using this

/-- If a functional is nonpositive on `K`, then it is nonpositive on `closure K`. -/
lemma closure_subset_polarCone_polar [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E] (K : Set E) :
    closure K ⊆
        PointedCone.dual (R := ℝ)
          ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip (polarCone (E := E) K) := by
  intro x hx
  refine (mem_polarCone_polar_iff (E := E) (K := K) (x := x)).2 ?_
  intro φ hφ
  have hcont : Continuous fun x : E => φ x := by
    simpa using
      (LinearMap.continuous_of_finiteDimensional (f := (φ : E →ₗ[ℝ] ℝ)))
  have hclosed : IsClosed {x : E | φ x ≤ 0} := by
    simpa [Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)
  have hsubset : K ⊆ {x : E | φ x ≤ 0} := by
    intro y hy
    exact hφ y hy
  have hx' : x ∈ {x : E | φ x ≤ 0} := (closure_minimal hsubset hclosed) hx
  simpa using hx'

/-- The polar of `polarCone K` is contained in `closure K` for a nonempty convex cone `K`. -/
lemma polarCone_polar_subset_closure_of_convexCone [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] (K : ConvexCone ℝ E)
    (hKne : (K : Set E).Nonempty) :
    (PointedCone.dual (R := ℝ)
          ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
          (polarCone (E := E) (K : Set E)) : Set E) ⊆
      closure (K : Set E) := by
  intro x hx
  by_contra hxcl
  have hKcl_ne : ((K.closure : ConvexCone ℝ E) : Set E).Nonempty := by
    simpa [ConvexCone.coe_closure] using hKne.closure
  have hKcl_closed : IsClosed ((K.closure : ConvexCone ℝ E) : Set E) := by
    simp [ConvexCone.coe_closure]
  classical
  rcases
      (ConvexCone.canLift (𝕜 := ℝ) (E := E)).prf K.closure ⟨hKcl_ne, hKcl_closed⟩ with
    ⟨C, hCeq⟩
  have hxC : x ∉ (C : Set E) := by
    intro hxC
    have hxC' : x ∈ ((↑C : ConvexCone ℝ E) : Set E) := by simpa using hxC
    have hxKcl : x ∈ (K.closure : Set E) := by simpa [hCeq] using hxC'
    have hxcl' : x ∈ closure (K : Set E) := by simpa [ConvexCone.coe_closure] using hxKcl
    exact hxcl hxcl'
  obtain ⟨f, hfC, hfx⟩ := ProperCone.hyperplane_separation_point (C := C) (x₀ := x) hxC
  let φ : Module.Dual ℝ E := -(f : E →ₗ[ℝ] ℝ)
  have hφK : ∀ y, y ∈ (K : Set E) → φ y ≤ 0 := by
    intro y hy
    have hyC : y ∈ (C : Set E) := by
      have hycl : y ∈ closure (K : Set E) := subset_closure hy
      have hyKcl : y ∈ (K.closure : Set E) := by simpa [ConvexCone.coe_closure] using hycl
      have hyC' : y ∈ ((↑C : ConvexCone ℝ E) : Set E) := by simpa [hCeq] using hyKcl
      simpa using hyC'
    have hfnonneg : 0 ≤ f y := hfC y hyC
    have : -(f y) ≤ 0 := (neg_nonpos).2 hfnonneg
    simpa [φ] using this
  have hxle : φ x ≤ 0 := by
    have hx' := (mem_polarCone_polar_iff (E := E) (K := (K : Set E)) (x := x)).1 hx
    exact hx' φ hφK
  have hxpos : 0 < φ x := by
    have : 0 < -(f x) := (neg_pos).2 hfx
    simpa [φ] using this
  exact (not_lt_of_ge hxle) hxpos

/-- Text 14.0.4: The polar of `Kᵒ` is the closure of `K`, i.e. `(Kᵒ)ᵒ = cl K`. -/
theorem polarCone_polar_eq_closure [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    (K : ConvexCone ℝ E) (hKne : (K : Set E).Nonempty) :
    PointedCone.dual (R := ℝ)
        ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
        (polarCone (E := E) (K : Set E)) =
      closure (K : Set E) := by
  ext x
  constructor
  · intro hx
    exact polarCone_polar_subset_closure_of_convexCone (E := E) (K := K) hKne hx
  · intro hx
    exact closure_subset_polarCone_polar (E := E) (K := (K : Set E)) hx

/-- Text 14.0.5: The polar of a non-empty convex set `C` is
`C^∘ = {x★ | δ*(x★ | C) - 1 ≤ 0} = {x★ | ∀ x ∈ C, ⟪x, x★⟫ ≤ 1}`.

Here we model `δ*(x★ | C)` as the Fenchel–Legendre conjugate of the `EReal`-indicator of `C`
with respect to the evaluation pairing. -/
noncomputable def polar (C : Set E) : Set (Module.Dual ℝ E) :=
  {φ : Module.Dual ℝ E |
    fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) (erealIndicator C) φ ≤
      (1 : EReal)}

/-- If `fenchelConjugateBilin (eval) (erealIndicator C) φ ≤ 1`, then `φ` is bounded above by `1` on `C`. -/
lemma section14_le_one_on_C_of_fenchelConjugate_indicator_le_one {C : Set E} {φ : Module.Dual ℝ E}
    (hφ :
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) (erealIndicator C) φ ≤
        (1 : EReal)) :
    ∀ x ∈ C, φ x ≤ 1 := by
  classical
  intro x hx
  have hxle :
      ((LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) x φ : EReal) -
          erealIndicator C x ≤
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) (erealIndicator C) φ := by
    unfold fenchelConjugateBilin
    exact le_sSup ⟨x, rfl⟩
  have hxle' :
      ((LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) x φ : EReal) -
          erealIndicator C x ≤
        (1 : EReal) :=
    le_trans hxle hφ
  have : (φ x : EReal) ≤ (1 : EReal) := by
    simpa [erealIndicator, hx, LinearMap.applyₗ] using hxle'
  exact (EReal.coe_le_coe_iff).1 (by simpa using this)

/-- If `φ` is bounded above by `1` on `C`, then `fenchelConjugateBilin (eval) (erealIndicator C) φ ≤ 1`. -/
lemma section14_fenchelConjugate_indicator_le_one_of_le_one_on_C {C : Set E} {φ : Module.Dual ℝ E}
    (hφ : ∀ x ∈ C, φ x ≤ 1) :
    fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) (erealIndicator C) φ ≤
      (1 : EReal) := by
  classical
  unfold fenchelConjugateBilin
  refine sSup_le ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ C
  · have hxle : (φ x : EReal) ≤ (1 : EReal) := EReal.coe_le_coe (hφ x hx)
    simpa [erealIndicator, hx, LinearMap.applyₗ] using hxle
  · simp [erealIndicator, hx]

/-- Text 14.0.5 (membership form): `x★ ∈ C^∘` iff `⟪x, x★⟫ ≤ 1` for all `x ∈ C`. -/
theorem mem_polar_iff {C : Set E} {φ : Module.Dual ℝ E} :
    φ ∈ polar (E := E) C ↔ ∀ x ∈ C, φ x ≤ 1 := by
  classical
  constructor
  · intro hφ
    have hφ' :
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) (erealIndicator C) φ ≤
          (1 : EReal) := by
      simpa [polar] using hφ
    exact section14_le_one_on_C_of_fenchelConjugate_indicator_le_one (E := E) (C := C) (φ := φ) hφ'
  · intro hφ
    have hφ' :
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) (erealIndicator C) φ ≤
          (1 : EReal) :=
      section14_fenchelConjugate_indicator_le_one_of_le_one_on_C (E := E) (C := C) (φ := φ) hφ
    simpa [polar] using hφ'

/-- If `φ ∈ polar C`, then `φ` is bounded above by `1` on `C`.

This is a convenient lemma for Text 14.0.6 that avoids unfolding `mem_polar_iff`. -/
lemma section14_le_one_of_mem_polar {C : Set E} {φ : Module.Dual ℝ E}
    (hφ : φ ∈ polar (E := E) C) :
    ∀ x ∈ C, φ x ≤ 1 := by
  classical
  intro x hx
  have hφ' :
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) (erealIndicator C) φ ≤
        (1 : EReal) := by
    simpa [polar] using hφ
  have hxle :
      ((LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) x φ : EReal) -
          erealIndicator C x ≤
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) (erealIndicator C) φ := by
    unfold fenchelConjugateBilin
    exact le_sSup ⟨x, rfl⟩
  have hxle' :
      ((LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) x φ : EReal) -
          erealIndicator C x ≤
        (1 : EReal) :=
    le_trans hxle hφ'
  have : (φ x : EReal) ≤ (1 : EReal) := by
    simpa [erealIndicator, hx, LinearMap.applyₗ] using hxle'
  exact (EReal.coe_le_coe_iff).1 (by simpa using this)

/-- If `φ ∈ polar C` and `C` is absorbent, then `fenchelConjugateBilin (eval) (gauge C) φ = 0`. -/
lemma section14_fenchelConjugate_gauge_eq_zero_of_mem_polar {C : Set E} (hCabs : Absorbent ℝ C)
    {φ : Module.Dual ℝ E} (hφ : φ ∈ polar (E := E) C) :
    fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))
        (fun x => (gauge C x : EReal)) φ = 0 := by
  classical
  unfold fenchelConjugateBilin
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    have hφx : φ x ≤ gauge C x := by
      refine le_of_forall_pos_lt_add ?_
      intro ε hε
      have hgauge : gauge C x < gauge C x + ε := lt_add_of_pos_right _ hε
      obtain ⟨b, hb0, hb_lt, hxmem⟩ := exists_lt_of_gauge_lt hCabs hgauge
      rcases hxmem with ⟨c, hcC, rfl⟩
      have hφc : φ c ≤ 1 := section14_le_one_of_mem_polar (C := C) hφ c hcC
      have hb_nonneg : 0 ≤ b := le_of_lt hb0
      have hφbc_le : φ (b • c) ≤ b := by
        have : b * φ c ≤ b * (1 : ℝ) := mul_le_mul_of_nonneg_left hφc hb_nonneg
        simpa [LinearMap.map_smul, smul_eq_mul] using this
      exact lt_of_le_of_lt hφbc_le hb_lt
    have hsub : (φ x - gauge C x : ℝ) ≤ 0 := sub_nonpos.2 hφx
    have hsubE : ((φ x - gauge C x : ℝ) : EReal) ≤ (0 : EReal) := EReal.coe_le_coe hsub
    -- `EReal` subtraction on real inputs is coerced subtraction.
    simpa [LinearMap.applyₗ, EReal.coe_sub] using hsubE
  · refine le_sSup ?_
    refine ⟨0, ?_⟩
    simp [LinearMap.applyₗ]

/-- If `φ ∉ polar C`, then `fenchelConjugateBilin (eval) (gauge C) φ = ⊤`. -/
lemma section14_fenchelConjugate_gauge_eq_top_of_not_mem_polar {C : Set E} {φ : Module.Dual ℝ E}
    (hφ : φ ∉ polar (E := E) C) :
    fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))
        (fun x => (gauge C x : EReal)) φ = ⊤ := by
  classical
  let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
  have hφ' :
      ¬ fenchelConjugateBilin p (erealIndicator C) φ ≤ (1 : EReal) := by
    simpa [polar] using hφ
  have hone_lt : (1 : EReal) < fenchelConjugateBilin p (erealIndicator C) φ :=
    lt_of_not_ge hφ'
  unfold fenchelConjugateBilin at hone_lt
  rcases (lt_sSup_iff).1 hone_lt with ⟨a, ha, hone_lt_a⟩
  rcases ha with ⟨x₀, rfl⟩
  have hx₀C : x₀ ∈ C := by
    by_contra hx₀C
    simp [erealIndicator, hx₀C] at hone_lt_a
  have hx₀ : (1 : ℝ) < φ x₀ := by
    have : (1 : EReal) < (φ x₀ : EReal) := by
      simpa [erealIndicator, hx₀C, p, LinearMap.applyₗ] using hone_lt_a
    exact (EReal.coe_lt_coe_iff).1 (by simpa using this)
  unfold fenchelConjugateBilin
  refine (sSup_eq_top).2 ?_
  intro b hb
  induction b using EReal.rec with
  | bot =>
      refine ⟨(0 : EReal), ⟨0, by simp⟩, by simp⟩
  | coe r =>
      have hx₀' : 0 < φ x₀ - 1 := sub_pos.2 hx₀
      obtain ⟨n : ℕ, hn⟩ : ∃ n : ℕ, r / (φ x₀ - 1) < n := exists_nat_gt (r / (φ x₀ - 1))
      have hr : r < (n : ℝ) * (φ x₀ - 1) := by
        have : r / (φ x₀ - 1) < (n : ℝ) := by simpa using hn
        exact (div_lt_iff₀ hx₀').1 this
      have hgauge₀ : gauge C x₀ ≤ 1 := gauge_le_one_of_mem hx₀C
      have hgauge : gauge C ((n : ℝ) • x₀) ≤ (n : ℝ) := by
        have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.cast_nonneg n)
        calc
          gauge C ((n : ℝ) • x₀) = (n : ℝ) * gauge C x₀ := by
            simpa [smul_eq_mul] using (gauge_smul_of_nonneg (s := C) (x := x₀) hn_nonneg)
          _ ≤ (n : ℝ) * (1 : ℝ) := mul_le_mul_of_nonneg_left hgauge₀ hn_nonneg
          _ = (n : ℝ) := by simp
      have hphi : φ ((n : ℝ) • x₀) = (n : ℝ) * φ x₀ := by
        simp [smul_eq_mul]
      have hsub : (n : ℝ) * φ x₀ - (n : ℝ) ≤ φ ((n : ℝ) • x₀) - gauge C ((n : ℝ) • x₀) := by
        -- Use monotonicity of subtraction in the second argument.
        simpa [hphi] using
          (sub_le_sub_left hgauge ((n : ℝ) * φ x₀))
      have hr' : r < (n : ℝ) * φ x₀ - (n : ℝ) := by
        simpa [mul_sub, mul_one] using hr
      have hlt : (r : EReal) < ((φ ((n : ℝ) • x₀) - gauge C ((n : ℝ) • x₀) : ℝ) : EReal) := by
        have hrE : (r : EReal) < (( (n : ℝ) * φ x₀ - (n : ℝ) : ℝ) : EReal) :=
          EReal.coe_lt_coe hr'
        have hsubE :
            (( (n : ℝ) * φ x₀ - (n : ℝ) : ℝ) : EReal) ≤
              ((φ ((n : ℝ) • x₀) - gauge C ((n : ℝ) • x₀) : ℝ) : EReal) :=
          EReal.coe_le_coe hsub
        exact lt_of_lt_of_le hrE hsubE
      refine ⟨(p ((n : ℝ) • x₀) φ : EReal) - (gauge C ((n : ℝ) • x₀) : EReal), ?_, ?_⟩
      · exact ⟨(n : ℝ) • x₀, rfl⟩
      ·
        simpa [p, LinearMap.applyₗ, EReal.coe_sub, hphi] using hlt
  | top =>
      cases (lt_irrefl (⊤ : EReal) hb)

/-- The Fenchel conjugate of the (real-valued) gauge is the `EReal` indicator of `polar C`,
assuming `C` is absorbent. -/
lemma section14_fenchelConjugate_gauge_eq_erealIndicator_polar {C : Set E} (hCabs : Absorbent ℝ C) :
    fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))
        (fun x => (gauge C x : EReal)) =
      erealIndicator (E := Module.Dual ℝ E) (polar (E := E) C) := by
  classical
  funext φ
  by_cases hφ : φ ∈ polar (E := E) C
  ·
    simp [erealIndicator, hφ,
      section14_fenchelConjugate_gauge_eq_zero_of_mem_polar (C := C) hCabs hφ]
  ·
    simp [erealIndicator, hφ,
      section14_fenchelConjugate_gauge_eq_top_of_not_mem_polar (C := C) hφ]

/-- Text 14.0.6: Let `C` be a non-empty convex set. Then the closure `cl γ(·|C)` of the gauge
equals the support function `δ*(·|C^∘)` of the polar set.

In this file we model `γ(·|C)` as mathlib's `gauge C`, and we model the closure operation `cl`
as the Fenchel–Legendre biconjugate with respect to the evaluation pairing. We model
`δ*(·|C^∘)` as the Fenchel–Legendre conjugate of the `EReal`-indicator of `polar C`
with respect to the flipped evaluation pairing.

Note: mathlib's `gauge C` is real-valued, so to match the intended convex-analytic gauge (which
may take the value `⊤` when `C` does not absorb directions), we explicitly assume `C` is
absorbent. -/
theorem fenchelBiconjugate_gauge_eq_fenchelConjugate_indicator_polar {C : Set E}
    (hCabs : Absorbent ℝ C) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    fenchelConjugateBilin p.flip (fenchelConjugateBilin p (fun x => (gauge C x : EReal))) =
      fenchelConjugateBilin p.flip (erealIndicator (E := Module.Dual ℝ E) (polar (E := E) C)) := by
  classical
  dsimp
  rw [section14_fenchelConjugate_gauge_eq_erealIndicator_polar (C := C) hCabs]

/-
### Text 14.0.7: basic properties of the polar cone
-/

/-- `polarCone K` is an intersection of pointwise half-spaces. -/
lemma section14_polarCone_eq_iInter (K : Set E) :
    polarCone (E := E) K =
      ⋂ x : E, ⋂ (_ : x ∈ K), {φ : Module.Dual ℝ E | φ x ≤ 0} := by
  classical
  ext φ
  constructor
  · intro hφ
    have hle : ∀ x, x ∈ K → φ x ≤ 0 :=
      (mem_polarCone_iff (E := E) (K := K) (φ := φ)).1 hφ
    refine Set.mem_iInter.2 (fun x => Set.mem_iInter.2 (fun hx => ?_))
    exact hle x hx
  · intro hφ
    have hle : ∀ x, x ∈ K → φ x ≤ 0 := by
      intro x hx
      exact (Set.mem_iInter.1 (Set.mem_iInter.1 hφ x) hx)
    exact (mem_polarCone_iff (E := E) (K := K) (φ := φ)).2 hle

/-- `polarCone` is closed in the weak topology on `Module.Dual`. -/
lemma section14_isClosed_polarCone (K : Set E) :
    IsClosed (polarCone (E := E) K) := by
  classical
  have hclosed_half : ∀ x : E, IsClosed {φ : Module.Dual ℝ E | φ x ≤ 0} := by
    intro x
    have hcont : Continuous fun φ : Module.Dual ℝ E => φ x := by
      simpa [LinearMap.applyₗ] using
        (WeakBilin.eval_continuous
          (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip) x)
    simpa [Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)
  simpa [section14_polarCone_eq_iInter (E := E) (K := K)] using
    (isClosed_iInter (fun x : E => isClosed_iInter (fun _ : x ∈ K => hclosed_half x)))

/-- `polarCone` is convex (as a subset of the dual space). -/
lemma section14_convex_polarCone (K : Set E) :
    Convex ℝ (polarCone (E := E) K) := by
  classical
  intro φ₁ hφ₁ φ₂ hφ₂ a b ha hb hab
  refine (mem_polarCone_iff (E := E) (K := K) (φ := a • φ₁ + b • φ₂)).2 ?_
  intro x hx
  have h₁ : φ₁ x ≤ 0 := (mem_polarCone_iff (E := E) (K := K) (φ := φ₁)).1 hφ₁ x hx
  have h₂ : φ₂ x ≤ 0 := (mem_polarCone_iff (E := E) (K := K) (φ := φ₂)).1 hφ₂ x hx
  have ha' : 0 ≤ a := ha
  have hb' : 0 ≤ b := hb
  have hax : a * (φ₁ x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha' h₁
  have hbx : b * (φ₂ x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb' h₂
  simpa [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] using add_nonpos hax hbx

/-- The zero functional always belongs to the polar cone. -/
lemma section14_zero_mem_polarCone (K : Set E) :
    (0 : Module.Dual ℝ E) ∈ polarCone (E := E) K := by
  refine (mem_polarCone_iff (E := E) (K := K) (φ := 0)).2 ?_
  intro x hx
  simp

/-- Text 14.0.7. Let `K` be a non-empty convex cone in `ℝ^n`. Then the polar cone `Kᵒ` defined in
Text 14.0.1 is a closed convex cone containing the origin.

In this file, `Kᵒ` is modeled as `polarCone (E := E) (K : Set E)`, a subset of the dual space
`Module.Dual ℝ E`. -/
theorem isClosed_convex_polarCone_and_zero_mem (K : ConvexCone ℝ E) :
    IsClosed (polarCone (E := E) (K : Set E)) ∧
      Convex ℝ (polarCone (E := E) (K : Set E)) ∧
        (0 : Module.Dual ℝ E) ∈ polarCone (E := E) (K : Set E) := by
  refine ⟨section14_isClosed_polarCone (E := E) (K := (K : Set E)), ?_, ?_⟩
  · exact section14_convex_polarCone (E := E) (K := (K : Set E))
  · exact section14_zero_mem_polarCone (E := E) (K := (K : Set E))

/-- `polarCone` is order-reversing: enlarging the set shrinks its polar cone. -/
lemma section14_polarCone_antitone {A B : Set E} (hAB : A ⊆ B) :
    polarCone (E := E) B ⊆ polarCone (E := E) A := by
  intro φ hφ
  refine (mem_polarCone_iff (E := E) (K := A) (φ := φ)).2 ?_
  intro x hx
  have hφ' : ∀ x, x ∈ B → φ x ≤ 0 :=
    (mem_polarCone_iff (E := E) (K := B) (φ := φ)).1 hφ
  exact hφ' x (hAB hx)

/-- If every linear functional is continuous (e.g. in finite dimension), then polar membership
extends from a set to its topological closure. -/
lemma section14_polarCone_subset_polarCone_closure
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] [FiniteDimensional ℝ E] (K : Set E) :
    polarCone (E := E) K ⊆ polarCone (E := E) (closure K) := by
  intro φ hφ
  have hφK : ∀ x, x ∈ K → φ x ≤ 0 :=
    (mem_polarCone_iff (E := E) (K := K) (φ := φ)).1 hφ
  have hclosed : IsClosed ({x : E | φ x ≤ 0} : Set E) := by
    have hclosed' : IsClosed ((fun x : E => φ x) ⁻¹' Set.Iic (0 : ℝ)) :=
      (isClosed_Iic : IsClosed (Set.Iic (0 : ℝ))).preimage (φ.continuous_of_finiteDimensional)
    simpa [Set.preimage, Set.Iic] using hclosed'
  have hKsub : K ⊆ {x : E | φ x ≤ 0} := by
    intro x hx
    exact hφK x hx
  have hclsub : closure K ⊆ {x : E | φ x ≤ 0} :=
    closure_minimal hKsub hclosed
  refine (mem_polarCone_iff (E := E) (K := closure K) (φ := φ)).2 ?_
  intro x hx
  exact hclsub hx

/-- Text 14.0.8. Let `K` be a non-empty convex cone in `ℝ^n`. Then the polar of `cl K`
coincides with the polar of `K`, i.e. `(cl K)^∘ = K^∘`. In this file, we express this using the
polar cone `polarCone` (Text 14.0.1): `polarCone (closure K) = polarCone K`. -/
theorem polarCone_closure_eq [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] [FiniteDimensional ℝ E]
    (K : ConvexCone ℝ E) :
    polarCone (E := E) (closure (K : Set E)) = polarCone (E := E) (K : Set E) := by
  apply le_antisymm
  ·
    exact
      section14_polarCone_antitone (E := E) (A := (K : Set E)) (B := closure (K : Set E))
        subset_closure
  ·
    simpa using
      section14_polarCone_subset_polarCone_closure (E := E) (K := (K : Set E))

/-- The normal cone to a set `C` at the origin, modeled in the dual space: `N(0 | C)`. -/
def normalConeAtOrigin (C : Set E) : Set (Module.Dual ℝ E) :=
  {φ : Module.Dual ℝ E | ∀ x ∈ C, φ x ≤ 0}

/-- The normal cone to a set `C` in the dual space at the origin, modeled in the primal space:
`N(0 | C)`. -/
def normalConeAtOriginDual (C : Set (Module.Dual ℝ E)) : Set E :=
  {x : E | ∀ φ ∈ C, φ x ≤ 0}

/-- The polar cone agrees with the normal cone to the set at the origin (in the dual space). -/
lemma section14_polarCone_eq_normalConeAtOrigin (K : Set E) :
    polarCone (E := E) K = normalConeAtOrigin (E := E) K := by
  ext φ
  simp [normalConeAtOrigin, mem_polarCone_iff]

/-- The normal cone at the origin in the primal agrees with the dual cone defined via evaluation. -/
lemma section14_normalConeAtOriginDual_eq_pointedCone_dual_flip (C : Set (Module.Dual ℝ E)) :
    normalConeAtOriginDual (E := E) C =
      PointedCone.dual (R := ℝ)
        ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip C := by
  ext x
  constructor
  · intro hx
    refine
      (PointedCone.mem_dual (p :=
        ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip) (s := C) (y := x)).2 ?_
    intro φ hφ
    have hxle : φ x ≤ 0 := by
      have : ∀ ψ ∈ C, ψ x ≤ 0 := by
        simpa [normalConeAtOriginDual] using hx
      exact this φ hφ
    have : 0 ≤ -(φ x) := (neg_nonneg).2 hxle
    simpa [LinearMap.neg_apply, LinearMap.applyₗ] using this
  · intro hx
    -- Unfold the normal cone and rewrite the `PointedCone` inequality.
    have hx' :
        ∀ ⦃φ : Module.Dual ℝ E⦄,
          φ ∈ C →
            0 ≤ ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip φ x := by
      simpa [PointedCone.mem_dual] using hx
    refine (by
      simp [normalConeAtOriginDual]
      intro φ hφ
      have h0 := hx' (φ := φ) hφ
      have : 0 ≤ -(φ x) := by
        simpa [LinearMap.neg_apply, LinearMap.applyₗ] using h0
      exact (neg_nonneg).1 this)

/-- Text 14.0.9. Let `K` be a non-empty closed convex cone in `ℝ^n`. Then the polar cone `K^∘`
consists of all vectors normal to `K` at the origin, and conversely `K` consists of all vectors
normal to `K^∘` at the origin. Equivalently, writing `N(0 | C)` for the normal cone of `C` at `0`,
one has `K^∘ = N(0 | K)` and `K = N(0 | K^∘)`.

In this file, `K^∘` is modeled by `polarCone (E := E) (K : Set E)`. The normal cone at `0` is
modeled by `normalConeAtOrigin` (in the dual) and `normalConeAtOriginDual` (in the primal). -/
theorem polarCone_eq_normalConeAtOrigin_and_normalConeAtOriginDual_polarCone_eq
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [T2Space E] [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    (K : ConvexCone ℝ E) (hKne : (K : Set E).Nonempty) (hKclosed : IsClosed (K : Set E)) :
    polarCone (E := E) (K : Set E) = normalConeAtOrigin (E := E) (K : Set E) ∧
      (K : Set E) = normalConeAtOriginDual (E := E) (polarCone (E := E) (K : Set E)) := by
  refine ⟨?_, ?_⟩
  · simpa using section14_polarCone_eq_normalConeAtOrigin (E := E) (K := (K : Set E))
  ·
    have hdual :
        normalConeAtOriginDual (E := E) (polarCone (E := E) (K : Set E)) =
          closure (K : Set E) := by
      calc
        normalConeAtOriginDual (E := E) (polarCone (E := E) (K : Set E)) =
            PointedCone.dual (R := ℝ)
              ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
              (polarCone (E := E) (K : Set E)) := by
            simpa using
              (section14_normalConeAtOriginDual_eq_pointedCone_dual_flip (E := E)
                (C := polarCone (E := E) (K : Set E)))
        _ = closure (K : Set E) := polarCone_polar_eq_closure (E := E) (K := K) hKne
    exact (hKclosed.closure_eq).symm.trans hdual.symm

/-- Unpack membership in the dual cone w.r.t. the pairing `-(innerₗ _)`. -/
lemma section14_mem_pointedConeDual_negInner_iff (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ (PointedCone.dual (R := ℝ) (-innerₗ (EuclideanSpace ℝ (Fin n))) K :
          Set (EuclideanSpace ℝ (Fin n))) ↔
      ∀ x, x ∈ K → ⟪x, y⟫ ≤ 0 := by
  constructor
  · intro hy x hx
    have hneg : 0 ≤ (-innerₗ (EuclideanSpace ℝ (Fin n))) x y := hy hx
    have hneg' : 0 ≤ -⟪x, y⟫ := by
      simpa [LinearMap.neg_apply, innerₗ_apply_apply] using hneg
    exact (neg_nonneg).1 hneg'
  · intro hy x hx
    have hxy : ⟪x, y⟫ ≤ 0 := hy x hx
    have hneg : 0 ≤ -⟪x, y⟫ := (neg_nonneg).2 hxy
    simpa [LinearMap.neg_apply, innerₗ_apply_apply] using hneg

/-- A vector in the dual cone of the nonnegative orthant has all coordinates nonpositive. -/
lemma section14_coord_nonpos_of_mem_dual_nonnegOrthant (n : ℕ) (y : EuclideanSpace ℝ (Fin n))
    (hy :
      y ∈ (PointedCone.dual (R := ℝ) (-innerₗ (EuclideanSpace ℝ (Fin n)))
            ({x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin n))) :
            Set (EuclideanSpace ℝ (Fin n)))) :
    ∀ i, y i ≤ 0 := by
  classical
  intro i
  have hy' :
      ∀ x,
        x ∈ ({x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin n))) →
          ⟪x, y⟫ ≤ 0 :=
    (section14_mem_pointedConeDual_negInner_iff (n := n)
          ({x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin n))) y).1 hy
  have hxmem :
      EuclideanSpace.single i (1 : ℝ) ∈
        ({x : EuclideanSpace ℝ (Fin n) | ∀ j, 0 ≤ x j} : Set (EuclideanSpace ℝ (Fin n))) := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · simp [EuclideanSpace.single_apply, h]
  have hinner : ⟪EuclideanSpace.single i (1 : ℝ), y⟫ ≤ 0 := hy' _ hxmem
  simpa [EuclideanSpace.inner_single_left] using hinner

/-- Membership in the negation of the nonnegative orthant is coordinatewise nonpositivity. -/
lemma section14_mem_neg_nonnegOrthant_iff_coord_nonpos (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ -({x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin n))) ↔
      ∀ i, y i ≤ 0 := by
  classical
  constructor <;> intro hy <;> simpa using hy

/-- If `x` has nonnegative coordinates and `y` has nonpositive coordinates, then `⟪x, y⟫ ≤ 0`. -/
lemma section14_inner_nonpos_of_coords_nonneg_nonpos (n : ℕ) (x y : EuclideanSpace ℝ (Fin n))
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, y i ≤ 0) :
    ⟪x, y⟫ ≤ 0 := by
  classical
  -- Expand the inner product as a finite sum. On `EuclideanSpace`, the inner product is defined
  -- using the dot product with swapped arguments: `⟪x, y⟫ = ∑ i, y i * x i`.
  have hsum : ⟪x, y⟫ = ∑ i : Fin n, y i * x i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  rw [hsum]
  refine Finset.sum_nonpos ?_
  intro i hi
  exact mul_nonpos_of_nonpos_of_nonneg (hy i) (hx i)

/-- Text 14.0.10. Let `K ⊆ ℝ^n` be the non-negative orthant
`K = {x = (ξ₁, …, ξₙ) | ξⱼ ≥ 0 for j = 1, …, n}`. Then the polar cone of `K` is the non-positive
orthant, i.e. `K^∘ = -K`.

In Lean, we model `ℝ^n` as `EuclideanSpace ℝ (Fin n)` and the polar cone as the dual cone with
respect to the pairing `-(innerₗ _)`, so that `y` is in the polar cone of `K` iff `⟪x, y⟫ ≤ 0` for
all `x ∈ K`. -/
theorem polarCone_nonnegOrthant_eq_neg (n : ℕ) :
    (PointedCone.dual (R := ℝ) (-innerₗ (EuclideanSpace ℝ (Fin n)))
          ({x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n))) =
      -({x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin n))) := by
  classical
  ext y
  constructor
  · intro hy
    have hycoord : ∀ i, y i ≤ 0 :=
      section14_coord_nonpos_of_mem_dual_nonnegOrthant (n := n) y hy
    exact (section14_mem_neg_nonnegOrthant_iff_coord_nonpos (n := n) y).2 hycoord
  · intro hy
    have hycoord : ∀ i, y i ≤ 0 :=
      (section14_mem_neg_nonnegOrthant_iff_coord_nonpos (n := n) y).1 hy
    refine
      (section14_mem_pointedConeDual_negInner_iff (n := n)
            ({x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i} : Set (EuclideanSpace ℝ (Fin n))) y).2
        ?_
    intro x hx
    exact
      section14_inner_nonpos_of_coords_nonneg_nonpos (n := n) x y (hx := hx) (hy := hycoord)

/-- Text 14.0.11. Polarity is order-inverting: if `C₁ ⊆ C₂` are closed convex sets containing the
origin, then their polars satisfy `C₁^∘ ⊇ C₂^∘`.

In this file, `C^∘` is modeled as `polar (E := E) C`. -/
theorem polar_antitone_of_subset [TopologicalSpace E] {C₁ C₂ : Set E}
    (hC : C₁ ⊆ C₂) :
    polar (E := E) C₂ ⊆ polar (E := E) C₁ := by
  intro φ hφ
  -- The geometric hypotheses are irrelevant for this order-reversing property: it is immediate
  -- from the membership characterization `mem_polar_iff`.
  have hφ' : ∀ x ∈ C₂, φ x ≤ 1 :=
    (mem_polar_iff (E := E) (C := C₂) (φ := φ)).1 hφ
  refine (mem_polar_iff (E := E) (C := C₁) (φ := φ)).2 ?_
  intro x hx
  exact hφ' x (hC hx)

/-- A linear functional on `ℝ^n` is determined by its values on the coordinate vectors. -/
lemma section14_dual_apply_eq_sum_mul_single {n : ℕ}
    (φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    φ x =
      Finset.univ.sum (fun i : Fin n => x i * φ (EuclideanSpace.single i (1 : ℝ))) := by
  classical
  have hx :
      (Finset.univ.sum fun i : Fin n => (x i) • EuclideanSpace.single i (1 : ℝ)) = x := by
    ext j
    simp [smul_eq_mul, Pi.single_apply, Finset.sum_ite_eq, mul_ite]
  calc
    φ x = φ (Finset.univ.sum fun i : Fin n => (x i) • EuclideanSpace.single i (1 : ℝ)) := by
      simp [hx]
    _ =
        Finset.univ.sum fun i : Fin n => φ ((x i) • EuclideanSpace.single i (1 : ℝ)) := by
      simp [map_sum]
    _ = Finset.univ.sum (fun i : Fin n => x i * φ (EuclideanSpace.single i (1 : ℝ))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [smul_eq_mul]

/-- Each coordinate vector `e_j` belongs to the subprobability simplex `{x | x ≥ 0, ∑ x ≤ 1}`. -/
lemma section14_single_one_mem_subprobabilitySimplex (n : ℕ) (j : Fin n) :
    (EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin n)) ∈
      {x : EuclideanSpace ℝ (Fin n) |
        (∀ j, 0 ≤ x j) ∧ (Finset.univ.sum (fun j => x j)) ≤ (1 : ℝ)} := by
  constructor
  · intro i
    by_cases h : i = j
    · subst h
      simp [EuclideanSpace.single_apply]
    · simp [EuclideanSpace.single_apply, h]
  · simp [EuclideanSpace.single_apply, Finset.sum_ite_eq']

/-- If `φ` is bounded by `1` on all coordinate vectors, then it is bounded by `1` on `C₁`. -/
lemma section14_le_one_of_forall_single_le_one_and_mem_C₁ {n : ℕ}
    (φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (hφ : ∀ j : Fin n, φ (EuclideanSpace.single j (1 : ℝ)) ≤ 1)
    (hxnonneg : ∀ j : Fin n, 0 ≤ x j)
    (hxsum : (Finset.univ.sum fun j : Fin n => x j) ≤ (1 : ℝ)) :
    φ x ≤ 1 := by
  classical
  -- Expand `φ x` into a coordinate sum and bound termwise using `hxnonneg`.
  rw [section14_dual_apply_eq_sum_mul_single (φ := φ) (x := x)]
  have hle :
      (Finset.univ.sum fun i : Fin n => x i * φ (EuclideanSpace.single i (1 : ℝ))) ≤
        Finset.univ.sum fun i : Fin n => x i * (1 : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact mul_le_mul_of_nonneg_left (hφ i) (hxnonneg i)
  have hle' :
      (Finset.univ.sum fun i : Fin n => x i * φ (EuclideanSpace.single i (1 : ℝ))) ≤
        Finset.univ.sum fun i : Fin n => x i := by
    simpa [mul_one] using hle
  exact le_trans hle' hxsum

/-- Text 14.0.12 (Example). Define
`C₁ = {x = (ξ₁, …, ξₙ) | ξⱼ ≥ 0, ξ₁ + ⋯ + ξₙ ≤ 1}`.
Then its polar is
`C₁^∘ = {x★ = (ξ₁★, …, ξₙ★) | ξⱼ★ ≤ 1 for j = 1, …, n}`.

In this file, `C^∘` is modeled as `polar (E := E) C : Set (Module.Dual ℝ E)`. For `ℝ^n` we use
`E = EuclideanSpace ℝ (Fin n)`, and we express the coordinate inequalities as
`φ (Pi.single j 1) ≤ 1`. -/
theorem polar_subprobabilitySimplex_eq (n : ℕ) :
    let C₁ : Set (EuclideanSpace ℝ (Fin n)) :=
      {x | (∀ j, 0 ≤ x j) ∧ (Finset.univ.sum (fun j => x j)) ≤ (1 : ℝ)}
    polar (E := EuclideanSpace ℝ (Fin n)) C₁ =
      {φ : Module.Dual ℝ (EuclideanSpace ℝ (Fin n)) |
        ∀ j, φ (EuclideanSpace.single j (1 : ℝ)) ≤ 1} := by
  classical
  -- Unfold the `let`-bound definition of `C₁`.
  simp
  set C₁ : Set (EuclideanSpace ℝ (Fin n)) :=
    {x | (∀ j, 0 ≤ x j) ∧ (Finset.univ.sum (fun j => x j)) ≤ (1 : ℝ)}
  ext φ
  constructor
  · intro hφ j
    have hφ' : ∀ x ∈ C₁, φ x ≤ 1 :=
      (mem_polar_iff (E := EuclideanSpace ℝ (Fin n)) (C := C₁) (φ := φ)).1 hφ
    have hjmem : EuclideanSpace.single j (1 : ℝ) ∈ C₁ := by
      simpa [C₁] using section14_single_one_mem_subprobabilitySimplex (n := n) j
    exact hφ' _ hjmem
  · intro hφ
    refine
      (mem_polar_iff (E := EuclideanSpace ℝ (Fin n)) (C := C₁) (φ := φ)).2 ?_
    intro x hx
    rcases (show (∀ j, 0 ≤ x j) ∧ (Finset.univ.sum (fun j => x j)) ≤ (1 : ℝ) by
      simpa [C₁] using hx) with
      ⟨hxnonneg, hxsum⟩
    exact section14_le_one_of_forall_single_le_one_and_mem_C₁ (φ := φ) (x := x) hφ hxnonneg hxsum

end Section14
end Chap03
