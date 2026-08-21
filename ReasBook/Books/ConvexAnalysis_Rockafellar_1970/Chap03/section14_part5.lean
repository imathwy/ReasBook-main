/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section14_part4
section Chap03
section Section14

open scoped Pointwise
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If `inf f < 0`, then the `0`-sublevel set of `f` is nonempty. -/
lemma section14_sublevelZero_nonempty {F : Type*} {f : F → EReal}
    (hInf : sInf (Set.range f) < (0 : EReal)) : ({x : F | f x ≤ (0 : EReal)}).Nonempty := by
  classical
  by_contra hne
  have hnonneg : ∀ x, (0 : EReal) ≤ f x := by
    intro x
    by_contra hx
    have hxlt : f x < (0 : EReal) := lt_of_not_ge hx
    exact hne ⟨x, le_of_lt hxlt⟩
  have h0lb : (0 : EReal) ≤ sInf (Set.range f) := by
    refine le_sInf ?_
    rintro y ⟨x, rfl⟩
    exact hnonneg x
  exact (not_lt_of_ge h0lb) hInf

/-- If `inf f < 0`, then there exists a point with `f x < 0`. -/
lemma section14_exists_lt_zero_of_sInf_lt_zero {F : Type*} {f : F → EReal}
    (hInf : sInf (Set.range f) < (0 : EReal)) : ∃ x : F, f x < (0 : EReal) := by
  classical
  by_contra hne
  have hnonneg : ∀ x, (0 : EReal) ≤ f x := by
    intro x
    by_contra hx
    have hxlt : f x < (0 : EReal) := lt_of_not_ge hx
    exact hne ⟨x, hxlt⟩
  have h0lb : (0 : EReal) ≤ sInf (Set.range f) := by
    refine le_sInf ?_
    rintro y ⟨x, rfl⟩
    exact hnonneg x
  exact (not_lt_of_ge h0lb) hInf

/-!
### Auxiliary lemmas for inner-product polar cones

These lemmas are used to connect `0`-sublevel sets of support functions (Section 13) with
`innerDualCone` (Mathlib) and to access the bipolar identity in `ℝⁿ`.
-/

section InnerDual

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- For fixed `y`, the set `{x | 0 ≤ ⟪x, y⟫}` is a closed convex cone. -/
private def section14_innerHalfspaceCone (y : H) : ConvexCone ℝ H where
  carrier := {x : H | 0 ≤ ⟪x, y⟫_ℝ}
  smul_mem' c hc x hx := by
    -- `⟪c • x, y⟫ = c * ⟪x, y⟫` and `c ≥ 0`.
    simpa [real_inner_smul_left] using mul_nonneg (le_of_lt hc) hx
  add_mem' x hx z hz := by
    have hadd : ⟪x + z, y⟫_ℝ = ⟪x, y⟫_ℝ + ⟪z, y⟫_ℝ := by
      simpa using (inner_add_left (x := x) (y := z) (z := y))
    -- Rewrite using additivity and conclude by `add_nonneg`.
    simpa [hadd] using add_nonneg hx hz

/-- The inner dual cone is unchanged by replacing a set with the closure of its conic hull. -/
lemma section14_innerDualCone_closure_coneHull_eq (s : Set H) :
    ProperCone.innerDual (E := H)
        (closure ((ConvexCone.hull ℝ (Set.insert (0 : H) s) : ConvexCone ℝ H) : Set H)) =
      ProperCone.innerDual (E := H) s := by
  classical
  ext y
  constructor
  · intro hy x hx
    -- Restrict the inequality to points of `s`.
    have hx' :
        x ∈ closure ((ConvexCone.hull ℝ (Set.insert (0 : H) s) : ConvexCone ℝ H) : Set H) :=
      subset_closure <|
        ConvexCone.subset_hull (R := ℝ) (s := Set.insert (0 : H) s) (by
          exact Set.mem_insert_of_mem (0 : H) hx)
    exact (ProperCone.mem_innerDual (E := H) (s := _) (y := y)).1 hy hx'
  · intro hy
    -- If `y` is nonnegative on `s`, then it is nonnegative on the closed conic hull of `s`,
    -- since `{x | 0 ≤ ⟪x,y⟫}` is a closed convex cone containing `s`.
    have hs : Set.insert (0 : H) s ⊆ (section14_innerHalfspaceCone (H := H) y : Set H) := by
      intro x hx
      rcases (Set.mem_insert_iff).1 hx with rfl | hx
      · simp [section14_innerHalfspaceCone]
      · simpa [section14_innerHalfspaceCone] using (ProperCone.mem_innerDual (E := H) (s := s) (y := y)).1 hy hx
    have hHull :
        ((ConvexCone.hull ℝ (Set.insert (0 : H) s) : ConvexCone ℝ H) : Set H) ⊆
          (section14_innerHalfspaceCone (H := H) y : Set H) := by
      intro x hx
      have hx' :
          x ∈ (section14_innerHalfspaceCone (H := H) y : Set H) := by
        have hle :
            ConvexCone.hull ℝ (Set.insert (0 : H) s) ≤ section14_innerHalfspaceCone (H := H) y :=
          (ConvexCone.hull_le_iff (C := section14_innerHalfspaceCone (H := H) y)
                (s := Set.insert (0 : H) s)).2 hs
        exact hle hx
      exact hx'
    have hClosed :
        IsClosed (section14_innerHalfspaceCone (H := H) y : Set H) := by
      -- `{x | 0 ≤ ⟪x,y⟫}` is the preimage of `Ici 0` under a continuous map.
      have hcont : Continuous fun x : H => ⟪x, y⟫_ℝ := by
        simpa using (Continuous.inner (f := fun x : H => x) (g := fun _ : H => y)
          continuous_id' continuous_const)
      simpa [section14_innerHalfspaceCone, Set.preimage, Set.mem_Ici] using
        (isClosed_Ici.preimage hcont)
    refine (ProperCone.mem_innerDual (E := H) (s := _) (y := y)).2 ?_
    intro x hx
    have hx' : x ∈ (section14_innerHalfspaceCone (H := H) y : Set H) :=
      (closure_minimal hHull hClosed) hx
    simpa [section14_innerHalfspaceCone] using hx'

/-- Bipolar theorem (inner-product version): the double inner dual cone of a set is the closure
of its conic hull. -/
lemma section14_innerDualCone_innerDualCone_eq_closure_coneHull (s : Set H) :
    (ProperCone.innerDual (E := H) (ProperCone.innerDual (E := H) s : Set H) : Set H) =
      closure ((ConvexCone.hull ℝ (Set.insert (0 : H) s) : ConvexCone ℝ H) : Set H) := by
  classical
  -- Apply the bipolar theorem for nonempty closed convex cones to the closed conic hull of `s`.
  let K : ConvexCone ℝ H := (ConvexCone.hull ℝ (Set.insert (0 : H) s)).closure
  have hKne : (K : Set H).Nonempty := by
    refine ⟨0, ?_⟩
    have h0 : (0 : H) ∈ (ConvexCone.hull ℝ (Set.insert (0 : H) s) : ConvexCone ℝ H) :=
      ConvexCone.subset_hull (R := ℝ) (s := Set.insert (0 : H) s) (by
        exact Set.mem_insert (0 : H) s)
    exact subset_closure h0
  have hKclosed : IsClosed (K : Set H) := by
    -- `ConvexCone.closure` has carrier `closure (K : Set H)`.
    simp [K, ConvexCone.coe_closure]
  have hDual :
      ProperCone.innerDual (E := H) s = ProperCone.innerDual (E := H) (K : Set H) := by
    simpa [K, ConvexCone.coe_closure] using (section14_innerDualCone_closure_coneHull_eq (H := H) s).symm
  have hBip :
      (ProperCone.innerDual (E := H) (ProperCone.innerDual (E := H) (K : Set H) : Set H) : Set H) =
        (K : Set H) := by
    have hK : (K : Set H).Nonempty ∧ IsClosed (K : Set H) := ⟨hKne, hKclosed⟩
    have hKp : ∃ Kp : ProperCone ℝ H, (Kp : ConvexCone ℝ H) = K := by
      simpa using (CanLift.prf (x := K) hK)
    let Kp : ProperCone ℝ H := Classical.choose hKp
    have hKp_coe : (Kp : ConvexCone ℝ H) = K := Classical.choose_spec hKp
    have hKp_set : (Kp : Set H) = (K : Set H) := by
      ext x
      simp [← hKp_coe]
    have hBipKp :
        (ProperCone.innerDual (E := H) (ProperCone.innerDual (E := H) (Kp : Set H) : Set H) : Set H) =
          (Kp : Set H) := by
      simp
    simpa [hKp_set] using hBipKp
  calc
    (ProperCone.innerDual (E := H) (ProperCone.innerDual (E := H) s : Set H) : Set H)
        =
        (ProperCone.innerDual (E := H) (ProperCone.innerDual (E := H) (K : Set H) : Set H) : Set H) := by
          simp [hDual]
    _ = (K : Set H) := hBip
    _ = closure ((ConvexCone.hull ℝ (Set.insert (0 : H) s) : ConvexCone ℝ H) : Set H) := by
          simp [K, ConvexCone.coe_closure]

/-- In a real inner product space, the polar cone condition for `toDual y` is the inequality
`⟪y, x⟫ ≤ 0` on the set. -/
lemma section14_toDual_mem_polarCone_iff (s : Set H) (y : H) :
    ((InnerProductSpace.toDual ℝ H y : StrongDual ℝ H) : Module.Dual ℝ H) ∈
        polarCone (E := H) s ↔
      ∀ x, x ∈ s → ⟪y, x⟫_ℝ ≤ 0 := by
  simpa [InnerProductSpace.toDual_apply_apply] using
    (mem_polarCone_iff (E := H) (K := s)
      (φ := ((InnerProductSpace.toDual ℝ H y : StrongDual ℝ H) : Module.Dual ℝ H)))

/-- In a real inner product space, the polar cone condition for `toDual y` is equivalent to
membership of `-y` in the inner dual cone of the set. -/
lemma section14_toDual_mem_polarCone_iff_neg_mem_innerDualCone (s : Set H) (y : H) :
    ((InnerProductSpace.toDual ℝ H y : StrongDual ℝ H) : Module.Dual ℝ H) ∈
        polarCone (E := H) s ↔ (-y) ∈ (ProperCone.innerDual (E := H) s : Set H) := by
  constructor
  · intro hy
    -- `0 ≤ ⟪x, -y⟫` is the same as `⟪x, y⟫ ≤ 0`.
    refine (ProperCone.mem_innerDual (E := H) (s := s) (y := -y)).2 ?_
    intro x hx
    have hx' : ⟪y, x⟫_ℝ ≤ 0 :=
      (section14_toDual_mem_polarCone_iff (H := H) (s := s) (y := y)).1 hy x hx
    simpa [inner_neg_right, real_inner_comm] using (neg_nonneg.2 hx')
  · intro hy
    refine (section14_toDual_mem_polarCone_iff (H := H) (s := s) (y := y)).2 ?_
    intro x hx
    have hx' : 0 ≤ ⟪x, -y⟫_ℝ :=
      (ProperCone.mem_innerDual (E := H) (s := s) (y := -y)).1 hy hx
    -- Convert back to `⟪x, y⟫ ≤ 0`.
    have hx'' : 0 ≤ -⟪x, y⟫_ℝ := by
      simpa [inner_neg_right] using hx'
    simpa [real_inner_comm] using (neg_nonneg).1 hx''

end InnerDual

/-- If `f* φ ≤ 0`, then `φ` is nonpositive on the `0`-sublevel set of `f`. -/
lemma section14_le_zero_on_sublevelZero_of_fenchelConjugate_le_zero {f : E → EReal}
    (φ : Module.Dual ℝ E)
    (hφ : fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal)) :
    ∀ x, f x ≤ (0 : EReal) → φ x ≤ 0 := by
  intro x hx0
  have hleSup :
      ((φ x : EReal) - f x) ≤
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ := by
    unfold fenchelConjugateBilin
    exact le_sSup ⟨x, rfl⟩
  have hdiff : (φ x : EReal) - f x ≤ (0 : EReal) := hleSup.trans hφ
  have hφlefx : (φ x : EReal) ≤ f x := (EReal.sub_nonpos).1 hdiff
  have hφle0 : (φ x : EReal) ≤ (0 : EReal) := hφlefx.trans hx0
  exact (EReal.coe_le_coe_iff.1 (by simpa using hφle0))

/-- The Fenchel conjugate is nonpositive iff the functional is dominated by the primal function:
`f* φ ≤ 0` iff `φ x ≤ f x` for all `x`. -/
lemma section14_fenchelConjugate_le_zero_iff {f : E → EReal} (φ : Module.Dual ℝ E) :
    fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal) ↔
      ∀ x : E, (φ x : EReal) ≤ f x := by
  classical
  unfold fenchelConjugateBilin
  constructor
  · intro hSup x
    have hleSup :
        ((LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ) x φ : EReal) - f x) ≤
          sSup (Set.range fun y : E => (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ) y φ : EReal) - f y) :=
      le_sSup ⟨x, rfl⟩
    have hterm : ((φ x : EReal) - f x) ≤ (0 : EReal) := by
      simpa [LinearMap.applyₗ] using hleSup.trans hSup
    exact (EReal.sub_nonpos).1 hterm
  · intro h
    refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    have hterm : ((φ x : EReal) - f x) ≤ (0 : EReal) := (EReal.sub_nonpos).2 (h x)
    simpa [LinearMap.applyₗ] using hterm

/-- The `0`-sublevel set of `f*` lies in the polar cone of the convex cone generated by the
`0`-sublevel set of `f`. -/
lemma section14_sublevel_fenchelConjugate_le_zero_subset_polarCone_hull_sublevelZero
    {f : E → EReal} :
    {φ : Module.Dual ℝ E |
          fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal)} ⊆
      polarCone (E := E)
        ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E) := by
  intro φ hφ
  refine (mem_polarCone_iff (E := E)
        (K :=
          ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E))
        (φ := φ)).2 ?_
  intro x hx
  have hx' : x ∈ (nonposCone (E := E) φ : Set E) := by
    have hle :
        ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} ≤ nonposCone (E := E) φ := by
      refine (ConvexCone.hull_le_iff (C := nonposCone (E := E) φ) (s := {x : E | f x ≤ 0})).2 ?_
      intro y hy
      exact section14_le_zero_on_sublevelZero_of_fenchelConjugate_le_zero (E := E) (f := f) φ hφ y hy
    exact hle hx
  simpa [mem_nonposCone_iff] using hx'

/-- If a set of dual elements is contained in the polar cone of `K`, then the closed convex cone
generated by that set is also contained in the polar cone of `K`. -/
lemma section14_closure_coneHull_subset_polarCone_of_subset
    [TopologicalSpace (Module.Dual ℝ E)] {K : Set E} {T : Set (Module.Dual ℝ E)}
    (hT : T ⊆ polarCone (E := E) K) (hclosed : IsClosed (polarCone (E := E) K)) :
    closure
        ((ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) :
          Set (Module.Dual ℝ E)) ⊆
      polarCone (E := E) K := by
  classical
  -- View the polar cone as a convex cone in the dual space.
  let Cpol : ConvexCone ℝ (Module.Dual ℝ E) :=
    (PointedCone.dual (R := ℝ)
          (-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) K :
        ConvexCone ℝ (Module.Dual ℝ E))
  have hT' : T ⊆ (Cpol : Set (Module.Dual ℝ E)) := by
    intro φ hφ
    have : φ ∈ polarCone (E := E) K := hT hφ
    simpa [Cpol, polarCone] using this
  have hHull_le : (ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) ≤ Cpol :=
    (ConvexCone.hull_le_iff (R := ℝ) (C := Cpol) (s := T)).2 hT'
  have hHull_subset :
      ((ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) :
          Set (Module.Dual ℝ E)) ⊆
        polarCone (E := E) K := by
    intro φ hφ
    have : φ ∈ (Cpol : Set (Module.Dual ℝ E)) := hHull_le hφ
    simpa [Cpol, polarCone] using this
  exact closure_minimal hHull_subset hclosed

/-- The polar cone is unchanged by replacing a set with the convex cone it generates. -/
lemma section14_polarCone_hull_eq (S : Set E) :
    polarCone (E := E) ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E) =
      polarCone (E := E) S := by
  classical
  ext φ
  constructor
  · intro hφ
    refine (mem_polarCone_iff (E := E) (K := S) (φ := φ)).2 ?_
    intro x hx
    have hx' :
        x ∈ ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E) :=
      ConvexCone.subset_hull (R := ℝ) (s := S) hx
    exact
      (mem_polarCone_iff (E := E)
            (K := ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E)) (φ := φ)).1 hφ x hx'
  · intro hφ
    refine
      (mem_polarCone_iff (E := E)
            (K := ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E)) (φ := φ)).2 ?_
    intro x hx
    have hle :
        (ConvexCone.hull ℝ S : ConvexCone ℝ E) ≤ nonposCone (E := E) φ := by
      refine (ConvexCone.hull_le_iff (C := nonposCone (E := E) φ) (s := S)).2 ?_
      intro y hy
      have hy' : φ y ≤ 0 :=
        (mem_polarCone_iff (E := E) (K := S) (φ := φ)).1 hφ y hy
      simpa [mem_nonposCone_iff] using hy'
    have hx' : x ∈ (nonposCone (E := E) φ : Set E) := hle hx
    simpa [mem_nonposCone_iff] using hx'

/-- In a finite-dimensional real topological vector space, membership in a polar cone propagates
from a set to its closure (and conversely). -/
lemma section14_polarCone_closure_eq
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] (K : Set E) :
    polarCone (E := E) (closure K) = polarCone (E := E) K := by
  classical
  ext φ
  constructor
  · intro hφ
    refine (mem_polarCone_iff (E := E) (K := K) (φ := φ)).2 ?_
    intro x hx
    have hxcl : x ∈ closure K := subset_closure hx
    exact (mem_polarCone_iff (E := E) (K := closure K) (φ := φ)).1 hφ x hxcl
  · intro hφ
    refine (mem_polarCone_iff (E := E) (K := closure K) (φ := φ)).2 ?_
    intro x hx
    have hcont : Continuous fun y : E => φ y := by
      simpa using
        (LinearMap.continuous_of_finiteDimensional (f := (φ : E →ₗ[ℝ] ℝ)))
    have hclosed : IsClosed {y : E | φ y ≤ 0} := by
      simpa [Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)
    have hsubset : K ⊆ {y : E | φ y ≤ 0} := by
      intro y hy
      exact (mem_polarCone_iff (E := E) (K := K) (φ := φ)).1 hφ y hy
    have hx' : x ∈ {y : E | φ y ≤ 0} := (closure_minimal hsubset hclosed) hx
    simpa using hx'

/-- Restrict a polar-cone condition from the closed conic hull of a set to the set itself. -/
lemma section14_mem_polarCone_of_mem_polarCone_closure_coneHull
    (S : Set E) [TopologicalSpace E] (φ : Module.Dual ℝ E)
    (hφ :
      φ ∈
        polarCone (E := E)
          (closure ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E))) :
    φ ∈ polarCone (E := E) S := by
  classical
  refine (mem_polarCone_iff (E := E) (K := S) (φ := φ)).2 ?_
  intro x hx
  have hx' :
      x ∈ closure ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E) :=
    subset_closure (ConvexCone.subset_hull (R := ℝ) (s := S) hx)
  exact
    (mem_polarCone_iff (E := E)
          (K := closure ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E)) (φ := φ)).1 hφ x hx'

/-- The `0`-sublevel set of the Fenchel conjugate lies in the polar cone of the `0`-sublevel set
of the primal function. -/
lemma section14_sublevel_fenchelConjugate_le_zero_subset_polarCone_sublevelZero
    {f : E → EReal} :
    {φ : Module.Dual ℝ E |
          fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal)} ⊆
      polarCone (E := E) {x : E | f x ≤ (0 : EReal)} := by
  intro φ hφ
  have hφ' :
      φ ∈
        polarCone (E := E)
          ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E) := by
    simpa using
      (section14_sublevel_fenchelConjugate_le_zero_subset_polarCone_hull_sublevelZero
        (E := E) (f := f) hφ)
  simpa [section14_polarCone_hull_eq (E := E) {x : E | f x ≤ (0 : EReal)}] using hφ'

/-- The weak topology on the algebraic dual induced by the evaluation pairing.

This is the canonical topology in which closure statements about polar sets and conjugate
sublevel sets are meaningful; it ensures that all evaluation maps `φ ↦ φ x` are continuous. -/
noncomputable local instance section14_instTopologicalSpace_dualWeak :
    TopologicalSpace (Module.Dual ℝ E) :=
  WeakBilin.instTopologicalSpace
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

noncomputable local instance section14_instContinuousAdd_dualWeak :
    ContinuousAdd (Module.Dual ℝ E) :=
  WeakBilin.instContinuousAdd
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

noncomputable local instance section14_instIsTopologicalAddGroup_dualWeak :
    IsTopologicalAddGroup (Module.Dual ℝ E) :=
  WeakBilin.instIsTopologicalAddGroup
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

noncomputable local instance section14_instContinuousSMul_dualWeak :
    ContinuousSMul ℝ (Module.Dual ℝ E) :=
  WeakBilin.instContinuousSMul
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

noncomputable local instance section14_instLocallyConvexSpace_dualWeak :
    LocallyConvexSpace ℝ (Module.Dual ℝ E) :=
  WeakBilin.locallyConvexSpace
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

/-- If `T` is nonempty, then the closure of the convex cone generated by `T` is nonempty. -/
lemma section14_closure_coneHull_nonempty_of_nonempty [TopologicalSpace (Module.Dual ℝ E)]
    {T : Set (Module.Dual ℝ E)} (hT : T.Nonempty) :
    (closure
          ((ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) :
            Set (Module.Dual ℝ E))).Nonempty := by
  rcases hT with ⟨φ, hφ⟩
  refine ⟨φ, subset_closure ?_⟩
  exact ConvexCone.subset_hull (R := ℝ) (s := T) hφ

/-- If `φ` is not in the weak-closure of the convex cone generated by `T`, then there is a point
`x : E` such that all elements of that closed cone are nonpositive on `x`, but `φ x > 0`.

This is a separation argument in the weak topology; the separating functional is represented as an
evaluation map using reflexivity of finite-dimensional spaces. -/
lemma section14_exists_eval_pos_of_not_mem_closure_coneHull
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    (T : Set (Module.Dual ℝ E))
    (hKne :
      (closure
            ((ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) :
              Set (Module.Dual ℝ E))).Nonempty)
    (φ : Module.Dual ℝ E)
    (hφ :
      φ ∉
        closure
          ((ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) :
            Set (Module.Dual ℝ E))) :
    ∃ x : E,
      (∀ ψ : Module.Dual ℝ E,
            ψ ∈
              closure
                ((ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) :
                  Set (Module.Dual ℝ E)) →
              ψ x ≤ 0) ∧
        (0 : ℝ) < φ x := by
  classical
  -- Work with the *closed* convex cone `K★ = cl (coneHull T)`.
  let Kstar : ConvexCone ℝ (Module.Dual ℝ E) := ConvexCone.hull ℝ T
  let KstarCl : ConvexCone ℝ (Module.Dual ℝ E) := Kstar.closure
  have hφ' : φ ∉ (KstarCl : Set (Module.Dual ℝ E)) := by
    simpa [KstarCl, ConvexCone.coe_closure, Kstar] using hφ
  have hKstarCl_ne : (KstarCl : Set (Module.Dual ℝ E)).Nonempty := by
    simpa [KstarCl, ConvexCone.coe_closure, Kstar] using hKne
  have hKstarCl_closed : IsClosed (KstarCl : Set (Module.Dual ℝ E)) := by
    simp [KstarCl, ConvexCone.coe_closure]
  -- Lift the closed nonempty cone `K★` to a `ProperCone` so we can use Farkas' lemma.
  rcases
      (ConvexCone.canLift (𝕜 := ℝ) (E := Module.Dual ℝ E)).prf KstarCl
        ⟨hKstarCl_ne, hKstarCl_closed⟩ with
    ⟨C, hCeq⟩
  have hCeqSet :
      ((↑C : ConvexCone ℝ (Module.Dual ℝ E)) : Set (Module.Dual ℝ E)) =
        (KstarCl : Set (Module.Dual ℝ E)) := by
    simpa using
      congrArg (fun K : ConvexCone ℝ (Module.Dual ℝ E) => (K : Set (Module.Dual ℝ E))) hCeq
  have hφC : φ ∉ (C : Set (Module.Dual ℝ E)) := by
    intro hφC
    have hφC' : φ ∈ ((↑C : ConvexCone ℝ (Module.Dual ℝ E)) : Set (Module.Dual ℝ E)) := by
      simpa using hφC
    have : φ ∈ (KstarCl : Set (Module.Dual ℝ E)) := by
      simpa [hCeqSet] using hφC'
    exact hφ' this
  obtain ⟨f0, hfC, hfφneg⟩ := ProperCone.hyperplane_separation_point (C := C) (x₀ := φ) hφC
  -- Flip the sign so that the separator is nonpositive on the cone and positive at `φ`.
  let f : StrongDual ℝ (Module.Dual ℝ E) := -f0
  have hf_nonpos : ∀ ψ : Module.Dual ℝ E, ψ ∈ (C : Set (Module.Dual ℝ E)) → f ψ ≤ 0 := by
    intro ψ hψ
    have : 0 ≤ f0 ψ := hfC ψ hψ
    have : -f0 ψ ≤ 0 := (neg_nonpos).2 this
    simpa [f] using this
  have hf_pos : (0 : ℝ) < f φ := by
    have : 0 < -f0 φ := (neg_pos).2 hfφneg
    simpa [f] using this
  -- Represent the separating functional `f` as evaluation at some `x : E`.
  let g : Module.Dual ℝ (Module.Dual ℝ E) := f.toLinearMap
  haveI : Module.IsReflexive ℝ E := by infer_instance
  let x : E := (Module.evalEquiv ℝ E).symm g
  refine ⟨x, ?_, ?_⟩
  · intro ψ hψcl
    have hψ' : ψ ∈ (C : Set (Module.Dual ℝ E)) := by
      have hψK : ψ ∈ (KstarCl : Set (Module.Dual ℝ E)) := by
        simpa [KstarCl, ConvexCone.coe_closure, Kstar] using hψcl
      have hψC' : ψ ∈ ((↑C : ConvexCone ℝ (Module.Dual ℝ E)) : Set (Module.Dual ℝ E)) := by
        simpa [hCeqSet] using hψK
      simpa using hψC'
    have hle : f ψ ≤ 0 := hf_nonpos ψ hψ'
    have hrepr : (ψ x : ℝ) = g ψ := by
      simp [x]
    simpa [g, hrepr] using hle
  · -- Convert `f φ > 0` to `φ x > 0`.
    have hrepr : (φ x : ℝ) = g φ := by
      simp [x]
    simpa [g, hrepr] using hf_pos

/-!
### Theorem 14.3 (duality backbone)

A functional nonpositive on `{x | f x ≤ 0}` lies in the closed convex cone generated by
`{φ | f* φ ≤ 0}`.

This is the only missing step in `section14_part3`: the intended proof uses the Section 13
support-function/positively-homogeneous-hull correspondence (Theorem 13.5) together with the polar
recession-cone correspondence (Theorem 14.2) and the `0`-sublevel/cone-hull identification (Theorem
7.6). Importing the needed Section 13 files is currently blocked by a global name collision on
`_root_.fenchelConjugateBilin`.
-/
/-- (Theorem 14.3, auxiliary) Nonemptiness of the `0`-sublevel set of the Fenchel conjugate.

In the textbook proof this is deduced from the Fenchel–Moreau identity at `0`:
`f 0 = - inf (f*)`, so `f 0 > 0` forces `inf (f*) < 0` and hence `{φ | f* φ ≤ 0}` is nonempty.

In this development, the corresponding Section 13/Fenchel–Moreau bridge is not yet imported due to a
global name collision on `_root_.fenchelConjugateBilin`. -/
lemma section14_sublevelZero_fenchelConjugate_nonempty
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) :
    ({φ : Module.Dual ℝ E |
          fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal)}
        : Set (Module.Dual ℝ E)).Nonempty := by
  classical
  /-
  We use a geometric Hahn–Banach separation on the (real) epigraph of `f` in `E × ℝ`, separating
  the origin `(0,0)` from that epigraph. The resulting separating functional has a positive
  coefficient on the `ℝ`-coordinate (using `hf0_ltTop` so that the epigraph contains a vertical
  ray at `x = 0`). Normalizing by that coefficient yields a linear functional dominated by `f`,
  hence with Fenchel conjugate value `≤ 0`.
  -/
  let epi : Set (E × ℝ) := {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}

  have hEpiConvex : Convex ℝ epi := by
    intro p hp q hq a b ha hb hab
    have hp' : f p.1 ≤ (p.2 : EReal) := hp
    have hq' : f q.1 ≤ (q.2 : EReal) := hq
    have hfconv' : ConvexERealFunction (F := E) f := hf.2
    have hfconv := hfconv' (x := p.1) (y := q.1) (a := a) (b := b) ha hb hab
    have haE : (0 : EReal) ≤ (a : EReal) := by simpa [EReal.coe_nonneg] using ha
    have hbE : (0 : EReal) ≤ (b : EReal) := by simpa [EReal.coe_nonneg] using hb
    have hmul_p : (a : EReal) * f p.1 ≤ (a : EReal) * (p.2 : EReal) :=
      mul_le_mul_of_nonneg_left hp' haE
    have hmul_q : (b : EReal) * f q.1 ≤ (b : EReal) * (q.2 : EReal) :=
      mul_le_mul_of_nonneg_left hq' hbE
    have hsum :
        (a : EReal) * f p.1 + (b : EReal) * f q.1 ≤
          (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) :=
      add_le_add hmul_p hmul_q
    -- Unpack the product convex combination.
    have hfst : (a • p + b • q).1 = a • p.1 + b • q.1 := by rfl
    have hsnd : (a • p + b • q).2 = a • p.2 + b • q.2 := by rfl
    -- Apply convexity of `f` and combine inequalities.
    have hle :
        f (a • p.1 + b • q.1) ≤
          (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) :=
      hfconv.trans hsum
    -- Rewrite the RHS as the coercion of the real second coordinate.
    have hrhs :
        (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) =
          ((a • p.2 + b • q.2 : ℝ) : EReal) := by
      -- All terms are real coercions.
      simp [smul_eq_mul]
    have hle' : f (a • p.1 + b • q.1) ≤ ((a • p.2 + b • q.2 : ℝ) : EReal) :=
      hle.trans_eq hrhs
    have : f ((a • p + b • q).1) ≤ ((a • p + b • q).2 : EReal) := by
      simpa [hfst, hsnd] using hle'
    simpa [epi] using this

  have hEpiClosed : IsClosed epi := by
    -- `epi` is the preimage of the closed epigraph in `E × EReal` under the embedding
    -- `(x, μ) ↦ (x, (μ : EReal))`.
    let g : E × ℝ → E × EReal := fun p => (p.1, (p.2 : EReal))
    have hg : Continuous g := by
      refine continuous_fst.prodMk ?_
      simpa using (continuous_coe_real_ereal.comp continuous_snd)
    have hclosed : IsClosed {p : E × EReal | f p.1 ≤ p.2} := hf_closed.isClosed_epigraph
    have : IsClosed (g ⁻¹' {p : E × EReal | f p.1 ≤ p.2}) := hclosed.preimage hg
    simpa [epi, g] using this

  have h0not : (0 : E × ℝ) ∉ epi := by
    intro h0
    have : f 0 ≤ (0 : EReal) := by simpa [epi] using h0
    exact (not_le_of_gt hf0) this

  -- Strictly separate the point `0` from the closed convex set `epi`.
  obtain ⟨L, u, hLu0, hLu⟩ :=
    geometric_hahn_banach_point_closed (E := E × ℝ) (t := epi) (x := (0 : E × ℝ))
      hEpiConvex hEpiClosed h0not

  have hu_pos : 0 < u := by
    simpa using (show L (0 : E × ℝ) < u from hLu0)

  -- Extract the `E`-part of `L` as a linear functional.
  let φ0 : Module.Dual ℝ E :=
    { toFun := fun x => L (x, (0 : ℝ))
      map_add' := by
        intro x y
        -- `map_add` on `E × ℝ`, then simplify.
        simpa using (map_add L (x, (0 : ℝ)) (y, (0 : ℝ)))
      map_smul' := by
        intro c x
        -- `c • (x, 0) = (c • x, 0)`.
        simpa [Prod.smul_mk, smul_eq_mul] using (map_smul L c (x, (0 : ℝ))) }

  -- Extract the `ℝ`-coefficient of `L` and show it is positive.
  set a : ℝ := L ((0 : E), (1 : ℝ))

  have hL0r : ∀ r : ℝ, L ((0 : E), r) = r * a := by
    intro r
    -- `(0,r) = r • (0,1)`
    have hr : (r : ℝ) • ((0 : E), (1 : ℝ)) = ((0 : E), r) := by
      ext <;> simp [Prod.smul_mk, smul_eq_mul]
    calc
      L ((0 : E), r) = L (r • ((0 : E), (1 : ℝ))) := by simp [hr]
      _ = r • L ((0 : E), (1 : ℝ)) := by simpa using (map_smul L r ((0 : E), (1 : ℝ)))
      _ = r * a := by simp [a, smul_eq_mul]

  have hLxr : ∀ x : E, ∀ r : ℝ, L (x, r) = φ0 x + r * a := by
    intro x r
    calc
      L (x, r) = L ((x, (0 : ℝ)) + ((0 : E), r)) := by simp
      _ = L (x, (0 : ℝ)) + L ((0 : E), r) := by
            simpa using (map_add L (x, (0 : ℝ)) ((0 : E), r))
      _ = φ0 x + r * a := by simp [φ0, hL0r]

  -- Use finiteness of `f 0` to produce a vertical ray in `epi`, forcing `a > 0`.
  rcases section14_eq_coe_of_lt_top (z := f 0) hf0_ltTop (hf.1.1 0) with ⟨r0, hr0⟩
  have hmem0 : ((0 : E), r0) ∈ epi := by
    simp [epi, hr0]

  have ha_ne : a ≠ 0 := by
    intro ha0
    have hu_lt : u < L ((0 : E), r0) := hLu ((0 : E), r0) hmem0
    have hLr0 : L ((0 : E), r0) = r0 * a := hL0r r0
    have : L ((0 : E), r0) = 0 := by simpa [ha0] using hLr0
    have : u < 0 := by simpa [this] using hu_lt
    exact (not_lt_of_ge (le_of_lt hu_pos)) this

  have ha_pos : 0 < a := by
    by_contra ha
    have ha_lt : a < 0 := lt_of_le_of_ne (le_of_not_gt ha) ha_ne
    -- Choose a large natural `n` so that `r0 + n ≥ u / a`, contradicting `u < (r0+n) * a`.
    obtain ⟨n : ℕ, hn⟩ : ∃ n : ℕ, (u / a - r0) < (n : ℝ) := exists_nat_gt (u / a - r0)
    have hn' : u / a < r0 + (n : ℝ) := by linarith
    have hmul : (r0 + (n : ℝ)) * a < u := by
      -- Multiply by the negative number `a`.
      have := (mul_lt_mul_of_neg_right hn' ha_lt)
      -- `(u/a) * a = u`.
      have ha0' : a ≠ 0 := ha_ne
      simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ ha0'] using this
    have hmemn : ((0 : E), r0 + (n : ℝ)) ∈ epi := by
      have : f 0 ≤ ((r0 + (n : ℝ) : ℝ) : EReal) := by
        -- `r0 ≤ r0 + n`
        have : (r0 : EReal) ≤ ((r0 + (n : ℝ) : ℝ) : EReal) := by
          exact_mod_cast (le_add_of_nonneg_right (by exact_mod_cast (Nat.cast_nonneg n)))
        simpa [hr0] using this
      simpa [epi] using this
    have hu_lt : u < L ((0 : E), r0 + (n : ℝ)) := hLu ((0 : E), r0 + (n : ℝ)) hmemn
    have : L ((0 : E), r0 + (n : ℝ)) = (r0 + (n : ℝ)) * a := by simpa using hL0r (r0 + (n : ℝ))
    exact (not_lt_of_gt (by simpa [this] using hu_lt)) hmul

  -- Define the candidate dual element and show it lies in the `≤ 0`-sublevel set of `f*`.
  let ψ : Module.Dual ℝ E := (-(1 / a)) • φ0
  have hu_div_pos : 0 < u / a := div_pos hu_pos ha_pos

  have hψ_le : ∀ x : E, (ψ x : EReal) ≤ f x := by
    intro x
    by_cases hxTop : f x = ⊤
    · simp [hxTop]
    · have hxlt : f x < ⊤ := lt_top_iff_ne_top.2 hxTop
      rcases section14_eq_coe_of_lt_top (z := f x) hxlt (hf.1.1 x) with ⟨r, hr⟩
      have hxmem : (x, r) ∈ epi := by
        simp [epi, hr]
      have hu_lt : u < L (x, r) := hLu (x, r) hxmem
      have hrepr : L (x, r) = φ0 x + r * a := hLxr x r
      have hineq : (-(1 / a)) * (φ0 x) + u / a < r := by
        -- Start from `u < φ0 x + r * a` and divide by `a > 0`.
        have hu' : u - φ0 x < r * a := by
          have : u < φ0 x + r * a := by simpa [hrepr] using hu_lt
          linarith
        have hdiv : (u - φ0 x) / a < (r * a) / a := div_lt_div_of_pos_right hu' ha_pos
        have hrdiv : (r * a) / a = r := by field_simp [ha_ne]
        have h1 : (u - φ0 x) / a < r := by simpa [hrdiv] using hdiv
        have hrewrite : (u - φ0 x) / a = (-(1 / a)) * (φ0 x) + u / a := by
          field_simp [ha_ne]
          ring
        simpa [hrewrite] using h1
      have hψ_lt : ψ x < r := by
        -- Use positivity of `u/a` to drop the constant term.
        have hdrop : (-(1 / a)) * (φ0 x) < (-(1 / a)) * (φ0 x) + u / a := by
          linarith
        have hψx : ψ x = (-(1 / a)) * (φ0 x) := by
          simp [ψ, φ0, smul_eq_mul]
        -- Now chain the inequalities.
        have : (-(1 / a)) * (φ0 x) < r := lt_of_lt_of_le (hdrop.trans hineq) (le_rfl)
        simpa [hψx] using this
      -- Convert to an `EReal` inequality using the real representation of `f x`.
      have : (ψ x : EReal) ≤ (r : EReal) := by
        exact_mod_cast (le_of_lt hψ_lt)
      simpa [hr] using this

  refine ⟨ψ, (section14_fenchelConjugate_le_zero_iff (E := E) (f := f) ψ).2 ?_⟩
  intro x
  simpa using hψ_le x

/-- Positively homogeneous hull generated by `f`:
`k(x) = inf_{t>0} t * f(t⁻¹ • x)`.

This is the standard conic hull construction used in the proof of Theorem 14.3. -/
noncomputable def section14_posHomHull (f : E → EReal) : E → EReal :=
  fun x =>
    sInf {r : EReal | ∃ t : ℝ, 0 < t ∧ r = (t : EReal) * f (t⁻¹ • x)}

/-- Multiplication by a positive real number is an order isomorphism on `EReal`. -/
noncomputable def section14_mulPosOrderIso (t : ℝ) (ht : 0 < t) : EReal ≃o EReal where
  toFun x := (t : EReal) * x
  invFun x := ((t⁻¹ : ℝ) : EReal) * x
  left_inv x := by
    have htne : t ≠ 0 := ne_of_gt ht
    -- `t⁻¹ * (t * x) = (t⁻¹ * t) * x = x`.
    calc
      ((t⁻¹ : ℝ) : EReal) * ((t : EReal) * x) = (((t⁻¹ : ℝ) : EReal) * (t : EReal)) * x := by
        simp [mul_assoc]
      _ = ((t⁻¹ * t : ℝ) : EReal) * x := by
        -- `↑(t⁻¹ * t) = ↑t⁻¹ * ↑t`.
        simp [mul_assoc]
      _ = (1 : EReal) * x := by
        -- Now use `t⁻¹ * t = 1` in `ℝ`.
        simp [inv_mul_cancel₀ (a := t) htne]
      _ = x := by simp
  right_inv x := by
    have htne : t ≠ 0 := ne_of_gt ht
    -- `(t * (t⁻¹ * x)) = (t * t⁻¹) * x = x`.
    calc
      (t : EReal) * (((t⁻¹ : ℝ) : EReal) * x) = ((t : EReal) * ((t⁻¹ : ℝ) : EReal)) * x := by
        simp [mul_assoc]
      _ = ((t * t⁻¹ : ℝ) : EReal) * x := by
        -- `↑(t * t⁻¹) = ↑t * ↑t⁻¹`.
        simp [mul_assoc]
      _ = (1 : EReal) * x := by
        simp [mul_inv_cancel₀ (a := t) htne]
      _ = x := by simp
  map_rel_iff' := by
    intro a b
    constructor
    · intro hab
      have ht_inv_nonneg : (0 : EReal) ≤ ((t⁻¹ : ℝ) : EReal) := by
        have : (0 : ℝ) ≤ t⁻¹ := le_of_lt (inv_pos_of_pos ht)
        exact_mod_cast this
      have hab' := mul_le_mul_of_nonneg_left hab ht_inv_nonneg
      have htne : t ≠ 0 := ne_of_gt ht
      -- Cancel the positive scalar on the left.
      have hab'' :
          (((t⁻¹ : ℝ) : EReal) * (t : EReal)) * a ≤ (((t⁻¹ : ℝ) : EReal) * (t : EReal)) * b := by
        simpa [mul_assoc] using hab'
      have hcoeff : ((t⁻¹ : ℝ) : EReal) * (t : EReal) = (1 : EReal) := by
        -- `↑(t⁻¹ * t) = ↑t⁻¹ * ↑t` and `t⁻¹ * t = 1` in `ℝ`.
        calc
          ((t⁻¹ : ℝ) : EReal) * (t : EReal) = ((t⁻¹ * t : ℝ) : EReal) := by
            simp
          _ = (1 : EReal) := by simp [inv_mul_cancel₀ (a := t) htne]
      simpa [hcoeff] using hab''
    · intro hab
      have ht_nonneg : (0 : EReal) ≤ (t : EReal) := by
        have : (0 : ℝ) ≤ t := le_of_lt ht
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_left hab ht_nonneg

/-- Rewrite `section14_posHomHull` as an indexed infimum over positive scalars. -/
lemma section14_posHomHull_eq_iInf (f : E → EReal) (x : E) :
    section14_posHomHull (E := E) f x =
      ⨅ t : {t : ℝ // 0 < t}, (t.1 : EReal) * f (t.1⁻¹ • x) := by
  classical
  have hset :
      {r : EReal | ∃ t : ℝ, 0 < t ∧ r = (t : EReal) * f (t⁻¹ • x)} =
        Set.range (fun t : {t : ℝ // 0 < t} => (t.1 : EReal) * f (t.1⁻¹ • x)) := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t.1, t.2, rfl⟩
  simp [section14_posHomHull, hset, sInf_range]

/-- Positive homogeneity of `section14_posHomHull` for strictly positive scalars. -/
lemma section14_posHomHull_smul (f : E → EReal) {t : ℝ} (ht : 0 < t) (x : E) :
    section14_posHomHull (E := E) f (t • x) =
      (t : EReal) * section14_posHomHull (E := E) f x := by
  classical
  -- Use the indexed `iInf` form and reindex by multiplication with `t`.
  let ι := {r : ℝ // 0 < r}
  have htne : t ≠ 0 := ne_of_gt ht
  have ht_pos : 0 < t := ht
  -- The equivalence `ι ≃ ι` given by multiplying by `t`.
  let e : ι ≃ ι :=
    { toFun := fun r => ⟨t * r.1, mul_pos ht_pos r.2⟩
      invFun := fun r => ⟨t⁻¹ * r.1, mul_pos (inv_pos_of_pos ht_pos) r.2⟩
      left_inv := by
        intro r
        ext
        field_simp [htne]
      right_inv := by
        intro r
        ext
        field_simp [htne] }
  -- Expand both sides as `iInf` over `ι`.
  have hk_tx :
      section14_posHomHull (E := E) f (t • x) =
        ⨅ r : ι, (r.1 : EReal) * f (r.1⁻¹ • (t • x)) := by
    simpa using (section14_posHomHull_eq_iInf (E := E) f (t • x))
  have hk_x :
      section14_posHomHull (E := E) f x =
        ⨅ r : ι, (r.1 : EReal) * f (r.1⁻¹ • x) := by
    simpa using (section14_posHomHull_eq_iInf (E := E) f x)
  -- Reindex the `iInf` on the LHS.
  have hk_tx' :
      section14_posHomHull (E := E) f (t • x) =
        ⨅ r : ι,
          ((t * r.1 : ℝ) : EReal) * f ((t * r.1)⁻¹ • (t • x)) := by
    -- Reindex by the equivalence `e`.
    let g0 : ι → EReal := fun r : ι => (r.1 : EReal) * f (r.1⁻¹ • (t • x))
    calc
      section14_posHomHull (E := E) f (t • x) = ⨅ r : ι, g0 r := by simpa [g0] using hk_tx
      _ = ⨅ r : ι, g0 (e r) := by simpa [g0] using (Equiv.iInf_comp (g := g0) e).symm
      _ = ⨅ r : ι, ((t * r.1 : ℝ) : EReal) * f ((t * r.1)⁻¹ • (t • x)) := by
            simp [g0, e]
  -- Simplify the argument and factor out the constant multiplier.
  have hk_tx'' :
      section14_posHomHull (E := E) f (t • x) =
        ⨅ r : ι, (t : EReal) * ((r.1 : EReal) * f (r.1⁻¹ • x)) := by
    -- The simplification `(t * r)⁻¹ • (t • x) = r⁻¹ • x` is purely algebraic.
    -- All multipliers are real coercions, so we can reassociate freely.
    refine hk_tx'.trans ?_
    refine iInf_congr fun r => ?_
    have htr_ne : t * r.1 ≠ 0 := by exact mul_ne_zero htne (ne_of_gt r.2)
    have hsmul :
        ((t * r.1)⁻¹ : ℝ) • (t • x) = (r.1⁻¹ : ℝ) • x := by
      -- `(t*r)⁻¹ • (t•x) = ((t*r)⁻¹*t) • x = r⁻¹ • x`.
      simp [smul_smul, htne]
    calc
      ((t * r.1 : ℝ) : EReal) * f ((t * r.1)⁻¹ • (t • x)) =
          ((t : ℝ) : EReal) * ((r.1 : ℝ) : EReal) * f (r.1⁻¹ • x) := by
            -- Rewrite the argument using `hsmul`, then factor `t * r` as a product in `EReal`.
            calc
              ((t * r.1 : ℝ) : EReal) * f ((t * r.1)⁻¹ • (t • x)) =
                  ((t * r.1 : ℝ) : EReal) * f ((r.1⁻¹ : ℝ) • x) := by
                    -- Rewrite the argument of `f`.
                    rw [hsmul]
              _ = (((t : ℝ) : EReal) * ((r.1 : ℝ) : EReal)) * f (r.1⁻¹ • x) := by
                    simp [EReal.coe_mul]
              _ = ((t : ℝ) : EReal) * ((r.1 : ℝ) : EReal) * f (r.1⁻¹ • x) := by
                    simp [mul_assoc]
      _ = (t : EReal) * ((r.1 : EReal) * f (r.1⁻¹ • x)) := by
            simp [mul_assoc]
  -- Use the order isomorphism to pull the constant multiplication outside the `iInf`.
  have :
      (t : EReal) * (⨅ r : ι, (r.1 : EReal) * f (r.1⁻¹ • x)) =
        ⨅ r : ι, (t : EReal) * ((r.1 : EReal) * f (r.1⁻¹ • x)) := by
    -- `OrderIso.map_iInf` transports `iInf` through the order isomorphism.
    change
      (section14_mulPosOrderIso (t := t) ht) (⨅ r : ι, (r.1 : EReal) * f (r.1⁻¹ • x)) =
        ⨅ r : ι, (section14_mulPosOrderIso (t := t) ht) ((r.1 : EReal) * f (r.1⁻¹ • x))
    exact OrderIso.map_iInf (section14_mulPosOrderIso (t := t) ht)
      (fun r : ι => (r.1 : EReal) * f (r.1⁻¹ • x))
  -- Finish by rewriting `k x` and using the two identities above.
  simpa [hk_x] using (hk_tx''.trans this.symm)

/-- The positively-homogeneous hull never exceeds the original function (take `t = 1`). -/
lemma section14_posHomHull_le (f : E → EReal) (x : E) : section14_posHomHull (E := E) f x ≤ f x := by
  have hxmem :
      f x ∈ {r : EReal | ∃ t : ℝ, 0 < t ∧ r = (t : EReal) * f (t⁻¹ • x)} := by
    refine ⟨(1 : ℝ), by norm_num, ?_⟩
    simp
  simpa [section14_posHomHull] using (sInf_le hxmem)

/-- A linear functional dominated by `f` is also dominated by the positively-homogeneous hull of `f`. -/
lemma section14_le_posHomHull_of_le (f : E → EReal) (φ : Module.Dual ℝ E)
    (hφ : ∀ x : E, (φ x : EReal) ≤ f x) :
    ∀ x : E, (φ x : EReal) ≤ section14_posHomHull (E := E) f x := by
  intro x
  -- Unfold the infimum definition and compare with each candidate value.
  refine le_sInf ?_
  intro r hr
  rcases hr with ⟨t, htpos, rfl⟩
  have htne : t ≠ 0 := ne_of_gt htpos
  have hdom : (φ (t⁻¹ • x) : EReal) ≤ f (t⁻¹ • x) := hφ (t⁻¹ • x)
  have htE : (0 : EReal) ≤ (t : EReal) := by
    simpa [EReal.coe_nonneg] using (show (0 : ℝ) ≤ t from le_of_lt htpos)
  have hmul :
      (t : EReal) * (φ (t⁻¹ • x) : EReal) ≤ (t : EReal) * f (t⁻¹ • x) :=
    mul_le_mul_of_nonneg_left hdom htE
  have hmul_lhs : (t : EReal) * (φ (t⁻¹ • x) : EReal) = (φ x : EReal) := by
    have hreal : t * φ (t⁻¹ • x) = φ x := by
      -- `φ (t⁻¹ • x) = t⁻¹ * φ x`, hence `t * (t⁻¹ * φ x) = φ x`.
      simp [map_smul, smul_eq_mul, htne]
    have hE : (t * φ (t⁻¹ • x) : EReal) = (φ x : EReal) := by
      exact_mod_cast hreal
    calc
      (t : EReal) * (φ (t⁻¹ • x) : EReal) = (t * φ (t⁻¹ • x) : EReal) := by simp
      _ = (φ x : EReal) := hE
  simpa using (hmul_lhs ▸ hmul)

/-- Pointwise domination by the positively-homogeneous hull of `f` is equivalent to domination by `f`. -/
lemma section14_le_posHomHull_iff_le (f : E → EReal) (φ : Module.Dual ℝ E) :
    (∀ x : E, (φ x : EReal) ≤ section14_posHomHull (E := E) f x) ↔ ∀ x : E, (φ x : EReal) ≤ f x := by
  constructor
  · intro h x
    exact (h x).trans (section14_posHomHull_le (E := E) (f := f) x)
  · intro h
    exact section14_le_posHomHull_of_le (E := E) (f := f) (φ := φ) h

/-- The `0`-sublevel set of `f*` is unchanged if `f` is replaced by its positively-homogeneous hull. -/
lemma section14_sublevelZero_fenchelConjugate_posHomHull_eq (f : E → EReal) :
    {φ : Module.Dual ℝ E |
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) (section14_posHomHull (E := E) f)
            φ ≤ (0 : EReal)} =
      {φ : Module.Dual ℝ E |
        fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal)} := by
  classical
  ext φ
  -- Use the pointwise domination characterization on both sides.
  simp [section14_fenchelConjugate_le_zero_iff, section14_le_posHomHull_iff_le]

/-- A basic scaling estimate for the positively-homogeneous hull:
choosing the same scaling parameter in the infimum gives `k (t • x) ≤ t * f x` for `t > 0`. -/
lemma section14_posHomHull_smul_le (f : E → EReal) {t : ℝ} (ht : 0 < t) (x : E) :
    section14_posHomHull (E := E) f (t • x) ≤ (t : EReal) * f x := by
  have hxmem :
      (t : EReal) * f (t⁻¹ • (t • x)) ∈
        {r : EReal | ∃ t' : ℝ, 0 < t' ∧ r = (t' : EReal) * f (t'⁻¹ • (t • x))} := by
    refine ⟨t, ht, rfl⟩
  have : section14_posHomHull (E := E) f (t • x) ≤ (t : EReal) * f (t⁻¹ • (t • x)) := by
    simpa [section14_posHomHull] using (sInf_le hxmem)
  simpa [inv_smul_smul₀ (ne_of_gt ht)] using this


end Section14
end Chap03
