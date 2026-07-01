/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part8
section Chap03
section Section14

open scoped Pointwise
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

-- The weak topology on the algebraic dual induced by evaluation (see `section14_part3`).
noncomputable local instance section14_instTopologicalSpace_dualWeak_part9 :
    TopologicalSpace (Module.Dual ℝ E) :=
  WeakBilin.instTopologicalSpace
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

/-- A canonical bilinear pairing on triples `(λ, x, μ)` induced by a bilinear pairing `p` on `E`:
`⟪(λ, x, μ), (λ★, x★, μ★)⟫ = λ * λ★ + p x x★ + μ * μ★`. -/
noncomputable def section14_triplePairing (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    (ℝ × E × ℝ) →ₗ[ℝ] (ℝ × E × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun z w => z.1 * w.1 + p z.2.1 w.2.1 + z.2.2 * w.2.2)
    (by
      intro z₁ z₂ w
      simp
      ring)
    (by
      intro c z w
      simp
      ring)
    (by
      intro z w₁ w₂
      simp
      ring)
    (by
      intro c z w
      simp
      ring)

@[simp] lemma section14_triplePairing_apply (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (z w : ℝ × E × ℝ) :
    section14_triplePairing (E := E) p z w = z.1 * w.1 + p z.2.1 w.2.1 + z.2.2 * w.2.2 :=
  rfl

@[simp] lemma section14_triplePairing_one_x_mu_negMuStar_xStar_negOne (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (x xStar : E) (μ μStar : ℝ) :
    section14_triplePairing (E := E) p (1, x, μ) (-μStar, xStar, -1) =
      (-μStar + p x xStar - μ) := by
  simp [section14_triplePairing, sub_eq_add_neg]

/-- A pointwise reformulation of `fenchelConjugateBilin p f x★ ≤ μ★`. -/
lemma section14_fenchelConjugate_le_iff_forall {F : Type*} [AddCommGroup F] [Module ℝ F]
    (p : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (f : E → EReal) (xStar : F) (μStar : EReal) :
    fenchelConjugateBilin p f xStar ≤ μStar ↔ ∀ x, (p x xStar : EReal) - f x ≤ μStar := by
  classical
  unfold fenchelConjugateBilin
  constructor
  · intro h x
    exact (sSup_le_iff).1 h _ ⟨x, rfl⟩
  · intro h
    refine (sSup_le_iff).2 ?_
    rintro _ ⟨x, rfl⟩
    exact h x

/-- In finite dimensions, `PointedCone.dual p s` is a closed set. -/
lemma section14_isClosed_pointedCone_dual {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℝ M] [Module ℝ N] [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousSMul ℝ N]
    [T2Space N] [FiniteDimensional ℝ N]
    (p : M →ₗ[ℝ] N →ₗ[ℝ] ℝ) (s : Set M) :
    IsClosed (PointedCone.dual (R := ℝ) p s : Set N) := by
  classical
  -- Unfold the dual as an intersection of closed half-spaces.
  have hrepr :
      (PointedCone.dual (R := ℝ) p s : Set N) =
        ⋂ x : M, ⋂ (_ : x ∈ s), {y : N | 0 ≤ (p x) y} := by
    ext y
    constructor
    · intro hy
      refine Set.mem_iInter.2 (fun x => Set.mem_iInter.2 (fun hx => ?_))
      exact (PointedCone.mem_dual).1 hy hx
    · intro hy
      refine (PointedCone.mem_dual).2 ?_
      intro x hx
      exact (Set.mem_iInter.1 (Set.mem_iInter.1 hy x) hx)
  -- Each half-space is closed.
  have hclosed_half : ∀ x : M, IsClosed {y : N | 0 ≤ (p x) y} := by
    intro x
    have hcont : Continuous fun y : N => (p x) y := by
      simpa using
        (LinearMap.continuous_of_finiteDimensional (f := (p x : N →ₗ[ℝ] ℝ)))
    simpa [Set.preimage, Set.mem_Ici] using (isClosed_Ici.preimage hcont)
  -- Intersections of closed sets are closed.
  simpa [hrepr] using
    (isClosed_iInter (fun x : M => isClosed_iInter (fun _ : x ∈ s => hclosed_half x)))

/-- Slice characterization for the lifted-epigraph cone (core of Theorem 14.4). -/
lemma section14_mem_dual_liftedEpigraphCone_slice_iff
    [TopologicalSpace E]
    {f : E → EReal} (hf : ProperConvexERealFunction (F := E) f)
    (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (xStar : E) (μStar : ℝ) :
    let q := section14_triplePairing (E := E) p
    let K : Set (ℝ × E × ℝ) :=
      ((ConvexCone.hull ℝ {z : ℝ × E × ℝ | ∃ x μ, z = (1, x, μ) ∧ f x ≤ (μ : EReal)} :
              ConvexCone ℝ (ℝ × E × ℝ)) :
          Set (ℝ × E × ℝ))
    (-μStar, xStar, -1) ∈ (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ)) ↔
      fenchelConjugateBilin p f xStar ≤ (μStar : EReal) := by
  classical
  intro q K
  -- Rewrite the dual membership as a family of `≤ 0` inequalities.
  have hdual_iff :
      (-μStar, xStar, -1) ∈ (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ)) ↔
        ∀ z, z ∈ K → q z (-μStar, xStar, -1) ≤ 0 := by
    constructor
    · intro hy z hz
      have h0 : 0 ≤ ((-q) z) (-μStar, xStar, -1) := (PointedCone.mem_dual).1 hy hz
      have : 0 ≤ -(q z (-μStar, xStar, -1)) := by simpa using h0
      exact (neg_nonneg).1 this
    · intro hy
      refine (PointedCone.mem_dual).2 ?_
      intro z hz
      have hz' : q z (-μStar, xStar, -1) ≤ 0 := hy z hz
      have : 0 ≤ -(q z (-μStar, xStar, -1)) := (neg_nonneg).2 hz'
      simpa using this

  -- Encode the generator set as a `Set.range` to use the "extend from generators" lemma.
  let I := {xμ : E × ℝ // f xμ.1 ≤ (xμ.2 : EReal)}
  let a : I → (ℝ × E × ℝ) := fun i => (1, i.1.1, i.1.2)
  have hgen :
      {z : ℝ × E × ℝ | ∃ x μ, z = (1, x, μ) ∧ f x ≤ (μ : EReal)} = Set.range a := by
    ext z
    constructor
    · rintro ⟨x, μ, rfl, hxμ⟩
      exact ⟨⟨(x, μ), hxμ⟩, rfl⟩
    · rintro ⟨⟨⟨x, μ⟩, hxμ⟩, rfl⟩
      exact ⟨x, μ, rfl, hxμ⟩
  have hK : K = ((ConvexCone.hull ℝ (Set.range a) : ConvexCone ℝ (ℝ × E × ℝ)) : Set _) := by
    simp [K, hgen]

  -- Replace the dual membership by inequalities on generators.
  have hgen_iff :
      (∀ z, z ∈ K → q z (-μStar, xStar, -1) ≤ 0) ↔
        ∀ i : I, q (a i) (-μStar, xStar, -1) ≤ 0 := by
    constructor
    · intro h i
      have : a i ∈ K := by
        -- `a i` is a generator, hence in the hull.
        have : a i ∈ {z : ℝ × E × ℝ | ∃ x μ, z = (1, x, μ) ∧ f x ≤ (μ : EReal)} := by
          rcases i with ⟨⟨x, μ⟩, hxμ⟩
          exact ⟨x, μ, rfl, hxμ⟩
        have : a i ∈ (ConvexCone.hull ℝ
              {z : ℝ × E × ℝ | ∃ x μ, z = (1, x, μ) ∧ f x ≤ (μ : EReal)} :
              ConvexCone ℝ (ℝ × E × ℝ)) := (ConvexCone.subset_hull this)
        simpa [K] using this
      exact h (a i) this
    · intro h z hz
      -- Extend `≤ 0` from generators to the whole hull.
      have hz' :
          z ∈ ((ConvexCone.hull ℝ (Set.range a) : ConvexCone ℝ (ℝ × E × ℝ)) : Set _) := by
        simpa [hK] using hz
      have hlin :
          ∀ t,
            t ∈ ((ConvexCone.hull ℝ (Set.range a) : ConvexCone ℝ (ℝ × E × ℝ)) : Set _) →
              (q.flip (-μStar, xStar, -1)) t ≤ 0 := by
        -- This is exactly `le_zero_on_hull_of_le_zero_on_generators` applied to `q.flip w`.
        refine le_zero_on_hull_of_le_zero_on_generators
          (E := (ℝ × E × ℝ)) (a := a) (φ := (q.flip (-μStar, xStar, -1))) ?_
        intro i
        -- Translate back to the required inequality on `q`.
        simpa [LinearMap.flip_apply] using (h i)
      simpa [LinearMap.flip_apply] using hlin z hz'

  -- Put it together and translate to the Fenchel conjugate.
  constructor
  · intro hy
    have hy' : ∀ i : I, q (a i) (-μStar, xStar, -1) ≤ 0 :=
      (hgen_iff).1 ((hdual_iff).1 hy)
    -- Use the generator inequality at `μ = f x` (as a real) for each `x`.
    have hpoint : ∀ x, (p x xStar : EReal) - f x ≤ (μStar : EReal) := by
      intro x
      -- Split into `f x = ⊤` and `f x = r`.
      cases hfx : f x using EReal.rec with
      | bot =>
          -- Properness excludes `⊥`.
          exact (False.elim ((hf.1.1 x) hfx))
      | top =>
          -- `(p x x★) - ⊤ = ⊥`.
          simp
      | coe r =>
          -- Use the generator `(1, x, r)`.
          have hqle :
              q (a ⟨(x, r), by simp [hfx]⟩) (-μStar, xStar, -1) ≤ 0 :=
            hy' ⟨(x, r), by simp [hfx]⟩
          have hreal : p x xStar - r ≤ μStar := by
            -- Expand and rearrange.
            have : (-μStar + p x xStar - r) ≤ 0 := by
              simpa [q, a, section14_triplePairing_one_x_mu_negMuStar_xStar_negOne] using hqle
            linarith
          have hcoe : ((p x xStar - r : ℝ) : EReal) ≤ (μStar : EReal) :=
            EReal.coe_le_coe hreal
          simpa [hfx] using hcoe
    exact (section14_fenchelConjugate_le_iff_forall (E := E) (p := p) (f := f)
        (xStar := xStar) (μStar := (μStar : EReal))).2 hpoint
  · intro hconj
    have hpoint : ∀ x, (p x xStar : EReal) - f x ≤ (μStar : EReal) :=
      (section14_fenchelConjugate_le_iff_forall (E := E) (p := p) (f := f)
        (xStar := xStar) (μStar := (μStar : EReal))).1 hconj
    -- Prove the generator inequalities, then extend to the whole hull.
    have hy' : ∀ i : I, q (a i) (-μStar, xStar, -1) ≤ 0 := by
      rintro ⟨⟨x, μ⟩, hxμ⟩
      -- Use monotonicity of subtraction in the second argument: `f x ≤ μ`.
      have hsub :
          (p x xStar : EReal) - (μ : EReal) ≤ (p x xStar : EReal) - f x := by
        -- `x - z ≤ y - t` whenever `x ≤ y` and `t ≤ z`.
        simpa using (EReal.sub_le_sub (le_rfl : (p x xStar : EReal) ≤ (p x xStar : EReal)) hxμ)
      have hle : (p x xStar : EReal) - (μ : EReal) ≤ (μStar : EReal) :=
        (hsub.trans (hpoint x))
      have hreal : p x xStar - μ ≤ μStar := by
        -- Convert the `EReal` inequality to a real inequality.
        have hcoe : ((p x xStar - μ : ℝ) : EReal) ≤ (μStar : EReal) := by
          simpa using hle
        exact (EReal.coe_le_coe_iff).1 hcoe
      -- Expand `q` and conclude.
      have : (-μStar + p x xStar - μ) ≤ 0 := by linarith
      simpa [q, a, section14_triplePairing_one_x_mu_negMuStar_xStar_negOne] using this
    -- Extend generator inequalities to all of `K`.
    have hy : ∀ z, z ∈ K → q z (-μStar, xStar, -1) ≤ 0 :=
      (hgen_iff).2 hy'
    exact (hdual_iff).2 hy

/-- Key inclusion for Theorem 14.3: any functional nonpositive on the closed cone generated by the
`0`-sublevel set `{x | f x ≤ 0}` lies in the closed cone generated by the `0`-sublevel set of the
Fenchel conjugate `{φ | f* φ ≤ 0}`. -/
lemma section14_polarCone_closure_coneHull_sublevelZero_subset_closure_coneHull_sublevelZero_fenchelConjugate
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) (hInf : sInf (Set.range f) < (0 : EReal)) :
    polarCone (E := E)
        (closure
          ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E)) ⊆
      closure
        ((ConvexCone.hull ℝ
              {φ : Module.Dual ℝ E |
                fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤
                  (0 : EReal)} :
              ConvexCone ℝ (Module.Dual ℝ E)) :
          Set (Module.Dual ℝ E)) := by
  classical
  -- Notation for the primal/dual `0`-sublevel generators.
  set S : Set E := {x : E | f x ≤ (0 : EReal)}
  set T : Set (Module.Dual ℝ E) :=
    {φ : Module.Dual ℝ E |
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal)}

  intro φ hφ
  have hφS : φ ∈ polarCone (E := E) S :=
    section14_mem_polarCone_of_mem_polarCone_closure_coneHull (E := E) (S := S) (φ := φ)
      (by simpa [S] using hφ)
  have hmem :
      φ ∈
        closure
          ((ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) :
            Set (Module.Dual ℝ E)) :=
    section14_polarCone_sublevelZero_subset_closure_coneHull_sublevelZero_fenchelConjugate
      (E := E) (f := f) hf hf_closed hf0 hf0_ltTop hInf (by simpa [S] using hφS)
  simpa [T] using hmem

/-- Theorem 14.3. Let `f` be a closed proper convex function such that `f 0 > 0 > inf f`.
Then the closed convex cones generated by the sublevel sets `{x | f x ≤ 0}` and
`{x★ | f* x★ ≤ 0}` are polar to each other, where `f*` denotes the Fenchel–Legendre conjugate
of `f` with respect to the evaluation pairing. -/
theorem polar_closure_coneHull_sublevelZero_eq_closure_coneHull_sublevelZero_fenchelConjugate
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) (hInf : sInf (Set.range f) < (0 : EReal)) :
    polarCone (E := E)
        (closure
          ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E)) =
      closure
        ((ConvexCone.hull ℝ
              {φ : Module.Dual ℝ E |
                fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤
                  (0 : EReal)} :
              ConvexCone ℝ (Module.Dual ℝ E)) :
          Set (Module.Dual ℝ E)) ∧
      PointedCone.dual (R := ℝ)
          ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
          (closure
            ((ConvexCone.hull ℝ
                  {φ : Module.Dual ℝ E |
                    fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤
                      (0 : EReal)} :
                  ConvexCone ℝ (Module.Dual ℝ E)) :
              Set (Module.Dual ℝ E))) =
        closure
          ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E) := by
  classical
  -- Notation for the primal/dual `0`-sublevel generators.
  set S : Set E := {x : E | f x ≤ (0 : EReal)}
  set T : Set (Module.Dual ℝ E) :=
    {φ : Module.Dual ℝ E |
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal)}

  -- The textbook argument starts by observing that both `S` and `T` are nonempty.
  have hSne : S.Nonempty := section14_sublevelZero_nonempty (F := E) (f := f) hInf
  have hTsubset :
      T ⊆
        polarCone (E := E) ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E) := by
    simpa [T, S] using
      (section14_sublevel_fenchelConjugate_le_zero_subset_polarCone_hull_sublevelZero
        (E := E) (f := f))

  -- The inclusion `T ⊆ polarCone (coneHull S)` propagates to the closed convex cone generated by `T`,
  -- using that `polarCone (coneHull S)` is closed (Text 14.0.7).
  let K : ConvexCone ℝ E := ConvexCone.hull ℝ S
  let Kstar : ConvexCone ℝ (Module.Dual ℝ E) := ConvexCone.hull ℝ T
  have hKne : (K : Set E).Nonempty := by
    rcases hSne with ⟨x, hx⟩
    exact ⟨x, ConvexCone.subset_hull (R := ℝ) (s := S) hx⟩
  have hPolK_closed : IsClosed (polarCone (E := E) (K : Set E)) :=
    (isClosed_convex_polarCone_and_zero_mem (E := E) (K := K)).1
  have hKstar_closure_subset_polK :
      closure (Kstar : Set (Module.Dual ℝ E)) ⊆ polarCone (E := E) (K : Set E) := by
    refine
      section14_closure_coneHull_subset_polarCone_of_subset (E := E) (K := (K : Set E))
        (T := T) ?_ hPolK_closed
    simpa [K] using hTsubset

  have hPolKcl_subset_polK :
      polarCone (E := E) (closure (K : Set E)) ⊆ polarCone (E := E) (K : Set E) := by
    intro φ hφ
    refine (mem_polarCone_iff (E := E) (K := (K : Set E)) (φ := φ)).2 ?_
    intro x hx
    have hxcl : x ∈ closure (K : Set E) := subset_closure hx
    exact (mem_polarCone_iff (E := E) (K := closure (K : Set E)) (φ := φ)).1 hφ x hxcl

  have hPolK_subset_polKcl :
      polarCone (E := E) (K : Set E) ⊆ polarCone (E := E) (closure (K : Set E)) := by
    intro φ hφ
    refine (mem_polarCone_iff (E := E) (K := closure (K : Set E)) (φ := φ)).2 ?_
    intro x hx
    have hcont : Continuous fun x : E => φ x := by
      simpa using
        (LinearMap.continuous_of_finiteDimensional (f := (φ : E →ₗ[ℝ] ℝ)))
    have hclosed : IsClosed {x : E | φ x ≤ 0} := by
      simpa [Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)
    have hsubset : (K : Set E) ⊆ {x : E | φ x ≤ 0} := by
      intro y hy
      exact (mem_polarCone_iff (E := E) (K := (K : Set E)) (φ := φ)).1 hφ y hy
    have hx' : x ∈ {x : E | φ x ≤ 0} := (closure_minimal hsubset hclosed) hx
    simpa using hx'

  have hKstar_closure_subset_polKcl :
      closure (Kstar : Set (Module.Dual ℝ E)) ⊆ polarCone (E := E) (closure (K : Set E)) := by
    intro φ hφ
    have : φ ∈ polarCone (E := E) (K : Set E) := hKstar_closure_subset_polK hφ
    exact hPolK_subset_polKcl this

  have hclK_subset_polar_clKstar :
      closure (K : Set E) ⊆
        (PointedCone.dual (R := ℝ)
              ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
              (closure (Kstar : Set (Module.Dual ℝ E))) : Set E) := by
    -- Use antitonicity of the polar map on the dual side, together with the bipolar theorem for `K`.
    have hpol :
        (PointedCone.dual (R := ℝ)
              ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
              (polarCone (E := E) (closure (K : Set E))) : Set E) ⊆
          (PointedCone.dual (R := ℝ)
              ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
              (closure (Kstar : Set (Module.Dual ℝ E))) : Set E) := by
      intro x hx
      refine (section14_mem_dual_flip_eval_iff_forall_le_zero (E := E)
            (S := closure (Kstar : Set (Module.Dual ℝ E))) (x := x)).2 ?_
      intro ψ hψ
      -- Since `ψ ∈ closure Kstar ⊆ polarCone (closure K)`, apply `hx` with this `ψ`.
      have hψpol : ψ ∈ polarCone (E := E) (closure (K : Set E)) := hKstar_closure_subset_polKcl hψ
      exact
        (section14_mem_dual_flip_eval_iff_forall_le_zero (E := E)
              (S := polarCone (E := E) (closure (K : Set E))) (x := x)).1 hx ψ hψpol
    -- Identify the polar of the polar cone of `K` with `closure K`.
    have hKne_cl : ((K.closure : ConvexCone ℝ E) : Set E).Nonempty := by
      simpa [ConvexCone.coe_closure] using hKne.closure
    have hbip :
        (PointedCone.dual (R := ℝ)
              ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
              (polarCone (E := E) ((K.closure : ConvexCone ℝ E) : Set E)) : Set E) =
          closure (K : Set E) := by
      simpa [ConvexCone.coe_closure] using
        (polarCone_polar_eq_closure (E := E) (K := K.closure) hKne_cl)
    intro x hx
    -- Rewrite `hx` using the bipolar identity and then apply `hpol`.
    have hx' :
          x ∈
            (PointedCone.dual (R := ℝ)
                  ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
                  (polarCone (E := E) ((K.closure : ConvexCone ℝ E) : Set E)) : Set E) := by
        -- Avoid unfolding the membership predicate; rewrite the goal at the set level.
        rw [hbip]
        exact hx
    exact hpol hx'

  refine And.intro ?_ ?_
  · -- Equality of polar cones.
    refine subset_antisymm ?_ ?_
    · -- Missing direction: `polarCone (closure K) ⊆ closure (coneHull T)`.
      simpa [Kstar, K] using
        section14_polarCone_closure_coneHull_sublevelZero_subset_closure_coneHull_sublevelZero_fenchelConjugate
          (E := E) (f := f) hf hf_closed hf0 hf0_ltTop hInf
    · -- Proven inclusion.
      simpa [Kstar, K] using hKstar_closure_subset_polKcl
  · -- Equality of primal cones follows from the bipolar identity and the first equality.
    have hPolEq :
        polarCone (E := E) (closure (K : Set E)) = closure (Kstar : Set (Module.Dual ℝ E)) := by
      ext φ
      constructor <;> intro hφ
      · have : φ ∈ closure (Kstar : Set (Module.Dual ℝ E)) := by
          have hsub :
              polarCone (E := E) (closure (K : Set E)) ⊆
                closure (Kstar : Set (Module.Dual ℝ E)) := by
              simpa [Kstar, K] using
                section14_polarCone_closure_coneHull_sublevelZero_subset_closure_coneHull_sublevelZero_fenchelConjugate
                  (E := E) (f := f) hf hf_closed hf0 hf0_ltTop hInf
          exact hsub hφ
        exact this
      · have : φ ∈ polarCone (E := E) (closure (K : Set E)) := by
          have hsub :
              closure (Kstar : Set (Module.Dual ℝ E)) ⊆ polarCone (E := E) (closure (K : Set E)) :=
            by
              simpa [Kstar, K] using hKstar_closure_subset_polKcl
          exact hsub hφ
        exact this
    have hKne_cl : ((K.closure : ConvexCone ℝ E) : Set E).Nonempty := by
      simpa [ConvexCone.coe_closure] using hKne.closure
    have hbip :
        (PointedCone.dual (R := ℝ)
              ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
              (polarCone (E := E) (closure (K : Set E))) : Set E) =
          closure (K : Set E) := by
      simpa [ConvexCone.coe_closure, closure_closure] using
        (polarCone_polar_eq_closure (E := E) (K := K.closure) hKne_cl)
    -- Rewrite the left-hand side using `hPolEq` and apply the bipolar identity.
    simpa [Kstar, K] using (by
      -- `rw` is more reliable than `simp` for rewriting under `PointedCone.dual`.
      rw [hPolEq.symm]
      exact hbip)

/-- Coordinate involution used in Theorem 14.4: `swapNeg (λ, x, μ) = (-μ, x, -λ)`. -/
def section14_swapNegₗ (E : Type*) [AddCommGroup E] [Module ℝ E] :
    (ℝ × E × ℝ) →ₗ[ℝ] (ℝ × E × ℝ) where
  toFun z := (-z.2.2, z.2.1, -z.1)
  map_add' z w := by
    ext <;> simp <;> abel
  map_smul' c z := by
    ext <;> simp

@[simp] lemma section14_swapNegₗ_apply (z : ℝ × E × ℝ) :
    section14_swapNegₗ E z = (-z.2.2, z.2.1, -z.1) :=
  rfl

/-- The linear equivalence associated to `section14_swapNegₗ`. -/
def section14_swapNeg (E : Type*) [AddCommGroup E] [Module ℝ E] :
    (ℝ × E × ℝ) ≃ₗ[ℝ] (ℝ × E × ℝ) where
  toLinearMap := section14_swapNegₗ E
  invFun z := (-z.2.2, z.2.1, -z.1)
  left_inv z := by
    ext <;> simp
  right_inv z := by
    ext <;> simp

@[simp] lemma section14_swapNeg_apply (z : ℝ × E × ℝ) :
    section14_swapNeg E z = (-z.2.2, z.2.1, -z.1) :=
  rfl

@[simp] lemma section14_swapNeg_swapNeg (z : ℝ × E × ℝ) :
    section14_swapNeg E (section14_swapNeg E z) = z := by
  ext <;> simp [section14_swapNeg]

/-- Elements of the dual of the lifted-epigraph cone have nonpositive last coordinate. -/
lemma section14_dual_liftedEpigraphCone_last_nonpos
    [TopologicalSpace E]
    {f : E → EReal} (hf : ProperConvexERealFunction (F := E) f)
    (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    let q := section14_triplePairing (E := E) p
    let K : Set (ℝ × E × ℝ) :=
      ((ConvexCone.hull ℝ {z : ℝ × E × ℝ | ∃ x μ, z = (1, x, μ) ∧ f x ≤ (μ : EReal)} :
              ConvexCone ℝ (ℝ × E × ℝ)) :
          Set (ℝ × E × ℝ))
    ∀ w, w ∈ (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ)) → w.2.2 ≤ 0 := by
  classical
  intro q K w hw
  rcases hf.1.2 with ⟨x0, hx0neTop⟩
  have hx0lt : f x0 < ⊤ := lt_top_iff_ne_top.2 hx0neTop
  rcases section14_eq_coe_of_lt_top (z := f x0) hx0lt (hf.1.1 x0) with ⟨r0, hr0⟩

  have hineq : ∀ μ : ℝ, r0 ≤ μ → q (1, x0, μ) w ≤ 0 := by
    intro μ hμ
    have hxμ : f x0 ≤ (μ : EReal) := by
      have : (r0 : EReal) ≤ (μ : EReal) := EReal.coe_le_coe hμ
      simpa [hr0] using this
    have hgen :
        (1, x0, μ) ∈
          {z : ℝ × E × ℝ | ∃ x μ, z = (1, x, μ) ∧ f x ≤ (μ : EReal)} :=
      ⟨x0, μ, rfl, hxμ⟩
    have hKmem : (1, x0, μ) ∈ K := by
      have :
          (1, x0, μ) ∈
            (ConvexCone.hull ℝ
                  {z : ℝ × E × ℝ | ∃ x μ, z = (1, x, μ) ∧ f x ≤ (μ : EReal)} :
                ConvexCone ℝ (ℝ × E × ℝ)) :=
        ConvexCone.subset_hull hgen
      simpa [K] using this
    have h0 : 0 ≤ ((-q) (1, x0, μ)) w := (PointedCone.mem_dual).1 hw hKmem
    have : 0 ≤ -(q (1, x0, μ) w) := by simpa using h0
    exact (neg_nonneg).1 this

  have hnat : ∀ n : ℕ, (n : ℝ) * w.2.2 ≤ -(q (1, x0, r0) w) := by
    intro n
    have hrle : r0 ≤ r0 + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
    have hle : q (1, x0, r0 + (n : ℝ)) w ≤ 0 := hineq (r0 + (n : ℝ)) hrle
    have hrewrite :
        q (1, x0, r0 + (n : ℝ)) w = q (1, x0, r0) w + (n : ℝ) * w.2.2 := by
      simp [q, section14_triplePairing_apply, add_mul]
      ring
    have : q (1, x0, r0) w + (n : ℝ) * w.2.2 ≤ 0 := by simpa [hrewrite] using hle
    linarith

  exact section14_real_nonpos_of_nat_mul_le (r := w.2.2) (C := -(q (1, x0, r0) w)) hnat

/-- Cone-slicing reconstruction for the lifted-epigraph polar (reverse inclusion in Theorem 14.4).

If `swapNeg z` lies in the polar of the lifted-epigraph cone, then `z` lies in the closure of
the cone generated by the epigraph of the Fenchel conjugate. -/
lemma section14_swapNeg_preimage_dual_subset_closure_Kstar
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : ProperConvexERealFunction (F := E) f)
    (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hdom : ∃ x0 : E, ∃ μ0 : ℝ, fenchelConjugateBilin p f x0 ≤ (μ0 : EReal)) :
    let q := section14_triplePairing (E := E) p
    let K : Set (ℝ × E × ℝ) :=
      ((ConvexCone.hull ℝ {z : ℝ × E × ℝ | ∃ x μ, z = (1, x, μ) ∧ f x ≤ (μ : EReal)} :
              ConvexCone ℝ (ℝ × E × ℝ)) :
          Set (ℝ × E × ℝ))
    let Kstar : Set (ℝ × E × ℝ) :=
      ((ConvexCone.hull ℝ
              {z : ℝ × E × ℝ |
                ∃ x μ, z = (1, x, μ) ∧ fenchelConjugateBilin p f x ≤ (μ : EReal)} :
              ConvexCone ℝ (ℝ × E × ℝ)) :
          Set (ℝ × E × ℝ))
    {z : ℝ × E × ℝ |
        section14_swapNeg E z ∈ (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ))} ⊆
      closure Kstar := by
  classical
  intro q K Kstar z hz
  let Dcone : PointedCone ℝ (ℝ × E × ℝ) := PointedCone.dual (R := ℝ) (-q) K
  have hzD : section14_swapNeg E z ∈ (Dcone : Set (ℝ × E × ℝ)) := by
    simpa [Dcone] using hz

  have hR_add :
      ∀ {z₁ z₂ : ℝ × E × ℝ},
        section14_swapNeg E z₁ ∈ (Dcone : Set (ℝ × E × ℝ)) →
          section14_swapNeg E z₂ ∈ (Dcone : Set (ℝ × E × ℝ)) →
            section14_swapNeg E (z₁ + z₂) ∈ (Dcone : Set (ℝ × E × ℝ)) := by
    intro z₁ z₂ hz₁ hz₂
    have hadd : section14_swapNeg E z₁ + section14_swapNeg E z₂ ∈ Dcone := Dcone.add_mem hz₁ hz₂
    have hswap :
        section14_swapNeg E (z₁ + z₂) = section14_swapNeg E z₁ + section14_swapNeg E z₂ := by
      simpa [section14_swapNeg] using (section14_swapNegₗ E).map_add z₁ z₂
    exact hswap.symm ▸ hadd

  have hR_smul :
      ∀ {c : ℝ} (hc : 0 ≤ c) {z : ℝ × E × ℝ},
        section14_swapNeg E z ∈ (Dcone : Set (ℝ × E × ℝ)) →
          section14_swapNeg E (c • z) ∈ (Dcone : Set (ℝ × E × ℝ)) := by
    intro c hc z hz
    have hsmul' : c • section14_swapNeg E z ∈ Dcone := Dcone.smul_mem hc hz
    have hswap : section14_swapNeg E (c • z) = c • section14_swapNeg E z := by
      ext <;> simp [section14_swapNeg_apply]
    simpa [hswap] using hsmul'

  have hz1nonneg : 0 ≤ z.1 := by
    have hwlast : (section14_swapNeg E z).2.2 ≤ 0 := by
      have hlast :
          ∀ w,
            w ∈ (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ)) → w.2.2 ≤ 0 := by
        simpa [q, K] using (section14_dual_liftedEpigraphCone_last_nonpos (E := E) (f := f) hf p)
      have hwmem :
          section14_swapNeg E z ∈
            (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ)) := by
        simpa [Dcone] using hzD
      exact hlast (section14_swapNeg E z) hwmem
    have : -z.1 ≤ 0 := by simpa [section14_swapNeg_apply] using hwlast
    exact (neg_nonpos).1 this

  rcases hdom with ⟨x0, μ0, hx0μ0⟩
  set z0 : ℝ × E × ℝ := (1, x0, μ0)
  have hz0D : section14_swapNeg E z0 ∈ (Dcone : Set (ℝ × E × ℝ)) := by
    have hs :
        (-μ0, x0, -1) ∈ (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ)) ↔
          fenchelConjugateBilin p f x0 ≤ (μ0 : EReal) := by
      simpa [q, K] using (section14_mem_dual_liftedEpigraphCone_slice_iff (E := E) (f := f) hf p x0 μ0)
    have : (-μ0, x0, -1) ∈ (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ)) :=
      hs.2 hx0μ0
    simpa [z0, Dcone, section14_swapNeg_apply] using this

  have hz_pos_mem_Kstar :
      ∀ {z : ℝ × E × ℝ},
        section14_swapNeg E z ∈ (Dcone : Set (ℝ × E × ℝ)) → 0 < z.1 → z ∈ Kstar := by
    intro z hz hz1pos
    let c : ℝ := 1 / z.1
    have hcpos : 0 < c := one_div_pos.2 hz1pos
    have hc : 0 ≤ c := le_of_lt hcpos
    have hczD : section14_swapNeg E (c • z) ∈ (Dcone : Set (ℝ × E × ℝ)) := hR_smul hc hz
    have hfst : (c • z).1 = 1 := by
      have hz1ne : z.1 ≠ 0 := ne_of_gt hz1pos
      simp [c, hz1ne]
    have hfst' : c * z.1 = 1 := by
      simpa using hfst
    have hs :
        (-((c • z).2.2), (c • z).2.1, -1) ∈
            (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ)) ↔
          fenchelConjugateBilin p f (c • z).2.1 ≤ ((c • z).2.2 : EReal) := by
      simpa [q, K] using
        (section14_mem_dual_liftedEpigraphCone_slice_iff (E := E) (f := f) hf p (c • z).2.1 (c • z).2.2)
    have hmemSlice :
        (-((c • z).2.2), (c • z).2.1, -1) ∈
          (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ)) := by
      simpa [Dcone, section14_swapNeg_apply, hfst'] using hczD
    have hconj :
        fenchelConjugateBilin p f (c • z).2.1 ≤ ((c • z).2.2 : EReal) :=
      (hs.1 hmemSlice)
    have hgen :
        (c • z) ∈
          {z : ℝ × E × ℝ |
            ∃ x μ, z = (1, x, μ) ∧ fenchelConjugateBilin p f x ≤ (μ : EReal)} := by
      refine ⟨(c • z).2.1, (c • z).2.2, ?_, hconj⟩
      ext <;> simp [hfst]
    have hczKstar : (c • z) ∈ Kstar := by
      have :
          (c • z) ∈
            (ConvexCone.hull ℝ
                  {z : ℝ × E × ℝ |
                    ∃ x μ, z = (1, x, μ) ∧ fenchelConjugateBilin p f x ≤ (μ : EReal)} :
                ConvexCone ℝ (ℝ × E × ℝ)) :=
        ConvexCone.subset_hull hgen
      simpa [Kstar] using this
    have hscale : z.1 • (c • z) = z := by
      have hz1ne : z.1 ≠ 0 := ne_of_gt hz1pos
      ext <;> simp [c, hz1ne, smul_smul]
    -- Scale back into `Kstar` using the cone property.
    have hzCone :
        z.1 • (c • z) ∈
          (ConvexCone.hull ℝ
                {z : ℝ × E × ℝ |
                  ∃ x μ, z = (1, x, μ) ∧ fenchelConjugateBilin p f x ≤ (μ : EReal)} :
              ConvexCone ℝ (ℝ × E × ℝ)) := by
      have hczCone :
          (c • z) ∈
            (ConvexCone.hull ℝ
                  {z : ℝ × E × ℝ |
                    ∃ x μ, z = (1, x, μ) ∧ fenchelConjugateBilin p f x ≤ (μ : EReal)} :
                ConvexCone ℝ (ℝ × E × ℝ)) := by
        simpa [Kstar] using hczKstar
      exact
        (ConvexCone.hull ℝ
              {z : ℝ × E × ℝ |
                ∃ x μ, z = (1, x, μ) ∧ fenchelConjugateBilin p f x ≤ (μ : EReal)}).smul_mem hz1pos
          hczCone
    simpa [Kstar, hscale] using hzCone

  by_cases hz1pos : 0 < z.1
  · have hzKstar : z ∈ Kstar := hz_pos_mem_Kstar (z := z) hzD hz1pos
    exact subset_closure hzKstar
  · have hz1zero : z.1 = 0 := le_antisymm (le_of_not_gt hz1pos) hz1nonneg
    -- Approximate `z` by points with positive first coordinate.
    let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have ht0 : Filter.Tendsto t Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa [t] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hmem : ∀ n : ℕ, z + t n • z0 ∈ Kstar := by
      intro n
      have htpos : 0 < t n := by
        have : 0 < ((n : ℝ) + 1) := by positivity
        simpa [t] using (one_div_pos.2 this)
      have htnonneg : 0 ≤ t n := le_of_lt htpos
      have hztnD :
          section14_swapNeg E (z + t n • z0) ∈ (Dcone : Set (ℝ × E × ℝ)) := by
        have htD : section14_swapNeg E (t n • z0) ∈ (Dcone : Set (ℝ × E × ℝ)) :=
          hR_smul htnonneg (z := z0) hz0D
        exact hR_add (z₁ := z) (z₂ := t n • z0) hzD htD
      have hfstpos : 0 < (z + t n • z0).1 := by
        simpa [z0, hz1zero, t, add_assoc, add_comm, add_left_comm, mul_assoc] using htpos
      exact hz_pos_mem_Kstar (z := z + t n • z0) hztnD hfstpos
    have hcont : Continuous fun r : ℝ => z + r • z0 := by
      exact continuous_const.add (continuous_id.smul continuous_const)
    have htend :
        Filter.Tendsto (fun n : ℕ => z + t n • z0) Filter.atTop (𝓝 z) := by
      have :
          Filter.Tendsto (fun r : ℝ => z + r • z0) (𝓝 (0 : ℝ)) (𝓝 (z + (0 : ℝ) • z0)) := by
        simpa using (hcont.tendsto 0)
      have htend' :
          Filter.Tendsto (fun n : ℕ => z + t n • z0) Filter.atTop (𝓝 (z + (0 : ℝ) • z0)) :=
        this.comp ht0
      simpa using htend'
    exact mem_closure_of_tendsto htend (Filter.Eventually.of_forall hmem)

/-- Theorem 14.4. Let `f` be a closed proper convex function on `ℝⁿ`. Let `K` be the convex cone
generated by points `(1, x, μ) ∈ ℝ × ℝⁿ × ℝ` such that `μ ≥ f x`, and let `K★` be the convex cone
generated by points `(1, x★, μ★)` such that `μ★ ≥ f★ x★`, where `f★` is the Fenchel–Legendre
conjugate of `f`. Then

`cl K★ = { (λ★, x★, μ★) | (-μ★, x★, -λ★) ∈ Kᵒ }`.

In this formalization, `f★` is `fenchelConjugateBilin p f` for a chosen bilinear pairing `p` on `E`,
and `Kᵒ` is modeled as `PointedCone.dual (-q) K` for a chosen bilinear pairing `q` on
`ℝ × E × ℝ`. -/
theorem closure_coneHull_liftedEpigraph_fenchelConjugate_eq_setOf_swapNeg_mem_dual
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E]
    {f : E → EReal} (hf : ProperConvexERealFunction (F := E) f)
    (_hf_closed : LowerSemicontinuous f) (p : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (q : (ℝ × E × ℝ) →ₗ[ℝ] (ℝ × E × ℝ) →ₗ[ℝ] ℝ)
    (hq : q = section14_triplePairing (E := E) p) :
    (∃ x0 : E, ∃ μ0 : ℝ, fenchelConjugateBilin p f x0 ≤ (μ0 : EReal)) →
    let K : Set (ℝ × E × ℝ) :=
      ((ConvexCone.hull ℝ {z : ℝ × E × ℝ | ∃ x μ, z = (1, x, μ) ∧ f x ≤ (μ : EReal)} :
              ConvexCone ℝ (ℝ × E × ℝ)) :
          Set (ℝ × E × ℝ))
    let Kstar : Set (ℝ × E × ℝ) :=
      ((ConvexCone.hull ℝ
              {z : ℝ × E × ℝ |
                ∃ x μ, z = (1, x, μ) ∧ fenchelConjugateBilin p f x ≤ (μ : EReal)} :
              ConvexCone ℝ (ℝ × E × ℝ)) :
          Set (ℝ × E × ℝ))
    closure Kstar =
      {z : ℝ × E × ℝ |
        (-z.2.2, z.2.1, -z.1) ∈ (PointedCone.dual (R := ℝ) (-q) K : Set (ℝ × E × ℝ))} := by
  classical
  intro hdom K Kstar
  subst hq
  /-
  The textbook proof identifies the slice `{(-μ★, x★, -1)}` of the polar cone of `K` with the
  epigraph of the Fenchel conjugate `f★`, and then uses a cone-slicing/closure argument to rebuild
  the full dual cone from that slice.

  In Lean, carrying out this proof requires a compatibility hypothesis relating the bilinear
  pairing `q` on `ℝ × E × ℝ` to the bilinear pairing `p` used to define `fenchelConjugateBilin p f`.
  Without such a hypothesis, the statement cannot hold for arbitrary `q` (e.g. take `q = 0`,
  giving `PointedCone.dual (-q) K = ⊤`).
  -/
  -- One inclusion (`⊆`): the closed cone generated by the epigraph of `f*` maps into the dual of
  -- the lifted epigraph cone of `f` via `swapNeg`.
  have hsubset₁ :
      closure Kstar ⊆
        {z : ℝ × E × ℝ |
          (-z.2.2, z.2.1, -z.1) ∈
            (PointedCone.dual (R := ℝ) (-(section14_triplePairing (E := E) p)) K :
              Set (ℝ × E × ℝ))} := by
    -- Let `D` be the dual cone and consider its preimage under `swapNeg`.
    let Dcone : PointedCone ℝ (ℝ × E × ℝ) :=
      PointedCone.dual (R := ℝ) (-(section14_triplePairing (E := E) p)) K
    let D : Set (ℝ × E × ℝ) := (Dcone : Set (ℝ × E × ℝ))
    have hD_closed : IsClosed D :=
      section14_isClosed_pointedCone_dual (p := (-(section14_triplePairing (E := E) p))) (s := K)
    have hcont_swap : Continuous fun z : (ℝ × E × ℝ) => section14_swapNeg E z := by
      change Continuous fun z : (ℝ × E × ℝ) => section14_swapNegₗ E z
      exact LinearMap.continuous_of_finiteDimensional (f := section14_swapNegₗ E)
    have hR_closed : IsClosed {z : ℝ × E × ℝ | section14_swapNeg E z ∈ D} := by
      simpa [Set.preimage, D] using (hD_closed.preimage hcont_swap)
    have hKstar_subset : Kstar ⊆ {z : ℝ × E × ℝ | section14_swapNeg E z ∈ D} := by
      -- Build a convex cone structure on the preimage, so we can use `ConvexCone.hull_le_iff`.
      let Rcone : ConvexCone ℝ (ℝ × E × ℝ) :=
        { carrier := {z : ℝ × E × ℝ | section14_swapNeg E z ∈ D}
          add_mem' := by
            intro z₁ hz₁ z₂ hz₂
            have hadd :
                section14_swapNeg E z₁ + section14_swapNeg E z₂ ∈ Dcone :=
              Dcone.add_mem hz₁ hz₂
            have hswap :
                section14_swapNeg E (z₁ + z₂) = section14_swapNeg E z₁ + section14_swapNeg E z₂ :=
              by
                simpa [section14_swapNeg] using (section14_swapNegₗ E).map_add z₁ z₂
            have : section14_swapNeg E (z₁ + z₂) ∈ Dcone := hswap.symm ▸ hadd
            simpa [D] using this
          smul_mem' := by
            intro c hc z hz
            have hc' : 0 ≤ c := le_of_lt hc
            have hsmul :
                c • section14_swapNeg E z ∈ Dcone :=
              Dcone.smul_mem hc' hz
            have hswap : section14_swapNeg E (c • z) = c • section14_swapNeg E z := by
              ext <;> simp [section14_swapNeg_apply]
            simpa [D, hswap] using hsmul }
      have hgen :
          {z : ℝ × E × ℝ |
              ∃ x μ, z = (1, x, μ) ∧ fenchelConjugateBilin p f x ≤ (μ : EReal)} ⊆
            (Rcone : Set (ℝ × E × ℝ)) := by
        rintro _ ⟨x, μ, rfl, hxμ⟩
        -- Use the slice characterization with `μ★ = μ` and `x★ = x`.
        have hs :
            (-μ, x, -1) ∈
                (PointedCone.dual (R := ℝ) (-(section14_triplePairing (E := E) p)) K :
                  Set (ℝ × E × ℝ)) ↔
              fenchelConjugateBilin p f x ≤ (μ : EReal) := by
          simpa [K] using
            (section14_mem_dual_liftedEpigraphCone_slice_iff (E := E) (f := f) hf p x μ)
        have : (-μ, x, -1) ∈ D := by
          have : (-μ, x, -1) ∈
              (PointedCone.dual (R := ℝ) (-(section14_triplePairing (E := E) p)) K :
                Set (ℝ × E × ℝ)) :=
            (hs.2 hxμ)
          simpa [Dcone, D] using this
        simpa [Rcone, section14_swapNeg_apply, D] using this
      have hle :
          (ConvexCone.hull ℝ
                {z : ℝ × E × ℝ |
                  ∃ x μ, z = (1, x, μ) ∧ fenchelConjugateBilin p f x ≤ (μ : EReal)} :
                ConvexCone ℝ (ℝ × E × ℝ)) ≤ Rcone :=
        (ConvexCone.hull_le_iff (C := Rcone)).2 hgen
      intro z hz
      exact hle (by simpa [Kstar] using hz)
    -- Take closures.
    have : closure Kstar ⊆ {z : ℝ × E × ℝ | section14_swapNeg E z ∈ D} :=
      closure_minimal hKstar_subset hR_closed
    intro z hz
    have hz' : section14_swapNeg E z ∈ D := this hz
    have hz'' : section14_swapNeg E z ∈ (Dcone : Set (ℝ × E × ℝ)) := by
      simpa [D] using hz'
    have hz''' : (-z.2.2, z.2.1, -z.1) ∈ (Dcone : Set (ℝ × E × ℝ)) := by
      simpa [section14_swapNeg_apply] using hz''
    simpa [Dcone] using hz'''

  refine subset_antisymm hsubset₁ ?_
  -- Reverse inclusion (`⊇`): cone-slicing reconstruction using a witness of finiteness of `f*`.
  simpa [K, Kstar, section14_swapNeg_apply] using
    (section14_swapNeg_preimage_dual_subset_closure_Kstar (E := E) (f := f) hf p hdom)

/-- Sanity check for Theorem 14.5: mathlib's `gauge` is real-valued, so it cannot match a support
function that can take the value `⊤` (e.g. for `C = {0}`). -/
lemma section14_sanity_gauge_counterexample :
    (fun x : ℝ => (gauge ({0} : Set ℝ) x : EReal)) ≠
      (let p := LinearMap.applyₗ (R := ℝ) (M := ℝ) (M₂ := ℝ)
      fenchelConjugateBilin p.flip
        (erealIndicator (E := Module.Dual ℝ ℝ) (polar (E := ℝ) ({0} : Set ℝ)))) := by
  classical
  intro h
  have h1 := congrArg (fun f => f 1) h
  have hgauge : (gauge ({0} : Set ℝ) (1 : ℝ) : EReal) = 0 := by
    simp [gauge]
  let p := LinearMap.applyₗ (R := ℝ) (M := ℝ) (M₂ := ℝ)
  let φ2 : Module.Dual ℝ ℝ := (2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hφ2 : φ2 ∈ polar (E := ℝ) ({0} : Set ℝ) := by
    refine (mem_polar_iff (E := ℝ) (C := ({0} : Set ℝ)) (φ := φ2)).2 ?_
    intro x hx
    subst hx
    simp [φ2]
  have hle :
      (2 : EReal) ≤
        (let p := LinearMap.applyₗ (R := ℝ) (M := ℝ) (M₂ := ℝ)
        fenchelConjugateBilin p.flip
          (erealIndicator (E := Module.Dual ℝ ℝ) (polar (E := ℝ) ({0} : Set ℝ))))
          (1 : ℝ) := by
    -- `2 = (p.flip φ2 1) - 0`, and `0` comes from the indicator of `polar {0}`.
    have hval :
        (2 : EReal) =
          (p.flip φ2 (1 : ℝ) : EReal) -
            erealIndicator (E := Module.Dual ℝ ℝ) (polar (E := ℝ) ({0} : Set ℝ)) φ2 := by
      have hexpr :
          (p.flip φ2 (1 : ℝ) : EReal) -
              erealIndicator (E := Module.Dual ℝ ℝ) (polar (E := ℝ) ({0} : Set ℝ)) φ2 =
            ((2 : ℝ) : EReal) := by
        simp [p, φ2, erealIndicator, hφ2, LinearMap.applyₗ]
      exact (EReal.coe_natCast (n := 2)).symm.trans hexpr.symm
    have :
        (p.flip φ2 (1 : ℝ) : EReal) -
            erealIndicator (E := Module.Dual ℝ ℝ) (polar (E := ℝ) ({0} : Set ℝ)) φ2 ≤
          fenchelConjugateBilin p.flip
            (erealIndicator (E := Module.Dual ℝ ℝ) (polar (E := ℝ) ({0} : Set ℝ)))
            (1 : ℝ) := by
      unfold fenchelConjugateBilin
      exact le_sSup ⟨φ2, rfl⟩
    simpa [hval, p] using this
  have hRHS0 :
      (let p := LinearMap.applyₗ (R := ℝ) (M := ℝ) (M₂ := ℝ)
      fenchelConjugateBilin p.flip
        (erealIndicator (E := Module.Dual ℝ ℝ) (polar (E := ℝ) ({0} : Set ℝ))))
        (1 : ℝ) = 0 := by
    have : (0 : EReal) =
        (let p := LinearMap.applyₗ (R := ℝ) (M := ℝ) (M₂ := ℝ)
        fenchelConjugateBilin p.flip
          (erealIndicator (E := Module.Dual ℝ ℝ) (polar (E := ℝ) ({0} : Set ℝ))))
          (1 : ℝ) := by
      simpa [hgauge] using h1
    simpa using this.symm
  have hle0 : (2 : EReal) ≤ (0 : EReal) := by
    simpa [hRHS0] using hle
  have : ¬ ((2 : EReal) ≤ (0 : EReal)) := by simp
  exact this hle0


end Section14
end Chap03
