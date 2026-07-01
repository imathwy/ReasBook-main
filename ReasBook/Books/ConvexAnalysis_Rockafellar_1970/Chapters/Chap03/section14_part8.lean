/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section14_part7
section Chap03
section Section14

open scoped Pointwise
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

-- The weak topology on the algebraic dual induced by evaluation (see `section14_part3`).
noncomputable local instance section14_instTopologicalSpace_dualWeak_part8 :
    TopologicalSpace (Module.Dual ℝ E) :=
  WeakBilin.instTopologicalSpace
    (B := (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)).flip)

/-- (Theorem 14.3, auxiliary) Analytic core: a point in the `0`-sublevel set of the Fenchel
biconjugate of `k = posHomHull f` lies in the closed conic hull of `{x | f x ≤ 0}`. -/
lemma section14_sublevelZero_fenchelBiconjugate_posHomHull_subset_closure_coneHull_sublevelZero
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) (hInf : sInf (Set.range f) < (0 : EReal)) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    let k : E → EReal := section14_posHomHull (E := E) f
    let kcl : E → EReal := fenchelConjugateBilin p.flip (fenchelConjugateBilin p k)
    {y : E | kcl y ≤ (0 : EReal)} ⊆
      closure ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E) := by
  intro p k kcl
  classical
  intro y hy
  have hy_cl :
      y ∈ closure {z : E | k z < (0 : EReal)} :=
    (section14_sublevelZero_fenchelBiconjugate_posHomHull_subset_closure_strictSublevel_posHomHull
          (E := E) (f := f) hf hf_closed hf0 hf0_ltTop hInf)
      (by simpa [kcl, k] using hy)
  have hsubset :
      {z : E | k z < (0 : EReal)} ⊆
        ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E) := by
    -- `k < 0` implies membership in the conic hull of `{f ≤ 0}`.
    simpa [k] using
      (section14_strictSublevel_posHomHull_subset_coneHull_sublevelZero (E := E) (f := f) hf)
  exact (closure_mono hsubset) hy_cl

/-- (Theorem 14.3, auxiliary) Recession directions of the Fenchel biconjugate `(k*)*` lie in the
closure of the recession directions of `k`.

This is the missing structural bridge in the conic-separation proof of Theorem 14.3. -/
lemma section14_recessionConeEReal_fenchelBiconjugate_subset_closure
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) (hInf : sInf (Set.range f) < (0 : EReal)) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    let k : E → EReal := section14_posHomHull (E := E) f
    let kcl : E → EReal := fenchelConjugateBilin p.flip (fenchelConjugateBilin p k)
    recessionConeEReal (F := E) kcl ⊆ closure (recessionConeEReal (F := E) k) := by
  intro p k kcl
  classical
  -- Write the target closure set as the closure of the conic hull of the primal `0`-sublevel set.
  -- (This is the part of the textbook argument that uses positive homogeneity and Theorem 7.6.)
  set S : Set E := {x : E | f x ≤ (0 : EReal)}
  let K : ConvexCone ℝ E := ConvexCone.hull ℝ S

  have hk0 : k 0 = 0 :=
    section14_posHomHull_zero (E := E) (f := f) (hf0 := hf0) (hf0_ltTop := hf0_ltTop)
      (hf0_ne_bot := hf.1.1 0)
  have hk_subadd : ∀ x y : E, k (x + y) ≤ k x + k y :=
    section14_posHomHull_subadd (E := E) (f := f) hf hf_closed hf0 hf0_ltTop
  have hrec_k :
      recessionConeEReal (F := E) k = {y : E | k y ≤ (0 : EReal)} :=
    section14_recessionConeEReal_eq_sublevel_of_subadd_zero (F := E) k hk0 hk_subadd

  -- `K ⊆ recessionConeEReal k` since `k x ≤ f x` and `k` is subadditive with `k 0 = 0`.
  have hK_subset_rec :
      (K : Set E) ⊆ recessionConeEReal (F := E) k := by
    -- First show `K ⊆ {y | k y ≤ 0}`.
    have hcone :
        (K : Set E) ⊆ {y : E | k y ≤ (0 : EReal)} := by
      -- The set `{y | k y ≤ 0}` is a convex cone.
      let Ck : ConvexCone ℝ E :=
        { carrier := {y : E | k y ≤ (0 : EReal)}
          smul_mem' := by
            intro c hc x hx
            have hsmul : k (c • x) = (c : EReal) * k x :=
              section14_posHomHull_smul (E := E) (f := f) (t := c) hc x
            have hcE : (0 : EReal) ≤ (c : EReal) := by
              simpa [EReal.coe_nonneg] using (le_of_lt hc)
            have hmul : (c : EReal) * k x ≤ (c : EReal) * (0 : EReal) :=
              mul_le_mul_of_nonneg_left hx hcE
            simpa [hsmul] using (hmul.trans_eq (by simp))
          add_mem' := by
            intro x hx y hy
            have hxy : k (x + y) ≤ k x + k y := hk_subadd x y
            have hsum : k x + k y ≤ (0 : EReal) + (0 : EReal) := add_le_add hx hy
            have hsum' : k x + k y ≤ (0 : EReal) := by simpa using hsum
            exact hxy.trans hsum' }
      have hS : S ⊆ (Ck : Set E) := by
        intro x hx
        have hxk : k x ≤ f x := section14_posHomHull_le (E := E) (f := f) x
        exact hxk.trans hx
      have hle : K ≤ Ck :=
        (ConvexCone.hull_le_iff (C := Ck) (s := S)).2 hS
      intro x hx
      exact hle hx
    -- Now rewrite `recessionConeEReal k` using subadditivity and `k 0 = 0`.
    simpa [hrec_k] using hcone

  -- `recessionConeEReal k ⊆ closure K` is already established for `k := posHomHull f`.
  have hrec_subset_clK :
      recessionConeEReal (F := E) k ⊆ closure (K : Set E) :=
    section14_recessionCone_posHomHull_subset_closure_coneHull_sublevelZero (E := E) (f := f) hf
      hf_closed hf0 hf0_ltTop hInf

  have hcl_rec_eq : closure (recessionConeEReal (F := E) k) = closure (K : Set E) := by
    refine subset_antisymm ?_ ?_
    · -- `closure rec(k) ⊆ closure K` from `rec(k) ⊆ closure K`.
      exact closure_minimal hrec_subset_clK isClosed_closure
    · -- `closure K ⊆ closure rec(k)` since `K ⊆ rec(k)`.
      exact closure_mono hK_subset_rec

  -- Reduce to showing `recessionConeEReal kcl ⊆ closure K`.
  -- This is the genuine missing structural bridge: for `kcl = (k*)*` (the lsc hull of `k`),
  -- recession directions are limits of recession directions of `k`.
  have hbridge : recessionConeEReal (F := E) kcl ⊆ closure (K : Set E) := by
    intro y hy
    -- First reduce to the `0`-sublevel set of `kcl` using the recession inequality at `x = 0`.
    have hkcl0 :
        (0 : E) ∈ erealDom kcl ∧ kcl 0 ≤ (0 : EReal) := by
      simpa [kcl, k] using
        (section14_kcl_zero_dom_and_le_zero (E := E) (f := f) hf hf_closed hf0 hf0_ltTop)
    have hy_le0 : kcl y ≤ (0 : EReal) := by
      have hy_le0' : kcl y ≤ kcl 0 :=
        section14_le_at_zero_of_mem_recessionConeEReal (F := E) (g := kcl) (y := y) hy hkcl0.1
      exact hy_le0'.trans hkcl0.2
    -- Convert the `0`-sublevel condition into membership in the closed conic hull of `{f ≤ 0}`.
    have hy_mem :
        y ∈
          closure
            ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E) := by
      exact
        (section14_sublevelZero_fenchelBiconjugate_posHomHull_subset_closure_coneHull_sublevelZero
              (E := E) (f := f) hf hf_closed hf0 hf0_ltTop hInf)
          (by simpa [kcl, k] using hy_le0)
    -- Rewrite the target closure set.
    simpa [K, S] using hy_mem
  intro y hy
  have : y ∈ closure (K : Set E) := hbridge hy
  -- Rewrite `closure (K : Set E)` as `closure (recessionConeEReal k)`.
  simpa [hcl_rec_eq] using this

/-- (Theorem 14.3, auxiliary) Geometric conversion step for the separation proof.

This is the missing implication in the contradiction argument: if a point `x : E` is nonpositive
under every functional in the closed cone generated by `{φ | f* φ ≤ 0}`, then `x` lies in the
closed cone generated by `{x | f x ≤ 0}`.

The textbook proof routes this through the positively-homogeneous hull `k` of `f`, the conjugacy
`(cl k)* = ι_{ {φ | f* φ ≤ 0} }`, and the polar/recession correspondence (Theorem 14.2). -/
lemma section14_dual_flip_closure_coneHull_sublevelZero_fenchelConjugate_subset_closure_coneHull_sublevelZero
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) (hInf : sInf (Set.range f) < (0 : EReal)) :
    (PointedCone.dual (R := ℝ)
            ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
            (closure
              ((ConvexCone.hull ℝ
                    {φ : Module.Dual ℝ E |
                      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤
                        (0 : EReal)} :
                    ConvexCone ℝ (Module.Dual ℝ E)) :
                Set (Module.Dual ℝ E))) :
          Set E) ⊆
      closure ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E) := by
  classical
  -- Notation for the primal/dual `0`-sublevel generators.
  set S : Set E := {x : E | f x ≤ (0 : EReal)}
  set T : Set (Module.Dual ℝ E) :=
    {φ : Module.Dual ℝ E |
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal)}
  let K : ConvexCone ℝ E := ConvexCone.hull ℝ S
  let Kstar : ConvexCone ℝ (Module.Dual ℝ E) := ConvexCone.hull ℝ T

  -- The proof is a direct application of the bipolar theorem for cones (Text 14.0.4):
  -- it suffices to know that `polarCone (closure K) ⊆ closure K★`.
  --
  -- In the textbook, this inclusion is proved by introducing the positively-homogeneous hull `k`
  -- generated by `f`, using the Section 13 conjugacy `(cl k)* = ι_{T}`, and then applying the
  -- polar/recession correspondence (Theorem 14.2) together with the closure/sublevel identity
  -- (Theorem 7.6). Importing the needed Section 13 development is currently blocked by a global
  -- name collision on `_root_.fenchelConjugateBilin`.
  have hPol_core : polarCone (E := E) S ⊆ closure (Kstar : Set (Module.Dual ℝ E)) := by
    intro φ hφ
    -- Introduce the positively homogeneous hull `k` and use the polar/recession correspondence
    -- (Theorem 14.2) for `k`.
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    let k : E → EReal := section14_posHomHull (E := E) f
    let kcl : E → EReal := fenchelConjugateBilin p.flip (fenchelConjugateBilin p k)
    have hk_proper : ProperConvexERealFunction (F := E) k :=
      section14_properConvex_posHomHull (E := E) (f := f) hf hf_closed hf0 hf0_ltTop
    have hkcl_proper : ProperConvexERealFunction (F := E) kcl := by
      simpa [p, kcl, k] using
        (section14_properConvex_fenchelBiconjugate_posHomHull (E := E) (f := f) hf hf_closed hf0
          hf0_ltTop)
    have hkcl_closed : LowerSemicontinuous kcl := by
      simpa [p, kcl, k] using (section14_lowerSemicontinuous_posHomHull (E := E) (f := f) hf_closed)

    -- First propagate `φ ≤ 0` from `S` to the closed conic hull of `S`.
    have hφKcl : φ ∈ polarCone (E := E) (closure (K : Set E)) := by
      have hφK : φ ∈ polarCone (E := E) (K : Set E) := by
        simpa [K, section14_polarCone_hull_eq (E := E) S] using hφ
      simpa [section14_polarCone_closure_eq (E := E) (K := (K : Set E))] using hφK

    -- Recession directions of `k` lie in `closure K`.
    have hrec :
        recessionConeEReal (F := E) k ⊆ closure (K : Set E) :=
      section14_recessionCone_posHomHull_subset_closure_coneHull_sublevelZero (E := E) (f := f) hf
        hf_closed hf0 hf0_ltTop hInf

    have hφRec : φ ∈ polarCone (E := E) (recessionConeEReal (F := E) k) := by
      refine (mem_polarCone_iff (E := E) (K := recessionConeEReal (F := E) k) (φ := φ)).2 ?_
      intro y hy
      have hyK : y ∈ closure (K : Set E) := hrec hy
      exact (mem_polarCone_iff (E := E) (K := closure (K : Set E)) (φ := φ)).1 hφKcl y hyK

    have hφRec_cl : φ ∈ polarCone (E := E) (recessionConeEReal (F := E) kcl) := by
      have hinc :
          recessionConeEReal (F := E) kcl ⊆ closure (recessionConeEReal (F := E) k) := by
        simpa [kcl, k] using
          (section14_recessionConeEReal_fenchelBiconjugate_subset_closure (E := E) (f := f) hf
            hf_closed hf0 hf0_ltTop hInf)
      exact
        section14_mem_polarCone_of_mem_polarCone_closure_of_subset (E := E)
          (A := recessionConeEReal (F := E) kcl) (B := recessionConeEReal (F := E) k) hinc hφRec

    -- Apply Theorem 14.2 (dual) to rewrite the polar as the closure of the cone generated by the
    -- effective domain of `k*`, then identify that domain with the `0`-sublevel set of `f*`.
    have hPolEq :
        polarCone (E := E) (recessionConeEReal (F := E) kcl) =
          closure
            ((ConvexCone.hull ℝ (erealDom (fenchelConjugateBilin p kcl)) :
                  ConvexCone ℝ (Module.Dual ℝ E)) :
              Set (Module.Dual ℝ E)) :=
      polar_recessionCone_eq_closure_coneGenerated_dom_fenchelConjugate (E := E) (f := kcl)
        hkcl_proper hkcl_closed
    have hdom :
        erealDom (fenchelConjugateBilin p kcl) = T := by
      -- Use the triconjugate identity to reduce to the already established domain identification
      -- for the positively homogeneous hull.
      have htri :
          fenchelConjugateBilin p kcl = fenchelConjugateBilin p k := by
        -- `kcl = (k*)*` and `((k*)*)* = k*` for proper `k`.
        have hk_proper' : ProperERealFunction k := hk_proper.1
        have hk_dom : ∃ y0 : Module.Dual ℝ E, fenchelConjugateBilin p k y0 < ⊤ := by
          -- Use the nonempty `0`-sublevel set of `f*` and the domain identification for `k*`.
          obtain ⟨ψ, hψ⟩ :=
            section14_sublevelZero_fenchelConjugate_nonempty (E := E) (f := f) hf hf_closed hf0
              hf0_ltTop
          have hdom_k :
              erealDom (fenchelConjugateBilin p k) = T := by
            simpa [k, T] using
              (section14_erealDom_fenchelConjugate_posHomHull_eq_sublevelZero (E := E) (f := f))
          have hψ' : ψ ∈ erealDom (fenchelConjugateBilin p k) := by
            simpa [hdom_k, T] using hψ
          exact ⟨ψ, hψ'⟩
        simpa [kcl] using
          (section14_fenchelConjugate_triconjugate_eq_of_proper (p := p) (f := k) hk_proper' hk_dom)
      -- Now use the existing identification for `k`.
      simpa [htri, k, T] using
        (section14_erealDom_fenchelConjugate_posHomHull_eq_sublevelZero (E := E) (f := f))
    have hmem :
        φ ∈
          closure
            ((ConvexCone.hull ℝ (erealDom (fenchelConjugateBilin p kcl) :
                    Set (Module.Dual ℝ E)) :
                  ConvexCone ℝ (Module.Dual ℝ E)) :
              Set (Module.Dual ℝ E)) := by
      simpa [hPolEq] using hφRec_cl
    simpa [Kstar, hdom] using hmem
  have hPol :
      polarCone (E := E) (closure (K : Set E)) ⊆ closure (Kstar : Set (Module.Dual ℝ E)) := by
    intro φ hφ
    have hφK : φ ∈ polarCone (E := E) (K : Set E) := by
      simpa [section14_polarCone_closure_eq (E := E) (K := (K : Set E))] using hφ
    have hφS : φ ∈ polarCone (E := E) S := by
      simpa [K, section14_polarCone_hull_eq (E := E) S] using hφK
    exact hPol_core hφS

  intro x hx
  -- Use antitonicity of `PointedCone.dual` on the dual side.
  have hx' :
      x ∈
        (PointedCone.dual (R := ℝ)
              ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
              (polarCone (E := E) (closure (K : Set E))) : Set E) := by
    refine
      (section14_mem_dual_flip_eval_iff_forall_le_zero (E := E)
            (S := polarCone (E := E) (closure (K : Set E))) (x := x)).2 ?_
    intro φ hφ
    have hφ' : φ ∈ closure (Kstar : Set (Module.Dual ℝ E)) := hPol hφ
    exact
      (section14_mem_dual_flip_eval_iff_forall_le_zero (E := E)
            (S := closure (Kstar : Set (Module.Dual ℝ E))) (x := x)).1 hx φ hφ'
  -- Bipolar theorem for the nonempty cone `K`.
  have hSne : S.Nonempty := section14_sublevelZero_nonempty (F := E) (f := f) hInf
  have hKne : (K : Set E).Nonempty := by
    rcases hSne with ⟨x0, hx0⟩
    exact ⟨x0, ConvexCone.subset_hull (R := ℝ) (s := S) hx0⟩
  have hKne_cl : ((K.closure : ConvexCone ℝ E) : Set E).Nonempty := by
    simpa [ConvexCone.coe_closure] using hKne.closure
  have hbip :
      (PointedCone.dual (R := ℝ)
              ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
              (polarCone (E := E) (closure (K : Set E))) : Set E) =
        closure (K : Set E) := by
    simpa [ConvexCone.coe_closure, closure_closure] using
      (polarCone_polar_eq_closure (E := E) (K := K.closure) hKne_cl)
  -- Conclude.
  have : x ∈ closure (K : Set E) := by simpa [hbip] using hx'
  simpa [K, S] using this

lemma section14_polarCone_sublevelZero_subset_closure_coneHull_sublevelZero_fenchelConjugate
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) (hInf : sInf (Set.range f) < (0 : EReal)) :
    polarCone (E := E) {x : E | f x ≤ (0 : EReal)} ⊆
      closure
        ((ConvexCone.hull ℝ
              {φ : Module.Dual ℝ E |
                fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤
                  (0 : EReal)} :
              ConvexCone ℝ (Module.Dual ℝ E)) :
          Set (Module.Dual ℝ E)) := by
  classical
  -- Notation for the primal and dual `0`-sublevel generators.
  set S : Set E := {x : E | f x ≤ (0 : EReal)}
  set T : Set (Module.Dual ℝ E) :=
    {φ : Module.Dual ℝ E |
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) f φ ≤ (0 : EReal)}

  have hTsubset : T ⊆ polarCone (E := E) S := by
    simpa [T, S] using
      (section14_sublevel_fenchelConjugate_le_zero_subset_polarCone_sublevelZero (E := E) (f := f))

  -- The remaining inclusion is the genuine content of Theorem 14.3, and in this development it
  -- is intended to be discharged using the Section 13 support-function/positive-homogeneous-hull
  -- correspondence (Theorem 13.5) together with the polar/recession correspondence (Theorem 14.2)
  -- and the closure-of-sublevel identification (Theorem 7.6). Importing those Section 13 files is
  -- currently blocked by a global name collision on `_root_.fenchelConjugateBilin`.
  intro φ hφ
  -- With `section14_instTopologicalSpace_dualWeak`, the topology on `Module.Dual ℝ E` is the weak
  -- topology induced by evaluation. The remaining step is the genuine content of Theorem 14.3:
  -- show that every `φ` nonpositive on `S` lies in the weak-closure of the convex cone generated by
  -- `T`. The textbook proof routes this through the positively homogeneous hull `k` of `f` and the
  -- Section 13 conjugacy between `cl k` and the indicator of `{φ | f* φ ≤ 0}`; importing those
  -- Section 13 files is currently blocked by the global name collision on `_root_.fenchelConjugateBilin`.
  by_contra hφmem
  have hKne :
      (closure
            ((ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) :
              Set (Module.Dual ℝ E))).Nonempty := by
    rcases
        (section14_sublevelZero_fenchelConjugate_nonempty (E := E) (f := f) hf hf_closed hf0
              hf0_ltTop) with
      ⟨ψ, hψ⟩
    refine ⟨ψ, ?_⟩
    exact subset_closure (ConvexCone.subset_hull (R := ℝ) (s := T) (by simpa [T] using hψ))
  obtain ⟨x, hxK, hxpos⟩ :=
    section14_exists_eval_pos_of_not_mem_closure_coneHull (E := E) (T := T) (hKne := hKne)
      (φ := φ) hφmem
  -- To reach a contradiction, it suffices to know that `x` lies in the closed convex cone
  -- generated by `S`; then continuity of `y ↦ φ y` propagates `φ ≤ 0` from `S` to that closure.
  have hxS :
      x ∈
        closure
          ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E) := by
    -- Convert the separation conclusion `hxK` into membership in a dual cone.
    have hxDual :
        x ∈
          (PointedCone.dual (R := ℝ)
                ((-LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ))).flip
                (closure
                  ((ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) :
                    Set (Module.Dual ℝ E))) :
              Set E) := by
      refine
        (section14_mem_dual_flip_eval_iff_forall_le_zero (E := E)
              (S :=
                closure
                  ((ConvexCone.hull ℝ T : ConvexCone ℝ (Module.Dual ℝ E)) :
                    Set (Module.Dual ℝ E)))
              (x := x)).2 ?_
      intro ψ hψ
      exact hxK ψ hψ
    -- This is the remaining geometric input from the textbook proof: identify the dual cone above
    -- with the closed primal cone generated by `S`, via the positively-homogeneous hull
    -- construction and the polar/recession correspondence (Theorem 14.2).
    --
    -- Importing the corresponding Section 13 results is currently blocked by a global name
    -- collision on `_root_.fenchelConjugateBilin`.
    exact
      (section14_dual_flip_closure_coneHull_sublevelZero_fenchelConjugate_subset_closure_coneHull_sublevelZero
            (E := E) (f := f) hf hf_closed hf0 hf0_ltTop hInf)
        hxDual
  have hφHull :
      φ ∈
        polarCone (E := E) ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E) := by
    simpa [S, section14_polarCone_hull_eq (E := E) S] using hφ
  have hφle : φ x ≤ 0 := by
    have hcont : Continuous fun y : E => φ y := by
      simpa using
        (LinearMap.continuous_of_finiteDimensional (f := (φ : E →ₗ[ℝ] ℝ)))
    have hclosed : IsClosed {y : E | φ y ≤ 0} := by
      simpa [Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)
    have hsubset :
        ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E) ⊆ {y : E | φ y ≤ 0} := by
      intro y hy
      exact
        (mem_polarCone_iff (E := E)
              (K := ((ConvexCone.hull ℝ S : ConvexCone ℝ E) : Set E)) (φ := φ)).1 hφHull y hy
    have hx' : x ∈ {y : E | φ y ≤ 0} := (closure_minimal hsubset hclosed) hxS
    simpa using hx'
  exact (not_lt_of_ge hφle) hxpos


end Section14
end Chap03
