/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yuhao Jiang, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section14_part6
section Chap03
section Section14

open scoped Pointwise
open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- (Theorem 14.3, auxiliary) If `inf f < 0`, then the `0`-sublevel set of the positively
homogeneous hull is contained in the closure of its strict `0`-sublevel set. -/
lemma section14_sublevel_posHomHull_le_zero_subset_closure_strictSublevel
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal} (hf : ProperConvexERealFunction (F := E) f)
    (hf_closed : LowerSemicontinuous f) (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤)
    (hInf : sInf (Set.range f) < (0 : EReal)) :
    {x : E | section14_posHomHull (E := E) f x ≤ (0 : EReal)} ⊆
      closure {x : E | section14_posHomHull (E := E) f x < (0 : EReal)} := by
  classical
  intro x hx
  let k : E → EReal := section14_posHomHull (E := E) f
  -- Pick a direction with `f x0 < 0`.
  obtain ⟨x0, hx0⟩ := section14_exists_lt_zero_of_sInf_lt_zero (F := E) (f := f) hInf
  have hx0k : k x0 < (0 : EReal) :=
    lt_of_le_of_lt (section14_posHomHull_le (E := E) (f := f) x0) hx0

  -- Use a concrete sequence of positive scalars converging to `0`.
  let ε : ℕ → ℝ := fun n => (1 : ℝ) / ((n : ℝ) + 1)
  have hε_tendsto : Filter.Tendsto ε Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hε_pos : ∀ n : ℕ, 0 < ε n := by
    intro n
    have hn : 0 < (n : ℝ) + 1 := by
      have : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      linarith
    exact one_div_pos.2 hn

  let u : ℕ → E := fun n => x + (ε n) • x0
  have hu_tendsto : Filter.Tendsto u Filter.atTop (𝓝 x) := by
    have hsmul : Filter.Tendsto (fun n => (ε n) • x0) Filter.atTop (𝓝 (0 : E)) := by
      simpa using hε_tendsto.smul_const x0
    have : Filter.Tendsto (fun n => x + (ε n) • x0) Filter.atTop (𝓝 (x + 0)) :=
      (tendsto_const_nhds (x := x)).add hsmul
    simpa [u, add_zero] using this

  have hu_mem : ∀ n : ℕ, u n ∈ {z : E | k z < (0 : EReal)} := by
    intro n
    have hsub :=
      section14_posHomHull_subadd (E := E) (f := f) hf hf_closed hf0 hf0_ltTop x ((ε n) • x0)
    have hkε_le : k ((ε n) • x0) ≤ (ε n : EReal) * f x0 :=
      section14_posHomHull_smul_le (E := E) (f := f) (t := ε n) (hε_pos n) x0
    have hkε_lt0 : (ε n : EReal) * f x0 < (0 : EReal) := by
      -- Multiply the strict inequality `f x0 < 0` by the positive scalar `ε n`.
      have :=
        (OrderIso.strictMono (section14_mulPosOrderIso (t := ε n) (hε_pos n))) hx0
      simpa [section14_mulPosOrderIso] using this
    have hkε_lt0' : k ((ε n) • x0) < (0 : EReal) := lt_of_le_of_lt hkε_le hkε_lt0
    have hsum_le : k (x + (ε n) • x0) ≤ k x + k ((ε n) • x0) := by
      simpa [k] using hsub
    have hx' : k x ≤ (0 : EReal) := by simpa [k] using hx
    have hsum_le' : k (x + (ε n) • x0) ≤ (0 : EReal) + k ((ε n) • x0) := by
      exact le_trans hsum_le (add_le_add_left hx' _)
    have hsum_lt : k (x + (ε n) • x0) < (0 : EReal) := by
      -- `0 + k((ε n)•x0) = k((ε n)•x0)` and the latter is `< 0`.
      have : k (x + (ε n) • x0) ≤ k ((ε n) • x0) := by simpa using hsum_le'
      exact lt_of_le_of_lt this (by simpa using hkε_lt0')
    simpa [u] using hsum_lt

  -- Conclude by "closure from convergence": `u n → x` and `u n ∈ {k < 0}`.
  refine mem_closure_of_tendsto hu_tendsto ?_
  refine Filter.mem_of_superset Filter.univ_mem ?_
  intro n hn
  exact hu_mem n

/-- (Theorem 14.3, auxiliary) Recession directions of `posHomHull f` lie in the closed conic hull
of the `0`-sublevel set `{x | f x ≤ 0}`. -/
lemma section14_recessionCone_posHomHull_subset_closure_coneHull_sublevelZero
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) (hInf : sInf (Set.range f) < (0 : EReal)) :
    recessionConeEReal (F := E) (section14_posHomHull (E := E) f) ⊆
      closure ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E) := by
  classical
  intro y hy
  let k : E → EReal := section14_posHomHull (E := E) f
  have hk0 : k 0 = 0 :=
    section14_posHomHull_zero (E := E) (f := f) (hf0 := hf0) (hf0_ltTop := hf0_ltTop)
      (hf0_ne_bot := hf.1.1 0)
  have hk0_dom : (0 : E) ∈ erealDom k := by
    -- `k 0 = 0 < ⊤`.
    have : k 0 < ⊤ := by simp [hk0]
    simpa [erealDom] using this
  have hy0 :
      k y ≤ (0 : EReal) := by
    have hy' :=
      (section14_mem_recessionConeEReal_iff (F := E) (g := k) (y := y)).1 (by simpa [k] using hy)
        0 hk0_dom
    -- From `k (0+y) - k 0 ≤ 0` deduce `k y ≤ k 0 = 0`.
    have : k y ≤ k 0 := by
      have : k y - k 0 ≤ (0 : EReal) := by simpa [zero_add] using hy'
      exact (EReal.sub_nonpos).1 this
    simpa [hk0] using this

  have hy_cl :
      y ∈ closure {x : E | k x < (0 : EReal)} :=
    section14_sublevel_posHomHull_le_zero_subset_closure_strictSublevel (E := E) (f := f) hf
      hf_closed hf0 hf0_ltTop hInf (by simpa [k] using hy0)
  have hsubset :
      {x : E | k x < (0 : EReal)} ⊆
        ((ConvexCone.hull ℝ {x : E | f x ≤ (0 : EReal)} : ConvexCone ℝ E) : Set E) :=
    section14_strictSublevel_posHomHull_subset_coneHull_sublevelZero (E := E) (f := f) hf
  exact (closure_mono hsubset) hy_cl

/-- (Theorem 14.3, auxiliary) If `A ⊆ closure B` and `φ` is nonpositive on `B`, then `φ` is
nonpositive on `A`.

This is the form needed to transfer a polar condition along an inclusion into a closure. -/
lemma section14_mem_polarCone_of_mem_polarCone_closure_of_subset
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E]
    {A B : Set E} {φ : Module.Dual ℝ E} (hA : A ⊆ closure B)
    (hφ : φ ∈ polarCone (E := E) B) :
    φ ∈ polarCone (E := E) A := by
  have hφcl : φ ∈ polarCone (E := E) (closure B) := by
    simpa [section14_polarCone_closure_eq (E := E) (K := B)] using hφ
  refine (mem_polarCone_iff (E := E) (K := A) (φ := φ)).2 ?_
  intro x hx
  have hxcl : x ∈ closure B := hA hx
  exact (mem_polarCone_iff (E := E) (K := closure B) (φ := φ)).1 hφcl x hxcl

/-- Transport membership in `recessionConeEReal` along a linear equivalence. -/
lemma section14_mem_recessionConeEReal_iff_map_mem_recessionConeEReal_of_linearEquiv
    {E₁ F₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup F₁] [Module ℝ F₁]
    (e : E₁ ≃ₗ[ℝ] F₁) (g : E₁ → EReal) (y : E₁) :
    y ∈ recessionConeEReal (F := E₁) g ↔
      e y ∈ recessionConeEReal (F := F₁) (fun z : F₁ => g (e.symm z)) := by
  classical
  constructor
  · intro hy
    refine (section14_mem_recessionConeEReal_iff (F := F₁) (g := fun z : F₁ => g (e.symm z))
      (y := e y)).2 ?_
    intro z hz
    have hz' : e.symm z ∈ erealDom g := by
      simpa [erealDom] using hz
    have hy' :=
      (section14_mem_recessionConeEReal_iff (F := E₁) (g := g) (y := y)).1 hy (e.symm z) hz'
    -- Rewrite `e.symm (z + e y) = e.symm z + y`.
    simpa [LinearEquiv.map_add] using hy'
  · intro hy
    refine (section14_mem_recessionConeEReal_iff (F := E₁) (g := g) (y := y)).2 ?_
    intro x hx
    have hx' : (e x) ∈ erealDom (fun z : F₁ => g (e.symm z)) := by
      simpa [erealDom] using hx
    have hy' :=
      (section14_mem_recessionConeEReal_iff (F := F₁) (g := fun z : F₁ => g (e.symm z))
            (y := e y)).1 hy (e x) hx'
    -- Rewrite `e.symm (e x + e y) = x + y`.
    simpa [LinearEquiv.map_add] using hy'

/-- `recessionConeEReal` commutes with linear equivalences, as a set. -/
lemma section14_recessionConeEReal_image_linearEquiv
    {E₁ F₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup F₁] [Module ℝ F₁]
    (e : E₁ ≃ₗ[ℝ] F₁) (g : E₁ → EReal) :
    e '' recessionConeEReal (F := E₁) g =
      recessionConeEReal (F := F₁) (fun z : F₁ => g (e.symm z)) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (section14_mem_recessionConeEReal_iff_map_mem_recessionConeEReal_of_linearEquiv
      (e := e) (g := g) (y := y)).1 hy
  · intro hz
    refine ⟨e.symm z, ?_, by simp⟩
    have hz' :
        z ∈ recessionConeEReal (F := F₁) (fun z : F₁ => g (e.symm z)) := by
      simpa using hz
    -- Apply the transport lemma to `e.symm` and simplify.
    simpa using
      (section14_mem_recessionConeEReal_iff_map_mem_recessionConeEReal_of_linearEquiv
        (e := e.symm) (g := fun z : F₁ => g (e.symm z)) (y := z)).1 hz'

/-- Recession directions of a subadditive function with `g 0 = 0` are exactly its `0`-sublevel set. -/
lemma section14_recessionConeEReal_eq_sublevel_of_subadd_zero {F : Type*} [AddCommGroup F]
    (g : F → EReal) (hg0 : g 0 = 0) (hg_subadd : ∀ x y, g (x + y) ≤ g x + g y) :
    recessionConeEReal (F := F) g = {y : F | g y ≤ (0 : EReal)} := by
  classical
  ext y
  constructor
  · intro hy
    have h0dom : (0 : F) ∈ erealDom g := by
      have : g 0 < ⊤ := by simp [hg0]
      simpa [erealDom] using this
    have hy' :=
      (section14_mem_recessionConeEReal_iff (F := F) (g := g) (y := y)).1 hy 0 h0dom
    have : g y ≤ g 0 := by
      have : g y - g 0 ≤ (0 : EReal) := by simpa [zero_add] using hy'
      exact (EReal.sub_nonpos).1 this
    simpa [hg0] using this
  · intro hy
    refine (section14_mem_recessionConeEReal_iff (F := F) (g := g) (y := y)).2 ?_
    intro x hx
    have hxy : g (x + y) ≤ g x + g y := hg_subadd x y
    have hxy' : g x + g y ≤ g x + (0 : EReal) := by
      -- `g y ≤ 0` implies `g x + g y ≤ g x + 0`.
      simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right hy (g x))
    have hxy'' : g (x + y) ≤ g x + (0 : EReal) := hxy.trans hxy'
    have hle : g (x + y) ≤ g x := by simpa using hxy''
    exact (EReal.sub_nonpos).2 hle

/-- Recession directions give a pointwise inequality at the origin: if `y ∈ recessionConeEReal g`
and `0 ∈ dom g`, then `g y ≤ g 0`. -/
lemma section14_le_at_zero_of_mem_recessionConeEReal {F : Type*} [AddCommGroup F] (g : F → EReal)
    {y : F} (hy : y ∈ recessionConeEReal (F := F) g) (h0dom : (0 : F) ∈ erealDom g) :
    g y ≤ g 0 := by
  have hy0 :=
    (section14_mem_recessionConeEReal_iff (F := F) (g := g) (y := y)).1 hy 0 h0dom
  have : g y - g 0 ≤ (0 : EReal) := by simpa [zero_add] using hy0
  exact (EReal.sub_nonpos).1 this

/-- For `kcl = (k*)*` coming from the positively homogeneous hull `k` of `f`, we have
`0 ∈ dom kcl` and `kcl 0 ≤ 0`. -/
lemma section14_kcl_zero_dom_and_le_zero
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    let k : E → EReal := section14_posHomHull (E := E) f
    let kcl : E → EReal := fenchelConjugateBilin p.flip (fenchelConjugateBilin p k)
    (0 : E) ∈ erealDom kcl ∧ kcl 0 ≤ (0 : EReal) := by
  intro p k kcl
  have hk0 : k 0 = 0 :=
    section14_posHomHull_zero (E := E) (f := f) (hf0 := hf0) (hf0_ltTop := hf0_ltTop)
      (hf0_ne_bot := hf.1.1 0)
  have hk_proper : ProperConvexERealFunction (F := E) k :=
    section14_properConvex_posHomHull (E := E) (f := f) hf hf_closed hf0 hf0_ltTop
  have hkcl_le_k : ∀ x : E, kcl x ≤ k x :=
    section14_fenchelBiconjugate_le_of_proper (p := p) (f := k) hk_proper.1
  have hkcl0_le : kcl 0 ≤ (0 : EReal) := by
    simpa [hk0] using (hkcl_le_k 0)
  have hkcl0_dom : (0 : E) ∈ erealDom kcl := by
    have : kcl 0 < ⊤ := lt_of_le_of_lt hkcl0_le (by simp)
    simpa [erealDom] using this
  exact ⟨hkcl0_dom, hkcl0_le⟩

/-- (Theorem 14.3, auxiliary) If `y` is not in the closure of the strict `ε`-sublevel set of `k`,
then `(y, ε/2)` is not in the closure of the (real) epigraph of `k`. -/
lemma section14_not_mem_closure_epigraph_of_not_mem_closure_strictSublevel
    {F : Type*} [TopologicalSpace F] {k : F → EReal} {y : F} {ε : ℝ} (hε : 0 < ε)
    (hy : y ∉ closure {z : F | k z < (ε : EReal)}) :
    let r0 : ℝ := ε / 2
    let epi : Set (F × ℝ) := {p : F × ℝ | k p.1 ≤ (p.2 : EReal)}
    (y, r0) ∉ closure epi := by
  classical
  intro r0 epi
  -- Work with `U = (closure A)ᶜ` where `A = {k < ε}`.
  let A : Set F := {z : F | k z < (ε : EReal)}
  let U : Set F := (closure A)ᶜ
  have hyU : y ∈ U := by simpa [U] using hy
  have hU_nhds : U ∈ 𝓝 y := by
    have hU_open : IsOpen U := by
      simp [U]
    exact hU_open.mem_nhds hyU
  have hr0_lt : r0 < ε := by
    dsimp [r0]
    linarith
  have hI_nhds : Set.Iio ε ∈ 𝓝 r0 := Iio_mem_nhds hr0_lt
  have hprod_nhds : U ×ˢ Set.Iio ε ∈ 𝓝 (y, r0) := by
    refine (mem_nhds_prod_iff).2 ?_
    exact ⟨U, hU_nhds, Set.Iio ε, hI_nhds, by intro p hp; exact hp⟩

  intro hmem
  rcases (mem_closure_iff_nhds).1 hmem (U ×ˢ Set.Iio ε) hprod_nhds with ⟨p, hp⟩
  have hpU : p.1 ∈ U := hp.1.1
  have hpI : p.2 < ε := hp.1.2
  have hpEpi : k p.1 ≤ (p.2 : EReal) := hp.2
  have hpA : p.1 ∈ A := by
    have hpI' : (p.2 : EReal) < (ε : EReal) := by
      simpa using (EReal.coe_lt_coe_iff.2 hpI)
    exact lt_of_le_of_lt hpEpi hpI'
  have hpcl : p.1 ∈ closure A := subset_closure hpA
  exact hpU (by simpa [U] using hpcl)

/-- (Theorem 14.3, auxiliary) From an affine bound `ψ + c ≤ k`, one gets `k* ψ ≤ -c`. -/
lemma section14_fenchelConjugate_le_neg_const_of_add_const_le
    {k : E → EReal} {ψ : Module.Dual ℝ E} {c : ℝ}
    (hk_ne_bot : ∀ x : E, k x ≠ ⊥) (hψ : ∀ x : E, (ψ x : EReal) + (c : EReal) ≤ k x) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    fenchelConjugateBilin p k ψ ≤ (-(c : EReal)) := by
  intro p
  classical
  unfold fenchelConjugateBilin
  refine sSup_le ?_
  rintro _ ⟨x, rfl⟩
  have hle_left : (ψ x : EReal) ≤ (-(c : EReal)) + k x := by
    -- Add `-c` on the right and simplify in `ℝ`.
    have htmp := add_le_add_right (hψ x) (-(c : EReal))
    have hleft :
        (-(c : EReal)) + ((ψ x : EReal) + (c : EReal)) = (ψ x : EReal) := by
      -- All terms are real coercions, so this is `-c + (ψ x + c) = ψ x` in `ℝ`.
      calc
        (-(c : EReal)) + ((ψ x : EReal) + (c : EReal))
            = ((-c : ℝ) : EReal) + ((ψ x + c : ℝ) : EReal) := by
                simp [EReal.coe_add]
        _ = ((-c + (ψ x + c) : ℝ) : EReal) := by
                simpa using (EReal.coe_add (-c) (ψ x + c)).symm
        _ = (ψ x : EReal) := by
                simp [add_left_comm, add_comm]
    calc
      (ψ x : EReal) = (-(c : EReal)) + ((ψ x : EReal) + (c : EReal)) := by
            simpa using hleft.symm
      _ ≤ (-(c : EReal)) + k x := htmp
  -- Rewrite `ψ x - k x ≤ -c` as `ψ x ≤ -c + k x`.
  exact
    (EReal.sub_le_iff_le_add (a := (ψ x : EReal)) (b := k x) (c := (-(c : EReal)))
          (.inl (hk_ne_bot x)) (.inr (by simp))).2
      hle_left

/-- (Theorem 14.3, auxiliary) A dual certificate forces strict positivity of the biconjugate. -/
lemma section14_fenchelBiconjugate_pos_of_dual_certificate
    {k : E → EReal} {y : E} {ψ : Module.Dual ℝ E} {c r0 : ℝ}
    (hr0 : (r0 : EReal) < (ψ y : EReal) + (c : EReal))
    (hconj :
      fenchelConjugateBilin (LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)) k ψ ≤ (-(c : EReal))) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    let kcl : E → EReal := fenchelConjugateBilin p.flip (fenchelConjugateBilin p k)
    (r0 : EReal) < kcl y := by
  intro p kcl
  have hsub_le : (ψ y : EReal) - fenchelConjugateBilin p k ψ ≤ kcl y := by
    -- `kcl y` is a supremum over all dual variables; keep only the term for `ψ`.
    unfold kcl fenchelConjugateBilin
    have :
        ((p.flip ψ y : ℝ) : EReal) - fenchelConjugateBilin p k ψ ≤
          sSup (Set.range fun φ : Module.Dual ℝ E => ((p.flip φ y : ℝ) : EReal) - fenchelConjugateBilin p k φ) :=
      le_sSup ⟨ψ, rfl⟩
    simpa [p, LinearMap.applyₗ] using this
  have hc_le : (c : EReal) ≤ -(fenchelConjugateBilin p k ψ) := by
    have : -(-(c : EReal)) ≤ -(fenchelConjugateBilin p k ψ) := (EReal.neg_le_neg_iff).2 hconj
    simpa using this
  have hadd_le : (ψ y : EReal) + (c : EReal) ≤ (ψ y : EReal) - fenchelConjugateBilin p k ψ := by
    have := add_le_add_left hc_le (ψ y : EReal)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  exact lt_of_lt_of_le hr0 (hadd_le.trans hsub_le)

/-- (Theorem 14.3, auxiliary) The closure of a real epigraph is upward closed in the `ℝ`-coordinate.

This is the basic monotonicity property inherited from the definition `k x ≤ r`. -/
lemma section14_closure_epigraph_upwardClosed
    {F : Type*} [TopologicalSpace F] {k : F → EReal} {x : F} {r r' : ℝ}
    (hr : (x, r) ∈ closure {p : F × ℝ | k p.1 ≤ (p.2 : EReal)}) (hrr' : r ≤ r') :
    (x, r') ∈ closure {p : F × ℝ | k p.1 ≤ (p.2 : EReal)} := by
  classical
  set epi : Set (F × ℝ) := {p : F × ℝ | k p.1 ≤ (p.2 : EReal)}
  have hshift : ∀ {s : ℝ}, 0 ≤ s → (fun p : F × ℝ => (p.1, p.2 + s)) '' epi ⊆ epi := by
    intro s hs
    rintro _ ⟨p, hp, rfl⟩
    have hp' : k p.1 ≤ (p.2 : EReal) := by simpa [epi] using hp
    have hsE : (0 : EReal) ≤ (s : EReal) := by simpa [EReal.coe_nonneg] using hs
    have : k p.1 ≤ (p.2 : EReal) + (s : EReal) := hp'.trans (le_add_of_nonneg_right hsE)
    simpa [epi, EReal.coe_add, add_assoc] using this
  have hcont : Continuous fun p : F × ℝ => (p.1, p.2 + (r' - r)) := by
    refine continuous_fst.prodMk ?_
    simpa [add_comm, add_left_comm, add_assoc] using (continuous_snd.add continuous_const)
  have hmem :
      (x, r') ∈ (fun p : F × ℝ => (p.1, p.2 + (r' - r))) '' closure epi := by
    refine ⟨(x, r), hr, ?_⟩
    ext <;> simp [sub_eq_add_neg]
  have :
      (fun p : F × ℝ => (p.1, p.2 + (r' - r))) '' closure epi ⊆ closure epi := by
    have himg :
        (fun p : F × ℝ => (p.1, p.2 + (r' - r))) '' closure epi ⊆
          closure ((fun p : F × ℝ => (p.1, p.2 + (r' - r))) '' epi) :=
      image_closure_subset_closure_image hcont
    refine himg.trans ?_
    have hsub :
        (fun p : F × ℝ => (p.1, p.2 + (r' - r))) '' epi ⊆ epi := by
      refine hshift (s := (r' - r)) ?_
      linarith
    exact closure_mono hsub
  simpa [epi] using this hmem

/-- (Theorem 14.3, auxiliary) If `ψ₁ + c₁ ≤ k`, then `g(x,r) = ψ₁ x - r` is bounded above on
`closure (epi k)`. -/
lemma section14_linearPerturb_bound_on_closure_epigraph
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E]
    {k : E → EReal} {ψ₁ : Module.Dual ℝ E} {c₁ : ℝ}
    (hminor : ∀ x, (ψ₁ x : EReal) + (c₁ : EReal) ≤ k x) :
    let epi : Set (E × ℝ) := {p : E × ℝ | k p.1 ≤ (p.2 : EReal)}
    let g : StrongDual ℝ (E × ℝ) :=
      (ψ₁.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ E ℝ)) -
        (ContinuousLinearMap.snd ℝ E ℝ)
    ∀ p ∈ closure epi, g p ≤ -c₁ := by
  intro epi g p hp
  -- First show the bound on `epi`, then extend it to `closure epi` by continuity.
  have hsubset : epi ⊆ {q : E × ℝ | g q ≤ -c₁} := by
    intro q hq
    rcases q with ⟨x, r⟩
    have hq' : k x ≤ (r : EReal) := hq
    have hleE : (ψ₁ x : EReal) + (c₁ : EReal) ≤ (r : EReal) := (hminor x).trans hq'
    have hleR : ψ₁ x + c₁ ≤ r := by
      have : ((ψ₁ x + c₁ : ℝ) : EReal) ≤ (r : EReal) := by
        simpa [EReal.coe_add] using hleE
      exact (EReal.coe_le_coe_iff.1 this)
    have : ψ₁ x - r ≤ -c₁ := by linarith [hleR]
    have hg' : g (x, r) = ψ₁ x - r := by
      simp [g, LinearMap.coe_toContinuousLinearMap']
    simpa [hg'] using this
  have hclosed : IsClosed {q : E × ℝ | g q ≤ -c₁} := by
    have hcont : Continuous fun q : E × ℝ => g q := by
      simpa using g.continuous
    simpa [Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)
  have hcl : closure epi ⊆ {q : E × ℝ | g q ≤ -c₁} := closure_minimal hsubset hclosed
  exact hcl hp

/-- (Theorem 14.3, auxiliary) Separation of a point from `closure (epi k)` yields a dual
certificate `ψ + c ≤ k` that is strictly above the point in the epigraph direction. -/
lemma section14_sep_dual_certificate_of_not_mem_closure_epigraph
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {k : E → EReal} (hk : ProperConvexERealFunction (F := E) k) (hk0 : k 0 = 0)
    (hminor : ∃ (ψ₁ : Module.Dual ℝ E) (c₁ : ℝ), ∀ x, (ψ₁ x : EReal) + (c₁ : EReal) ≤ k x)
    {y : E} {r0 : ℝ} :
    let epi : Set (E × ℝ) := {p : E × ℝ | k p.1 ≤ (p.2 : EReal)}
    (y, r0) ∉ closure epi →
      ∃ (ψ : Module.Dual ℝ E) (c : ℝ),
        (r0 : EReal) < (ψ y : EReal) + (c : EReal) ∧
          ∀ x, (ψ x : EReal) + (c : EReal) ≤ k x := by
  intro epi hnot
  classical
  -- Work with the closed convex set `C = closure epi`.
  let C : Set (E × ℝ) := closure epi

  -- Convexity of the real epigraph of `k`.
  have hEpiConvex : Convex ℝ epi := by
    intro p hp q hq a b ha hb hab
    have hp' : k p.1 ≤ (p.2 : EReal) := hp
    have hq' : k q.1 ≤ (q.2 : EReal) := hq
    have hkconv : ConvexERealFunction (F := E) k := hk.2
    have hkconv' := hkconv (x := p.1) (y := q.1) (a := a) (b := b) ha hb hab
    have haE : (0 : EReal) ≤ (a : EReal) := by simpa [EReal.coe_nonneg] using ha
    have hbE : (0 : EReal) ≤ (b : EReal) := by simpa [EReal.coe_nonneg] using hb
    have hmul_p : (a : EReal) * k p.1 ≤ (a : EReal) * (p.2 : EReal) :=
      mul_le_mul_of_nonneg_left hp' haE
    have hmul_q : (b : EReal) * k q.1 ≤ (b : EReal) * (q.2 : EReal) :=
      mul_le_mul_of_nonneg_left hq' hbE
    have hsum :
        (a : EReal) * k p.1 + (b : EReal) * k q.1 ≤
          (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) :=
      add_le_add hmul_p hmul_q
    have hfst : (a • p + b • q).1 = a • p.1 + b • q.1 := by rfl
    have hsnd : (a • p + b • q).2 = a • p.2 + b • q.2 := by rfl
    have hle :
        k (a • p.1 + b • q.1) ≤
          (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) :=
      hkconv'.trans hsum
    have hrhs :
        (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) =
          ((a • p.2 + b • q.2 : ℝ) : EReal) := by
      simp [smul_eq_mul]
    have hle' : k (a • p.1 + b • q.1) ≤ ((a • p.2 + b • q.2 : ℝ) : EReal) :=
      hle.trans_eq hrhs
    have : k ((a • p + b • q).1) ≤ ((a • p + b • q).2 : EReal) := by
      simpa [hfst, hsnd] using hle'
    simpa [epi] using this

  have hCconv : Convex ℝ C := (hEpiConvex.closure)
  have hCclosed : IsClosed C := isClosed_closure

  -- Separate the point `(y,r0)` from the closed convex set `C`.
  obtain ⟨L0, u0, hL0u0C, hu0⟩ :=
    geometric_hahn_banach_closed_point (E := E × ℝ) (s := C) (x := (y, r0))
      hCconv hCclosed (by simpa [C] using hnot)

  -- Build a perturbation direction that is bounded above on `C` and strictly decreases in the
  -- `ℝ`-coordinate.
  rcases hminor with ⟨ψ₁, c₁, hψ₁⟩
  let M : ℝ := -c₁
  let g : StrongDual ℝ (E × ℝ) :=
    (ψ₁.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ E ℝ)) -
      (ContinuousLinearMap.snd ℝ E ℝ)

  have hgC : ∀ p ∈ C, g p ≤ M := by
    intro p hp
    have : g p ≤ -c₁ := by
      simpa [g, LinearMap.coe_toContinuousLinearMap'] using
        (section14_linearPerturb_bound_on_closure_epigraph (E := E) (k := k) (ψ₁ := ψ₁) (c₁ := c₁) hψ₁
          p hp)
    simpa [M] using this

  have hg01 : g ((0 : E), (1 : ℝ)) = -1 := by
    simp [g, LinearMap.coe_toContinuousLinearMap']

  -- The vertical ray `(0,μ)` lies in `C`, forcing `L0 (0,1) ≤ 0`.
  have ht0_le : L0 ((0 : E), (1 : ℝ)) ≤ 0 := by
    by_contra ht
    have htpos : 0 < L0 ((0 : E), (1 : ℝ)) := lt_of_not_ge ht
    obtain ⟨n : ℕ, hn⟩ :
        ∃ n : ℕ, (u0 / L0 ((0 : E), (1 : ℝ))) < n :=
      exists_nat_gt (u0 / L0 ((0 : E), (1 : ℝ)))
    have hn_mul : u0 < (n : ℝ) * L0 ((0 : E), (1 : ℝ)) := by
      have htne : L0 ((0 : E), (1 : ℝ)) ≠ 0 := ne_of_gt htpos
      have :
          (u0 / L0 ((0 : E), (1 : ℝ))) * L0 ((0 : E), (1 : ℝ)) <
            (n : ℝ) * L0 ((0 : E), (1 : ℝ)) :=
        (mul_lt_mul_of_pos_right hn htpos)
      simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ htne] using this
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.cast_nonneg n)
    have hmemEpi : ((0 : E), (n : ℝ)) ∈ epi := by
      simp [epi, hk0]
    have hmemC : ((0 : E), (n : ℝ)) ∈ C := subset_closure hmemEpi
    have hlt : L0 ((0 : E), (n : ℝ)) < u0 := hL0u0C ((0 : E), (n : ℝ)) hmemC
    have hL0r : L0 ((0 : E), (n : ℝ)) = (n : ℝ) * L0 ((0 : E), (1 : ℝ)) := by
      have hr : (n : ℝ) • ((0 : E), (1 : ℝ)) = ((0 : E), (n : ℝ)) := by
        ext <;> simp [Prod.smul_mk, smul_eq_mul]
      calc
        L0 ((0 : E), (n : ℝ)) = L0 ((n : ℝ) • ((0 : E), (1 : ℝ))) := by simp [hr]
        _ = (n : ℝ) • L0 ((0 : E), (1 : ℝ)) := by
              simpa using (map_smul L0 (n : ℝ) ((0 : E), (1 : ℝ)))
        _ = (n : ℝ) * L0 ((0 : E), (1 : ℝ)) := by simp [smul_eq_mul]
    have hlt' : (n : ℝ) * L0 ((0 : E), (1 : ℝ)) < u0 := by simpa [hL0r] using hlt
    exact (not_lt_of_gt hn_mul) hlt'

  -- Choose a small positive `ε` so strict separation survives after perturbing by `g`.
  set x0 : E × ℝ := (y, r0)
  have hΔ : 0 < L0 x0 - u0 := sub_pos.2 hu0
  set denom : ℝ := 2 * (|M - g x0| + 1)
  have hdenom_pos : 0 < denom := by
    have : 0 < |M - g x0| + 1 := by linarith [abs_nonneg (M - g x0)]
    have : 0 < (2 : ℝ) * (|M - g x0| + 1) := mul_pos (by norm_num) this
    simpa [denom, mul_assoc] using this
  set ε : ℝ := (L0 x0 - u0) / denom
  have hε_pos : 0 < ε := div_pos hΔ hdenom_pos
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos

  let L : StrongDual ℝ (E × ℝ) := L0 + ε • g
  let u : ℝ := u0 + ε * M

  have hLuC : ∀ a ∈ C, L a < u := by
    intro a ha
    have hL0 : L0 a < u0 := hL0u0C a ha
    have hg : g a ≤ M := hgC a ha
    have hgmul : ε * g a ≤ ε * M := mul_le_mul_of_nonneg_left hg hε_nonneg
    have : L0 a + ε * g a < u0 + ε * M := add_lt_add_of_lt_of_le hL0 hgmul
    simpa [L, u] using this

  have hu : u < L x0 := by
    -- First bound the perturbation error by `ε * |M - g x0|`.
    have habs_lt : |M - g x0| < |M - g x0| + 1 := by
      linarith [abs_nonneg (M - g x0)]
    have hmul_lt : ε * |M - g x0| < ε * (|M - g x0| + 1) :=
      mul_lt_mul_of_pos_left habs_lt hε_pos
    have hmul_eq : ε * (|M - g x0| + 1) = (L0 x0 - u0) / 2 := by
      have habs1_ne : |M - g x0| + 1 ≠ 0 := by linarith [abs_nonneg (M - g x0)]
      calc
        ε * (|M - g x0| + 1)
            = ((L0 x0 - u0) / (2 * (|M - g x0| + 1))) * (|M - g x0| + 1) := by
                simp [ε, denom]
        _ = (L0 x0 - u0) / 2 := by
              field_simp [habs1_ne, mul_assoc]
    have hmul_half : ε * |M - g x0| < (L0 x0 - u0) / 2 := by simpa [hmul_eq] using hmul_lt
    have hpos_lower : 0 < (L0 x0 - u0) - ε * |M - g x0| := by
      have : 0 < (L0 x0 - u0) / 2 := by linarith
      linarith
    have hbound :
        (L0 x0 - u0) - ε * |M - g x0| ≤ (L0 x0 - u0) + ε * (g x0 - M) := by
      -- Use `- |a| ≤ a` with `a = g x0 - M = -(M - g x0)`.
      have hnegabs : -|M - g x0| ≤ g x0 - M := by
        have : -( |M - g x0| ) ≤ -(M - g x0) := by
          simpa using (neg_le_neg (le_abs_self (M - g x0)))
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have hmul_le : -ε * |M - g x0| ≤ ε * (g x0 - M) := by
        have := mul_le_mul_of_nonneg_left hnegabs hε_nonneg
        simpa [mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      linarith
    have hsubpos : 0 < (L0 x0 - u0) + ε * (g x0 - M) := lt_of_lt_of_le hpos_lower hbound
    have :
        0 < (L0 x0 + ε * g x0) - (u0 + ε * M) := by
      have : (L0 x0 + ε * g x0) - (u0 + ε * M) = (L0 x0 - u0) + ε * (g x0 - M) := by ring
      simpa [this] using hsubpos
    have : u0 + ε * M < L0 x0 + ε * g x0 := sub_pos.1 this
    simpa [L, u] using this

  -- Decompose `L` into an `E`-part and a scalar coefficient on the `ℝ`-coordinate.
  let φ0 : Module.Dual ℝ E :=
    { toFun := fun x => L (x, (0 : ℝ))
      map_add' := by
        intro x y
        simpa using (map_add L (x, (0 : ℝ)) (y, (0 : ℝ)))
      map_smul' := by
        intro c x
        simpa [Prod.smul_mk, smul_eq_mul] using (map_smul L c (x, (0 : ℝ))) }

  set t : ℝ := L ((0 : E), (1 : ℝ))

  have hL0r : ∀ r : ℝ, L ((0 : E), r) = r * t := by
    intro r
    have hr : (r : ℝ) • ((0 : E), (1 : ℝ)) = ((0 : E), r) := by
      ext <;> simp [Prod.smul_mk, smul_eq_mul]
    calc
      L ((0 : E), r) = L (r • ((0 : E), (1 : ℝ))) := by simp [hr]
      _ = r • L ((0 : E), (1 : ℝ)) := by simpa using (map_smul L r ((0 : E), (1 : ℝ)))
      _ = r * t := by simp [t, smul_eq_mul]

  have hLxr : ∀ x : E, ∀ r : ℝ, L (x, r) = φ0 x + r * t := by
    intro x r
    calc
      L (x, r) = L ((x, (0 : ℝ)) + ((0 : E), r)) := by simp
      _ = L (x, (0 : ℝ)) + L ((0 : E), r) := by
            simpa using (map_add L (x, (0 : ℝ)) ((0 : E), r))
      _ = φ0 x + r * t := by simp [φ0, hL0r]

  -- The perturbation makes the `ℝ`-coefficient strictly negative.
  have ht_lt : t < 0 := by
    have ht0_le' : L0 ((0 : E), (1 : ℝ)) + ε * g ((0 : E), (1 : ℝ)) < 0 := by
      -- `L0(0,1) ≤ 0` and `g(0,1) = -1`.
      have : L0 ((0 : E), (1 : ℝ)) + ε * g ((0 : E), (1 : ℝ)) = L0 ((0 : E), (1 : ℝ)) - ε := by
        simp [hg01, sub_eq_add_neg]
      -- Any positive `ε` makes it strictly negative.
      linarith [ht0_le, hε_pos, this]
    have :
        t = L0 ((0 : E), (1 : ℝ)) + ε * g ((0 : E), (1 : ℝ)) := by
      simp [t, L]
    exact by simpa [this] using ht0_le'

  have htpos : 0 < -t := by linarith [ht_lt]

  -- Normalize the separator to an affine minorant.
  let ψ : Module.Dual ℝ E := (1 / (-t)) • φ0
  let c : ℝ := (-u) / (-t)

  have hψc_eq_div (x : E) : ψ x + c = (φ0 x - u) / (-t) := by
    -- Expand definitions and combine terms with a common denominator.
    have : (ψ x : ℝ) = (φ0 x) / (-t) := by
      have hψx : (ψ x : ℝ) = (1 / (-t)) * φ0 x := by
        simp [ψ, smul_eq_mul]
      calc
        (ψ x : ℝ) = (1 / (-t)) * φ0 x := hψx
        _ = φ0 x * (1 / (-t)) := by rw [mul_comm]
        _ = (φ0 x) / (-t) := by simp [div_eq_mul_inv]
    -- `a/(-t) + (-u)/(-t) = (a-u)/(-t)`.
    calc
      ψ x + c = (φ0 x) / (-t) + (-u) / (-t) := by simp [this, c]
      _ = (φ0 x + (-u)) / (-t) := by simpa using (add_div (φ0 x) (-u) (-t)).symm
      _ = (φ0 x - u) / (-t) := by simp [sub_eq_add_neg]

  have hr0_lt : (r0 : ℝ) < ψ y + c := by
    have hu' : u < φ0 y + r0 * t := by simpa [hLxr] using hu
    have : (r0 : ℝ) * (-t) < φ0 y - u := by
      -- Rearrangement of `u < φ0 y + r0*t`.
      linarith [hu']
    have : (r0 : ℝ) < (φ0 y - u) / (-t) := (lt_div_iff₀ htpos).2 this
    simpa [hψc_eq_div (x := y)] using this

  refine ⟨ψ, c, ?_, ?_⟩
  · -- Cast the real strict inequality to `EReal`.
    simpa [EReal.coe_add] using (EReal.coe_lt_coe_iff.2 hr0_lt)
  · intro x
    by_cases hxTop : k x = ⊤
    · simp [hxTop]
    · have hxlt : k x < ⊤ := lt_top_iff_ne_top.2 hxTop
      rcases section14_eq_coe_of_lt_top (z := k x) hxlt (hk.1.1 x) with ⟨r, hr⟩
      have hxmem : (x, r) ∈ epi := by simp [epi, hr]
      have hxmemC : (x, r) ∈ C := subset_closure hxmem
      have hL_lt : L (x, r) < u := hLuC (x, r) hxmemC
      have hL_lt' : φ0 x + r * t < u := by simpa [hLxr] using hL_lt
      have : φ0 x - u < r * (-t) := by
        -- Rearrange `φ0 x + r*t < u`.
        linarith [hL_lt']
      have hreal : (φ0 x - u) / (-t) < r := (div_lt_iff₀ htpos).2 this
      have hreal_le : (φ0 x - u) / (-t) ≤ r := le_of_lt hreal
      have hreal_le' : ψ x + c ≤ r := by
        simpa [hψc_eq_div (x := x)] using hreal_le
      have hE : ((ψ x + c : ℝ) : EReal) ≤ (r : EReal) := by
        exact_mod_cast hreal_le'
      -- Rewrite in the required `EReal` form.
      have : (ψ x : EReal) + (c : EReal) ≤ (r : EReal) := by
        simpa [EReal.coe_add] using hE
      simpa [hr] using this

/-- (Theorem 14.3, auxiliary) Approximation of `kcl`-sublevel points by strict sublevels of `k`.

This is the analytic heart of Theorem 14.3: from `kcl y ≤ 0` one should be able to find points
arbitrarily close to `y` where the (possibly non-closed) positively homogeneous hull `k` takes an
arbitrarily small (strict) value. -/
lemma section14_fenchelBiconjugate_sublevelZero_approx_by_posHomHull
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    let k : E → EReal := section14_posHomHull (E := E) f
    let kcl : E → EReal := fenchelConjugateBilin p.flip (fenchelConjugateBilin p k)
    ∀ {y : E}, kcl y ≤ (0 : EReal) →
      ∀ {ε : ℝ}, 0 < ε → y ∈ closure {z : E | k z < (ε : EReal)} := by
  intro p k kcl y hy ε hε
  classical
  -- Notation for the strict sublevel set and the real epigraph of `k`.
  let A : Set E := {z : E | k z < (ε : EReal)}
  let epi : Set (E × ℝ) := {p : E × ℝ | k p.1 ≤ (p.2 : EReal)}
  let r0 : ℝ := ε / 2

  -- Auxiliary lemmas local to this proof.
  -- If a point is not in the closure of a strict sublevel set, then the corresponding epigraph
  -- point at height `ε/2` is not in the closure of the epigraph.
  have h_not_mem_closure_epi :
      y ∉ closure A → (y, r0) ∉ closure epi := by
    intro hyA
    -- Apply the general topological bridge lemma.
    simpa [A, epi, r0] using
      (section14_not_mem_closure_epigraph_of_not_mem_closure_strictSublevel (F := E) (k := k)
        (y := y) (ε := ε) hε (by simpa [A] using hyA))

  -- Prove the approximation by contradiction.
  by_contra hycl
  have hnot_epi : (y, r0) ∉ closure epi := h_not_mem_closure_epi (by simpa [A] using hycl)

  have hk0 : k 0 = 0 :=
    section14_posHomHull_zero (E := E) (f := f) (hf0 := hf0) (hf0_ltTop := hf0_ltTop)
      (hf0_ne_bot := hf.1.1 0)
  have hk_proper : ProperConvexERealFunction (F := E) k :=
    section14_properConvex_posHomHull (E := E) (f := f) hf hf_closed hf0 hf0_ltTop
  have hminor_k : ∃ (ψ₁ : Module.Dual ℝ E) (c₁ : ℝ), ∀ x, (ψ₁ x : EReal) + (c₁ : EReal) ≤ k x := by
    rcases
        (section14_sublevelZero_fenchelConjugate_nonempty (E := E) (f := f) hf hf_closed hf0 hf0_ltTop) with
      ⟨ψ₁, hψ₁⟩
    have hψ₁_le_f : ∀ x : E, (ψ₁ x : EReal) ≤ f x :=
      (section14_fenchelConjugate_le_zero_iff (E := E) (f := f) ψ₁).1 hψ₁
    have hψ₁_le_k : ∀ x : E, (ψ₁ x : EReal) ≤ k x :=
      section14_le_posHomHull_of_le (E := E) (f := f) (φ := ψ₁) hψ₁_le_f
    refine ⟨ψ₁, 0, ?_⟩
    intro x
    simpa using (hψ₁_le_k x)
  obtain ⟨ψ, c, hr0_lt, hψ_le⟩ :=
    (section14_sep_dual_certificate_of_not_mem_closure_epigraph (E := E) (k := k) hk_proper hk0
          hminor_k
          (y := y) (r0 := r0) (by simpa [epi] using hnot_epi))
  -- Turn `ψ + c ≤ k` into a bound on the Fenchel conjugate `k* ψ`.
  have hk_ne_bot : ∀ x : E, k x ≠ ⊥ := by
    exact hk_proper.1.1
  have hconj_le : fenchelConjugateBilin p k ψ ≤ (-(c : EReal)) := by
    simpa using
      (section14_fenchelConjugate_le_neg_const_of_add_const_le (E := E) (k := k) (ψ := ψ)
        (c := c) hk_ne_bot hψ_le)
  -- The certificate forces a positive lower bound on the biconjugate `kcl y`.
  have hr0_lt_kcl : (r0 : EReal) < kcl y := by
    simpa [kcl] using
      (section14_fenchelBiconjugate_pos_of_dual_certificate (E := E) (k := k) (y := y) (ψ := ψ)
        (c := c) (r0 := r0) hr0_lt hconj_le)
  have hr0_pos : (0 : EReal) < (r0 : EReal) := by
    have : 0 < r0 := by
      dsimp [r0]
      linarith
    simpa using (EReal.coe_lt_coe_iff.2 this)
  have : (r0 : EReal) < (0 : EReal) := lt_of_lt_of_le hr0_lt_kcl hy
  exact (not_lt_of_gt hr0_pos) this

/-- (Theorem 14.3, auxiliary) If `k z` is small and moving in a fixed direction makes `k` very
negative, then the translated point lies in the strict `0`-sublevel set. -/
lemma section14_strictSublevel_mem_of_smallValue_add_smul_negDir
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤)
    {x0 z : E} {ε t : ℝ} (ht : 0 < t)
    (hz : section14_posHomHull (E := E) f z < (ε : EReal))
    (hx0 : (t : EReal) * f x0 < -(ε : EReal)) :
    section14_posHomHull (E := E) f (z + t • x0) < (0 : EReal) := by
  classical
  let k : E → EReal := section14_posHomHull (E := E) f
  have hk_subadd : ∀ x y : E, k (x + y) ≤ k x + k y :=
    section14_posHomHull_subadd (E := E) (f := f) hf hf_closed hf0 hf0_ltTop
  have hk_smul_le : k (t • x0) ≤ (t : EReal) * f x0 :=
    section14_posHomHull_smul_le (E := E) (f := f) (t := t) ht x0
  have hk_smul_lt : k (t • x0) < -(ε : EReal) := lt_of_le_of_lt hk_smul_le hx0
  have hsum_lt : k z + k (t • x0) < (ε : EReal) + (-(ε : EReal)) :=
    EReal.add_lt_add (by simpa [k] using hz) (by simpa [k] using hk_smul_lt)
  have hsum_lt0 : k z + k (t • x0) < (0 : EReal) := by
    have hcancel : (ε : EReal) + (-(ε : EReal)) = (0 : EReal) := by
      -- `ε` is a real number, so cancellation reduces to `ε + (-ε) = 0` in `ℝ`.
      have hneg : (-(ε : EReal)) = ((-ε : ℝ) : EReal) := by simp
      calc
        (ε : EReal) + (-(ε : EReal)) = (ε : EReal) + ((-ε : ℝ) : EReal) := by rw [hneg]
        _ = ((ε + (-ε) : ℝ) : EReal) := by simpa using (EReal.coe_add ε (-ε)).symm
        _ = (0 : EReal) := by simp
    simpa [hcancel] using hsum_lt
  have hle : k (z + t • x0) ≤ k z + k (t • x0) := by
    simpa [k] using hk_subadd z (t • x0)
  exact lt_of_le_of_lt hle hsum_lt0

/-- (Theorem 14.3, auxiliary) From `kcl y ≤ 0` we can reach the strict `0`-sublevel of `k` by
arbitrarily small perturbations, hence `y` lies in the closure of `{k < 0}`. -/
lemma section14_sublevelZero_fenchelBiconjugate_posHomHull_subset_closure_strictSublevel_posHomHull
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [FiniteDimensional ℝ E] [LocallyConvexSpace ℝ E]
    {f : E → EReal}
    (hf : ProperConvexERealFunction (F := E) f) (hf_closed : LowerSemicontinuous f)
    (hf0 : (0 : EReal) < f 0) (hf0_ltTop : f 0 < ⊤) (hInf : sInf (Set.range f) < (0 : EReal)) :
    let p := LinearMap.applyₗ (R := ℝ) (M := E) (M₂ := ℝ)
    let k : E → EReal := section14_posHomHull (E := E) f
    let kcl : E → EReal := fenchelConjugateBilin p.flip (fenchelConjugateBilin p k)
    {y : E | kcl y ≤ (0 : EReal)} ⊆ closure {z : E | k z < (0 : EReal)} := by
  intro p k kcl
  classical
  intro y hy
  -- Choose a direction with `f x0 < 0`.
  obtain ⟨x0, hx0⟩ := section14_exists_lt_zero_of_sInf_lt_zero (F := E) (f := f) hInf
  have hx0k : k x0 < (0 : EReal) :=
    lt_of_le_of_lt (section14_posHomHull_le (E := E) (f := f) x0) hx0
  -- Extract a real `a` with `f x0 = a` to do the perturbation arithmetic in `ℝ`.
  have hfx0_ltTop : f x0 < ⊤ := lt_of_lt_of_le hx0 le_top
  rcases section14_eq_coe_of_lt_top (z := f x0) hfx0_ltTop (hf.1.1 x0) with ⟨a, ha⟩
  have ha_lt0 : a < 0 := by
    have : (a : EReal) < (0 : EReal) := by simpa [ha] using hx0
    simpa using (EReal.coe_lt_coe_iff.1 this)

  -- Neighborhood formulation of closure.
  refine (mem_closure_iff_nhds).2 ?_
  intro U hU
  -- Split a neighborhood of `y` into `V + W ⊆ U`.
  have hpre :
      (fun p : E × E => p.1 + p.2) ⁻¹' U ∈ 𝓝 (y, (0 : E)) := by
    have hcont : ContinuousAt (fun p : E × E => p.1 + p.2) (y, (0 : E)) :=
      (continuous_add.continuousAt : _)
    simpa using hcont.preimage_mem_nhds (by simpa [add_zero] using hU)
  rcases (mem_nhds_prod_iff).1 hpre with ⟨V, hV, W, hW, hVW⟩
  have hVaddW : V + W ⊆ U := by
    intro x hx
    rcases hx with ⟨v, hv, w, hw, rfl⟩
    have : (v, w) ∈ (fun p : E × E => p.1 + p.2) ⁻¹' U := hVW ⟨hv, hw⟩
    simpa using this

  -- Pick a small `t > 0` with `t • x0 ∈ W`.
  have hcont_smul : Continuous fun t : ℝ => t • x0 := by
    simpa using (continuous_id.smul continuous_const)
  have hWx0 : {t : ℝ | t • x0 ∈ W} ∈ 𝓝 (0 : ℝ) := by
    have hW' : W ∈ 𝓝 ((0 : ℝ) • x0) := by simpa using hW
    simpa using hcont_smul.continuousAt.preimage_mem_nhds hW'
  rcases Metric.mem_nhds_iff.1 hWx0 with ⟨δ, hδpos, hδ⟩
  set t : ℝ := δ / 2
  have htpos : 0 < t := by
    dsimp [t]
    linarith
  have htW : t • x0 ∈ W := by
    have htball : t ∈ Metric.ball (0 : ℝ) δ := by
      have : t < δ := by
        dsimp [t]
        linarith
      have : |t| < δ := by simpa [abs_of_pos htpos] using this
      simpa [Metric.ball, Real.dist_eq, abs_sub_comm, sub_zero] using this
    exact (hδ htball)

  -- Choose a strict sublevel threshold `ε = -(t*a)/2 > 0`.
  set ε : ℝ := -(t * a) / 2
  have hεpos : 0 < ε := by
    have hta_neg : t * a < 0 := by nlinarith [htpos, ha_lt0]
    dsimp [ε]
    nlinarith
  have hx0_mul_lt : (t : EReal) * f x0 < -(ε : EReal) := by
    -- This is `t*a < t*a/2` in `ℝ` (since `t*a < 0`).
    have hlt : t * a < t * a / 2 := by
      have hta_neg : t * a < 0 := by nlinarith [htpos, ha_lt0]
      nlinarith
    have : ((t * a : ℝ) : EReal) < ((t * a / 2 : ℝ) : EReal) := by
      simpa using (EReal.coe_lt_coe_iff.2 hlt)
    -- Rewrite the endpoints using `ha` and the definition of `ε`.
    have hleft : (t : EReal) * f x0 = ((t * a : ℝ) : EReal) := by
      simp [ha, EReal.coe_mul]
    have hright : -(ε : EReal) = ((t * a / 2 : ℝ) : EReal) := by
      simp [ε, EReal.coe_mul, mul_assoc, div_eq_mul_inv]
    simpa [hleft, hright]

  -- Approximate `y` by `z ∈ V` with `k z < ε`.
  have hy_cl : y ∈ closure {z : E | k z < (ε : EReal)} :=
    by
      -- Unfold the `let`-bindings from the approximation lemma to match our local `p,k,kcl`.
      simpa [p, k, kcl] using
        (section14_fenchelBiconjugate_sublevelZero_approx_by_posHomHull (E := E) (f := f) hf
              hf_closed hf0 hf0_ltTop (y := y) (by simpa using hy) hεpos)
  rcases (mem_closure_iff_nhds).1 hy_cl V hV with ⟨z, hzV, hzk⟩

  -- Perturb to land in `{k < 0}` inside `U`.
  have hkneg : k (z + t • x0) < (0 : EReal) :=
    section14_strictSublevel_mem_of_smallValue_add_smul_negDir (E := E) (f := f) hf hf_closed hf0
      hf0_ltTop (x0 := x0) (z := z) (ε := ε) (t := t) htpos hzk hx0_mul_lt
  refine ⟨z + t • x0, ?_, ?_⟩
  · exact hVaddW ⟨z, hzV, t • x0, htW, by simp⟩
  · exact hkneg


end Section14
end Chap03
