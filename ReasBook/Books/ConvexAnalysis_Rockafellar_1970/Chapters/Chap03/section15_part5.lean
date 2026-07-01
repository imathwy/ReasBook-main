/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Yijie Wang, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section15_part4

section Chap03
section Section15

open scoped BigOperators
open scoped Pointwise
open scoped RealInnerProductSpace

/-- The bipolar of a gauge equals the epigraph-closure infimum. -/
lemma polarGauge_bipolar_eq_kCl {n : ℕ} {k : (Fin n → ℝ) → EReal} (hk : IsGauge k) :
    let kCl : (Fin n → ℝ) → EReal :=
      fun x =>
        sInf
          {μ : EReal |
            ∃ r : ℝ,
              μ = (r : EReal) ∧
                (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)}
    polarGauge (polarGauge k) = kCl := by
  classical
  let E₂ := EuclideanSpace ℝ (Fin n)
  let H₂ := WithLp 2 (E₂ × ℝ)
  let eH := eH_transport_to_H2 n
  let σ₂ : H₂ → H₂ := fun p => WithLp.toLp 2 (- (WithLp.ofLp p).1, (WithLp.ofLp p).2)
  let S₂ : Set H₂ := eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) k
  have hkPolar : IsGauge (polarGauge k) := polarGauge_isGauge (k := k)
  have hT :
      eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge k) =
        σ₂ ⁻¹' (ProperCone.innerDual (E := H₂) S₂ : Set H₂) := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨q, hq, rfl⟩
      rcases q with ⟨xStar, μ⟩
      have hmem :=
        (epigraph_polarGauge_eq_preimage_innerDualCone_H2
            (hk := hk) (xStar := xStar) (μ := μ)).1 hq
      simpa [E₂, H₂, eH, σ₂, S₂] using hmem
    · intro hp
      refine ⟨eH p, ?_, by simp⟩
      have hmem :
          σ₂ (eH.symm (eH p)) ∈
            (ProperCone.innerDual (E := H₂) S₂ : Set H₂) := by
        simpa [E₂, H₂, eH, σ₂, S₂] using hp
      simpa [E₂, H₂, eH, σ₂, S₂] using
        (epigraph_polarGauge_eq_preimage_innerDualCone_H2
            (hk := hk) (xStar := (eH p).1) (μ := (eH p).2)).2 hmem
  have hT2 :
      eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) =
        σ₂ ⁻¹'
          (ProperCone.innerDual (E := H₂)
              (eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge k)) :
            Set H₂) := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨q, hq, rfl⟩
      rcases q with ⟨xStar, μ⟩
      have hmem :=
        (epigraph_polarGauge_eq_preimage_innerDualCone_H2
            (hk := hkPolar) (xStar := xStar) (μ := μ)).1 hq
      simpa [E₂, H₂, eH, σ₂] using hmem
    · intro hp
      refine ⟨eH p, ?_, by simp⟩
      have hmem :
          σ₂ (eH.symm (eH p)) ∈
            (ProperCone.innerDual (E := H₂)
                (eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge k)) :
              Set H₂) := by
        simpa [E₂, H₂, eH, σ₂] using hp
      simpa [E₂, H₂, eH, σ₂] using
        (epigraph_polarGauge_eq_preimage_innerDualCone_H2
            (hk := hkPolar) (xStar := (eH p).1) (μ := (eH p).2)).2 hmem
  have hT2' :
      eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) =
        σ₂ ⁻¹' (ProperCone.innerDual (E := H₂)
          (σ₂ ⁻¹' (ProperCone.innerDual (E := H₂) S₂ : Set H₂)) : Set H₂) := by
    simpa [hT] using hT2
  have hT2'' :
      eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) =
        (ProperCone.innerDual (E := H₂)
            (ProperCone.innerDual (E := H₂) S₂ : Set H₂) : Set H₂) := by
    have hcomm :
        (ProperCone.innerDual (E := H₂) (σ₂ ⁻¹' (ProperCone.innerDual (E := H₂) S₂ : Set H₂)) :
          Set H₂) =
          σ₂ ⁻¹'
            (ProperCone.innerDual (E := H₂)
                (ProperCone.innerDual (E := H₂) S₂ : Set H₂) : Set H₂) := by
      simpa [E₂, H₂, σ₂] using
        (innerDual_preimage_signflip (n := n)
          (A := (ProperCone.innerDual (E := H₂) S₂ : Set H₂)))
    have hpre :
        σ₂ ⁻¹'
            (σ₂ ⁻¹'
                (ProperCone.innerDual (E := H₂)
                    (ProperCone.innerDual (E := H₂) S₂ : Set H₂) : Set H₂)) =
          (ProperCone.innerDual (E := H₂)
              (ProperCone.innerDual (E := H₂) S₂ : Set H₂) : Set H₂) := by
      ext p
      have hσ : σ₂ (σ₂ p) = p := by
        simpa [E₂, H₂, σ₂] using (signflip_H2_involutive (n := n) (p := p))
      simp [Set.preimage_preimage, hσ]
    calc
      eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k))
          = σ₂ ⁻¹'
              (σ₂ ⁻¹'
                  (ProperCone.innerDual (E := H₂)
                      (ProperCone.innerDual (E := H₂) S₂ : Set H₂) : Set H₂)) := by
              simpa [hcomm] using hT2'
      _ = (ProperCone.innerDual (E := H₂)
              (ProperCone.innerDual (E := H₂) S₂ : Set H₂) : Set H₂) := hpre
  have hH2 :
      eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) =
        closure ((ConvexCone.hull ℝ (Set.insert (0 : H₂) S₂) : ConvexCone ℝ H₂) : Set H₂) := by
    calc
      eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k))
          = (ProperCone.innerDual (E := H₂)
              (ProperCone.innerDual (E := H₂) S₂ : Set H₂) : Set H₂) := hT2''
      _ =
          closure ((ConvexCone.hull ℝ (Set.insert (0 : H₂) S₂) : ConvexCone ℝ H₂) : Set H₂) := by
            simpa using
              (section14_innerDualCone_innerDualCone_eq_closure_coneHull
                (H := H₂) (s := S₂))
  -- `S₂` is already a convex cone containing `0`, so the cone hull is `S₂`.
  let C2 : ConvexCone ℝ H₂ :=
    { carrier := S₂
      smul_mem' := by
        intro c hc p hp
        rcases hp with ⟨q, hq, hqeq⟩
        refine ⟨c • q, (epigraph_isConvexCone_of_isGauge hk).smul_mem hc hq, ?_⟩
        calc
          eH.symm (c • q) = c • eH.symm q := eH.symm.map_smul c q
          _ = c • p := by simp [hqeq]
      add_mem' := by
        intro p hp q hq
        rcases hp with ⟨p' : (Fin n → ℝ) × ℝ, hp', hpeq⟩
        rcases hq with ⟨q' : (Fin n → ℝ) × ℝ, hq', hqeq⟩
        refine ⟨p' + q',
          (epigraph_isConvexCone_of_isGauge hk).add_mem hp' hq', ?_⟩
        calc
          eH.symm (p' + q') = eH.symm p' + eH.symm q' := eH.symm.map_add p' q'
          _ = p + q := by simp [hpeq, hqeq]
    }
  have h0 : (0 : H₂) ∈ S₂ := by
    refine ⟨((0 : Fin n → ℝ), (0 : ℝ)), ?_, ?_⟩
    · have h0le : k (0 : Fin n → ℝ) ≤ (0 : EReal) := by
        simp [hk.2.2.2]
      exact (mem_epigraph_univ_iff (f := k) (x := 0) (μ := (0 : ℝ))).2 h0le
    · exact eH.symm.map_zero
  have hHull_eq :
      ((ConvexCone.hull ℝ (Set.insert (0 : H₂) S₂) : ConvexCone ℝ H₂) : Set H₂) = S₂ := by
    apply Set.Subset.antisymm
    · intro x hx
      have hsub :
          ConvexCone.hull ℝ (Set.insert (0 : H₂) S₂) ≤ C2 :=
        (ConvexCone.hull_le_iff (C := C2) (s := Set.insert (0 : H₂) S₂)).2 (by
          intro y hy
          rcases (Set.mem_insert_iff).1 hy with rfl | hy'
          · simpa [C2] using h0
          · simpa [C2] using hy')
      have hx' : x ∈ (C2 : Set H₂) := hsub hx
      simpa [C2] using hx'
    · intro x hx
      exact ConvexCone.subset_hull (R := ℝ) (s := Set.insert (0 : H₂) S₂)
        (Set.mem_insert_of_mem (0 : H₂) hx)
  have hH2' :
      eH.symm '' epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) =
        closure S₂ := by
    simpa [hHull_eq] using hH2
  have himage :
      eH '' closure S₂ = closure (eH '' S₂) := by
    simpa using (eH.toHomeomorph.image_closure (s := S₂))
  have himage' :
      eH '' S₂ = epigraph (S := (Set.univ : Set (Fin n → ℝ))) k := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨u, hu, rfl⟩
      rcases hu with ⟨q, hq, rfl⟩
      simpa using hq
    · intro hp
      refine ⟨eH.symm p, ?_, by simp⟩
      exact ⟨p, hp, by simp⟩
  have hset :
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) =
        closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k) := by
    have hpre :
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) =
          eH '' closure S₂ := by
      ext p
      constructor
      · intro hp
        have hx : eH.symm p ∈ eH.symm '' epigraph
            (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) := ⟨p, hp, rfl⟩
        have hx' : eH.symm p ∈ closure S₂ := by
          simpa [hH2'] using hx
        exact ⟨eH.symm p, hx', by simp⟩
      · intro hp
        rcases hp with ⟨u, hu, rfl⟩
        have hu' : u ∈ eH.symm '' epigraph
            (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) := by
          simpa [hH2'] using hu
        rcases hu' with ⟨p, hp, hpe⟩
        have hp' : p = eH u := by
          have := congrArg eH hpe
          simpa using this
        simpa [hp'] using hp
    calc
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k))
          = eH '' closure S₂ := hpre
      _ = closure (eH '' S₂) := himage
      _ = closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k) := by simp [himage']
  have hclosure :
      closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k) =
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) := by
    simpa using (closure_epigraph_eq_epigraph_sInf (f := k)).symm
  have hset' :
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) =
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) := by
    simpa [hclosure] using hset
  have hfun : polarGauge (polarGauge k) = epigraphClosureInf k := by
    funext x
    have hle :
        polarGauge (polarGauge k) x ≤ epigraphClosureInf k x := by
      by_cases htop : epigraphClosureInf k x = ⊤
      · simp [htop]
      by_cases hbot : epigraphClosureInf k x = ⊥
      · have hleall : ∀ μ : ℝ, polarGauge (polarGauge k) x ≤ (μ : EReal) := by
          intro μ
          have hxg :
              (x, μ) ∈
                epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) := by
            refine (mem_epigraph_univ_iff (f := epigraphClosureInf k) (x := x) (μ := μ)).2 ?_
            simp [hbot]
          have hxf :
              (x, μ) ∈
                epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) := by
            simpa [hset'] using hxg
          exact (mem_epigraph_univ_iff (f := polarGauge (polarGauge k)) (x := x) (μ := μ)).1 hxf
        have hbotf : polarGauge (polarGauge k) x = ⊥ :=
          ereal_eq_bot_of_le_all_coe hleall
        simp [hbotf, hbot]
      · have hxg :
            (x, (epigraphClosureInf k x).toReal) ∈
              epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) := by
          refine (mem_epigraph_univ_iff (f := epigraphClosureInf k) (x := x)
            (μ := (epigraphClosureInf k x).toReal)).2 ?_
          exact EReal.le_coe_toReal htop
        have hxf :
            (x, (epigraphClosureInf k x).toReal) ∈
              epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge (polarGauge k)) := by
          simpa [hset'] using hxg
        have hxle :
            polarGauge (polarGauge k) x ≤ ((epigraphClosureInf k x).toReal : EReal) :=
          (mem_epigraph_univ_iff (f := polarGauge (polarGauge k)) (x := x)
            (μ := (epigraphClosureInf k x).toReal)).1 hxf
        have hcoe :
            ((epigraphClosureInf k x).toReal : EReal) = epigraphClosureInf k x :=
          EReal.coe_toReal htop hbot
        simpa [hcoe] using hxle
    have hge :
        epigraphClosureInf k x ≤ polarGauge (polarGauge k) x := by
      by_cases htop : polarGauge (polarGauge k) x = ⊤
      · simp [htop]
      by_cases hbot : polarGauge (polarGauge k) x = ⊥
      · have hleall : ∀ μ : ℝ, epigraphClosureInf k x ≤ (μ : EReal) := by
          intro μ
          have hxf :
              (x, μ) ∈
                epigraph (S := (Set.univ : Set (Fin n → ℝ)))
                  (polarGauge (polarGauge k)) := by
            refine (mem_epigraph_univ_iff (f := polarGauge (polarGauge k)) (x := x) (μ := μ)).2 ?_
            simp [hbot]
          have hxg :
              (x, μ) ∈
                epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) := by
            simpa [hset'] using hxf
          exact (mem_epigraph_univ_iff (f := epigraphClosureInf k) (x := x) (μ := μ)).1 hxg
        have hbotg : epigraphClosureInf k x = ⊥ :=
          ereal_eq_bot_of_le_all_coe hleall
        simp [hbotg, hbot]
      · have hxf :
            (x, (polarGauge (polarGauge k) x).toReal) ∈
              epigraph (S := (Set.univ : Set (Fin n → ℝ)))
                (polarGauge (polarGauge k)) := by
          refine (mem_epigraph_univ_iff (f := polarGauge (polarGauge k)) (x := x)
            (μ := (polarGauge (polarGauge k) x).toReal)).2 ?_
          exact EReal.le_coe_toReal htop
        have hxg :
            (x, (polarGauge (polarGauge k) x).toReal) ∈
              epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) := by
          simpa [hset'] using hxf
        have hxle :
            epigraphClosureInf k x ≤ ((polarGauge (polarGauge k) x).toReal : EReal) :=
          (mem_epigraph_univ_iff (f := epigraphClosureInf k) (x := x)
            (μ := (polarGauge (polarGauge k) x).toReal)).1 hxg
        have hcoe :
            ((polarGauge (polarGauge k) x).toReal : EReal) = polarGauge (polarGauge k) x :=
          EReal.coe_toReal htop hbot
        simpa [hcoe] using hxle
    exact le_antisymm hle hge
  have hkCl :
      (fun x =>
        sInf
          {μ : EReal |
            ∃ r : ℝ,
              μ = (r : EReal) ∧
                (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)}) =
        epigraphClosureInf k := kCl_eq_epigraphClosureInf (n := n) k
  simpa [hkCl] using hfun

/-- Theorem 15.1: If `k` is a gauge function, then its polar `k^∘` is a closed gauge function and
`k^{∘∘} = cl k`. Moreover, if `k = γ(· | C)` for some nonempty convex set `C ⊆ ℝ^n` that is
absorbing, then `k^∘` agrees with the support function of `C`.

In this development, `k^∘` is `polarGauge k`; "closed" is expressed as `IsClosed (epigraph univ ·)`;
and `cl k` is modeled as the extended-real function whose epigraph is the topological closure of
`epigraph univ k`. -/
theorem polarGauge_isGauge_isClosed_and_bipolar_eq_closure_epigraph {n : ℕ}
    {k : (Fin n → ℝ) → EReal} (hk : IsGauge k) :
    let kPolar : (Fin n → ℝ) → EReal := polarGauge k
    let kCl : (Fin n → ℝ) → EReal :=
      fun x =>
        sInf
          {μ : EReal |
            ∃ r : ℝ,
              μ = (r : EReal) ∧
                (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)}
    IsGauge kPolar ∧
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) kPolar) ∧
        polarGauge kPolar = kCl ∧
          ∀ C : Set (Fin n → ℝ),
            C.Nonempty →
              Convex ℝ C →
                (∀ x : Fin n → ℝ, ∃ r : ℝ, 0 ≤ r ∧ ∃ y ∈ C, x = r • y) →
                  k = (fun x => (gaugeFunction C x : EReal)) →
                    kPolar = supportFunctionEReal C := by
  classical
  dsimp
  refine ⟨?hGauge, ?hClosed⟩
  · simpa using (polarGauge_isGauge (k := k))
  · refine ⟨?hClosed', ?hRest⟩
    · simpa using (isClosed_epigraph_polarGauge (k := k) hk)
    · refine ⟨?hBipolar, ?hSupport⟩
      · simpa using (polarGauge_bipolar_eq_kCl (k := k) hk)
      · intro C hCne hCconv hCabs hkC
        funext xStar
        have hle :
            supportFunctionEReal C xStar ≤ polarGauge k xStar := by
          simpa [hkC] using
            (supportFunctionEReal_le_polarGauge_of_gaugeFunction (C := C) xStar)
        have hge :
            polarGauge k xStar ≤ supportFunctionEReal C xStar := by
          simpa [hkC] using
            (polarGauge_of_gaugeFunction_le_supportFunctionEReal (C := C) hCne hCabs xStar)
        exact le_antisymm hge hle

/-- A gauge with closed epigraph equals its epigraph-closure infimum. -/
lemma epigraphClosureInf_eq_of_isGauge_isClosed_epigraph {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsGauge k)
    (hclosed : IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)) :
    epigraphClosureInf k = k := by
  classical
  have hset :
      epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) =
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) k := by
    have hclosure :
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) =
          closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k) := by
      simpa using (closure_epigraph_eq_epigraph_sInf (f := k))
    simpa [hclosed.closure_eq] using hclosure
  funext x
  have hle : epigraphClosureInf k x ≤ k x := by
    by_cases htop : k x = ⊤
    · simp [htop]
    · have hk_ne_bot : k x ≠ ⊥ := IsGauge.ne_bot hk x
      have hxk :
          (x, (k x).toReal) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) k := by
        refine (mem_epigraph_univ_iff (f := k) (x := x) (μ := (k x).toReal)).2 ?_
        exact EReal.le_coe_toReal htop
      have hxg :
          (x, (k x).toReal) ∈
            epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) := by
        simpa [hset] using hxk
      have hle_toReal :
          epigraphClosureInf k x ≤ ((k x).toReal : EReal) :=
        (mem_epigraph_univ_iff (f := epigraphClosureInf k) (x := x)
          (μ := (k x).toReal)).1 hxg
      have hcoe : ((k x).toReal : EReal) = k x :=
        EReal.coe_toReal htop hk_ne_bot
      simpa [hcoe] using hle_toReal
  have hge : k x ≤ epigraphClosureInf k x := by
    by_cases htop : epigraphClosureInf k x = ⊤
    · simp [htop]
    · have hbot : epigraphClosureInf k x ≠ ⊥ := by
        intro hbot
        have hleall : ∀ μ : ℝ, epigraphClosureInf k x ≤ (μ : EReal) := by
          intro μ
          simp [hbot]
        have hleall' : ∀ μ : ℝ, k x ≤ (μ : EReal) := by
          intro μ
          have hxg :
              (x, μ) ∈
                epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) := by
            refine (mem_epigraph_univ_iff (f := epigraphClosureInf k) (x := x) (μ := μ)).2 ?_
            exact hleall μ
          have hxk :
              (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ))) k := by
            simpa [hset] using hxg
          exact (mem_epigraph_univ_iff (f := k) (x := x) (μ := μ)).1 hxk
        have hkbot : k x = ⊥ := ereal_eq_bot_of_le_all_coe hleall'
        exact (IsGauge.ne_bot hk x) hkbot
      have hxg :
          (x, (epigraphClosureInf k x).toReal) ∈
            epigraph (S := (Set.univ : Set (Fin n → ℝ))) (epigraphClosureInf k) := by
        refine (mem_epigraph_univ_iff (f := epigraphClosureInf k) (x := x)
          (μ := (epigraphClosureInf k x).toReal)).2 ?_
        exact EReal.le_coe_toReal htop
      have hxk :
          (x, (epigraphClosureInf k x).toReal) ∈
            epigraph (S := (Set.univ : Set (Fin n → ℝ))) k := by
        simpa [hset] using hxg
      have hle_toReal :
          k x ≤ ((epigraphClosureInf k x).toReal : EReal) :=
        (mem_epigraph_univ_iff (f := k) (x := x)
          (μ := (epigraphClosureInf k x).toReal)).1 hxk
      have hcoe : ((epigraphClosureInf k x).toReal : EReal) = epigraphClosureInf k x :=
        EReal.coe_toReal htop hbot
      simpa [hcoe] using hle_toReal
  exact le_antisymm hle hge

/-- Closed gauges are fixed by double polarity. -/
lemma polarGauge_involutive_of_isGauge_isClosed_epigraph {n : ℕ} {k : (Fin n → ℝ) → EReal}
    (hk : IsGauge k)
    (hclosed : IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)) :
    polarGauge (polarGauge k) = k := by
  have hkCl :
      (fun x =>
        sInf
          {μ : EReal |
            ∃ r : ℝ,
              μ = (r : EReal) ∧
                (x, r) ∈ closure (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)}) =
        epigraphClosureInf k := kCl_eq_epigraphClosureInf (n := n) k
  have hfun : polarGauge (polarGauge k) = epigraphClosureInf k :=
    (polarGauge_bipolar_eq_kCl (k := k) hk).trans hkCl
  calc
    polarGauge (polarGauge k) = epigraphClosureInf k := hfun
    _ = k := epigraphClosureInf_eq_of_isGauge_isClosed_epigraph hk hclosed

/-- The polar gauge of a closed gauge is again a closed gauge. -/
lemma polarGauge_mapsTo_closedGauges {n : ℕ} {k : (Fin n → ℝ) → EReal} :
    (IsGauge k ∧ IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)) →
      (IsGauge (polarGauge k) ∧
        IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (polarGauge k))) := by
  intro hk
  refine ⟨polarGauge_isGauge (k := k), ?_⟩
  simpa using (isClosed_epigraph_polarGauge (k := k) hk.1)

/-- Corollary 15.1.1: The polarity mapping `k ↦ k^∘` induces a one-to-one symmetric correspondence
on the class of all closed gauges on `ℝⁿ`. Two closed convex sets containing the origin are polar
to each other if and only if their gauge functions are polar to each other. -/
theorem polarGauge_bijOn_closedGauges {n : ℕ} :
    Set.BijOn (fun k : (Fin n → ℝ) → EReal => polarGauge k)
      {k | IsGauge k ∧ IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)}
      {k | IsGauge k ∧ IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) k)} := by
  refine ⟨?hmap, ?hrest⟩
  · intro k hk
    exact polarGauge_mapsTo_closedGauges (k := k) hk
  · refine ⟨?hinj, ?hsurj⟩
    · intro k1 hk1 k2 hk2 hpol
      have h1 :
          polarGauge (polarGauge k1) = k1 :=
        polarGauge_involutive_of_isGauge_isClosed_epigraph hk1.1 hk1.2
      have h2 :
          polarGauge (polarGauge k2) = k2 :=
        polarGauge_involutive_of_isGauge_isClosed_epigraph hk2.1 hk2.2
      have hpol' := congrArg polarGauge hpol
      simpa [h1, h2] using hpol'
    · intro k hk
      refine ⟨polarGauge k, ?_, ?_⟩
      · exact polarGauge_mapsTo_closedGauges (k := k) hk
      · simpa using
          (polarGauge_involutive_of_isGauge_isClosed_epigraph hk.1 hk.2)

/-- The polar set is the `≤ 1` sublevel set of the support function. -/
lemma supportFunctionEReal_sublevel_one_eq_polarSet {n : ℕ} {C : Set (Fin n → ℝ)} :
    {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} =
      {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
  ext xStar; constructor
  · intro hx
    exact (section13_supportFunctionEReal_le_coe_iff (C := C) (y := xStar) (μ := (1 : ℝ))).1 hx
  · intro hx
    exact
      (section13_supportFunctionEReal_le_coe_iff (C := C) (y := xStar) (μ := (1 : ℝ))).2
        (by simpa using hx)

/-- The polar gauge of a gauge-function equals the support function under absorbing. -/
lemma polarGauge_gaugeFunction_eq_supportFunctionEReal {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCne : C.Nonempty)
    (hCabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C) :
    polarGauge (fun x => (gaugeFunction C x : EReal)) = supportFunctionEReal C := by
  have hCabs' : ∀ x : Fin n → ℝ, ∃ r : ℝ, 0 ≤ r ∧ ∃ y ∈ C, x = r • y := by
    intro x
    rcases hCabs x with ⟨r, hr0, hxmem⟩
    rcases hxmem with ⟨y, hyC, hxy⟩
    exact ⟨r, hr0, y, hyC, hxy.symm⟩
  funext xStar
  apply le_antisymm
  · exact polarGauge_of_gaugeFunction_le_supportFunctionEReal (C := C) hCne hCabs' xStar
  · exact supportFunctionEReal_le_polarGauge_of_gaugeFunction (C := C) xStar

/-- The support function is bounded above by the gauge of a polar set. -/
lemma supportFunctionEReal_le_gaugeFunction_of_polarSet {n : ℕ} {C D : Set (Fin n → ℝ)}
    (hDabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' D)
    (hD : D = {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1}) :
    ∀ xStar : Fin n → ℝ,
      supportFunctionEReal C xStar ≤ (gaugeFunction D xStar : EReal) := by
  intro xStar
  refine
    (section13_supportFunctionEReal_le_coe_iff (C := C) (y := xStar)
        (μ := gaugeFunction D xStar)).2 ?_
  intro x hxC
  let S : Set ℝ := {r : ℝ | 0 ≤ r ∧ ∃ y ∈ D, xStar = r • y}
  have hS_nonempty : S.Nonempty := by
    rcases hDabs xStar with ⟨r, hr0, hxmem⟩
    rcases hxmem with ⟨y, hyD, hxy⟩
    exact ⟨r, ⟨hr0, y, hyD, hxy.symm⟩⟩
  have hle : ∀ r ∈ S, dotProduct x xStar ≤ r := by
    intro r hr
    rcases hr with ⟨hr0, y, hyD, hxy⟩
    have hyD' : ∀ x ∈ C, (dotProduct x y : ℝ) ≤ 1 := by
      have : y ∈ {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
        simpa [hD] using hyD
      simpa using this
    have hxy_le : dotProduct x y ≤ 1 := hyD' x hxC
    have hdot : dotProduct x xStar = r * dotProduct x y := by
      simp [hxy, dotProduct_smul, smul_eq_mul]
    have hmul : r * dotProduct x y ≤ r * 1 :=
      mul_le_mul_of_nonneg_left hxy_le hr0
    have hmul' : r * dotProduct x y ≤ r := by simpa using hmul
    simpa [hdot] using hmul'
  have hxle : dotProduct x xStar ≤ sInf S := by
    exact le_csInf hS_nonempty (by intro r hr; exact hle r hr)
  simpa [gaugeFunction, S] using hxle

/-- The support function of a polar set agrees with the corresponding gauge function. -/
lemma supportFunctionEReal_eq_gaugeFunction_of_polarSet {n : ℕ} {C D : Set (Fin n → ℝ)}
    (hC0 : (0 : Fin n → ℝ) ∈ C)
    (hCabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C)
    (hDabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' D)
    (hD : D = {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1}) :
    supportFunctionEReal C = fun xStar => (gaugeFunction D xStar : EReal) := by
  have hD_sublevel :
      D = {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} := by
    calc
      D = {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} := hD
      _ = {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} := by
            symm
            exact supportFunctionEReal_sublevel_one_eq_polarSet (C := C)
  have hCne : C.Nonempty := ⟨0, hC0⟩
  have hpol :
      polarGauge (fun x => (gaugeFunction C x : EReal)) = supportFunctionEReal C :=
    polarGauge_gaugeFunction_eq_supportFunctionEReal (C := C) hCne hCabs
  have hk : IsGauge (supportFunctionEReal C) := by
    have hk' :
        IsGauge (polarGauge (fun x => (gaugeFunction C x : EReal))) :=
      polarGauge_isGauge (k := fun x => (gaugeFunction C x : EReal))
    simpa [hpol] using hk'
  have hk_finite : ∀ xStar, supportFunctionEReal C xStar ≠ ⊤ := by
    intro xStar
    have hle :
        supportFunctionEReal C xStar ≤ (gaugeFunction D xStar : EReal) :=
      supportFunctionEReal_le_gaugeFunction_of_polarSet (C := C) (D := D) hDabs hD xStar
    intro htop
    have hle' : (⊤ : EReal) ≤ (gaugeFunction D xStar : EReal) := by
      calc
        (⊤ : EReal) = supportFunctionEReal C xStar := htop.symm
        _ ≤ (gaugeFunction D xStar : EReal) := hle
    have htop' : (gaugeFunction D xStar : EReal) = ⊤ := (top_le_iff).1 hle'
    exact (EReal.coe_ne_top (gaugeFunction D xStar)) htop'
  have hEq :
      (fun xStar => (gaugeFunction D xStar : EReal)) = supportFunctionEReal C :=
    gaugeFunction_eq_of_convex_nonempty_eq_sublevel (n := n) (k := supportFunctionEReal C)
      (C := D) hD_sublevel hk hk_finite
  exact hEq.symm

/-- Corollary 15.1.1 (sets version): Two closed convex absorbing sets containing the origin are
polar to each other if and only if their gauge functions are polar to each other. -/
theorem closed_convex_sets_polar_iff_gaugeFunctions_polar {n : ℕ} {C D : Set (Fin n → ℝ)}
    (hC_closed : IsClosed C) (hC_conv : Convex ℝ C) (hC0 : (0 : Fin n → ℝ) ∈ C)
    (hCabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' C)
    (hD_closed : IsClosed D) (hD_conv : Convex ℝ D) (hD0 : (0 : Fin n → ℝ) ∈ D)
    (hDabs : ∀ x : Fin n → ℝ, ∃ lam : ℝ, 0 ≤ lam ∧ x ∈ (fun y => lam • y) '' D) :
    (D = {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} ∧
        C = {x | ∀ xStar ∈ D, (x ⬝ᵥ xStar : ℝ) ≤ 1}) ↔
      (polarGauge (fun x => (gaugeFunction C x : EReal)) =
          (fun xStar => (gaugeFunction D xStar : EReal)) ∧
        polarGauge (fun xStar => (gaugeFunction D xStar : EReal)) =
          (fun x => (gaugeFunction C x : EReal))) := by
  constructor
  · intro hpol
    rcases hpol with ⟨hD, hC⟩
    have hCne : C.Nonempty := ⟨0, hC0⟩
    have hDne : D.Nonempty := ⟨0, hD0⟩
    have hCpol :
        polarGauge (fun x => (gaugeFunction C x : EReal)) = supportFunctionEReal C :=
      polarGauge_gaugeFunction_eq_supportFunctionEReal (C := C) hCne hCabs
    have hDpol :
        polarGauge (fun x => (gaugeFunction D x : EReal)) = supportFunctionEReal D :=
      polarGauge_gaugeFunction_eq_supportFunctionEReal (C := D) hDne hDabs
    have hCD :
        supportFunctionEReal C = fun xStar => (gaugeFunction D xStar : EReal) :=
      supportFunctionEReal_eq_gaugeFunction_of_polarSet (C := C) (D := D)
        hC0 hCabs hDabs hD
    have hC' : C = {xStar | ∀ x ∈ D, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
      simpa [dotProduct_comm] using hC
    have hDC :
        supportFunctionEReal D = fun x => (gaugeFunction C x : EReal) :=
      supportFunctionEReal_eq_gaugeFunction_of_polarSet (C := D) (D := C)
        hD0 hDabs hCabs hC'
    refine ⟨?_, ?_⟩
    · calc
        polarGauge (fun x => (gaugeFunction C x : EReal))
            = supportFunctionEReal C := hCpol
        _ = (fun xStar => (gaugeFunction D xStar : EReal)) := hCD
    · calc
        polarGauge (fun xStar => (gaugeFunction D xStar : EReal))
            = supportFunctionEReal D := hDpol
        _ = (fun x => (gaugeFunction C x : EReal)) := hDC
  · intro hpol
    rcases hpol with ⟨hCD, hDC⟩
    have hCne : C.Nonempty := ⟨0, hC0⟩
    have hDne : D.Nonempty := ⟨0, hD0⟩
    have hCpol :
        polarGauge (fun x => (gaugeFunction C x : EReal)) = supportFunctionEReal C :=
      polarGauge_gaugeFunction_eq_supportFunctionEReal (C := C) hCne hCabs
    have hDpol :
        polarGauge (fun x => (gaugeFunction D x : EReal)) = supportFunctionEReal D :=
      polarGauge_gaugeFunction_eq_supportFunctionEReal (C := D) hDne hDabs
    have hCD' :
        supportFunctionEReal C = fun xStar => (gaugeFunction D xStar : EReal) := by
      simpa [hCpol] using hCD
    have hDC' :
        supportFunctionEReal D = fun x => (gaugeFunction C x : EReal) := by
      simpa [hDpol] using hDC
    have hDset :
        D = {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} := by
      have hDsub :
          D = {xStar | (gaugeFunction D xStar : EReal) ≤ (1 : EReal)} :=
        set_eq_gaugeFunction_sublevel_one (n := n) (D := D)
          hD_closed hD_conv hD0 hDabs
      simpa [hCD'] using hDsub
    have hCset :
        C = {x | supportFunctionEReal D x ≤ (1 : EReal)} := by
      have hCsub :
          C = {x | (gaugeFunction C x : EReal) ≤ (1 : EReal)} :=
        set_eq_gaugeFunction_sublevel_one (n := n) (D := C)
          hC_closed hC_conv hC0 hCabs
      simpa [hDC'] using hCsub
    have hDpolar :
        D = {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
      calc
        D = {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} := hDset
        _ = {xStar | ∀ x ∈ C, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
              exact supportFunctionEReal_sublevel_one_eq_polarSet (C := C)
    have hCpolar :
        C = {x | ∀ xStar ∈ D, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
      calc
        C = {x | supportFunctionEReal D x ≤ (1 : EReal)} := hCset
        _ = {x | ∀ xStar ∈ D, (x ⬝ᵥ xStar : ℝ) ≤ 1} := by
              simpa [dotProduct_comm] using
                (supportFunctionEReal_sublevel_one_eq_polarSet (C := D))
    exact ⟨hDpolar, hCpolar⟩


end Section15
end Chap03
