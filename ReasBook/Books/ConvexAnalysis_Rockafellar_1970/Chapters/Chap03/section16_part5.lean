/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Weiran Shi, Yunxi Duan, Zaiwen Wen
-/

import Mathlib

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap03.section16_part4

section Chap03
section Section16

open scoped BigOperators
open scoped Pointwise

/-- In the improper case, the conjugates are identically `⊤`. -/
lemma section16_fenchelConjugate_precomp_eq_top_of_improper_of_exists_mem_ri
    {n m : Nat} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (g : (Fin m → ℝ) → EReal) (hg : ConvexFunction g)
    (hri :
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) g))
    (hproper : ¬ ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    (fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) = constPosInf n) ∧
      (fenchelConjugate m g = constPosInf m) := by
  classical
  have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g := by
    simpa [ConvexFunction] using hg
  have himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g :=
    ⟨hconv_on, hproper⟩
  rcases hri with ⟨x0, hx0⟩
  have hxbot : g (A x0 : Fin m → ℝ) = (⊥ : EReal) :=
    improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := g) himproper (x := A x0) hx0
  have hbot : ∃ x : Fin m → ℝ, g x = (⊥ : EReal) := ⟨(A x0 : Fin m → ℝ), hxbot⟩
  have hbot_precomp :
      ∃ x : Fin n → ℝ, g (A (WithLp.toLp 2 x) : Fin m → ℝ) = (⊥ : EReal) := by
    refine ⟨WithLp.ofLp x0, ?_⟩
    simpa [WithLp.toLp_ofLp] using hxbot
  have hstar : fenchelConjugate m g = constPosInf m := by
    funext xStar
    apply le_antisymm
    · exact le_top
    · rcases hbot with ⟨x, hx⟩
      have htop : ((x ⬝ᵥ xStar : ℝ) : EReal) - g x = (⊤ : EReal) := by
        simp [hx]
      have hmem :
          (⊤ : EReal) ∈
            Set.range (fun y : Fin m → ℝ => ((y ⬝ᵥ xStar : ℝ) : EReal) - g y) := by
        refine ⟨x, ?_⟩
        exact htop
      simpa [constPosInf, fenchelConjugate] using (le_sSup hmem)
  have hstar_precomp :
      fenchelConjugate n (fun x => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) = constPosInf n := by
    funext xStar
    apply le_antisymm
    · exact le_top
    · rcases hbot_precomp with ⟨x, hx⟩
      have htop :
          ((x ⬝ᵥ xStar : ℝ) : EReal) - g (A (WithLp.toLp 2 x) : Fin m → ℝ) = (⊤ : EReal) := by
        simp [hx]
      have hmem :
          (⊤ : EReal) ∈
            Set.range
              (fun y : Fin n → ℝ =>
                ((y ⬝ᵥ xStar : ℝ) : EReal) - g (A (WithLp.toLp 2 y) : Fin m → ℝ)) := by
        refine ⟨x, ?_⟩
        exact htop
      simpa [constPosInf, fenchelConjugate] using (le_sSup hmem)
  exact ⟨hstar_precomp, hstar⟩

/-- Closure commutes with linear precomposition under a relative-interior preimage point. -/
lemma section16_convexFunctionClosure_precomp_eq_precomp_convexFunctionClosure_of_exists_mem_ri
    {n m : Nat} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    {g : (Fin m → ℝ) → EReal}
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hri :
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) g)) :
    convexFunctionClosure (fun x : Fin n → ℝ => g (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
      fun x => convexFunctionClosure g (A (WithLp.toLp 2 x) : Fin m → ℝ) := by
  classical
  let e_n := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n))
  let e_m := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m))
  let A' : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    e_m.toLinearMap.comp (A.comp e_n.symm.toLinearMap)
  have hri' :
      ∃ x : Fin n → ℝ,
        e_m.symm (A' x) ∈
          euclideanRelativeInterior m
            (Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g)) := by
    rcases hri with ⟨x0, hx0⟩
    refine ⟨e_n x0, ?_⟩
    have himage :
        Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) =
          e_m ⁻¹' effectiveDomain (Set.univ : Set (Fin m → ℝ)) g := by
      simpa using
        (ContinuousLinearEquiv.image_eq_preimage_symm
          (e := e_m.symm)
          (s := effectiveDomain (Set.univ : Set (Fin m → ℝ)) g))
    have hx0' :
        A x0 ∈
          euclideanRelativeInterior m
            (Set.image e_m.symm (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g)) := by
      simpa [himage] using hx0
    have hA' : e_m.symm (A' (e_n x0)) = A x0 := by
      simp [A', e_n, e_m]
    simpa [hA'] using hx0'
  have hmain :=
    convexFunctionClosure_precomp_linearMap_eq (hgproper := hgproper) (A := A') hri'
  have hA' :
      ∀ x : Fin n → ℝ, A' x = (A (WithLp.toLp 2 x) : Fin m → ℝ) := by
    intro x
    have htoLp :
        WithLp.toLp 2 (A (WithLp.toLp 2 x) : Fin m → ℝ) = A (WithLp.toLp 2 x) := by
      simp [WithLp.toLp_ofLp]
    calc
      A' x = e_m (A (WithLp.toLp 2 x)) := by
        simp [A', e_n, e_m]
      _ = e_m (WithLp.toLp 2 (A (WithLp.toLp 2 x) : Fin m → ℝ)) := by
        simp [htoLp]
      _ = (A (WithLp.toLp 2 x) : Fin m → ℝ) := by
        simpa using
          (section16_euclideanSpace_equiv_toLp
            (x := (A (WithLp.toLp 2 x) : Fin m → ℝ)))
  simpa [hA'] using hmain

/-- Closedness and attainment for the adjoint-image infimum under the `ri` condition. -/
lemma section16_adjointImage_closed_and_attained_of_exists_mem_ri_effectiveDomain
    {n m : Nat} (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (g : (Fin m → ℝ) → EReal)
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hri :
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) g)) :
    let Aadj :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      ((LinearMap.adjoint :
              (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
                (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
            A)
    let gStar : (Fin m → ℝ) → EReal := fenchelConjugate m g
    let h : (Fin n → ℝ) → EReal :=
      fun xStar : Fin n → ℝ =>
        sInf
          ((fun yStar : EuclideanSpace ℝ (Fin m) => gStar (yStar : Fin m → ℝ)) ''
            {yStar | Aadj yStar = WithLp.toLp 2 xStar})
    (convexFunctionClosure h = h) ∧
      ∀ xStar : Fin n → ℝ,
        h xStar = ⊤ ∨
          ∃ yStar : EuclideanSpace ℝ (Fin m),
            Aadj yStar = WithLp.toLp 2 xStar ∧
              gStar (yStar : Fin m → ℝ) = h xStar := by
  classical
  let Aadj :
      EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((LinearMap.adjoint :
            (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ⋆[ℝ]
              (EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
          A)
  let gStar : (Fin m → ℝ) → EReal := fenchelConjugate m g
  let h : (Fin n → ℝ) → EReal :=
    fun xStar : Fin n → ℝ =>
      sInf
        ((fun yStar : EuclideanSpace ℝ (Fin m) => gStar (yStar : Fin m → ℝ)) ''
          {yStar | Aadj yStar = WithLp.toLp 2 xStar})
  let h0_plus : (Fin m → ℝ) → EReal := recessionFunction gStar
  let e_n := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n))
  let e_m := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m))
  let Aadj' : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    e_n.toLinearMap.comp (Aadj.comp e_m.symm.toLinearMap)
  have hAadj' :
      ∀ z : Fin m → ℝ,
        Aadj' z = (Aadj (WithLp.toLp 2 z) : Fin n → ℝ) := by
    intro z
    have htoLp :
        WithLp.toLp 2 (Aadj (WithLp.toLp 2 z) : Fin n → ℝ) = Aadj (WithLp.toLp 2 z) := by
      simp [WithLp.toLp_ofLp]
    calc
      Aadj' z = e_n (Aadj (e_m.symm z)) := by
        simp [Aadj', e_n, e_m]
      _ = e_n (Aadj (WithLp.toLp 2 z)) := by
        simp [e_m]
      _ = e_n (WithLp.toLp 2 (Aadj (WithLp.toLp 2 z) : Fin n → ℝ)) := by
        simp [htoLp]
      _ = (Aadj (WithLp.toLp 2 z) : Fin n → ℝ) := by
        simpa using
          (section16_euclideanSpace_equiv_toLp
            (x := (Aadj (WithLp.toLp 2 z) : Fin n → ℝ)))
  have hset :
      ∀ xStar : Fin n → ℝ,
        {yStar : EuclideanSpace ℝ (Fin m) | Aadj yStar = WithLp.toLp 2 xStar} =
          {yStar : EuclideanSpace ℝ (Fin m) | (Aadj yStar : Fin n → ℝ) = xStar} := by
    intro xStar
    ext yStar
    constructor
    · intro hy
      have hy' := congrArg (fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) hy
      simpa [WithLp.ofLp_toLp] using hy'
    · intro hy
      have hy' :=
        congrArg (fun z : Fin n → ℝ => (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))) hy
      simpa [WithLp.toLp_ofLp] using hy'
  let Ah : (Fin n → ℝ) → EReal :=
    fun xStar : Fin n → ℝ =>
      sInf
        {z : EReal |
          ∃ yStar : Fin m → ℝ, Aadj' yStar = xStar ∧ z = gStar yStar}
  have hAh : Ah = h := by
    funext xStar
    have hset' :
        {z : EReal | ∃ yStar : Fin m → ℝ, Aadj' yStar = xStar ∧ z = gStar yStar} =
          {z : EReal |
            ∃ yStar : EuclideanSpace ℝ (Fin m),
              (Aadj yStar : Fin n → ℝ) = xStar ∧ z = gStar (yStar : Fin m → ℝ)} := by
      ext z
      constructor
      · rintro ⟨yStar, hyA, rfl⟩
        refine ⟨WithLp.toLp 2 yStar, ?_, ?_⟩
        · have hyA' :
            (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ) = xStar := by
            simpa [hAadj' yStar] using hyA
          exact hyA'
        · simp
      · rintro ⟨yStar, hyA, rfl⟩
        have hyA' :
            (Aadj (WithLp.toLp 2 (yStar : Fin m → ℝ)) : Fin n → ℝ) = xStar := by
          simpa [WithLp.toLp_ofLp] using hyA
        have hyA'' : Aadj' (yStar : Fin m → ℝ) = xStar := by
          simpa [hAadj' (yStar : Fin m → ℝ)] using hyA'
        exact ⟨(yStar : Fin m → ℝ), hyA'', rfl⟩
    have himage :
        sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) => gStar (yStar : Fin m → ℝ)) ''
              {yStar : EuclideanSpace ℝ (Fin m) | (Aadj yStar : Fin n → ℝ) = xStar}) =
          sInf
            {z : EReal |
              ∃ yStar : EuclideanSpace ℝ (Fin m),
                (Aadj yStar : Fin n → ℝ) = xStar ∧ z = gStar (yStar : Fin m → ℝ)} := by
      simpa using
        (section16_sInf_image_fiber_eq_sInf_exists
          (φ := fun yStar : EuclideanSpace ℝ (Fin m) => gStar (yStar : Fin m → ℝ))
          (S := {yStar : EuclideanSpace ℝ (Fin m) | (Aadj yStar : Fin n → ℝ) = xStar}))
    have hrewrite :
        h xStar =
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) => gStar (yStar : Fin m → ℝ)) ''
              {yStar : EuclideanSpace ℝ (Fin m) | (Aadj yStar : Fin n → ℝ) = xStar}) := by
      simp [h, hset]
    calc
      Ah xStar =
          sInf
            {z : EReal |
              ∃ yStar : EuclideanSpace ℝ (Fin m),
                (Aadj yStar : Fin n → ℝ) = xStar ∧ z = gStar (yStar : Fin m → ℝ)} := by
          simp [Ah, hset']
      _ =
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin m) => gStar (yStar : Fin m → ℝ)) ''
              {yStar : EuclideanSpace ℝ (Fin m) | (Aadj yStar : Fin n → ℝ) = xStar}) := by
          symm
          exact himage
      _ = h xStar := by
          symm
          exact hrewrite
  have hclosedStar : ClosedConvexFunction gStar := by
    have h := fenchelConjugate_closedConvex (n := m) (f := g)
    exact ⟨h.2, h.1⟩
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) gStar :=
    proper_fenchelConjugate_of_proper (n := m) (f := g) hgproper
  have hsupp :
      supportFunctionEReal (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) = h0_plus := by
    simpa [h0_plus, gStar, recessionFunction] using
      (supportFunctionEReal_effectiveDomain_eq_recession_fenchelConjugate
        (n := m) (f := g) (hf := hgproper) (fStar0_plus := h0_plus) (by intro y; rfl))
  have hdom_ne :
      Set.Nonempty (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) :=
    section13_effectiveDomain_nonempty_of_proper (n := m) (f := g) hgproper
  have hdom_conv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) := by
    have hconv_on : ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) g := hgproper.1
    simpa using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin m → ℝ))) (f := g) (hf := hconv_on))
  have hsupp_props :=
    section13_supportFunctionEReal_closedProperConvex_posHom
      (n := m) (C := effectiveDomain (Set.univ : Set (Fin m → ℝ)) g) hdom_ne hdom_conv
  have hpos : PositivelyHomogeneous h0_plus := by
    simpa [hsupp] using hsupp_props.2.2
  have hproper0 :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) h0_plus := by
    simpa [hsupp] using hsupp_props.2.1
  have hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin m → ℝ)) gStar) =
        epigraph (Set.univ : Set (Fin m → ℝ)) h0_plus := by
    let f : Fin 1 → (Fin m → ℝ) → EReal := fun _ => gStar
    have hconv : ∀ i : Fin 1,
        Convex ℝ (epigraph (Set.univ : Set (Fin m → ℝ)) (f i)) := by
      intro i
      have hconvStar : ConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) gStar := by
        have hconv : ConvexFunction gStar :=
          (fenchelConjugate_closedConvex (n := m) (f := g)).2
        simpa [ConvexFunction] using hconv
      simpa [f] using
        (convex_epigraph_of_convexFunctionOn (hf := hconvStar))
    have hproper : ∀ i : Fin 1,
        ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (f i) := by
      intro i
      simpa [f] using hproperStar
    have hk : ∀ (i : Fin 1) (y : Fin m → ℝ),
        h0_plus y = sSup { r : EReal | ∃ x : Fin m → ℝ, r = f i (x + y) - f i x } := by
      intro i y
      simpa [f, h0_plus] using
        (section16_recessionFunction_eq_sSup_unrestricted (f := gStar) y)
    have hrec' :=
      recessionCone_epigraph_eq_epigraph_k (f := f) (k := h0_plus) hconv hproper hk
    simpa [f] using hrec' (i := 0)
  have hno :
      ¬ ∃ yStar : EuclideanSpace ℝ (Fin m),
          Aadj yStar = 0 ∧
            h0_plus (yStar : Fin m → ℝ) ≤ (0 : EReal) ∧
              h0_plus (-yStar : Fin m → ℝ) > (0 : EReal) := by
    have hcorr :=
      (section16_exists_image_mem_ri_effectiveDomain_iff_not_exists_adjoint_eq_zero_recession_ineq
        (A := A) (g := g) hgproper)
    have hno' :
        ¬ ∃ yStar : EuclideanSpace ℝ (Fin m),
            Aadj yStar = 0 ∧
              recessionFunction (fenchelConjugate m g) (yStar : Fin m → ℝ) ≤ (0 : EReal) ∧
                recessionFunction (fenchelConjugate m g) (-yStar : Fin m → ℝ) > (0 : EReal) := by
      exact (hcorr).mpr hri
    simpa [gStar, h0_plus] using hno'
  have hA' :
      ∀ z : Fin m → ℝ,
        h0_plus z ≤ (0 : EReal) →
          h0_plus (-z) > (0 : EReal) →
            Aadj' z ≠ 0 := by
    intro z hzle hzgt hAz
    have hAz' : (Aadj (WithLp.toLp 2 z) : Fin n → ℝ) = 0 := by
      simpa [hAadj' z] using hAz
    have hAz'' : Aadj (WithLp.toLp 2 z) = 0 := by
      ext i
      simpa using congrArg (fun f => f i) hAz'
    apply hno
    refine ⟨WithLp.toLp 2 z, hAz'', ?_, ?_⟩
    · simpa [WithLp.ofLp_toLp] using hzle
    · simpa [WithLp.ofLp_toLp] using hzgt
  have hmain :=
    linearMap_infimum_closed_proper_convex_recession (h := gStar) (h0_plus := h0_plus)
      hclosedStar hproperStar hrec hpos hproper0
      (A := Aadj') hA'
  have hclosedAh : ClosedConvexFunction Ah := by
    simpa [Ah] using hmain.1
  have hproperAh :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) Ah := by
    simpa [Ah] using hmain.2.1
  have hnotbot : ∀ x : Fin n → ℝ, Ah x ≠ (⊥ : EReal) := by
    intro x
    exact hproperAh.2.2 x (by simp)
  have hclosureAh : convexFunctionClosure Ah = Ah :=
    convexFunctionClosure_eq_of_closedConvexFunction (f := Ah) hclosedAh hnotbot
  have hclosure : convexFunctionClosure h = h := by
    simpa [hAh] using hclosureAh
  have hatt :
      ∀ xStar : Fin n → ℝ,
        h xStar = ⊤ ∨
          ∃ yStar : EuclideanSpace ℝ (Fin m),
            Aadj yStar = WithLp.toLp 2 xStar ∧
              gStar (yStar : Fin m → ℝ) = h xStar := by
    intro xStar
    have hAh_eq : Ah xStar = h xStar := by
      simpa using congrArg (fun f => f xStar) hAh
    have hatt' :
        Ah xStar = ⊤ ∨
          ∃ yStar : Fin m → ℝ,
            Aadj' yStar = xStar ∧ gStar yStar = Ah xStar := by
      by_cases htop : Ah xStar = ⊤
      · exact Or.inl htop
      · rcases (hmain.2.2.2 xStar htop) with ⟨yStar, hyA, hyEq⟩
        exact Or.inr ⟨yStar, hyA, hyEq.symm⟩
    cases hatt' with
    | inl htop =>
        left
        simpa [hAh_eq] using htop
    | inr hcase =>
        rcases hcase with ⟨yStar, hyA, hyEq⟩
        right
        have hyA' :
            Aadj (WithLp.toLp 2 yStar) = WithLp.toLp 2 xStar := by
          have hyA' :
              (Aadj (WithLp.toLp 2 yStar) : Fin n → ℝ) = xStar := by
            simpa [hAadj' yStar] using hyA
          have hyAset :
              (WithLp.toLp 2 yStar) ∈
                {yStar : EuclideanSpace ℝ (Fin m) | (Aadj yStar : Fin n → ℝ) = xStar} := by
            simpa using hyA'
          have hyAset' :
              (WithLp.toLp 2 yStar) ∈
                {yStar : EuclideanSpace ℝ (Fin m) | Aadj yStar = WithLp.toLp 2 xStar} := by
            simpa [hset xStar] using hyAset
          simpa using hyAset'
        have hyEq' : gStar (WithLp.toLp 2 yStar : Fin m → ℝ) = h xStar := by
          simpa [WithLp.ofLp_toLp, hAh_eq] using hyEq
        exact ⟨WithLp.toLp 2 yStar, hyA', hyEq'⟩
  exact ⟨hclosure, hatt⟩

/-- Properness and `ri`-compatibility for indicator functions under a feasible point. -/
lemma section16_properConvexFunctionOn_indicatorFunction_of_exists_mem_ri {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (D : Set (Fin m → ℝ))
    (hD : Convex ℝ D)
    (hri :
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹' D)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (indicatorFunction D) ∧
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) (indicatorFunction D)) := by
  classical
  rcases hri with ⟨x0, hx0⟩
  have hx0_mem_pre :
      A x0 ∈
        ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹' D) :=
    (euclideanRelativeInterior_subset_closure m
        ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹' D)).1 hx0
  have hx0_mem : (A x0 : Fin m → ℝ) ∈ D := by
    simpa using hx0_mem_pre
  have hDne : D.Nonempty := ⟨(A x0 : Fin m → ℝ), hx0_mem⟩
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (indicatorFunction D) :=
    properConvexFunctionOn_indicator_of_convex_of_nonempty (C := D) hD hDne
  have hri' :
      ∃ x : EuclideanSpace ℝ (Fin n),
        A x ∈
          euclideanRelativeInterior m
            ((fun z : EuclideanSpace ℝ (Fin m) => (z : Fin m → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin m → ℝ)) (indicatorFunction D)) := by
    refine ⟨x0, ?_⟩
    simpa [effectiveDomain_indicatorFunction_eq (C := D)] using hx0
  exact ⟨hproper, hri'⟩

/-- Precomposition of an indicator is the indicator of a preimage set. -/
lemma section16_indicator_precomp_eq_indicator_preimage {n m : Nat}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) (D : Set (Fin m → ℝ)) :
    (fun x : Fin n → ℝ => indicatorFunction D (A (WithLp.toLp 2 x) : Fin m → ℝ)) =
      indicatorFunction
        (Set.preimage (fun x : Fin n → ℝ => (A (WithLp.toLp 2 x) : Fin m → ℝ)) D) := by
  funext x
  by_cases hx : (A (WithLp.toLp 2 x) : Fin m → ℝ) ∈ D
  · simp [indicatorFunction, hx, Set.mem_preimage]
  · simp [indicatorFunction, hx, Set.mem_preimage]

end Section16
end Chap03
