/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section09_part3

noncomputable section
open scoped Pointwise
open scoped BigOperators
open scoped Topology
open scoped RealInnerProductSpace

section Chap02
section Section09

/-- Membership in the kernel of `linearMap_prod` is componentwise. -/
lemma mem_ker_linearMap_prod_iff {n m : Nat}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) (p : (Fin n → Real) × Real) :
    p ∈ LinearMap.ker (linearMap_prod A) ↔ A p.1 = 0 ∧ p.2 = 0 := by
  constructor
  · intro hp
    have hmap : linearMap_prod A p = 0 := by
      simpa using hp
    have hmap1 : A p.1 = 0 := by
      have h := congrArg Prod.fst hmap
      simpa [linearMap_prod] using h
    have hmap2 : p.2 = 0 := by
      have h := congrArg Prod.snd hmap
      simpa [linearMap_prod] using h
    exact ⟨hmap1, hmap2⟩
  · rintro ⟨h1, h2⟩
    have hmap : linearMap_prod A p = 0 := by
      ext <;> simp [linearMap_prod, h1, h2]
    simpa using hmap

/-- Recession cones commute with linear equivalences. -/
lemma recessionCone_image_linearEquiv {E F : Type*} [AddCommGroup E] [Module Real E]
    [AddCommGroup F] [Module Real F] (e : E ≃ₗ[Real] F) (C : Set E) :
    Set.recessionCone (e '' C) = e '' Set.recessionCone C := by
  ext y
  constructor
  · intro hy
    have hy' : e.symm y ∈ Set.recessionCone C := by
      intro x hx t ht
      have hx' : e x ∈ e '' C := ⟨x, hx, rfl⟩
      have hmem : e x + t • y ∈ e '' C := hy hx' ht
      have hmem' : e (x + t • e.symm y) ∈ e '' C := by
        have hmap : e (x + t • e.symm y) = e x + t • y := by
          simp
        simpa [hmap] using hmem
      rcases hmem' with ⟨x', hx', hx'eq⟩
      have hx'eq' : x' = x + t • e.symm y := e.injective hx'eq
      simpa [hx'eq'] using hx'
    refine ⟨e.symm y, hy', by simp⟩
  · rintro ⟨z, hz, rfl⟩
    intro x hx t ht
    rcases hx with ⟨x', hx', rfl⟩
    have hmem : x' + t • z ∈ C := hz hx' ht
    refine ⟨x' + t • z, hmem, ?_⟩
    simp

/-- The recession cone of the embedded epigraph is the embedded epigraph of `h0_plus`. -/
lemma recessionCone_embedded_epigraph_eq_epigraph_h0_plus {n : Nat}
    {h h0_plus : (Fin n → Real) → EReal}
    (hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) h) =
        epigraph (Set.univ : Set (Fin n → Real)) h0_plus) :
    Set.recessionCone
        ((prodLinearEquiv_append (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) h) =
      (prodLinearEquiv_append (n := n)) ''
        epigraph (Set.univ : Set (Fin n → Real)) h0_plus := by
  calc
    Set.recessionCone
        ((prodLinearEquiv_append (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) h) =
        (prodLinearEquiv_append (n := n)) ''
          Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) h) := by
      exact
        (recessionCone_image_linearEquiv (e := prodLinearEquiv_append (n := n))
          (C := epigraph (Set.univ : Set (Fin n → Real)) h))
    _ =
        (prodLinearEquiv_append (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) h0_plus := by
      simp [hrec]

/-- Corollary 4.7.2 specialized to `h0_plus`. -/
lemma h0_plus_neg_ge_neg_of_posHom_proper {n : Nat}
    {h0_plus : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous h0_plus)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) h0_plus) :
    ∀ z : Fin n → Real, h0_plus (-z) ≥ -h0_plus z := by
  intro z
  exact convexFunction_neg_ge_neg_of_posHom_proper (hpos := hpos) (hproper := hproper) z

/-- Precomposition with a surjective linear map preserves proper convexity on `Set.univ`. -/
lemma properConvexFunctionOn_precomp_linearMap_surjective {n m : Nat}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hA : Function.Surjective A)
    {f : (Fin m → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin m → Real)) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => f (A x)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact convexFunctionOn_precomp_linearMap (A := A) (g := f) hf.1
  · rcases hf.2.1 with ⟨⟨y, μ⟩, hy⟩
    rcases hA y with ⟨x, rfl⟩
    refine ⟨(x, μ), ?_⟩
    have hy' : f (A x) ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff (f := f)).1 hy
    exact (mem_epigraph_univ_iff (f := fun x => f (A x))).2 hy'
  · intro x hx
    exact hf.2.2 (A x) (by simp)

/-- Kernel directions in the embedded recession cone are lineality directions. -/
lemma lineality_of_kernel_recession_embedded_epigraph {n m : Nat}
    {h h0_plus : (Fin n → Real) → EReal}
    (hclosed : ClosedConvexFunction h)
    (hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) h) =
        epigraph (Set.univ : Set (Fin n → Real)) h0_plus)
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hA :
      ∀ z : Fin n → Real,
        h0_plus z ≤ (0 : EReal) → h0_plus (-z) > (0 : EReal) → A z ≠ 0) :
    ∀ z, z ≠ 0 →
      z ∈ Set.recessionCone
        (closure ((prodLinearEquiv_append (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) h)) →
      (linearMap_prod_embedded (A := A)) z = 0 →
      z ∈ Set.linealitySpace
        (closure ((prodLinearEquiv_append (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) h)) := by
  classical
  let eN := prodLinearEquiv_append (n := n)
  let eM := prodLinearEquiv_append (n := m)
  let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
    eN '' epigraph (Set.univ : Set (Fin n → Real)) h
  let Aemb := linearMap_prod_embedded (A := A)
  intro z hz0 hzrec hAz
  have hclosed_sub :
      ∀ α : Real, IsClosed {x : Fin n → Real | h x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel (f := h)).1 hclosed.2
  have hclosed_epi :
      IsClosed (epigraph (Set.univ : Set (Fin n → Real)) h) :=
    closed_epigraph_of_closed_sublevel (f := h) hclosed_sub
  have hCclosed : IsClosed C := by
    let hhome := (eN.toAffineEquiv).toHomeomorphOfFiniteDimensional
    have hclosed' :
        IsClosed ((hhome : _ → _) '' epigraph (Set.univ : Set (Fin n → Real)) h) :=
      (hhome.isClosed_image (s := epigraph (Set.univ : Set (Fin n → Real)) h)).2 hclosed_epi
    simpa [C, hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
  have hzrec' : z ∈ Set.recessionCone C := by
    simpa [hCclosed.closure_eq, C] using hzrec
  have hrec_eq :
      Set.recessionCone C =
        (prodLinearEquiv_append (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) h0_plus := by
    simpa [C, eN] using
      (recessionCone_embedded_epigraph_eq_epigraph_h0_plus (h := h) (h0_plus := h0_plus) hrec)
  have hzmem :
      z ∈ (prodLinearEquiv_append (n := n)) ''
        epigraph (Set.univ : Set (Fin n → Real)) h0_plus := by
    simpa [hrec_eq] using hzrec'
  rcases hzmem with ⟨p, hp, rfl⟩
  rcases p with ⟨v, μ⟩
  have hle : h0_plus v ≤ (μ : EReal) :=
    (mem_epigraph_univ_iff (f := h0_plus)).1 hp
  have hker : linearMap_prod A (v, μ) = 0 := by
    have h := congrArg (fun w => (prodLinearEquiv_append (n := m)).symm w) hAz
    simpa [Aemb, linearMap_prod_embedded, LinearMap.comp_apply, eN, eM] using h
  have hker' : (v, μ) ∈ LinearMap.ker (linearMap_prod A) := by
    simpa using hker
  rcases (mem_ker_linearMap_prod_iff (A := A) (p := (v, μ))).1 hker' with ⟨hAv, hμ⟩
  have hμ' : μ = 0 := hμ
  have hle0 : h0_plus v ≤ (0 : EReal) := by
    simpa [hμ'] using hle
  have hneg : h0_plus (-v) ≤ (0 : EReal) := by
    by_contra hneg
    have hneg' : h0_plus (-v) > (0 : EReal) := lt_of_not_ge hneg
    exact (hA v hle0 hneg') hAv
  have hnegmem :
      -(prodLinearEquiv_append (n := n)) (v, μ) ∈
        (prodLinearEquiv_append (n := n)) ''
          epigraph (Set.univ : Set (Fin n → Real)) h0_plus := by
    refine ⟨(-v, -μ), ?_, ?_⟩
    · have hle' : h0_plus (-v) ≤ ((-μ) : EReal) := by
        simpa [hμ'] using hneg
      exact (mem_epigraph_univ_iff (f := h0_plus)).2 hle'
    · simpa using
        (LinearMap.map_neg (prodLinearEquiv_append (n := n)).toLinearMap (v, μ))
  have hzneg' :
      -(prodLinearEquiv_append (n := n)) (v, μ) ∈ Set.recessionCone C := by
    simpa [hrec_eq] using hnegmem
  have hzneg :
      -(prodLinearEquiv_append (n := n)) (v, μ) ∈
        Set.recessionCone (closure C) := by
    simpa [hCclosed.closure_eq] using hzneg'
  have hzneg_mem :
      (prodLinearEquiv_append (n := n)) (v, μ) ∈
        -Set.recessionCone (closure C) := by
    simpa using hzneg
  exact ⟨hzneg_mem, hzrec⟩

/-- The image epigraph has no downward vertical recession directions under `h0_plus`. -/
lemma no_downward_vertical_recession_image_epigraph {n m : Nat}
    {h h0_plus : (Fin n → Real) → EReal}
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) h)
    (hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) h) =
        epigraph (Set.univ : Set (Fin n → Real)) h0_plus)
    (hpos : PositivelyHomogeneous h0_plus)
    (hproper0 : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) h0_plus)
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hA :
      ∀ z : Fin n → Real,
        h0_plus z ≤ (0 : EReal) → h0_plus (-z) > (0 : EReal) → A z ≠ 0) :
    ¬ ∃ μ < 0,
      (0, μ) ∈ Set.recessionCone
        ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h) := by
  classical
  rintro ⟨μ, hμneg, hμrec⟩
  let eN := prodLinearEquiv_append (n := n)
  let eM := prodLinearEquiv_append (n := m)
  let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
    eN '' epigraph (Set.univ : Set (Fin n → Real)) h
  let Aemb := linearMap_prod_embedded (A := A)
  let Cimg : Set ((Fin m → Real) × Real) :=
    (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h
  have hCne : Set.Nonempty C := by
    rcases hproper.2.1 with ⟨p, hp⟩
    exact ⟨eN p, ⟨p, hp, rfl⟩⟩
  have hconv_epi :
      Convex Real (epigraph (Set.univ : Set (Fin n → Real)) h) :=
    convex_epigraph_of_convexFunctionOn (hf := hproper.1)
  have hCconv : Convex Real C := by
    simpa [C] using hconv_epi.linear_image eN.toLinearMap
  have hclosed_sub :
      ∀ α : Real, IsClosed {x : Fin n → Real | h x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel (f := h)).1 hclosed.2
  have hclosed_epi :
      IsClosed (epigraph (Set.univ : Set (Fin n → Real)) h) :=
    closed_epigraph_of_closed_sublevel (f := h) hclosed_sub
  have hCclosed : IsClosed C := by
    let hhome := (eN.toAffineEquiv).toHomeomorphOfFiniteDimensional
    have hclosed' :
        IsClosed ((hhome : _ → _) '' epigraph (Set.univ : Set (Fin n → Real)) h) :=
      (hhome.isClosed_image (s := epigraph (Set.univ : Set (Fin n → Real)) h)).2 hclosed_epi
    simpa [C, hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
  have hlineal :
      ∀ z, z ≠ 0 → z ∈ Set.recessionCone (closure C) → Aemb z = 0 →
        z ∈ Set.linealitySpace (closure C) := by
    simpa [C, Aemb] using
      (lineality_of_kernel_recession_embedded_epigraph (hclosed := hclosed) (hrec := hrec)
        (A := A) (hA := hA))
  have hmain :=
    linearMap_closure_image_eq_image_closure_of_recessionCone_kernel_lineality
      (n := n + 1) (m := m + 1) (C := C) hCne hCconv Aemb hlineal
  have hrec_emb :
      Set.recessionCone (Aemb '' C) = Aemb '' Set.recessionCone C := by
    have hrec' :
        Set.recessionCone (Aemb '' closure C) = Aemb '' Set.recessionCone (closure C) :=
      hmain.2.1
    simpa [hCclosed.closure_eq] using hrec'
  have himage_eq :
      eM '' Cimg = Aemb '' C := by
    simpa [C, eN, eM, Aemb, Cimg] using (image_linearMap_prod_embedded (A := A) (h := h))
  have hmem_emb :
      eM (0, μ) ∈ Set.recessionCone (eM '' Cimg) := by
    have hrec_eq := recessionCone_image_linearEquiv (e := eM) (C := Cimg)
    have : eM (0, μ) ∈ eM '' Set.recessionCone Cimg := ⟨(0, μ), hμrec, rfl⟩
    simpa [hrec_eq] using this
  have hmem_emb' : eM (0, μ) ∈ Aemb '' Set.recessionCone C := by
    have hrec_eq' : Set.recessionCone (eM '' Cimg) = Aemb '' Set.recessionCone C := by
      simpa [himage_eq] using hrec_emb
    simpa [hrec_eq'] using hmem_emb
  rcases hmem_emb' with ⟨z, hzrec, hzmap⟩
  have hzrec' : z ∈ eN '' Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) h) := by
    have hrec_eqN :=
      recessionCone_image_linearEquiv (e := eN)
        (C := epigraph (Set.univ : Set (Fin n → Real)) h)
    have hzrec'' : z ∈ Set.recessionCone (eN '' epigraph (Set.univ : Set (Fin n → Real)) h) := by
      simpa [C, eN] using hzrec
    simpa [hrec_eqN] using hzrec''
  rcases hzrec' with ⟨p, hp, rfl⟩
  have hmap :
      linearMap_prod A p = (0, μ) := by
    have hmap' : eM (linearMap_prod A p) = eM (0, μ) := by
      simpa [Aemb, linearMap_prod_embedded, LinearMap.comp_apply, eN, eM] using hzmap
    exact eM.injective hmap'
  rcases p with ⟨v, μ'⟩
  have hAv : A v = 0 := by
    have h := congrArg Prod.fst hmap
    simpa [linearMap_prod] using h
  have hμeq : μ' = μ := by
    have h := congrArg Prod.snd hmap
    simpa [linearMap_prod] using h
  have hle :
      h0_plus v ≤ (μ : EReal) := by
    have hp' : (v, μ') ∈ epigraph (Set.univ : Set (Fin n → Real)) h0_plus := by
      simpa [hrec] using hp
    have hle' : h0_plus v ≤ (μ' : EReal) :=
      (mem_epigraph_univ_iff (f := h0_plus)).1 hp'
    simpa [hμeq] using hle'
  have hμle : (μ : EReal) ≤ (0 : EReal) :=
    (EReal.coe_le_coe_iff).2 (le_of_lt hμneg)
  have hle0 : h0_plus v ≤ (0 : EReal) := le_trans hle hμle
  have hneg :
      h0_plus (-v) ≥ -h0_plus v :=
    h0_plus_neg_ge_neg_of_posHom_proper (hpos := hpos) (hproper := hproper0) v
  have hneg' : ((-μ : Real) : EReal) ≤ -h0_plus v := by
    have hneg'' : -(μ : EReal) ≤ -h0_plus v := by
      simpa [neg_le_neg_iff] using hle
    simpa [EReal.coe_neg] using hneg''
  have hμpos : (0 : EReal) < ((-μ : Real) : EReal) := by
    have hμpos' : (0 : Real) < -μ := by linarith
    exact (EReal.coe_lt_coe_iff).2 hμpos'
  have hpos : h0_plus (-v) > (0 : EReal) := by
    have hleμ : ((-μ : Real) : EReal) ≤ h0_plus (-v) := le_trans hneg' hneg
    exact lt_of_lt_of_le hμpos hleμ
  exact (hA v hle0 (by simpa using hpos)) hAv

/-- The image of the epigraph under the lifted linear map. -/
lemma image_epigraph_linearMap_eq {n m : Nat}
    {h : (Fin n → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h =
      {p : (Fin m → Real) × Real |
        ∃ x : Fin n → Real, A x = p.1 ∧ h x ≤ (p.2 : EReal)} := by
  classical
  ext p
  constructor
  · rintro ⟨⟨x, μ⟩, hx, rfl⟩
    have hxle : h x ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := h)).1 hx
    exact ⟨x, rfl, hxle⟩
  · rintro ⟨x, hxA, hxle⟩
    refine ⟨(x, p.2), ?_, ?_⟩
    · exact (mem_epigraph_univ_iff (f := h)).2 hxle
    · ext <;> simp [linearMap_prod, hxA]

/-- The projected epigraph is contained in the epigraph of the fiber infimum. -/
lemma image_epigraph_linearMap_subset_epigraph_infimum {n m : Nat}
    {h : (Fin n → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h ⊆
      epigraph (Set.univ : Set (Fin m → Real))
        (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) := by
  intro p hp
  rcases hp with ⟨⟨x, μ⟩, hx, rfl⟩
  have hxle : h x ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := h)).1 hx
  have hxmem :
      h x ∈ { z : EReal | ∃ x' : Fin n → Real, A x' = A x ∧ z = h x' } := by
    exact ⟨x, rfl, rfl⟩
  have hle :
      sInf { z : EReal | ∃ x' : Fin n → Real, A x' = A x ∧ z = h x' } ≤ h x :=
    sInf_le hxmem
  have hle' :
      sInf { z : EReal | ∃ x' : Fin n → Real, A x' = A x ∧ z = h x' } ≤ (μ : EReal) :=
    le_trans hle hxle
  exact (mem_epigraph_univ_iff
    (f := fun y => sInf { z : EReal | ∃ x' : Fin n → Real, A x' = y ∧ z = h x' })).2 hle'

/-- If the fiber infimum is not `⊤`, then the fiber is nonempty. -/
lemma exists_preimage_of_sInf_ne_top {n m : Nat} {h : (Fin n → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) {y : Fin m → Real}
    (hy :
      sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } ≠ (⊤ : EReal)) :
    ∃ x : Fin n → Real, A x = y := by
  classical
  by_contra hne
  have hset :
      { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact hne ⟨x, hx⟩
  have htop :
      sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } = (⊤ : EReal) := by
    simp [hset]
  exact hy htop

/-- If the fiber infimum is strictly below a real bound, there is a fiber point below that bound. -/
lemma exists_preimage_of_sInf_lt {n m : Nat} {h : (Fin n → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) {y : Fin m → Real} {μ : Real}
    (hμ :
      sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } < (μ : EReal)) :
    ∃ x : Fin n → Real, A x = y ∧ h x ≤ (μ : EReal) := by
  rcases (sInf_lt_iff).1 hμ with ⟨z, hz, hzlt⟩
  rcases hz with ⟨x, hx, rfl⟩
  exact ⟨x, hx, le_of_lt hzlt⟩

/-- Closed image of the epigraph identifies the epigraph of the fiber infimum. -/
lemma epigraph_infimum_eq_image_of_closed_image {n m : Nat}
    {h : (Fin n → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hclosed :
      IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h)) :
    epigraph (Set.univ : Set (Fin m → Real))
        (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) =
      (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h := by
  classical
  apply Set.Subset.antisymm
  · intro p hp
    rcases p with ⟨y, μ⟩
    have hle :
        sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff
        (f := fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x })).1 hp
    have hseq :
        ∀ k : ℕ,
          (y, μ + 1 / ((k : ℝ) + 1)) ∈
            (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h := by
      intro k
      have hpos : 0 < (1 / ((k : ℝ) + 1)) := by
        have hden : 0 < (k : ℝ) + 1 := by nlinarith
        exact one_div_pos.2 hden
      have hμlt_real : μ < μ + 1 / ((k : ℝ) + 1) := by linarith
      have hμlt :
          (μ : EReal) < (μ + 1 / ((k : ℝ) + 1) : ℝ) :=
        (EReal.coe_lt_coe_iff).2 hμlt_real
      have hlt :
          sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } <
            (μ + 1 / ((k : ℝ) + 1) : ℝ) :=
        lt_of_le_of_lt hle hμlt
      rcases (sInf_lt_iff).1 hlt with ⟨z, hz, hzlt⟩
      rcases hz with ⟨x, hxA, rfl⟩
      have hxle : h x ≤ (μ + 1 / ((k : ℝ) + 1) : ℝ) := le_of_lt hzlt
      refine ⟨(x, μ + 1 / ((k : ℝ) + 1)), ?_, ?_⟩
      · exact (mem_epigraph_univ_iff (f := h)).2 hxle
      · ext <;> simp [linearMap_prod, hxA]
    have htend :
        Filter.Tendsto (fun k : ℕ => (y, μ + 1 / ((k : ℝ) + 1))) Filter.atTop
          (𝓝 (y, μ)) := by
      refine (Prod.tendsto_iff
        (seq := fun k : ℕ => (y, μ + 1 / ((k : ℝ) + 1)))
        (p := (y, μ))).2 ?_
      constructor
      · exact
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => y) Filter.atTop (𝓝 y))
      · have hconst :
            Filter.Tendsto (fun _ : ℕ => μ) Filter.atTop (𝓝 μ) := tendsto_const_nhds
        have hdiv :
            Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1))
              Filter.atTop (𝓝 (0 : ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        have hsum := hconst.add hdiv
        simpa [add_zero] using hsum
    have hmem :
        ∀ᶠ k : ℕ in Filter.atTop,
          (y, μ + 1 / ((k : ℝ) + 1)) ∈
            (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h :=
      Filter.Eventually.of_forall hseq
    have hmem' :
        (y, μ) ∈ (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h :=
      hclosed.mem_of_tendsto htend hmem
    exact hmem'
  · exact image_epigraph_linearMap_subset_epigraph_infimum (A := A)

/-- If a fiber infimum is `⊥`, the projected epigraph has a negative vertical recession
direction. -/
lemma exists_negative_vertical_recession_of_bot {n m : Nat} {h : (Fin n → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) h)
    (himage_closed :
      IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h))
    (hEq_epi :
      epigraph (Set.univ : Set (Fin m → Real))
          (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) =
        (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h)
    {y : Fin m → Real}
    (hbot :
      sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } = (⊥ : EReal)) :
    ∃ μ < 0, (0, μ) ∈ Set.recessionCone
      ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h) := by
  classical
  let Cimg : Set ((Fin m → Real) × Real) :=
    (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h
  have hmem_epi :
      ∀ μ : Real,
        (y, μ) ∈
          epigraph (Set.univ : Set (Fin m → Real))
            (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) := by
    intro μ
    have hle :
        sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } ≤ (μ : EReal) := by
      simp [hbot]
    exact (mem_epigraph_univ_iff
      (f := fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x })).2 hle
  have hmem_img : ∀ μ : Real, (y, μ) ∈ Cimg := by
    intro μ
    have hmem := hmem_epi μ
    simpa [hEq_epi, Cimg] using hmem
  have hline :
      ∀ t : Real, 0 ≤ t → (y, 0) + t • (0, (-1 : Real)) ∈ Cimg := by
    intro t ht
    have hmem : (y, -t) ∈ Cimg := hmem_img (-t)
    simpa using hmem
  let eM := prodLinearEquiv_append (n := m)
  let Cemb : Set (EuclideanSpace Real (Fin (m + 1))) := eM '' Cimg
  have hCimg_ne : Set.Nonempty Cimg := by
    rcases hproper.2.1 with ⟨p, hp⟩
    exact ⟨linearMap_prod A p, ⟨p, hp, rfl⟩⟩
  have hCemb_ne : Set.Nonempty Cemb := hCimg_ne.image eM
  have hconv_epi :
      Convex Real (epigraph (Set.univ : Set (Fin n → Real)) h) :=
    convex_epigraph_of_convexFunctionOn (hf := hproper.1)
  have hconv_img : Convex Real Cimg := by
    simpa [Cimg] using hconv_epi.linear_image (linearMap_prod A)
  have hconv_emb : Convex Real Cemb := by
    simpa [Cemb] using hconv_img.linear_image eM.toLinearMap
  have hclosed_emb : IsClosed Cemb := by
    let hhome := (eM.toAffineEquiv).toHomeomorphOfFiniteDimensional
    have hclosed' : IsClosed ((hhome : _ → _) '' Cimg) :=
      (hhome.isClosed_image (s := Cimg)).2 (by simpa using himage_closed)
    simpa [Cemb, hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
  have hline_emb :
      ∀ t : Real, 0 ≤ t →
        eM (y, 0) + t • eM (0, (-1 : Real)) ∈ Cemb := by
    intro t ht
    have hmem : (y, 0) + t • (0, (-1 : Real)) ∈ Cimg := hline t ht
    have hmem' :
        eM ((y, 0) + t • (0, (-1 : Real))) ∈ Cemb := ⟨_, hmem, rfl⟩
    have hmap :
        eM ((y, 0) + t • (0, (-1 : Real))) =
          eM (y, 0) + t • eM (0, (-1 : Real)) := by
      let eMlin : ((Fin m → Real) × Real) →ₗ[Real] EuclideanSpace Real (Fin (m + 1)) := eM
      change eMlin ((y, 0) + t • (0, (-1 : Real))) =
          eMlin (y, 0) + t • eMlin (0, (-1 : Real))
      calc
        eMlin ((y, 0) + t • (0, (-1 : Real))) =
            eMlin (y, 0) + eMlin (t • (0, (-1 : Real))) := by
              exact (LinearMap.map_add (f := eMlin) (y, 0) (t • (0, (-1 : Real))))
        _ = eMlin (y, 0) + t • eMlin (0, (-1 : Real)) := by
              rw [LinearMap.map_smul (fₗ := eMlin) t (0, (-1 : Real))]
    exact hmap ▸ hmem'
  have hdir_ne : eM (0, (-1 : Real)) ≠ (0 : EuclideanSpace Real (Fin (m + 1))) := by
    intro h
    have h' : (0, (-1 : Real)) = (0 : (Fin m → Real) × Real) := by
      apply eM.injective
      calc
        eM (0, (-1 : Real)) = 0 := h
        _ = eM (0 : (Fin m → Real) × Real) := by simp
    have : (-1 : Real) = 0 := by
      exact congrArg Prod.snd h'
    linarith
  have hrec_emb :
      eM (0, (-1 : Real)) ∈ Set.recessionCone Cemb := by
    have hex :
        ∃ x0 : EuclideanSpace Real (Fin (m + 1)),
          ∀ t : Real, 0 ≤ t → x0 + t • eM (0, (-1 : Real)) ∈ Cemb :=
      ⟨eM (y, 0), hline_emb⟩
    exact
      (recessionCone_of_exists_halfline (n := m + 1) (C := Cemb)
        hCemb_ne hclosed_emb hconv_emb hdir_ne hex).1
  have hrec_img : (0, (-1 : Real)) ∈ Set.recessionCone Cimg := by
    have hrec_eq :
        Set.recessionCone Cemb = eM '' Set.recessionCone Cimg := by
      simpa [Cemb] using (recessionCone_image_linearEquiv (e := eM) (C := Cimg))
    have hrec_emb' : eM (0, (-1 : Real)) ∈ eM '' Set.recessionCone Cimg := by
      simpa [hrec_eq] using hrec_emb
    rcases hrec_emb' with ⟨v, hv, hv_eq⟩
    have hv_eq' : v = (0, (-1 : Real)) := eM.injective hv_eq
    simpa [hv_eq'] using hv
  exact ⟨-1, by linarith, by simpa [Cimg] using hrec_img⟩

/-- Theorem 9.2. Let `h` be a closed proper convex function on `R^n`, and let `A` be a linear
transformation from `R^n` to `R^m`. Assume that `A z ≠ 0` for every `z` such that
`(h0^+)(z) ≤ 0` and `(h0^+)(-z) > 0`. Then the function `Ah`, where
`(Ah)(y) = inf { h(x) | A x = y }`, is a closed proper convex function, and
`(Ah)0^+ = A(h0^+)`. Moreover, for each `y` such that `(Ah)(y) ≠ +infty`, the infimum
in the definition of `(Ah)(y)` is attained for some `x`. -/
theorem linearMap_infimum_closed_proper_convex_recession
    {n m : Nat} {h h0_plus : (Fin n → Real) → EReal}
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) h)
    (hrec :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → Real)) h) =
        epigraph (Set.univ : Set (Fin n → Real)) h0_plus)
    (hpos : PositivelyHomogeneous h0_plus)
    (hproper0 : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) h0_plus)
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hA :
      ∀ z : Fin n → Real,
        h0_plus z ≤ (0 : EReal) → h0_plus (-z) > (0 : EReal) → A z ≠ 0) :
    let Ah : (Fin m → Real) → EReal :=
      fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }
    let Ah0_plus : (Fin m → Real) → EReal :=
      fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h0_plus x }
    ClosedConvexFunction Ah ∧
      ProperConvexFunctionOn (Set.univ : Set (Fin m → Real)) Ah ∧
      Ah0_plus =
        (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h0_plus x }) ∧
      (∀ y : Fin m → Real, Ah y ≠ (⊤ : EReal) →
        ∃ x : Fin n → Real, A x = y ∧ Ah y = h x) := by
  classical
  dsimp
  have himage_closed :
      IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h) := by
    -- This should follow from the linear-image closedness theorem and the kernel/lineality
    -- hypothesis induced by the `h0_plus` condition.
    classical
    let eN := prodLinearEquiv_append (n := n)
    let eM := prodLinearEquiv_append (n := m)
    let C : Set (EuclideanSpace Real (Fin (n + 1))) :=
      eN '' epigraph (Set.univ : Set (Fin n → Real)) h
    let Aemb := linearMap_prod_embedded (A := A)
    have hCne : Set.Nonempty C := by
      rcases hproper.2.1 with ⟨p, hp⟩
      exact ⟨eN p, ⟨p, hp, rfl⟩⟩
    have hconv_epi :
        Convex Real (epigraph (Set.univ : Set (Fin n → Real)) h) :=
      convex_epigraph_of_convexFunctionOn (hf := hproper.1)
    have hCconv : Convex Real C := by
      simpa [C] using hconv_epi.linear_image eN.toLinearMap
    have hclosed_sub :
        ∀ α : Real, IsClosed {x : Fin n → Real | h x ≤ (α : EReal)} :=
      (lowerSemicontinuous_iff_closed_sublevel (f := h)).1 hclosed.2
    have hclosed_epi :
        IsClosed (epigraph (Set.univ : Set (Fin n → Real)) h) :=
      closed_epigraph_of_closed_sublevel (f := h) hclosed_sub
    have hCclosed : IsClosed C := by
      let hhome := (eN.toAffineEquiv).toHomeomorphOfFiniteDimensional
      have hclosed' :
          IsClosed ((hhome : _ → _) '' epigraph (Set.univ : Set (Fin n → Real)) h) :=
        (hhome.isClosed_image (s := epigraph (Set.univ : Set (Fin n → Real)) h)).2 hclosed_epi
      simpa [C, hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed'
    have hlineal :
        ∀ z,
          z ≠ 0 → z ∈ Set.recessionCone (closure C) → Aemb z = 0 →
            z ∈ Set.linealitySpace (closure C) := by
      simpa [C, Aemb] using
        (lineality_of_kernel_recession_embedded_epigraph (hclosed := hclosed) (hrec := hrec)
          (A := A) (hA := hA))
    have hmain :=
      linearMap_closure_image_eq_image_closure_of_recessionCone_kernel_lineality
        (n := n + 1) (m := m + 1) (C := C) hCne hCconv Aemb hlineal
    have hcl :
        closure (Aemb '' C) = Aemb '' closure C := hmain.1
    have hcl' : closure (Aemb '' C) = Aemb '' C := by
      simpa [hCclosed.closure_eq] using hcl
    have hclosed_embedded : IsClosed (Aemb '' C) :=
      (closure_eq_iff_isClosed).1 hcl'
    have himage_eq :
        eM '' ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h) =
          Aemb '' C := by
      simpa [C, eN, eM, Aemb] using (image_linearMap_prod_embedded (A := A) (h := h))
    have hclosed_image :
        IsClosed (eM '' ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h)) := by
      simpa [himage_eq] using hclosed_embedded
    let hhome := (eM.toAffineEquiv).toHomeomorphOfFiniteDimensional
    have hclosed' :
        IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h) :=
      (hhome.isClosed_image
        (s := (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h)).1
        (by
          simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed_image)
    exact hclosed'
  have hEq_epi :
      epigraph (Set.univ : Set (Fin m → Real))
          (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) =
        (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h :=
    epigraph_infimum_eq_image_of_closed_image (A := A) (h := h) himage_closed
  have hclosed_epi :
      IsClosed
        (epigraph (Set.univ : Set (Fin m → Real))
          (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x })) := by
    simpa [hEq_epi] using himage_closed
  have hconv :
      ConvexFunction
        (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) :=
    convexFunction_linearMap_infimum (A := A) (h := h) hclosed.1
  have hclosedAh : ClosedConvexFunction
      (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) := by
    refine ⟨hconv, ?_⟩
    have hclosed_sub :
        ∀ α : Real,
          IsClosed
            {x : Fin m → Real |
              sInf { z : EReal | ∃ x' : Fin n → Real, A x' = x ∧ z = h x' } ≤ (α : EReal)} := by
      exact
        (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph
          (f := fun y =>
            sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x })).2.mpr hclosed_epi
    exact
      (lowerSemicontinuous_iff_closed_sublevel
        (f := fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x })).2 hclosed_sub
  have hconv_on :
      ConvexFunctionOn (S := (Set.univ : Set (Fin m → Real)))
        (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) :=
    convexFunctionOn_inf_fiber_linearMap (A := A) (h := h) hproper.1
  have hne_epi :
      Set.Nonempty
        (epigraph (Set.univ : Set (Fin m → Real))
          (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x })) :=
    nonempty_epigraph_linearMap_infimum (A := A) (h := h) hproper.2.1
  have hproperAh :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → Real))
        (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) := by
    refine ⟨hconv_on, hne_epi, ?_⟩
    intro y _ hbot
    -- exclude `⊥` values using the recession condition on `h0_plus`
    have hneg :
        ∃ μ < 0,
          (0, μ) ∈ Set.recessionCone
            ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h) := by
      exact
        exists_negative_vertical_recession_of_bot (A := A) (hproper := hproper)
          himage_closed hEq_epi (y := y) hbot
    have hno_vertical :
        ¬ ∃ μ < 0,
          (0, μ) ∈ Set.recessionCone
            ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h) := by
      exact
        no_downward_vertical_recession_image_epigraph (hclosed := hclosed) (hproper := hproper)
          (hrec := hrec) (hpos := hpos) (hproper0 := hproper0) (A := A) (hA := hA)
    exact (hno_vertical hneg)
  refine ⟨hclosedAh, hproperAh, rfl, ?_⟩
  intro y hy
  have hbot :
      sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } ≠ (⊥ : EReal) := by
    have hne := hproperAh.2.2 y (by simp)
    simpa using hne
  have hAh_real :
      sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } =
        ((sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }).toReal : EReal) := by
    simpa using (EReal.coe_toReal hy hbot).symm
  have hmem_epi :
      (y, (sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }).toReal) ∈
        epigraph (Set.univ : Set (Fin m → Real))
          (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) := by
    have hle :
        sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } ≤
          ((sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }).toReal : EReal) :=
      EReal.le_coe_toReal hy
    exact (mem_epigraph_univ_iff
      (f := fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x })).2 hle
  have hmem_image :
      (y, (sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }).toReal) ∈
        (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → Real)) h := by
    simpa [hEq_epi] using hmem_epi
  have hmem' :
      ∃ x : Fin n → Real,
        A x = y ∧
          h x ≤
            ((sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }).toReal : EReal) := by
    simpa [image_epigraph_linearMap_eq (A := A) (h := h)] using hmem_image
  rcases hmem' with ⟨x, hxA, hxle⟩
  have hxmem :
      h x ∈ { z : EReal | ∃ x' : Fin n → Real, A x' = y ∧ z = h x' } := by
    exact ⟨x, hxA, rfl⟩
  have hle : sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } ≤ h x :=
    sInf_le hxmem
  have hge :
      h x ≤ sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } := by
    exact hAh_real.symm ▸ hxle
  exact ⟨x, hxA, le_antisymm hle hge⟩

/-- If `h0_plus` is strictly positive away from zero, then `h0_plus z ≤ 0` forces `z = 0`. -/
lemma h0_plus_le_zero_imp_zero {n : Nat} {h0_plus : (Fin n → Real) → EReal}
    (hno : ∀ z : Fin n → Real, z ≠ 0 → h0_plus z > (0 : EReal)) :
    ∀ z : Fin n → Real, h0_plus z ≤ (0 : EReal) → z = 0 := by
  intro z hzle
  by_contra hz0
  exact (not_lt_of_ge hzle) (hno z hz0)

/-- If `z = 0` and `h0_plus 0 = 0`, then `h0_plus (-z) = 0`. -/
lemma h0_plus_neg_eq_zero_of_z_eq_zero {n : Nat} {h0_plus : (Fin n → Real) → EReal}
    (hzero : h0_plus (0 : Fin n → Real) = (0 : EReal)) :
    ∀ z : Fin n → Real, z = 0 → h0_plus (-z) = (0 : EReal) := by
  intro z hz
  simp [hz, hzero]

/-- The coordinate-sum linear map on function blocks. -/
def sumLinearMapFun {n m : Nat} :
    (Fin m → (Fin n → Real)) →ₗ[Real] (Fin n → Real) :=
  { toFun := fun x => ∑ i, x i
    map_add' := by
      intro x y
      simp [Finset.sum_add_distrib]
    map_smul' := by
      intro r x
      simpa using
        (Finset.smul_sum (s := (Finset.univ : Finset (Fin m)))
          (f := fun i => x i) (r := r)).symm }

/-- Linear equivalence between `Fin (m * n) → Real` and block functions. -/
noncomputable def blockEquivFun {n m : Nat} :
    (Fin (m * n) → Real) ≃ₗ[Real] (Fin m → (Fin n → Real)) := by
  classical
  let e0 :=
    (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (m * n))).symm.toLinearEquiv
  let e1 := euclideanSpace_equiv_prod_block (n := n) (m := m)
  let e2 :=
    LinearEquiv.piCongrRight (R := Real) (ι := Fin m) (fun _ =>
      (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).toLinearEquiv)
  exact e0.trans (e1.trans e2)

/-- Block-sum linear map on function spaces. -/
noncomputable def blockSumLinearMapFun {n m : Nat} :
    (Fin (m * n) → Real) →ₗ[Real] (Fin n → Real) :=
  (sumLinearMapFun (n := n) (m := m)).comp
    (blockEquivFun (n := n) (m := m)).toLinearMap

/-- Remark 9.2.0.2. The hypothesis of Theorem 9.2 concerning `h0_plus` is trivially satisfied
if `h` has no directions of recession, in particular if `dom h` is bounded; the example at the
beginning of this section violates this hypothesis. -/
lemma linearMap_infimum_hypothesis_trivial_of_no_recession_direction
    {n m : Nat} {h0_plus : (Fin n → Real) → EReal}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (hno : ∀ z : Fin n → Real, z ≠ 0 → h0_plus z > (0 : EReal))
    (hzero : h0_plus (0 : Fin n → Real) = (0 : EReal)) :
    ∀ z : Fin n → Real, h0_plus z ≤ (0 : EReal) → h0_plus (-z) > (0 : EReal) → A z ≠ 0 := by
  intro z hzle hzneg
  have hz : z = 0 :=
    h0_plus_le_zero_imp_zero (hno := hno) z hzle
  have hzero' : h0_plus (-z) = (0 : EReal) :=
    h0_plus_neg_eq_zero_of_z_eq_zero (hzero := hzero) z hz
  have hfalse : False := by
    simp [hzero'] at hzneg
  exact hfalse.elim

end Section09
end Chap02
