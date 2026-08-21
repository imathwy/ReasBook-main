/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Guangxuan Pan, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Mathlib.Topology.Instances.EReal.Lemmas
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section06_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section07_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section10_part3

noncomputable section

section Chap02
section Section10

open scoped BigOperators Pointwise

/-- Theorem 10.3. Let `C` be a locally simplicial convex set, and let `f` be a finite convex
function on `ri C` which is bounded above on every bounded subset of `ri C`. Then `f` can be
extended in one and only one way to a continuous finite convex function on the whole of `C`. -/
theorem convexOn_exists_unique_continuousExtension_of_locallySimplicial {n : ℕ}
    {C : Set (Fin n → Real)} (hCconv : Convex ℝ C) (hCloc : Set.LocallySimplicial n C)
    (f : EuclideanSpace Real (Fin n) → Real)
    (hfconv :
      ConvexOn ℝ
        (euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C))
        f)
    (hf_bddAbove :
      ∀ s,
        s ⊆
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C) →
          Bornology.IsBounded s → BddAbove (f '' s)) :
    ∃ g : EuclideanSpace Real (Fin n) → Real,
      (ConvexOn ℝ ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C) g ∧
          Function.ContinuousRelativeTo g
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C) ∧
        (∀ x ∈
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C),
          g x = f x)) ∧
        ∀ g' : EuclideanSpace Real (Fin n) → Real,
          (ConvexOn ℝ ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C) g' ∧
              Function.ContinuousRelativeTo g'
                ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C) ∧
            (∀ x ∈
                euclideanRelativeInterior n
                  ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C),
              g' x = f x)) →
            ∀ x ∈ ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C),
              g' x = g x := by
  classical
  by_cases hCempty : C = ∅
  · subst hCempty
    refine ⟨(fun _ => 0), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · refine ⟨convex_empty, ?_⟩
        intro x hx y hy a b ha hb hab
        exact (hx.elim)
      · simp [Function.ContinuousRelativeTo]
      · intro x hx
        have hx' : x ∈ (∅ : Set (EuclideanSpace Real (Fin n))) :=
          (euclideanRelativeInterior_subset_closure n (∅ : Set (EuclideanSpace Real (Fin n)))).1 hx
        exact hx'.elim
    · intro g' hg' x hx
      simp at hx
  · have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCempty
    -- Set up the ambient Euclidean set and its relative interior.
    set CE : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C
    set riCE : Set (EuclideanSpace Real (Fin n)) := euclideanRelativeInterior n CE
    let e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
      EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)
    -- Extend `f` by `⊤` outside `riCE`, and form the convex closure.
    let F : (Fin n → Real) → EReal :=
      fun x : Fin n → Real => if e.symm x ∈ riCE then (f (e.symm x) : EReal) else (⊤ : EReal)
    let clF : (Fin n → Real) → EReal := convexFunctionClosure F
    -- `riCE` is nonempty because `CE` is a nonempty convex set.
    let A : EuclideanSpace Real (Fin n) →ₗ[Real] (Fin n → Real) := e.toLinearMap
    have hCEconv : Convex ℝ CE := by
      have hCE' : CE = A ⁻¹' C := by
        ext x
        simp [CE, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
      simpa [hCE'] using hCconv.linear_preimage A
    have hCEne : CE.Nonempty := by
      rcases hCne with ⟨y, hyC⟩
      refine ⟨e.symm y, ?_⟩
      -- show the coercion of `e.symm y` lies in `C`
      simpa [CE, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hyC
    have hriCEne : riCE.Nonempty := by
      have h := (euclideanRelativeInterior_closure_convex_affineSpan (n := n) (C := CE) hCEconv)
      exact h.2.2.2.2 hCEne
    have hFproper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) F := by
      simpa [F] using
        (Section10.properConvexFunctionOn_univ_extendTopOutside_ri (n := n) (riCE := riCE)
          hriCEne f hfconv e)
    have hcl_props :=
      convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := F) hFproper
    have hcl_closed : ClosedConvexFunction clF := by
      simpa [clF] using hcl_props.1.1
    have hcl_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) clF := by
      simpa [clF] using hcl_props.1.2
    have hagree :=
      (by
        intro x hx
        simpa [clF] using hcl_props.2 x hx :
        ∀ x ∈
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → Real)) F),
          clF x = F x)
    have hdomF :
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) F = riCE) ∧
          euclideanRelativeInterior n
              ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → Real)) F) = riCE := by
      simpa [CE, riCE, e, F] using
        (Section10.preimage_effectiveDomain_extendTopOutside_ri (n := n) (C := C) f)
    -- Finiteness of `clF` on `C` from boundedness on bounded subsets of `riCE`.
    have hCsub : C ⊆ effectiveDomain (Set.univ : Set (Fin n → Real)) clF := by
      intro y hyC
      have hyclosure : (e.symm y : EuclideanSpace Real (Fin n)) ∈ closure riCE := by
        have hcl_eq :
            closure riCE = closure CE :=
          (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq (n := n)
              (C := CE) hCEconv).1
        have hyCE : (e.symm y : EuclideanSpace Real (Fin n)) ∈ CE := by
          simpa [CE, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hyC
        have : (e.symm y : EuclideanSpace Real (Fin n)) ∈ closure CE := subset_closure hyCE
        simpa [hcl_eq] using this
      have hneTop :
          clF y ≠ (⊤ : EReal) := by
        simpa [clF, F] using
          (Section10.convexFunctionClosure_ne_top_of_mem_closure_ri_of_bddAbove
            (n := n) (riCE := riCE) (f := f) (hf_bddAbove := hf_bddAbove) (e := e) y hyclosure)
      have hltTop : clF y < (⊤ : EReal) := (lt_top_iff_ne_top).2 hneTop
      have :
          y ∈ {x | x ∈ (Set.univ : Set (Fin n → Real)) ∧ clF x < (⊤ : EReal)} := by
        exact ⟨by simp, hltTop⟩
      simpa [effectiveDomain_eq] using this
    -- Continuity of `clF` on `C` via Theorem 10.2.
    have hcont_clF_C : ContinuousOn clF C := by
      have hcont :=
        (convexFunctionOn_upperSemicontinuousOn_of_locallySimplicial (n := n) (f := clF)
            (hf := hcl_proper.1) (hS := hCloc) (hSdom := hCsub)).2
      exact hcont hcl_closed
    -- Define the real-valued extension on `CE` by `toReal`.
    let g : EuclideanSpace Real (Fin n) → Real := fun x => (clF (x : Fin n → Real)).toReal
    have hg_cont : Function.ContinuousRelativeTo g CE := by
      -- `clF` is continuous on `C`, hence `clF ∘ A` is continuous on `CE = A ⁻¹' C`.
      have hCE' : CE = A ⁻¹' C := by
        ext x
        simp [CE, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
      have hcont_clF_A :
          ContinuousOn (fun x : EuclideanSpace Real (Fin n) => clF (A x)) CE := by
        refine hcont_clF_C.comp (A.continuous_of_finiteDimensional.continuousOn) ?_
        intro x hx
        simpa [hCE'] using hx
      have hmaps :
          Set.MapsTo (fun x : EuclideanSpace Real (Fin n) => clF (A x)) CE
            ({⊥, ⊤}ᶜ : Set EReal) :=
        by
          intro x hx
          have hxC : A x ∈ C := by
            simpa [hCE'] using hx
          have hneTop : clF (A x) ≠ (⊤ : EReal) :=
            mem_effectiveDomain_imp_ne_top (S := Set.univ) (f := clF) (hCsub hxC)
          have hneBot : clF (A x) ≠ (⊥ : EReal) := hcl_proper.2.2 (A x) (by simp)
          exact by
            simp [Set.mem_compl_iff, Set.mem_insert_iff, hneBot, hneTop]
      have hcont_gA :
          ContinuousOn (fun x : EuclideanSpace Real (Fin n) => (clF (A x)).toReal) CE :=
        (EReal.continuousOn_toReal).comp hcont_clF_A hmaps
      -- Rewrite `(clF (A x)).toReal` as `g x`.
      have hrewrite :
          (fun x : EuclideanSpace Real (Fin n) => (clF (A x)).toReal) = g := by
        funext x
        simp [g, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
      simpa [Function.ContinuousRelativeTo, hrewrite] using hcont_gA
    have hg_conv : ConvexOn ℝ CE g := by
      -- Convexity of `toReal ∘ clF` on `effectiveDomain clF`.
      have hconv_dom :
          ConvexOn ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) clF)
            (fun x => (clF x).toReal) :=
        convexOn_toReal_on_effectiveDomain (f := clF) hcl_proper
      have hconv_C : ConvexOn ℝ C (fun x => (clF x).toReal) :=
        hconv_dom.subset hCsub hCconv
      have hCE' : CE = A ⁻¹' C := by
        ext x
        simp [CE, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
      have hconv_CE' :
          ConvexOn ℝ (A ⁻¹' C) ((fun x => (clF x).toReal) ∘ A) :=
        (ConvexOn.comp_linearMap (hf := hconv_C) A)
      -- Rewrite in terms of the coercion preimage `CE` and `g`.
      simpa [g, hCE', A, Function.comp, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
        hconv_CE'
    have hg_eq : ∀ x ∈ riCE, g x = f x := by
      intro x hxri
      have hx' :
          x ∈
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → Real)) F) := by
        simpa [hdomF.2] using hxri
      have hcl_eq : clF x = F x := hagree x hx'
      have hsymm : e.symm (x : Fin n → Real) = x := by
        have hx_eq : (x : Fin n → Real) = e x := by
          simp [e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
        simp [hx_eq]
      have hFx : F (x : Fin n → Real) = (f x : EReal) := by
        simp [F, hsymm, hxri]
      -- Convert the EReal equality to a real one via `toReal`.
      simp [g, hcl_eq, hFx]
    -- Uniqueness on `CE` from density of `riCE`.
    have hri_sub : riCE ⊆ CE := (euclideanRelativeInterior_subset_closure n CE).1
    have hCEclosure : CE ⊆ closure riCE := by
      have hcl_eq :
          closure riCE = closure CE :=
        (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq (n := n)
            (C := CE) hCEconv).1
      intro x hx
      have : x ∈ closure CE := subset_closure hx
      simpa [hcl_eq] using this
    refine ⟨g, ?_, ?_⟩
    · refine ⟨hg_conv, hg_cont, ?_⟩
      intro x hxri
      simpa [riCE] using hg_eq x hxri
    · intro g' hg'
      have hg'_cont :
          Function.ContinuousRelativeTo g'
            ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C) := hg'.2.1
      have hg'_eq :
          ∀ x ∈ riCE, g x = g' x := by
        intro x hxri
        have hgx : g x = f x := hg_eq x (by simpa [riCE] using hxri)
        have hg'x : g' x = f x := hg'.2.2 x (by simpa [riCE] using hxri)
        simp [hgx, hg'x]
      -- Apply the general density lemma.
      intro x hxCE
      have hgcont' : Function.ContinuousRelativeTo g CE := hg_cont
      have hg'cont' : Function.ContinuousRelativeTo g' CE := by
        simpa [CE] using hg'_cont
      exact
        by
          have hgg' :
              g x = g' x :=
            (Section10.unique_extension_on_C_of_continuous_eqOn_ri (n := n) (CE := CE) (riCE := riCE)
                hri_sub hCEclosure hgcont' hg'cont' (by
                  intro x hx
                  exact hg'_eq x hx))
              x (by simpa [CE] using hxCE)
          simpa using hgg'.symm

/-- Boundedness above on bounded subsets of the positive orthant, from coordinatewise monotonicity. -/
lemma Section10.bddAbove_image_of_monotoneOn_of_isBounded_posOrthant {n : ℕ}
    {f : (Fin n → Real) → Real} (hfmono : MonotoneOn f {x : Fin n → Real | ∀ i, 0 < x i})
    {s : Set (Fin n → Real)} (hs : s ⊆ {x : Fin n → Real | ∀ i, 0 < x i})
    (hsbdd : Bornology.IsBounded s) :
    BddAbove (f '' s) := by
  classical
  rcases hsbdd.subset_closedBall (0 : Fin n → Real) with ⟨R, hR⟩
  refine ⟨f (fun _ => max R 1), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxpos : x ∈ {x : Fin n → Real | ∀ i, 0 < x i} := hs hx
  have hmaxpos : 0 < max R 1 := by
    exact lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (le_max_right R 1)
  have hle : x ≤ fun _ => max R 1 := by
    intro i
    have hxball : x ∈ Metric.closedBall (0 : Fin n → Real) R := hR hx
    have hxnorm : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
    have hxi_norm : ‖x i‖ ≤ R := le_trans (norm_le_pi_norm (f := x) i) hxnorm
    have hxi_abs : |x i| ≤ R := by
      simpa [Real.norm_eq_abs] using hxi_norm
    have hxi_le : x i ≤ R := by
      simpa [abs_of_pos (hxpos i)] using hxi_abs
    exact le_trans hxi_le (le_max_left R 1)
  exact hfmono hxpos (by intro _; exact hmaxpos) hle

/-- The relative interior of the nonnegative orthant in `EuclideanSpace` is the positive orthant. -/
lemma Section10.euclideanRelativeInterior_preimage_nonnegOrthant {n : ℕ} :
    let C : Set (Fin n → Real) := {y : Fin n → Real | ∀ i, 0 ≤ y i}
    let CE : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C
    euclideanRelativeInterior n CE =
      {x : EuclideanSpace Real (Fin n) | ∀ i, 0 < (x : Fin n → Real) i} := by
  classical
  intro C CE
  let e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)
  have hcoe :
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) = fun x => e x := by
    funext x
    simp [e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
  have hCE' : CE = e ⁻¹' C := by
    ext x
    simp [CE, hcoe]
  have hCpi :
      C = (Set.univ : Set (Fin n)).pi (fun _ : Fin n => Set.Ici (0 : Real)) := by
    ext y
    simp [C, Set.pi]
  have hIntC : interior C = {y : Fin n → Real | ∀ i, 0 < y i} := by
    have hIntC' :
        interior C =
          (Set.univ : Set (Fin n)).pi (fun _ : Fin n => interior (Set.Ici (0 : Real))) := by
      simpa [hCpi] using
        (interior_pi_set (I := (Set.univ : Set (Fin n)))
          (hI := (Set.finite_univ : (Set.univ : Set (Fin n)).Finite))
          (s := fun _ : Fin n => Set.Ici (0 : Real)))
    ext y
    simp [hIntC', Set.pi]
  have hIntCE : interior CE = {x : EuclideanSpace Real (Fin n) | ∀ i, 0 < (x : Fin n → Real) i} := by
    have hinter :
        interior (e ⁻¹' C) = e ⁻¹' interior C := by
      simpa using (Homeomorph.preimage_interior (e.toHomeomorph) C).symm
    ext x
    constructor
    · intro hx
      have hx' : x ∈ e ⁻¹' interior C := by
        have : x ∈ interior (e ⁻¹' C) := by simpa [hCE'] using hx
        simpa [hinter] using this
      have : e x ∈ interior C := hx'
      have hxpos : ∀ i, 0 < (e x) i := by
        simpa [hIntC] using this
      intro i
      simpa [hcoe] using hxpos i
    · intro hxpos
      have hxpos' : ∀ i, 0 < (e x) i := by
        intro i
        simpa [hcoe] using hxpos i
      have : e x ∈ interior C := by
        simpa [hIntC] using hxpos'
      have : x ∈ e ⁻¹' interior C := this
      have : x ∈ interior (e ⁻¹' C) := by simpa [hinter] using this
      simpa [hCE'] using this
  -- `CE` is full-dimensional (its affine span is all of `ℝ^n`), hence `ri CE = interior CE`.
  have hCconv : Convex ℝ C := by
    simpa [hCpi] using
      (convex_pi (s := (Set.univ : Set (Fin n))) (t := fun _ : Fin n => Set.Ici (0 : Real))
        (by intro _ _; exact convex_Ici (0 : Real)))
  have hCEconv : Convex ℝ CE := by
    simpa [hCE'] using hCconv.linear_preimage e.toLinearMap
  have hIntCEne : (interior CE).Nonempty := by
    refine ⟨e.symm (fun _ : Fin n => (1 : Real)), ?_⟩
    have hxpos : ∀ i : Fin n, 0 < ((fun _ : Fin n => (1 : Real)) i) := by
      intro i; norm_num
    have : ∀ i, 0 < ((e.symm (fun _ : Fin n => (1 : Real)) : EuclideanSpace Real (Fin n)) : Fin n → Real) i := by
      intro i
      have hsymm :
          ((e.symm (fun _ : Fin n => (1 : Real)) : EuclideanSpace Real (Fin n)) : Fin n → Real) =
            (fun _ : Fin n => (1 : Real)) := by
        calc
          ((e.symm (fun _ : Fin n => (1 : Real)) : EuclideanSpace Real (Fin n)) : Fin n → Real) =
              e (e.symm (fun _ : Fin n => (1 : Real))) := by
                simpa using congrArg (fun f => f (e.symm (fun _ : Fin n => (1 : Real)))) hcoe
          _ = (fun _ : Fin n => (1 : Real)) := e.apply_symm_apply _
      simp [hsymm]
    simpa [hIntCE] using this
  have hIntHullCEne : (interior (convexHull ℝ CE)).Nonempty := by
    have hHull : convexHull ℝ CE = CE := hCEconv.convexHull_eq
    simpa [hHull] using hIntCEne
  have hAffTop : affineSpan ℝ CE = ⊤ :=
    affineSpan_eq_top_of_nonempty_interior hIntHullCEne
  have hAff : (affineSpan Real CE : Set (EuclideanSpace Real (Fin n))) = Set.univ := by
    simp [hAffTop]
  have hri : euclideanRelativeInterior n CE = interior CE :=
    euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ n CE hAff
  simp [hri, hIntCE]

/-- The coordinate singleton vectors `Pi.single i M` are linearly independent when `M ≠ 0`. -/
lemma Section10.linearIndependent_piSingle {n : ℕ} {M : Real} (hM : M ≠ 0) :
    LinearIndependent Real (fun i : Fin n => (Pi.single i M : Fin n → Real)) := by
  classical
  have hlin1 :
      LinearIndependent Real (fun i : Fin n => (Pi.single i (1 : Real) : Fin n → Real)) :=
    Pi.linearIndependent_single_one (Fin n) Real
  have hlinM :
      LinearIndependent Real
        (fun i : Fin n =>
          ((Units.mk0 M hM : Units Real) : Real) • (Pi.single i (1 : Real) : Fin n → Real)) :=
    hlin1.units_smul (fun _ => Units.mk0 M hM)
  have hlinM' :
      LinearIndependent Real (fun i : Fin n => M • (Pi.single i (1 : Real) : Fin n → Real)) := by
    simpa using hlinM
  have hsingle :
      (fun i : Fin n => M • (Pi.single i (1 : Real) : Fin n → Real)) =
        fun i : Fin n => (Pi.single i M : Fin n → Real) := by
    funext i
    ext j
    by_cases hji : j = i
    · subst j
      simp [Pi.single]
    · simp [Pi.single, hji]
  simpa [hsingle] using hlinM'

/-- The family of vertices `{0} ∪ {Pi.single i M}` is affinely independent when `M ≠ 0`. -/
lemma Section10.affineIndependent_zero_piSingle {n : ℕ} {M : Real} (hM : M ≠ 0) :
    let b : Fin (n + 1) → Fin n → Real := Fin.cases 0 (fun i : Fin n => Pi.single i M)
    AffineIndependent Real b := by
  classical
  cases n with
  | zero =>
      intro b
      -- The index type `Fin 1` is subsingleton, so any such family is affinely independent.
      haveI : Subsingleton (Fin 1) := by
        refine ⟨?_⟩
        intro i j
        fin_cases i; fin_cases j; rfl
      simpa using (affineIndependent_of_subsingleton (k := Real) b)
  | succ n =>
      intro b
      have hb0 : b 0 = 0 := by simp [b]
      -- Identify `{i : Fin (n+2) // i ≠ 0}` with `Fin (n+1)` via `succAbove`/`predAbove` at `0`.
      let e : {i : Fin (n + 2) // i ≠ 0} ≃ Fin (n + 1) :=
        { toFun := fun i => (0 : Fin (n + 1)).predAbove i.1
          invFun := fun j =>
            ⟨(0 : Fin (n + 2)).succAbove j, by
              simp⟩
          left_inv := by
            intro i
            apply Subtype.ext
            simpa using
              (Fin.succAbove_predAbove (p := (0 : Fin (n + 1))) (i := i.1) (by simpa using i.2))
          right_inv := by
            intro j
            exact Fin.predAbove_succAbove (p := (0 : Fin (n + 1))) (i := j) }
      have hlin_sub :
          LinearIndependent Real
            (fun i : {i : Fin (n + 2) // i ≠ 0} =>
              (b i -ᵥ b 0 : Fin (n + 1) → Real)) := by
        have hcomp :
            (fun i : Fin (n + 1) => (Pi.single i M : Fin (n + 1) → Real)) ∘ e =
              (fun i : {i : Fin (n + 2) // i ≠ 0} =>
                (b i -ᵥ b 0 : Fin (n + 1) → Real)) := by
          funext i
          have hi :
              (0 : Fin (n + 2)).succAbove ((0 : Fin (n + 1)).predAbove i.1) = i.1 := by
            simpa using
              (Fin.succAbove_predAbove (p := (0 : Fin (n + 1))) (i := i.1) (by simpa using i.2))
          have hbi : b i = Pi.single (e i) M := by
            have hb' :
                b i = b ((0 : Fin (n + 2)).succAbove ((0 : Fin (n + 1)).predAbove i.1)) := by
              simpa using (congrArg b hi.symm)
            calc
              b i = b ((0 : Fin (n + 2)).succAbove ((0 : Fin (n + 1)).predAbove i.1)) := hb'
              _ = Pi.single ((0 : Fin (n + 1)).predAbove i.1) M := by
                  simp [b]
              _ = Pi.single (e i) M := rfl
          simp [hbi, hb0, vsub_eq_sub]
        have hlin_comp :
            LinearIndependent Real
              ((fun i : Fin (n + 1) => (Pi.single i M : Fin (n + 1) → Real)) ∘ e) :=
          (linearIndependent_equiv e
              (f := fun i : Fin (n + 1) => (Pi.single i M : Fin (n + 1) → Real))).2
            (Section10.linearIndependent_piSingle (n := n + 1) (M := M) hM)
        simpa [hcomp] using hlin_comp
      exact
        (affineIndependent_iff_linearIndependent_vsub (k := Real) (p := b) (i1 := (0 : Fin (n + 2)))).2
          (by simpa [hb0] using hlin_sub)

/-- The convex hull of `{0} ∪ {Pi.single i M}` is an `n`-simplex when `M ≠ 0`. -/
lemma Section10.isSimplex_convexHull_zero_piSingle {n : ℕ} {M : Real} (hM : M ≠ 0) :
    let b : Fin (n + 1) → Fin n → Real := Fin.cases 0 (fun i : Fin n => Pi.single i M)
    IsSimplex n n (convexHull Real (Set.range b)) := by
  intro b
  refine ⟨b, Section10.affineIndependent_zero_piSingle (n := n) (M := M) hM, rfl⟩

/-- A nonnegative vector with sum bounded by `M` lies in the simplex `convexHull {0, M e_i}`. -/
lemma Section10.mem_convexHull_zero_piSingle_of_nonneg_sum_le {n : ℕ} {M : Real} (hM : 0 < M)
    (y : Fin n → Real) (hy0 : ∀ i, 0 ≤ y i) (hysum : (∑ i : Fin n, y i) ≤ M) :
    let b : Fin (n + 1) → Fin n → Real := Fin.cases 0 (fun i : Fin n => Pi.single i M)
    y ∈ convexHull Real (Set.range b) := by
  classical
  intro b
  have hM0 : M ≠ 0 := ne_of_gt hM
  -- Barycentric weights for the vertices `0, Pi.single i M`.
  let μ : Fin (n + 1) → Real :=
    Fin.cases (1 - (∑ i : Fin n, y i) / M) (fun i : Fin n => y i / M)
  have hμ0 : ∀ i, 0 ≤ μ i := by
    intro i
    cases i using Fin.cases with
    | zero =>
        -- weight at `0`
        have hle1 : (∑ i : Fin n, y i) / M ≤ (1 : Real) := (div_le_one hM).2 hysum
        -- `0 ≤ 1 - a` simplifies to `a ≤ 1`.
        simpa [μ, sub_nonneg] using hle1
    | succ i =>
        -- weights at `Pi.single i M`
        simpa [μ] using div_nonneg (hy0 i) (le_of_lt hM)
  have hμ1 : (∑ i : Fin (n + 1), μ i) = (1 : Real) := by
    calc
      (∑ i : Fin (n + 1), μ i) = μ 0 + ∑ i : Fin n, μ i.succ := by
        simpa using (Fin.sum_univ_succ μ)
      _ = (1 - (∑ i : Fin n, y i) / M) + ∑ i : Fin n, y i / M := by
        simp [μ]
      _ = (1 - (∑ i : Fin n, y i) / M) + ((∑ i : Fin n, y i) / M) := by
        congr 1
        -- `∑ (y i / M) = (∑ y i) / M`.
        symm
        simpa using
          (Finset.sum_div (s := (Finset.univ : Finset (Fin n))) (f := fun i : Fin n => y i)
            (a := M))
      _ = 1 := by ring
  have hterm (i : Fin n) :
      (y i / M) • (Pi.single i M : Fin n → Real) = (Pi.single i (y i) : Fin n → Real) := by
    ext j
    by_cases hji : j = i
    · subst j
      have hdiv : y i / M * M = y i := by field_simp [hM0]
      simp [Pi.single, hdiv]
    · simp [Pi.single, hji]
  have hμy : y = ∑ i : Fin (n + 1), μ i • b i := by
    have hsum :
        (∑ i : Fin (n + 1), μ i • b i) = y := by
      calc
        (∑ i : Fin (n + 1), μ i • b i) = μ 0 • b 0 + ∑ i : Fin n, μ i.succ • b i.succ := by
          simpa using (Fin.sum_univ_succ fun i : Fin (n + 1) => μ i • b i)
        _ = ∑ i : Fin n, (y i / M) • (Pi.single i M : Fin n → Real) := by
          simp [μ, b]
        _ = ∑ i : Fin n, (Pi.single i (y i) : Fin n → Real) := by
          simp [hterm]
        _ = y := by
          simpa using (Finset.univ_sum_single (fun i : Fin n => y i))
    exact hsum.symm
  have hy_mem :
      y ∈
      {z : Fin n → Real |
        ∃ w : Fin (n + 1) → Real,
          (∀ i, 0 ≤ w i) ∧ (∑ i, w i = (1 : Real)) ∧ z = ∑ i, w i • b i} := by
    exact ⟨μ, hμ0, hμ1, hμy⟩
  simpa [convexHull_range_eq_setOf_weighted_sum (n := n) (m := n) (b := b)] using hy_mem

/-- The nonnegative orthant is locally simplicial. -/
lemma Section10.locallySimplicial_nonnegOrthant {n : ℕ} :
    Set.LocallySimplicial n {y : Fin n → Real | ∀ i, 0 ≤ y i} := by
  classical
  intro x hx
  set C : Set (Fin n → Real) := {y : Fin n → Real | ∀ i, 0 ≤ y i}
  have hCconv : Convex ℝ C := by
    have hC :
        C = (Set.univ : Set (Fin n)).pi (fun _ : Fin n => Set.Ici (0 : Real)) := by
      ext y
      simp [C, Set.pi]
    simpa [hC] using
      (convex_pi (s := (Set.univ : Set (Fin n))) (t := fun _ : Fin n => Set.Ici (0 : Real))
        (by intro _ _; exact convex_Ici (0 : Real)))
  -- A convenient neighborhood in which all coordinates are bounded above.
  set U : Set (Fin n → Real) := {y : Fin n → Real | ∀ i, y i < x i + 1}
  have hUopen : IsOpen U := by
    have hU : U = ⋂ i : Fin n, {y : Fin n → Real | y i < x i + 1} := by
      ext y
      simp [U]
    rw [hU]
    refine isOpen_iInter_of_finite ?_
    intro i
    simpa [Set.preimage] using (isOpen_Iio.preimage (continuous_apply i))
  have hxU : x ∈ U := by
    intro i
    linarith
  have hUnhds : U ∈ nhds x := hUopen.mem_nhds hxU
  -- Choose a large simplex inside the orthant containing `U ∩ C`.
  let M : Real := (∑ i : Fin n, (x i + 1)) + 1
  have hMpos : 0 < M := by
    have hsum_nonneg : 0 ≤ ∑ i : Fin n, (x i + 1) := by
      refine Finset.sum_nonneg ?_
      intro i hi
      have hx0 : 0 ≤ x i := by
        have : x ∈ C := by simpa [C] using hx
        exact this i
      linarith
    have : 0 < (∑ i : Fin n, (x i + 1)) + 1 := by linarith
    simpa [M] using this
  have hM0 : M ≠ 0 := ne_of_gt hMpos
  let b : Fin (n + 1) → Fin n → Real := Fin.cases 0 (fun i : Fin n => Pi.single i M)
  let P : Set (Fin n → Real) := convexHull Real (Set.range b)
  have hbC : Set.range b ⊆ C := by
    rintro y ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero =>
        intro j
        simp [b]
    | succ i =>
        intro j
        by_cases hji : j = i
        · subst j
          have : 0 ≤ M := le_of_lt hMpos
          simp [b, Pi.single, this]
        · simp [b, Pi.single, hji]
  have hPsub : P ⊆ C := by
    exact convexHull_min hbC hCconv
  have hUCsubP : U ∩ C ⊆ P := by
    intro y hy
    have hyU : y ∈ U := hy.1
    have hyC : y ∈ C := hy.2
    have hy0 : ∀ i, 0 ≤ y i := hyC
    have hy_le : ∀ i, y i ≤ x i + 1 := fun i => le_of_lt (hyU i)
    have hsum_le :
        (∑ i : Fin n, y i) ≤ M := by
      have hsum_le' :
          (∑ i : Fin n, y i) ≤ ∑ i : Fin n, (x i + 1) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hy_le i
      have hsum_leM : (∑ i : Fin n, (x i + 1)) ≤ M := by
        dsimp [M]
        linarith
      exact le_trans hsum_le' hsum_leM
    simpa [P, b] using
      (Section10.mem_convexHull_zero_piSingle_of_nonneg_sum_le (n := n) (M := M) hMpos
        (y := y) hy0 hsum_le)
  refine ⟨({P} : Set (Set (Fin n → Real))), U, Set.finite_singleton P, hUnhds, ?_, ?_⟩
  · intro Q hQ
    have hQ' : Q = P := by simpa using hQ
    subst hQ'
    refine ⟨n, ?_, hPsub⟩
    simpa [P, b] using (Section10.isSimplex_convexHull_zero_piSingle (n := n) (M := M) hM0)
  · -- `U ∩ P = U ∩ C` since `U ∩ C ⊆ P ⊆ C`.
    have hUPsub : U ∩ P ⊆ U ∩ C := by
      intro y hy
      exact ⟨hy.1, hPsub hy.2⟩
    have hUCsub : U ∩ C ⊆ U ∩ P := by
      intro y hy
      exact ⟨hy.1, hUCsubP hy⟩
    have hEq : U ∩ P = U ∩ C := Set.Subset.antisymm hUPsub hUCsub
    simp [hEq]

/-- Theorem 10.3.1. Let `C ⊆ ℝ^n` be the nonnegative orthant,
`C = {x = (ξ₁, …, ξₙ) | ξⱼ ≥ 0, j = 1, …, n}`. Assume `f` is a finite convex function on the
positive orthant `int C` and is non-decreasing in each coordinate.

Then `f` is bounded above on every bounded subset of the positive orthant, and hence `f` admits a
unique extension to a finite continuous convex function on the whole nonnegative orthant `C`. -/
theorem convexOn_bddAbove_and_exists_unique_extension_nonnegOrthant_of_monotoneOn {n : ℕ}
    (f : (Fin n → Real) → Real)
    (hfconv : ConvexOn ℝ {x : Fin n → Real | ∀ i, 0 < x i} f)
    (hfmono : MonotoneOn f {x : Fin n → Real | ∀ i, 0 < x i}) :
    (∀ s,
        s ⊆ {x : Fin n → Real | ∀ i, 0 < x i} →
          Bornology.IsBounded s → BddAbove (f '' s)) ∧
      (∃ g : (Fin n → Real) → Real,
          (ConvexOn ℝ {x : Fin n → Real | ∀ i, 0 ≤ x i} g ∧
              ContinuousOn g {x : Fin n → Real | ∀ i, 0 ≤ x i} ∧
            (∀ x ∈ {x : Fin n → Real | ∀ i, 0 < x i}, g x = f x)) ∧
            ∀ g' : (Fin n → Real) → Real,
              (ConvexOn ℝ {x : Fin n → Real | ∀ i, 0 ≤ x i} g' ∧
                  ContinuousOn g' {x : Fin n → Real | ∀ i, 0 ≤ x i} ∧
                (∀ x ∈ {x : Fin n → Real | ∀ i, 0 < x i}, g' x = f x)) →
                ∀ x ∈ {x : Fin n → Real | ∀ i, 0 ≤ x i}, g' x = g x) := by
  classical
  -- Part (1): boundedness above on bounded subsets of the positive orthant.
  have hbdd :
      ∀ s,
        s ⊆ {x : Fin n → Real | ∀ i, 0 < x i} →
          Bornology.IsBounded s → BddAbove (f '' s) := by
    intro s hs hsbdd
    exact
      Section10.bddAbove_image_of_monotoneOn_of_isBounded_posOrthant (f := f) hfmono hs hsbdd
  refine ⟨hbdd, ?_⟩
  -- Part (2): apply Theorem 10.3 to extend from the positive orthant to the nonnegative orthant.
  let C : Set (Fin n → Real) := {x : Fin n → Real | ∀ i, 0 ≤ x i}
  let pos : Set (Fin n → Real) := {x : Fin n → Real | ∀ i, 0 < x i}
  have hCconv : Convex ℝ C := by
    -- Coordinatewise `Ici` is convex, hence their product is convex.
    have hC :
        C = (Set.univ : Set (Fin n)).pi (fun _ : Fin n => Set.Ici (0 : Real)) := by
      ext x
      simp [C, Set.pi]
    simpa [hC] using
      (convex_pi (s := (Set.univ : Set (Fin n))) (t := fun _ : Fin n => Set.Ici (0 : Real))
        (by intro _ _; exact convex_Ici (0 : Real)))
  have hCloc : Set.LocallySimplicial n C := by
    simpa [C] using (Section10.locallySimplicial_nonnegOrthant (n := n))
  -- Work on the `EuclideanSpace` preimage needed by Theorem 10.3.
  set CE : Set (EuclideanSpace Real (Fin n)) :=
    (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹' C
  have hriCE :
      euclideanRelativeInterior n CE =
        {x : EuclideanSpace Real (Fin n) | ∀ i, 0 < (x : Fin n → Real) i} := by
    simpa [C, CE] using (Section10.euclideanRelativeInterior_preimage_nonnegOrthant (n := n))
  let fE : EuclideanSpace Real (Fin n) → Real := fun x => f (x : Fin n → Real)
  -- Transport convexity from `pos` to `euclideanRelativeInterior n CE`.
  let e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)
  let A : EuclideanSpace Real (Fin n) →ₗ[Real] (Fin n → Real) := e.toLinearMap
  have hpre_pos :
      {x : EuclideanSpace Real (Fin n) | ∀ i, 0 < (x : Fin n → Real) i} = A ⁻¹' pos := by
    ext x
    simp [pos, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
  have hfconvE :
      ConvexOn ℝ (euclideanRelativeInterior n CE) fE := by
    have hfconvA :
        ConvexOn ℝ (A ⁻¹' pos) (fun x : EuclideanSpace Real (Fin n) => f (A x)) :=
      (ConvexOn.comp_linearMap (hf := hfconv) A)
    simpa [fE, hriCE, hpre_pos, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
      hfconvA
  -- Boundedness above for `fE` on bounded subsets of `euclideanRelativeInterior n CE`.
  have hf_bddAboveE :
      ∀ s,
        s ⊆ euclideanRelativeInterior n CE →
          Bornology.IsBounded s → BddAbove (fE '' s) := by
    intro s hsri hsbdd
    have hspos :
        (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' s ⊆ pos := by
      rintro y ⟨x, hx, rfl⟩
      have hx' : x ∈ {x : EuclideanSpace Real (Fin n) | ∀ i, 0 < (x : Fin n → Real) i} := by
        have : x ∈ euclideanRelativeInterior n CE := hsri hx
        simpa [hriCE] using this
      simpa [pos] using hx'
    have hsbdd' :
        Bornology.IsBounded
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' s) := by
      -- Control the image by combining a closed-ball bound on `s` with the operator norm of `e`.
      rcases hsbdd.subset_closedBall (0 : EuclideanSpace Real (Fin n)) with ⟨R, hR⟩
      have hEq :
          (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) =
            fun x => e x := by
        funext x
        simp [e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
      refine
        (Metric.isBounded_iff_subset_closedBall (s :=
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' s))
          (c := (0 : Fin n → Real))).2 ?_
      refine ⟨‖e.toContinuousLinearMap‖ * R, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have hxball : x ∈ Metric.closedBall (0 : EuclideanSpace Real (Fin n)) R := hR hx
      have hxnorm : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
      have hmap : ‖e x‖ ≤ ‖e.toContinuousLinearMap‖ * ‖x‖ := by
        simpa using (e.toContinuousLinearMap.le_opNorm x)
      have hmapR : ‖e x‖ ≤ ‖e.toContinuousLinearMap‖ * R :=
        le_trans hmap (mul_le_mul_of_nonneg_left hxnorm (norm_nonneg _))
      simpa [Metric.mem_closedBall, dist_eq_norm, hEq] using hmapR
    have : BddAbove (f '' ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) '' s)) :=
      hbdd _ hspos hsbdd'
    simpa [fE, Set.image_image] using this
  -- Apply Theorem 10.3 on the nonnegative orthant `C`.
  rcases
      convexOn_exists_unique_continuousExtension_of_locallySimplicial
        (n := n) (C := C) (hCconv := hCconv) (hCloc := hCloc) (f := fE) hfconvE hf_bddAboveE with
    ⟨gE, ⟨hgEconv, hgEcont, hgEeq⟩, hgEuniq⟩
  -- Pull back the `EuclideanSpace` extension to `(Fin n → Real)` using the linear equivalence.
  let g : (Fin n → Real) → Real := fun x => gE (e.symm x)
  refine ⟨g, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · -- Convexity of `g` on `C`.
      have hCE : CE = A ⁻¹' C := by
        ext x
        simp [CE, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
      have hpreC : e.symm.toLinearMap ⁻¹' CE = C := by
        ext x
        simp [hCE, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
      have hg_conv' : ConvexOn ℝ (e.symm.toLinearMap ⁻¹' CE) (gE ∘ e.symm.toLinearMap) :=
        (ConvexOn.comp_linearMap (hf := hgEconv) e.symm.toLinearMap)
      simpa [g, Function.comp, hpreC] using hg_conv'
    · -- Continuity of `g` on `C`.
      have hCE : CE = A ⁻¹' C := by
        ext x
        simp [CE, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
      have hgEcont' : ContinuousOn gE CE := by
        simpa [Function.ContinuousRelativeTo] using hgEcont
      have hmaps : Set.MapsTo e.symm C CE := by
        intro x hx
        have : e.symm x ∈ A ⁻¹' C := by
          simpa [A] using hx
        simpa [hCE] using this
      have hcomp :
          ContinuousOn (fun x : Fin n → Real => gE (e.symm x)) C :=
        hgEcont'.comp e.symm.continuous.continuousOn hmaps
      simpa [g] using hcomp
    · -- Agreement with `f` on the positive orthant.
      intro x hx
      have hxE : e.symm x ∈ euclideanRelativeInterior n CE := by
        have : e.symm x ∈ {x : EuclideanSpace Real (Fin n) | ∀ i, 0 < (x : Fin n → Real) i} := by
          intro i
          simpa [e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using (hx i)
        simpa [hriCE] using this
      have := hgEeq (e.symm x) hxE
      simpa [g, fE, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using this
  · -- Uniqueness of the pulled-back extension.
    intro g' hg'
    -- Push `g'` forward to `EuclideanSpace` and use uniqueness there.
    let gE' : EuclideanSpace Real (Fin n) → Real := fun x => g' (e x)
    have hCE : CE = A ⁻¹' C := by
      ext x
      simp [CE, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
    have hgE'conv : ConvexOn ℝ CE gE' := by
      have : ConvexOn ℝ (A ⁻¹' C) (fun x : EuclideanSpace Real (Fin n) => g' (A x)) :=
        (ConvexOn.comp_linearMap (hf := hg'.1) A)
      simpa [gE', hCE, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using this
    have hgE'cont : Function.ContinuousRelativeTo gE' CE := by
      have hg'cont : ContinuousOn g' C := hg'.2.1
      have hmaps : Set.MapsTo e CE C := by
        intro x hx
        have hxC : A x ∈ C := by
          simpa [hCE, A] using hx
        simpa [A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hxC
      have hcomp : ContinuousOn (fun x : EuclideanSpace Real (Fin n) => g' (e x)) CE :=
        hg'cont.comp e.continuous.continuousOn hmaps
      simpa [Function.ContinuousRelativeTo, gE'] using hcomp
    have hgE'eq : ∀ x ∈ euclideanRelativeInterior n CE, gE' x = fE x := by
      intro x hxri
      have hxpos : e x ∈ pos := by
        have hx' : x ∈ {x : EuclideanSpace Real (Fin n) | ∀ i, 0 < (x : Fin n → Real) i} := by
          simpa [hriCE] using hxri
        intro i
        simpa [e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using hx' i
      have : g' (e x) = f (e x) := hg'.2.2 (e x) (by simpa [pos] using hxpos)
      simpa [gE', fE, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using this
    have hgE'eq' :
        ∀ x ∈ euclideanRelativeInterior n CE, gE' x = fE x := hgE'eq
    have hEqOn : ∀ x ∈ CE, gE' x = gE x := by
      intro x hxCE
      have :=
        hgEuniq gE' ⟨hgE'conv, hgE'cont, hgE'eq'⟩ x hxCE
      simpa using this
    intro x hxC
    have hxCE : e.symm x ∈ CE := by
      have : e.symm x ∈ A ⁻¹' C := by
        simpa [A] using hxC
      simpa [hCE] using this
    have := hEqOn (e.symm x) hxCE
    simpa [g, gE', e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using this

/-- Definition 10.3.2. Let `S ⊆ ℝ^n`. A real-valued function `f` defined on `S` is called
Lipschitzian relative to `S` if there exists a real number `α ≥ 0` such that
`|f(y) - f(x)| ≤ α |y - x|` for all `x ∈ S` and `y ∈ S`. -/
def Function.LipschitzRelativeTo {n : ℕ} (f : EuclideanSpace Real (Fin n) → Real)
    (S : Set (EuclideanSpace Real (Fin n))) : Prop :=
  ∃ K : NNReal, LipschitzOnWith K f S

/-- A function that is Lipschitz on a set is uniformly continuous on that set. -/
lemma Function.LipschitzRelativeTo.uniformContinuousOn {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real} {S : Set (EuclideanSpace Real (Fin n))}
    (hf : Function.LipschitzRelativeTo f S) :
    UniformContinuousOn f S := by
  rcases hf with ⟨K, hK⟩
  exact hK.uniformContinuousOn

/-- Theorem 10.3.3. Let `S ⊆ ℝ^n`.
If a real-valued function `f` is Lipschitzian relative to `S`, then `f` is uniformly continuous
relative to `S`. -/
theorem Function.uniformContinuousOn_of_lipschitzRelativeTo {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real} {S : Set (EuclideanSpace Real (Fin n))}
    (hf : Function.LipschitzRelativeTo f S) :
    UniformContinuousOn f S := by
  exact hf.uniformContinuousOn

/-- A compact set included in the relative interior admits a uniform radius whose translated
scaled unit ball (intersected with the affine span) stays in the relative interior. -/
lemma Section10.exists_pos_eps_uniform_ball_subset_ri {n : ℕ}
    {C S : Set (EuclideanSpace Real (Fin n))} (hS : IsCompact S)
    (hSsubset : S ⊆ euclideanRelativeInterior n C) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ S,
        ((fun u => x + u) '' (ε • euclideanUnitBall n)) ∩
            (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) ⊆
          euclideanRelativeInterior n C := by
  classical
  by_cases hSem : S = ∅
  · subst hSem
    refine ⟨1, by norm_num, ?_⟩
    intro x hx
    simp at hx
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.2 hSem
    let ι : Type := {x // x ∈ S}
    have hεx :
        ∀ x : ι,
          ∃ ε : ℝ,
            0 < ε ∧
              ((fun u => x.1 + u) '' (ε • euclideanUnitBall n)) ∩
                  (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) ⊆
                euclideanRelativeInterior n C := fun x =>
          euclideanRelativeInterior_ball_subset n C (x := x.1) (hSsubset x.2)
    classical
    choose ε hεpos hεsub using hεx
    -- Cover `S` by metric balls `ball x (ε x / 2)` and take a finite subcover.
    have hcover : S ⊆ ⋃ x : ι, Metric.ball x.1 (ε x / 2) := by
      intro y hyS
      refine Set.mem_iUnion.2 ?_
      refine ⟨⟨y, hyS⟩, ?_⟩
      have : (0 : ℝ) < ε ⟨y, hyS⟩ / 2 := by exact half_pos (hεpos ⟨y, hyS⟩)
      simpa [Metric.mem_ball, dist_self] using this
    obtain ⟨t, htcover⟩ :=
      hS.elim_finite_subcover (fun x : ι => Metric.ball x.1 (ε x / 2)) (fun _ => Metric.isOpen_ball)
        hcover
    have htne : t.Nonempty := by
      rcases hSne with ⟨x0, hx0S⟩
      rcases Set.mem_iUnion₂.1 (htcover hx0S) with ⟨i, hiT, hiBall⟩
      exact ⟨i, hiT⟩
    let fδ : ι → ℝ := fun x => ε x / 2
    let sδ : Finset ℝ := t.image fδ
    have hsδne : sδ.Nonempty := htne.image fδ
    let δ : ℝ := sδ.min' hsδne
    have hδpos : 0 < δ := by
      have hmem : δ ∈ sδ := by
        simpa [δ] using (Finset.min'_mem sδ hsδne)
      rcases (Finset.mem_image.1 hmem) with ⟨i, hiT, hiEq⟩
      have : 0 < fδ i := half_pos (hεpos i)
      simpa [hiEq] using this
    refine ⟨δ, hδpos, ?_⟩
    intro x hxS
    -- Choose a center `i ∈ t` such that `x ∈ ball i (ε i / 2)`.
    rcases Set.mem_iUnion₂.1 (htcover hxS) with ⟨i, hiT, hxi⟩
    have hxnorm : ‖x - i.1‖ ≤ ε i / 2 := by
      have : dist x i.1 < ε i / 2 := by
        simpa [Metric.mem_ball] using hxi
      -- convert `dist` to `norm`
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm] using (le_of_lt this)
    have hδle : δ ≤ ε i / 2 := by
      have hleast : IsLeast (sδ : Set ℝ) δ := by
        simpa [δ] using (Finset.isLeast_min' sδ hsδne)
      have hi_mem : fδ i ∈ sδ := Finset.mem_image_of_mem fδ hiT
      have hi_mem' : fδ i ∈ (sδ : Set ℝ) := by simpa using hi_mem
      exact hleast.2 hi_mem'
    intro y hy
    rcases hy with ⟨hy_ball, hy_aff⟩
    rcases hy_ball with ⟨u, hu, rfl⟩
    have hu_norm : ‖u‖ ≤ δ := by
      exact
        norm_le_of_mem_smul_unitBall (n := n) (ε := δ) (le_of_lt hδpos) (v := u) hu
    have hsum : ‖(x - i.1) + u‖ ≤ ε i := by
      have hu_le : ‖u‖ ≤ ε i / 2 := le_trans hu_norm hδle
      calc
        ‖(x - i.1) + u‖ ≤ ‖x - i.1‖ + ‖u‖ := norm_add_le _ _
        _ ≤ ε i / 2 + ε i / 2 := add_le_add hxnorm hu_le
        _ = ε i := by ring
    have huv : (x - i.1) + u ∈ ε i • euclideanUnitBall n :=
      mem_smul_unitBall_of_norm_le (n := n) (ε := ε i) (hεpos i) hsum
    have hy_ball' :
        x + u ∈ (fun t => i.1 + t) '' (ε i • euclideanUnitBall n) := by
      refine ⟨(x - i.1) + u, huv, ?_⟩
      -- `i + ((x - i) + u) = x + u`
      abel_nf
    have hy' :
        x + u ∈
          ((fun t => i.1 + t) '' (ε i • euclideanUnitBall n)) ∩
            (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) :=
      ⟨hy_ball', by simpa using hy_aff⟩
    -- Apply the relative interior ball containment at `i`.
    exact hεsub i hy'


end Section10
end Chap02
