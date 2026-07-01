/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Guangxuan Pan, Siyuan Shao, Zaiwen Wen
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section10_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section08_part5

noncomputable section

section Chap02
section Section10

open scoped BigOperators Pointwise

/-- Theorem 10.4. Let `f` be a proper convex function, and let `S` be any closed bounded subset
of `ri (dom f)`. Then `f` is Lipschitzian relative to `S`. -/
theorem properConvexFunctionOn_lipschitzRelativeTo_of_isClosed_isBounded_subset_ri_effectiveDomain
    {n : ℕ} {f : (Fin n → Real) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {S : Set (EuclideanSpace Real (Fin n))} (hSclosed : IsClosed S)
    (hSbdd : Bornology.IsBounded S)
    (hSsubset :
      S ⊆
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    Function.LipschitzRelativeTo
        (fun x : EuclideanSpace Real (Fin n) => EReal.toReal (f (x : Fin n → Real))) S := by
  classical
  by_cases hSem : S = ∅
  · subst hSem
    refine ⟨0, ?_⟩
    exact (lipschitzOnWith_empty (K := (0 : NNReal))
      (f := fun x : EuclideanSpace Real (Fin n) => EReal.toReal (f (x : Fin n → Real))))
  · have hScomp : IsCompact S := by
      rcases hSbdd.subset_closedBall (0 : EuclideanSpace Real (Fin n)) with ⟨R, hR⟩
      exact (isCompact_closedBall (0 : EuclideanSpace Real (Fin n)) R).of_isClosed_subset hSclosed hR
    have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.2 hSem
    -- Set up the Euclidean effective domain and its relative interior.
    set CE : Set (EuclideanSpace Real (Fin n)) :=
      (fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin n → Real)) f
    set riCE : Set (EuclideanSpace Real (Fin n)) := euclideanRelativeInterior n CE
    have hSsubset' : S ⊆ riCE := by simpa [riCE, CE] using hSsubset
    -- Choose a uniform thickening radius inside `riCE`.
    obtain ⟨ε, hεpos, hεball⟩ :=
      Section10.exists_pos_eps_uniform_ball_subset_ri (n := n) (C := CE) (S := S) hScomp hSsubset'
    -- The thickened compact set where we will bound `f`.
    set K : Set (EuclideanSpace Real (Fin n)) :=
      ((fun p : EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin n) => p.1 + p.2) '' (S ×ˢ
          (ε • euclideanUnitBall n))) ∩
        (affineSpan Real CE : Set (EuclideanSpace Real (Fin n)))
    have hKcomp : IsCompact K := by
      have hball_eq : ε • euclideanUnitBall n = Metric.closedBall (0 : EuclideanSpace Real (Fin n)) ε := by
        ext v
        constructor
        · intro hv
          have hv' : ‖v‖ ≤ ε :=
            norm_le_of_mem_smul_unitBall (n := n) (ε := ε) (le_of_lt hεpos) hv
          simpa [Metric.mem_closedBall, dist_eq_norm] using hv'
        · intro hv
          have hv' : ‖v‖ ≤ ε := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hv
          exact mem_smul_unitBall_of_norm_le (n := n) (ε := ε) hεpos hv'
      have hcomp_ball : IsCompact (ε • euclideanUnitBall n) := by
        simpa [hball_eq] using
          (isCompact_closedBall (0 : EuclideanSpace Real (Fin n)) ε)
      have hcomp_add :
          IsCompact
            ((fun p : EuclideanSpace Real (Fin n) × EuclideanSpace Real (Fin n) => p.1 + p.2) '' (S ×ˢ
                (ε • euclideanUnitBall n))) :=
        (hScomp.prod hcomp_ball).image (by
          simpa using (continuous_fst.add continuous_snd))
      have haff_closed :
          IsClosed (affineSpan Real CE : Set (EuclideanSpace Real (Fin n))) := by
        simpa using
          (AffineSubspace.closed_of_finiteDimensional (s := affineSpan Real CE))
      simpa [K] using hcomp_add.inter_right haff_closed
    have hKsubset_ri : K ⊆ riCE := by
      intro y hyK
      rcases hyK with ⟨hy_add, hy_aff⟩
      rcases hy_add with ⟨p, hp, rfl⟩
      rcases hp with ⟨hxS, hvBall⟩
      have hy_mem :
          (p.1 + p.2) ∈
            ((fun u => p.1 + u) '' (ε • euclideanUnitBall n)) ∩
              (affineSpan Real CE : Set (EuclideanSpace Real (Fin n))) :=
        ⟨⟨p.2, hvBall, by simp⟩, by simpa using hy_aff⟩
      exact hεball p.1 hxS hy_mem
    have hSK : S ⊆ K := by
      intro x hxS
      rcases hSsubset' hxS with ⟨hx_aff, _, _, _⟩
      have hzero : (0 : EuclideanSpace Real (Fin n)) ∈ ε • euclideanUnitBall n := by
        refine ⟨0, ?_, by simp⟩
        simp [euclideanUnitBall]
      refine ⟨?_, hx_aff⟩
      refine ⟨(x, (0 : EuclideanSpace Real (Fin n))), ⟨hxS, hzero⟩, by simp⟩
    -- Define the real-valued function.
    let g : EuclideanSpace Real (Fin n) → Real := fun x => (f (x : Fin n → Real)).toReal
    -- Convexity of `g` on the Euclidean effective domain.
    have hg_conv : ConvexOn ℝ CE g := by
      let e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
        EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)
      let A : EuclideanSpace Real (Fin n) →ₗ[Real] (Fin n → Real) := e.toLinearMap
      have hCE' : CE = A ⁻¹' effectiveDomain (Set.univ : Set (Fin n → Real)) f := by
        ext x
        simp [CE, A, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv]
      have hconv_toReal :
          ConvexOn ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f) (fun x => (f x).toReal) :=
        convexOn_toReal_on_effectiveDomain (f := f) hf
      have hconv_pre :
          ConvexOn ℝ (A ⁻¹' effectiveDomain (Set.univ : Set (Fin n → Real)) f)
            ((fun x => (f x).toReal) ∘ A) :=
        (ConvexOn.comp_linearMap (hf := hconv_toReal) A)
      simpa [g, hCE', A, Function.comp, e, EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv] using
        hconv_pre
    -- Continuity of `g` on `riCE`, hence on `K`, so it attains bounds on `K`.
    have hg_cont_ri : ContinuousOn g riCE := by
      have hconv_toReal :
          ConvexOn ℝ (effectiveDomain (Set.univ : Set (Fin n → Real)) f) (fun x => (f x).toReal) :=
        convexOn_toReal_on_effectiveDomain (f := f) hf
      simpa [g, riCE, CE] using continuousOn_toReal_on_ri_effectiveDomain (f := f) hconv_toReal
    have hg_cont_K : ContinuousOn g K := hg_cont_ri.mono hKsubset_ri
    have hKne : K.Nonempty := by
      rcases hSne with ⟨x, hxS⟩
      exact ⟨x, hSK hxS⟩
    obtain ⟨xmin, hxminK, hxmin⟩ := hKcomp.exists_isMinOn hKne hg_cont_K
    obtain ⟨xmax, hxmaxK, hxmax⟩ := hKcomp.exists_isMaxOn hKne hg_cont_K
    have hxmin' : ∀ x ∈ K, g xmin ≤ g x := by
      simpa [IsMinOn, IsMinFilter] using hxmin
    have hxmax' : ∀ x ∈ K, g x ≤ g xmax := by
      simpa [IsMaxOn, IsMaxFilter] using hxmax
    set m : Real := g xmin
    set M : Real := g xmax
    have hm_le : ∀ x ∈ K, m ≤ g x := by
      intro x hxK
      simpa [m] using hxmin' x hxK
    have hle_M : ∀ x ∈ K, g x ≤ M := by
      intro x hxK
      simpa [M] using hxmax' x hxK
    have hmM : m ≤ M := by
      have := hxmin' xmax hxmaxK
      simpa [m, M] using this
    set L : Real := (M - m) / ε
    have oneside {x y : EuclideanSpace Real (Fin n)} (hx : x ∈ S) (hy : y ∈ S) :
        g y - g x ≤ L * ‖y - x‖ := by
      obtain rfl | hxy := eq_or_ne x y
      · simp
      have hxypos : 0 < ‖y - x‖ := by
        exact (norm_pos_iff).2 (sub_ne_zero.2 hxy.symm)
      have hrne : ‖y - x‖ ≠ 0 := ne_of_gt hxypos
      -- Construct the auxiliary point `z`.
      set z : EuclideanSpace Real (Fin n) :=
        y + (ε / ‖y - x‖) • (y - x)
      have hz_ball :
          (ε / ‖y - x‖) • (y - x) ∈ ε • euclideanUnitBall n := by
        have hnorm :
            ‖(ε / ‖y - x‖) • (y - x)‖ ≤ ε := by
          have hscalar :
              ‖(ε / ‖y - x‖ : ℝ)‖ = ε / ‖y - x‖ :=
            Real.norm_of_nonneg (le_of_lt (div_pos hεpos hxypos))
          have : ‖(ε / ‖y - x‖) • (y - x)‖ = ε := by
            calc
              ‖(ε / ‖y - x‖) • (y - x)‖ =
                  ‖(ε / ‖y - x‖ : ℝ)‖ * ‖y - x‖ := by
                    simpa using (norm_smul (ε / ‖y - x‖) (y - x))
              _ = (ε / ‖y - x‖) * ‖y - x‖ := by simp [hscalar]
              _ = ε := by field_simp [hrne]
          simp [this]
        exact mem_smul_unitBall_of_norm_le (n := n) (ε := ε) hεpos hnorm
      have hxK : x ∈ K := hSK hx
      have hyK : y ∈ K := hSK hy
      have hx_aff : x ∈ (affineSpan Real CE : Set (EuclideanSpace Real (Fin n))) := hxK.2
      have hy_aff : y ∈ (affineSpan Real CE : Set (EuclideanSpace Real (Fin n))) := hyK.2
      have hz_aff : z ∈ (affineSpan Real CE : Set (EuclideanSpace Real (Fin n))) := by
        -- `z` is obtained by translating `y` by a vector in the direction of `affineSpan Real CE`.
        have hdir_vsub :
            (y -ᵥ x : EuclideanSpace Real (Fin n)) ∈ (affineSpan Real CE).direction :=
          AffineSubspace.vsub_mem_direction hy_aff hx_aff
        have hdir_sub :
            (y - x : EuclideanSpace Real (Fin n)) ∈ (affineSpan Real CE).direction := by
          simpa [vsub_eq_sub] using hdir_vsub
        have hdir :
            (ε / ‖y - x‖) • (y - x) ∈ (affineSpan Real CE).direction :=
          (affineSpan Real CE).direction.smul_mem (ε / ‖y - x‖) hdir_sub
        have :
            (ε / ‖y - x‖) • (y - x) +ᵥ y ∈ affineSpan Real CE :=
          AffineSubspace.vadd_mem_of_mem_direction hdir hy_aff
        simpa [z, vadd_eq_add, add_comm, add_left_comm, add_assoc] using this
      have hzK : z ∈ K := by
        refine ⟨?_, hz_aff⟩
        refine ⟨(y, (ε / ‖y - x‖) • (y - x)), ?_, by simp [z]⟩
        exact ⟨hy, hz_ball⟩
      have hxCE : x ∈ CE := (euclideanRelativeInterior_subset_closure n CE).1 (hKsubset_ri hxK)
      have hzCE : z ∈ CE := (euclideanRelativeInterior_subset_closure n CE).1 (hKsubset_ri hzK)
      -- Express `y` as a convex combination of `x` and `z`.
      let r : Real := ‖y - x‖
      let lam : Real := r / (ε + r)
      have hr : r = ‖y - x‖ := rfl
      have hlam0 : 0 ≤ lam := by
        have hr0 : 0 ≤ r := by simp [hr]
        have hden : 0 < ε + r := by linarith [hεpos, hr0]
        exact div_nonneg hr0 (le_of_lt hden)
      have hlamle1 : lam ≤ 1 := by
        have hr0 : 0 ≤ r := by simp [hr]
        have hden : 0 < ε + r := by linarith [hεpos, hr0]
        have : r ≤ ε + r := by linarith [hεpos, hr0]
        simpa [lam] using (div_le_one hden).2 this
      have h1lam0 : 0 ≤ 1 - lam := sub_nonneg.2 hlamle1
      have hab : (1 - lam) + lam = (1 : Real) := by ring
      have hy_eq : (1 - lam) • x + lam • z = y := by
        have hden : ε + r ≠ 0 := by
          have hr0 : 0 ≤ r := by simp [hr]
          linarith [hεpos, hr0]
        let a : Real := ε / (ε + r)
        have h1lam : 1 - lam = a := by
          -- `1 - r/(ε+r) = ε/(ε+r)`
          have : 1 - r / (ε + r) = ε / (ε + r) := by
            field_simp [hden]
            ring
          simpa [lam, a] using this
        have hlamε : lam * (ε / r) = a := by
          have hrne' : r ≠ 0 := by simpa [hr] using hrne
          have : (r / (ε + r)) * (ε / r) = ε / (ε + r) := by
            field_simp [hden, hrne']
          simpa [lam, a, mul_assoc, mul_left_comm, mul_comm] using this
        have halam : a + lam = (1 : Real) := by
          have : ε / (ε + r) + r / (ε + r) = (1 : Real) := by
            field_simp [hden]
          simpa [lam, a, add_comm, add_left_comm, add_assoc] using this
        calc
          (1 - lam) • x + lam • z
              = a • x + lam • y + (lam * (ε / r)) • (y - x) := by
                  simp [z, r, lam, a, h1lam, smul_add, smul_smul, add_assoc]
          _ = a • x + lam • y + a • (y - x) := by simp [hlamε]
          _ = a • y + lam • y := by
                -- `a•x + a•(y-x) = a•y`
                have hax : a • x + a • (y - x) = a • y := by
                  have hxy : x + (y - x) = y := add_sub_cancel x y
                  calc
                    a • x + a • (y - x) = a • (x + (y - x)) := (smul_add a x (y - x)).symm
                    _ = a • y := by simp [hxy]
                calc
                  a • x + lam • y + a • (y - x) = lam • y + (a • x + a • (y - x)) := by abel
                  _ = lam • y + a • y := by simp [hax]
                  _ = a • y + lam • y := by abel
          _ = (a + lam) • y := by
                exact (add_smul a lam y).symm
          _ = y := by simp [halam]
      -- Apply convexity at `x` and `z`.
      have hconv :=
        hg_conv.2 hxCE hzCE h1lam0 hlam0 hab
      have hconv' : g y ≤ (1 - lam) • g x + lam • g z := by
        simpa [hy_eq] using hconv
      have hdiff₁ : g y - g x ≤ lam * (g z - g x) := by
        have hconv'' : g y ≤ (1 - lam) * g x + lam * g z := by
          simpa [smul_eq_mul] using hconv'
        have hsub := sub_le_sub_right hconv'' (g x)
        have hrhs : ((1 - lam) * g x + lam * g z) - g x = lam * (g z - g x) := by ring
        simpa [hrhs] using hsub
      have hgz_le : g z ≤ M := hle_M z hzK
      have hmx_le : m ≤ g x := hm_le x hxK
      have hdiff₂ : g z - g x ≤ M - m := by linarith [hgz_le, hmx_le]
      have hdiff₃ : lam * (g z - g x) ≤ lam * (M - m) :=
        mul_le_mul_of_nonneg_left hdiff₂ hlam0
      have hlamle : lam ≤ r / ε := by
        have hr0 : 0 ≤ r := by simp [hr]
        have hεle : ε ≤ ε + r := le_add_of_nonneg_right hr0
        have : r / (ε + r) ≤ r / ε :=
          div_le_div_of_nonneg_left hr0 hεpos hεle
        simpa [lam] using this
      have hMm0 : 0 ≤ M - m := sub_nonneg.2 hmM
      have hmul : lam * (M - m) ≤ (r / ε) * (M - m) :=
        mul_le_mul_of_nonneg_right hlamle hMm0
      have hmain : g y - g x ≤ (r / ε) * (M - m) :=
        le_trans (le_trans hdiff₁ hdiff₃) hmul
      have hrε : (r / ε) * (M - m) = L * ‖y - x‖ := by
        simp [L, hr, div_eq_mul_inv, mul_assoc, mul_comm]
      exact hmain.trans_eq hrε
    refine ⟨Real.toNNReal L, ?_⟩
    refine LipschitzOnWith.of_dist_le' (fun x hx y hy => ?_)
    have hxy : g x - g y ≤ L * ‖x - y‖ := by
      simpa [norm_sub_rev] using (oneside hy hx)
    have hyx : g y - g x ≤ L * ‖x - y‖ := by
      simpa [norm_sub_rev] using (oneside hx hy)
    simp [dist_eq_norm_sub, Real.norm_eq_abs]
    exact (abs_sub_le_iff.2 ⟨hxy, hyx⟩)

/-- `WithLp.toLp` is a two-sided coercion between `Fin n → ℝ` and the Euclidean space
`ℝ^n = EuclideanSpace ℝ (Fin n)`; converting to a function and back gives the same point. -/
lemma Section10.toLp_coeFn_eq {n : ℕ} (x : EuclideanSpace Real (Fin n)) :
    WithLp.toLp (p := 2) (x : Fin n → Real) = x := by
  simp

/-- A Lipschitz function on a set remains Lipschitz when restricting to a subset. -/
lemma Function.LipschitzRelativeTo.mono {n : ℕ} {f : EuclideanSpace Real (Fin n) → Real}
    {S T : Set (EuclideanSpace Real (Fin n))}
    (hT : Function.LipschitzRelativeTo f T) (hST : S ⊆ T) :
    Function.LipschitzRelativeTo f S := by
  rcases hT with ⟨K, hK⟩
  exact ⟨K, hK.mono hST⟩

/-- The relative interior of the whole Euclidean space is the whole space. -/
lemma Section10.euclideanRelativeInterior_univ (n : ℕ) :
    euclideanRelativeInterior n (Set.univ : Set (EuclideanSpace Real (Fin n))) = Set.univ := by
  simpa using
    (euclideanRelativeInterior_affineSubspace_eq n
      (⊤ : AffineSubspace Real (EuclideanSpace Real (Fin n))))

/-- A finite convex function on `ℝ^n` yields a proper convex `EReal`-valued function on `univ`
by coercing to `EReal` (after viewing `Fin n → ℝ` as `ℝ^n` via `WithLp.toLp`). -/
lemma Section10.properConvexFunctionOn_univ_coe_comp_toLp_of_convexOn {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hf : ConvexOn ℝ (Set.univ : Set (EuclideanSpace Real (Fin n))) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
      (fun x : Fin n → Real => (f (WithLp.toLp (p := 2) x) : EReal)) := by
  classical
  let F : (Fin n → Real) → EReal := fun x => (f (WithLp.toLp (p := 2) x) : EReal)
  have hF_ne_bot : ∀ x ∈ (Set.univ : Set (Fin n → Real)), F x ≠ (⊥ : EReal) := by
    intro x hx
    simp [F]
  have hF_conv : ConvexFunctionOn (Set.univ : Set (Fin n → Real)) F := by
    refine
      (convexFunctionOn_iff_segment_inequality (n := n) (C := (Set.univ : Set (Fin n → Real)))
            (f := F) (hC := convex_univ) (hnotbot := hF_ne_bot)).2 ?_
    intro x hx y hy t ht0 ht1
    have hreal :
        f (WithLp.toLp (p := 2) ((1 - t) • x + t • y)) ≤
          (1 - t) • f (WithLp.toLp (p := 2) x) + t • f (WithLp.toLp (p := 2) y) := by
      have hineq := hf.2
      have h :=
        hineq (x := WithLp.toLp (p := 2) x) (by trivial) (y := WithLp.toLp (p := 2) y)
          (by trivial) (a := 1 - t) (b := t) (by linarith) (by linarith) (by ring)
      simpa using h
    have hreal' :
        f (WithLp.toLp (p := 2) ((1 - t) • x + t • y)) ≤
          (1 - t) * f (WithLp.toLp (p := 2) x) + t * f (WithLp.toLp (p := 2) y) := by
      simpa [smul_eq_mul, add_assoc, add_left_comm, add_comm] using hreal
    have hE :
        (f (WithLp.toLp (p := 2) ((1 - t) • x + t • y)) : EReal) ≤
          (((1 - t) * f (WithLp.toLp (p := 2) x) + t * f (WithLp.toLp (p := 2) y) : Real) :
            EReal) := by
      exact (EReal.coe_le_coe_iff.2 hreal')
    simpa [F, EReal.coe_add, EReal.coe_mul, smul_eq_mul, add_assoc, add_left_comm, add_comm] using
      hE
  refine ⟨hF_conv, ?_⟩
  refine ⟨?_, ?_⟩
  · refine ⟨((0 : Fin n → Real), f (WithLp.toLp (p := 2) (0 : Fin n → Real))), ?_⟩
    refine (mem_epigraph_univ_iff (f := F)).2 ?_
    simp [F]
  · exact hF_ne_bot

/-- Theorem 10.4.1. Let `f : ℝ^n → ℝ` be a finite convex function.
Then `f` is uniformly continuous, and even Lipschitzian, relative to every bounded subset of
`ℝ^n`. -/
theorem convexOn_uniformContinuousOn_and_lipschitzRelativeTo_of_isBounded {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hf : ConvexOn ℝ (Set.univ : Set (EuclideanSpace Real (Fin n))) f) :
    ∀ S : Set (EuclideanSpace Real (Fin n)),
      Bornology.IsBounded S → UniformContinuousOn f S ∧ Function.LipschitzRelativeTo f S := by
  classical
  intro S hSbdd
  rcases hSbdd.subset_closedBall (0 : EuclideanSpace Real (Fin n)) with ⟨R, hSR⟩
  let T : Set (EuclideanSpace Real (Fin n)) := Metric.closedBall 0 R
  let F : (Fin n → Real) → EReal := fun x => (f (WithLp.toLp (p := 2) x) : EReal)
  have hFproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) F :=
    by
      simpa [F] using
        (Section10.properConvexFunctionOn_univ_coe_comp_toLp_of_convexOn (n := n) (f := f) hf)
  have heff : effectiveDomain (Set.univ : Set (Fin n → Real)) F = Set.univ := by
    simpa [F] using
      (effectiveDomain_univ_coe_real (n := n) (fun x : Fin n → Real => f (WithLp.toLp (p := 2) x)))
  have hTclosed : IsClosed T := by
    simpa [T] using
      (Metric.isClosed_closedBall :
        IsClosed (Metric.closedBall (0 : EuclideanSpace Real (Fin n)) R))
  have hTbdd : Bornology.IsBounded T := by
    simpa [T] using
      (Metric.isBounded_closedBall :
        Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace Real (Fin n)) R))
  have hTsubset :
      T ⊆
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) F) := by
    simp [T, heff, Section10.euclideanRelativeInterior_univ (n := n)]
  have hTLip' :
      Function.LipschitzRelativeTo
          (fun x : EuclideanSpace Real (Fin n) => EReal.toReal (F (x : Fin n → Real))) T :=
    properConvexFunctionOn_lipschitzRelativeTo_of_isClosed_isBounded_subset_ri_effectiveDomain
      (n := n) (f := F) (hf := hFproper) (S := T) (hSclosed := hTclosed) (hSbdd := hTbdd)
      (hSsubset := hTsubset)
  have hTLip : Function.LipschitzRelativeTo f T := by
    rcases hTLip' with ⟨K, hK⟩
    refine ⟨K, ?_⟩
    simpa [F, Section10.toLp_coeFn_eq] using hK
  have hSLip : Function.LipschitzRelativeTo f S :=
    Function.LipschitzRelativeTo.mono (S := S) (T := T) hTLip (by simpa [T] using hSR)
  exact ⟨hSLip.uniformContinuousOn, hSLip⟩

/-- The recession function `f₀⁺` of a real-valued function `f` on `ℝ^n`, defined by
`f₀⁺(y) = sup_x (f(x + y) - f(x))` (as an extended real). -/
noncomputable def Function.recessionFunction {n : ℕ} (f : EuclideanSpace Real (Fin n) → Real) :
    EuclideanSpace Real (Fin n) → EReal :=
  fun y =>
    sSup
      {r : EReal |
        ∃ x : EuclideanSpace Real (Fin n), r = ((f (x + y) - f x : Real) : EReal)}

/-- The recession function `f₀⁺` is finite everywhere (i.e. takes values in `ℝ`). -/
def Function.RecessionFunctionFiniteEverywhere {n : ℕ}
    (f : EuclideanSpace Real (Fin n) → Real) : Prop :=
  ∀ y, ∃ r : Real, Function.recessionFunction f y = (r : EReal)

/-- Any increment `f(x+y)-f x` is bounded above by the recession function `f₀⁺(y)`. -/
lemma Section10.recessionFunction_diff_le {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real} (x y : EuclideanSpace Real (Fin n)) :
    ((f (x + y) - f x : Real) : EReal) ≤ Function.recessionFunction f y := by
  unfold Function.recessionFunction
  refine le_sSup ?_
  exact ⟨x, rfl⟩

/-- The recession function `f₀⁺` is zero at the origin. -/
lemma Section10.recessionFunction_zero {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real} :
    Function.recessionFunction f 0 = (0 : EReal) := by
  unfold Function.recessionFunction
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    intro r hr
    rcases hr with ⟨x, rfl⟩
    simp
  · refine le_sSup ?_
    exact ⟨0, by simp⟩

/-- The recession function never takes the value `⊥`. -/
lemma Section10.recessionFunction_ne_bot {n : ℕ}
    (f : EuclideanSpace Real (Fin n) → Real) (y : EuclideanSpace Real (Fin n)) :
    Function.recessionFunction f y ≠ (⊥ : EReal) := by
  intro hbot
  have hle :
      ((f (0 + y) - f 0 : Real) : EReal) ≤ Function.recessionFunction f y :=
    Section10.recessionFunction_diff_le (f := f) (x := 0) (y := y)
  have hlt : (⊥ : EReal) < ((f (0 + y) - f 0 : Real) : EReal) := by
    simpa using (EReal.bot_lt_coe (f (0 + y) - f 0))
  have : (⊥ : EReal) < Function.recessionFunction f y := lt_of_lt_of_le hlt hle
  exact this.ne' hbot

/-- Uniform continuity of `f` on `univ` forces its recession function to be finite everywhere. -/
lemma Section10.recessionFunctionFiniteEverywhere_of_uniformContinuousOn_univ {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hu : UniformContinuousOn f (Set.univ : Set (EuclideanSpace Real (Fin n)))) :
    Function.RecessionFunctionFiniteEverywhere f := by
  classical
  have hu' : UniformContinuous f := (uniformContinuousOn_univ : _ ↔ UniformContinuous f).1 hu
  rcases (Metric.uniformContinuous_iff.1 hu' 1 (by norm_num)) with ⟨δ, hδpos, hδ⟩
  intro y
  by_cases hy0 : y = 0
  · subst hy0
    refine ⟨0, by simp [Section10.recessionFunction_zero]⟩
  · obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖y‖ / δ < (N : ℝ) := exists_nat_gt (‖y‖ / δ)
    have hNpos : 0 < (N : ℝ) := by
      have hyδ : 0 ≤ ‖y‖ / δ := by
        exact div_nonneg (norm_nonneg y) (le_of_lt hδpos)
      exact lt_of_le_of_lt hyδ hN
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    let u : EuclideanSpace Real (Fin n) := (1 / (N : ℝ)) • y
    have hu_norm : ‖u‖ < δ := by
      have hy_lt : ‖y‖ < δ * (N : ℝ) := by
        have : ‖y‖ < (N : ℝ) * δ := (div_lt_iff₀ hδpos).1 hN
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have hy_div : ‖y‖ / (N : ℝ) < δ := by
        exact (div_lt_iff₀ hNpos).2 hy_lt
      have hposinv : 0 < (1 / (N : ℝ)) := one_div_pos.2 hNpos
      have : ‖u‖ = ‖y‖ / (N : ℝ) := by
        simp [u, norm_smul, div_eq_mul_inv, mul_comm]
      simpa [this] using hy_div
    have hdiff_bound : ∀ x : EuclideanSpace Real (Fin n), f (x + y) - f x ≤ (N : ℝ) := by
      intro x
      have hstep : ∀ k : ℕ,
          f (x + ((k + 1 : ℕ) : ℝ) • u) - f (x + (k : ℝ) • u) ≤ 1 := by
        intro k
        have hdist : dist (x + ((k + 1 : ℕ) : ℝ) • u) (x + (k : ℝ) • u) < δ := by
          have hdist0 : dist (((k + 1 : ℕ) : ℝ) • u) ((k : ℝ) • u) = ‖u‖ := by
            have hk :
                (((k + 1 : ℕ) : ℝ) - (k : ℝ)) = (1 : ℝ) := by
              simp [Nat.cast_add_one]
            have hsub :
                (((k + 1 : ℕ) : ℝ) • u) - ((k : ℝ) • u) = u := by
              calc
                (((k + 1 : ℕ) : ℝ) • u) - ((k : ℝ) • u)
                    = ((((k + 1 : ℕ) : ℝ) - (k : ℝ)) • u) := by
                        simpa [sub_smul] using (sub_smul ((k + 1 : ℕ) : ℝ) (k : ℝ) u).symm
                _ = (1 : ℝ) • u := by simp
                _ = u := by simp
            have hsub' : ((k : ℝ) + 1) • u - (k : ℝ) • u = u := by
              simpa [Nat.cast_add_one] using hsub
            simp [dist_eq_norm, Nat.cast_add_one, hsub']
          have hdist1 :
              dist (x + ((k + 1 : ℕ) : ℝ) • u) (x + (k : ℝ) • u) = ‖u‖ := by
            simpa [dist_add_left] using hdist0
          -- Avoid `simp` rewriting away the translation.
          rw [hdist1]
          exact hu_norm
        have hlt : dist (f (x + ((k + 1 : ℕ) : ℝ) • u)) (f (x + (k : ℝ) • u)) < 1 :=
          hδ hdist
        have hlt' : |f (x + ((k + 1 : ℕ) : ℝ) • u) - f (x + (k : ℝ) • u)| < 1 := by
          simpa [Real.dist_eq, abs_sub_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            hlt
        have : f (x + ((k + 1 : ℕ) : ℝ) • u) - f (x + (k : ℝ) • u) < 1 :=
          (abs_lt.1 hlt').2
        exact le_of_lt this
      have hbound' :
          ∀ m : ℕ, f (x + (m : ℝ) • u) - f x ≤ (m : ℝ) := by
        intro m
        induction m with
        | zero =>
            simp
        | succ m hm =>
            have hinc :
                f (x + ((m + 1 : ℕ) : ℝ) • u) - f (x + (m : ℝ) • u) ≤ 1 := hstep m
            have htel :
                f (x + ((m + 1 : ℕ) : ℝ) • u) - f x =
                  (f (x + ((m + 1 : ℕ) : ℝ) • u) - f (x + (m : ℝ) • u)) +
                    (f (x + (m : ℝ) • u) - f x) := by
              ring
            calc
              f (x + ((m + 1 : ℕ) : ℝ) • u) - f x
                  =
                    (f (x + ((m + 1 : ℕ) : ℝ) • u) - f (x + (m : ℝ) • u)) +
                      (f (x + (m : ℝ) • u) - f x) := htel
              _ ≤ 1 + (m : ℝ) := by
                    exact add_le_add hinc hm
              _ = ((m + 1 : ℕ) : ℝ) := by
                    simp [Nat.cast_add_one, add_comm]
      have hbound : f (x + (N : ℝ) • u) - f x ≤ (N : ℝ) := hbound' N
      have hNy : (N : ℝ) • u = y := by
        simp [u, hNne]
      simpa [hNy, add_assoc] using hbound
    have hsup : Function.recessionFunction f y ≤ ((N : ℝ) : EReal) := by
      unfold Function.recessionFunction
      refine sSup_le ?_
      intro r hr
      rcases hr with ⟨x, rfl⟩
      exact (EReal.coe_le_coe_iff.2 (hdiff_bound x))
    have hne_top : Function.recessionFunction f y ≠ (⊤ : EReal) := by
      intro htop
      have : (⊤ : EReal) ≤ ((N : ℝ) : EReal) := by simpa [htop] using hsup
      have : ((N : ℝ) : EReal) = (⊤ : EReal) := top_le_iff.mp this
      exact (EReal.coe_ne_top (N : ℝ)) this
    have hne_bot : Function.recessionFunction f y ≠ (⊥ : EReal) := by
      intro hbot
      have hle :=
        (Section10.recessionFunction_diff_le (f := f) (x := 0) (y := y))
      have hlt : (⊥ : EReal) < ((f (0 + y) - f 0 : Real) : EReal) := by
        simpa using (EReal.bot_lt_coe (f (0 + y) - f 0))
      exact (not_le_of_gt hlt) (by simpa [hbot] using hle)
    refine ⟨(Function.recessionFunction f y).toReal, ?_⟩
    exact (EReal.coe_toReal hne_top hne_bot).symm

/-- If the recession function is finite everywhere, a convex function is Lipschitz on `univ`. -/
lemma Section10.lipschitzRelativeTo_univ_of_recessionFunctionFiniteEverywhere {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hf : ConvexOn ℝ (Set.univ : Set (EuclideanSpace Real (Fin n))) f)
    (hfin : Function.RecessionFunctionFiniteEverywhere f) :
    Function.LipschitzRelativeTo f (Set.univ : Set (EuclideanSpace Real (Fin n))) := by
  classical
  -- Transfer `f` to a function on `Fin n → ℝ` and apply Theorem 8.5.
  let F : (Fin n → Real) → Real := fun x => f (WithLp.toLp (p := 2) x)
  let f0 : (Fin n → Real) → EReal := fun y => Function.recessionFunction f (WithLp.toLp (p := 2) y)
  have hFproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (F x : EReal)) := by
    simpa [F] using
      (Section10.properConvexFunctionOn_univ_coe_comp_toLp_of_convexOn (n := n) (f := f) hf)
  have hf0_plus :
      ∀ y : Fin n → Real,
        f0 y =
          sSup { r : EReal |
            ∃ x ∈ (Set.univ : Set (Fin n → Real)),
              r = ((F (x + y) - F x : Real) : EReal) } := by
    intro y
    have hset :
        {r : EReal | ∃ x : EuclideanSpace Real (Fin n), r = ((f (x + WithLp.toLp (p := 2) y) - f x : Real) : EReal)} =
          { r : EReal |
            ∃ x ∈ (Set.univ : Set (Fin n → Real)),
              r = ((F (x + y) - F x : Real) : EReal) } := by
      ext r
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨(x : Fin n → Real), by simp, ?_⟩
        -- rewrite `x` using `WithLp.toLp` and `F`
        have hx : WithLp.toLp (p := 2) (x : Fin n → Real) = x :=
          Section10.toLp_coeFn_eq (n := n) x
        simp [F, hx, WithLp.toLp_add]
      · rintro ⟨x, hx, rfl⟩
        refine ⟨WithLp.toLp (p := 2) x, ?_⟩
        simp [F, WithLp.toLp_add]
    unfold f0 Function.recessionFunction
    rw [hset]
  have hprops :=
    recessionFunction_properties (n := n) (C := (Set.univ : Set (Fin n → Real)))
      (f := F) (f0_plus := f0) (hf := hFproper) (hC := rfl) (hf0_plus := hf0_plus)
  have hpos : PositivelyHomogeneous f0 := hprops.1
  have hf0proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f0 := hprops.2.1

  -- Finiteness of `f₀⁺` everywhere.
  have hf0_fin : ∀ y : Fin n → Real, ∃ r : Real, f0 y = (r : EReal) := by
    intro y
    simpa [f0] using hfin (WithLp.toLp (p := 2) y)
  have heff : effectiveDomain (Set.univ : Set (Fin n → Real)) f0 = Set.univ := by
    ext y
    constructor
    · intro hy; simp
    · intro hy
      rcases hf0_fin y with ⟨r, hr⟩
      have : f0 y ≠ (⊤ : EReal) := by simp [hr]
      simp [effectiveDomain_eq, lt_top_iff_ne_top, this]

  -- Lipschitz control of `f₀⁺` on the unit ball, hence a global linear bound by homogeneity.
  set S : Set (EuclideanSpace Real (Fin n)) := Metric.closedBall 0 1
  have hSclosed : IsClosed S := by
    simpa [S] using
      (Metric.isClosed_closedBall :
        IsClosed (Metric.closedBall (0 : EuclideanSpace Real (Fin n)) (1 : ℝ)))
  have hSbdd : Bornology.IsBounded S := by
    simpa [S] using
      (Metric.isBounded_closedBall :
        Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace Real (Fin n)) (1 : ℝ)))
  have hSsubset :
      S ⊆
        euclideanRelativeInterior n
          ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f0) := by
    simp [S, heff, Section10.euclideanRelativeInterior_univ (n := n)]
  have hLipS :
      Function.LipschitzRelativeTo
        (fun x : EuclideanSpace Real (Fin n) => (f0 (x : Fin n → Real)).toReal) S :=
    properConvexFunctionOn_lipschitzRelativeTo_of_isClosed_isBounded_subset_ri_effectiveDomain
      (n := n) (f := f0) (hf := hf0proper) (S := S) (hSclosed := hSclosed) (hSbdd := hSbdd)
      (hSsubset := hSsubset)
  rcases hLipS with ⟨K, hK⟩
  have h0S : (0 : EuclideanSpace Real (Fin n)) ∈ S := by simp [S]
  have hK_bound :
      ∀ u : EuclideanSpace Real (Fin n), u ∈ S →
        (f0 (u : Fin n → Real)).toReal ≤ (K : ℝ) := by
    intro u huS
    have hu_edist : edist u (0 : EuclideanSpace Real (Fin n)) ≤ (1 : ENNReal) := by
      have hu_dist : dist u (0 : EuclideanSpace Real (Fin n)) ≤ (1 : ℝ) := by
        simpa [S, Metric.mem_closedBall] using huS
      have :
          edist u (0 : EuclideanSpace Real (Fin n)) ≤ ENNReal.ofReal (1 : ℝ) :=
        (edist_le_ofReal (x := u) (y := (0 : EuclideanSpace Real (Fin n))) (r := (1 : ℝ))
              (by norm_num)).2 hu_dist
      simpa using this
    have hdistE :
        edist (f0 (u : Fin n → Real)).toReal (f0 (0 : Fin n → Real)).toReal ≤ (K : ENNReal) := by
      have hdistE' :=
        hK.edist_le_mul_of_le huS h0S hu_edist
      simpa [one_mul] using hdistE'
    have hdistR :
        dist (f0 (u : Fin n → Real)).toReal (f0 (0 : Fin n → Real)).toReal ≤ (K : ℝ) := by
      have ha :
          edist (f0 (u : Fin n → Real)).toReal (f0 (0 : Fin n → Real)).toReal ≠ (⊤ : ENNReal) := by
        exact edist_ne_top _ _
      have hb : (K : ENNReal) ≠ (⊤ : ENNReal) := by simp
      have htoReal :
          (edist (f0 (u : Fin n → Real)).toReal (f0 (0 : Fin n → Real)).toReal).toReal ≤
            ((K : ENNReal)).toReal :=
        (ENNReal.toReal_le_toReal ha hb).2 hdistE
      simpa [dist_edist] using htoReal
    have hdist' :
        |(f0 (u : Fin n → Real)).toReal - (f0 (0 : Fin n → Real)).toReal| ≤ (K : ℝ) := by
      simpa [Real.dist_eq] using hdistR
    have hzero : (f0 (0 : Fin n → Real)).toReal = 0 := by
      have : f0 (0 : Fin n → Real) = (0 : EReal) := by
        simpa [f0] using (Section10.recessionFunction_zero (f := f))
      simp [this]
    have habs : |(f0 (u : Fin n → Real)).toReal| ≤ (K : ℝ) := by
      simpa [hzero, sub_eq_add_neg] using hdist'
    have : (f0 (u : Fin n → Real)).toReal ≤ |(f0 (u : Fin n → Real)).toReal| := le_abs_self _
    exact this.trans habs

  -- Global upper bound for the recession function.
  have hrec_le : ∀ v : EuclideanSpace Real (Fin n),
      Function.recessionFunction f v ≤ (((K : ℝ) * ‖v‖ : ℝ) : EReal) := by
    intro v
    by_cases hv0 : v = 0
    · subst hv0
      simp [Section10.recessionFunction_zero]
    · have htpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
      set u : EuclideanSpace Real (Fin n) := (‖v‖)⁻¹ • v
      have hu_norm : ‖u‖ = 1 := by
        simp [u, norm_smul, htpos.ne']
      have huS : u ∈ S := by
        -- `u` lies on the unit sphere, hence in the closed unit ball.
        simp [S, Metric.mem_closedBall, dist_eq_norm, hu_norm]
      have hfu_le : (f0 (u : Fin n → Real)).toReal ≤ (K : ℝ) := hK_bound u huS
      have hfu_ne_top : f0 (u : Fin n → Real) ≠ (⊤ : EReal) := by
        rcases hf0_fin (u : Fin n → Real) with ⟨r, hr⟩
        simp [hr]
      have hfu_ne_bot : f0 (u : Fin n → Real) ≠ (⊥ : EReal) :=
        hf0proper.2.2 (u : Fin n → Real) (by simp)
      have hfu_coe :
          (f0 (u : Fin n → Real)).toReal = (f0 (u : Fin n → Real)).toReal := rfl
      have hfu_eq :
          f0 (u : Fin n → Real) = (((f0 (u : Fin n → Real)).toReal : ℝ) : EReal) := by
        exact (EReal.coe_toReal hfu_ne_top hfu_ne_bot).symm
      have hhom :
          f0 ((‖v‖ : ℝ) • (u : Fin n → Real)) = ((‖v‖ : ℝ) : EReal) * f0 (u : Fin n → Real) :=
        hpos (u : Fin n → Real) ‖v‖ htpos
      have hv_repr_fn : (‖v‖ : ℝ) • (u : Fin n → Real) = (v : Fin n → Real) := by
        ext i
        simp [u, htpos.ne']
      have hv_eq : f0 (v : Fin n → Real) = ((‖v‖ : ℝ) : EReal) * f0 (u : Fin n → Real) := by
        simpa [hv_repr_fn] using hhom
      have hmul_le :
          ((‖v‖ : ℝ) : EReal) * f0 (u : Fin n → Real) ≤
            ((‖v‖ : ℝ) : EReal) * ((K : ℝ) : EReal) := by
        have hvn : 0 ≤ ‖v‖ := norm_nonneg v
        have hreal :
            ‖v‖ * (f0 (u : Fin n → Real)).toReal ≤ ‖v‖ * (K : ℝ) :=
          mul_le_mul_of_nonneg_left hfu_le hvn
        have hcoe :
            ((‖v‖ * (f0 (u : Fin n → Real)).toReal : ℝ) : EReal) ≤
              ((‖v‖ * (K : ℝ) : ℝ) : EReal) :=
          (EReal.coe_le_coe_iff.2 hreal)
        calc
          ((‖v‖ : ℝ) : EReal) * f0 (u : Fin n → Real)
              = ((‖v‖ : ℝ) : EReal) *
                  (((f0 (u : Fin n → Real)).toReal : ℝ) : EReal) := by
                    simpa using
                      congrArg (fun t => ((‖v‖ : ℝ) : EReal) * t) hfu_eq
          _ = ((‖v‖ * (f0 (u : Fin n → Real)).toReal : ℝ) : EReal) := by
                    simp [EReal.coe_mul]
          _ ≤ ((‖v‖ * (K : ℝ) : ℝ) : EReal) := hcoe
          _ = ((‖v‖ : ℝ) : EReal) * ((K : ℝ) : EReal) := by
                    simp [EReal.coe_mul]
      have hv_toLp : WithLp.toLp (p := 2) (v : Fin n → Real) = v :=
        Section10.toLp_coeFn_eq (n := n) v
      have huv_toLp : WithLp.toLp (p := 2) (u : Fin n → Real) = u :=
        Section10.toLp_coeFn_eq (n := n) u
      have hrv : Function.recessionFunction f v = f0 (v : Fin n → Real) := by
        simp [f0, hv_toLp]
      -- Convert to the desired bound.
      have :
          Function.recessionFunction f v ≤ ((‖v‖ : ℝ) : EReal) * ((K : ℝ) : EReal) := by
        simpa [hrv, hv_eq] using hmul_le
      -- Commute scalars and rewrite as a real-coe.
      simpa [EReal.coe_mul, mul_assoc, mul_comm, mul_left_comm] using this

  -- Lipschitz estimate for `f` itself from the global recession bound.
  refine ⟨Real.toNNReal (K : ℝ), ?_⟩
  refine LipschitzOnWith.of_dist_le' (fun x _ y _ => ?_)
  have hxyE :
      ((f y - f x : ℝ) : EReal) ≤ (((K : ℝ) * ‖y - x‖ : ℝ) : EReal) := by
    have h₁ :
        ((f (x + (y - x)) - f x : ℝ) : EReal) ≤ Function.recessionFunction f (y - x) :=
      Section10.recessionFunction_diff_le (f := f) x (y - x)
    have h₂ :
        Function.recessionFunction f (y - x) ≤ (((K : ℝ) * ‖y - x‖ : ℝ) : EReal) :=
      hrec_le (y - x)
    simpa [add_sub_cancel] using le_trans h₁ h₂
  have hyxE :
      ((f x - f y : ℝ) : EReal) ≤ (((K : ℝ) * ‖y - x‖ : ℝ) : EReal) := by
    have h₁ :
        ((f (y + (x - y)) - f y : ℝ) : EReal) ≤ Function.recessionFunction f (x - y) :=
      Section10.recessionFunction_diff_le (f := f) y (x - y)
    have h₂ :
        Function.recessionFunction f (x - y) ≤ (((K : ℝ) * ‖x - y‖ : ℝ) : EReal) :=
      hrec_le (x - y)
    have h₃ :
        (((K : ℝ) * ‖x - y‖ : ℝ) : EReal) = (((K : ℝ) * ‖y - x‖ : ℝ) : EReal) := by
      simp [norm_sub_rev]
    simpa [add_sub_cancel] using le_trans h₁ (h₂.trans_eq h₃)
  have hxy : f y - f x ≤ (K : ℝ) * ‖y - x‖ := by
    exact (EReal.coe_le_coe_iff.1 hxyE)
  have hyx : f x - f y ≤ (K : ℝ) * ‖y - x‖ := by
    exact (EReal.coe_le_coe_iff.1 hyxE)
  have hxy' : f y - f x ≤ (K : ℝ) * ‖x - y‖ := by
    simpa [norm_sub_rev] using hxy
  have hyx' : f x - f y ≤ (K : ℝ) * ‖x - y‖ := by
    simpa [norm_sub_rev] using hyx
  simp [dist_eq_norm_sub]
  exact (abs_sub_le_iff.2 ⟨hyx', hxy'⟩)

/-- Theorem 10.5. Let `f` be a finite convex function on `ℝ^n`. In order that `f` be uniformly
continuous relative to `ℝ^n`, it is necessary and sufficient that the recession function `f₀⁺`
of `f` be finite everywhere. In this event, `f` is actually Lipschitzian relative to `ℝ^n`. -/
theorem convexOn_uniformContinuousOn_univ_iff_recessionFunctionFiniteEverywhere {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hf : ConvexOn ℝ (Set.univ : Set (EuclideanSpace Real (Fin n))) f) :
    (UniformContinuousOn f (Set.univ : Set (EuclideanSpace Real (Fin n))) ↔
        Function.RecessionFunctionFiniteEverywhere f) ∧
      (Function.RecessionFunctionFiniteEverywhere f →
        Function.LipschitzRelativeTo f (Set.univ : Set (EuclideanSpace Real (Fin n)))) := by
  refine ⟨?_, ?_⟩
  · constructor
    · exact Section10.recessionFunctionFiniteEverywhere_of_uniformContinuousOn_univ (f := f)
    · intro hfin
      exact
        (Section10.lipschitzRelativeTo_univ_of_recessionFunctionFiniteEverywhere (n := n) (f := f)
              hf hfin).uniformContinuousOn
  · intro hfin
    exact
      Section10.lipschitzRelativeTo_univ_of_recessionFunctionFiniteEverywhere (n := n) (f := f)
        hf hfin

/-- A finite convex function on `ℝ^n` yields a closed convex `EReal`-valued function on `univ`
after composing with `WithLp.toLp` and coercing to `EReal`. -/
lemma Section10.closedConvexFunction_coe_comp_toLp_of_convexOn {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hf : ConvexOn ℝ (Set.univ : Set (EuclideanSpace Real (Fin n))) f) :
    ClosedConvexFunction (fun x : Fin n → Real => (f (WithLp.toLp (p := 2) x) : EReal)) := by
  classical
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real))
        (fun x : Fin n → Real => (f (WithLp.toLp (p := 2) x) : EReal)) :=
    Section10.properConvexFunctionOn_univ_coe_comp_toLp_of_convexOn (n := n) (f := f) hf
  have hf_cont : Continuous f := by
    have hcontOn : ContinuousOn f (Set.univ : Set (EuclideanSpace Real (Fin n))) := by
      simpa [interior_univ] using hf.continuousOn_interior
    exact (continuousOn_univ.1 hcontOn)
  have hcont_toLp : Continuous (fun x : Fin n → Real => WithLp.toLp (p := 2) x) := by
    simpa using
      (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n => Real))
  have hcont_comp : Continuous (fun x : Fin n → Real => f (WithLp.toLp (p := 2) x)) :=
    hf_cont.comp hcont_toLp
  have hlsc :
      LowerSemicontinuous (fun x : Fin n → Real => (f (WithLp.toLp (p := 2) x) : EReal)) :=
    (_root_.continuous_coe_real_ereal.comp hcont_comp).lowerSemicontinuous
  exact (properConvexFunction_closed_iff_lowerSemicontinuous (f :=
      fun x : Fin n → Real => (f (WithLp.toLp (p := 2) x) : EReal)) hproper).2 hlsc

/-- Along a ray, the difference quotient `(f(t•y) - f(0))/t` converges to the recession function.

This is Theorem 8.5 specialized to `x = 0` and rewritten in terms of `Function.recessionFunction`. -/
lemma Section10.tendsto_div_sub_to_recessionFunction {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hf : ConvexOn ℝ (Set.univ : Set (EuclideanSpace Real (Fin n))) f) :
    ∀ y : EuclideanSpace Real (Fin n),
      Filter.Tendsto (fun t : ℝ => (((f (t • y) - f 0) / t : Real) : EReal)) Filter.atTop
        (nhds (Function.recessionFunction f y)) := by
  classical
  intro y
  -- Transfer `f` to a function on `Fin n → ℝ` and apply Theorem 8.5.
  let F : (Fin n → Real) → Real := fun x => f (WithLp.toLp (p := 2) x)
  let f0 : (Fin n → Real) → EReal := fun y => Function.recessionFunction f (WithLp.toLp (p := 2) y)
  have hFproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fun x => (F x : EReal)) := by
    simpa [F] using
      (Section10.properConvexFunctionOn_univ_coe_comp_toLp_of_convexOn (n := n) (f := f) hf)
  have hf0_plus :
      ∀ y : Fin n → Real,
        f0 y =
          sSup { r : EReal |
            ∃ x ∈ (Set.univ : Set (Fin n → Real)),
              r = ((F (x + y) - F x : Real) : EReal) } := by
    intro y
    have hset :
        {r : EReal | ∃ x : EuclideanSpace Real (Fin n), r = ((f (x + WithLp.toLp (p := 2) y) - f x : Real) : EReal)} =
          { r : EReal |
            ∃ x ∈ (Set.univ : Set (Fin n → Real)),
              r = ((F (x + y) - F x : Real) : EReal) } := by
      ext r
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨(x : Fin n → Real), by simp, ?_⟩
        have hx : WithLp.toLp (p := 2) (x : Fin n → Real) = x :=
          Section10.toLp_coeFn_eq (n := n) x
        simp [F, hx, WithLp.toLp_add]
      · rintro ⟨x, hx, rfl⟩
        refine ⟨WithLp.toLp (p := 2) x, ?_⟩
        simp [F, WithLp.toLp_add]
    unfold f0 Function.recessionFunction
    rw [hset]
  have hprops :=
    recessionFunction_properties (n := n) (C := (Set.univ : Set (Fin n → Real)))
      (f := F) (f0_plus := f0) (hf := hFproper) (hC := rfl) (hf0_plus := hf0_plus)
  rcases hprops with ⟨_, _, _, hclosedprops⟩
  have hclosedF :
      ClosedConvexFunction (fun x : Fin n → Real => (F x : EReal)) := by
    simpa [F] using
      (Section10.closedConvexFunction_coe_comp_toLp_of_convexOn (n := n) (f := f) hf)
  have htend :=
    (hclosedprops hclosedF).2 0 (by simp) (y : Fin n → Real)
  -- Rewrite the statement back in terms of `f` on `EuclideanSpace`.
  simpa [F, f0, Section10.toLp_coeFn_eq] using htend.2

/-- If `liminf_{t→∞} f(t•y)/t` is finite for all `y`, then the recession function is finite
everywhere. -/
lemma Section10.recessionFunctionFiniteEverywhere_of_liminf_div_lt_top {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hf : ConvexOn ℝ (Set.univ : Set (EuclideanSpace Real (Fin n))) f)
    (hlim :
      ∀ y : EuclideanSpace Real (Fin n),
        Filter.liminf (fun t : ℝ => ((f (t • y) / t : Real) : EReal)) Filter.atTop < (⊤ : EReal)) :
    Function.RecessionFunctionFiniteEverywhere f := by
  classical
  intro y
  let g : ℝ → EReal := fun t => ((f (t • y) / t : Real) : EReal)
  let diff : ℝ → EReal := fun t => (((f (t • y) - f 0) / t : Real) : EReal)
  let c : EReal := ((|f 0| : Real) : EReal)
  have htend :
      Filter.Tendsto diff Filter.atTop (nhds (Function.recessionFunction f y)) := by
    simpa [diff] using (Section10.tendsto_div_sub_to_recessionFunction (n := n) (f := f) hf y)
  have hdiff_le : ∀ᶠ t : ℝ in Filter.atTop, diff t ≤ g t + c := by
    have hge1 : ∀ᶠ t : ℝ in Filter.atTop, (1 : ℝ) ≤ t :=
      Filter.eventually_atTop.2 ⟨1, fun t ht => ht⟩
    filter_upwards [hge1] with t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
    have hreal : (f (t • y) - f 0) / t ≤ f (t • y) / t + |f 0| := by
      have hneg_le : (-f 0) / t ≤ |f 0| := by
        have h₁ : (-f 0) / t ≤ |f 0| / t := by
          exact div_le_div_of_nonneg_right (neg_le_abs (f 0)) (le_of_lt htpos)
        have h₂ : |f 0| / t ≤ |f 0| := div_le_self (abs_nonneg (f 0)) ht
        exact h₁.trans h₂
      -- `((a - b)/t) = a/t + (-b)/t` and bound the second term by `|b|`.
      have : f (t • y) / t + (-f 0) / t ≤ f (t • y) / t + |f 0| :=
        add_le_add_right hneg_le (f (t • y) / t)
      simpa [sub_eq_add_neg, add_div, add_assoc, add_left_comm, add_comm] using this
    have hE :
        diff t ≤ ((f (t • y) / t + |f 0| : Real) : EReal) :=
      (EReal.coe_le_coe_iff.2 hreal)
    simpa [g, diff, c, EReal.coe_add] using hE
  have hliminf_le :
      Filter.liminf diff Filter.atTop ≤ Filter.liminf (fun t : ℝ => g t + c) Filter.atTop :=
    (Filter.liminf_le_liminf hdiff_le (hu := by isBoundedDefault) (hv := by isBoundedDefault))
  have hliminf_g_add :
      Filter.liminf (fun t : ℝ => g t + c) Filter.atTop < (⊤ : EReal) := by
    -- Since `c` is a finite constant, `liminf (c + g)` is bounded above by `c + liminf g`.
    let u : ℝ → EReal := fun _ => c
    have hu_ne_top : Filter.limsup u Filter.atTop ≠ (⊤ : EReal) := by
      simp [u, Filter.limsup_const, c]
    have hg_ne_top : Filter.liminf g Filter.atTop ≠ (⊤ : EReal) := by
      have : Filter.liminf g Filter.atTop < (⊤ : EReal) := by
        simpa [g] using hlim y
      exact this.ne
    have hle :
        Filter.liminf (fun t : ℝ => c + g t) Filter.atTop ≤
          c + Filter.liminf g Filter.atTop := by
      simpa [u, Filter.limsup_const, add_assoc] using
        (EReal.liminf_add_le (f := (Filter.atTop : Filter ℝ)) (u := u) (v := g)
          (Or.inr hg_ne_top) (Or.inl hu_ne_top))
    have hlt : c + Filter.liminf g Filter.atTop < (⊤ : EReal) := by
      refine EReal.add_lt_top (EReal.coe_ne_top (|f 0|)) ?_
      have : Filter.liminf g Filter.atTop < (⊤ : EReal) := by
        simpa [g] using hlim y
      exact this.ne
    have : Filter.liminf (fun t : ℝ => c + g t) Filter.atTop < (⊤ : EReal) :=
      lt_of_le_of_lt hle hlt
    simpa [add_comm] using this
  have hliminf_diff_lt : Filter.liminf diff Filter.atTop < (⊤ : EReal) :=
    lt_of_le_of_lt hliminf_le hliminf_g_add
  have hne_top : Function.recessionFunction f y ≠ (⊤ : EReal) := by
    have hEq : Filter.liminf diff Filter.atTop = Function.recessionFunction f y :=
      (Filter.Tendsto.liminf_eq htend)
    have : Filter.liminf diff Filter.atTop ≠ (⊤ : EReal) := hliminf_diff_lt.ne
    simpa [hEq] using this
  have hne_bot : Function.recessionFunction f y ≠ (⊥ : EReal) :=
    Section10.recessionFunction_ne_bot (n := n) f y
  refine ⟨(Function.recessionFunction f y).toReal, ?_⟩
  exact (EReal.coe_toReal hne_top hne_bot).symm

/-- Corollary 10.5.1. A finite convex function `f` is Lipschitzian relative to `ℝ^n` if
`liminf_{λ → ∞} f(λ • y) / λ < ∞` for all `y`. -/
theorem convexOn_lipschitzRelativeTo_univ_of_liminf_div_lt_top {n : ℕ}
    {f : EuclideanSpace Real (Fin n) → Real}
    (hf : ConvexOn ℝ (Set.univ : Set (EuclideanSpace Real (Fin n))) f)
    (hlim :
      ∀ y : EuclideanSpace Real (Fin n),
        Filter.liminf (fun t : ℝ => ((f (t • y) / t : Real) : EReal)) Filter.atTop <
          (⊤ : EReal)) :
    Function.LipschitzRelativeTo f (Set.univ : Set (EuclideanSpace Real (Fin n))) := by
  have hfin : Function.RecessionFunctionFiniteEverywhere f :=
    Section10.recessionFunctionFiniteEverywhere_of_liminf_div_lt_top (n := n) (f := f) hf hlim
  exact (convexOn_uniformContinuousOn_univ_iff_recessionFunctionFiniteEverywhere (n := n) (f := f)
    hf).2 hfin

/-- If `u ≤ v` eventually along a filter, then `liminf u ≤ liminf v`. -/
lemma Section10.liminf_le_liminf_of_eventually_le {α : Type*} {l : Filter α}
    {u v : α → EReal} (h : ∀ᶠ a in l, u a ≤ v a) :
    Filter.liminf u l ≤ Filter.liminf v l := by
  simpa using (Filter.liminf_le_liminf (f := l) (u := u) (v := v) h)

end Section10
end Chap02
