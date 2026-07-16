import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap10.Example_10_44
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap12.Definition_12_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

open InnerProductSpace (toDualMap)

/- Lemma 12.3 is `bridge/view`: Definition 12.5 already owns the source-facing Chapter 12 terms
`F(y) = f*(Aᵀ y)` and `G(y) = g*(-y)` on the dual space, while Definition 12.4 owns the dual
objective `q` and its primal-space bridge. The `G`-side bridge here only evaluates that owner
along the Riesz map `toDualMap ℝ Y`, so it lives on a real inner-product space. The `F`-side
bridge additionally identifies `A.dualMap` with the Riesz image of `A.adjoint`, so the public
owner can stay on the chapter's linear-map parameter `A : E →ₗ[ℝ] Y` while the Hilbert adjoint is
handled internally through the canonical continuous-linear-map bridge. Finite-dimensional
hypotheses re-enter only for the Chapter 5 finiteness and smoothness consequences. This file
therefore keeps only the source-facing primal formulas for `F` and `G` and their analytic
properties as thin pullback consequences of the Chapter 4/5 owner theorems for conjugates. -/

section

variable {E : Type u} {Y : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

-- Proof sketch: evaluate the Chapter 12 owner `dual_based_proximal_gradient_dual_F_term` at the
-- Riesz functional `toDualMap ℝ Y y`, rewrite the primal conjugate by
-- `conjugate_function_primal_apply`, and use the adjoint identity to identify the pulled-back dual
-- functional with `toDualMap ℝ E (A.adjoint y)`.
/-- Evaluating the Chapter 12 owner `F(y) = f*(Aᵀ y)` on the primal-space variable `y` gives the
primal-space formula `(f∗) (A.adjoint y)`. -/
@[simp] theorem dual_based_proximal_gradient_dual_F_primal_apply
    (f : E → EReal) (A : E →ₗ[ℝ] Y) (y : Y) :
    dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ Y y) =
      (f∗) (A.adjoint y) := by
  rw [dual_based_proximal_gradient_dual_F_term_apply, conjugate_function_primal_apply]
  congr
  ext x
  simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, A.adjoint_inner_left]

-- Proof sketch: the primal conjugate `f∗` is convex by the Chapter 4 conjugacy theorem, and
-- precomposition with the linear map `A.adjoint` preserves convexity.
/-- Lemma 12.3 (1): source part (a). The dual term `F(y) = f*(Aᵀ y)` is convex. -/
theorem dual_based_proximal_gradient_dual_F_primal_convex
    (f : E → EReal) (A : E →ₗ[ℝ] Y) :
    is_convex_function (fun y : Y ↦ (f∗) (A.adjoint y)) := by
  simpa using
    is_convex_function_precompose_linearMap_add
      (conjugate_function_closed_and_convex f).2
      A.adjoint (0 : E)

-- Proof sketch: a proper closed `σ`-strongly convex function has a finite-valued Fenchel
-- conjugate everywhere by `conjugate_function_finite_of_proper_closed_strongConvexOn`. Evaluate
-- that owner at the canonical Riesz functional `InnerProductSpace.toDual ℝ E (A.adjoint y)`.
/-- Lemma 12.3 (2): source part (a). If `f` is proper, closed, and `σ`-strongly convex, then
`F(y) = f*(Aᵀ y)` is finite-valued for every `y`. -/
theorem dual_based_proximal_gradient_dual_F_primal_finite_valued
    (σ : PosReal) (f : E → EReal) (A : E →ₗ[ℝ] Y)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)) :
    ∀ y : Y,
      (f∗) (A.adjoint y) ≠ ⊥ ∧
        (f∗) (A.adjoint y) < ⊤ := by
  intro y
  have hfin :=
    conjugate_function_finite_of_proper_closed_strongConvexOn
      (σ : ℝ) σ.2 f hf_proper.ne_bot hf_proper.effective_domain_nonempty hf_closed hf_strong
      (InnerProductSpace.toDual ℝ E (A.adjoint y))
  simpa [conjugate_function_strongDual, conjugate_function_primal_apply, conjugate_function]
    using hfin

/-- Helper for Lemma 12.3: the Chapter 5 strong-dual smoothness theorem transports through the
Riesz isometry to the primal conjugate `x ↦ ((f∗) x).toReal`. -/
lemma conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
    (σ : PosReal) (f : E → EReal)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)) :
    is_l_smooth_on
      (fun x : E ↦ ((f∗) x).toReal)
      Set.univ
      (Real.toNNReal (1 / (σ : ℝ))) := by
  let fStarStrongDual : StrongDual ℝ E → ℝ := fun y ↦ (conjugate_function_strongDual f y).toReal
  have hsmooth :=
    is_l_smooth_on_toReal_conjugate_function_strongDual_of_proper_closed_strongConvexOn
      (σ : ℝ) σ.2 f hf_proper.ne_bot hf_proper.effective_domain_nonempty hf_closed hf_strong
  let T : E →L[ℝ] StrongDual ℝ E :=
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap
  rw [is_l_smooth_on_iff] at hsmooth ⊢
  refine ⟨?_, ?_⟩
  · intro x hx
    -- Transport differentiability through the Riesz identification `E ≃ StrongDual ℝ E`.
    have hdiff : DifferentiableAt ℝ fStarStrongDual (T x) := hsmooth.1 _ (by simp [T])
    simpa [T, fStarStrongDual, conjugate_function_primal_apply, conjugate_function_strongDual,
      InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
      hdiff.comp x T.differentiableAt
  · intro x hx y hy
    -- The derivative bound is preserved because precomposition with the Riesz isometry keeps the
    -- operator norm unchanged.
    have hxy := hsmooth.2 (T x) (by simp [T]) (T y) (by simp [T])
    have hTx : DifferentiableAt ℝ fStarStrongDual (T x) := hsmooth.1 _ (by simp [T])
    have hTy : DifferentiableAt ℝ fStarStrongDual (T y) := hsmooth.1 _ (by simp [T])
    have hTderiv (z : E) : fderiv ℝ (fun w : E ↦ T w) z = T := by
      simpa [T] using T.fderiv
    have hxderiv :
        fderiv ℝ (fun z : E ↦ fStarStrongDual (T z)) x =
          (fderiv ℝ fStarStrongDual (T x)).comp T := by
      simpa [Function.comp, T, ContinuousLinearMap.comp_apply, hTderiv x] using
        (fderiv_comp x hTx T.differentiableAt)
    have hyderiv :
        fderiv ℝ (fun z : E ↦ fStarStrongDual (T z)) y =
          (fderiv ℝ fStarStrongDual (T y)).comp T := by
      simpa [Function.comp, T, ContinuousLinearMap.comp_apply, hTderiv y] using
        (fderiv_comp y hTy T.differentiableAt)
    have hsub :
        (fderiv ℝ fStarStrongDual (T x)).comp T -
          (fderiv ℝ fStarStrongDual (T y)).comp T =
        (fderiv ℝ fStarStrongDual (T x) -
            fderiv ℝ fStarStrongDual (T y)).comp T := by
      ext z
      rfl
    calc
      ‖fderiv ℝ (fun z : E ↦ fStarStrongDual (T z)) x -
          fderiv ℝ (fun z : E ↦ fStarStrongDual (T z)) y‖
          =
          ‖(fderiv ℝ fStarStrongDual (T x)).comp T -
            (fderiv ℝ fStarStrongDual (T y)).comp T‖ := by
              rw [hxderiv, hyderiv]
      _ =
          ‖(fderiv ℝ fStarStrongDual (T x) -
              fderiv ℝ fStarStrongDual (T y)).comp T‖ := by
              exact congrArg norm hsub
      _ =
          ‖fderiv ℝ fStarStrongDual (T x) -
              fderiv ℝ fStarStrongDual (T y)‖ := by
              simpa [T] using
                (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv
                  (f := fderiv ℝ fStarStrongDual (T x) -
                    fderiv ℝ fStarStrongDual (T y))
                  (g := InnerProductSpace.toDual ℝ E))
      _ ≤ (Real.toNNReal (1 / (σ : ℝ)) : ℝ) * ‖T x - T y‖ := hxy
      _ = (Real.toNNReal (1 / (σ : ℝ)) : ℝ) * ‖x - y‖ := by
            rw [← map_sub]
            have hnorm : ‖T (x - y)‖ = ‖x - y‖ := by
              simpa [T] using (InnerProductSpace.toDual ℝ E).norm_map (x - y)
            rw [hnorm]

/-- Helper for Lemma 12.3: precomposing an `L`-smooth real-valued function on `E` with
`A.adjoint` multiplies the smoothness constant by `‖A‖^2`. -/
lemma is_l_smooth_on_precompose_adjoint
    (A : E →ₗ[ℝ] Y) (h : E → ℝ) {L : NNReal}
    (hh : is_l_smooth_on h Set.univ L) :
    is_l_smooth_on
      (fun y : Y ↦ h (A.adjoint y))
      Set.univ
      (L * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ)) := by
  have hA :
      ‖A.adjoint.toContinuousLinearMap‖₊ = ‖A.toContinuousLinearMap‖₊ := by
    simpa [LinearMap.adjoint_toContinuousLinearMap] using
      (ContinuousLinearMap.adjoint.nnnorm_map A.toContinuousLinearMap)
  -- Reuse the Chapter 10 continuous-linear pullback lemma, then rewrite the adjoint norm.
  simpa [hA] using
    Example_10_44.is_l_smooth_on_precompose_continuousLinearMap
      A.adjoint.toContinuousLinearMap h hh

-- Proof sketch: first apply the Chapter 5 theorem that a proper closed `σ`-strongly convex
-- function has globally `1 / σ`-smooth conjugate on the primal space. Then precompose with the
-- adjoint map `A.adjoint`; the smoothness constant is multiplied by
-- `‖A.toContinuousLinearMap‖²`.
/-- Lemma 12.3 (3): source part (a). If `f` is proper, closed, and `σ`-strongly convex, then the
finite-valued function `F(y) = f*(Aᵀ y)` is globally smooth with constant `‖A‖^2 / σ`, written
here as the equivalent `NNReal` constant
`Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊^2`. -/
theorem dual_based_proximal_gradient_dual_F_primal_is_l_smooth
    (σ : PosReal) (f : E → EReal) (A : E →ₗ[ℝ] Y)
    (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f)
    (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)) :
    is_l_smooth_on
      (fun y : Y ↦ ((f∗) (A.adjoint y)).toReal)
      Set.univ
      (Real.toNNReal (1 / (σ : ℝ)) * ‖A.toContinuousLinearMap‖₊ ^ (2 : ℕ)) := by
  -- First put the Chapter 5 smoothness statement on the primal conjugate `f∗`.
  have hconj :=
    conjugate_function_primal_is_l_smooth_on_of_proper_closed_strongConvexOn
      σ f hf_proper hf_closed hf_strong
  -- Then pull that global smoothness bound back along `A.adjoint`.
  simpa using is_l_smooth_on_precompose_adjoint A (fun x : E ↦ ((f∗) x).toReal) hconj

end

section

variable {Y : Type v}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

-- Proof sketch: evaluate the Chapter 12 owner `dual_based_proximal_gradient_dual_G_term` at the
-- Riesz functional `toDualMap ℝ Y y`, then rewrite the negated functional as the Riesz image of
-- `-y`.
/-- Evaluating the Chapter 12 owner `G(y) = g*(-y)` on the primal-space variable `y` gives the
primal-space formula `(g∗) (-y)`. -/
@[simp] theorem dual_based_proximal_gradient_dual_G_primal_apply
    (g : Y → EReal) (y : Y) :
    dual_based_proximal_gradient_dual_G_term g (toDualMap ℝ Y y) = (g∗) (-y) := by
  rw [dual_based_proximal_gradient_dual_G_term_apply, conjugate_function_primal_apply]
  congr
  ext x
  simp [InnerProductSpace.toDualMap_apply_apply]

-- Proof sketch: a proper convex extended-real-valued function has a proper conjugate. Composing
-- the primal conjugate `g∗` with negation preserves properness.
/-- Lemma 12.3 (4): source part (b). If `g` is proper and convex, then `G(y) = g*(-y)` is proper.
-/
theorem dual_based_proximal_gradient_dual_G_primal_proper
    [FiniteDimensional ℝ Y]
    (g : Y → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (hg_convex : is_convex_function g) :
    IsProperExtendedRealFunction (fun y : Y ↦ (g∗) (-y)) := by
  let hconj := isProperExtendedRealFunction_conjugate_function g hg_proper hg_convex
  refine ⟨?_, ?_⟩
  · intro y
    simpa [conjugate_function_primal_apply] using hconj.ne_bot (toDualMap ℝ Y (-y))
  · rcases hconj.effective_domain_nonempty with ⟨y, hy⟩
    let y' : StrongDual ℝ Y := LinearMap.toContinuousLinearMap y
    rcases (InnerProductSpace.toDual ℝ Y).surjective y' with ⟨x, hx⟩
    refine ⟨-x, ?_⟩
    rw [mem_effective_domain]
    simpa [conjugate_function_primal_apply] using hx ▸ hy

-- Proof sketch: the primal conjugate `g∗` is always closed and convex, and composing with the
-- continuous linear map `y ↦ -y` preserves both lower semicontinuity and convexity.
/-- Lemma 12.3 (5): source part (b). The dual term `G(y) = g*(-y)` is closed and convex. -/
theorem dual_based_proximal_gradient_dual_G_primal_closed_and_convex
    (g : Y → EReal) :
    LowerSemicontinuous (fun y : Y ↦ (g∗) (-y)) ∧
      is_convex_function (fun y : Y ↦ (g∗) (-y)) := by
  refine ⟨?_, ?_⟩
  · exact
      (conjugate_function_closed_and_convex g).1.comp
        ((-ContinuousLinearMap.id ℝ Y).continuous)
  · simpa using
      is_convex_function_precompose_linearMap_add
        (conjugate_function_closed_and_convex g).2
        (-LinearMap.id : Y →ₗ[ℝ] Y) (0 : Y)

end
