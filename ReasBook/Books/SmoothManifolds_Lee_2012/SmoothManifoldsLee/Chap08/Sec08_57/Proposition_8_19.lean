import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Definition_8_57_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Definition_8_57_extra_2

open scoped ContDiff Manifold

-- The source-facing owners are the chapter predicate `VectorField.f_related` and the textbook
-- pushforward surface `F_* X`; the canonical pullback-smoothness owner used internally is
-- mathlib's `ContMDiff.mpullback_vectorField`.

universe u𝕜 uE uE' uH uH' uM uN

noncomputable section

section

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E' H'}
  [IsManifold I (∞ : ℕ∞ω) M]
  [IsManifold J (∞ : ℕ∞ω) N]

omit [IsManifold I (∞ : ℕ∞ω) M] [IsManifold J (∞ : ℕ∞ω) N] in
private theorem mfderiv_symm_isInvertible
    (F : M ≃ₘ⟮I, J⟯ N)
    (q : N) :
    (mfderiv J I F.symm q).IsInvertible :=
by
  let e : TangentSpace J q ≃L[𝕜] TangentSpace I (F.symm q) :=
    F.symm.mfderivToContinuousLinearEquiv (by simp) q
  refine ⟨e, ?_⟩
  simpa [e] using
    (F.symm.mfderivToContinuousLinearEquiv_coe (by simp) :
      ↑(F.symm.mfderivToContinuousLinearEquiv (by simp) q) = mfderiv J I F.symm q).symm

/- Lee's pushforward vector field `F_* X` is `F`-related to `X`. -/
omit [IsManifold I (∞ : ℕ∞ω) M] [IsManifold J (∞ : ℕ∞ω) N] in
theorem f_related_pushforward_of_diffeomorph
    (F : M ≃ₘ⟮I, J⟯ N)
    (X : ∀ p : M, TangentSpace I p) :
    VectorField.f_related (F : M → N) X (((F _* X) : ∀ q : N, TangentSpace J q)) := by
  refine ⟨F.contMDiff, ?_⟩
  intro p
  change (mfderiv I J F p) (X p) = VectorField.mpullback J I F.symm X (F p)
  rw [VectorField.mpullback_apply, F.symm_apply_apply, eq_comm]
  refine
    (ContinuousLinearMap.IsInvertible.inverse_apply_eq
      (mfderiv_symm_isInvertible F (F p))).2 ?_
  have hF : ContMDiff I J ∞ F := F.contMDiff
  have hFsymm : ContMDiff J I ∞ F.symm := F.symm.contMDiff
  have h :
      mfderiv I I (F.symm ∘ F) p (X p) =
        mfderiv J I F.symm (F p) ((mfderiv I J F p) (X p)) :=
    mfderiv_comp_apply
      p
      (hFsymm.mdifferentiableAt (by simp))
      (hF.mdifferentiableAt (by simp))
      (X p)
  have hcomp : (⇑F.symm ∘ ⇑F) = id := by
    funext x
    simp
  rw [hcomp, mfderiv_id] at h
  simpa using h

/-- Helper for Proposition 8.19: the pushforward of a smooth vector field along a diffeomorphism
is smooth. -/
theorem contMDiff_pushforward_of_diffeomorph
    (F : M ≃ₘ⟮I, J⟯ N)
    {X : ∀ p : M, TangentSpace I p}
    (hX : ContMDiff I I.tangent (∞ : ℕ∞ω) (T% X)) :
    ContMDiff J J.tangent (∞ : ℕ∞ω) (T% (((F _* X) : ∀ q : N, TangentSpace J q))) := by
  -- Rewrite the pushforward section as the tangent map of `F` applied to `X ∘ F.symm`.
  have hT : ContMDiff I.tangent J.tangent (∞ : ℕ∞ω) (tangentMap I J F) := by
    simpa using F.contMDiff.contMDiff_tangentMap (m := (∞ : ℕ∞ω)) (by simp)
  have hcomp :
      ContMDiff J J.tangent (∞ : ℕ∞ω) ((tangentMap I J F) ∘ (T% X) ∘ F.symm) := by
    simpa [Function.comp_apply] using hT.comp (hX.comp F.symm.contMDiff)
  have hpush :
      (tangentMap I J F) ∘ (T% X) ∘ F.symm =
        (T% (((F _* X) : ∀ q : N, TangentSpace J q))) := by
    funext q
    have hrelated :=
      VectorField.f_related_apply (f_related_pushforward_of_diffeomorph F X) (F.symm q)
    refine Bundle.TotalSpace.ext (F.apply_symm_apply q) ?_
    refine heq_of_eq ?_
    convert hrelated using 1
    simpa using
      congrArg (((F _* X) : ∀ q : N, TangentSpace J q)) (F.apply_symm_apply q).symm
  exact hcomp.congr fun q ↦ (congrFun hpush q).symm

omit [IsManifold I (∞ : ℕ∞ω) M] [IsManifold J (∞ : ℕ∞ω) N] in
/-- Helper for Proposition 8.19: an `F`-related vector field on the target is forced to equal the
canonical pushforward `F _* X`. -/
theorem eq_pushforward_of_f_related
    (F : M ≃ₘ⟮I, J⟯ N)
    {X : ∀ p : M, TangentSpace I p}
    {Y : ∀ q : N, TangentSpace J q}
    (hY : VectorField.f_related F X Y) :
    Y = ((F _* X) : ∀ q : N, TangentSpace J q) := by
  -- Compare the two relatedness formulas at the preimage point `F.symm q`.
  funext q
  have hYq := VectorField.f_related_apply hY (F.symm q)
  have hFq := VectorField.f_related_apply (f_related_pushforward_of_diffeomorph F X) (F.symm q)
  -- The common left-hand side identifies the target values after rewriting `F (F.symm q) = q`.
  rw [← F.apply_symm_apply q]
  exact hYq.symm.trans hFq

/-- Proposition 8.19: if `F : M → N` is a diffeomorphism and `X` is a smooth vector field on `M`,
then there is a unique smooth vector field on `N` that is `F`-related to `X`; canonically, this
vector field is `F _* X`. -/
theorem existsUnique_smooth_f_related_vectorField_of_diffeomorph
    (F : M ≃ₘ⟮I, J⟯ N)
    {X : ∀ p : M, TangentSpace I p}
    (hX : ContMDiff I I.tangent (∞ : ℕ∞ω) (T% X)) :
    ∃! Y : ∀ q : N, TangentSpace J q,
      ContMDiff J J.tangent (∞ : ℕ∞ω) (T% Y) ∧
        VectorField.f_related F X Y := by
  -- Choose the canonical pushforward as the candidate target vector field.
  refine ⟨((F _* X) : ∀ q : N, TangentSpace J q), ?_, ?_⟩
  · -- Existence combines smoothness of the pushforward with its built-in relatedness.
    constructor
    · exact contMDiff_pushforward_of_diffeomorph F hX
    · exact f_related_pushforward_of_diffeomorph F X
  · intro Y hY
    -- Uniqueness depends only on the relatedness equation; smoothness is bookkeeping here.
    exact eq_pushforward_of_f_related F hY.2

end
