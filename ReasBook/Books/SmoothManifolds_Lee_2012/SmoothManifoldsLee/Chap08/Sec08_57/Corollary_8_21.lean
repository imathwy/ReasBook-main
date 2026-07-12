import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Proposition_8_19
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Proposition_8_16

open scoped ContDiff Manifold

noncomputable section

section

universe uE uE' uH uH' uM uN

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}
  [IsManifold I (∞ : ℕ∞ω) M]
  [IsManifold J (∞ : ℕ∞ω) N]

/-- Corollary 8.21: suppose `F : M → N` is a diffeomorphism and `X` is a vector field on `M`. For
any smooth function `f ∈ C^∞(N)`, the smooth function obtained by applying Lee's
pushforward vector field `F_* X` to `f`, then pulling back along `F`, agrees with the smooth
function obtained by applying `X` to `f ∘ F`. The identity itself does not require a separate
smoothness hypothesis on `X`. -/
theorem pushforward_apply_comp_eq
    (F : M ≃ₘ⟮I, J⟯ N)
    {X : ∀ p : M, TangentSpace I p}
    (f : C^∞⟮J, N; 𝓘(ℝ), ℝ⟯)
    (p : M) :
    mfderiv% f (F p) ((F _* X) (F p)) =
      mfderiv% (f.comp (F : C^∞⟮I, M; J, N⟯)) p (X p) := by
  symm
  simpa using
    (f_related_iff_mfderiv_comp_eq F.contMDiff).1
      (f_related_pushforward_of_diffeomorph F X) p f f.contMDiff.contMDiffAt

end
