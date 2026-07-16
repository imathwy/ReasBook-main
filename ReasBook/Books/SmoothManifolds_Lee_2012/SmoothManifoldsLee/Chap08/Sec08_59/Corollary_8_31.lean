import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Proposition_8_19
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_59.Proposition_8_30

open scoped ContDiff Manifold

noncomputable section

section

universe u𝕜 uE uE' uH uH' uM uN

-- Domain sampling pass:
-- * primary domain: smooth vector fields on manifolds under diffeomorphism pushforward;
-- * relevant owner-style declarations sampled upstream: `VectorField.mpullback`,
--   `VectorField.mpullback_mlieBracket`, and `ContMDiff.mpullback_vectorField`;
-- * bridge/view syntax sampled in the chapter: `F _* X`, expanding to `VectorField.mpullback`
--   along `F.symm`;
-- * derived local surface: this corollary is the pushforward-form restatement of Lie-bracket
--   naturality in the chapter's diffeomorphism-pushforward notation.
-- Primitive data is only the diffeomorphism `F` and the smooth vector fields `X₁`, `X₂`; the
-- pushforward itself is derived from the canonical pullback owner along `F.symm`.

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

/-- Corollary 8.31 (Pushforwards of Lie Brackets): if `F : M ≃ₘ⟮I, J⟯ N` is a diffeomorphism and
`X₁`, `X₂` are smooth vector fields on `M`, then the pushforward of their Lie bracket is the Lie
bracket of their pushforwards. -/
theorem pushforward_mlieBracket
    (F : M ≃ₘ⟮I, J⟯ N)
    {X₁ X₂ : ∀ p : M, TangentSpace I p}
    (hX₁ : ContMDiff I I.tangent (∞ : ℕ∞ω) (T% X₁))
    (hX₂ : ContMDiff I I.tangent (∞ : ℕ∞ω) (T% X₂)) :
    (F _* (⁅X₁, X₂⁆)) = ⁅F _* X₁, F _* X₂⁆ := by
  sorry

end
