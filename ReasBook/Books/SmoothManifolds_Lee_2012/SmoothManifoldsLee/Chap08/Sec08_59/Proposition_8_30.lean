import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_59.Definition_8_59_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Definition_8_57_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology ContDiff Manifold

noncomputable section

section

universe u𝕜 uE uE' uH uH' uM uN

-- Domain sampling pass:
-- * primary domain: smooth vector fields on manifolds and their Lie bracket;
-- * source-facing owner: `VectorField.f_related`;
-- * source-facing derived API for that owner: `f_related_iff_mfderiv_comp_eq`;
-- * core/canonical bracket owner: `VectorField.mlieBracket`, exposed via `⁅X, Y⁆`;
-- * smoothness API for the bracket: `ContMDiff.mlieBracket_vectorField`.
-- Primitive data is only the map `F` and the vector fields `Xᵢ`, `Yᵢ`; smoothness and
-- `f_related` are derived hypotheses, so this file should stay a thin bridge theorem over the
-- existing owners rather than introducing any local wrapper API. In particular, completeness of
-- the source model space belongs to one proof route for pullback naturality, not to the public
-- `f_related` statement itself.

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
  [IsManifold I ∞ M]
  [IsManifold J ∞ N]

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so the API owners
-- were verified directly against the chapter predicate `VectorField.f_related`, its derived
-- characterization `f_related_iff_mfderiv_comp_eq`, mathlib's `VectorField.mlieBracket`, and
-- `ContMDiff.mlieBracket_vectorField`.

/-- Helper for Proposition 8.30: applying `mfderiv% g` after an `F`-related vector field is just
the chain rule plus the defining pointwise relatedness identity. -/
lemma fRelated_mfderivCompEq
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H'']
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
    {K : ModelWithCorners 𝕜 E'' H''} [IsManifold K ∞ P]
    {F : M → N}
    {X : ∀ p : M, TangentSpace I p}
    {Y : ∀ q : N, TangentSpace J q}
    (hXY : VectorField.f_related F X Y) (p : M) {g : N → P}
    (hg : ContMDiffAt J K ∞ g (F p)) :
    mfderiv% (fun x ↦ g (F x)) p (X p) =
      mfderiv% g (F p) (Y (F p)) := by
  -- Differentiate the composite and then substitute the pointwise `F`-related identity.
  calc
    mfderiv% (fun x ↦ g (F x)) p (X p)
        = mfderiv% g (F p) (mfderiv I J F p (X p)) := by
            simpa [Function.comp] using
              (mfderiv_comp_apply (x := p) (g := g)
                (hg.mdifferentiableAt (by simp))
                (hXY.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
                (X p))
    _ = mfderiv% g (F p) (Y (F p)) := by
          rw [VectorField.f_related_apply hXY p]

/-- Helper for Proposition 8.30: if `g` is smooth and `Y` is a smooth vector field, then the
vector-space-valued field `q ↦ mfderiv% g q (Y q)` is smooth at the basepoint. -/
lemma contMDiffAt_mfderiv_applyField
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {g : N → E''}
    {Y : ∀ q : N, TangentSpace J q}
    {p : N}
    (hg : ContMDiffAt J 𝓘(𝕜, E'') ∞ g p)
    (hY : ContMDiffAt J J.tangent ∞ (T% Y) p) :
    ContMDiffAt J 𝓘(𝕜, E'') ∞
      (fun q ↦ NormedSpace.fromTangentSpace (g q) (mfderiv% g q (Y q))) p := by
  -- View `d% g` as a smooth Hom-bundle section and apply it to the smooth tangent section `Y`.
  simpa [mvfderiv] using
    (hg.mfderiv_const (m := ∞) (by simp)).clm_bundle_apply hY

/-- Helper for Proposition 8.30: the preferred chart point lies in the model-validity set
`Set.range J`, so chart-side within-derivative statements can be evaluated there. -/
lemma extChartAt_self_mem_range (p : N) :
    extChartAt J p p ∈ Set.range J := by
  exact extChartAt_target_subset_range (I := J) p (mem_extChartAt_target (I := J) p)

/-- Helper for Proposition 8.30: the manifold Lie bracket acts on a smooth map by the commutator
of the first-order differential operators induced by the vector fields. -/
lemma mfderiv_apply_mlieBracket_eq_commutator
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {g : N → E''}
    {Y₁ Y₂ : ∀ q : N, TangentSpace J q}
    {p : N}
    (hg : ContMDiffAt J 𝓘(𝕜, E'') ∞ g p)
    (hY₁ : ContMDiffAt J J.tangent ∞ (T% Y₁) p)
    (hY₂ : ContMDiffAt J J.tangent ∞ (T% Y₂) p) :
    NormedSpace.fromTangentSpace (g p) (mfderiv% g p (⁅Y₁, Y₂⁆ p)) =
      NormedSpace.fromTangentSpace
          (NormedSpace.fromTangentSpace (g p) (mfderiv% g p (Y₂ p)))
          (mfderiv% (fun q ↦ NormedSpace.fromTangentSpace (g q) (mfderiv% g q (Y₂ q))) p
            (Y₁ p)) -
        NormedSpace.fromTangentSpace
          (NormedSpace.fromTangentSpace (g p) (mfderiv% g p (Y₁ p)))
          (mfderiv% (fun q ↦ NormedSpace.fromTangentSpace (g q) (mfderiv% g q (Y₁ q))) p
            (Y₂ p)) := by
  -- TODO: write the whole proof in one source-chart normal form on `Set.range J`:
  -- first transport `⁅Y₁, Y₂⁆` to `lieBracketWithin` by `mpullbackWithin_mlieBracketWithin`,
  -- then normalize `x ↦ fderivWithin 𝕜 (g ∘ (extChartAt J p).symm) (Set.range J) x (...)`
  -- to the manifold field `q ↦ NormedSpace.fromTangentSpace (g q) (mfderiv% g q (...))`
  -- by an eventual-equality helper near `extChartAt J p p`, and finally apply
  -- `VectorField.fderivWithin_apply_lieBracket`.
  sorry

/-- Proposition 8.30 (Naturality of the Lie Bracket): if `F : M → N` is smooth and the smooth
vector fields `X₁`, `X₂` on `M` are respectively `F`-related to the smooth vector fields `Y₁`,
`Y₂` on `N`, then the Lie bracket `[X₁, X₂]` is `F`-related to the Lie bracket `[Y₁, Y₂]`. -/
theorem f_related_mlieBracket
    {F : M → N}
    {X₁ X₂ : ∀ p : M, TangentSpace I p}
    {Y₁ Y₂ : ∀ q : N, TangentSpace J q}
    (hX₁ : ContMDiff I I.tangent ∞ (T% X₁))
    (hX₂ : ContMDiff I I.tangent ∞ (T% X₂))
    (hY₁ : ContMDiff J J.tangent ∞ (T% Y₁))
    (hY₂ : ContMDiff J J.tangent ∞ (T% Y₂))
    (h₁ : VectorField.f_related F X₁ Y₁)
    (h₂ : VectorField.f_related F X₂ Y₂) :
    VectorField.f_related F ⁅X₁, X₂⁆ ⁅Y₁, Y₂⁆ := by
  -- Route correction: push the target equality through the preferred target chart once, then use
  -- the commutator formula for `mfderiv%` together with the first-order `f_related` chain rule.
  -- TODO: for each `p`, let `ψ := extChartAt J (F p)` and `Bᵢ q := (mfderiv% ψ q (Yᵢ q) : E')`.
  -- Use `mfderiv_apply_mlieBracket_eq_commutator` for `ψ ∘ F` and for `ψ`, use
  -- `contMDiffAt_mfderiv_applyField` to see each `Bᵢ` is smooth at `F p`, rewrite the two
  -- source-side first-order terms to derivatives of `Bᵢ ∘ F` by eventual equality on the chart
  -- source neighborhood, apply `fRelated_mfderivCompEq` twice, and then cancel
  -- `mfderiv% ψ (F p)`.
  sorry

end
