import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_59.Definition_8_59_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Proposition_8_16
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_59.Proposition_8_30

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

section

universe u𝕜 uE uE' uH uH' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

-- Semantic sampling pass:
-- * primary domain: smooth vector fields on product manifolds;
-- * core/canonical owner for the Lie bracket: mathlib's `VectorField.mlieBracket`, exposed in
--   Chapter 8 through the source-facing notation `⁅X, Y⁆`;
-- * companion product/smoothness API checked here: `ContMDiff.prodMk`, `contMDiff_prod_iff`,
--   and the product tangent-space identification implicit in
--   `TangentSpace (I.prod J) (p, q)`;
-- * owner choice here: the source-facing product field belongs under `namespace VectorField`,
--   while smoothness and bracket formulas are derived API over that owner.

namespace VectorField

/-- The product vector field on `M × N` with components `X` and `Y`. -/
def prod
    (X : ∀ p : M, TangentSpace I p)
    (Y : ∀ q : N, TangentSpace J q) :
    ∀ r : M × N, TangentSpace (I.prod J) r
  | (p, q) => (X p, Y q)

section

omit [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- Pointwise formula for the product vector field. -/
theorem prod_apply
    (X : ∀ p : M, TangentSpace I p)
    (Y : ∀ q : N, TangentSpace J q)
    (p : M) (q : N) :
    prod X Y (p, q) = (X p, Y q) := rfl

end

attribute [simp] prod_apply

section

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Problem 8-17: the canonical tangent-bundle product equivalence splits the section
of `prod X Y` into the sections of `X` and `Y`. -/
lemma equivTangentBundleProd_prod_apply
    {X : ∀ p : M, TangentSpace I p}
    {Y : ∀ q : N, TangentSpace J q}
    (r : M × N) :
    equivTangentBundleProd I M J N (T% (prod X Y) r) = (T% X r.1, T% Y r.2) := by
  -- Expanding the product section shows that the bundle equivalence just separates components.
  rcases r with ⟨p, q⟩
  rfl

/-- Problem 8-17 (1): if `X` and `Y` are smooth vector fields on `M` and `N`, then their product
vector field on `M × N` is smooth. -/
theorem contMDiff_prod
    {X : ∀ p : M, TangentSpace I p}
    {Y : ∀ q : N, TangentSpace J q}
    (hX : ContMDiff I I.tangent ∞ (T% X))
    (hY : ContMDiff J J.tangent ∞ (T% Y)) :
    ContMDiff (I.prod J) (I.prod J).tangent ∞ (T% (prod X Y)) := by
  let F : M × N → TangentBundle I M × TangentBundle J N := fun r ↦ (T% X r.1, T% Y r.2)
  have hF : ContMDiff (I.prod J) (I.tangent.prod J.tangent) ∞ F := by
    -- Each component section stays smooth after precomposing with the smooth projection.
    simpa [F, Function.comp] using (hX.comp contMDiff_fst).prodMk (hY.comp contMDiff_snd)
  have htransport :
      ContMDiff (I.prod J) (I.prod J).tangent ∞
        ((equivTangentBundleProd I M J N).symm ∘ F) := by
    -- Transport the smooth pair of sections back to the tangent bundle of the product manifold.
    exact
      (contMDiff_equivTangentBundleProd_symm
        (I := I) (I' := J) (M := M) (M' := N)).comp hF
  have hEq : ((equivTangentBundleProd I M J N).symm ∘ F) = T% (prod X Y) := by
    -- The transport formula is certified by the forward bundle equivalence.
    funext r
    apply (equivTangentBundleProd I M J N).injective
    simpa [F, Function.comp] using
      equivTangentBundleProd_prod_apply (I := I) (J := J) (M := M) (N := N)
        (X := X) (Y := Y) r
  simpa [hEq] using htransport

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Problem 8-17: the product field is `Prod.fst`-related to its first component. -/
lemma f_related_fst_prod
    {X : ∀ p : M, TangentSpace I p}
    {Y : ∀ q : N, TangentSpace J q} :
    VectorField.f_related (Prod.fst : M × N → M) (prod X Y) X := by
  constructor
  · -- The first projection of a product manifold is smooth.
    exact contMDiff_fst
  · intro r
    -- Its differential discards the second tangent component.
    rw [mfderiv_fst]
    rcases r with ⟨p, q⟩
    rfl

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- Helper for Problem 8-17: the product field is `Prod.snd`-related to its second component. -/
lemma f_related_snd_prod
    {X : ∀ p : M, TangentSpace I p}
    {Y : ∀ q : N, TangentSpace J q} :
    VectorField.f_related (Prod.snd : M × N → N) (prod X Y) Y := by
  constructor
  · -- The second projection of a product manifold is smooth.
    exact contMDiff_snd
  · intro r
    -- Its differential discards the first tangent component.
    rw [mfderiv_snd]
    rcases r with ⟨p, q⟩
    rfl

end

/-- Problem 8-17 (2): the Lie bracket of product vector fields is the product of the Lie
brackets of the component fields. -/
theorem lie_bracket_prod
    {X₁ X₂ : ∀ p : M, TangentSpace I p}
    {Y₁ Y₂ : ∀ q : N, TangentSpace J q}
    (hX₁ : ContMDiff I I.tangent ∞ (T% X₁))
    (hX₂ : ContMDiff I I.tangent ∞ (T% X₂))
    (hY₁ : ContMDiff J J.tangent ∞ (T% Y₁))
    (hY₂ : ContMDiff J J.tangent ∞ (T% Y₂)) :
    ⁅prod X₁ Y₁, prod X₂ Y₂⁆ = prod ⁅X₁, X₂⁆ ⁅Y₁, Y₂⁆ := by
  -- Route correction: compare the bracket through the two projection maps instead of unfolding the
  -- Lie bracket construction on the product manifold.
  have hprod₁ : ContMDiff (I.prod J) (I.prod J).tangent ∞ (T% (prod X₁ Y₁)) :=
    contMDiff_prod hX₁ hY₁
  have hprod₂ : ContMDiff (I.prod J) (I.prod J).tangent ∞ (T% (prod X₂ Y₂)) :=
    contMDiff_prod hX₂ hY₂
  have hfst :
      VectorField.f_related
        (Prod.fst : M × N → M)
        ⁅prod X₁ Y₁, prod X₂ Y₂⁆
        ⁅X₁, X₂⁆ := by
    -- Naturality of the Lie bracket pushes the product bracket to the first factor.
    exact
      f_related_mlieBracket hprod₁ hprod₂ hX₁ hX₂
        (f_related_fst_prod (I := I) (J := J) (X := X₁) (Y := Y₁))
        (f_related_fst_prod (I := I) (J := J) (X := X₂) (Y := Y₂))
  have hsnd :
      VectorField.f_related
        (Prod.snd : M × N → N)
        ⁅prod X₁ Y₁, prod X₂ Y₂⁆
        ⁅Y₁, Y₂⁆ := by
    -- The same naturality argument pushes to the second factor.
    exact
      f_related_mlieBracket hprod₁ hprod₂ hY₁ hY₂
        (f_related_snd_prod (I := I) (J := J) (X := X₁) (Y := Y₁))
        (f_related_snd_prod (I := I) (J := J) (X := X₂) (Y := Y₂))
  funext r
  -- Equality in the product tangent space is determined by its two coordinates.
  apply Prod.ext
  · have hfst_r := VectorField.f_related_apply hfst r
    rw [mfderiv_fst] at hfst_r
    simpa using hfst_r
  · have hsnd_r := VectorField.f_related_apply hsnd r
    rw [mfderiv_snd] at hsnd_r
    simpa using hsnd_r

end VectorField

end
