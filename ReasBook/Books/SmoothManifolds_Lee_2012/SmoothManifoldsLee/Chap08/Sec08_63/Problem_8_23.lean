import Mathlib.Algebra.Lie.Prod
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_60.Notation_8_60_extra_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff

-- Domain sampling pass:
-- * source-facing split: Problem 8-23 has a product Lie-algebra recall in part (1) and a
--   tangent-space product identification for Lie groups in part (2);
-- * core/canonical owners checked before refinement:
--   `LieAlgebra.Prod.instLieRing`, `LieAlgebra.Prod.instLieAlgebra`,
--   `LieAlgebra.Prod.bracket_apply`, `equivTangentBundleProd`, `GroupLieAlgebra`, and `LieEquiv`;
-- * primitive data for part (2) is only the tangent-space splitting at the identity, while the
--   linear and Lie-algebra equivalences are derived bridge/view API from that splitting.

/- Problem 8-23 (1): mathlib already owns the product Lie-ring and Lie-algebra structure together
with the componentwise bracket formula, so the source-faithful surface here is direct recall of
those canonical declarations. -/
recall LieAlgebra.Prod.instLieRing
recall LieAlgebra.Prod.instLieAlgebra
recall LieAlgebra.Prod.bracket_apply

section ProductTangentSpaces

universe u𝕜 uEG uHG uG uEH uHH uH

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]

namespace GroupLieAlgebra

/-- The forward map from `Lie(G × H)` to `Lie(G) × Lie(H)` induced by the tangent-bundle product
equivalence at the identity. -/
noncomputable def prodToProd
    (v : GroupLieAlgebra (I.prod J) (G × H)) :
    GroupLieAlgebra I G × GroupLieAlgebra J H :=
  let p := equivTangentBundleProd I G J H ⟨((1 : G), (1 : H)), v⟩
  (p.1.2, p.2.2)

/-- The inverse map from `Lie(G) × Lie(H)` back to `Lie(G × H)` induced by the tangent-bundle
product equivalence at the identity. -/
noncomputable def prodFromProd
    (v : GroupLieAlgebra I G × GroupLieAlgebra J H) :
    GroupLieAlgebra (I.prod J) (G × H) :=
  ((equivTangentBundleProd I G J H).symm (⟨(1 : G), v.1⟩, ⟨(1 : H), v.2⟩)).2

/-- The forward tangent-space map for `Lie(G × H)` is additive. -/
theorem prodToProd_add
    (v w : GroupLieAlgebra (I.prod J) (G × H)) :
    prodToProd (v + w) = prodToProd v + prodToProd w := by
  -- The product tangent-space equivalence is fiberwise linear, so addition splits componentwise.
  ext <;> rfl

/-- The forward tangent-space map for `Lie(G × H)` commutes with scalar multiplication. -/
theorem prodToProd_smul
    (c : 𝕜) (v : GroupLieAlgebra (I.prod J) (G × H)) :
    prodToProd (c • v) = c • prodToProd v := by
  -- The same normalization shows that the tangent-space splitting is `𝕜`-linear.
  ext <;> rfl

/-- The forward and inverse tangent-space maps are left inverses at the identity. -/
theorem prod_left_inv
    (v : GroupLieAlgebra (I.prod J) (G × H)) :
    prodFromProd (prodToProd v) = v := by
  -- Applying the explicit inverse of `equivTangentBundleProd` recovers the original tangent vector.
  simp [prodToProd, prodFromProd]

/-- The forward and inverse tangent-space maps are right inverses at the identity. -/
theorem prod_right_inv
    (v : GroupLieAlgebra I G × GroupLieAlgebra J H) :
    prodToProd (prodFromProd v) = v := by
  -- The explicit product decomposition at the identity is two-sided.
  simp [prodToProd, prodFromProd]

/-- The identity tangent-space splitting of a product Lie group is a linear equivalence. -/
noncomputable def prodLinearEquiv :
    GroupLieAlgebra (I.prod J) (G × H) ≃ₗ[𝕜] GroupLieAlgebra I G × GroupLieAlgebra J H where
  toFun := prodToProd
  invFun := prodFromProd
  map_add' := prodToProd_add
  map_smul' := prodToProd_smul
  left_inv := prod_left_inv
  right_inv := prod_right_inv

end GroupLieAlgebra

end ProductTangentSpaces

section ProductLieGroups

universe u𝕜 uEG uHG uG uEH uHH uH

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [LieGroup I (minSmoothness 𝕜 3) G] [LieGroup J (minSmoothness 𝕜 3) H]

namespace ContinuousLinearMap

/-- Helper for Problem 8-23: the inverse of a product of invertible continuous linear maps acts
componentwise. -/
lemma prodMap_inverse_apply
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {f : E₁ →L[𝕜] F₁} {g : E₂ →L[𝕜] F₂}
    (hf : f.IsInvertible) (hg : g.IsInvertible) (u : F₁ × F₂) :
    (f.prodMap g).inverse u = (f.inverse u.1, g.inverse u.2) := by
  -- Reduce to the product of genuine continuous linear equivalences.
  rcases hf with ⟨ef, rfl⟩
  rcases hg with ⟨eg, rfl⟩
  -- The inverse of the product equivalence is the product of the inverses.
  change (ef.prodCongr eg).symm u = (ef.symm u.1, eg.symm u.2)
  rfl

end ContinuousLinearMap

namespace VectorField

/-- Helper for Problem 8-23: the product vector field with component fields on the two factors. -/
def prod
    (X : ∀ p : G, TangentSpace I p)
    (Y : ∀ q : H, TangentSpace J q) :
    ∀ r : G × H, TangentSpace (I.prod J) r
  | (g, h) => (X g, Y h)

/-- Helper for Problem 8-23: the vector-space Lie bracket on a product set is computed
componentwise. -/
lemma lieBracketWithin_prod_apply
    {V₁ V₂ : EG → EG} {W₁ W₂ : EH → EH}
    {s : Set EG} {t : Set EH} {x : EG} {y : EH}
    (hV₁ : DifferentiableWithinAt 𝕜 V₁ s x) (hV₂ : DifferentiableWithinAt 𝕜 V₂ s x)
    (hW₁ : DifferentiableWithinAt 𝕜 W₁ t y) (hW₂ : DifferentiableWithinAt 𝕜 W₂ t y)
    (hs : UniqueDiffWithinAt 𝕜 s x) (ht : UniqueDiffWithinAt 𝕜 t y) :
    lieBracketWithin 𝕜 (fun p : EG × EH ↦ (V₁ p.1, W₁ p.2))
      (fun p ↦ (V₂ p.1, W₂ p.2)) (s ×ˢ t) (x, y) =
      (lieBracketWithin 𝕜 V₁ V₂ s x, lieBracketWithin 𝕜 W₁ W₂ t y) := by
  -- Expand the product Lie bracket to derivatives on the product model space.
  rw [VectorField.lieBracketWithin_eq]
  have hV₁' : HasFDerivWithinAt V₁ (fderivWithin 𝕜 V₁ s x) (Prod.fst '' (s ×ˢ t)) x :=
    hV₁.hasFDerivWithinAt.mono <| by
      intro x' hx'
      rcases hx' with ⟨p, hp, rfl⟩
      exact hp.1
  have hV₂' : HasFDerivWithinAt V₂ (fderivWithin 𝕜 V₂ s x) (Prod.fst '' (s ×ˢ t)) x :=
    hV₂.hasFDerivWithinAt.mono <| by
      intro x' hx'
      rcases hx' with ⟨p, hp, rfl⟩
      exact hp.1
  have hW₁' : HasFDerivWithinAt W₁ (fderivWithin 𝕜 W₁ t y) (Prod.snd '' (s ×ˢ t)) y :=
    hW₁.hasFDerivWithinAt.mono <| by
      intro y' hy'
      rcases hy' with ⟨p, hp, rfl⟩
      exact hp.2
  have hW₂' : HasFDerivWithinAt W₂ (fderivWithin 𝕜 W₂ t y) (Prod.snd '' (s ×ˢ t)) y :=
    hW₂.hasFDerivWithinAt.mono <| by
      intro y' hy'
      rcases hy' with ⟨p, hp, rfl⟩
      exact hp.2
  have hProd₂ :
      HasFDerivWithinAt (fun p : EG × EH ↦ (V₂ p.1, W₂ p.2))
        ((fderivWithin 𝕜 V₂ s x).prodMap (fderivWithin 𝕜 W₂ t y)) (s ×ˢ t) (x, y) :=
    by simpa using HasFDerivWithinAt.prodMap (p := (x, y)) hV₂' hW₂'
  have hProd₁ :
      HasFDerivWithinAt (fun p : EG × EH ↦ (V₁ p.1, W₁ p.2))
        ((fderivWithin 𝕜 V₁ s x).prodMap (fderivWithin 𝕜 W₁ t y)) (s ×ˢ t) (x, y) :=
    by simpa using HasFDerivWithinAt.prodMap (p := (x, y)) hV₁' hW₁'
  -- Rewrite the product derivative and simplify componentwise.
  simp [VectorField.lieBracketWithin_eq, hProd₂.fderivWithin (hs.prod ht),
    hProd₁.fderivWithin (hs.prod ht)]

/-- Helper for Problem 8-23: in product coordinates at `((1, 1))`, pulling back a split vector
field through the product chart splits into the pullbacks of the component fields. -/
lemma mpullbackWithin_prod_apply_one
    (X : ∀ p : G, TangentSpace I p)
    (Y : ∀ q : H, TangentSpace J q)
    {z : EG × EH}
    (hz : z ∈ (extChartAt (I.prod J) ((1 : G), (1 : H))).target) :
    VectorField.mpullbackWithin 𝓘(𝕜, EG × EH) (I.prod J)
        (extChartAt (I.prod J) ((1 : G), (1 : H))).symm (prod X Y) (Set.range (I.prod J)) z =
      (VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm X (Set.range I) z.1,
        VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm Y (Set.range J) z.2) := by
  -- Route correction: keep the full target-neighborhood statement, since the Lie-bracket proof
  -- uses eventual equality near the chart center rather than only equality at the center.
  have hz' : z ∈ (extChartAt I (1 : G)).target ×ˢ (extChartAt J (1 : H)).target := by
    -- Rewrite the product chart as the product of the factor charts.
    rw [extChartAt_prod] at hz
    simpa using hz
  have hz₁ : z.1 ∈ (extChartAt I (1 : G)).target := hz'.1
  have hz₂ : z.2 ∈ (extChartAt J (1 : H)).target := hz'.2
  have hmfderiv :
      mfderivWithin 𝓘(𝕜, EG × EH) (I.prod J)
          (extChartAt (I.prod J) ((1 : G), (1 : H))).symm (Set.range (I.prod J)) z =
        (mfderivWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm (Set.range I) z.1).prodMap
          (mfderivWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm (Set.range J) z.2) := by
    -- The derivative of the product chart inverse splits into the derivatives on the two factors.
    rw [extChartAt_prod]
    simpa using
      (mfderivWithin_prodMap
        (I := 𝓘(𝕜, EG)) (I' := 𝓘(𝕜, EH)) (J := I) (J' := J)
        (s := Set.range I) (t := Set.range J)
        (f := (extChartAt I (1 : G)).symm) (g := (extChartAt J (1 : H)).symm)
        (p := z)
        (mdifferentiableWithinAt_extChartAt_symm hz₁)
        (mdifferentiableWithinAt_extChartAt_symm hz₂)
        I.uniqueMDiffOn.uniqueMDiffWithinAt_image
        J.uniqueMDiffOn.uniqueMDiffWithinAt_image)
  -- Evaluate the inverse derivative on the split tangent vector and simplify each factor.
  let A : EG →L[𝕜] TangentSpace I ((extChartAt I (1 : G)).symm z.1) :=
    mfderivWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm (Set.range I) z.1
  let B : EH →L[𝕜] TangentSpace J ((extChartAt J (1 : H)).symm z.2) :=
    mfderivWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm (Set.range J) z.2
  have hA : A.IsInvertible := by
    simpa [A] using
      (isInvertible_mfderivWithin_extChartAt_symm hz₁ :
        (mfderivWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm (Set.range I) z.1).IsInvertible)
  have hB : B.IsInvertible := by
    simpa [B] using
      (isInvertible_mfderivWithin_extChartAt_symm hz₂ :
        (mfderivWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm (Set.range J) z.2).IsInvertible)
  rw [VectorField.mpullbackWithin_apply, VectorField.mpullbackWithin_apply,
    VectorField.mpullbackWithin_apply, hmfderiv]
  change (A.prodMap B).inverse
      (X ((extChartAt I (1 : G)).symm z.1), Y ((extChartAt J (1 : H)).symm z.2)) =
    (A.inverse (X ((extChartAt I (1 : G)).symm z.1)),
      B.inverse (Y ((extChartAt J (1 : H)).symm z.2)))
  simpa [A, B, VectorField.prod, extChartAt_prod] using
    (ContinuousLinearMap.prodMap_inverse_apply
      (E₁ := EG) (E₂ := EH) hA hB
      (X ((extChartAt I (1 : G)).symm z.1), Y ((extChartAt J (1 : H)).symm z.2)))

end VectorField

namespace GroupLieAlgebra

/-- Helper for Problem 8-23: evaluating the Lie bracket of split vector fields at the identity
pair matches the pair of Lie brackets on the two factors. -/
theorem prodToProd_mlieBracket_prod_apply_one
    {X₁ X₂ : ∀ p : G, TangentSpace I p}
    {Y₁ Y₂ : ∀ q : H, TangentSpace J q}
    (hX₁ : MDiffAt (T% X₁) (1 : G)) (hX₂ : MDiffAt (T% X₂) (1 : G))
    (hY₁ : MDiffAt (T% Y₁) (1 : H)) (hY₂ : MDiffAt (T% Y₂) (1 : H)) :
    prodToProd
      (VectorField.mlieBracket (I.prod J) (VectorField.prod X₁ Y₁) (VectorField.prod X₂ Y₂)
        ((1 : G), (1 : H))) =
      (VectorField.mlieBracket I X₁ X₂ (1 : G), VectorField.mlieBracket J Y₁ Y₂ (1 : H)) := by
  -- Route correction: reuse the stable neighborhood-equality argument from the earlier product
  -- vector-field proof, since the bracket depends on derivatives near the chart center.
  let r : G × H := ((1 : G), (1 : H))
  let φ := extChartAt (I.prod J) r
  let φG := extChartAt I (1 : G)
  let φH := extChartAt J (1 : H)
  let U₁ : EG → EG := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φG.symm X₁ (Set.range I)
  let U₂ : EG → EG := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φG.symm X₂ (Set.range I)
  let V₁ : EH → EH := VectorField.mpullbackWithin 𝓘(𝕜, EH) J φH.symm Y₁ (Set.range J)
  let V₂ : EH → EH := VectorField.mpullbackWithin 𝓘(𝕜, EH) J φH.symm Y₂ (Set.range J)
  let W₁ : EG × EH → EG × EH :=
    VectorField.mpullbackWithin 𝓘(𝕜, EG × EH) (I.prod J) φ.symm
      (VectorField.prod X₁ Y₁) (Set.range (I.prod J))
  let W₂ : EG × EH → EG × EH :=
    VectorField.mpullbackWithin 𝓘(𝕜, EG × EH) (I.prod J) φ.symm
      (VectorField.prod X₂ Y₂) (Set.range (I.prod J))
  have hRange : Set.range (I.prod J) = Set.range I ×ˢ Set.range J := by
    simpa using (Set.range_prodMap (f := I) (g := J))
  have hX₁u : MDiffAt[Set.univ] (T% X₁) (1 : G) := hX₁.mdifferentiableWithinAt (s := Set.univ)
  have hX₂u : MDiffAt[Set.univ] (T% X₂) (1 : G) := hX₂.mdifferentiableWithinAt (s := Set.univ)
  have hY₁u : MDiffAt[Set.univ] (T% Y₁) (1 : H) := hY₁.mdifferentiableWithinAt (s := Set.univ)
  have hY₂u : MDiffAt[Set.univ] (T% Y₂) (1 : H) := hY₂.mdifferentiableWithinAt (s := Set.univ)
  have hW₁ :
      W₁ =ᶠ[nhdsWithin (φ r) (Set.range (I.prod J))] fun z ↦ (U₁ z.1, V₁ z.2) := by
    -- On the target of the product chart, the pullback of a split field stays split.
    refine Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin r) ?_
    intro z hz
    simpa [W₁, U₁, V₁, φ, φG, φH, r] using
      VectorField.mpullbackWithin_prod_apply_one (I := I) (J := J) (X := X₁) (Y := Y₁) hz
  have hW₂ :
      W₂ =ᶠ[nhdsWithin (φ r) (Set.range (I.prod J))] fun z ↦ (U₂ z.1, V₂ z.2) := by
    -- The same chart-level splitting applies to the second field.
    refine Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin r) ?_
    intro z hz
    simpa [W₂, U₂, V₂, φ, φG, φH, r] using
      VectorField.mpullbackWithin_prod_apply_one (I := I) (J := J) (X := X₂) (Y := Y₂) hz
  have hU₁ : DifferentiableWithinAt 𝕜 U₁ (Set.range I) (φG (1 : G)) := by
    -- The chart pullback of the first `G`-field is differentiable on the model range.
    simpa [U₁, φG] using hX₁u.differentiableWithinAt_mpullbackWithin_vectorField
  have hU₂ : DifferentiableWithinAt 𝕜 U₂ (Set.range I) (φG (1 : G)) := by
    -- The same argument handles the second `G`-field.
    simpa [U₂, φG] using hX₂u.differentiableWithinAt_mpullbackWithin_vectorField
  have hV₁ : DifferentiableWithinAt 𝕜 V₁ (Set.range J) (φH (1 : H)) := by
    -- And likewise for the first `H`-field.
    simpa [V₁, φH] using hY₁u.differentiableWithinAt_mpullbackWithin_vectorField
  have hV₂ : DifferentiableWithinAt 𝕜 V₂ (Set.range J) (φH (1 : H)) := by
    -- The second `H`-field satisfies the same pullback differentiability statement.
    simpa [V₂, φH] using hY₂u.differentiableWithinAt_mpullbackWithin_vectorField
  have hBracket :
      VectorField.lieBracketWithin 𝕜 W₁ W₂ (Set.range (I.prod J)) (φ r) =
        (VectorField.lieBracketWithin 𝕜 U₁ U₂ (Set.range I) (φG (1 : G)),
          VectorField.lieBracketWithin 𝕜 V₁ V₂ (Set.range J) (φH (1 : H))) := by
    -- First replace the product pullbacks by their split forms near the chart center.
    have hφr : φ r ∈ Set.range (I.prod J) := by
      exact extChartAt_target_subset_range r (mem_extChartAt_target r)
    rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hW₁ hW₂ hφr]
    -- Then compute the vector-space bracket componentwise.
    rw [hRange]
    simpa [φ, φG, φH, r, extChartAt_prod] using
      (VectorField.lieBracketWithin_prod_apply (𝕜 := 𝕜) (s := Set.range I) (t := Set.range J)
        (x := φG (1 : G)) (y := φH (1 : H)) hU₁ hU₂ hV₁ hV₂
        (I.uniqueDiffOn.uniqueDiffWithinAt_image) (J.uniqueDiffOn.uniqueDiffWithinAt_image))
  have hmfderiv :
      mfderiv (I := I.prod J) (I' := 𝓘(𝕜, EG × EH)) (fun p : G × H ↦ φ p) r =
        (mfderiv (I := I) (I' := 𝓘(𝕜, EG)) (fun g : G ↦ φG g) (1 : G)).prodMap
          (mfderiv (I := J) (I' := 𝓘(𝕜, EH)) (fun h : H ↦ φH h) (1 : H)) := by
    -- The derivative of the preferred product chart is the product of the factor derivatives.
    rw [extChartAt_prod]
    simpa [φ, φG, φH, r] using
      (mfderiv_prodMap
        (I := I) (I' := J) (J := 𝓘(𝕜, EG)) (J' := 𝓘(𝕜, EH))
        (f := φG) (g := φH) (p := r)
        (mdifferentiableAt_extChartAt (I := I) (x := (1 : G)))
        (mdifferentiableAt_extChartAt (I := J) (x := (1 : H))))
  have hprod :
      VectorField.mlieBracket (I.prod J) (VectorField.prod X₁ Y₁) (VectorField.prod X₂ Y₂) r =
        (VectorField.mlieBracket I X₁ X₂ (1 : G), VectorField.mlieBracket J Y₁ Y₂ (1 : H)) := by
    -- Rewrite the manifold bracket by the chart pullback formulas and split the inverse
    -- derivative into the two factor derivatives.
    simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply, Set.preimage_univ,
      Set.univ_inter, φ, φG, φH, r] at hBracket ⊢
    rw [hBracket, hmfderiv, ContinuousLinearMap.prodMap_inverse_apply
      (isInvertible_mfderiv_extChartAt (I := I) (x := (1 : G)) (y := (1 : G))
        (mem_extChartAt_source (1 : G)))
      (isInvertible_mfderiv_extChartAt (I := J) (x := (1 : H)) (y := (1 : H))
        (mem_extChartAt_source (1 : H)))]
    rfl
  -- Finally, `prodToProd` just reads off the two tangent-space coordinates at the identity pair.
  simpa [GroupLieAlgebra.prodToProd, r] using hprod

/-- Helper for Problem 8-23: the invariant vector field on `G × H` splits into the invariant
fields of the two identity components. -/
theorem mulInvariantVectorField_prod_apply
    (v : GroupLieAlgebra (I.prod J) (G × H)) (g : G) (h : H) :
    vᴸ (g, h) =
      VectorField.prod (((prodToProd v).1)ᴸ) (((prodToProd v).2)ᴸ) (g, h) := by
  -- Rewrite left multiplication on the product group as the product of left multiplications.
  have hMinSmooth : minSmoothness 𝕜 3 ≠ 0 :=
    lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hContG : ContMDiffAt I I (minSmoothness 𝕜 3) (g * ·) (1 : G) := by
    simpa using contMDiffAt_mul_left (I := I) (n := minSmoothness 𝕜 3) (a := g) (b := (1 : G))
  have hContH : ContMDiffAt J J (minSmoothness 𝕜 3) (h * ·) (1 : H) := by
    simpa using contMDiffAt_mul_left (I := J) (n := minSmoothness 𝕜 3) (a := h) (b := (1 : H))
  have hmdiffG : MDiffAt (g * ·) (1 : G) := hContG.mdifferentiableAt hMinSmooth
  have hmdiffH : MDiffAt (h * ·) (1 : H) := hContH.mdifferentiableAt hMinSmooth
  have hmul :
      (fun p : G × H ↦ (g, h) * p) = Prod.map (g * ·) (h * ·) := by
    ext p <;> rcases p with ⟨g', h'⟩ <;> rfl
  -- The derivative of `Prod.map` splits into the derivatives on each factor.
  rw [mulInvariantVectorField, hmul, mfderiv_prodMap hmdiffG hmdiffH]
  -- Unfold the tangent-space splitting at the identity and identify each factor field.
  rfl

/-- Helper for Problem 8-23: package the pointwise product formula as an equality of vector
fields. -/
theorem mulInvariantVectorField_prod
    (v : GroupLieAlgebra (I.prod J) (G × H)) :
    vᴸ = VectorField.prod (((prodToProd v).1)ᴸ) (((prodToProd v).2)ᴸ) := by
  -- The pointwise formula is the stable rewrite used in the bracket computation.
  funext p
  rcases p with ⟨g, h⟩
  simpa using mulInvariantVectorField_prod_apply (v := v) g h

/-- Helper for Problem 8-23: after splitting invariant vector fields on `G × H`, the Lie bracket
also splits into the component Lie brackets. -/
theorem prodToProd_bracket
    (v w : GroupLieAlgebra (I.prod J) (G × H)) :
    prodToProd ⁅v, w⁆ = ⁅prodToProd v, prodToProd w⁆ := by
  -- Route correction: compute the bracket only at the identity pair, where the Lie algebra lives.
  rw [GroupLieAlgebra.bracket_def, mulInvariantVectorField_prod, mulInvariantVectorField_prod]
  -- The chart-level product formula turns the product bracket into the pair of factor brackets.
  simpa [GroupLieAlgebra.bracket_def] using
    prodToProd_mlieBracket_prod_apply_one
      (I := I) (J := J)
      (X₁ := ((prodToProd v).1)ᴸ) (X₂ := ((prodToProd w).1)ᴸ)
      (Y₁ := ((prodToProd v).2)ᴸ) (Y₂ := ((prodToProd w).2)ᴸ)
      (mdifferentiableAt_mulInvariantVectorField ((prodToProd v).1))
      (mdifferentiableAt_mulInvariantVectorField ((prodToProd w).1))
      (mdifferentiableAt_mulInvariantVectorField ((prodToProd v).2))
      (mdifferentiableAt_mulInvariantVectorField ((prodToProd w).2))

/-- The product splitting of `Lie(G × H)` preserves the Lie bracket. -/
theorem prodLinearEquiv_map_lie
    (v w : GroupLieAlgebra (I.prod J) (G × H)) :
    prodLinearEquiv ⁅v, w⁆ = ⁅prodLinearEquiv v, prodLinearEquiv w⁆ := by
  -- The bracket statement for `prodLinearEquiv` is just the normalized `prodToProd` statement.
  simpa [prodLinearEquiv] using prodToProd_bracket (v := v) (w := w)

/-- Problem 8-23 (2): the Lie algebra of a product Lie group is canonically isomorphic to the
direct sum of the Lie algebras of its factors. -/
noncomputable def prodLieEquiv :
    GroupLieAlgebra (I.prod J) (G × H) ≃ₗ⁅𝕜⁆ GroupLieAlgebra I G × GroupLieAlgebra J H where
  toFun := prodLinearEquiv
  invFun := prodLinearEquiv.symm
  map_add' := fun x y ↦
    prodLinearEquiv.map_add x y
  map_smul' := fun c x ↦
    prodLinearEquiv.map_smul c x
  map_lie' := fun {x y} ↦
    prodLinearEquiv_map_lie x y
  left_inv := fun x ↦
    prodLinearEquiv.left_inv x
  right_inv := fun x ↦
    prodLinearEquiv.right_inv x

/-- The product Lie algebra equivalence acts by the tangent-space splitting at the identity. -/
theorem prodLieEquiv_apply
    (v : GroupLieAlgebra (I.prod J) (G × H)) :
    prodLieEquiv v = prodToProd v := by
  -- The `LieEquiv` uses `prodLinearEquiv` as its underlying linear equivalence.
  rfl

end GroupLieAlgebra

end ProductLieGroups
