import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_16_4
import StacksProject_2024.stacks_project.Chap13.Lemma_13_19_11
import StacksProject_2024.stacks_project.Chap13.Lemma_13_34_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_34_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped ZeroObject
open DerivedCategory
open DerivedCategory.TStructure

universe v u

namespace CategoryTheory

section

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
  [HasCountableProducts 𝒜] [CountableAB4Star 𝒜] [EnoughInjectives 𝒜]

local instance isInjective_containsZero : (isInjective 𝒜).ContainsZero where
  exists_zero := ⟨0, Limits.isZero_zero 𝒜, inferInstance⟩

local instance isInjective_hasMonoEmbedding : HasMonoEmbedding (isInjective 𝒜) where
  exists_mono X := ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩

local instance isInjective_isClosedUnderFiniteProducts :
    (isInjective 𝒜).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J := by
    refine ⟨?_⟩
    intro X hX
    rcases hX with ⟨hX⟩
    let f : J → 𝒜 := fun j ↦ hX.diag.obj (Discrete.mk j)
    let _ : ∀ j : J, Injective (f j) := fun j ↦ hX.prop_diag_obj (Discrete.mk j)
    let _ : Injective (∏ᶜ f) := inferInstance
    let e : ∏ᶜ f ≅ X :=
      Pi.isoLimit hX.diag ≪≫ (hX.isLimit.conePointUniqueUpToIso (limit.isLimit hX.diag)).symm
    exact Injective.of_iso e inferInstance

/- Domain-style sampling for Lemma 13.34.7:
- primary domain: K-injective resolutions of cochain complexes in an abelian category with enough
  injectives and exact countable products;
- sampled owner declarations:
  `CountableAB4Star`,
  `CountableAB4Star.ofShape`,
  `CountableAB4Star.of_hasExactLimitsOfShape_nat`,
  `CategoryTheory.isInjective`,
  `LowerTruncationResolutionSystem`,
  `LowerTruncationResolutionSystem.intoLimit`,
  `isKInjective_lowerTruncationResolutionSystemLimit`,
  `lowerTruncationResolutionLimit_quasiIso_iff_isIso_derivedComparison`;
- best owner abstraction: for the exact-product hypothesis, the source-facing owner is
  `CountableAB4Star 𝒜`; `HasExactLimitsOfShape (Discrete ℕ) 𝒜` is only a bridge recovered from it
  by `CountableAB4Star.ofShape ℕ`. For the resolution data, the canonical map is `S.intoLimit`
  from a chosen lower truncation resolution system `S` to its inverse-limit complex; the
  source-facing theorem should expose only the resulting K-injective complex and quasi-isomorphism,
  not the auxiliary resolution-system data;
- primitive-vs-derived split:
  primitive data: the source complex `K` and the ambient hypotheses `EnoughInjectives` plus
    exact countable products, canonically expressed by `[HasCountableProducts 𝒜]` and
    `[CountableAB4Star 𝒜]`;
  derived API: the chosen lower truncation resolution system, its limit complex `limit S.diagram`,
  the K-injectivity theorem for that limit, and the canonical map `S.intoLimit`.

Source/core/bridge triage:
- `source-facing`: existence of a quasi-isomorphism from `K^•` to a K-injective complex;
- `core/canonical`: `CountableAB4Star 𝒜` for exact countable products, and
  `LowerTruncationResolutionSystem.intoLimit` together with
  `isKInjective_lowerTruncationResolutionSystemLimit` for the resolution construction;
- `bridge/view`: `CountableAB4Star.ofShape ℕ` as the local bridge to
  `HasExactLimitsOfShape (Discrete ℕ) 𝒜`, and the quasi-isomorphism claim for `S.intoLimit`,
  reduced in Lemma 13.34.6 to the corresponding derived-limit comparison statement. -/

-- Proof sketch: choose a lower truncation resolution system by injective objects from
-- `exists_lowerTruncationResolutionSystem`, form its inverse-limit complex, and use
-- `isKInjective_lowerTruncationResolutionSystemLimit` to see that the target is K-injective.
-- Lemma 13.34.6 reduces the quasi-isomorphism claim to showing that
-- `K ⟶ R lim_n τ_{\ge -(n + 1)} K` is an isomorphism in the derived category, which follows from
-- the Milnor triangle together with exactness of countable products, used through the canonical
-- owner `[CountableAB4Star 𝒜]` as in Lemma 13.34.2.
/-- Helper for Lemma 13.34.7: the canonical maps from `K^•` to its shifted lower truncation
stages form a cone over the shifted lower truncation tower in the derived category. -/
lemma derivedLowerTruncationToStage_comp_transition
    (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    derivedLowerTruncationToStage K (n + 1) ≫
        (derivedLowerTruncationTower K).transitionMap (Nat.le_succ n) =
      derivedLowerTruncationToStage K n := by
  sorry

/-- Helper for Lemma 13.34.7: the canonical cone map from `K^•` to the Milnor product object is
annihilated by the Milnor difference map. -/
lemma lower_truncation_product_cone_comp_difference_zero
    (K : CochainComplex 𝒜 ℤ)
    [HasProduct (inverseSystemFamily (derivedLowerTruncationTower K))] :
    Pi.lift (fun n ↦ derivedLowerTruncationToStage K n) ≫
        derivedLimitDifferenceMap (derivedLowerTruncationTower K) =
      0 := by
  sorry

/-- Helper for Lemma 13.34.7: any chosen Milnor-model of the shifted lower truncation tower
admits a comparison map from `K^•` whose stage projections recover the canonical truncation maps.
-/
lemma exists_lowerTruncationDerivedLimitComparison_of_isDerivedLimit
    (K : CochainComplex 𝒜 ℤ) {L : DerivedCategory 𝒜}
    (hL : IsDerivedLimit (derivedLowerTruncationTower K) L) :
    ∃ c : Q.obj K ⟶ L, IsLowerTruncationDerivedLimitComparison K L c := by
  sorry

/-- Helper for Lemma 13.34.7: the degree-`p` cohomology map induced by the canonical truncation
projection `X ⟶ τ_{\ge p} X` is an isomorphism. -/
lemma homology_map_truncGEπ_isIso
    (X : DerivedCategory 𝒜) (p : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 p).map ((t.truncGEπ p).app X)) := by
  sorry

/-- Helper for Lemma 13.34.7: once the truncation bound lies below degree `p`, the canonical map
`K^• ⟶ τ_{\ge -(m + 1)} K^•` induces an isomorphism on `H^p`. -/
lemma homology_map_derivedLowerTruncationToStage_isIso
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) (m : ℕ)
    (hm : -(((m + 1 : ℕ)) : ℤ) ≤ p) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 p).map (derivedLowerTruncationToStage K m)) := by
  sorry

/-- Helper for Lemma 13.34.7: in stable degrees, the cohomology transition map between adjacent
shifted lower truncation stages is an isomorphism. -/
lemma lower_truncation_transition_homology_isIso
    (K : CochainComplex 𝒜 ℤ) (q : ℤ) (n : ℕ)
    (hq : -(((n + 1 : ℕ)) : ℤ) ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 q).map (Q.map (lowerTruncationStep K n))) := by
  let H := DerivedCategory.homologyFunctor 𝒜
  have hq' : -((((n + 1) + 1 : ℕ)) : ℤ) ≤ q := by
    omega
  have hstage_succ :
      IsIso ((H q).map (derivedLowerTruncationToStage K (n + 1))) :=
    homology_map_derivedLowerTruncationToStage_isIso (𝒜 := 𝒜) K q (n + 1) hq'
  have hstage :
      IsIso ((H q).map (derivedLowerTruncationToStage K n)) :=
    homology_map_derivedLowerTruncationToStage_isIso (𝒜 := 𝒜) K q n hq
  have hcomp :
      (H q).map (derivedLowerTruncationToStage K (n + 1)) ≫
          (H q).map (Q.map (lowerTruncationStep K n)) =
        (H q).map (derivedLowerTruncationToStage K n) := by
    -- Proof comment: rewrite the tower transition to the concrete truncation step and then map
    -- the canonical stage-compatibility identity on the nose.
    simpa [Functor.map_comp, derivedLowerTruncationTower, lowerTruncationDiagram,
      SequentialInverseSystem.transitionMap] using
      congrArg ((H q).map) (derivedLowerTruncationToStage_comp_transition (𝒜 := 𝒜) K n)
  have hcompIso :
      IsIso
        (((H q).map (derivedLowerTruncationToStage K (n + 1))) ≫
          (H q).map (Q.map (lowerTruncationStep K n))) := by
    rw [hcomp]
    exact hstage
  -- Proof comment: two-out-of-three transfers invertibility from the stable stage maps to the
  -- transition map on cohomology.
  let _ : IsIso ((H q).map (derivedLowerTruncationToStage K (n + 1))) := hstage_succ
  let _ :
      IsIso
        (((H q).map (derivedLowerTruncationToStage K (n + 1))) ≫
          (H q).map (Q.map (lowerTruncationStep K n))) := hcompIso
  exact
    IsIso.of_isIso_comp_left
      ((H q).map (derivedLowerTruncationToStage K (n + 1)))
      ((H q).map (Q.map (lowerTruncationStep K n)))

/-- Helper for Lemma 13.34.7: on the concrete product of shifted lower truncations, the degree-`q`
homology of the Milnor difference map has the expected componentwise formula `x_n - f_n(x_{n+1})`.
-/
lemma lower_truncation_homology_difference_component
    (K : CochainComplex 𝒜 ℤ) (q : ℤ) (n : ℕ) :
    ((DerivedCategory.homologyFunctor 𝒜 q).map
        (Q.map (derivedLimitDifferenceMap (lowerTruncationDiagram K))) ≫
      (homology_termwise_product_iso q (fun j ↦ lowerTruncationStage K j)).hom ≫
      Pi.π (fun j ↦
        (DerivedCategory.homologyFunctor 𝒜 q).obj (Q.obj (lowerTruncationStage K j))) n) =
      (DerivedCategory.homologyFunctor 𝒜 q).map
          (Q.map (Pi.π (fun j ↦ lowerTruncationStage K j) n)) -
        (DerivedCategory.homologyFunctor 𝒜 q).map
          (Q.map (Pi.π (fun j ↦ lowerTruncationStage K j) (n + 1) ≫
            lowerTruncationStep K n)) := by
  sorry

/-- Helper for Lemma 13.34.7: once the degree-`p - 1` Milnor difference map is epi and the
kernel of the degree-`p` Milnor difference map projects isomorphically to stage `m`, exactness of
the Milnor triangle forces the degree-`p` projection from the Milnor limit object to be an
isomorphism. -/
lemma lower_truncation_projection_homology_isIso_of_difference_data
    (K : CochainComplex 𝒜 ℤ)
    {L : DerivedCategory 𝒜}
    [HasProduct (inverseSystemFamily (derivedLowerTruncationTower K))]
    {ι : L ⟶ ∏ᶜ inverseSystemFamily (derivedLowerTruncationTower K)}
    (hι : HasMilnorTriangle.WithMap (derivedLowerTruncationTower K) ι)
    (p : ℤ) (m : ℕ)
    (hDiffEpi : Epi ((DerivedCategory.homologyFunctor 𝒜 (p - 1)).map
      (derivedLimitDifferenceMap (derivedLowerTruncationTower K))))
    (hKernelProj :
      IsIso
        (kernel.ι
            ((DerivedCategory.homologyFunctor 𝒜 p).map
              (derivedLimitDifferenceMap (derivedLowerTruncationTower K))) ≫
          (DerivedCategory.homologyFunctor 𝒜 p).map
            (Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m))) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 p).map
      (ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m)) := by
  sorry

/-- Helper for Lemma 13.34.7: in the Milnor triangle for the shifted lower truncation tower, the
projection to any sufficiently stable stage induces an isomorphism on degree-`p` cohomology. -/
lemma lower_truncation_projection_homology_isIso
    (K : CochainComplex 𝒜 ℤ)
    {L : DerivedCategory 𝒜}
    [HasProduct (inverseSystemFamily (derivedLowerTruncationTower K))]
    {ι : L ⟶ ∏ᶜ inverseSystemFamily (derivedLowerTruncationTower K)}
    (hι : HasMilnorTriangle.WithMap (derivedLowerTruncationTower K) ι)
    (p : ℤ) (m : ℕ)
    (hm : -(((m + 1 : ℕ)) : ℤ) ≤ p) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 p).map
      (ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m)) := by
  sorry

/-- Helper for Lemma 13.34.7: the shifted lower truncation tower of a complex admits a
compatible derived-limit comparison that is already an isomorphism in the derived category. -/
lemma exists_isIso_lowerTruncationDerivedLimitComparison
    (K : CochainComplex 𝒜 ℤ) :
    ∃ (L : DerivedCategory 𝒜) (c : Q.obj K ⟶ L),
      IsLowerTruncationDerivedLimitComparison K L c ∧ IsIso c := by
  sorry

/-- Lemma 13.34.7: if an abelian category has enough injectives and exact countable products, then
every cochain complex admits a quasi-isomorphism to a K-injective complex. -/
theorem exists_quasiIso_to_kInjective
    (K : CochainComplex 𝒜 ℤ) :
    ∃ (I : CochainComplex 𝒜 ℤ) (_ : I.IsKInjective) (f : K ⟶ I), QuasiIso f := by
  obtain ⟨S⟩ := exists_lowerTruncationResolutionSystem (isInjective 𝒜) K
  -- Proof comment: the inverse limit of the chosen injective resolution system is already
  -- K-injective, so only the quasi-isomorphism of the canonical map remains.
  refine ⟨limit S.diagram, isKInjective_lowerTruncationResolutionSystemLimit S, S.intoLimit, ?_⟩
  -- Proof comment: reduce the quasi-isomorphism claim to the existence of an isomorphic
  -- compatible comparison with the same shifted lower truncation tower.
  obtain ⟨L, c, hc, hcIso⟩ := exists_isIso_lowerTruncationDerivedLimitComparison (𝒜 := 𝒜) K
  exact
    (lowerTruncationResolutionLimit_quasiIso_iff_isIso_derivedComparison S hc).2 hcIso

end

end CategoryTheory
