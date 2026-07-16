import Mathlib
import stacks_proof.stacks_project.Chap13.Lemma_13_16_4
import stacks_proof.stacks_project.Chap13.Lemma_13_19_11
import stacks_proof.stacks_project.Chap13.Lemma_13_34_2
import stacks_proof.stacks_project.Chap13.Lemma_13_34_6

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
  -- Proof comment: apply the derived-category quotient functor to the commutative square for the
  -- cochain-level lower truncation maps.
  simpa [derivedLowerTruncationToStage, derivedLowerTruncationTower, lowerTruncationDiagram,
    SequentialInverseSystem.transitionMap, Category.assoc] using
    congrArg Q.map (πTruncGE_comp_lowerTruncationStep K n).w

/-- Helper for Lemma 13.34.7: the canonical cone map from `K^•` to the Milnor product object is
annihilated by the Milnor difference map. -/
lemma lower_truncation_product_cone_comp_difference_zero
    (K : CochainComplex 𝒜 ℤ)
    [HasProduct (inverseSystemFamily (derivedLowerTruncationTower K))] :
    Pi.lift (fun n ↦ derivedLowerTruncationToStage K n) ≫
        derivedLimitDifferenceMap (derivedLowerTruncationTower K) =
      0 := by
  -- Proof comment: compare both sides after each product projection and use cone compatibility of
  -- the stage maps with the tower transition maps.
  apply Pi.hom_ext
  intro n
  calc
    Pi.lift (fun n ↦ derivedLowerTruncationToStage K n) ≫
        derivedLimitDifferenceMap (derivedLowerTruncationTower K) ≫
        Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n =
      derivedLowerTruncationToStage K n -
        derivedLowerTruncationToStage K (n + 1) ≫
          (derivedLowerTruncationTower K).transitionMap (Nat.le_succ n) := by
        simp [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ = derivedLowerTruncationToStage K n - derivedLowerTruncationToStage K n := by
        rw [derivedLowerTruncationToStage_comp_transition]
    _ = 0 := by simp

/-- Helper for Lemma 13.34.7: any chosen Milnor-model of the shifted lower truncation tower
admits a comparison map from `K^•` whose stage projections recover the canonical truncation maps.
-/
lemma exists_lowerTruncationDerivedLimitComparison_of_isDerivedLimit
    (K : CochainComplex 𝒜 ℤ) {L : DerivedCategory 𝒜}
    (hL : IsDerivedLimit (derivedLowerTruncationTower K) L) :
    ∃ c : Q.obj K ⟶ L, IsLowerTruncationDerivedLimitComparison K L c := by
  rcases hL with ⟨hP, ι, δ, hT⟩
  letI : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)) := hP
  let α : Q.obj K ⟶ ∏ᶜ inverseSystemFamily (derivedLowerTruncationTower K) :=
    Pi.lift (fun n ↦ derivedLowerTruncationToStage K n)
  have hαzero :
      α ≫ derivedLimitDifferenceMap (derivedLowerTruncationTower K) = 0 := by
    -- Proof comment: the canonical cone satisfies the defining equalizer relation of the Milnor
    -- product cone.
    simpa [α] using
      lower_truncation_product_cone_comp_difference_zero (𝒜 := 𝒜) K
  let T : Triangle (DerivedCategory 𝒜) :=
    Triangle.mk ι (derivedLimitDifferenceMap (derivedLowerTruncationTower K)) δ
  obtain ⟨c, hc⟩ := T.coyoneda_exact₂ hT α (by simpa [T] using hαzero)
  refine ⟨c, ?_⟩
  refine ⟨hP, ι, ⟨δ, hT⟩, ?_⟩
  intro n
  -- Proof comment: the lifted map agrees with the original cone map after projection to every
  -- stage.
  have hproj :
      c ≫ ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n =
        α ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n := by
    simpa [T, α, Category.assoc] using
      congrArg
        (fun f ↦ f ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) n)
        hc
  simpa [α, Category.assoc] using hproj

/-- Helper for Lemma 13.34.7: the degree-`p` cohomology map induced by the canonical truncation
projection `X ⟶ τ_{\ge p} X` is an isomorphism. -/
lemma homology_map_truncGEπ_isIso
    (X : DerivedCategory 𝒜) (p : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 p).map ((t.truncGEπ p).app X)) := by
  let H := DerivedCategory.homologyFunctor 𝒜
  let T : Triangle (DerivedCategory 𝒜) := (t.triangleLTGE p).obj X
  have hT : T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using t.triangleLTGE_distinguished p X
  have h₁ : T.obj₁.IsLE (p - 1) := by
    dsimp [T]
    infer_instance
  have hmor₁_zero : (H p).map T.mor₁ = 0 := by
    -- Proof comment: the left truncation term has no degree-`p` cohomology.
    exact (isZero_of_isLE T.obj₁ (p - 1) p (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T p (p + 1) rfl = 0 := by
    -- Proof comment: the connecting morphism lands in another vanishing cohomology group of the
    -- left truncation term.
    exact (isZero_of_isLE T.obj₁ (p - 1) (p + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H p).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT p (p + 1) rfl).2 hδ_zero
  letI : Mono ((H p).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT p).2 hmor₁_zero
  simpa [T] using isIso_of_mono_of_epi ((H p).map T.mor₂)

/-- Helper for Lemma 13.34.7: once the truncation bound lies below degree `p`, the canonical map
`K^• ⟶ τ_{\ge -(m + 1)} K^•` induces an isomorphism on `H^p`. -/
lemma homology_map_derivedLowerTruncationToStage_isIso
    (K : CochainComplex 𝒜 ℤ) (p : ℤ) (m : ℕ)
    (hm : -(((m + 1 : ℕ)) : ℤ) ≤ p) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 p).map (derivedLowerTruncationToStage K m)) := by
  let H := DerivedCategory.homologyFunctor 𝒜
  let f := derivedLowerTruncationToStage K m
  let Y := (derivedLowerTruncationTower K).obj (Opposite.op m)
  have hf :
      (H p).map f ≫ (H p).map ((t.truncGEπ p).app Y) =
        (H p).map ((t.truncGEπ p).app (Q.obj K)) ≫ (H p).map ((t.truncGE p).map f) := by
    -- Proof comment: rewrite `H^p(f)` against the naturality square for `t.truncGEπ p`.
    simpa [Functor.map_comp, f, Y, derivedLowerTruncationToStage] using
      congrArg ((H p).map) (NatTrans.naturality (t.truncGEπ p) f)
  have hmiddle : IsIso ((H p).map ((t.truncGE p).map f)) := by
    haveI : IsIso ((t.truncGE p).map f) := by
      simpa [f, derivedLowerTruncationToStage] using
        t.isIso_truncGE_map_truncGEπ_app p (-(((m + 1 : ℕ)) : ℤ)) hm (Q.obj K)
    exact Functor.map_isIso (H p) ((t.truncGE p).map f)
  have hcomp :
      IsIso ((H p).map f ≫ (H p).map ((t.truncGEπ p).app Y)) := by
    rw [hf]
    let _ : IsIso ((H p).map ((t.truncGEπ p).app (Q.obj K))) :=
      homology_map_truncGEπ_isIso (𝒜 := 𝒜) (Q.obj K) p
    let _ : IsIso ((H p).map ((t.truncGE p).map f)) := hmiddle
    infer_instance
  let _ : IsIso ((H p).map f ≫ (H p).map ((t.truncGEπ p).app Y)) := hcomp
  exact IsIso.of_isIso_comp_right ((H p).map f) ((H p).map ((t.truncGEπ p).app Y))

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

/-- Helper for Lemma 13.34.7: after transporting both stable stages back to `H^q(K)`, the
cohomology transition map on the shifted lower truncation tower becomes the identity. -/
lemma lower_truncation_transition_homology_conj_eq_id
    (K : CochainComplex 𝒜 ℤ) (q : ℤ) (n : ℕ)
    (hq : -(((n + 1 : ℕ)) : ℤ) ≤ q) :
    (asIso ((DerivedCategory.homologyFunctor 𝒜 q).map
        (derivedLowerTruncationToStage K (n + 1)))).hom ≫
        ((DerivedCategory.homologyFunctor 𝒜 q).map (Q.map (lowerTruncationStep K n))) ≫
        (asIso ((DerivedCategory.homologyFunctor 𝒜 q).map
          (derivedLowerTruncationToStage K n))).inv =
      𝟙 _ := by
  let H := DerivedCategory.homologyFunctor 𝒜
  have hq' : -((((n + 1) + 1 : ℕ)) : ℤ) ≤ q := by
    omega
  let _ : IsIso ((H q).map (derivedLowerTruncationToStage K (n + 1))) :=
    homology_map_derivedLowerTruncationToStage_isIso (𝒜 := 𝒜) K q (n + 1) hq'
  let _ : IsIso ((H q).map (derivedLowerTruncationToStage K n)) :=
    homology_map_derivedLowerTruncationToStage_isIso (𝒜 := 𝒜) K q n hq
  have hcomp :
      (H q).map (derivedLowerTruncationToStage K (n + 1)) ≫
          (H q).map (Q.map (lowerTruncationStep K n)) =
        (H q).map (derivedLowerTruncationToStage K n) := by
    -- Proof comment: this is the same stage-compatibility identity as above, now kept for the
    -- explicit conjugation-to-identity rewrite used by the eventual constant-tail algebra.
    simpa [Functor.map_comp, derivedLowerTruncationTower, lowerTruncationDiagram,
      SequentialInverseSystem.transitionMap] using
      congrArg ((H q).map) (derivedLowerTruncationToStage_comp_transition (𝒜 := 𝒜) K n)
  -- Proof comment: compose the compatibility identity with the inverse of the stage-`n`
  -- comparison to collapse the conjugated transition to the identity on `H^q(K)`.
  calc
    (asIso ((H q).map (derivedLowerTruncationToStage K (n + 1)))).hom ≫
        (H q).map (Q.map (lowerTruncationStep K n)) ≫
        (asIso ((H q).map (derivedLowerTruncationToStage K n))).inv =
      (H q).map (derivedLowerTruncationToStage K n) ≫
        (asIso ((H q).map (derivedLowerTruncationToStage K n))).inv := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ f ≫ (asIso ((H q).map (derivedLowerTruncationToStage K n))).inv)
            hcomp
    _ = 𝟙 _ := by
        simp

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
  -- Proof comment: first rewrite the projection from `H^q` of the termwise product using the
  -- product comparison iso from Lemma 13.34.2, then unfold the Milnor difference component.
  calc
    ((DerivedCategory.homologyFunctor 𝒜 q).map
        (Q.map (derivedLimitDifferenceMap (lowerTruncationDiagram K))) ≫
      (homology_termwise_product_iso q (fun j ↦ lowerTruncationStage K j)).hom ≫
      Pi.π (fun j ↦
        (DerivedCategory.homologyFunctor 𝒜 q).obj (Q.obj (lowerTruncationStage K j))) n) =
      (DerivedCategory.homologyFunctor 𝒜 q).map
        (Q.map (derivedLimitDifferenceMap (lowerTruncationDiagram K))) ≫
          (DerivedCategory.homologyFunctor 𝒜 q).map
            (Q.map (Pi.π (fun j ↦ lowerTruncationStage K j) n)) := by
        rw [homology_termwise_product_iso_hom]
        simp [Category.assoc]
    _ =
      (DerivedCategory.homologyFunctor 𝒜 q).map
        (Q.map
          (derivedLimitDifferenceMap (lowerTruncationDiagram K) ≫
            Pi.π (fun j ↦ lowerTruncationStage K j) n)) := by
        simp [Functor.map_comp, Category.assoc]
    _ =
      (DerivedCategory.homologyFunctor 𝒜 q).map
        (Q.map
          (Pi.π (fun j ↦ lowerTruncationStage K j) n -
            Pi.π (fun j ↦ lowerTruncationStage K j) (n + 1) ≫ lowerTruncationStep K n)) := by
        rw [derivedLimitDifferenceMap_comp_π]
    _ =
      (DerivedCategory.homologyFunctor 𝒜 q).map
          (Q.map (Pi.π (fun j ↦ lowerTruncationStage K j) n)) -
        (DerivedCategory.homologyFunctor 𝒜 q).map
          (Q.map (Pi.π (fun j ↦ lowerTruncationStage K j) (n + 1) ≫
            lowerTruncationStep K n)) := by
        simp [Functor.map_sub, Functor.map_comp]

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
  let H := DerivedCategory.homologyFunctor 𝒜
  let _ : Epi ((H (p - 1)).map (derivedLimitDifferenceMap (derivedLowerTruncationTower K))) :=
    hDiffEpi
  let _ :
      IsIso
        (kernel.ι ((H p).map (derivedLimitDifferenceMap (derivedLowerTruncationTower K))) ≫
          (H p).map (Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m)) :=
    hKernelProj
  rcases hι with ⟨δ, hT⟩
  let T : Triangle (DerivedCategory 𝒜) :=
    Triangle.mk ι (derivedLimitDifferenceMap (derivedLowerTruncationTower K)) δ
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk
      ((H p).map T.mor₁)
      ((H p).map T.mor₂)
      (by
        -- Proof comment: `H^p` sends the zero composite of the first two triangle maps to zero.
        simpa [T, Functor.map_comp] using
          congrArg ((H p).map) (comp_distTriang_mor_zero₁₂ _ hT))
  have hδ_zero : HomologySequence.δ T (p - 1) p rfl = 0 := by
    -- Proof comment: exactness at `H^(p - 1)` kills the connecting morphism once the Milnor
    -- difference is epi in that degree.
    exact
      ((homologyMap_exact₃_of_distTriang T hT (p - 1) p rfl).epi_f_iff).1
        (by simpa [T] using hDiffEpi)
  have hmono : Mono S.f := by
    -- Proof comment: with the connecting morphism zero, exactness upgrades `H^p(ι)` to a kernel.
    exact ((homologyMap_exact₁_of_distTriang T hT (p - 1) p rfl).mono_g_iff).2 hδ_zero
  have hExact : S.Exact := by
    -- Proof comment: this is the middle exactness statement of the long exact cohomology
    -- sequence for the Milnor triangle.
    simpa [S, T] using homologyMap_exact₂_of_distTriang T hT p
  have hKernel :
      IsLimit (KernelFork.ofι S.f S.zero) := by
    exact ((S.exact_and_mono_f_iff_f_is_kernel).1 ⟨hExact, hmono⟩).some
  let eKernel :
      S.X₁ ≅ kernel S.g :=
    IsLimit.conePointUniqueUpToIso hKernel (kernelIsKernel S.g)
  have hkernel_comp :
      eKernel.hom ≫ kernel.ι S.g = S.f := by
    -- Proof comment: compare the chosen kernel presentation from exactness with the canonical
    -- kernel owner.
    simpa [S, eKernel] using
      hKernel.conePointUniqueUpToIso_hom_comp (kernelIsKernel S.g) WalkingParallelPair.zero
  have hcompIso :
      IsIso
        (eKernel.hom ≫
          kernel.ι ((H p).map (derivedLimitDifferenceMap (derivedLowerTruncationTower K))) ≫
            (H p).map (Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m)) := by
    -- Proof comment: compose the kernel comparison with the assumed kernel projection
    -- isomorphism.
    change IsIso
      (eKernel.hom ≫
        (kernel.ι ((H p).map (derivedLimitDifferenceMap (derivedLowerTruncationTower K))) ≫
          (H p).map (Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m)))
    let _ : IsIso eKernel.hom := eKernel.isIso_hom
    infer_instance
  have hprojIso : IsIso (S.f ≫ (H p).map
      (Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m)) := by
    rw [← hkernel_comp] at hcompIso
    exact hcompIso
  -- Proof comment: substitute the concrete first morphism of the exact row and rewrite the
  -- desired projection through functoriality.
  simpa [S, T, Functor.map_comp, Category.assoc] using hprojIso

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
  -- Route correction: the remaining work is no longer the Milnor-triangle exactness step.
  -- That closing argument is packaged below; only the source-faithful tail algebra for the raw
  -- degree-`p - 1`/`p` difference maps remains.
  refine
    lower_truncation_projection_homology_isIso_of_difference_data
      (𝒜 := 𝒜) K hι p m
  · -- TODO: transport the degree-`p - 1` Milnor difference map to the eventual-constant tail
    -- model and prove it is epi there, then transport the result back to the chosen product
    -- object.
    sorry
  · -- TODO: identify the kernel of the degree-`p` Milnor difference map with the compatible
    -- families on the stable tail, then show projection to stage `m` is an isomorphism by the
    -- explicit constant-tail inverse construction.
    sorry

/-- Helper for Lemma 13.34.7: the shifted lower truncation tower of a complex admits a
compatible derived-limit comparison that is already an isomorphism in the derived category. -/
lemma exists_isIso_lowerTruncationDerivedLimitComparison
    (K : CochainComplex 𝒜 ℤ) :
    ∃ (L : DerivedCategory 𝒜) (c : Q.obj K ⟶ L),
      IsLowerTruncationDerivedLimitComparison K L c ∧ IsIso c := by
  obtain ⟨S⟩ := exists_lowerTruncationResolutionSystem (isInjective 𝒜) K
  obtain ⟨c, hc⟩ :=
    exists_lowerTruncationDerivedLimitComparison_of_isDerivedLimit (𝒜 := 𝒜) K
      (lowerTruncationResolutionSystemLimit_isDerivedLimit S)
  refine ⟨Q.obj (limit S.diagram), c, hc, ?_⟩
  rw [derivedCategory_isIso_iff_homology_map_isIso (F := 𝟭 𝒜) c]
  intro p
  let m : ℕ := Int.natAbs p
  have hm : -(((m + 1 : ℕ)) : ℤ) ≤ p := by
    cases p <;> omega
  rcases hc with ⟨hP, ι, hι, hcomp⟩
  letI : HasProduct (inverseSystemFamily (derivedLowerTruncationTower K)) := hP
  have hstage :
      IsIso ((DerivedCategory.homologyFunctor 𝒜 p).map (derivedLowerTruncationToStage K m)) :=
    homology_map_derivedLowerTruncationToStage_isIso (𝒜 := 𝒜) K p m hm
  have hproj :
      IsIso ((DerivedCategory.homologyFunctor 𝒜 p).map
        (ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m)) :=
    lower_truncation_projection_homology_isIso (𝒜 := 𝒜) K hι p m hm
  have hfactor :
      ((DerivedCategory.homologyFunctor 𝒜 p).map c) ≫
          ((DerivedCategory.homologyFunctor 𝒜 p).map
            (ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m)) =
        ((DerivedCategory.homologyFunctor 𝒜 p).map (derivedLowerTruncationToStage K m)) := by
    -- Proof comment: compatibility identifies the degree-`p` factorization of `H^p(c)` through
    -- the stable stage `τ_{\ge -(m + 1)} K^•`.
    simpa [Functor.map_comp] using
      congrArg ((DerivedCategory.homologyFunctor 𝒜 p).map) (hcomp m)
  have hcompIso :
      IsIso (((DerivedCategory.homologyFunctor 𝒜 p).map c) ≫
        ((DerivedCategory.homologyFunctor 𝒜 p).map
          (ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m))) := by
    rw [hfactor]
    exact hstage
  let _ :
      IsIso (((DerivedCategory.homologyFunctor 𝒜 p).map c) ≫
        ((DerivedCategory.homologyFunctor 𝒜 p).map
          (ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m))) := hcompIso
  exact
    IsIso.of_isIso_comp_right
      ((DerivedCategory.homologyFunctor 𝒜 p).map c)
      ((DerivedCategory.homologyFunctor 𝒜 p).map
        (ι ≫ Pi.π (inverseSystemFamily (derivedLowerTruncationTower K)) m))

/-- Lemma 13.34.7: if an abelian category has enough injectives and exact countable products, then
every cochain complex admits a quasi-isomorphism to a K-injective complex. -/
@[stacks 090Y]
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
