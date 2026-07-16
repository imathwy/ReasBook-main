import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_18_1
import stacks_proof.stacks_project.Chap13.Lemma_13_18_8
import stacks_proof.stacks_project.Chap13.Lemma_13_15_2
import stacks_proof.stacks_project.Chap13.Definition_13_15_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

attribute [local instance] HasDerivedCategory.standard

section

variable {𝒜 : Type u₁} {𝒟 : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜]
  [Category.{v₂} 𝒟]

variable (F : K⁺(𝒜) ⥤ 𝒟)

local notation "QisPlus" => Qis⁺(𝒜)
local notation "KQplus" => HomotopyCategory.Plus.quotient 𝒜
local notation "KplusToDplus" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))

private theorem KplusToDplus_isLocalization :
    Functor.IsLocalization KplusToDplus QisPlus := by
  sorry

attribute [local instance] KplusToDplus_isLocalization

/- Domain-style sampling for Lemma 13.20.1:
- primary domain: bounded-below injective cochain complexes and right-derived computation /
  acyclicity for additive functors on bounded-below and unbounded homotopy categories;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.PlusWithTermsIn.instIsKInjective`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `Functor.ComputesRightDerivedAt`,
  `computes_right_derived_functor_at_iff_bounded_below`;
- best owner abstraction: part `(1)` is source-facing at the chapter owner
  `CochainComplex.InjectivePlus 𝒜`, with computation exported through the canonical owner
  `Functor.ComputesRightDerivedAt`; part `(2)` is the degree-zero specialization to the Chapter 13
  owner `IsRightAcyclicForAdditiveFunctor`;
- primitive data: a bounded-below injective complex `I : CochainComplex.InjectivePlus 𝒜`, or an
  injective object `I : 𝒜`;
- derived API: the computation statement at `((HomotopyCategory.Plus.quotient 𝒜).obj I)` and the
  right-acyclicity statement
  for `I`.

Source/core/bridge triage:
- `source-facing`: the two textbook statements below;
- `core/canonical`: `CochainComplex.InjectivePlus 𝒜`,
  `Functor.ComputesRightDerivedAt`, and `IsRightAcyclicForAdditiveFunctor`;
- `bridge/view`: the canonical K-injective bridge
  `CochainComplex.PlusWithTermsIn.instIsKInjective`, the hom-bijection theorem
  `CochainComplex.IsKInjective.Qh_map_bijective`, and the bounded/unbounded comparison theorem
  `computes_right_derived_functor_at_iff_bounded_below`.
-/

-- Proof sketch: the owner `CochainComplex.InjectivePlus 𝒜` carries the canonical K-injective
-- structure from `CochainComplex.PlusWithTermsIn.instIsKInjective`. Hence the pointwise
-- costructured-arrow diagram over `((HomotopyCategory.Plus.quotient 𝒜).obj I)` is already
-- controlled by the hom-bijection theorem `CochainComplex.IsKInjective.Qh_map_bijective`, so the
-- identity denominator witnesses that `I` computes the right derived functor.
/-- Helper for Lemma 13.20.1: maps from a bounded-below homotopy object into a bounded-below
injective complex are already determined after passing to `D^+(\mathcal A)`. -/
private theorem boundedBelowInjective_mapBoundedBelowHomotopyToDerivedBelow_bijective
    (Y : K⁺(𝒜)) (I : CochainComplex.InjectivePlus 𝒜) :
    Function.Bijective
      ((KplusToDplus).map :
        (Y ⟶ (KQplus).obj I) →
          ((KplusToDplus).obj Y ⟶ (KplusToDplus).obj ((KQplus).obj I))) := by
  sorry

/-- Helper for Lemma 13.20.1: after transporting the canonical localization through the concrete
bounded-below derived localization, factorization through the identity denominator is equivalent
to an ordinary morphism equality in `D^+(\mathcal A)`. -/
private lemma boundedBelowInjective_factorization_iff
    (I : CochainComplex.InjectivePlus 𝒜)
    (g : CostructuredArrow (QisPlus).Q ((QisPlus).Q.obj ((KQplus).obj I)))
    (β : g.left ⟶ (KQplus).obj I) :
    (QisPlus).Q.map β = g.hom ↔
      (KplusToDplus).map β =
        ((Localization.compUniqFunctor (QisPlus).Q KplusToDplus QisPlus).app g.left).inv ≫
          (Localization.uniq (QisPlus).Q KplusToDplus QisPlus).functor.map g.hom ≫
          ((Localization.compUniqFunctor (QisPlus).Q KplusToDplus QisPlus).app
            ((KQplus).obj I)).hom := by
  sorry

/-- Helper for Lemma 13.20.1: every object of the right-derived indexing category admits a unique
map to the identity denominator once the target complex is bounded below injective. -/
private lemma boundedBelowInjective_existsUnique_factorization
    (I : CochainComplex.InjectivePlus 𝒜)
    (g : CostructuredArrow (QisPlus).Q ((QisPlus).Q.obj ((KQplus).obj I))) :
    ∃! β : g.left ⟶ (KQplus).obj I, (QisPlus).Q.map β = g.hom := by
  sorry

/-- Helper for Lemma 13.20.1: the identity denominator is terminal in the pointwise
costructured-arrow category of a bounded-below injective complex. -/
private noncomputable def boundedBelowInjective_identity_costructuredArrow_isTerminal
    (I : CochainComplex.InjectivePlus 𝒜) :
    Limits.IsTerminal
      (CostructuredArrow.mk (𝟙 ((QisPlus).Q.obj ((KQplus).obj I))) :
        CostructuredArrow (QisPlus).Q ((QisPlus).Q.obj ((KQplus).obj I))) := by
  sorry

/-- Helper for Lemma 13.20.1: the pointwise right-derived indexing diagram at a bounded-below
injective complex has a terminal-object colimit. -/
private lemma boundedBelowInjective_hasPointwiseRightDerivedFunctorAt
    (I : CochainComplex.InjectivePlus 𝒜) :
    F.HasPointwiseRightDerivedFunctorAt QisPlus ((KQplus).obj I) := by
  sorry

/-- Helper for Lemma 13.20.1: the identity-denominator leg in the pointwise colimit presentation
is the colimit inclusion at a terminal object, hence an isomorphism. -/
private lemma boundedBelowInjective_rightDerivedValueLeg_id_isIso
    (I : CochainComplex.InjectivePlus 𝒜) :
    let _ : F.HasPointwiseRightDerivedFunctorAt QisPlus ((KQplus).obj I) :=
      boundedBelowInjective_hasPointwiseRightDerivedFunctorAt (𝒜 := 𝒜) (F := F) I
    IsIso
      (rightDerivedValueLeg QisPlus F (𝟙 ((KQplus).obj I))
        ((QisPlus).id_mem ((KQplus).obj I))) := by
  sorry

/-- Lemma 13.20.1 (1): a bounded-below cochain complex of injective objects in an abelian
category computes the right derived functor of any functor
`F : K^+(\mathcal A) ⥤ \mathcal D` with respect to quasi-isomorphisms. -/
@[stacks 05TH]
theorem boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
    (I : CochainComplex.InjectivePlus 𝒜) :
    F.ComputesRightDerivedAt QisPlus ((KQplus).obj I) := by
  sorry

end

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F

-- Proof sketch: package the degree-zero complex `I[0]` as an object of
-- `CochainComplex.InjectivePlus 𝒜` using the injectivity of `I`, then apply part (1). Use
-- `computes_right_derived_functor_at_iff_bounded_below` to pass from the bounded-below
-- computation to the unbounded pointwise one, then conclude with the Chapter 13 source-facing owner
-- `IsRightAcyclicForAdditiveFunctor`.
/-- Helper for Lemma 13.20.1: every term of the bounded-below degree-zero complex on an injective
object is injective. -/
private lemma single0Plus_terms_injective
    (I : 𝒜) [Injective I] :
    ∀ n : ℤ, Injective ((((single0Plus 𝒜).obj I).obj.as).X n) := by
  intro n
  -- Proof comment: the degree-zero term is `I`, and every other term is canonically zero.
  by_cases hn : n = 0
  · subst hn
    simpa [HomotopyCategory.quotient_obj_as] using (inferInstance : Injective I)
  ·
    let hzero :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I n hn
    exact Injective.of_iso hzero.isoZero.symm inferInstance

/-- Helper for Lemma 13.20.1: the degree-zero bounded-below complex on an injective object
defines an object of `CochainComplex.InjectivePlus 𝒜`. -/
private abbrev single0Plus_to_injectivePlus
    (I : 𝒜) [Injective I] : CochainComplex.InjectivePlus 𝒜 :=
  ⟨⟨((single0Plus 𝒜).obj I).obj.as, ((single0Plus 𝒜).obj I).property⟩,
    single0Plus_terms_injective (𝒜 := 𝒜) I⟩

/-- Lemma 13.20.1 (2): every injective object of an abelian category is right acyclic for any
additive functor to an abelian category. -/
@[stacks 05TH]
theorem injective_isRightAcyclicForAdditiveFunctor
    (I : 𝒜) [Injective I] :
    IsRightAcyclicForAdditiveFunctor F I := by
  have hBounded :
      (mapBoundedBelowHomotopyCategoryToDerivedBelow F).ComputesRightDerivedAt
        (Qis⁺(𝒜)) ((single0Plus 𝒜).obj I) := by
    -- Proof comment: the degree-zero complex `I[0]` is itself a bounded-below injective complex.
    simpa [single0Plus_to_injectivePlus] using
      (boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
        (𝒜 := 𝒜) (𝒟 := D⁺(ℬ))
        (F := mapBoundedBelowHomotopyCategoryToDerivedBelow F)
        (single0Plus_to_injectivePlus (𝒜 := 𝒜) I))
  -- Proof comment: transport the bounded-below computation statement to the unbounded degree-zero
  -- complex using the bounded/unbounded comparison theorem.
  simpa [IsRightAcyclicForAdditiveFunctor, HomotopyCategory.quotient_obj_as] using
    (computes_right_derived_functor_at_iff_bounded_below
      (F := F) ((single0Plus 𝒜).obj I)).2 hBounded

end

end CategoryTheory
