import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_15_3
import stacks_proof.stacks_project.Chap13.Proposition_13_16_8
import stacks_proof.stacks_project.Chap13.Lemma_13_16_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable {𝒝 : Type u₂} [Category.{v₂} 𝒝] [Abelian 𝒝] [HasDerivedCategory.{w} 𝒝]
variable (F : 𝒜 ⥤ 𝒝) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/- Domain-style sampling for Lemma 13.16.9:
-- primary domain: exact functors between abelian categories and their right derived functors,
  with source-facing consequences stated on the chapter owners for acyclicity, bounded-below
  derivability, and higher derived vanishing;
- sampled owner declarations:
  `Functor.mapDerivedCategory`,
  `Functor.mapDerivedCategoryFactors`,
  `IsRightAcyclicForAdditiveFunctor`,
  `Functor.boundedBelowHigherRightDerivedVanishes`,
  `Functor.higherRightDerivedVanishes`,
  `Functor.IsRightDerivedFunctor`,
  `Functor.HasRightDerivedFunctor.mk'`;
- best owner abstraction: the core/canonical owner is the induced derived-category functor
  `F.mapDerivedCategory` with its factorization isomorphism `F.mapDerivedCategoryFactors`; the
  source-facing API should then be stated using the chapter owners
  `IsRightAcyclicForAdditiveFunctor F`, `Functor.HasRightDerivedFunctor KplusToDplus QisPlus`,
  `Functor.ComputesRightDerivedAt`, `RF.boundedBelowHigherRightDerivedVanishes`, and, under the
  stronger injective-resolution hypothesis, `F.higherRightDerivedVanishes`;
- primitive data: the exact functor `F` and the factorization isomorphism
  `DerivedCategory.Q ⋙ F.mapDerivedCategory ≅ F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q`;
- derived API: from the core witness that `F.mapDerivedCategory` is the right derived functor, we
  obtain that every object is right `F`-acyclic, the bounded-below and unbounded right derived
  functors are everywhere defined, every bounded-below and unbounded complex computes the
  corresponding right derived functor, the source-facing bounded-below higher right derived
  functors vanish, and under injective resolutions the unbounded higher right derived functors
  vanish.

Source/core/bridge triage:
- `source-facing`: the textbook consequences for an exact functor, namely right acyclicity of all
  objects, bounded-below and unbounded right-derivability, computation by every complex, and the
  bounded-below vanishing statement for positive right derived functors;
- `core/canonical`: `Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`,
  `Functor.IsRightDerivedFunctor`, and `Functor.HasRightDerivedFunctor`;
- `bridge/view`: the packaging of the canonical derived-category functor into right-derived-functor
  and pointwise-computation statements on the Chapter `13` owners, together with the stronger
  unbounded vanishing companion under injective resolutions. -/

local notation "Qis" => HomologicalComplex.quasiIso 𝒜 (up ℤ)
local notation "Qish" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "QisPlus" => boundedBelowHomotopyQuasiIso 𝒜
local notation "DplusQ" => mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "KplusToDplus" => mapBoundedBelowHomotopyCategoryToDerivedBelow F

/- Lemma 13.16.9: for an exact functor of abelian categories, the canonical comparisons between
applying `F` before passing to the derived category and applying the induced functor on derived
categories directly are the owner isomorphisms `F.mapDerivedCategoryFactors` on cochain complexes
and `F.mapDerivedCategoryFactorsh` on homotopy categories. -/
#check F.mapDerivedCategoryFactors

-- Proof sketch: exact functors preserve quasi-isomorphisms, so the universal property of the
-- localization by quasi-isomorphisms identifies `F.mapDerivedCategory` as the right derived
-- functor of both canonical source functors appearing in Lemma `13.16.9`.
private instance mapDerivedCategory_isRightDerivedFunctor :
    F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactors.inv Qis := by
  simpa using
    (Functor.isRightDerivedFunctor_of_inverts Qis
      F.mapDerivedCategory F.mapDerivedCategoryFactors)

private instance mapDerivedCategoryh_isRightDerivedFunctor :
    F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv Qish := by
  simpa [mapHomotopyCategoryToDerived] using
    (Functor.isRightDerivedFunctor_of_inverts Qish
      F.mapDerivedCategory F.mapDerivedCategoryFactorsh)

local notation "Qh" => Qish.Q

-- Proof sketch: after packaging `F.mapDerivedCategory` as the right derived functor of `KtoD`,
-- the total right derived unit is definitionally the comparison
-- `F.mapDerivedCategoryFactorsh.inv`; exactness makes its target functor invert quasi-isomorphisms,
-- so every homotopy object computes the right derived functor.
/-- Helper for Lemma 13.16.9: every object of the homotopy category computes the unbounded right
derived functor of an exact functor. -/
lemma computes_right_derived_at_all_complexes_of_exact
    (K : HomotopyCategory 𝒜 (up ℤ)) :
    Functor.ComputesRightDerivedAt KtoD Qish K := by
  letI : Functor.HasRightDerivedFunctor KtoD Qish :=
    Functor.HasRightDerivedFunctor.mk' F.mapDerivedCategory F.mapDerivedCategoryFactorsh.inv
  rw [Functor.computesRightDerivedAt_iff (F := KtoD) (S := Qish) (X := K)]
  -- Proof comment: `Qh ⋙ F.mapDerivedCategory` inverts quasi-isomorphisms because `Qh` does, so
  -- the canonical comparison to that right derived functor is an isomorphism.
  have hComparison :
      IsIso (F.mapDerivedCategoryFactorsh.inv.app K) := by
    let hInverts : Qish.IsInvertedBy (Qh ⋙ F.mapDerivedCategory) :=
      MorphismProperty.IsInvertedBy.of_comp Qish Qh Qish.Q_inverts F.mapDerivedCategory
    have :
        IsIso F.mapDerivedCategoryFactorsh.inv := by
      exact
        Functor.isIso_of_isRightDerivedFunctor_of_inverts
          F.mapDerivedCategory F.mapDerivedCategoryFactorsh.inv hInverts
    infer_instance
  simpa using hComparison

-- Proof sketch: every object of `𝒜` is represented by its degree-zero complex `A[0]`, and the
-- previous core statement identifies `F.mapDerivedCategory` with the right derived functor of the
-- exact functor on complexes. Since `F` already carries quasi-isomorphisms to isomorphisms, the
-- degree-zero complex computes the right derived functor.
/-- Lemma 13.16.9 (1): every object of `𝒜` is right acyclic for the exact functor `F`. -/
@[stacks 015F]
theorem isRightAcyclicForAdditiveFunctor_of_exact (A : 𝒜) :
    IsRightAcyclicForAdditiveFunctor F A := by
  -- Proof comment: specialize the all-complexes computation statement to the degree-zero complex
  -- representing `A`.
  simpa [IsRightAcyclicForAdditiveFunctor] using
    computes_right_derived_at_all_complexes_of_exact
      (F := F) ((HomotopyCategory.singleFunctor 𝒜 0).obj A)

-- Proof sketch: once `F.mapDerivedCategory` is identified as a right derived functor, existence
-- of the right derived functor follows by `Functor.HasRightDerivedFunctor.mk'`.
/-- The total right derived functor of the functor on cochain complexes induced by `F` is
everywhere defined. -/
instance mapHomologicalComplex_hasRightDerivedFunctor :
    (F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor Qis := by
  simpa using
    (Functor.HasRightDerivedFunctor.mk'
      F.mapDerivedCategory F.mapDerivedCategoryFactors.inv :
      (F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q).HasRightDerivedFunctor Qis)

-- Proof sketch: the homotopy-category source functor `KtoD` is canonically identified with
-- `F.mapDerivedCategory` via `F.mapDerivedCategoryFactorsh`, so the same owner-level
-- `HasRightDerivedFunctor.mk'` specialization gives the unbounded existence statement.
/-- Lemma 13.16.9 (3): the unbounded right derived functor of the exact functor `F` is everywhere
defined. -/
@[stacks 015F]
instance mapHomotopyCategoryToDerived_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor KtoD Qish := by
  simpa [mapHomotopyCategoryToDerived] using
    (Functor.HasRightDerivedFunctor.mk'
      F.mapDerivedCategory F.mapDerivedCategoryFactorsh.inv :
      Functor.HasRightDerivedFunctor KtoD Qish)

-- Proof sketch: Lemma `13.15.2` transports the degree-zero computation statement from the
-- unbounded homotopy category to the bounded-below one.
/-- Helper for Lemma 13.16.9: every object is bounded-below right acyclic for an exact functor. -/
lemma is_bounded_below_right_acyclic_of_exact (A : 𝒜) :
    IsBoundedBelowRightAcyclicForAdditiveFunctor F A := by
  -- Proof comment: compare the bounded-below and unbounded degree-zero complexes via
  -- `computes_right_derived_functor_at_iff_bounded_below`.
  simpa [IsRightAcyclicForAdditiveFunctor, HomotopyCategory.quotient_obj_as] using
    (computes_right_derived_functor_at_iff_bounded_below
      (F := F) ((single0Plus 𝒜).obj A)).1
      (isRightAcyclicForAdditiveFunctor_of_exact (F := F) A)

/-- Helper for Lemma 13.16.9: bounded-below right `F`-acyclic objects have mono embeddings,
witnessed here by the identity monomorphism because every object is already acyclic. -/
local instance bounded_below_right_acyclic_has_mono_embedding :
    ObjectProperty.HasMonoEmbedding
      (fun A : 𝒜 ↦ IsBoundedBelowRightAcyclicForAdditiveFunctor F A) where
  exists_mono A := by
    -- Proof comment: choose `A` itself; exactness already makes it bounded-below right acyclic.
    refine ⟨A, is_bounded_below_right_acyclic_of_exact (F := F) A, 𝟙 A, inferInstance⟩

-- Proof sketch: termwise bounded-below right acyclicity is now immediate from the objectwise
-- degree-zero statement above.
/-- Helper for Lemma 13.16.9: every bounded-below complex is termwise bounded-below right acyclic
for an exact functor. -/
lemma is_termwise_bounded_below_right_acyclic_of_exact (K : K⁺(𝒜)) :
    IsTermwiseBoundedBelowRightAcyclicForAdditiveFunctor F K := by
  -- Proof comment: apply the previous objectwise acyclicity statement to each term of `K`.
  intro n
  exact is_bounded_below_right_acyclic_of_exact (F := F) (K.obj.as.X n)

-- Proof sketch: Proposition `13.16.8` gives bounded-below existence once every object admits a
-- monomorphism into a right-acyclic one. For an exact functor, part `(1)` makes the identity
-- `A ⟶ A` such a monomorphism.
/-- Lemma 13.16.9 (2): the bounded-below right derived functor of the exact functor `F` is
everywhere defined. -/
@[stacks 015F]
instance mapBoundedBelowHomotopyCategoryToDerivedBelow_hasRightDerivedFunctor :
    Functor.HasRightDerivedFunctor KplusToDplus QisPlus := by
  -- Proof comment: Proposition `13.16.8` applies because every object is already bounded-below
  -- right acyclic, so the identity morphism supplies the required monomorphism.
  let _ :
      ObjectProperty.HasMonoEmbedding
        (fun A : 𝒜 ↦ IsBoundedBelowRightAcyclicForAdditiveFunctor F A) :=
    bounded_below_right_acyclic_has_mono_embedding (F := F)
  exact boundedBelow_hasRightDerivedFunctor_of_mono_into_boundedBelowRightAcyclic (F := F)

-- Proof sketch: once every object is right acyclic for `F`, every bounded-below complex is
-- termwise right acyclic, so Proposition `13.16.8` computes the bounded-below right derived
-- functor at any object of `K^+(\mathcal A)`.
/-- Every bounded-below complex computes the bounded-below right derived functor of an exact
functor. -/
theorem computesRightDerivedFunctorAt_boundedBelow_of_exact (K : K⁺(𝒜)) :
    Functor.ComputesRightDerivedAt KplusToDplus QisPlus K := by
  -- Proof comment: Proposition `13.16.8` reduces computation to termwise bounded-below
  -- right acyclicity, already established for exact functors.
  exact
    computesRightDerivedFunctorAt_of_termwise_boundedBelowRightAcyclic
      (F := F) K
      (is_termwise_bounded_below_right_acyclic_of_exact (F := F) K)

-- Proof sketch: exact functors send quasi-isomorphisms to isomorphisms after passage to the
-- derived category, so the comparison component `F.mapDerivedCategoryFactors.inv.app K` is an
-- isomorphism for every homotopy object `K`.
/-- Lemma 13.16.9 (4): every complex computes the unbounded right derived functor of an exact
functor. -/
@[stacks 015F]
theorem computesRightDerivedFunctorAt_of_exact (K : HomotopyCategory 𝒜 (up ℤ)) :
    Functor.ComputesRightDerivedAt KtoD Qish K := by
  -- Proof comment: this is exactly the all-complexes helper proved from the localization
  -- factorization of `F.mapDerivedCategory`.
  exact computes_right_derived_at_all_complexes_of_exact (F := F) K

-- Proof sketch: after choosing any bounded-below right derived functor `RF` of `F`, part `(2)`
-- gives that every degree-zero complex `A[0]` computes it. Lemma `13.16.4` then identifies
-- bounded-below right acyclicity with the vanishing of the positive bounded-below right derived
-- functors determined by `RF`.
/-- Lemma 13.16.9 (5), source-facing bounded-below form: for any bounded-below right derived
functor `RF` of an exact functor `F`, the positive bounded-below right derived functors of `F`
vanish on every object. -/
@[stacks 015F]
theorem boundedBelowHigherRightDerivedVanishes_of_exact
    [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization QisPlus]
    (RF : D⁺(𝒜) ⥤ D⁺(𝒝))
    (α : KplusToDplus ⟶ DplusQ ⋙ RF)
    [RF.IsRightDerivedFunctor α QisPlus] [RF.CommShift ℤ] [RF.IsTriangulated]
    (A : 𝒜) :
    RF.boundedBelowHigherRightDerivedVanishes A := by
  -- Proof comment: Lemma `13.16.4` identifies bounded-below right acyclicity with vanishing of
  -- the higher bounded-below right derived functors, and exactness gives that acyclicity.
  exact
    (isBoundedBelowRightAcyclicForAdditiveFunctor_iff_boundedBelowHigherRightDerivedVanishes
      (F := F) (RF := RF) (α := α) A).1
      (is_bounded_below_right_acyclic_of_exact (F := F) A)

section

variable [HasInjectiveResolutions 𝒜]

-- Proof sketch: under injective resolutions, the unbounded owner `higherRightDerivedVanishes F`
-- is the stronger companion to the bounded-below theorem above. Exactness implies left exactness,
-- so Lemma `13.16.4` identifies right acyclicity with vanishing of the positive unbounded right
-- derived functors, and part `(1)` supplies that acyclicity.
/-- Stronger-assumption companion to Lemma 13.16.9 (5): assuming injective resolutions exist, the
unbounded higher right derived functors of an exact functor vanish on every object. -/
theorem higherRightDerivedVanishes_of_exact (A : 𝒜) :
    F.higherRightDerivedVanishes A := by
  exact
    (isRightAcyclicForAdditiveFunctor_iff_higherRightDerivedVanishes
      F A).1
      (isRightAcyclicForAdditiveFunctor_of_exact F A)

end

end CategoryTheory
