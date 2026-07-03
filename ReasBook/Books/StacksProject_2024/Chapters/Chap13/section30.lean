import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_30_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.MorphismProperty
open Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  {S : MorphismProperty D} {S' : MorphismProperty D'}
  {F : D ⥤ D'} {G : D' ⥤ D}

/- Domain-style sampling:
- primary domain: pointwise left/right derived values along localization functors, together with
  the Hom-set comparison induced by an underived adjunction;
- sampled owner declarations:
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.HasPointwiseLeftDerivedFunctorAt`,
  `CategoryTheory.rightDerivedValue`,
  `CategoryTheory.leftDerivedValue`,
  `Adjunction.homEquiv`;
- owner abstraction:
  `source-facing`: the Stacks lemma compares the localized Hom-sets attached to the chosen
    pointwise derived values at `K` and `M`;
  `core/canonical`: the project owners `rightDerivedValue` / `leftDerivedValue` built on the
    mathlib pointwise derived-functor API, together with the underived adjunction owner
    `Adjunction.homEquiv`;
  `bridge/view`: the owner introduced in this file,
    `Adjunction.pointwiseDerivedHomEquiv`, built directly from those canonical ingredients.

Primitive data are exactly the adjunction `adj : G ⊣ F` and the pointwise derivability hypotheses
at the two chosen objects. The Hom-set equivalence is derived API, so this file should expose that
equivalence directly rather than through a second public wrapper family. We keep this source-facing
bridge instead of collapsing it to `Adjunction.derived`, because that functor-level owner requires
stronger absolute-derived hypotheses and would change the local source semantics.
-/

-- Proof sketch: express `Hom_{(S')⁻¹D'}(M, RF(K))` and `Hom_{S⁻¹D}(LG(M), K)` using the
-- pointwise right/left derived-value constructions together with the localization Hom-colimit
-- formulas from Chapter 4. Then commute the two colimits, apply the underived adjunction
-- `adj.homEquiv` termwise, and transport the result back to the localized Hom-sets.
namespace Adjunction

/-- Internal notation for the source Hom-set in Lemma 13.30.1. -/
private abbrev pointwiseDerivedHomSource
    (F : D ⥤ D') (S : MorphismProperty D) (S' : MorphismProperty D')
    (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K] :=
  (S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K

/-- Internal notation for the target Hom-set in Lemma 13.30.1. -/
private abbrev pointwiseDerivedHomTarget
    (G : D' ⥤ D) (S : MorphismProperty D) (S' : MorphismProperty D') (M : D') (K : D)
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :=
  leftDerivedValue S' (G ⋙ S.Q) M ⟶ S.Q.obj K

private def IsCanonicalPointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M]
    (e : pointwiseDerivedHomSource F S S' K M ≃ pointwiseDerivedHomTarget G S S' M K) : Prop :=
  ∀ {K' : D} {M' : D'} (m : M ⟶ M') (hm : S' m) (k : K ⟶ K') (hk : S k)
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M']
    (φ : M' ⟶ F.obj K'),
      e (S'.Q.map m ≫ S'.Q.map φ ≫ rightDerivedValueLeg S (F ⋙ S'.Q) k hk) =
        leftDerivedValueMap S' (G ⋙ S.Q) m ≫
          leftDerivedValueProjection S' (G ⋙ S.Q) m hm ≫
          S.Q.map (G.map m ≫ (adj.homEquiv M' K').symm φ) ≫
          (Localization.isoOfHom S.Q S k hk).inv

-- Proof sketch: construct the comparison family by transporting the Chapter 4 left/right
-- localization Hom descriptions through the underived adjunction `adj.homEquiv`, then descend
-- through the pointwise right/left derived-value presentations. The same denominator formulas
-- give both naturality laws and the normalization on basic fraction generators, and these three
-- clauses characterize the family uniquely.
private theorem existsUnique_pointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :
    ∃! e : pointwiseDerivedHomSource F S S' K M ≃ pointwiseDerivedHomTarget G S S' M K,
      IsCanonicalPointwiseDerivedHomEquiv adj S S' K M e := by
  sorry

/-- Lemma 13.30.1: if `F` is right adjoint to `G`, if the pointwise right derived value of
`F ⋙ S'.Q` is defined at `K`, and if the pointwise left derived value of `G ⋙ S.Q` is defined at
`M`, then the localized Hom-sets
`Hom_{(S')⁻¹\mathcal D'}(M, RF(K))` and `Hom_{S⁻¹\mathcal D}(LG(M), K)` are canonically
equivalent. -/
noncomputable def pointwiseDerivedHomEquiv
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :
    ((S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K) ≃
      (leftDerivedValue S' (G ⋙ S.Q) M ⟶ S.Q.obj K) :=
  Classical.choose (existsUnique_pointwiseDerivedHomEquiv adj S S' K M)

private theorem pointwiseDerivedHomEquiv_spec
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D') (K : D) (M : D')
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M] :
    IsCanonicalPointwiseDerivedHomEquiv adj S S' K M
      (pointwiseDerivedHomEquiv adj S S' K M) := by
  rcases Classical.choose_spec (existsUnique_pointwiseDerivedHomEquiv adj S S' K M) with ⟨he, -⟩
  exact he

theorem pointwiseDerivedHomEquiv_naturality_left
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    {K : D} {M₁ M₂ : D'} (m : M₁ ⟶ M₂)
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M₁]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M₂]
    (f : (S'.Q.obj M₂) ⟶ rightDerivedValue S (F ⋙ S'.Q) K) :
    adj.pointwiseDerivedHomEquiv S S' K M₁ ((S'.Q.map m) ≫ f) =
      leftDerivedValueMap S' (G ⋙ S.Q) m ≫ adj.pointwiseDerivedHomEquiv S S' K M₂ f :=
by
  sorry

theorem pointwiseDerivedHomEquiv_naturality_right
    (adj : G ⊣ F) (S : MorphismProperty D) (S' : MorphismProperty D')
    {K₁ K₂ : D} {M : D'} (k : K₁ ⟶ K₂)
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K₁]
    [(F ⋙ S'.Q).HasPointwiseRightDerivedFunctorAt S K₂]
    [(G ⋙ S.Q).HasPointwiseLeftDerivedFunctorAt S' M]
    (f : (S'.Q.obj M) ⟶ rightDerivedValue S (F ⋙ S'.Q) K₁) :
    adj.pointwiseDerivedHomEquiv S S' K₂ M (f ≫ rightDerivedValueMap S (F ⋙ S'.Q) k) =
      adj.pointwiseDerivedHomEquiv S S' K₁ M f ≫ S.Q.map k :=
by
  sorry

end Adjunction

end

end CategoryTheory

/-! ### Lemma_13_30_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open HomologicalComplex

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Adjunction

section

variable {C : Type u₁} {D : Type u₂} {ι : Type w}
  [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  {F : C ⥤ D} {G : D ⥤ C}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

/-- An adjunction `G ⊣ F` induces an adjunction on homological complexes of any fixed shape. -/
noncomputable def mapHomologicalComplex (adj : G ⊣ F) (c : ComplexShape ι) :
    G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c :=
  Adjunction.mkOfUnitCounit <|
    Adjunction.CoreUnitCounit.mk
      ((Functor.mapHomologicalComplexIdIso D c).inv ≫
        NatTrans.mapHomologicalComplex adj.unit c)
      (NatTrans.mapHomologicalComplex adj.counit c ≫
        (Functor.mapHomologicalComplexIdIso C c).hom)
      (by
        ext M i
        simp)
      (by
        ext K i
        simp)

end

section

variable {C : Type u₁} {D : Type u₂} {ι : Type w}
  [Category.{v₁} C] [Category.{v₂} D]
variable [Preadditive C] [Preadditive D]
variable {F : C ⥤ D} {G : D ⥤ C}
variable [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
variable [G.Additive]

/-- A homotopy between maps into `K` transports across the Hom-equivalence induced by
`adj.mapHomologicalComplex c`. -/
noncomputable def homotopy_mapHomologicalComplex_homEquiv
    (adj : G ⊣ F) (c : ComplexShape ι)
    {L : HomologicalComplex D c} {K : HomologicalComplex C c}
    {f g : (G.mapHomologicalComplex c).obj L ⟶ K} (h : Homotopy f g) :
    Homotopy
      (((adj.mapHomologicalComplex c).homEquiv L K) f)
      (((adj.mapHomologicalComplex c).homEquiv L K) g) := by
  letI : F.Additive := adj.right_adjoint_additive
  simpa [Adjunction.homEquiv_unit] using
    (F.mapHomotopy h).compLeft ((adj.mapHomologicalComplex c).unit.app L)

end

end Adjunction

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [HasZeroMorphisms 𝒜] [HasZeroMorphisms ℬ]
  [CategoryWithHomology 𝒜] [CategoryWithHomology ℬ]
  {F : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒜}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

local notation "QisA" => HomologicalComplex.quasiIso 𝒜 (up ℤ)
local notation "QisB" => HomologicalComplex.quasiIso ℬ (up ℤ)

/- Domain-style sampling:
- primary domain: pointwise left/right derived values on cochain complexes, compared through an
  underived adjunction between the base categories, at the quasi-isomorphism and homology layer;
- sampled owner declarations:
  `Adjunction.pointwiseDerivedHomEquiv`,
  `Adjunction.pointwiseDerivedHomEquiv_naturality_left`,
  `Adjunction.pointwiseDerivedHomEquiv_naturality_right`,
  `HomologicalComplex.quasiIso`,
  `MorphismProperty.Q`;
- owner abstraction:
  `source-facing`: the Stacks lemma comparing
    `Hom_{D(ℬ)}(M, RF(K))` and `Hom_{D(𝒜)}(LG(M), K)` for cochain complexes;
  `core/canonical`: `Adjunction.pointwiseDerivedHomEquiv` applied to the lifted adjunction on
    cochain complexes and the canonical localization functors `QisA.Q` and `QisB.Q`;
  `bridge/view`: `Adjunction.mapHomologicalComplex`, which lifts `G ⊣ F` to complexes.

Primitive data are the adjunction `adj : G ⊣ F` and the pointwise derivability hypotheses at
`K` and `M`. The Hom-equivalence and its two naturality identities are derived API, so this file
should expose them by reusing the owners above instead of rebuilding parallel local machinery.
-/

-- Proof sketch: specialize the general pointwise derived-adjunction construction to the
-- quasi-isomorphism localizations of cochain complexes in the two ambient categories. The
-- underived adjunction `G ⊣ F` is applied termwise on complexes, and Lemma `13.30.2` is exactly
-- the resulting specialization of the canonical owner from Lemma `13.30.1`.
section

variable (adj : G ⊣ F)

section

/- Lemma 13.30.2: for an adjoint pair `G ⊣ F` of additive functors between abelian categories,
if the pointwise right derived functor of `F` is defined at the complex `K` and the pointwise
left derived functor of `G` is defined at the complex `M`, then there is a canonical
isomorphism
`Hom_{D(\mathcal B)}(M^\bullet, RF(K^\bullet)) ≃ Hom_{D(\mathcal A)}(LG(M^\bullet), K^\bullet)`.
This recall is stated over the weaker canonical quasi-isomorphism layer:
`HasZeroMorphisms`, `CategoryWithHomology`, and the pointwise-derived hypotheses suffice for the
specialization of `Adjunction.pointwiseDerivedHomEquiv` along
`adj.mapHomologicalComplex (up ℤ)`. -/
#check (adj.mapHomologicalComplex (up ℤ)).pointwiseDerivedHomEquiv QisA QisB

end

section

/- The Hom-equivalence of Lemma 13.30.2 is natural in the complex of `ℬ`; this is the direct
specialization of `Adjunction.pointwiseDerivedHomEquiv_naturality_left` to cochain complexes and
quasi-isomorphisms. -/
#check (adj.mapHomologicalComplex (up ℤ)).pointwiseDerivedHomEquiv_naturality_left QisA QisB

end

section

/- The Hom-equivalence of Lemma 13.30.2 is natural in the complex of `𝒜`; this is the direct
specialization of `Adjunction.pointwiseDerivedHomEquiv_naturality_right` to cochain complexes and
quasi-isomorphisms. -/
#check (adj.mapHomologicalComplex (up ℤ)).pointwiseDerivedHomEquiv_naturality_right QisA QisB

end

end

end

end CategoryTheory

/-! ### Lemma_13_30_3 (from Chap13) -/
open CategoryTheory
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

namespace Adjunction

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ] [Abelian 𝒜] [Abelian ℬ]
  {F : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒜}
  [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

local notation "CpxA" => CochainComplex 𝒜 ℤ
local notation "CpxB" => CochainComplex ℬ ℤ
local notation "DA" => DerivedCategory 𝒜
local notation "DB" => DerivedCategory ℬ
local notation "Fcpx" => F.mapHomologicalComplex (up ℤ)
local notation "Gcpx" => G.mapHomologicalComplex (up ℤ)
local notation "QA" => (DerivedCategory.Q : CpxA ⥤ DA)
local notation "QB" => (DerivedCategory.Q : CpxB ⥤ DB)
local notation "QisA" => HomologicalComplex.quasiIso 𝒜 (up ℤ)
local notation "QisB" => HomologicalComplex.quasiIso ℬ (up ℤ)

/- Domain-style sampling for Lemma 13.30.3:
- primary domain: derived adjunctions for cochain-complex functors between derived categories of
  abelian categories;
- sampled owner declarations:
  `Adjunction.mapHomologicalComplex`,
  `Adjunction.pointwiseDerivedHomEquiv`,
  `Adjunction.mkOfHomEquiv`,
  `Functor.totalLeftDerived`,
  `Functor.totalRightDerived`;
- best owner abstraction:
  `source-facing`: the adjunction between the canonical total left derived functor `LG` of
    `Gcpx ⋙ QA` and the canonical total right derived functor `RF` of `Fcpx ⋙ QB`;
  `core/canonical`: the total-derived owners `Functor.totalLeftDerived` and
    `Functor.totalRightDerived`, together with the adjunction constructor `Adjunction.mkOfHomEquiv`;
  `bridge/view`: the cochain-complex lift `adj.mapHomologicalComplex (up ℤ)` and the pointwise
    Hom-set equivalence from `Lemma_13_30_2`.

Primitive data are the underived adjunction `adj : G ⊣ F` and the canonical total-derived
existence hypotheses for `Gcpx ⋙ QA` and `Fcpx ⋙ QB`. The objectwise Hom-equivalence and its
naturality are derived API supplied by `Lemma_13_30_2`, so the main declaration below keeps the
source-facing cochain specialization and does not expose the stronger absolute-derived composite
assumptions from `Adjunction.derived`.
-/

variable (adj : G ⊣ F)
variable [hL : Functor.HasLeftDerivedFunctor (Gcpx ⋙ QA) QisB]
variable [hR : Functor.HasRightDerivedFunctor (Fcpx ⋙ QB) QisA]

local notation "LG" =>
  (@Functor.totalLeftDerived _ _ _ _ _ _ (Gcpx ⋙ QA) QB QisB hL)
local notation "RF" =>
  (@Functor.totalRightDerived _ _ _ _ _ _ (Fcpx ⋙ QB) QA QisA hR)

-- Proof sketch: apply `Adjunction.mkOfHomEquiv` to the pointwise cochain-complex comparison from
-- Lemma `13.30.2`. The Hom-equivalence there identifies morphisms
-- `M ⟶ RF(K)` with morphisms `LG(M) ⟶ K` for complexes `M` and `K`; essential surjectivity of
-- `DerivedCategory.Q` upgrades these objectwise formulas to all objects of `D(ℬ)` and `D(𝒜)`,
-- and the naturality statements from Lemma `13.30.2` supply the two `CoreHomEquiv` axioms.
/-- Lemma 13.30.3: if `G ⊣ F`, if the canonical total left derived functor of
`Gcpx ⋙ DerivedCategory.Q` exists, and if the canonical total right derived functor of
`Fcpx ⋙ DerivedCategory.Q` exists, then these two total derived functors are adjoint. -/
noncomputable def derivedCochainComplex : LG ⊣ RF :=
  -- Package the Hom-equivalence from Lemma 13.30.2 as the `CoreHomEquiv` data.
  -- The required naturality fields are already built into `pointwiseDerivedHomEquiv`.
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M K ↦
        ((adj.mapHomologicalComplex (up ℤ)).pointwiseDerivedHomEquiv QisA QisB K M).symm }

end

end Adjunction

end CategoryTheory
