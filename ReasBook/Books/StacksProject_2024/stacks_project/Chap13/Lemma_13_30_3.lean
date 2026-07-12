import Mathlib
import StacksProject_2024.Chap13.Lemma_13_30_2

-- Declarations for this item will be appended below by the statement pipeline.

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
