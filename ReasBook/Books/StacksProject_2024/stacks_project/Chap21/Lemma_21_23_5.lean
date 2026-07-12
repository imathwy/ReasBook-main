import StacksProject_2024.Chap07.Definition_7_40_2
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap21.Lemma_21_20_3
import StacksProject_2024.Chap21.Lemma_21_20_7_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open RingedSite.Hom
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 21.23.5:
- primary domain: sequential derived inverse limits of `𝒪_X`-modules and their
  objectwise cohomology over a basis on a ringed site;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `RingedSite.Hom.cohomologyOverObject`,
  `RingedSite.Hom.cohomologySheaf`,
  `RingedSite.Hom.moduleSectionsAsAbelianFunctor`,
  `RingedSite.Hom.moduleSectionsAsAbelianDerived`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`,
  `singleFunctorIso_of_isGE_of_isLE`,
  `CategoryTheory.SequentialInverseSystem.firstDerivedLimit`;
- best owner abstraction: the ambient module category is the canonical ringed-site owner
  `RingedSite.Hom.ModuleCat X`, already introduced upstream in Lemma `21.20.5`, while the
  objectwise derived cohomology owner is already `H^p(U, K)` / `cohomologyOverObject` from
  Lemma `21.20.3`; the source-facing first assertion of the Stacks lemma is an object statement in
  `D(𝒪_X)`, so the best owner for the main entry is the canonical degree-zero
  identification supplied by the boundedness owners `K.IsGE 0`, `K.IsLE 0`, and
  `singleFunctorIso_of_isGE_of_isLE`; the degree-zero module-sheaf specialization should
  therefore be expressed directly as `H^p(U, ℱ[0])`, not by a parallel public wrapper; the
  additive sections bridge is
  canonically owned by
  `moduleSectionsAsAbelianFunctor X U` and its derived functor
  `moduleSectionsAsAbelianDerived X U` from Lemma `21.20.7`; the Milnor
  `R¹ lim←` term is canonically owned by
  `SequentialInverseSystem.firstDerivedLimit`, not by a local cokernel wrapper;
- primitive data: a ringed site `X`, a basis candidate `B`, a sequential tower
  `Fsys : ℕᵒᵖ ⥤ ModuleCat X`, and a chosen derived limit `K` of the degree-zero tower;
- derived API: the local degree-zero notation `single0`, the two cohomology-sheaf companion
  consequences, and the basiswise vanishing theorem obtained after identifying `K` with the
  degree-zero limit object.

Source/core/bridge triage:
- `source-facing`: the object-level identification
  `R lim←_n 𝓕_n ≅ (lim←_n 𝓕_n)[0]` and the resulting
  basiswise vanishing statement;
- `core/canonical`: `ModuleCat`, `ModuleDerived`,
  `cohomologyOverObject`, `cohomologySheaf`,
  `moduleSectionsAsAbelianFunctor`, `moduleSectionsAsAbelianDerived`, and
  `DerivedCategory.IsGE`, `DerivedCategory.IsLE`,
  `singleFunctorIso_of_isGE_of_isLE`, and `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: the local degree-zero notation `single0` used only to keep the source-facing
  theorem statements short. -/

section

variable (X : RingedSite.{u, v})
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

local notation "ModX" => ModuleCat X
local notation "DModX" => ModuleDerived X
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)

variable (B : Set X)
variable (Fsys : ℕᵒᵖ ⥤ ModX)
variable (K : DModX)

/-- Basiswise higher-cohomology vanishing for the degree-zero stages `𝓕_n[0]` of a sequential
inverse system of `𝒪_X`-modules. -/
def BasiswiseSingleAcyclic (B : Set X) (Fsys : ℕᵒᵖ ⥤ ModX) : Prop :=
  ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ p : ℤ, 0 < p →
    IsZero (H^p(U, (single0).obj (Fsys.obj (op n))))

/-- Basiswise vanishing of `R¹ lim←` for the towers of sections of a sequential inverse system of
`𝒪_X`-modules. -/
def BasiswiseFirstDerivedLimitIsZero (B : Set X) (Fsys : ℕᵒᵖ ⥤ ModX) : Prop :=
  ∀ U : X, U ∈ B →
    IsZero
      (SequentialInverseSystem.firstDerivedLimit
        (Fsys ⋙ moduleSectionsAsAbelianFunctor X U))

-- Proof sketch: each stage of `Fsys ⋙ single0` is already concentrated in degree `0`, so the
-- negative-degree objectwise cohomology terms in Remark `21.23.4` vanish without any basiswise
-- acyclicity or `R¹ lim←` input. Lemma `21.20.3` then upgrades this objectwise vanishing to the
-- canonical bounded-below owner `K.IsGE 0`.
/-- Companion to Lemma 21.23.5 (1): a chosen derived limit of a sequential inverse system of
degree-zero objects is automatically bounded below, i.e. it lies in `D^{≥ 0}`. -/
theorem derivedLimit_isGE_zero_of_single0
    (hK : IsDerivedLimit (Fsys ⋙ single0) K) :
    K.IsGE 0 := sorry

-- Proof sketch: apply Remark `21.23.4` objectwise on each `U ∈ B`. The positive-degree terms
-- vanish by hypothesis, and the `R¹ lim←` term on sections vanishes by assumption, so
-- every positive-degree objectwise cohomology group of `K` vanishes on the basis. Lemma `21.20.3`
-- upgrades these basiswise vanishings to the cohomology sheaves, yielding the canonical
-- bounded-above owner `K.IsLE 0`.
/-- Companion to Lemma 21.23.5 (1): under the basiswise acyclicity and `R¹ lim←`
hypotheses, the chosen derived limit `K = R lim←_n 𝓕_n` has no positive
cohomology, i.e. `K ∈ D^{≤ 0}`. -/
theorem derivedLimit_isLE_zero_of_basiswise_acyclic
    (hK : IsDerivedLimit (Fsys ⋙ single0) K)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hacyclic : BasiswiseSingleAcyclic X B Fsys)
    (hR1lim : BasiswiseFirstDerivedLimitIsZero X B Fsys) :
    K.IsLE 0 := sorry

-- Proof sketch: combine the two boundedness companions
-- `derivedLimit_isGE_zero_of_single0` and
-- `derivedLimit_isLE_zero_of_basiswise_acyclic` with the canonical owner
-- `singleFunctorIso_of_isGE_of_isLE`. The degree-zero cohomology sheaf of `K` is the ordinary
-- inverse limit sheaf `lim←_n 𝓕_n`, so the resulting single-degree model is
-- exactly `(lim←_n 𝓕_n)[0]`.
/-- Lemma 21.23.5 (1): if a subset `B` covers the ringed site `X`, if every stage `𝓕_n`
has vanishing higher cohomology on objects of `B`, and if the section towers
`n ↦ 𝓕_n(U)` have vanishing `R¹ lim←` for `U ∈ B`, then a chosen derived
limit `K = R lim←_n 𝓕_n` is canonically isomorphic in `D(𝒪_X)` to the
ordinary inverse limit sheaf placed in degree `0`. -/
@[stacks 0BKY]
theorem derivedLimit_isomorphic_degreeZeroLimit_of_basiswise_acyclic
    (hK : IsDerivedLimit (Fsys ⋙ single0) K)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hacyclic : BasiswiseSingleAcyclic X B Fsys)
    (hR1lim : BasiswiseFirstDerivedLimitIsZero X B Fsys) :
    IsIsomorphic
      K
      ((single0).obj (limit Fsys)) := sorry

-- Proof sketch: use Remark `21.23.4` objectwise on each `U ∈ B`. Since every stage `𝓕_n`
-- is concentrated in degree `0` and has no higher cohomology on `U`, the Milnor exact sequence
-- shows the higher objectwise cohomology of the chosen derived limit `K` vanishes on `B`. Then
-- Lemma `21.20.3` identifies the cohomology sheaf with the sheafification of this basiswise-zero
-- presheaf, so the higher cohomology sheaves of `K` vanish.
/-- Companion to Lemma 21.23.5 (1): every nonzero cohomology sheaf of the chosen derived limit
`K = R lim←_n 𝓕_n` vanishes under the basiswise acyclicity and
`R¹ lim←` hypotheses. -/
theorem derivedLimit_higherCohomologySheaf_isZero_of_basiswise_acyclic
    (hK : IsDerivedLimit (Fsys ⋙ single0) K)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hacyclic : BasiswiseSingleAcyclic X B Fsys)
    (hR1lim : BasiswiseFirstDerivedLimitIsZero X B Fsys)
    (q : ℤ) (hq : q ≠ 0) :
    IsZero (𝓗[q](X, K)) := sorry

-- Proof sketch: apply the same objectwise Milnor exact sequence on each `U ∈ B`. The positive
-- degree terms vanish by hypothesis, and the `R¹ lim←` term on sections vanishes by
-- assumption, so the degree-zero objectwise cohomology of `K` identifies with
-- `lim←_n 𝓕_n(U)` on the basis. Sheafifying with Lemma `21.20.3` identifies the
-- degree-zero cohomology sheaf of `K` with the ordinary inverse limit sheaf.
/-- Companion to Lemma 21.23.5 (1): the degree-zero cohomology sheaf of the chosen derived limit
`K = R lim←_n 𝓕_n` is isomorphic to the ordinary inverse limit sheaf
`lim←_n 𝓕_n`. -/
theorem derivedLimit_zeroCohomologySheaf_isomorphic_limit_of_basiswise_acyclic
    (hK : IsDerivedLimit (Fsys ⋙ single0) K)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hacyclic : BasiswiseSingleAcyclic X B Fsys)
    (hR1lim : BasiswiseFirstDerivedLimitIsZero X B Fsys) :
    IsIsomorphic
      (𝓗[0](X, K))
      (limit Fsys) := sorry

-- Proof sketch: combine the object-level identification from part `(1)` with the basiswise
-- acyclicity of the chosen derived limit `K`. Evaluating over a basis object `U ∈ B` then
-- identifies the higher cohomology of the ordinary inverse limit sheaf with that of `K`.
/-- Lemma 21.23.5 (2): under the same hypotheses, the ordinary inverse limit sheaf
`lim←_n 𝓕_n` has vanishing higher cohomology on every basis object `U ∈ B`. -/
@[stacks 0BKY]
theorem limit_objectwiseCohomology_isZero_of_basiswise_acyclic
    (hK : IsDerivedLimit (Fsys ⋙ single0) K)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hacyclic : BasiswiseSingleAcyclic X B Fsys)
    (hR1lim : BasiswiseFirstDerivedLimitIsZero X B Fsys)
    (U : X) (hU : U ∈ B) (p : ℤ) (hp : 0 < p) :
    IsZero (H^p(U, (single0).obj (limit Fsys))) := sorry

end
