import StacksProject_2024.stacks_project.Chap20.Remark_20_45_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

namespace OpenFamilyDerivedGluing

local instance : IsGrothendieckAbelian.{u} (RingedSpace.Modules X) :=
  sheafModules_isGrothendieckAbelian X

local notation "OpenX" => Opens X.carrier
local notation "DModX" => ModuleDerived X

/- Domain-style sampling for Lemma 20.45.6:
- primary domain: gluing derived `𝒪_X`-modules on a finite open cover of a ringed space,
  with existence and uniqueness measured by the canonical ambient-realization owners attached to
  `OpenFamilyDerivedGluing`;
- sampled canonical declarations:
  `OpenFamilyDerivedGluing.Realizes`,
  `OpenFamilyDerivedGluing.RealizationIso`,
  `OpenFamilyDerivedGluing.IsRealization`,
  `OpenFamilyDerivedGluing.IsCompatibleIso`,
  `OpenFamilyDerivedGluing.NegativeSelfExtVanishing`,
  `OpenFamilyDerivedGluing.OverlapGeneratedByBasis`,
  `OpenFamilyDerivedGluing.existsUniqueIso`,
  `sheafModules_isGrothendieckAbelian`;
- best owner abstraction:
  `source-facing`: the finite-cover gluing statement of the source item;
  `core/canonical`: `OpenFamilyDerivedGluing.Realizes`,
    `OpenFamilyDerivedGluing.IsCompatibleIso`, `OpenFamilyDerivedGluing.existsUniqueIso`,
    `NegativeSelfExtVanishing`, and the reusable overlap predicate
    `OpenFamilyDerivedGluing.OverlapGeneratedByBasis`;
  `bridge/view`: the finite cover by members of `𝓑` together with
    `OpenFamilyDerivedGluing.OverlapGeneratedByBasis X 𝓑`,
    which are weaker than the later basis-wide BBD assumptions and therefore must remain explicit
    in this lemma rather than being collapsed to `Opens.IsBasis`.
- primitive data: the gluing datum, a finite family of basis opens covering `X`, and the
  pairwise overlap-generation hypothesis packaged by
  `OpenFamilyDerivedGluing.OverlapGeneratedByBasis X 𝓑`;
- derived API: existence of an ambient realizing object expressed by `glue.Realizes`, together
  with uniqueness up to a unique compatible isomorphism between any two explicit realizations.

This file therefore keeps the source-facing finite-cover theorem and reuses the canonical owner
`OpenFamilyDerivedGluing` together with its realization predicate `Realizes` and the canonical
uniqueness API `existsUniqueIso`, while exposing the pairwise-intersection hypothesis through the
shared Chapter 20 owner `OverlapGeneratedByBasis` instead of repeating its defining formula in a
second public statement. As in the chapter's other finite-cover statements, the cover itself is
presented by a general finite index type rather than by an ordered enumeration `Fin n`, since no
order data enters the mathematics of this lemma. The Grothendieck-abelian structure on
`RingedSpace.Modules X` is proof support supplied canonically by
`sheafModules_isGrothendieckAbelian X`, not part of the public theorem inputs, and the monoidal
structure used to form negative Ext groups stays in the background rather than entering the public
statement.
-/

-- Proof sketch: choose an enumeration of the finite index type and argue by induction on its
-- cardinality. The base case is immediate. For the induction step, glue a solution on the union
-- of all but one covering open to the remaining local object using Lemma `20.45.1`, while Lemma
-- `20.45.4` provides the uniqueness clause.
/-- Lemma 20.45.6: if `X` is covered by finitely many opens in `𝓑`, the pairwise intersections of
members of `𝓑` are unions of smaller members of `𝓑`, and the local derived objects of the gluing
datum have vanishing negative self-Ext groups, then a realizing ambient derived object exists and
any two explicit realizations are uniquely isomorphic in a compatible way. -/
@[stacks 0D6A]
theorem exists_realization_uniqueUpToUniqueIso_of_finite_cover
    (glue : OpenFamilyDerivedGluing X 𝓑)
    {ι : Type u} [Finite ι]
    (cover : ι → OpenX)
    (hcover_mem : ∀ i, cover i ∈ 𝓑)
    (hcover : iSup cover = ⊤)
    (hoverlap : OverlapGeneratedByBasis X 𝓑)
    (hneg : NegativeSelfExtVanishing glue) :
    (∃ K : DModX, glue.Realizes K) ∧
      ∀ (K L : DModX)
        (isoK : glue.RealizationIso K) (hisoK : glue.IsRealization K isoK)
        (isoL : glue.RealizationIso L) (hisoL : glue.IsRealization L isoL),
        ∃! e : K ≅ L, glue.IsCompatibleIso isoK isoL e := by
  sorry

end OpenFamilyDerivedGluing

end

end AlgebraicGeometry.RingedSpace
