import StacksProject_2024.stacks_project.Chap20.Lemma_20_49_11
import StacksProject_2024.stacks_project.Chap20.Lemma_20_55_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open _root_.AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped IdealEtaComplex

section

variable {X : RingedSpace.{u}}
variable [(Opens.grothendieckTopology X.carrier).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [BraidedCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [MonoidalClosed (RingedSpace.Modules X)]
local notation "ModX" => RingedSpace.Modules X
local notation "DModX" => DerivedCategory ModX
local notation "𝒪X" => SheafOfModules.unit X.ringCatSheaf

/- Domain-style sampling for Lemma 20.55.10:
- primary domain: stalks of cohomology sheaves in `D(𝒪_X)` and the Berthelot-Ogus
  derived endofunctor in Situation `20.55.2`;
- sampled owner declarations:
  `RingedSpace.stalkModuleCat`,
  `ModuleDerived.cohomologyStalk`,
  `ModuleDerived.cohomologyStalkIsFiniteFree`,
  `Functor.IsIdealEtaDerived`,
  `idealEtaDerivedFunctor_obj_isomorphic`,
  `(ℐ ^⊗ i)`;
- best owner abstraction: the source-facing owner layer is the cohomology stalk
  `E.cohomologyStalk i x` over the stalk ring `𝒪_{X, x}`, with finite-freeness
  recorded by `E.cohomologyStalkIsFiniteFree i x`; the Berthelot-Ogus derived object is now an
  arbitrary endofunctor `F : D(𝒪_X) ⥤ D(𝒪_X)` carrying the owner
  `Functor.IsIdealEtaDerived I F`, and Lemma `20.55.7` supplies the bridge
  from that owner to the complex-level Berthelot-Ogus model; the tensor-power factor
  `𝓘_x^⊗ i` remains canonical via `(ℐ ^⊗ i)` and `RingedSpace.stalkModuleCat`;
- primitive data: an ideal sheaf `I : Subobject 𝒪_X` satisfying
  `SatisfiesLocallyPrincipalRegularIdealCondition`, a derived object `M`, a point `x` with
  nontrivial stalk ring, a degree `i`, and finite freeness of `H^i(M)_x`;
- derived API: finite freeness of
  `H^i((Lη[I]).obj M)_x` and equality of its rank with the rank of
  `H^i(M)_x`.

Source/core/bridge triage:
- `source-facing`: the two stalk-level conclusions of Lemma `20.55.10`;
- `core/canonical`: `RingedSpace.stalkModuleCat`, `ModuleDerived.cohomologyStalk`,
  `ModuleDerived.cohomologyStalkIsFiniteFree`, `Functor.IsIdealEtaDerived`, and `Module.rank`;
- `bridge/view`: `idealEtaDerivedFunctor_obj_isomorphic` together with the stalkwise tensor-power
  comparison from Lemma `20.55.5`.
-/

section

variable (I : Subobject 𝒪X)
variable [SatisfiesLocallyPrincipalRegularIdealCondition I]
variable (M : DModX) (i : ℤ) (x : X)

local notation "R" => X.presheaf.stalk x

section

-- Proof sketch: compute `F.obj M` via the Berthelot-Ogus comparison supplied by
-- `Functor.IsIdealEtaDerived I F`, use the canonical
-- comparison from Lemmas `20.55.7` and `20.55.5` to identify the stalk cohomology with
-- `𝓘_x^⊗ i ⊗_{𝒪_{X, x}} H^i(M)_x`, choose a regular generator of
-- the principal stalk ideal `𝓘_x`, identify every tensor power `𝓘_x^⊗ i`
-- with a free rank-one `𝒪_{X, x}`-module through multiplication by that generator, and
-- conclude that the tensor product is finite free.
/-- Lemma 20.55.10: let `x ∈ X` be a point whose stalk ring `𝒪_{X, x}` is nonzero. If
`H^i(M)_x` is finite free over `𝒪_{X, x}`, then `H^i(F(M))_x` is finite free
over `𝒪_{X, x}` for any Berthelot-Ogus derived functor `F`. -/
@[stacks 0GTA]
theorem cohomologyStalkIsFiniteFree_idealEtaDerivedFunctor
    (F : DModX ⥤ DModX) [Functor.IsIdealEtaDerived I F]
    (hR : Nontrivial R)
    (hM : M.cohomologyStalkIsFiniteFree i x) :
    (F.obj M).cohomologyStalkIsFiniteFree i x := sorry

-- Proof sketch: after the same canonical comparison with
-- `𝓘_x^⊗ i ⊗_{𝒪_{X, x}} H^i(M)_x`, use the same regular-generator
-- trivialization of `𝓘_x^⊗ i` to identify that tensor product with
-- `H^i(M)_x`; then `LinearEquiv.rank_eq` transports the resulting rank equality back to the
-- cohomology stalk of `F.obj M`.
/-- Under the same hypotheses, the stalk cohomology of `F.obj M` has the same
`𝒪_{X, x}`-module rank as the stalk cohomology of `M`, for any Berthelot-Ogus derived
functor `F`. -/
theorem rank_derivedCohomologyStalk_eq_idealEtaDerivedFunctor
    (F : DModX ⥤ DModX) [Functor.IsIdealEtaDerived I F]
    (hR : Nontrivial R)
    (hM : M.cohomologyStalkIsFiniteFree i x) :
    Module.rank R ((F.obj M).cohomologyStalk i x) =
      Module.rank R (M.cohomologyStalk i x) := sorry

end

end

end

end AlgebraicGeometry.RingedSpace
