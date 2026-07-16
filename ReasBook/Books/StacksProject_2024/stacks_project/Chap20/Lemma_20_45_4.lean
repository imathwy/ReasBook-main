import StacksProject_2024.stacks_project.Chap13.Definition_13_27_1
import StacksProject_2024.stacks_project.Chap20.Lemma_20_45_2
import StacksProject_2024.stacks_project.Chap20.Situation_20_45_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped DerivedExt

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

/- Domain-style sampling for Lemma 20.45.4:
- primary domain: uniqueness and negative Ext-vanishing for global realizations of a basiswise
  derived gluing datum on a ringed space;
- sampled canonical declarations:
  `OpenFamilyDerivedGluing.Realizes`,
  `OpenFamilyDerivedGluing.RealizationIso`,
  `OpenFamilyDerivedGluing.IsRealization`,
  `OpenFamilyDerivedGluing.IsCompatibleIso`,
  `TopologicalSpace.IsTopologicalBasis`,
  `isTopologicalBasis_generateFrom`,
  `preimage_negative_ext_isZero_on_all_opens`,
  `preimage_zero_derivedHom_presheaf_isSheaf`,
  `OpenFamilyDerivedGluing.NegativeSelfExtVanishing`;
- best owner abstraction: the source-facing owner `OpenFamilyDerivedGluing`, with the intrinsic
  realization predicate `glue.Realizes K` as the public owner for "K realizes the datum", while
  explicit realization identifications remain auxiliary data only where the theorem must mention
  compatibility against chosen local comparison maps;
- primitive data: a gluing datum `glue`, the source-faithful cover and overlap hypotheses on
  `𝓑`, ambient derived objects `K, L`, and, only for the uniqueness statement, explicit
  realization identifications on them;
- derived API: compatible isomorphisms between explicit realizations and global negative
  self-Ext vanishing for an intrinsically realized ambient object.

Source/core/bridge triage:
- `source-facing`: the uniqueness and negative self-Ext consequences for realizations of the
  gluing datum under the explicit Stacks cover and overlap hypotheses on `𝓑`;
- `core/canonical`: the owner `OpenFamilyDerivedGluing` together with `Realizes`,
  `RealizationIso`, `IsRealization`, and the derived restriction
  functor `moduleRestrictionToOpenDerived`, together with the canonical basis owner
  `TopologicalSpace.IsTopologicalBasis`;
- `bridge/view`: the internal passage from the explicit cover/overlap hypotheses to the canonical
  basis owner, and the sheaf of degree-zero derived-Homs used to pass from basiswise
  compatibility to a unique global isomorphism.

This file therefore keeps the source-facing consequences for ambient realizations of
`OpenFamilyDerivedGluing`, while the all-open Ext-vanishing and degree-zero derived-Hom sheaf
owners remain the upstream bridge API from Lemma `20.45.2` rather than a second local owner
layer. The Grothendieck-abelian structure on `RingedSpace.Modules X` and the monoidal-closed
infrastructure used in the proof route stay as local proof support, not public theorem inputs.
-/

namespace OpenFamilyDerivedGluing

local notation "DModX" => ModuleDerived X

variable
    (glue : OpenFamilyDerivedGluing X 𝓑)

local instance : IsGrothendieckAbelian.{u} (RingedSpace.Modules X) :=
  sheafModules_isGrothendieckAbelian X

variable
    (hcover : sSup 𝓑 = ⊤)
    (hoverlap :
      ∀ ⦃U V : Opens X.carrier⦄ (_ : U ∈ 𝓑) (_ : V ∈ 𝓑),
        U ⊓ V = sSup {W : Opens X.carrier | W ∈ 𝓑 ∧ W ≤ U ⊓ V})
    (hneg : NegativeSelfExtVanishing glue)

-- Proof sketch: apply Lemma `20.45.2` to the degree-zero derived-Hom presheaf of two realized
-- ambient derived objects. The basiswise negative Ext vanishing forces that presheaf to be a
-- sheaf, so the local comparison isomorphisms glue to a unique global isomorphism. Internally,
-- the explicit cover and overlap hypotheses recover the canonical basis owner needed for the
-- upstream sheaf argument.
/-- Lemma 20.45.4 (1): assume `X = ⋃_{U ∈ 𝓑} U`, each overlap `U ∩ V` with `U, V ∈ 𝓑` is the
union of members of `𝓑` contained in `U ∩ V`, and the local objects of the gluing problem have
vanishing negative self-Ext groups. Then any two realizations are uniquely isomorphic in a way
compatible with the gluing data. -/
@[stacks 0D68]
theorem existsUniqueIso
    (K L : DModX)
    (isoK : glue.RealizationIso K) (hisoK : glue.IsRealization K isoK)
    (isoL : glue.RealizationIso L) (hisoL : glue.IsRealization L isoL) :
    ∃! e : K ≅ L, glue.IsCompatibleIso isoK isoL e := sorry

-- Proof sketch: apply the same derived-Hom sheaf argument as in part `(1)` to one realized
-- ambient object against itself. The local negative self-Ext vanishing hypothesis implies that
-- the negative derived endomorphism groups vanish on every member of `𝓑`, hence globally as
-- well after passing through the same cover/overlap-to-basis bridge.
/-- Lemma 20.45.4 (2): under the same cover, overlap, and negative-Ext hypotheses, every
realization has vanishing negative self-Ext groups `Ext^i(K, K)` for `i < 0`. -/
@[stacks 0D68]
theorem negativeSelfExt_isZero
    (K : DModX)
    (hK : glue.Realizes K)
    (i : ℤ) (hi : i < 0) :
    IsZero (AddCommGrpCat.of (Ext^i(K, K))) := sorry

end OpenFamilyDerivedGluing

end

end AlgebraicGeometry.RingedSpace
