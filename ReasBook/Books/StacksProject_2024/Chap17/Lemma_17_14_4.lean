import Mathlib
import StacksProject_2024.Chap17.Definition_17_14_1

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : RingedSpace.{u}}

private abbrev IsFreeOn (ℱ : RingedSpace.Modules X) (U : Opens X) (I : Type u) : Prop :=
  Nonempty
    (ℱ.over U ≅
      (SheafOfModules.free.{u} I :
        SheafOfModules.{u} ((RingedSpace.ringCatSheaf X).over U)))

/- Domain-style sampling for Lemma 17.14.4:
- primary domain: locally free sheaves of modules on ringed spaces and their rank functions;
- sampled owner declarations of the same kind:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `SheafOfModules.IsLocallyFree`,
  `ENat.card`,
  `Module.isLocallyConstant_rankAtStalk`;
- best owner abstraction: the ambient owner category `(RingedSpace.Modules X)` together with the owner
  predicate `SheafOfModules.IsLocallyFree`; the basis-size value is the canonical `ENat.card`;
- primitive data: a ringed space `X`, a module sheaf `ℱ : (RingedSpace.Modules X)`, and local freeness of
  `ℱ`;
- derived API: existence of a locally constant rank function whose value agrees with any local free
  trivialization.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting existence of a locally constant rank function for a
  locally free module sheaf;
- `core/canonical`: `(RingedSpace.Modules X)`, `SheafOfModules.IsLocallyFree`, and `ENat.card`;
- `bridge/view`: this theorem identifies the source rank value with the canonical cardinality of a
  free basis index type. -/

-- Proof sketch: for each point `x`, choose a neighbourhood on which `ℱ` is free. Since the stalk
-- ring `𝒪_{X, x}` is nontrivial, invariant basis number for free modules over the stalk shows that
-- any two local free trivializations around `x` have the same finite-or-infinite basis size. This
-- defines a rank value at `x`, and shrinking local trivializations shows that these values are
-- locally constant.
/-- Lemma 17.14.4: if all stalks of the structure sheaf of a ringed space are nontrivial and
`\mathcal F` is a locally free `\mathcal O_X`-module, then there is a locally constant rank
function `X → {0,1,2,\ldots} ∪ {\infty}` whose value at `x` is the finite cardinality, or `∞`, of
any local basis of `\mathcal F` near `x`. -/
theorem exists_locallyConstant_rank_of_isLocallyFree
    (ℱ : RingedSpace.Modules X)
    (h𝒪 : ∀ x : X, Nontrivial (X.presheaf.stalk x)) [ℱ.IsLocallyFree] :
    ∃ rankℱ : LocallyConstant X (WithTop ℕ),
      ∀ (x : X) (U : Opens X) (_ : x ∈ U) (I : Type u) (htriv : IsFreeOn ℱ U I),
        rankℱ x = ENat.card I := sorry

end AlgebraicGeometry
