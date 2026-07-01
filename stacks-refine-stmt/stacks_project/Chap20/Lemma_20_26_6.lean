import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap17.Definition_17_5_1
import stacks_project.Chap15.Lemma_15_59_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ComplexShape HomotopyCategory MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [HasBinaryBiproducts (RingedSpace.Modules X)]
variable [Abelian (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

local notation "KX" => HomotopyCategory (RingedSpace.Modules X) (up ℤ)

/- Domain-style sampling for Lemma 20.26.6:
- primary domain: distinguished triangles of cochain complexes of `\mathcal O_X`-modules on a
  ringed space and the K-flat owner predicate on those complexes;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- best owner abstraction: the Chapter 15 generic `CochainComplex` distinguished-triangle
  two-out-of-three theorems for `IsKFlat`, specialized to `(RingedSpace.Modules X)`;
- primitive vs derived:
  primitive data are only a distinguished triangle in `K((RingedSpace.Modules X))` and the K-flatness
  hypotheses on two of its vertices;
  the ringed-space formulation is derived API by specialization, not a second local owner or
  wrapper.

Source/core/bridge triage:
- `source-facing`: the ringed-space two-out-of-three property for K-flat complexes in a
  distinguished triangle;
- `core/canonical`: the generic owner theorems
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`, and
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- `bridge/view`: this file, which records only the direct specialization to `(RingedSpace.Modules X)`. -/

-- Proof sketch: Lemma `20.26.1` identifies totalized tensoring with a fixed complex on
-- `K(\mathrm{Mod}(\mathcal O_X))` as a triangulated functor, and Definition `20.26.2` says that
-- K-flatness means this functor sends acyclic complexes to acyclic complexes. Applying the generic
-- Chapter 15 distinguished-triangle two-out-of-three theorem at the owner level yields the
-- ringed-space statement directly.
/- Lemma 20.26.6 is the ringed-space specialization of the generic distinguished-triangle
two-out-of-three property for the owner predicate `CochainComplex.IsKFlat`. -/
recall CochainComplex.isKFlat_obj₃_of_distinguished_triangle
recall CochainComplex.isKFlat_obj₂_of_distinguished_triangle
recall CochainComplex.isKFlat_obj₁_of_distinguished_triangle

section

variable (T : Triangle KX) (hT : T ∈ distTriang KX)

/- Source-facing specialization: for a ringed space `(X, \mathcal O_X)`, the canonical owner
theorems specialize exactly to distinguished triangles in `K(\mathrm{Mod}(\mathcal O_X))`. -/
#check CochainComplex.isKFlat_obj₃_of_distinguished_triangle T hT
#check CochainComplex.isKFlat_obj₂_of_distinguished_triangle T hT
#check CochainComplex.isKFlat_obj₁_of_distinguished_triangle T hT

end

end AlgebraicGeometry.RingedSpace
