import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Tactic.Recall

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

/- Source/core/bridge triage for Definition 13.9.1:
- primary domain: mapping cones and their standard triangles for cochain complexes in an additive
  category;
- inspected owner declarations:
  `CochainComplex.mappingCone`,
  `CochainComplex.mappingCone.inr`,
  `CochainComplex.mappingCone.fst`,
  `CochainComplex.mappingCone.triangle`;
- best owner abstraction: the upstream namespace owner `CochainComplex.mappingCone`, with the cone
  object as owner, the canonical inclusion `inr` and cocycle `fst` as atomic comparison data, and
  the standard triangle as derived API;
- layer: `core/canonical`; the item recalls canonical mathlib declarations rather than introducing
  a new source-facing wrapper;
- primitive data: a morphism of cochain complexes `f : K^• ⟶ L^•`;
- derived API: the cone object `CochainComplex.mappingCone f`, the canonical inclusion
  `CochainComplex.mappingCone.inr f`, the canonical cocycle
  `CochainComplex.mappingCone.fst f`, and the standard triangle
  `CochainComplex.mappingCone.triangle f`, whose third morphism is induced by `-fst f`.
-/

/- Definition 13.9.1: for a morphism `f : K^• ⟶ L^•` of cochain complexes in an additive
category, the cone is the canonical mathlib complex `CochainComplex.mappingCone f`. Degreewise it
is canonically the biproduct `K.X (n + 1) ⊞ L.X n`, with the standard mapping-cone differential
whose components are `-d_K`, `f`, and `d_L` relative to that decomposition. The canonical maps are
`CochainComplex.mappingCone.inr f : L ⟶ CochainComplex.mappingCone f`, the right inclusion of the
`L`-summand, and
`CochainComplex.mappingCone.fst f : Cocycle (CochainComplex.mappingCone f) K 1`, the first
projection to the shifted `K` summand; the latter induces the third morphism of the standard
mapping-cone triangle from `CochainComplex.mappingCone f` to `K⟦(1 : ℤ)⟧`. -/
recall CochainComplex.mappingCone

/- The canonical inclusion of the target complex into the mapping cone is
`CochainComplex.mappingCone.inr`. -/
recall CochainComplex.mappingCone.inr

/- The canonical degree-`1` cocycle on the mapping cone projecting to the shifted source is
`CochainComplex.mappingCone.fst`. -/
recall CochainComplex.mappingCone.fst

/- The canonical morphism from the mapping cone to the shift of the source is the third morphism
in the standard mapping-cone triangle `CochainComplex.mappingCone.triangle`, induced by
`-CochainComplex.mappingCone.fst`. -/
recall CochainComplex.mappingCone.triangle
