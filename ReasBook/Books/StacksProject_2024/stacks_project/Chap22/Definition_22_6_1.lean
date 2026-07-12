import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Tactic.Recall

open CategoryTheory Limits
open CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

/- Source/core/bridge triage for Definition 22.6.1:
- `source-facing`: the cone of a morphism of differential graded modules;
- `core/canonical`: the canonical cochain-complex mapping-cone owner `mappingCone`;
- `bridge/view`: in the current chapter, differential graded modules are used through their
  underlying cochain complexes, so the source cone and its canonical maps are recalled directly
  from that owner;
- primary domain: cones of morphisms of differential graded modules, viewed through the canonical
  cochain-complex owner used elsewhere in this chapter;
- inspected owner declarations:
  `mappingCone`,
  `mappingCone.inr`,
  `mappingCone.fst`,
  `mappingCone.triangle`;
- best owner abstraction: the upstream namespace owner `mappingCone`, with the cone object as
  owner, the canonical inclusion `inr` and cocycle `fst` as atomic comparison data, and the
  standard triangle as derived API;
- source-facing interpretation: for a morphism of differential graded `A`-modules, the cone
  object and its canonical maps `i : L ⟶ C(f)` and `p : C(f) ⟶ K⟦(1 : ℤ)⟧` are formalized on the
  underlying cochain-complex side by the `mappingCone` namespace.
-/

/- Definition 22.6.1: let `(A, d)` be a differential graded algebra and let `f : K ⟶ L` be a
homomorphism of differential graded `A`-modules. The cone `C(f)` is the canonical mapping-cone
complex `mappingCone f`. Degreewise it is canonically the biproduct
`K.X (n + 1) ⊞ L.X n`, which matches the source grading `Lⁿ ⊕ Kⁿ⁺¹` up to the standard biproduct
ordering used by mathlib; its differential is the standard mapping-cone differential with
components `-d_K`, `f`, and `d_L` relative to that decomposition. The canonical maps are
`mappingCone.inr f : L ⟶ mappingCone f`, corresponding to the source map `i : L ⟶ C(f)`, and the
canonical morphism from the cone to the shifted source complex, packaged via `mappingCone.fst f`
and the standard triangle `mappingCone.triangle f`. -/
recall mappingCone

/- The canonical inclusion of the target complex into the mapping cone is
`mappingCone.inr`. -/
recall mappingCone.inr

/- The canonical degree-`1` cocycle on the mapping cone projecting to the shifted source is
`mappingCone.fst`. -/
recall mappingCone.fst

/- The canonical morphism from the mapping cone to the shift of the source is the third morphism
in the standard mapping-cone triangle `mappingCone.triangle`, induced by `-mappingCone.fst`. -/
recall mappingCone.triangle
