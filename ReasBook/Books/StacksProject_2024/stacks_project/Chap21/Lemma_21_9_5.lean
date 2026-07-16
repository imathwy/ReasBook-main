import StacksProject_2024.stacks_project.Chap21.Lemma_21_9_4
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Topology.Sheaves.CommRingCat

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

noncomputable section

universe u w

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] (U : C)
variable [HasFiniteProducts (Over U)]
variable [Limits.HasCoproducts ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u})]
variable [Limits.HasProducts AddCommGrpCat.{u}]

local notation "ZMod" => ModuleCat ℤ

/- Domain-style sampling for Lemma 21.9.5:
- primary domain: the free-abelian Čech cover chain complex on the slice category `Over U`,
  together with evaluation at `V : Over U` and scalar extension from `ℤ` to the section ring
  `𝒪(V)`;
- sampled owner declarations:
  `freeAbelianCechChainComplex`,
  `cechComplexFunctor`,
  `ModuleCat.extendScalars`,
  `(forget₂ (ModuleCat ℤ) AddCommGrpCat).asEquivalence.inverse`;
- best owner abstraction: the source-facing chain complex owner is already
  `freeAbelianCechChainComplex family` from Lemma `21.9.4`; evaluation at `V` and
  extension of scalars are only bridge/view constructions and should not introduce parallel slice
  copies of that owner.

Source/core/bridge triage:
- `source-facing`: the sectionwise `ℤ`-linear and `𝒪(V)`-linear complexes attached to the cover;
- `core/canonical`: `freeAbelianCechChainComplex family`;
- `bridge/view`: evaluation at `V`, the additive-group-to-`ℤ`-module equivalence, and
  `ModuleCat.extendScalars`.

Primitive data versus derived API:
- primitive data: `U`, the family `family : ι → Over U`, the presheaf `𝒪`, and the object
  `V : Over U`;
- derived API: the evaluated `ℤ`-module chain complex and its scalar extension to
  `ModuleCat (((Over.forget U).op ⋙ 𝒪).obj (op V))`.
-/

/-- Helper for Lemma 21.9.5: the evaluated free-abelian Čech cover complex regarded as a chain
complex of `ℤ`-modules. -/
private abbrev cechCoverSectionChainComplex {ι : Type w} (family : ι → Over U) (V : Over U) :
    ChainComplex ZMod ℕ :=
  ((((evaluation (Over U)ᵒᵖ AddCommGrpCat.{u}).obj (op V)) ⋙
      (forget₂ ZMod AddCommGrpCat.{u}).asEquivalence.inverse).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (freeAbelianCechChainComplex family)

/-- The sectionwise tensor of the evaluated free-abelian Čech cover chain complex with the
commutative ring of sections of `𝒪` over `V`, realized as extension of scalars from `ℤ`. -/
abbrev cechCoverSectionTensorChainComplex
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) {ι : Type w} (family : ι → Over U) (V : Over U) :
    ChainComplex (ModuleCat (((Over.forget U).op ⋙ 𝒪).obj (op V))) ℕ :=
  ((ModuleCat.extendScalars
      (Int.castRingHom (((Over.forget U).op ⋙ 𝒪).obj (op V)))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (cechCoverSectionChainComplex U family V)

-- Proof sketch: for each `V : Over U`, evaluate Lemma `21.9.4` at `V` and identify the resulting
-- complex with a direct sum of bar-resolution summands. Tensoring that evaluated complex over `ℤ`
-- with the section ring `𝒪(V)` preserves exactness in positive degrees by the flatness argument of
-- Lemma `18.28.11`, exactly as in the textbook proof.
/-- Lemma 21.9.5: after restricting a ring-valued presheaf `𝒪` to `Over U`, tensoring the
evaluated free-abelian Čech cover chain complex with the ring of sections over any object
`V : Over U` yields a complex with zero homology in every positive degree. -/
@[stacks 03F5]
theorem cechCoverSectionTensorChainComplex_homology_isZero_succ
    {ι : Type w} (family : ι → Over U) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    (V : Over U) (i : ℕ) :
    IsZero ((cechCoverSectionTensorChainComplex U 𝒪 family V).homology (i + 1)) := sorry

/-- Positive-degree companion for Lemma 21.9.5 in arbitrary-index form. -/
theorem cechCoverSectionTensorChainComplex_homology_isZero_of_pos
    {ι : Type w} (family : ι → Over U) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
    (V : Over U) (i : ℕ) (hi : 0 < i) :
    IsZero ((cechCoverSectionTensorChainComplex U 𝒪 family V).homology i) := by
  rcases Nat.exists_eq_add_of_lt hi with ⟨j, rfl⟩
  simpa [Nat.add_comm] using
    cechCoverSectionTensorChainComplex_homology_isZero_succ U family 𝒪 V j

/-- Typeclass form of Lemma 21.9.5: the positive-degree homology objects of the sectionwise
tensor Čech cover complex are zero. -/
instance instIsZeroCechCoverSectionTensorChainComplexHomologySucc
    {ι : Type w} (family : ι → Over U) (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (V : Over U) (i : ℕ) :
    IsZero ((cechCoverSectionTensorChainComplex U 𝒪 family V).homology (i + 1)) :=
  cechCoverSectionTensorChainComplex_homology_isZero_succ U family 𝒪 V i

end CategoryTheory
