import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v u w

namespace CategoryTheory
namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling:
- primary domain: conservative families of site points and exactness detection on abelian sheaves;
- sampled owner declarations:
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `JointlyReflectIsomorphisms.exact_iff`,
  `GrothendieckTopology.hasEnoughPoints_iff_exists_conservativePointFamily`,
  `ExactFunctor.of p.sheafFiber`,
  `Abelian (Sheaf J AddCommGrpCat)`;
- source/core/bridge triage:
  `source-facing`: the two stalkwise exactness criteria below;
  `core/canonical`: `ObjectProperty.IsConservativeFamilyOfPoints` and
    `JointlyReflectIsomorphisms.exact_iff` in the abelian sheaf category
    `Sheaf J AddCommGrpCat.{max u v}`;
  `bridge/view`: this file specializes the owner exactness-detection theorem to stalk functors on
    sheaves of abelian groups and reuses the chapter-level enough-points bridge.
- primitive data: the short complex `S`, the indexed family of points `p`, and the conservativity
  hypothesis `hp`;
- derived API: the two iff-criteria below. -/

section

variable [LocallySmall C]

-- Proof sketch: apply the owner theorem `hp.jointlyReflectIsomorphisms AddCommGrpCat` to obtain
-- exactness detected by the full subcategory of points in the conservative family, then translate
-- that criterion back to the source-facing indexed family `p`.
/-- Lemma 18.14.4 (1): if `p_i`, `i ∈ I`, is a conservative family of points on a site, then a
short complex of abelian sheaves is exact if and only if it is exact on the stalks at the points
`p_i`. -/
theorem abelianSheaf_exact_iff_stalkwise_exact_of_conservativeFamily
    {I : Type w} (p : I → J.Point)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) :
    S.Exact ↔
      ∀ i : I, (S.map (p i).sheafFiber).Exact := by
  rw [(hp.jointlyReflectIsomorphisms AddCommGrpCat.{max u v}).exact_iff]
  constructor
  · intro h i
    simpa using h ⟨p i, ofObj_apply p i⟩
  · intro h Φ
    rcases (ofObj_iff p Φ.obj).1 Φ.property with ⟨i, hi⟩
    cases Φ
    cases hi
    simpa using h i

-- Proof sketch: choose a small conservative family of points from `J.HasEnoughPoints`, apply the
-- first clause to that family, and use that exactness on all stalks obviously implies exactness on
-- the selected conservative subfamily.
/-- Lemma 18.14.4 (2): if a site has enough points, then a short complex of abelian sheaves is
exact if and only if it is exact on all stalks. -/
theorem abelianSheaf_exact_iff_stalkwise_exact_of_hasEnoughPoints
    [HasEnoughPoints.{max u v} J]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) :
    S.Exact ↔
      ∀ p : J.Point,
        (S.map p.sheafFiber).Exact := by
  let hJ : HasEnoughPoints.{max u v} J := inferInstance
  obtain ⟨I, p, hp⟩ := hasEnoughPoints_iff_exists_conservativePointFamily.mp hJ
  constructor
  · intro hS p'
    exact hS.map p'.sheafFiber
  · intro hS
    exact (abelianSheaf_exact_iff_stalkwise_exact_of_conservativeFamily p hp S).2
      fun i ↦ hS (p i)

end

end GrothendieckTopology
end CategoryTheory
