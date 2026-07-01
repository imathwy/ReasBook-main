import Mathlib
import stacks_project.Chap07.Definition_7_38_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
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
  `ExactFunctor.of p.sheafFiber`;
- source/core/bridge triage:
  `source-facing`: the two stalkwise exactness criteria below;
  `core/canonical`: `ObjectProperty.IsConservativeFamilyOfPoints` and
    `JointlyReflectIsomorphisms.exact_iff`;
  `bridge/view`: this file specializes the owner exactness-detection theorem to stalk functors on
    sheaves of abelian groups and reuses the chapter-level enough-points bridge.
- primitive data: the short complex `S`, the indexed family of points `p`, and the conservativity
  hypothesis `hp`;
- derived API: the two iff-criteria below. -/

section

variable [LocallySmall C]

omit [LocallySmall C] in
private theorem stalkJointlyReflectsIsomorphisms {I : Type w}
    (p : I → Point.{max u v w} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints) :
    JointlyReflectIsomorphisms
      (fun i : I ↦
        ((p i).sheafFiber :
          Sheaf J AddCommGrpCat.{max u v w} ⥤ AddCommGrpCat.{max u v w})) := by
  refine ⟨?_⟩
  intro X Y f _
  let h := hp.jointlyReflectIsomorphisms AddCommGrpCat.{max u v w}
  let _ : ∀ Φ : (ofObj p).FullSubcategory, IsIso (Φ.obj.sheafFiber.map f) := fun Φ ↦ by
    rcases (ofObj_iff p Φ.obj).1 Φ.property with ⟨i, hi⟩
    have hΦ : Φ = ⟨p i, ofObj_apply p i⟩ := by
      cases Φ
      simp only [FullSubcategory.mk.injEq] at hi ⊢
      cases hi
      rfl
    cases hΦ
    infer_instance
  exact h.isIso f

end

-- Proof sketch: apply the exactness-detection theorem for a jointly conservative family of exact
-- fiber functors, using `hp.jointlyReflectIsomorphisms AddCommGrpCat` for the sheaf fibers
-- attached to the chosen family of points.
/-- Lemma 18.14.4 (1): if `p_i`, `i ∈ I`, is a conservative family of points on a site, then a
short complex of abelian sheaves is exact if and only if it is exact on the stalks at the points
`p_i`. -/
theorem abelianSheaf_exact_iff_stalkwise_exact_of_conservativeFamily
    {I : Type w} (p : I → Point.{max u v w} J)
    (hp : (ofObj p).IsConservativeFamilyOfPoints)
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v w})) :
    S.Exact ↔
      ∀ i : I, (S.map (p i).sheafFiber).Exact := by
  simpa using (stalkJointlyReflectsIsomorphisms p hp).exact_iff S

-- Proof sketch: choose a small conservative family of points from `J.HasEnoughPoints`, apply the
-- first clause to that family, and use that exactness on all stalks obviously implies exactness on
-- the selected conservative subfamily.
/-- Lemma 18.14.4 (2): if a site has enough points, then a short complex of abelian sheaves is
exact if and only if it is exact on all stalks. -/
theorem abelianSheaf_exact_iff_stalkwise_exact_of_hasEnoughPoints
    [HasEnoughPoints.{max u v w} J]
    [HasSheafify J AddCommGrpCat.{max u v w}]
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v w})) :
    S.Exact ↔
      ∀ p : Point.{max u v w} J,
        (S.map p.sheafFiber).Exact := by
  let hJ : HasEnoughPoints.{max u v w} J := inferInstance
  obtain ⟨I, p, hp⟩ := hasEnoughPoints_iff_exists_conservativePointFamily.mp hJ
  constructor
  · intro hS p'
    exact hS.map p'.sheafFiber
  · intro hS
    exact ((stalkJointlyReflectsIsomorphisms p hp).exact_iff S).2 fun i ↦ hS (p i)

end GrothendieckTopology
end CategoryTheory
