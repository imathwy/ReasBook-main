import Mathlib
import stacks_project.Chap04.Lemma_4_33_7

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Definition 8.2.2:
- primary domain: subpresheaves of the canonical Hom-presheaf attached to the fiber
  pseudofunctor of a fibred category;
- sampled owner-level declarations:
  `CategoryTheory.Subfunctor`,
  `CategoryTheory.Subfunctor.toFunctor`,
  `Pseudofunctor.presheafHom`,
  `canonicalFiberPseudofunctor`;
- best owner abstraction: the source-facing object `Isom(x, y)` should be a `Subfunctor` of the
  canonical Hom-presheaf, with the underlying presheaf obtained by `Subfunctor.toFunctor`;
- primitive data: only the sectionwise predicate `IsIso` on the canonical Hom-presheaf;
- derived API: the underlying presheaf `(fiberIsomorphismSubfunctor p x y).toFunctor`.

Source/core/bridge triage:
- `source-facing`: `fiberIsomorphismSubfunctor`;
- `core/canonical`: `Subfunctor ((canonicalFiberPseudofunctor p).presheafHom x y)`;
- `bridge/view`: `Subfunctor.toFunctor`. -/

section

variable (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U)

private theorem isIso_presheafHom_map
    {A B : (Over U)ᵒᵖ} (g : A ⟶ B)
    (φ : ((canonicalFiberPseudofunctor p).presheafHom x y).obj A) (hφ : IsIso φ) :
    IsIso (((canonicalFiberPseudofunctor p).presheafHom x y).map g φ) := by
  let F := canonicalFiberPseudofunctor p
  let a := A.unop.hom
  let b := B.unop.hom
  let f := g.unop.left
  have hg :
      a.op.toLoc ≫ f.op.toLoc = b.op.toLoc := by
    simpa [a, b, f] using congrArg (fun k ↦ k.op.toLoc) (Over.w g.unop)
  letI : IsIso φ := hφ
  let compIso := F.mapComp' a.op.toLoc f.op.toLoc b.op.toLoc hg
  let middleIso :
      (F.map a.op.toLoc).toFunctor.obj x ≅ (F.map a.op.toLoc).toFunctor.obj y := by
    simpa [presheafHom, pullHom] using asIso φ
  let e := (Cat.Hom.toNatIso compIso).app x ≪≫
      (F.map f.op.toLoc).toFunctor.mapIso middleIso ≪≫
      ((Cat.Hom.toNatIso compIso).app y).symm
  simpa [presheafHom, pullHom, compIso, middleIso, e, hg, Category.assoc] using
    (show IsIso e.hom from inferInstance)

/-- Definition 8.2.2: the presheaf `Isom(x, y)` is the canonical subpresheaf of `Mor(x, y)`
whose sections are fiberwise isomorphisms, expressed through the owner abstraction
`Subfunctor ((canonicalFiberPseudofunctor p).presheafHom x y)`. -/
noncomputable def fiberIsomorphismSubfunctor
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) :
    Subfunctor ((canonicalFiberPseudofunctor p).presheafHom x y) where
  obj _ := { φ | IsIso φ }
  map g := isIso_presheafHom_map p x y g

-- Proof sketch: unfold `fiberIsomorphismSubfunctor`; its sectionwise predicate was defined to be
-- exactly `IsIso` on the canonical Hom-presheaf.
/-- A section of `fiberIsomorphismSubfunctor p x y` is exactly an isomorphism in the corresponding
fiber. -/
@[simp]
theorem mem_fiberIsomorphismSubfunctor_obj_iff
    (p : S ⥤ C) [p.IsFibered] {U : C} (x y : p.Fiber U) {A : (Over U)ᵒᵖ}
    (φ : ((canonicalFiberPseudofunctor p).presheafHom x y).obj A) :
    (fiberIsomorphismSubfunctor p x y).obj A φ ↔ IsIso φ := by
  -- Unfold the defining sectionwise predicate of the subpresheaf `Isom(x, y)`.
  change IsIso φ ↔ IsIso φ
  -- The reduced goal is definitional.
  exact Iff.rfl

end

end CategoryTheory
