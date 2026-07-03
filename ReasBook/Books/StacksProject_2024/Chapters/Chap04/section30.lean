import Mathlib
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_30_1 (from Chap04) -/
namespace CategoryTheory

open Bicategory

/- Domain-style sampling for Definition 4.30.1:
- primary domain: bicategorical `(2,1)`-categories, i.e. locally groupoidal bicategories;
- sampled owner-level declarations:
  `Bicategory.IsLocallyGroupoid`,
  `CategoryTheory.IsGroupoid`,
  `CategoryTheory.IsGroupoid.all_isIso`,
  `CategoryTheory.Groupoid.ofIsGroupoid`;
- best owner abstraction: `Bicategory.IsLocallyGroupoid` is the canonical Prop-valued owner for
  the `(2,1)` condition on a bicategory;
- primitive data: for each pair of objects `a b : B`, the hom-category `a ⟶ b` carries the
  canonical owner predicate `IsGroupoid (a ⟶ b)`;
- derived API: the textbook reformulation saying every `2`-morphism is invertible via
  `IsGroupoid.all_isIso`, together with canonical downstream constructions such as `Pith`.

Source/core/bridge triage:
- `source-facing`: the textbook wording that every `2`-morphism is invertible;
- `core/canonical`: `Bicategory.IsLocallyGroupoid`;
- `bridge/view`: the pointwise consequence `IsGroupoid.all_isIso` on each hom-category. -/

/- Definition 4.30.1: the new content of a `(2,1)`-category, beyond the strictness condition from
Definition 4.29.1, is exactly the canonical mathlib predicate `IsLocallyGroupoid B`. Thus the
textbook notion is expressed by the pair of assumptions `[Strict B] [IsLocallyGroupoid B]`. -/
recall IsLocallyGroupoid

end CategoryTheory

/-! ### Example_4_30_2 (from Chap04) -/
universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

private theorem core_isoMk_eqToIso {C : Type u} [Category.{v} C] {x y : Core C} (e : x.of = y.of) :
    Core.isoMk (eqToIso e) = eqToIso (congrArg Core.mk e) := by
  cases x
  cases y
  cases e
  rfl

namespace Bicategory.Pith

variable {B : Type u} [Bicategory.{w, v} B] [Strict B]

/-- If a bicategory is strict, then its pith is strict as well. -/
instance strict : Strict (Pith B) where
  id_comp f := by
    exact congrArg Core.mk (Strict.id_comp f.of)
  comp_id f := by
    exact congrArg Core.mk (Strict.comp_id f.of)
  assoc f g h := by
    exact congrArg Core.mk (Strict.assoc f.of g.of h.of)
  leftUnitor_eqToIso f := by
    change Core.isoMk (λ_ f.of) = eqToIso (congrArg Core.mk (Strict.id_comp f.of))
    refine (congrArg Core.isoMk (Strict.leftUnitor_eqToIso f.of)).trans ?_
    exact core_isoMk_eqToIso (Strict.id_comp f.of)
  rightUnitor_eqToIso f := by
    change Core.isoMk (ρ_ f.of) = eqToIso (congrArg Core.mk (Strict.comp_id f.of))
    refine (congrArg Core.isoMk (Strict.rightUnitor_eqToIso f.of)).trans ?_
    exact core_isoMk_eqToIso (Strict.comp_id f.of)
  associator_eqToIso f g h := by
    change Core.isoMk (α_ f.of g.of h.of) = eqToIso (congrArg Core.mk (Strict.assoc f.of g.of h.of))
    refine (congrArg Core.isoMk (Strict.associator_eqToIso f.of g.of h.of)).trans ?_
    exact core_isoMk_eqToIso (Strict.assoc f.of g.of h.of)

end Bicategory.Pith

/- Example 4.30.2: categories, functors, and natural isomorphisms are formalized by the canonical
bridge/view `Pith Cat`. Since `Cat` is strict, the bridge carries the strictness half of
Definition 4.30.1 as well. -/
#check Pith Cat.{v, u}

/- The pith bridge for `Cat` is strict. -/
#check (inferInstance : Strict (Pith Cat.{v, u}))

/- The pith bridge for `Cat` is locally groupoidal, so together with strictness it realizes the
Stacks `(2,1)`-category example. -/
#check (inferInstance : IsLocallyGroupoid (Pith Cat.{v, u}))

end CategoryTheory

/-! ### Remark_4_30_3 (from Chap04) -/
universe u v

namespace CategoryTheory

open Bicategory

/- Domain-style sampling for Remark 4.30.3:
- primary domain: bicategorical `(2,1)`-category constructions obtained by restricting
  `2`-morphisms to isomorphisms;
- core/canonical owner abstraction: `CategoryTheory.Bicategory.Pith`;
- bridge/view declarations reused from the project: `FibredInGroupoidsOver`,
  `FibredInGroupoidsMor`, and `StackInGroupoidsOver`.

Primitive-vs-derived split:
- primitive data: the ambient bundled objects and `1`-morphisms from those owner declarations;
- derived API: the `2`-morphism types `(F ≅ G)` and `(M ≅ N)`, which are exactly the isomorphism
  spaces used by the pith construction. -/

/- Source/core/bridge triage for Remark 4.30.3:
- source-facing: the listed examples where one keeps the same objects and `1`-morphisms and
  restricts `2`-morphisms to isomorphisms;
- core/canonical: `Pith`;
- bridge/view: the chapter-level owners for fibred categories in groupoids and stacks in
  groupoids, together with their isomorphism-valued `2`-morphism types. -/

/- Remark 4.30.3: the construction of Example 4.30.2 is the canonical `Pith` construction,
which keeps the same objects and `1`-morphisms and restricts `2`-morphisms to isomorphisms. The
remark only lists further contexts where the same idea applies, so the main formal content here
is a recall of `Pith` and the corresponding canonical chapter-level examples. -/
recall Pith

/- The groupoid variant is the associated `(2,1)`-category `Pith Grpd`. -/
#check Pith Grpd

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver C}
variable {F G : FibredInGroupoidsMor X Y}

/- Over a fixed base `C`, categories fibred in groupoids are formalized by
`FibredInGroupoidsOver C`; the pith construction keeps the same objects and `1`-morphisms and
uses the isomorphisms `F ≅ G` in `FibredInGroupoidsMor X Y` as `2`-morphisms. -/
#check FibredInGroupoidsOver C
#check FibredInGroupoidsMor X Y
#check (F ≅ G)

variable (J : GrothendieckTopology C)
variable {S T : StackInGroupoidsOver J}
variable {M N : S ⟶ T}

/- Likewise, stacks in groupoids over a fixed site `(C, J)` are formalized by
`StackInGroupoidsOver J`; the associated pith keeps the same objects and `1`-morphisms and uses
the isomorphisms `M ≅ N` in `S ⟶ T` as `2`-morphisms. -/
#check StackInGroupoidsOver J
#check (S ⟶ T)
#check (M ≅ N)

end CategoryTheory
