import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

universe u v

/- Textbook notation for the free abelian presheaf `ℤ_G`. Since Lean does not support the
subscripted binder directly as notation, we use the reusable surface form `ℤ_ G`. -/
notation:max "ℤ_ " G:max => G ⋙ AddCommGrpCat.free

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 18.4.1:
- primary domain: presheaves of sets and presheaves of abelian groups on a category;
- sampled owner declarations:
  `AddCommGrpCat.free`,
  `AddCommGrpCat.adj`,
  `free_abelian_presheaf_hom_equiv`,
  `freeAbelianSheaf`;
- source-facing layer: the free abelian presheaf on a set-valued presheaf `G`;
- core/canonical owner: the whiskered functor
  `(Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat).obj AddCommGrpCat.free`,
  equivalently the objectwise expression `G ⋙ AddCommGrpCat.free`;
- bridge/view: the evaluation formula at `U` and the representable specialization
  `yoneda.obj X ⋙ AddCommGrpCat.free`.

Primitive data are only the presheaf `G` and the free abelian group functor.
The previous local abbreviations carried no extra mathematics beyond the canonical objectwise
composition already used downstream, so this item should recall that owner directly. -/

/- Definition 18.4.1: the free abelian presheaf on a presheaf of sets is the canonical
objectwise free-abelian-group functor on presheaves. -/
#check ((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat).obj AddCommGrpCat.free :
  (Cᵒᵖ ⥤ Type v) ⥤ Cᵒᵖ ⥤ AddCommGrpCat)

/- Companion recall: the objectwise construction is governed by the free-forgetful adjunction for
abelian groups. -/
recall AddCommGrpCat.adj

/-- The free abelian presheaf evaluates at `U` as the free abelian group on `G(U)`. -/
theorem freeAbelianPresheaf_obj (G : Cᵒᵖ ⥤ Type v) (U : Cᵒᵖ) :
    (ℤ_ G).obj U = AddCommGrpCat.of (FreeAbelianGroup (G.obj U)) :=
  rfl

/-- The free abelian presheaf on the representable presheaf `h_X` evaluates at `U` as the free
abelian group on `Hom(U, X)`. -/
theorem freeAbelianPresheafOfRepresentable_obj (X U : C) :
    (ℤ_ (yoneda.obj X)).obj (op U) =
      AddCommGrpCat.of (FreeAbelianGroup (U ⟶ X)) :=
  rfl

end
