import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_3_1 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Definition 4.3.1:
- primary domain: opposite categories and the reversal of morphisms in category theory
- sampled canonical declarations:
  `Cᵒᵖ`,
  `Category.opposite`,
  `Quiver.Hom.unop`,
  `unop_comp`
- best owner abstraction: the opposite type `Cᵒᵖ` equipped with the canonical instance
  `Category.opposite`
- primitive data: no new primitive data beyond the opposite-type and opposite-category
  constructions already provided by mathlib
- derived API: unopposite morphisms and the reversed-composition formula
-/
/- Source/core/bridge triage for Definition 4.3.1:
- source-facing notion: the opposite category of `C` and its reversed morphisms
- core/canonical owner: the opposite type `Cᵒᵖ` with the canonical instance `Category.opposite`
- primitive data: no new primitive data beyond the existing opposite-type and opposite-category
  constructions from mathlib
- derived API: unopposite morphisms and the reversed-composition formula
-/

/-
Definition 4.3.1: for a category `C`, the opposite category is the canonical mathlib category
instance `Category.opposite` on the opposite type `Cᵒᵖ`.
-/
#check Cᵒᵖ

recall Category.opposite

/- Definition 4.3.1: a morphism in `Cᵒᵖ` canonically unops to a morphism in `C` with reversed
source and target. -/
recall Quiver.Hom.unop

/- In the opposite category, composition is reversed; this is the canonical formula
`unop_comp`. -/
recall unop_comp

end CategoryTheory

/-! ### Definition_4_3_2 (from Chap04) -/
universe vC uC vA uA

namespace CategoryTheory

section

variable (C : Type uC) [Category.{vC} C]
variable (A : Type uA) [Category.{vA} A]

/- Domain-style sampling for Definition 4.3.2:
- primary domain: opposite-category presentations of contravariant functors
- sampled canonical declarations:
  `CategoryTheory.Functor`,
  `Category.opposite`,
  the functor-category notation `(· ⥤ ·)`,
  the chapter owner `Presheaf` from `Definition_4_3_3`
- best owner abstraction: the functor category `Cᵒᵖ ⥤ A`, i.e. `CategoryTheory.Functor`
  specialized to source `Cᵒᵖ` and target `A`
- primitive data: only the ordinary functor data and axioms for a functor out of the opposite
  category
- derived API: natural transformations and the inherited category structure on the functor
  category; the chapter owner `Presheaf C` is only the high-reuse specialization
  `Cᵒᵖ ⥤ Type _`, not a second generic owner
-/
/- Source/core/bridge triage for Definition 4.3.2:
- `source-facing`: a contravariant functor from `C` to `A`
- `core/canonical`: the functor category `Cᵒᵖ ⥤ A`
- primitive data: only an ordinary functor out of the opposite category
- derived API: natural transformations and the ambient category structure inherited from the
  functor category
- `bridge/view`: the chapter alias `Presheaf C` when `A = Type _`
-/

/- Definition 4.3.2: a contravariant functor from `C` to `A` is canonically an object of the
functor category `Cᵒᵖ ⥤ A`, so the refined item is a direct recall of that owner type expression
rather than a parallel local alias. -/
#check (Cᵒᵖ ⥤ A)

/- Companion recall: the primitive data of a contravariant functor are exactly the standard
object map, morphism map, and functoriality axioms of `CategoryTheory.Functor`, specialized to
source `Cᵒᵖ` and target `A`. -/
recall Functor

end

end CategoryTheory

/-! ### Definition_4_3_3 (from Chap04) -/
universe w v u

namespace CategoryTheory

/-
Source/core/bridge triage for Definition 4.3.3:
- source-facing owner: a set-valued presheaf on a category `C`
- sampled canonical declarations in this domain:
  the ambient functor category `Cᵒᵖ ⥤ Type w`,
  the topological specialization `TopCat.Presheaf`,
  and the site-level sheaf owner `Sheaf J (Type w)`, whose underlying primitive object is again a
  set-valued presheaf
- core/canonical background: the contravariant functor category `Cᵒᵖ ⥤ Type w`
- primitive data: only the underlying functor
- derived API: natural transformations, the inherited category structure, and later predicates on
  this owner such as representability and the sheaf condition
- owner choice: mathlib does not provide a generic owner alias for arbitrary set-valued
  presheaves, so this file remains the canonical project owner while staying definitionally equal
  to the ambient functor category
-/
/-- Definition 4.3.3: a presheaf of sets on a category `C` is the chapter owner `Presheaf C`,
definitionally equal to the contravariant functor category `Cᵒᵖ ⥤ Type w`. The short owner name
`Presheaf` is kept because it is stable, high-reuse vocabulary throughout the later
chapter/project development. -/
abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type w

variable {C : Type u} [Category.{v} C]

/-- For a presheaf on `C`, the restriction map along an identity morphism is the identity on the
section type over that object. -/
-- Proof sketch: this is the `map_id` axiom of the underlying contravariant functor.
theorem Presheaf_map_id (F : Presheaf C) (U : Cᵒᵖ) :
    F.map (𝟙 U) = 𝟙 (F.obj U) := by
  -- A presheaf is definitionally a functor `Cᵒᵖ ⥤ Type w`, so the claim is its identity law.
  exact F.map_id U

end CategoryTheory

/-! ### Example_4_3_4 (from Chap04) -/
universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Example 4.3.4:
- primary domain: presheaves on a category and the Yoneda realization of representable presheaves;
- inspected owner-level declarations:
  `Presheaf`,
  `yoneda`,
  `yoneda_obj_obj`,
  `yoneda_obj_map`;
- best owner abstraction: the ambient source-facing owner is `Presheaf C`, while the canonical
  core owner for the representable presheaf `h_U` is the Yoneda object `yoneda.obj U : Presheaf C`;
- primitive data: only the Yoneda embedding `yoneda`;
- derived API: the objectwise and morphismwise computation rules `yoneda_obj_obj` and
  `yoneda_obj_map`;
- bridge/view: the reusable source-facing notation `h[U]` for the textbook representable presheaf
  `h_U`.

Source/core/bridge triage:
- `source-facing`: the textbook representable presheaf `h_U : Presheaf C` and its evaluation
  formulas;
- `core/canonical`: `Presheaf`, `yoneda`, `yoneda_obj_obj`, `yoneda_obj_map`;
- `bridge/view`: the notation bridge `h[U]` for the owner object `yoneda.obj U`. -/

namespace RepresentablePresheaf

/- Textbook notation for the representable presheaf `h_U`. Since Lean does not support the
subscripted binder directly as notation, we write this reusable surface form as `h[U]`. -/
scoped notation:max "h[" U "]" => yoneda.obj U

end RepresentablePresheaf

open scoped RepresentablePresheaf

section

variable (U : C)

/- Example 4.3.4: the textbook representable presheaf attached to `U` is the canonical Yoneda
object `h[U] : Presheaf C`. -/
#check (h[U] : Presheaf C)

end

/- Example 4.3.4: the representable presheaves on `C` are organized by the canonical Yoneda
embedding `yoneda : C ⥤ Presheaf C`; the textbook object `h_U` is obtained by evaluating this
owner functor at `U`. -/
recall yoneda

/- Example 4.3.4 (object formula): for each object `U` of a category `C`, the representable
presheaf `h[U] = yoneda.obj U` sends an object `X` to the hom-set `Hom_C(X, U)`. This is the
canonical computation rule `yoneda_obj_obj`. -/
recall yoneda_obj_obj

/- Example 4.3.4 (morphism formula): for `f : X ⟶ Y` in `Cᵒᵖ`, the restriction map of the
representable presheaf `h[U]` is precomposition by `f.unop`, namely
`h[U].map f g = f.unop ≫ g`. This is the canonical computation rule
`yoneda_obj_map`. -/
recall yoneda_obj_map

end CategoryTheory

/-! ### Lemma_4_3_5_Yoneda_lemma (from Chap04) -/
universe v u

namespace CategoryTheory

open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

/- Source/core/bridge triage for Lemma 4.3.5:
- source-facing content: the Yoneda embedding is full and faithful, together with the standard
  evaluation equivalence it induces;
- core/canonical owner: `Yoneda.fullyFaithful`, `yonedaLemma`, and their pointwise companions
  `yonedaEquiv`, `yonedaEquiv_naturality`, `yonedaEquiv_apply`;
- bridge layer: none is needed here, because the source statement is already the canonical
  mathlib Yoneda API.
-/

/- Lemma 4.3.5 (Yoneda lemma): the Yoneda embedding `yoneda : C ⥤ Presheaf.{v} C` is full and
faithful. The canonical mathlib owner packaging this statement is `Yoneda.fullyFaithful`, from
which fullness and faithfulness are derived. -/
recall Yoneda.fullyFaithful

/- More generally, the Yoneda lemma identifies the Yoneda pairing with evaluation by a natural
isomorphism. This is the canonical mathlib natural isomorphism `yonedaLemma`. -/
recall yonedaLemma

/- Pointwise, for every object `U` of `C` and every presheaf `F : Presheaf.{v} C`, morphisms
`h[U] ⟶ F` are in bijection with elements of `F.obj (op U)`. This is the componentwise
equivalence underlying `yonedaLemma`. -/
recall yonedaEquiv

/- The pointwise Yoneda equivalence is natural in the Yoneda variable. -/
recall yonedaEquiv_naturality

/- Companion recall: the Yoneda equivalence is evaluation at `𝟙 U`, namely
`f ↦ f.app (op U) (𝟙 U)`. -/
recall yonedaEquiv_apply

end CategoryTheory

/-! ### Definition_4_3_6 (from Chap04) -/
universe v u

namespace CategoryTheory

open scoped RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

/- Source/core/bridge triage for Definition 4.3.6:
- sampled owner-style declarations in this domain:
  `Presheaf C`,
  `Functor.RepresentableBy`,
  `Functor.RepresentableBy.toIso`,
  `Functor.IsRepresentable`
- `source-facing`: the textbook condition that a presheaf be isomorphic to some `h[U]`
- `core/canonical`: the mathlib owner predicate `Functor.IsRepresentable`
- `bridge/view`: the equivalence between a representing structure `F.RepresentableBy U` and a
  Yoneda isomorphism `h[U] ≅ F`
- primitive data: a representing object `U : C` together with `F.RepresentableBy U`
- derived API: the source-facing Yoneda isomorphism from `Functor.RepresentableBy.toIso`, and when
  later needed the chosen representing object `reprX` with its Yoneda isomorphism `reprW`
-/
/- Definition 4.3.6: representability of a presheaf is the canonical mathlib predicate
`CategoryTheory.Functor.IsRepresentable`. -/
recall Functor.IsRepresentable

/-- A presheaf is representable exactly when it is isomorphic to a representable Yoneda
presheaf `h[U]` for some `U : C`. -/
-- Proof sketch: use the canonical chosen representing object and Yoneda isomorphism from
-- `Functor.IsRepresentable` in one direction, and build representability from the exhibited
-- Yoneda isomorphism in the other direction.
theorem isRepresentable_iff_exists_yoneda_obj_iso (F : Presheaf C) :
    F.IsRepresentable ↔ Nonempty (Σ U : C, h[U] ≅ F) := by
  constructor
  · intro hF
    -- Use the canonical representing object attached to the representability witness.
    let _ : F.IsRepresentable := hF
    refine ⟨⟨F.reprX, ?_⟩⟩
    -- The canonical Yoneda comparison gives the required source-facing isomorphism.
    simpa using (F.reprW : yoneda.obj F.reprX ≅ F)
  · rintro ⟨⟨U, e⟩⟩
    -- An exhibited Yoneda isomorphism is exactly the canonical constructor for representability.
    simpa using (Functor.IsRepresentable.mk' e : F.IsRepresentable)

end CategoryTheory
