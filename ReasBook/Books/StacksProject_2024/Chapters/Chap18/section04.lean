import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_4_1 (from Chap18) -/
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

/-! ### Lemma_18_4_2 (from Chap18) -/
open Opposite

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Lemma 18.4.2:
- primary domain: presheaves on a category, the Yoneda lemma, and the free-forgetful adjunction
  whiskered over the presheaf category `Cᵒᵖ ⥤ -`;
- sampled owner API:
  `yonedaEquiv`,
  `Adjunction.homEquiv`,
  `Adjunction.whiskerRight`,
  `Equiv.bijective`;
- best owner abstraction: the canonical Hom-to-sections equivalence `yonedaEquiv` for
  representables, and the whiskered adjunction `AddCommGrpCat.adj.whiskerRight Cᵒᵖ` for free
  abelian presheaves;
- primitive data: an object `U : C`, a presheaf of sets `F`, a presheaf of sets `G`, and an
  abelian-group-valued presheaf `A`;
- derived API: the specialized hom-set equivalences and their bijectivity, with part (3) obtained
  by composing the owners for parts (1) and (2).

Source/core/bridge triage:
- `source-facing`: the three Stacks bijections for representables, free abelian presheaves, and
  the representable-free-abelian specialization;
- `core/canonical`: `yonedaEquiv` and `Adjunction.homEquiv`;
- `bridge/view`: the specialization of `Adjunction.homEquiv` to
  `AddCommGrpCat.adj.whiskerRight Cᵒᵖ`, and the composite equivalence in part (3).

Parts (1) and (2) are exact owner-side recalls, so this file should not keep parallel local
`abbrev`s for them. Part (3) has no separate upstream owner name, but it is still only a thin
composite of the same canonical equivalences, so the public surface should present that composite
directly instead of naming another wrapper.
-/

/- Lemma 18.4.2 (1): for a presheaf `F : Cᵒᵖ ⥤ Type v` and an object `U : C`, morphisms
`yoneda.obj U ⟶ F` are canonically identified with the sections `F.obj (op U)`. This is exactly
`yonedaEquiv`. -/
recall yonedaEquiv

section

variable (G : Cᵒᵖ ⥤ Type v) (A : Cᵒᵖ ⥤ AddCommGrpCat.{v})

/- Lemma 18.4.2 (2): morphisms from the free abelian presheaf `G ⋙ AddCommGrpCat.free` to an
abelian presheaf `A` are canonically identified with morphisms from `G` to the underlying
set-valued presheaf of `A`. This is the `Adjunction.homEquiv` of the whiskered free-forgetful
adjunction. -/
#check (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv G A) :
  (G ⋙ AddCommGrpCat.free.{v} ⟶ A) ≃ (G ⟶ A ⋙ forget AddCommGrpCat))

/- Lemma 18.4.2 (2) companion: the specialized adjunction equivalence is bijective. -/
#check ((((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv G A).bijective) :
  Function.Bijective ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv G A))

end

section

variable (U : C) (A : Cᵒᵖ ⥤ AddCommGrpCat.{v})

/- Lemma 18.4.2 (3): specializing part (2) to the representable presheaf `yoneda.obj U` and then
applying `yonedaEquiv` identifies morphisms
`yoneda.obj U ⋙ AddCommGrpCat.free ⟶ A` with the sections `A.obj (op U)`. -/
#check ((((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) A).trans yonedaEquiv) :
  (yoneda.obj U ⋙ AddCommGrpCat.free.{v} ⟶ A) ≃ A.obj (op U))

/- Lemma 18.4.2 (3) companion: the composite equivalence is bijective. -/
#check ((Equiv.bijective
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) A).trans yonedaEquiv)) :
  Function.Bijective
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) A).trans yonedaEquiv))

end

end CategoryTheory

/-! ### Lemma_18_4_3 (from Chap18) -/
open CategoryTheory Limits Opposite

universe u v w

/- Domain-style sampling for Lemma 18.4.3:
- primary domain: set-valued and abelian-group-valued presheaves on `C`, together with coproducts
  in functor categories;
- inspected owner declarations:
  `(Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
    AddCommGrpCat.free`,
  `ℤ_ G`,
  `Limits.PreservesCoproduct.iso`,
  `Limits.sigmaComparison`;
- best owner abstraction: `Definition_18_4_1` owns the source-facing free abelian presheaf
  notation `ℤ_ G`, while the canonical coproduct comparison is owned by
  `Limits.PreservesCoproduct.iso` for the whiskered free abelian group functor;
- primitive data: a family `𝒢 : I → Cᵒᵖ ⥤ Type (max u v w)`;
- derived API: the canonical isomorphism
  `ℤ_ (∐ 𝒢) ≅ ∐ fun i ↦ ℤ_ (𝒢 i)` and equivalently the
  `IsIso` instance for the associated `sigmaComparison`.

Source/core/bridge triage:
- `source-facing`: the free abelian presheaf attached to a set-valued presheaf;
- `core/canonical`: the whiskered functor `AddCommGrpCat.free` and its coproduct comparison
  `PreservesCoproduct.iso`;
- `bridge/view`: the specialized recall that identifies the Stacks lemma with that canonical
  coproduct-preservation isomorphism.
-/

variable {C : Type u} [Category.{v} C]
variable {I : Type w}

variable (𝒢 : I → Cᵒᵖ ⥤ Type (max u v w))

/- Lemma 18.4.3: the free abelian presheaf of a coproduct of set-valued presheaves is canonically
isomorphic to the coproduct of the corresponding free abelian presheaves. This is exactly the
canonical coproduct-preservation isomorphism for the whiskered free abelian group functor, written
through the source-facing owner notation `ℤ_ G` from `Definition_18_4_1`. -/
#check
  (PreservesCoproduct.iso
      ((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
        AddCommGrpCat.free)
      𝒢 :
    ℤ_ (∐ 𝒢) ≅ ∐ fun i : I ↦ ℤ_ (𝒢 i))

/- Companion recall: equivalently, the canonical coproduct comparison map is an isomorphism. -/
#check
  (show IsIso
    (sigmaComparison
      ((Functor.whiskeringRight Cᵒᵖ (Type (max u v w)) AddCommGrpCat.{max u v w}).obj
        AddCommGrpCat.free)
      𝒢) by infer_instance)
