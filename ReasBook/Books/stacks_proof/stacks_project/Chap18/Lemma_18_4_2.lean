import stacks_proof.stacks_project.Chap18.Definition_18_4_1

-- Declarations for this item will be appended below by the statement pipeline.

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
  `ℤ_ G`,
  `yonedaEquiv`,
  `Adjunction.homEquiv`,
  `Adjunction.whiskerRight`,
  `Equiv.bijective`;
- best owner abstraction: the canonical Hom-to-sections equivalence `yonedaEquiv` for
  representables; the source-facing owner `ℤ_ G` from `Definition_18_4_1` for free abelian
  presheaves; and the whiskered adjunction `AddCommGrpCat.adj.whiskerRight Cᵒᵖ` for the
  corresponding canonical Hom equivalence;
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

/- Lemma 18.4.2 (2): morphisms from the free abelian presheaf `ℤ_ G` to an
abelian presheaf `A` are canonically identified with morphisms from `G` to the underlying
set-valued presheaf of `A`. This is the `Adjunction.homEquiv` of the whiskered free-forgetful
adjunction. -/
#check
  ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv G A :
    (ℤ_ G ⟶ A) ≃ _)

/- Lemma 18.4.2 (2) companion: the specialized adjunction equivalence is bijective. -/
#check
  (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv G A :
      (ℤ_ G ⟶ A) ≃ _).bijective)

end

section

variable (U : C) (A : Cᵒᵖ ⥤ AddCommGrpCat.{v})

/- Lemma 18.4.2 (3): specializing part (2) to the representable presheaf `yoneda.obj U` and then
applying `yonedaEquiv` identifies morphisms
`ℤ_ (yoneda.obj U) ⟶ A` with the sections `A.obj (op U)`. -/
#check
  (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) A).trans yonedaEquiv :
    (ℤ_ (yoneda.obj U) ⟶ A) ≃ _)

/- Lemma 18.4.2 (3) companion: the composite equivalence is bijective. -/
#check
  ((((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) A).trans yonedaEquiv :
      (ℤ_ (yoneda.obj U) ⟶ A) ≃ _).bijective)

end

end CategoryTheory
