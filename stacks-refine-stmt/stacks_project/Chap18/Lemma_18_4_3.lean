import Mathlib
import stacks_project.Chap18.Definition_18_4_1

-- Declarations for this item will be appended below by the statement pipeline.

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
