import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopCat.Presheaf TopCat.Presheaf.Sheafify TopologicalSpace

noncomputable section

universe v

section

variable {X : TopCat.{v}} (F : Presheaf (Type v) X)

/-
Domain-style sampling for Lemma 6.18.1:
- primary domain: sheafification of `Type`-valued presheaves and stalkwise local-germ criteria;
- sampled owner API:
  `TopCat.Presheaf.sheafify`,
  `TopCat.Presheaf.sheafifyStalkIso`,
  `TopCat.Presheaf.toSheafify`,
  `TopCat.Presheaf.Sheafify.isLocallyGerm`;
- best owner abstraction: the bundled sheafification `F.sheafify`, with stalk comparison given by
  `F.sheafifyStalkIso`;
- primitive data: the presheaf `F` and the open set `U`;
- derived API: the concrete subtype realization of `F.sheafify` inside the presheaf of functions
  into stalks, and the induced map on stalks from `F.toSheafify`.

Source/core/bridge triage:
- `source-facing`: the pullback description of sections of `F^#(U)`;
- `core/canonical`: `F.sheafify` together with `F.sheafifyStalkIso`;
- `bridge/view`: the subtype inclusion
  `(subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)`.
-/

-- Proof sketch: use the canonical owner `F.sheafify` for sections of `F^#(U)`, map a section to
-- its family of germs in the stalks of `F^#`, pass to the original stalks via the primitive owner
-- map `F.stalkToFiber` (equivalently the hom of `F.sheafifyStalkIso`), and compare with the local-
-- germ realization inside the product presheaf of stalks.
/-- Lemma 6.18.1: for an open set `U`, sections of the sheafification `F^#(U)` form the pullback of
the canonical inclusion `F^#(U) ↪ Π(F)(U)`, the family of germ maps
`F^#(U) → ∏_{x ∈ U} F_x` obtained from `F.sheafifyStalkIso`, the inclusion
`Π(F)(U) → ∏_{x ∈ U} Π(F)_x`, and the product of the canonical stalk maps
`∏_{x ∈ U} F_x → ∏_{x ∈ U} Π(F)_x`. -/
lemma sheafify_section_pullback_diagram (U : Opens X) :
    let Fsharp := F.sheafify.presheaf
    let stalkSections := X.presheafToTypes (fun x ↦ F.stalk x)
    let sectionStalks : Type v := ∀ x : U, F.stalk x.1
    let stalkSectionStalks : Type v := ∀ x : U, stalkSections.stalk x.1
    let ι :
        Fsharp.obj (op U) ⟶ stalkSections.obj (op U) :=
      (subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate).app (op U)
    let σ : Fsharp.obj (op U) ⟶ sectionStalks :=
      fun s x ↦ F.stalkToFiber x.1 (Fsharp.germ U x.1 x.2 s)
    let γ : stalkSections.obj (op U) ⟶ stalkSectionStalks :=
      fun s x ↦ stalkSections.germ U x.1 x.2 s
    let τ : sectionStalks ⟶ stalkSectionStalks :=
      fun s x ↦
        ((stalkFunctor (Type v) x.1).map
          (F.toSheafify ≫
            subpresheafToTypes.subtype (isLocallyGerm F).toPrelocalPredicate)) (s x)
    IsPullback ι σ γ τ := sorry

end
