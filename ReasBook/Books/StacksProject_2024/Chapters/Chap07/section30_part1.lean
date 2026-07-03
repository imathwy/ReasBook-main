import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_30_1 (from Chap07) -/
open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (ℱ : Sheaf J (Type w))

/- Domain-style sampling for Lemma 7.30.1:
- primary domain: localization of a sheaf topos at an object, expressed by the slice-category
  adjunction over that object;
- sampled owner declarations:
  `Over.forgetAdjStar`,
  `Over.forget`,
  `Over.star_obj_left`,
  `Over.star_obj_hom`;
- best owner abstraction: the canonical slice-localization owner is the adjunction
  `Over.forget ℱ ⊣ Over.star ℱ`, packaged by `Over.forgetAdjStar ℱ`;
- primitive data: only the sheaf `ℱ`;
- derived API: the forgetful functor `Over.forget ℱ` and the concrete description of
  `(Over.star ℱ).obj ℋ` through `Over.star_obj_left` and `Over.star_obj_hom`.

Source/core/bridge triage:
- `source-facing`: the identification of the localization morphism at `ℱ` with the standard slice
  forgetful functor and its right adjoint;
- `core/canonical`: `Over.forgetAdjStar ℱ`;
- `bridge/view`: `Over.star_obj_left ℱ` and `Over.star_obj_hom ℱ`, which describe the underlying
  object and structure morphism of the pullback-style inverse-image construction.
-/

/- Lemma 7.30.1: for a sheaf `ℱ` on `(C, J)`, the canonical localization morphism
`Sh(C, J)/ℱ ⥤ Sh(C, J)` is the slice forgetful functor `Over.forget ℱ`, with inverse-image
functor `Over.star ℱ`. The latter sends a sheaf `ℋ` to the slice object over `ℱ` whose
underlying sheaf is `ℱ ⨯ ℋ`, canonically equivalent to the textbook object `ℋ × ℱ / ℱ`; thus
`j_{ℱ!}` is forgetful and `j_ℱ^{-1}` is pullback along `ℱ ⟶ 1`. -/
#check Over.forgetAdjStar ℱ

/- Companion recall: the lower-shriek functor of the localization is the slice forgetful functor
`Over.forget ℱ : Over ℱ ⥤ Sheaf J (Type w)`. -/
#check Over.forget ℱ

/- Companion recall: the inverse-image functor sends `ℋ` to the slice object over `ℱ` with
underlying sheaf `ℱ ⨯ ℋ`. -/
#check Over.star_obj_left ℱ

/- Companion recall: the structure morphism of the inverse-image object is the projection
`ℱ ⨯ ℋ ⟶ ℱ`. -/
#check Over.star_obj_hom ℱ

/-! ### Lemma_7_30_2 (from Chap07) -/
open CategoryTheory

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable (ℱ : Sheaf J (Type w))

/- Domain-style sampling for Lemma 7.30.2:
- primary domain: slice-category sections in a locally cartesian closed topos, specialized to the
  localization slice `Sh(C, J) / ℱ`;
- sampled owner declarations:
  `Over.sections`,
  `Over.toOverSectionsAdj`,
  `forgetAdjToOver`,
  `Over.forgetAdjStar`;
- best owner abstraction: the direct image of the localization at `ℱ` is canonically owned by the
  slice sections functor `Over.sections`, with adjunction `Over.toOverSectionsAdj`; the
  identification of the localization inverse image with `toOver ℱ` is bridge data obtained from
  the two right adjoints to `Over.forget ℱ`;
- primitive data: only the sheaf `ℱ`;
- derived API: `Over.sections`, the adjunction `Over.toOverSectionsAdj`, and the comparison
  isomorphism `toOver ℱ ≅ Over.star ℱ`.

Source/core/bridge triage:
- `source-facing`: the direct-image functor `j_{ℱ,*}` described as the sheaf of local right
  inverses to an object of the slice topos;
- `core/canonical`: `Over.sections` and `Over.toOverSectionsAdj`;
- `bridge/view`: `((Over.forgetAdjStar ℱ).rightAdjointUniq (forgetAdjToOver ℱ)).symm`, which
  identifies the slice inverse-image owner `toOver ℱ` with the localization inverse-image owner
  `Over.star ℱ`.
-/

/- Lemma 7.30.2: in the situation of Lemma 7.30.1, the direct-image functor `j_{ℱ,*}` is obtained
by specializing the canonical slice sections functor `Over.sections`; for an object
`φ : Over ℱ`, this is the sheaf of local right inverses to `φ`, expressed abstractly by the
sections object in the slice category. -/
recall Over.sections

/- Companion recall: the sections functor is canonically right adjoint to `toOver`; this
adjunction is the abstract form of the textbook local-right-inverse construction. -/
recall Over.toOverSectionsAdj

/- Companion bridge: the right-adjoint owner `toOver ℱ` used by `Over.toOverSectionsAdj`
identifies canonically with the localization inverse-image functor `Over.star ℱ`. -/
#check ((Over.forgetAdjStar ℱ).rightAdjointUniq (forgetAdjToOver ℱ)).symm
