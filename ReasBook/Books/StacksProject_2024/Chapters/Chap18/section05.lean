import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_18_5_1 (from Chap18) -/
open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type v)] [HasWeakSheafify J AddCommGrpCat.{v}]
variable [J.PreservesSheafification AddCommGrpCat.free]
variable (𝒢 : Cᵒᵖ ⥤ Type v)

/- Domain-style sampling for Definition 18.5.1:
- primary domain: sheafification on a site and postcomposition by the free abelian group functor;
- sampled owner declarations:
  `ℤ_ 𝒢`,
  `AddCommGrpCat.free`,
  `Sheaf.composeAndSheafify`,
  `presheafToSheafCompComposeAndSheafifyIso`,
  `sheafifyComposeIso`;
- best owner abstraction: the sheaf-level owner `Sheaf.composeAndSheafify J AddCommGrpCat.free`;
- primitive data: the site `(C, J)`, a set-valued presheaf `𝒢`, and the chapter owner
  `ℤ_ 𝒢 := 𝒢 ⋙ AddCommGrpCat.free`;
- derived API: the source-facing owner `freeAbelianSheaf J 𝒢`, written `(ℤ_ 𝒢)^#[J]`, and its
  canonical comparison to the owner-level construction.

Source/core/bridge triage:
- `source-facing`: the free abelian sheaf `(ℤ_ 𝒢)^#`;
- `core/canonical`: `Sheaf.composeAndSheafify J AddCommGrpCat.free`;
- `bridge/view`: `presheafToSheafCompComposeAndSheafifyIso`, with
  `sheafifyComposeIso` as its objectwise specialization. -/

/-- The free abelian sheaf `(ℤ_ 𝒢)^#` on a set-valued presheaf `𝒢`. -/
abbrev freeAbelianSheaf : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (ℤ_ 𝒢)

namespace FreeAbelianSheaf

/- Textbook notation for the free abelian sheaf `(ℤ_ 𝒢)^#`. Since the site is not inferable from
the presheaf `𝒢`, we keep it explicit in the notation `(ℤ_ 𝒢)^#[J]`. -/
scoped notation:max "(ℤ_ " G ")^#[" J "]" =>
  CategoryTheory.freeAbelianSheaf J G

end FreeAbelianSheaf

open scoped FreeAbelianSheaf

/- Definition 18.5.1: the free abelian sheaf `(ℤ_ 𝒢)^#` is obtained by sheafifying the free
abelian presheaf `ℤ_ 𝒢`. -/
#check ((ℤ_ 𝒢)^#[J] : Sheaf J AddCommGrpCat.{v})

/- Companion recall: the sheaf-level owner is `Sheaf.composeAndSheafify`. -/
recall CategoryTheory.Sheaf.composeAndSheafify

#check (Sheaf.composeAndSheafify J AddCommGrpCat.free :
  Sheaf J (Type v) ⥤ Sheaf J AddCommGrpCat.{v})

/- Companion bridge: the owner-level free-abelian-sheaf construction on `𝒢^#` identifies
canonically with the source-facing object `(ℤ_ 𝒢)^#`. -/
#check ((presheafToSheafCompComposeAndSheafifyIso J AddCommGrpCat.free).app 𝒢 :
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj ((presheafToSheaf J (Type v)).obj 𝒢) ≅
    (ℤ_ 𝒢)^#[J])

end

end CategoryTheory

/-! ### Lemma_18_5_2 (from Chap18) -/
open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology
open scoped SheafifiedRepresentable

noncomputable section

universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma 18.5.2:
- primary domain: sheafification and adjunctions for sheaves of sets and abelian groups on a
  site;
- sampled owner declarations:
  `GrothendieckTopology.sheafifiedRepresentable`,
  `GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv`,
  `sheafificationAdjunction`,
  `Sheaf.adjunction`;
- best owner abstraction: the chapter-7 sheafified-representable owner
  `J.sheafifiedRepresentable` together with its canonical Hom-to-sections equivalence
  `J.uliftSheafifiedRepresentableHomEquiv`, and the sheaf-level free-forgetful adjunction
  `Sheaf.adjunction J AddCommGrpCat.adj`;
- primitive data: the site `(C, J)`, an object `U : C`, a sheaf of sets `ℱ`, and a sheaf of
  abelian groups `𝒜`;
- derived API: the composite equivalence in part (3), obtained by specializing the sheaf
  adjunction to `h[U]^#[J]` and then applying the canonical sheafified-representable equivalence.

Source/core/bridge triage:
- `core/canonical`: `J.uliftSheafifiedRepresentableHomEquiv` and
  `(Sheaf.adjunction J AddCommGrpCat.adj).homEquiv`;
- `bridge/view`: the part (3) composite equivalence;
- `source-facing`: the textbook identifications `Hom(h_U^#, ℱ) ≃ ℱ(U)` and
  `Hom(ℤ_{h_U^#}^#, 𝒜) ≃ 𝒜(U)`.

This file should therefore reuse the owner declarations for parts (1) and (2), and keep only the
part (3) composite as local derived API.
-/

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section SheafifiedRepresentable

variable [HasWeakSheafify J (Type (max u v))]
variable (U : C) (ℱ : Sheaf J (Type (max u v)))

/- Lemma 18.5.2 (1): the canonical equivalence
`Hom(h_U^#, ℱ) ≃ ℱ(U)` is already the chapter-7 owner declaration below. -/
#check
  (J.uliftSheafifiedRepresentableHomEquiv ℱ U :
    (h[U]^#[J] ⟶ ℱ) ≃ ℱ.obj.obj (op U))

/-- Lemma 18.5.2 (1), companion form: the canonical equivalence
`Hom(h_U^#, ℱ) ≃ ℱ(U)` is bijective. -/
theorem sheafifiedRepresentableHomEquivSections_bijective :
    Function.Bijective (J.uliftSheafifiedRepresentableHomEquiv ℱ U) :=
  (J.uliftSheafifiedRepresentableHomEquiv ℱ U).bijective

end SheafifiedRepresentable

section FreeAbelianAdjunction

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
variable (𝒢 : Sheaf J (Type (max u v))) (𝒜 : Sheaf J AddCommGrpCat.{max u v})

/- Lemma 18.5.2 (2): the free-forgetful comparison is exactly the sheaf-level adjunction
hom-equivalence below. -/
#check
  ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv 𝒢 𝒜 :
    ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj 𝒢 ⟶ 𝒜) ≃
      (𝒢 ⟶ (sheafForget J).obj 𝒜))

/-- Lemma 18.5.2 (2), companion form: the free-forgetful adjunction equivalence on sheaves is
bijective. -/
theorem freeAbelianSheafHomEquivUnderlyingSheaf_bijective :
    Function.Bijective ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv 𝒢 𝒜) :=
  ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv 𝒢 𝒜).bijective

end FreeAbelianAdjunction

section FreeAbelianRepresentable

variable [HasWeakSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
variable (U : C) (𝒜 : Sheaf J AddCommGrpCat.{max u v})

/-- Lemma 18.5.2 (3): specializing the free-forgetful sheaf adjunction to the sheafified
representable `h[U]^#[J]` identifies morphisms `ℤ_{h_U^#}^# ⟶ 𝒜` with the sections `𝒜(U)`. -/
noncomputable def freeAbelianSheafifiedRepresentableHomEquivSections :
    ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J] ⟶ 𝒜) ≃
      𝒜.obj.obj (op U) :=
  ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[U]^#[J] 𝒜).trans
    (J.uliftSheafifiedRepresentableHomEquiv ((sheafForget J).obj 𝒜) U)

/-- Lemma 18.5.2 (3), companion form: the specialization to the sheafified representable is
bijective. -/
theorem freeAbelianSheafifiedRepresentableHomEquivSections_bijective :
    Function.Bijective (freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜) :=
  (freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜).bijective

end FreeAbelianRepresentable

end CategoryTheory

/-! ### Lemma_18_5_3 (from Chap18) -/
open CategoryTheory Opposite

universe v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))] [HasWeakSheafify J AddCommGrpCat]
variable [J.HasSheafCompose AddCommGrpCat.free]
variable (𝒢 : Cᵒᵖ ⥤ Type (max u v))

/- Domain-style sampling for Lemma 18.5.3:
- primary domain: sheafification on sites and postcomposition with the free abelian group functor;
- sampled owner API:
  `Sheaf.composeAndSheafify`,
  `sheafificationAdjunction`,
  `sheafifyComposeIso`,
  `sheafComposeIso_hom_fac`;
- best owner abstraction: the canonical comparison isomorphism `sheafifyComposeIso` for
  postcomposition by a functor preserving sheafification;
- primitive data: the site `(C, J)`, the presheaf `𝒢`, and the functor `AddCommGrpCat.free`;
- derived API: the specialized comparison
  `sheafify J (𝒢 ⋙ AddCommGrpCat.free) ≅ sheafify J 𝒢 ⋙ AddCommGrpCat.free`.

Source/core/bridge triage:
- `source-facing`: the textbook identification `𝒵_𝒢^# = (𝒵_{𝒢^#})^#`;
- `core/canonical`: `sheafifyComposeIso`;
- `bridge/view`: the specialization to `AddCommGrpCat.free`. -/

/- Lemma 18.5.3: for a set-valued presheaf `𝒢` on a site `(C, J)`, sheafifying the
presheaf of free abelian groups generated by `𝒢` identifies canonically with applying the
free abelian group functor to the sheafification of `𝒢`. This is the library-facing form of
`𝒵_𝒢^# = (𝒵_{𝒢^#})^#`. -/
recall CategoryTheory.sheafifyComposeIso

#check (sheafifyComposeIso J AddCommGrpCat.free 𝒢 :
  sheafify J (𝒢 ⋙ AddCommGrpCat.free) ≅ sheafify J 𝒢 ⋙ AddCommGrpCat.free)
