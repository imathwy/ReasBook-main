import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap07.Lemma_7_12_4

-- Declarations for this item will be appended below by the statement pipeline.

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
recall GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv

#check
  (J.uliftSheafifiedRepresentableHomEquiv ℱ U :
    (h[U]^#[J] ⟶ ℱ) ≃ ℱ.obj.obj (op U))

/-- Lemma 18.5.2 (1), companion form: the canonical equivalence
`Hom(h_U^#, ℱ) ≃ ℱ(U)` is bijective. -/
@[stacks 03AB]
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
recall Sheaf.adjunction

#check
  ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv 𝒢 𝒜 :
    ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj 𝒢 ⟶ 𝒜) ≃
      (𝒢 ⟶ (sheafForget J).obj 𝒜))

/-- Lemma 18.5.2 (2), companion form: the free-forgetful adjunction equivalence on sheaves is
bijective. -/
@[stacks 03AB]
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
@[stacks 03AB]
def freeAbelianSheafifiedRepresentableHomEquivSections :
    ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj h[U]^#[J] ⟶ 𝒜) ≃
      𝒜.obj.obj (op U) :=
  ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv h[U]^#[J] 𝒜).trans
    (J.uliftSheafifiedRepresentableHomEquiv ((sheafForget J).obj 𝒜) U)

/-- Lemma 18.5.2 (3), companion form: the specialization to the sheafified representable is
bijective. -/
@[stacks 03AB]
theorem freeAbelianSheafifiedRepresentableHomEquivSections_bijective :
    Function.Bijective (freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜) :=
  (freeAbelianSheafifiedRepresentableHomEquivSections J U 𝒜).bijective

end FreeAbelianRepresentable

end CategoryTheory
