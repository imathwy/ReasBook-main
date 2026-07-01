import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u v

section

variable {R : Type u} [CommRing R]
variable {Λ : Type v} [CommRing Λ] [Algebra R Λ]

/-- The canonical diagram of selected `R`-algebras over `Λ`, viewed in `CommAlgCat R`. -/
abbrev selectedAlgebrasOverTargetDiagram
    (P : ObjectProperty (Over (CommAlgCat.of R Λ))) :
    P.FullSubcategory ⥤ CommAlgCat R :=
  ObjectProperty.ι P ⋙ Over.forget (CommAlgCat.of R Λ)

/-- The canonical cocone from the selected `R`-algebras over `Λ` to `Λ`. -/
abbrev selectedAlgebrasOverTargetCocone
    (P : ObjectProperty (Over (CommAlgCat.of R Λ))) :
    Cocone (selectedAlgebrasOverTargetDiagram P) :=
  (Over.forgetCocone (CommAlgCat.of R Λ)).whisker (ObjectProperty.ι P)

/-
Domain sampling:
* Primary domain: filtered colimit presentations inside the over category
  `Over (CommAlgCat.of R Λ)`.
* Core/canonical declarations inspected:
  - `ObjectProperty.ι`
  - `Over.forget`
  - `Over.forgetCocone`
  - `ObjectProperty.initial_ι`
* Owner abstraction: the ambient owner is the canonical over-category diagram
  `ObjectProperty.ι P ⋙ Over.forget (CommAlgCat.of R Λ)` together with its canonical cocone
  `(Over.forgetCocone (CommAlgCat.of R Λ)).whisker (ObjectProperty.ι P)`.
* Layer triage:
  - `source-facing`: the factorization criterion for selected finitely presented stages;
  - `core/canonical`: `ObjectProperty.ι`, `Over.forget`, and `Over.forgetCocone`;
  - `bridge/view`: the finite-presentation hypothesis selecting which over-objects participate.
* Primitive vs. derived:
  - primitive data: the object property `P`;
  - derived API: the induced diagram to `CommAlgCat R` and its canonical cocone to `Λ`.
-/

-- Proof sketch: for `(→)`, a map from a finitely presented `R`-algebra into the filtered colimit
-- `Λ` factors through some selected stage by the finite-presentation factorization property. For
-- `(←)`, compare the selected full subcategory with the filtered category of all finitely
-- presented `R`-algebras over `Λ`; the factorization hypothesis makes the inclusion cofinal, so
-- the canonical colimit over all finitely presented stages restricts to a filtered colimit over
-- the selected ones.
/-- Lemma 10.127.4: if every selected `R`-algebra over `Λ` is finitely presented over `R`, then the
selected family presents `Λ` as a filtered colimit exactly when every finitely presented
`R`-algebra mapping to `Λ` factors through one of the selected stages. -/
theorem selectedAlgebrasOverTarget_isFilteredColimit_iff_factorization
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hPfp : ∀ A : Over (CommAlgCat.of R Λ), P A → Algebra.FinitePresentation R A.left) :
    (IsFiltered P.FullSubcategory ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone P))) ↔
      ∀ (A : Over (CommAlgCat.of R Λ)) (_hA : Algebra.FinitePresentation R A.left),
        ∃ B : P.FullSubcategory, Nonempty (A ⟶ B.obj) :=
  sorry

end
