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

/-- Helper for Lemma 10.127.4: the full subcategory of over-objects whose source algebra is
finitely presented over `R`. -/
private abbrev finitelyPresentedOverTargetProperty :
    ObjectProperty (Over (CommAlgCat.of R Λ)) :=
  fun A : Over (CommAlgCat.of R Λ) ↦ Algebra.FinitePresentation R A.left

/-- Helper for Lemma 10.127.4: a commutative factorization of the structure maps packages into a
morphism in the over category. -/
private lemma over_hom_of_factorization
    {A B : Over (CommAlgCat.of R Λ)}
    (u : A.left ⟶ B.left) (hu : u ≫ B.hom = A.hom) :
    Nonempty (A ⟶ B) := by
  -- Proof comment: `Over.homMk` is the canonical constructor for morphisms in the slice category.
  exact ⟨Over.homMk u hu⟩

/-- Helper for Lemma 10.127.4: a finitely presented `R`-algebra is finitely presentable in
`CommAlgCat R`, after resolving the cross-universe bridge from the under-category owner theorem. -/
private lemma commAlgCat_isFinitelyPresentable_of_finitePresentation
    (A : CommAlgCat R) (hA : Algebra.FinitePresentation R A) :
    IsFinitelyPresentable A := by
  -- Route correction: the missing step is not the factorization argument itself, but the
  -- cross-universe transport from `CommRingCat.isFinitelyPresentable_under` to `CommAlgCat R`.
  -- TODO: lift the under-category owner theorem through the appropriate `ULift` comparison and the
  -- `CommAlgCat`/`Under` equivalence, then transport back to `A`.
  sorry

/-- Helper for Lemma 10.127.4: the forward implication reduces to factoring a map from a finitely
presented `R`-algebra through a colimit stage. -/
private lemma finitely_presentable_over_target_factors_through_selected_stage
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hcolim : IsFiltered P.FullSubcategory ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone P)))
    (A : Over (CommAlgCat.of R Λ))
    (hA : Algebra.FinitePresentation R A.left) :
    ∃ B : P.FullSubcategory, Nonempty (A ⟶ B.obj) := by
  let e := ShrinkHoms.equivalence P.FullSubcategory
  let Dsmall : ShrinkHoms P.FullSubcategory ⥤ CommAlgCat R :=
    e.inverse ⋙ selectedAlgebrasOverTargetDiagram P
  let csmall : Cocone Dsmall :=
    (selectedAlgebrasOverTargetCocone P).whisker e.inverse
  obtain ⟨hcΛ⟩ := hcolim.2
  let _ : IsFiltered P.FullSubcategory := hcolim.1
  let _ : IsFiltered (ShrinkHoms P.FullSubcategory) := IsFiltered.of_equivalence e
  let _ : e.inverse.Final := by infer_instance
  have hfpA : IsFinitelyPresentable A.left :=
    commAlgCat_isFinitelyPresentable_of_finitePresentation (R := R) A.left hA
  have hcsmall : IsColimit csmall := by
    -- Proof comment: reindex the colimit along the small-model equivalence of the index category.
    exact (Functor.Final.isColimitWhiskerEquiv e.inverse
      (selectedAlgebrasOverTargetCocone P)).symm hcΛ
  obtain ⟨B, u, hu⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcsmall A.hom
  have hu : u ≫ B.obj.hom = A.hom := by
    -- Proof comment: the represented functor surjectivity statement gives the required
    -- factorization of the map from `A.left` into the colimit point `Λ`.
    simpa using hu
  exact ⟨e.inverse.obj B, over_hom_of_factorization u hu⟩

/-- Helper for Lemma 10.127.4: the canonical cocone of all finitely presented `R`-algebras over
`Λ` should be the ambient filtered colimit presentation used in the backward implication. -/
private lemma finitely_presented_stages_over_target_isFilteredColimit :
    IsFiltered (finitelyPresentedOverTargetProperty (R := R) (Λ := Λ)).FullSubcategory ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone
        (finitelyPresentedOverTargetProperty (R := R) (Λ := Λ)))) := by
  -- Proof comment: this is the local replacement for Lemma 10.127.1 required by the source proof.
  -- TODO: prove that all finitely presented `R`-algebras over `Λ` form a filtered category and
  -- that their canonical cocone exhibits `Λ` as the filtered colimit, without importing the later
  -- file `Lemma_10_127_1.lean`.
  sorry

/-- Helper for Lemma 10.127.4: once the ambient finitely presented over-category is filtered, the
factorization hypothesis makes the selected inclusion final. -/
private lemma selected_stages_final_in_finitely_presented_stages
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hPfp : ∀ A : Over (CommAlgCat.of R Λ), P A → Algebra.FinitePresentation R A.left)
    (hfactor :
      ∀ (A : Over (CommAlgCat.of R Λ)) (_hA : Algebra.FinitePresentation R A.left),
        ∃ B : P.FullSubcategory, Nonempty (A ⟶ B.obj))
    [IsFiltered (finitelyPresentedOverTargetProperty (R := R) (Λ := Λ)).FullSubcategory] :
    let Q := finitelyPresentedOverTargetProperty (R := R) (Λ := Λ)
    let incl : P.FullSubcategory ⥤ Q.FullSubcategory :=
      ObjectProperty.ιOfLE (fun A hPA ↦ hPfp A hPA)
    incl.Final ∧ IsFiltered P.FullSubcategory := by
  let Q := finitelyPresentedOverTargetProperty (R := R) (Λ := Λ)
  let incl : P.FullSubcategory ⥤ Q.FullSubcategory :=
    ObjectProperty.ιOfLE (fun A hPA ↦ hPfp A hPA)
  have hExists : ∀ A : Q.FullSubcategory, ∃ B : P.FullSubcategory, Nonempty (A ⟶ incl.obj B) := by
    intro A
    rcases hfactor A.obj A.property with ⟨B, ⟨f⟩⟩
    -- Proof comment: morphisms in a full subcategory are just the underlying over-category maps.
    exact ⟨B, ⟨ObjectProperty.homMk f⟩⟩
  -- Proof comment: Lemma 4.19.3 is exactly the generic owner theorem for fully faithful
  -- inclusions into a filtered category.
  exact ⟨Functor.final_of_exists_of_isFiltered_of_fullyFaithful incl hExists,
    IsFiltered.of_exists_of_isFiltered_of_fullyFaithful incl hExists⟩

/-- Helper for Lemma 10.127.4: after identifying the selected stages as a final subcategory of all
finitely presented stages, the ambient colimit presentation transfers to the selected diagram. -/
private lemma selected_stages_isFilteredColimit_of_factorization
    (P : ObjectProperty (Over (CommAlgCat.of R Λ)))
    (hPfp : ∀ A : Over (CommAlgCat.of R Λ), P A → Algebra.FinitePresentation R A.left)
    (hfactor :
      ∀ (A : Over (CommAlgCat.of R Λ)) (_hA : Algebra.FinitePresentation R A.left),
        ∃ B : P.FullSubcategory, Nonempty (A ⟶ B.obj)) :
    IsFiltered P.FullSubcategory ∧
      Nonempty (IsColimit (selectedAlgebrasOverTargetCocone P)) := by
  let Q := finitelyPresentedOverTargetProperty (R := R) (Λ := Λ)
  let incl : P.FullSubcategory ⥤ Q.FullSubcategory :=
    ObjectProperty.ιOfLE (fun A hPA ↦ hPfp A hPA)
  have hQ := finitely_presented_stages_over_target_isFilteredColimit (R := R) (Λ := Λ)
  letI : IsFiltered Q.FullSubcategory := hQ.1
  have hfinal : incl.Final ∧ IsFiltered P.FullSubcategory :=
    selected_stages_final_in_finitely_presented_stages (R := R) (Λ := Λ) P hPfp hfactor
  letI : incl.Final := hfinal.1
  obtain ⟨hcQ⟩ := hQ.2
  refine ⟨hfinal.2, ?_⟩
  -- Proof comment: finality lets us transfer the ambient colimit witness directly to the selected
  -- subdiagram by whiskering along the inclusion.
  exact ⟨(Functor.Final.isColimitWhiskerEquiv incl
    (selectedAlgebrasOverTargetCocone Q)).symm hcQ⟩

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
  by
    constructor
    · intro hcolim A hA
      -- Proof comment: this is the compactness direction of the source proof.
      exact finitely_presentable_over_target_factors_through_selected_stage
        (R := R) (Λ := Λ) P hcolim A hA
    · intro hfactor
      -- Proof comment: this is the source-faithful backward route through the ambient category of
      -- all finitely presented stages and a final inclusion of the selected subcategory.
      exact selected_stages_isFilteredColimit_of_factorization
        (R := R) (Λ := Λ) P hPfp hfactor

end
