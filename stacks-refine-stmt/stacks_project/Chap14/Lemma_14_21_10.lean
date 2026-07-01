import Mathlib
import stacks_project.Chap14.Lemma_14_18_7
import stacks_project.Chap14.Lemma_14_21_3
import stacks_project.Chap14.Lemma_14_21_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open AlgebraicTopology

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A]

/- 
Domain-style sampling for Lemma 14.21.10:
- primary domain: simplicial-object skeleton/truncation adjunctions in an abelian category, viewed
  through the normalized Moore complex and the chapter's source-facing generated sub simplicial
  object;
- sampled owner declarations:
  `skAdj`,
  `SimplicialObject.generatedByDegreeLE`,
  `SimplicialObject.generatedByDegreeLE_app_subobject`,
  `NormalizedMooreComplex.objX`,
  `NatTrans.mono_iff_mono_app`;
- best owner abstraction:
  `source-facing`: the identification of `(sk n).obj U` with the canonical sub simplicial object
    `U.generatedByDegreeLE n ⊂ U`;
  `core/canonical`: the adjunction owner `skAdj n`, the canonical subobject
    `U.generatedByDegreeLE n : Subobject U`, its inclusion `.arrow`, and the normalized Moore
    complex functor;
  `bridge/view`: the mono proof for the counit together with the subobject comparison APIs
    `Subobject.mk_le_of_comm` and `Subobject.isoOfMkEqMk`.
- primitive data: only the simplicial object `U`, the skeleton counit, the canonical subobject
  `U.generatedByDegreeLE n`, and the normalized Moore degree subobjects;
- derived API: the counit mono companion, the equality of its image subobject with
  `U.generatedByDegreeLE n`, and the resulting isomorphism
  `(sk n).obj U ≅ U.generatedByDegreeLE n`. -/

/-- In degree `i ≤ n`, the counit `((skAdj n).counit.app U)` is an isomorphism. -/
theorem truncatedSkeleton_counit_app_isIso_of_le
    [HasFiniteColimits A]
    (n : ℕ) (U : SimplicialObject A) {i : ℕ} (hi : i ≤ n) :
    IsIso (((skAdj n).counit.app U).app (op (SimplexCategory.mk i))) := by
  let ε : (sk n).obj U ⟶ U := (skAdj n).counit.app U
  let i' : SimplexCategory.Truncated n := ⟨SimplexCategory.mk i, hi⟩
  haveI : IsIso ((skAdj n).unit.app ((truncation n).obj U)) := by infer_instance
  haveI : IsIso ((truncation n).map ε) := by
    exact isIso_of_hom_comp_eq_id ((skAdj n).unit.app ((truncation n).obj U))
      ((skAdj n).right_triangle_components U)
  simpa [ε] using
    ((NatTrans.isIso_iff_isIso_app ((truncation n).map ε)).1 inferInstance (op i'))

section

variable [Abelian A]

-- Proof sketch: by Lemma 14.21.9, the normalized Moore subobjects of `(sk n).obj U` vanish in
-- degrees `> n`, while Lemma 14.21.3 shows that the counit map is an isomorphism in degrees
-- `≤ n`. Hence the induced maps on normalized Moore complexes are monomorphisms in every degree.
-- Applying Lemma 14.18.7 gives that each simplicial degree map of the counit is mono, and
-- therefore the counit itself is a monomorphism in the functor category.
/-- Companion to Lemma 14.21.10: the counit morphism from the simplicial `n`-skeleton of `U` to
`U` is a monomorphism. -/
theorem truncatedSkeleton_counit_mono
    (n : ℕ) (U : SimplicialObject A) :
    Mono ((skAdj n).counit.app U) := by
  let ε : (sk n).obj U ⟶ U := (skAdj n).counit.app U
  exact mono_of_normalizedMooreComplex_degreewise_mono ε fun i ↦ by
    by_cases hi : n < i
    · have hbot : NormalizedMooreComplex.objX ((sk n).obj U) i = ⊥ := by
        simpa using truncatedExtension_normalizedMoore_eq_bot_of_lt n ((truncation n).obj U) hi
      let e₀' :
          ((normalizedMooreComplex A).obj ((sk n).obj U)).X i ≅
            ((⊥ : Subobject (((sk n).obj U).obj (op (SimplexCategory.mk i)))) : A) :=
        eqToIso <|
          congrArg
            (fun S : Subobject (((sk n).obj U).obj (op (SimplexCategory.mk i))) ↦ (S : A)) hbot
      let e₀ := e₀' ≪≫ Subobject.botCoeIsoZero
      exact mono_of_source_iso_zero (((normalizedMooreComplex A).map ε).f i) e₀
    · have hi' : i ≤ n := Nat.le_of_not_gt hi
      haveI : IsIso (ε.app (op (SimplexCategory.mk i))) :=
        truncatedSkeleton_counit_app_isIso_of_le n U hi'
      haveI : Mono (ε.app (op (SimplexCategory.mk i))) := by infer_instance
      haveI : Mono (NormalizedMooreComplex.objX U i).arrow := Subobject.arrow_mono _
      haveI : Mono (NormalizedMooreComplex.objX ((sk n).obj U) i).arrow := Subobject.arrow_mono _
      have hcomp :
          (((normalizedMooreComplex A).map ε).f i) ≫ (NormalizedMooreComplex.objX U i).arrow =
            (NormalizedMooreComplex.objX ((sk n).obj U) i).arrow ≫
              ε.app (op (SimplexCategory.mk i)) := by
        simpa [ε] using
          congrArg (fun φ ↦ φ.f i) ((inclusionOfMooreComplex A).naturality ε)
      have hmono :
          Mono ((((normalizedMooreComplex A).map ε).f i) ≫
            (NormalizedMooreComplex.objX U i).arrow) := by
        rw [hcomp]
        exact mono_comp' (Subobject.arrow_mono _) inferInstance
      letI :
          Mono ((((normalizedMooreComplex A).map ε).f i) ≫
            (NormalizedMooreComplex.objX U i).arrow) := hmono
      exact mono_of_mono (((normalizedMooreComplex A).map ε).f i)
        (NormalizedMooreComplex.objX U i).arrow

private theorem truncation_generatedByDegreeLE_arrow_isIso
    (n : ℕ) (U : SimplicialObject A) :
    IsIso ((truncation n).map (U.generatedByDegreeLE n).arrow) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 ?_
  intro Δ
  cases Δ with
  | op Δ =>
      cases Δ with
      | mk i hi =>
          simpa using generatedByDegreeLE_arrow_app_isIso_of_le U n hi

instance (n : ℕ) (U : SimplicialObject A) : Mono ((skAdj n).counit.app U) :=
  truncatedSkeleton_counit_mono n U

-- Proof sketch: the mono theorem above turns the counit into a simplicial subobject of `U`.
-- Because the counit is an isomorphism in every degree `≤ n`, all generators used in
-- `generatedByDegreeLEObj` lie in this image, so `U.generatedByDegreeLE n` factors through the
-- counit. Conversely, truncating `(U.generatedByDegreeLE n).arrow` gives an isomorphism, and
-- applying the adjunction `skAdj n` yields a factorization of the counit through that inclusion.
/-- The subobject of `U` defined by the counit `((skAdj n).counit.app U)` is exactly the canonical
sub simplicial object of `U` generated by simplices in degrees at most `n`. -/
theorem truncatedSkeletonCounit_subobject_eq_generatedByDegreeLE
    (n : ℕ) (U : SimplicialObject A) :
    Subobject.mk ((skAdj n).counit.app U) = U.generatedByDegreeLE n := by
  let ε : (sk n).obj U ⟶ U := (skAdj n).counit.app U
  let V : SimplicialObject A := (U.generatedByDegreeLE n : SimplicialObject A)
  let η : V ⟶ U := (U.generatedByDegreeLE n).arrow
  haveI : Mono ε := truncatedSkeleton_counit_mono n U
  haveI : Mono η := Subobject.arrow_mono (U.generatedByDegreeLE n)
  haveI : IsIso ((truncation n).map η) :=
    truncation_generatedByDegreeLE_arrow_isIso n U
  let φ : (sk n).obj U ⟶ V :=
    ((skAdj n).homEquiv ((truncation n).obj U) V).symm
      (inv ((truncation n).map η))
  have hφη : φ ≫ η = ε := by
    apply ((skAdj n).homEquiv ((truncation n).obj U) U).injective
    calc
      ((skAdj n).homEquiv ((truncation n).obj U) U) (φ ≫ η) =
          ((skAdj n).homEquiv ((truncation n).obj U) V) φ ≫ (truncation n).map η := by
            simpa using (skAdj n).homEquiv_naturality_right φ η
      _ = 𝟙 _ := by simp [φ]
      _ = ((skAdj n).homEquiv ((truncation n).obj U) U) ε := by
            rw [Adjunction.homEquiv_unit]
            exact ((skAdj n).right_triangle_components U).symm
  have h₁ : Subobject.mk ε ≤ U.generatedByDegreeLE n :=
    Subobject.mk_le_of_comm φ hφη
  have hηε :
      ∀ Δ : SimplexCategoryᵒᵖ, Subobject.mk (η.app Δ) ≤ Subobject.mk (ε.app Δ) := by
    intro Δ
    cases Δ with
    | op Δ =>
        cases Δ with
        | mk m =>
            rw [generatedByDegreeLE_app_subobject]
            exact
              (generatedByDegreeLEObj_isLUB_map_images U n m).2 (by
                rintro _ ⟨i, hi, θ, rfl⟩
                haveI : IsIso (ε.app (op (SimplexCategory.mk i))) :=
                  truncatedSkeleton_counit_app_isIso_of_le n U hi
                refine imageSubobject_le_mk (ε.app (op (SimplexCategory.mk m))) (U.map θ.op)
                  (inv (ε.app (op (SimplexCategory.mk i))) ≫ ((sk n).obj U).map θ.op) ?_
                rw [Category.assoc, ε.naturality]
                simp)
  let ψ : V ⟶ (sk n).obj U :=
    { app := fun Δ ↦ Subobject.ofMkLEMk (η.app Δ) (ε.app Δ) (hηε Δ)
      naturality := by
        intro Δ Δ' f
        apply (cancel_mono (ε.app Δ')).1
        calc
          (V.map f ≫ Subobject.ofMkLEMk (η.app Δ') (ε.app Δ') (hηε Δ')) ≫ ε.app Δ' =
              V.map f ≫ η.app Δ' := by
                rw [Category.assoc, Subobject.ofMkLEMk_comp]
          _ = η.app Δ ≫ U.map f := η.naturality f
          _ = (Subobject.ofMkLEMk (η.app Δ) (ε.app Δ) (hηε Δ) ≫ ε.app Δ) ≫ U.map f := by
                rw [Subobject.ofMkLEMk_comp]
          _ = (Subobject.ofMkLEMk (η.app Δ) (ε.app Δ) (hηε Δ) ≫ ((sk n).obj U).map f) ≫
                ε.app Δ' := by
                  simp_rw [Category.assoc]
                  rw [ε.naturality] }
  have hψη : ψ ≫ ε = η := by
    ext Δ
    simp [ψ]
  have h₂ : U.generatedByDegreeLE n ≤ Subobject.mk ε := by
    let g : V ⟶ (Subobject.mk ε : SimplicialObject A) :=
      ψ ≫ (Subobject.underlyingIso ε).inv
    have hg : g ≫ (Subobject.mk ε).arrow = η := by
      ext Δ
      simpa [g] using congr_app hψη Δ
    simpa [η, V] using Subobject.mk_le_of_comm g hg
  exact le_antisymm h₁ h₂

/-- Lemma 14.21.10: the canonical simplicial `n`-skeleton `i_{n!} sk_n U` is identified with the
canonical simplicial subobject of `U` generated by simplices in degrees at most `n`, namely
`U.generatedByDegreeLE n`. -/
def truncatedSkeletonIsoGeneratedByDegreeLE
    (n : ℕ) (U : SimplicialObject A) :
    (sk n).obj U ≅ (U.generatedByDegreeLE n : SimplicialObject A) :=
  Subobject.isoOfMkEq ((skAdj n).counit.app U) (U.generatedByDegreeLE n)
    (truncatedSkeletonCounit_subobject_eq_generatedByDegreeLE n U)

end

end CategoryTheory
