import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_88_7
import stacks_proof.stacks_project.Chap10.Lemma_10_36_23
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace Module

section RestrictScalars

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite R S] [Algebra.FinitePresentation R S]

/- Source/core/bridge triage:
* source-facing: the restriction-of-scalars stability statement from Lemma `10.88.11`.
* core/canonical: the chapter owner `Module.MittagLeffler` from `Definition_10_88_7`.
* bridge/view: viewing an `S`-module as an `R`-module along `R → S`.
-/
-- Proof sketch: choose a directed colimit presentation of `M` by finitely presented `S`-modules
-- with the eventual factorization property from `Module.MittagLeffler S M`. By Lemma `10.36.23`,
-- each stage is also finitely presented over `R`, and the same transition maps and factorization
-- identities remain valid after restriction of scalars, yielding a Mittag-Leffler presentation
-- over `R`.
omit [Module.Finite R S] [Algebra.FinitePresentation R S] in
/-- Helper for Lemma 10.88.11: restricting scalars on `ModuleCat.of S M` gives the expected
`ModuleCat.of R M`. -/
private noncomputable def restrictScalars_obj_iso :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M) ≅ ModuleCat.of R M :=
  (show ↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S M)) ≃ₗ[R] M from
      { __ := AddEquiv.refl _
        map_smul' := fun _ _ ↦ by simp }).toModuleIso

omit [Module.Finite R S] [Algebra.FinitePresentation R S] in
/-- Helper for Lemma 10.88.11: the textbook eventual-factorization condition is preserved when the
same directed system is viewed by restriction of scalars. -/
private lemma eventual_factorization_restrictScalars
    {I : Type w} [Preorder I]
    (F : I ⥤ ModuleCat S)
    (hfactor :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
          F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h :
          (F ⋙ ModuleCat.restrictScalars (algebraMap R S)).obj k ⟶
            (F ⋙ ModuleCat.restrictScalars (algebraMap R S)).obj j,
        (F ⋙ ModuleCat.restrictScalars (algebraMap R S)).map (homOfLE hij) =
          (F ⋙ ModuleCat.restrictScalars (algebraMap R S)).map (homOfLE hik) ≫ h := by
  intro i
  obtain ⟨j, hij, hj⟩ := hfactor i
  refine ⟨j, hij, ?_⟩
  intro k hik
  obtain ⟨h, hh⟩ := hj k hik
  refine ⟨(ModuleCat.restrictScalars (algebraMap R S)).map h, ?_⟩
  -- Apply the restriction-of-scalars functor to the source factorization equality.
  simpa using congrArg (fun f ↦ (ModuleCat.restrictScalars (algebraMap R S)).map f) hh

/-- Helper for Lemma 10.88.11: a Mittag-Leffler directed system of `S`-modules stays
Mittag-Leffler after restriction of scalars along a finite, finitely presented map `R → S`. -/
private lemma isMittagLefflerDirectedSystem_restrictScalars
    {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat S)
    (c : colimit F ≅ ModuleCat.of S M)
    (hML : IsMittagLefflerDirectedSystem F) :
    IsMittagLefflerDirectedSystem (F ⋙ ModuleCat.restrictScalars (algebraMap R S)) := by
  let G := ModuleCat.restrictScalars (algebraMap R S)
  let cR :
      colimit (F ⋙ G) ≅ ModuleCat.of R M :=
    (preservesColimitIso G F).symm ≪≫ G.mapIso c ≪≫ restrictScalars_obj_iso (R := R) (S := S)
  rcases hML with ⟨hfpS, hallS⟩
  have hfactorS :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
          F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h :=
    ((directed_colimit_presentation_mittag_leffler_tfae F hfpS c).out 3 2).mp hallS
  have hfactorR :
      ∀ i : I, ∃ (j : I) (hij : i ≤ j),
        ∀ (k : I) (hik : i ≤ k), ∃ h :
            (F ⋙ G).obj k ⟶ (F ⋙ G).obj j,
          (F ⋙ G).map (homOfLE hij) = (F ⋙ G).map (homOfLE hik) ≫ h :=
    eventual_factorization_restrictScalars (R := R) (S := S) F hfactorS
  have hfpR : ∀ i, Module.FinitePresentation R ((F ⋙ G).obj i) := by
    intro i
    -- Lemma `10.36.23` transfers finite presentation of each stage from `S` to `R`.
    let _ : Module R (F.obj i) := Module.compHom (F.obj i) (algebraMap R S)
    let _ : IsScalarTower R S (F.obj i) := IsScalarTower.restrictScalars R S (F.obj i)
    simpa using
      (Module.FinitePresentation.iff_of_finite_finitePresentation
        (R := R) (S := S) (M := F.obj i)).2 (hfpS i)
  have hallR :
      ∀ N : ModuleCat R, (colimitPresentationHomInverseSystem (F ⋙ G) N).IsMittagLeffler :=
    ((directed_colimit_presentation_mittag_leffler_tfae (F ⋙ G) hfpR cR).out 2 3).mp hfactorR
  exact ⟨hfpR, hallR⟩

/-- Lemma 10.88.11: if `R → S` is finite and finitely presented, then every Mittag-Leffler
`S`-module is Mittag-Leffler when viewed as an `R`-module by restriction of scalars. -/
@[stacks 05CQ]
theorem mittagLeffler_restrictScalars_of_finite_finitePresentation [MittagLeffler S M] :
    MittagLeffler R M := by
  classical
  let P : MittagLefflerPresentation S M := Classical.choice (MittagLeffler.exists_presentation
    (R := S) (M := M))
  letI : Preorder P.index := P.indexPreorder
  letI : Nonempty P.index := P.indexNonempty
  letI : IsDirectedOrder P.index := P.indexDirected
  let G := ModuleCat.restrictScalars (algebraMap R S)
  let cS : colimit P.diagram ≅ ModuleCat.of S M := Classical.choice P.colimitIso
  let cR :
      colimit (P.diagram ⋙ G) ≅ ModuleCat.of R M :=
    (preservesColimitIso G P.diagram).symm ≪≫ G.mapIso cS ≪≫
      restrictScalars_obj_iso (R := R) (S := S)
  have hMLR : IsMittagLefflerDirectedSystem (P.diagram ⋙ G) :=
    isMittagLefflerDirectedSystem_restrictScalars
      (R := R) (S := S) (M := M) P.diagram cS P.presentation_isMittagLeffler
  -- Reuse the same index category and diagram after forgetting `S`-linearity.
  exact ⟨⟨{
    index := P.index
    indexPreorder := P.indexPreorder
    indexNonempty := P.indexNonempty
    indexDirected := P.indexDirected
    diagram := P.diagram ⋙ G
    presentation_isMittagLeffler := hMLR
    colimitIso := ⟨cR⟩
  }⟩⟩

end RestrictScalars

end Module
