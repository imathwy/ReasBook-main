import Mathlib
import stacks_project.Chap10.Definition_10_88_7
import stacks_project.Chap10.Proposition_10_88_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u

namespace Module

section

variable {R : Type u} [CommRing R]
variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type u} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: Mittag-Leffler criteria for directed colimit presentations of modules;
- sampled owner declarations of the same kind:
  `Module.MittagLeffler`,
  `colimitPresentationHomInverseSystem`,
  `directed_colimit_presentation_mittag_leffler_tfae`,
  `TensorProduct.rTensorHomEquivHomRTensor`;
- owner abstraction: the chapter owner `Module.MittagLeffler`, with
  `directed_colimit_presentation_mittag_leffler_tfae` as the canonical presentation criterion;
- primitive data: the directed system `F`, its colimit identification `c`, the finite-free stage
  hypotheses, and the dual inverse-system Mittag-Leffler hypothesis;
- derived API: the source-facing bridge theorem below upgrading that dual hypothesis to
  `Module.MittagLeffler R M`.
-/
-- Proof sketch: start from the given finite free presentation and use the finite-free dual tensor-
-- Hom identification to promote the dual inverse-system Mittag-Leffler hypothesis to the universal
-- Hom inverse-system condition in Proposition `10.88.6`; the resulting presentation then witnesses
-- that `M` is Mittag-Leffler.
private theorem exists_factor_of_postcomp_range_subset
    [Nontrivial R]
    {A : Type u} [AddCommGroup A] [Module R A]
    {B : Type u} [AddCommGroup B] [Module R B]
    {C : Type u} [AddCommGroup C] [Module R C]
    [Module.Free R B] [Module.Finite R B]
    (u : A →ₗ[R] B) (v : A →ₗ[R] C)
    (h : Set.range (fun g : ModuleCat.of R B ⟶ ModuleCat.of R R ↦ ModuleCat.ofHom u ≫ g) ⊆
      Set.range (fun g : ModuleCat.of R C ⟶ ModuleCat.of R R ↦ ModuleCat.ofHom v ≫ g)) :
    ∃ w : C →ₗ[R] B, u = w.comp v := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex R B) R B := Module.Free.chooseBasis R B
  letI : Finite (Module.Free.ChooseBasisIndex R B) := Module.Finite.finite_basis b
  choose ψ hψ using fun i ↦ h ⟨ModuleCat.ofHom (b.coord i), by rfl⟩
  let e : ((i : Module.Free.ChooseBasisIndex R B) → R) ≃ₗ[R] B := b.equivFun.symm
  let w : C →ₗ[R] B := e.toLinearMap.comp (LinearMap.pi fun i ↦ (ψ i).hom)
  refine ⟨w, ?_⟩
  ext a
  apply b.equivFun.injective
  ext i
  change b.coord i (u a) = b.coord i (e ((LinearMap.pi fun i ↦ (ψ i).hom) (v a)))
  rw [Module.Basis.coord_equivFun_symm]
  simpa [LinearMap.comp_apply] using
    congrArg (fun f : ModuleCat.of R A ⟶ ModuleCat.of R R ↦ f.hom a) (hψ i).symm

private theorem finite_free_dual_isMittagLeffler_gives_factorization
    [Nontrivial R]
    (F : I ⥤ ModuleCat R)
    (hfree : ∀ i, Module.Free R (F.obj i))
    (hfinite : ∀ i, Module.Finite R (F.obj i))
    (hdualML : (colimitPresentationHomInverseSystem F (ModuleCat.of R R)).IsMittagLeffler) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
        F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  intro i
  let G := colimitPresentationHomInverseSystem F (ModuleCat.of R R)
  obtain ⟨jop, f, hf⟩ := (Functor.isMittagLeffler_iff_subset_range_comp G).mp hdualML (op i)
  let j := unop jop
  have hij : i ≤ j := leOfHom f.unop
  refine ⟨j, hij, ?_⟩
  intro k hik
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
  have hil : i ≤ l := hij.trans hjl
  have hf_unop : f.unop = homOfLE hij := Subsingleton.elim _ _
  have hsubset :
      Set.range (fun g : F.obj j ⟶ ModuleCat.of R R ↦ F.map (homOfLE hij) ≫ g) ⊆
        Set.range (fun g : F.obj l ⟶ ModuleCat.of R R ↦ F.map (homOfLE hil) ≫ g) := by
    simpa [G, hf_unop] using hf (homOfLE hjl).op
  letI := hfree j
  letI := hfinite j
  obtain ⟨hl, hfac⟩ := exists_factor_of_postcomp_range_subset
    ((F.map (homOfLE hij)).hom) ((F.map (homOfLE hil)).hom) hsubset
  refine ⟨F.map (homOfLE hkl) ≫ ModuleCat.ofHom hl, ?_⟩
  calc
    F.map (homOfLE hij) = F.map (homOfLE hil) ≫ ModuleCat.ofHom hl := by
      apply ModuleCat.hom_ext
      exact hfac
    _ = F.map (homOfLE hik) ≫ (F.map (homOfLE hkl) ≫ ModuleCat.ofHom hl) := by
      have hcomp : homOfLE hil = homOfLE hik ≫ homOfLE hkl := Subsingleton.elim _ _
      rw [hcomp, Functor.map_comp, Category.assoc]

/-- Remark 10.88.8: for a directed colimit presentation of `M` by finite free `R`-modules, it is
sufficient that the inverse system of duals `i ↦ Hom_R(Mᵢ, R)` be Mittag-Leffler in order for `M`
to be Mittag-Leffler. -/
theorem mittagLeffler_of_finite_free_presentation_of_dual_isMittagLeffler
    (F : I ⥤ ModuleCat R)
    (c : colimit F ≅ ModuleCat.of R M)
    (hfree : ∀ i, Module.Free R (F.obj i))
    (hfinite : ∀ i, Module.Finite R (F.obj i))
    (hdualML : (colimitPresentationHomInverseSystem F (ModuleCat.of R R)).IsMittagLeffler) :
    MittagLeffler R M := by
  classical
  by_cases hR : Nontrivial R
  · letI := hR
    have hfp : ∀ i, Module.FinitePresentation R (F.obj i) := by
      intro i
      letI := hfree i
      letI := hfinite i
      exact Module.finitePresentation_of_projective R (F.obj i)
    have hfactor :=
      finite_free_dual_isMittagLeffler_gives_factorization F hfree hfinite hdualML
    have hallN : ∀ N : ModuleCat R, (colimitPresentationHomInverseSystem F N).IsMittagLeffler :=
      ((directed_colimit_presentation_mittag_leffler_tfae F hfp c).out 2 3).mp hfactor
    exact ⟨⟨{
      index := I
      indexPreorder := inferInstance
      indexNonempty := inferInstance
      indexDirected := inferInstance
      diagram := F
      presentation_isMittagLeffler := ⟨hfp, hallN⟩
      colimitIso := ⟨c⟩
    }⟩⟩
  · letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    letI : Subsingleton M := Module.subsingleton R M
    letI : Module.Free R M := Module.Free.of_subsingleton R M
    letI : Module.Finite R M := ⟨∅, by
      ext x
      simp [Subsingleton.elim x 0]⟩
    letI : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
    infer_instance

end

end Module
