import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import stacks_proof.stacks_project.Chap10.Definition_10_88_2
import stacks_proof.stacks_project.Chap10.Lemma_10_11_1
import stacks_proof.stacks_project.Chap10.Lemma_10_11_4
import stacks_proof.stacks_project.Chap10.Lemma_10_79_4
import stacks_proof.stacks_project.Chap10.Lemma_10_82_14
import stacks_proof.stacks_project.Chap10.Lemma_10_88_3
import stacks_proof.stacks_project.Chap10.Lemma_10_88_5
import stacks_proof.stacks_project.Chap10.Proposition_10_88_6.HomInverseSystem

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped TensorProduct MonoidalCategory

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max v w)} [AddCommGroup M] [Module R M]

/-- Helper for Proposition 10.88.6: the product-target Mittag-Leffler condition yields the
eventual factorization condition on transition maps. -/
lemma product_hom_mittag_leffler_gives_stage_factorization
    (F : I ⥤ ModuleCat.{max v w} R)
    (hML : (colimitPresentationHomInverseSystem F
      (ModuleCat.of.{max v w} R ((s : I) → (F.obj s : Type (max v w))))).IsMittagLeffler) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j),
      ∀ (k : I) (hik : i ≤ k), ∃ h : F.obj k ⟶ F.obj j,
        F.map (homOfLE hij) = F.map (homOfLE hik) ≫ h := by
  classical
  intro i
  let G := colimitPresentationHomInverseSystem F
    (ModuleCat.of.{max v w} R ((s : I) → (F.obj s : Type (max v w))))
  obtain ⟨jop, f, hf⟩ := (Functor.isMittagLeffler_iff_subset_range_comp G).mp hML (op i)
  let j := unop jop
  have hij : i ≤ j := leOfHom f.unop
  let insj : F.obj j ⟶ ModuleCat.of.{max v w} R ((s : I) → (F.obj s : Type (max v w))) :=
    ModuleCat.ofHom (LinearMap.single R (fun s : I ↦ (F.obj s : Type (max v w))) j)
  let projj : ModuleCat.of.{max v w} R ((s : I) → (F.obj s : Type (max v w))) ⟶ F.obj j :=
    ModuleCat.ofHom (LinearMap.proj j)
  have hins_proj : insj ≫ projj = 𝟙 (F.obj j) := by
    apply ModuleCat.hom_ext
    ext x
    simp [insj, projj]
  refine ⟨j, hij, ?_⟩
  intro k hik
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
  have hil : i ≤ l := hij.trans hjl
  have hf_unop : f.unop = homOfLE hij := Subsingleton.elim _ _
  have hsubset :
      Set.range (fun g : F.obj j ⟶ ModuleCat.of.{max v w} R ((s : I) → (F.obj s : Type (max v w))) ↦
        F.map (homOfLE hij) ≫ g) ⊆
        Set.range (fun g : F.obj l ⟶ ModuleCat.of.{max v w} R ((s : I) → (F.obj s : Type (max v w))) ↦
          F.map (homOfLE hil) ≫ g) := by
    simpa [G, hf_unop] using hf ((homOfLE hjl).op)
  have hmem :
      F.map (homOfLE hij) ≫ insj ∈
        Set.range (fun g : F.obj j ⟶ ModuleCat.of.{max v w} R ((s : I) → (F.obj s : Type (max v w))) ↦
          F.map (homOfLE hij) ≫ g) := by
    exact ⟨insj, rfl⟩
  obtain ⟨gl, hgl⟩ := hsubset hmem
  refine ⟨F.map (homOfLE hkl) ≫ gl ≫ projj, ?_⟩
  -- Project the stabilized product-valued factorization to the `j`-th coordinate.
  calc
    F.map (homOfLE hij)
        = ((F.map (homOfLE hij) ≫ insj) ≫ projj) := by simp [Category.assoc, hins_proj]
    _ = ((F.map (homOfLE hil) ≫ gl) ≫ projj) := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ projj) hgl.symm
    _ = ((F.map (homOfLE hik) ≫ F.map (homOfLE hkl)) ≫ gl) ≫ projj := by
          have hcomp : homOfLE hil = homOfLE hik ≫ homOfLE hkl := Subsingleton.elim _ _
          rw [← Functor.map_comp, hcomp, Category.assoc]
    _ = F.map (homOfLE hik) ≫ (F.map (homOfLE hkl) ≫ gl ≫ projj) := by
          simp [Category.assoc]

end
