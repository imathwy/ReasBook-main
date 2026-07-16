import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import StacksProject_2024.stacks_project.Chap13.Lemma_13_10_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex

universe v u

namespace CochainComplex

/-
Semantic recall hit: `lean_leansearch` returned
`CochainComplex.trianglehOfDegreewiseSplit` and
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`; Chapter 13 already packages
their distinguishedness bridge as
`triangle_mk_mem_distTriang_of_degreewise_split_short_complex`, so the source-facing Chapter 22
statement should reuse that existing repository owner API.
-/

section

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasZeroObject V] [HasBinaryBiproducts V]

local notation "K" => HomotopyCategory V (up ℤ)

/-- Lemma 22.27.1 (1): an admissible short exact sequence of differential graded objects,
formalized as a degreewise split short complex of cochain complexes, yields the associated
distinguished triangle in the homotopy category. -/
@[stacks 09P6]
theorem trianglehOfDegreewiseSplit_distinguished
    (S : ShortComplex (CochainComplex V ℤ))
    (σ : ∀ n : ℤ, (S.map (eval V (up ℤ) n)).Splitting) :
    trianglehOfDegreewiseSplit S σ ∈ distTriang K :=
  by
    simpa using triangle_mk_mem_distTriang_of_degreewise_split_short_complex S σ

/-- Lemma 22.27.1 (2): in the triangle attached to a degreewise split short complex, the
composition `x ⟶ y ⟶ z` is zero in the homotopy category. -/
@[stacks 09P6, simp]
theorem trianglehOfDegreewiseSplit_comp_zero₁₂
    (S : ShortComplex (CochainComplex V ℤ))
    (σ : ∀ n : ℤ, (S.map (eval V (up ℤ) n)).Splitting) :
    (trianglehOfDegreewiseSplit S σ).mor₁ ≫ (trianglehOfDegreewiseSplit S σ).mor₂ = 0 :=
  comp_distTriang_mor_zero₁₂ _ (trianglehOfDegreewiseSplit_distinguished S σ)

/-- Lemma 22.27.1 (3): in the triangle attached to a degreewise split short complex, the
composition `y ⟶ z ⟶ x[1]` is zero in the homotopy category. -/
@[stacks 09P6, simp]
theorem trianglehOfDegreewiseSplit_comp_zero₂₃
    (S : ShortComplex (CochainComplex V ℤ))
    (σ : ∀ n : ℤ, (S.map (eval V (up ℤ) n)).Splitting) :
    (trianglehOfDegreewiseSplit S σ).mor₂ ≫ (trianglehOfDegreewiseSplit S σ).mor₃ = 0 :=
  comp_distTriang_mor_zero₂₃ _ (trianglehOfDegreewiseSplit_distinguished S σ)

/-- Lemma 22.27.1 (4): equivalently to the shifted vanishing of `z[-1] ⟶ x ⟶ y`, the composition
`z ⟶ x[1] ⟶ y[1]` is zero in the homotopy category for the triangle attached to a degreewise
split short complex. -/
@[stacks 09P6, simp]
theorem trianglehOfDegreewiseSplit_comp_zero₃₁
    (S : ShortComplex (CochainComplex V ℤ))
    (σ : ∀ n : ℤ, (S.map (eval V (up ℤ) n)).Splitting) :
    (trianglehOfDegreewiseSplit S σ).mor₃ ≫ (trianglehOfDegreewiseSplit S σ).mor₁⟦(1 : ℤ)⟧' = 0 :=
  comp_distTriang_mor_zero₃₁ _ (trianglehOfDegreewiseSplit_distinguished S σ)

end

end CochainComplex
