import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import StacksProject_2024.stacks_project.Chap22.Lemma_22_13_2

open CategoryTheory

universe u w

section

variable {DGModA : Type u} [Category DGModA]

local notation "CompZ" => CochainComplex (ModuleCat ℤ) ℤ

variable (tensorWithM : DGModA ⥤ CompZ) (homFromM : CompZ ⥤ DGModA)
variable (adj : tensorWithM ⊣ homFromM)
variable (QModZ : CompZ)
variable (DifferentialGradedBilinear : DGModA → Type w)
variable (tensorHomToQModZEquivBilinear :
  ∀ N : DGModA, (tensorWithM.obj N ⟶ QModZ) ≃ DifferentialGradedBilinear N)
variable (N : DGModA)

/-- Lemma 22.19.2: if `homFromM.obj QModZ` models the dual differential graded module `Mᵛ` and
`tensorHomToQModZEquivBilinear` models the Section 22.12 identification
`Hom_{Comp(ℤ)}(N ⊗_A M, Q/ℤ) = DifferentialGradedBilinear_A(N × M, Q/ℤ)`, then morphisms
`N ⟶ Mᵛ` in the differential graded module category identify canonically with differential graded
bilinear maps `N × M ⟶ Q/ℤ`. The adjunction step is already the Chapter 22 owner
`dgTensorHomEquiv`, so the present item is its source-facing composite with the tensor-to-bilinear
equivalence. -/
@[stacks 09K3]
noncomputable abbrev dgHomToDualQModZEquivDifferentialGradedBilinear :
    (N ⟶ homFromM.obj QModZ) ≃ DifferentialGradedBilinear N :=
  (dgTensorHomEquiv tensorWithM homFromM adj N QModZ).trans
    (tensorHomToQModZEquivBilinear N)

/-- Applying `dgHomToDualQModZEquivDifferentialGradedBilinear` is the composition of the
Chapter 22 tensor-Hom adjunction bridge with the tensor-to-bilinear equivalence. -/
theorem dgHomToDualQModZEquivDifferentialGradedBilinear_apply
    (f : N ⟶ homFromM.obj QModZ) :
    dgHomToDualQModZEquivDifferentialGradedBilinear
        tensorWithM homFromM adj QModZ DifferentialGradedBilinear
        tensorHomToQModZEquivBilinear N f =
      tensorHomToQModZEquivBilinear N
        (dgTensorHomEquiv tensorWithM homFromM adj N QModZ f) :=
  rfl

/-- The inverse of `dgHomToDualQModZEquivDifferentialGradedBilinear` first uses the inverse
tensor-to-bilinear equivalence and then the inverse Chapter 22 tensor-Hom adjunction bridge. -/
theorem dgHomToDualQModZEquivDifferentialGradedBilinear_symm_apply
    (f : DifferentialGradedBilinear N) :
    (dgHomToDualQModZEquivDifferentialGradedBilinear
        tensorWithM homFromM adj QModZ DifferentialGradedBilinear
        tensorHomToQModZEquivBilinear N).symm f =
      (dgTensorHomEquiv tensorWithM homFromM adj N QModZ).symm
        ((tensorHomToQModZEquivBilinear N).symm f) :=
  rfl

end
