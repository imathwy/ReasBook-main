import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_19_1
import stacks_proof.stacks_project.Chap15.Lemma_15_72_3
import stacks_proof.stacks_project.Chap15.Definition_15_59_1
import stacks_proof.stacks_project.Chap15.Definition_15_75_1
import stacks_proof.stacks_project.Chap15.«15_74_0_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalClosed

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "ProjMinus" => CochainComplex.ProjectiveMinus (ModuleCat R)

open scoped DerivedInternalHom
open scoped ModuleComplexInternalHom

/-- The canonical comparison between the Hom complex `\mathrm{Hom}^\bullet(P^•, K^•)` and the
chosen derived internal Hom `R\mathrm{Hom}_R(P^•, K^•)` when `P^•` is bounded above and
termwise projective. This is the direct theorem-level representation layer; the perfectness
hypothesis is only needed later for the K-flatness upgrade. -/
theorem module_complex_internal_hom_represents_derivedInternalHom_of_boundedAbove_projective
    (H : RHomPkg)
    (P : ProjMinus) (K : Cpx) :
    IsIsomorphic
      (DerivedCategory.Q.obj ⟪P, K⟫)
      (RHom[H](DerivedCategory.Q.obj (P : Cpx), DerivedCategory.Q.obj K)) := by
  admit

/-- Lemma 15.99.4: if `P^•` is a bounded-above cochain complex of projective `R`-modules, `K^•`
is K-flat, and `P^•` represents a perfect object of `D(R)`, then the module-valued internal-Hom
complex `\mathrm{Hom}^\bullet(P^•, K^•)` is K-flat, and the canonical comparison with
`R\mathrm{Hom}_R(P^•, K^•)` is an isomorphism in the derived category. -/
@[stacks 0BYQ]
theorem module_complex_internal_hom_isKFlat_and_represents_derivedInternalHom_of_isPerfect
    (H : RHomPkg)
    (P : ProjMinus) (K : Cpx)
    (hK : K.IsKFlat)
    (hperfect : DerivedCategory.IsPerfect (DerivedCategory.Q.obj (P : Cpx))) :
    (⟪P, K⟫).IsKFlat ∧
      IsIsomorphic
        (DerivedCategory.Q.obj ⟪P, K⟫)
        (RHom[H](DerivedCategory.Q.obj (P : Cpx), DerivedCategory.Q.obj K)) := by
  admit

/-- The Hom complex against a K-flat complex is K-flat when the source complex is bounded above,
termwise projective, and perfect in the derived category. -/
theorem module_complex_internal_hom_isKFlat_of_isPerfect
    (P : ProjMinus) (K : Cpx)
    (hK : K.IsKFlat)
    (hperfect : DerivedCategory.IsPerfect (DerivedCategory.Q.obj (P : Cpx))) :
    (⟪P, K⟫).IsKFlat := by
  admit

end

end CategoryTheory
