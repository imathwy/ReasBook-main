import Mathlib
import stacks_project.Chap13.Definition_13_33_1
import stacks_project.Chap13.Definition_13_34_1
import stacks_project.Chap15.Lemma_15_75_15

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open MonoidalClosed
open Opposite
open scoped DerivedInternalHom
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod

/- Domain-style sampling for Lemma 15.75.17:
- primary domain: derived duality for perfect objects in `D(A)` together with the Chapter 13
  homotopy-colimit / derived-limit owners for sequential diagrams;
- sampled owner declarations:
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.MonoidalClosed.internalHom`,
  `CategoryTheory.tensor_derivedDual_iso_derivedInternalHom`,
  `CategoryTheory.derivedDualMap`,
  `CategoryTheory.IsHomotopyColimitOf`,
  `CategoryTheory.IsDerivedLimit`;
- best owner abstraction:
  `source-facing`: the tensor-dual inverse system `n ↦ E ⊗_A^{\mathbf L} K_n^\vee` from the
    Stacks statement, now exposed directly as a `SequentialInverseSystem DMod`, together with the
    derived-limit conclusion for `RHom_A(K, E)`;
  `core/canonical`: the sequential inverse-system owner `SequentialInverseSystem DMod`, the
    source-variable internal-Hom owner `MonoidalClosed.internalHom.flip.obj E`, the notation
    `RHom[H](K, E)`, and the Chapter 13 predicates `IsHomotopyColimitOf` and `IsDerivedLimit`;
  `bridge/view`: the inverse-system isomorphism
    `derivedDualTensorInverseSystemIsoInternalHomTower`, whose components are the perfect-stage
    comparison isomorphisms from Lemma `15.75.15`.

Primitive data are only the sequential diagram `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯`, the chosen monoidal-closed
owner `H`, and the fixed tensor target `E`. The source-facing tensor-dual inverse system is the
right owner for the textbook statement, while the canonical owner-level inverse system is the
source-variable internal-Hom tower `(Functor.ofSequence f).op ⋙
MonoidalClosed.internalHom.flip.obj E`. Lemma `15.75.15` supplies the stagewise bridge between
these two owners.
-/

/-- The source-facing inverse system
`\cdots \to E \otimes_A^{\mathbf L} K_{n + 1}^\vee \to E \otimes_A^{\mathbf L} K_n^\vee`
attached to a sequential diagram `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(A)`. -/
abbrev derivedDualTensorInverseSystem
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) :
    SequentialInverseSystem DMod :=
  let X : ℕ → DMod := fun n ↦ E ⊗[A]^L (K n)ᵛ⟮H⟯
  Functor.ofOpSequence <| fun n ↦
    show X (n + 1) ⟶ X n from
      (derivedTensorProductMap H (derivedDualMap H (f n))).app E

/-- For a sequential diagram of perfect objects, the source-facing tensor-dual inverse system is
canonically isomorphic to the owner-level internal-Hom tower
`(Functor.ofSequence f).op ⋙ MonoidalClosed.internalHom.flip.obj E`. -/
noncomputable def derivedDualTensorInverseSystemIsoInternalHomTower
    (H : RHomPkg) (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1))
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n)) :
    letI := H
    derivedDualTensorInverseSystem H E K f ≅
      (Functor.ofSequence f).op ⋙ (MonoidalClosed.internalHom).flip.obj E := by
  letI : RHomPkg := H
  refine NatIso.ofComponents
    (fun n ↦
      letI : IsIso (derivedDualTensorComparison H (K n.unop)) :=
        tensor_derivedDual_iso_derivedInternalHom H (hperfect n.unop)
      (asIso (derivedDualTensorComparison H (K n.unop))).app E)
    (fun {X Y} g ↦ by
      sorry)

/-- Lemma 15.75.17: if `K` is a chosen homotopy colimit of a sequential system of perfect objects
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(A)`, then for every `E : D(A)` the derived internal Hom
`R\mathrm{Hom}_A(K,E)` is a derived limit of the source-facing inverse system
`n ↦ E \otimes_A^{\mathbf L} K_n^\vee`, where `K_n^\vee = R\mathrm{Hom}_A(K_n, A)`.
Lemma `15.75.15` supplies the stagewise bridge from this tensor-dual tower to the canonical
inverse system `n ↦ R\mathrm{Hom}_A(K_n, E)`. -/
-- Proof sketch: for each stage `n`, perfectness makes the canonical comparison
-- `E ⊗^L_A K_n^\vee ⟶ RHom_A(K_n, E)` an isomorphism by Lemma `15.75.15`. After replacing the
-- source-facing tower by the canonically isomorphic owner-level internal-Hom tower
-- `(Functor.ofSequence f).op ⋙ MonoidalClosed.internalHom.flip.obj E`, the source-variable
-- internal-Hom owner `MonoidalClosed.internalHom.flip.obj E` sends the homotopy-colimit triangle
-- for `K` to the Milnor triangle computing the derived limit of `RHom_A(K_n, E)`.
theorem derivedInternalHom_isDerivedLimit_of_homotopyColimit
    (H : RHomPkg) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) {Khocolim : DMod}
    [HasCoproduct (Functor.ofSequence f).obj]
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n))
    (hKhocolim : IsHomotopyColimitOf (Functor.ofSequence f) Khocolim) (E : DMod) :
    IsDerivedLimit
      (derivedDualTensorInverseSystem H E K f)
      (RHom[H](Khocolim, E)) := sorry

end

end CategoryTheory
