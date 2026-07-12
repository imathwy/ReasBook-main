import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.«15_60_1_1»

noncomputable section

open CategoryTheory
open MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModR'" => DerivedCategory (ModuleCat R')

open scoped DerivedTensorWithAlgebra

private noncomputable abbrev rightTensorAdj
    [MonoidalCategory DModR'] [BraidedCategory DModR'] [MonoidalClosed DModR']
    (L : DModR') : MonoidalCategory.tensorRight L ⊣ CategoryTheory.ihom L :=
  (CategoryTheory.ihom.adjunction L).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight L)

recall Adjunction.rightAdjointUniq
recall CategoryTheory.ihom.adjunction
recall CategoryTheory.ihom

/-- Helper for Lemma 15.100.1: any chosen right adjoint to tensoring on the right by
`K ⊗[R]^L[R']` is canonically isomorphic to the internal-Hom functor of that tensor factor. -/
noncomputable def derived_internal_hom_base_change_right_adjoint_iso
    [MonoidalCategory DModR'] [BraidedCategory DModR'] [MonoidalClosed DModR']
    (K : DModR) (G : DModR' ⥤ DModR')
    (adj : MonoidalCategory.tensorRight (K ⊗[R]^L[R']) ⊣ G) :
    G ≅ CategoryTheory.ihom (K ⊗[R]^L[R']) :=
  -- The source-faithful route identifies both functors as right adjoints to tensor-right by
  -- `K ⊗[R]^L[R']`, so uniqueness of right adjoints gives the comparison isomorphism.
  adj.rightAdjointUniq (rightTensorAdj (K ⊗[R]^L[R']))

/-- Helper for Lemma 15.100.1: the displayed comparison morphism is the component at `M` of the
canonical right-adjoint uniqueness isomorphism. -/
noncomputable def derived_internal_hom_base_change_comparison
    [MonoidalCategory DModR'] [BraidedCategory DModR'] [MonoidalClosed DModR']
    (K : DModR) (G : DModR' ⥤ DModR')
    (adj : MonoidalCategory.tensorRight (K ⊗[R]^L[R']) ⊣ G) (M : DModR') :
    G.obj M ⟶ ((K ⊗[R]^L[R']) ⟶[DModR'] M) :=
  -- Passing to the component at `M` exposes the source-facing morphism between internal-Hom
  -- objects.
  ((derived_internal_hom_base_change_right_adjoint_iso (R := R) (R' := R') K G adj).app M).hom

/-- Helper for Lemma 15.100.1: the comparison morphism is an isomorphism because it is the `hom`
field of a component of a natural isomorphism. -/
theorem derived_internal_hom_base_change_comparison_isIso
    [MonoidalCategory DModR'] [BraidedCategory DModR'] [MonoidalClosed DModR']
    (K : DModR) (G : DModR' ⥤ DModR')
    (adj : MonoidalCategory.tensorRight (K ⊗[R]^L[R']) ⊣ G) (M : DModR') :
    IsIso (derived_internal_hom_base_change_comparison (R := R) (R' := R') K G adj M) := by
  let e := (derived_internal_hom_base_change_right_adjoint_iso (R := R) (R' := R') K G adj).app M
  -- The comparison map is definitionally the `hom` of the iso component `e`.
  simpa [derived_internal_hom_base_change_comparison, e] using
    (inferInstance : IsIso e.hom)

/-- Lemma 15.100.1: for any chosen right adjoint to tensoring on the right by `K ⊗[R]^L[R']`,
evaluating at `M` yields the canonical target-ring internal-Hom isomorphism
`R\mathrm{Hom}_R(K, M) ≅ R\mathrm{Hom}_{R'}(K \otimes_R^{\mathbf L} R', M)`. -/
noncomputable def derivedInternalHom_baseChange_iso
    [MonoidalCategory DModR'] [BraidedCategory DModR'] [MonoidalClosed DModR']
    (K : DModR) (G : DModR' ⥤ DModR')
    (adj : MonoidalCategory.tensorRight (K ⊗[R]^L[R']) ⊣ G) (M : DModR') :
    G.obj M ≅ ((K ⊗[R]^L[R']) ⟶[DModR'] M) :=
  -- The main statement is exactly the component at `M` of the functor-level right-adjoint
  -- uniqueness isomorphism.
  (derived_internal_hom_base_change_right_adjoint_iso (R := R) (R' := R') K G adj).app M

end

end CategoryTheory
