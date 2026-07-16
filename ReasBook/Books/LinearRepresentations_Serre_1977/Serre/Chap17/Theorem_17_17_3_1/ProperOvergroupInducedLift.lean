import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Serre.Chap17.Theorem_17_17_3_1.InducedSubrepresentationLift

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

open CategoryTheory Rep
open scoped Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance properOvergroupInducedLiftResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance properOvergroupInducedLiftResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: once the Clifford split lands in the proper-overgroup branch,
the proof continues by recursing on that smaller subgroup and then transporting the lifted module
back across induction. -/
lemma exists_residueFieldLift_of_proper_overgroup_induced_viaExportedLift
    (hp : Nat.Prime p) (hC : C.Normal) (hCP : C.IsComplement' P) (hCyclic : IsCyclic C)
    (hCoprime : Nat.Coprime p (Nat.card C)) (hP : IsPGroup p P)
    (hrecSame :
      ∀ {H : Subgroup G} {W0 : Type w} [AddCommGroup W0] [Module k W0]
        [FiniteDimensional k W0]
        {C0 P0 : Subgroup H}
        (hH : H < ⊤)
        (hC0 : C0.Normal) (hC0P0 : C0.IsComplement' P0) (hC0cyc : IsCyclic C0)
        (hC0cop : Nat.Coprime p (Nat.card C0)) (hP0 : IsPGroup p P0)
        (σ : Representation k H W0) [σ.IsIrreducible],
          ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
            (_ : Module.Free A W') (_ : Module.Finite A W')
            (ρA_H : Representation A H W')
            (red_H : W' →ₗ[A] W0),
              IsResidueFieldLift σ ρA_H red_H)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hproper :
      ∃ H : Subgroup G,
        C ≤ H ∧ H < ⊤ ∧
          ∃ W : Subrepresentation (ρ.comp H.subtype),
            W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases hproper with ⟨H, hCH, hHlt, W, hWirred, hInd⟩
  let C0 : Subgroup H := C.subgroupOf H
  let P0 : Subgroup H := (H ⊓ P).subgroupOf H
  have hHdecomp :
      C0.Normal ∧ C0.IsComplement' P0 ∧ IsCyclic C0 ∧ Nat.Coprime p (Nat.card C0) ∧ IsPGroup p P0 :=
    subgroup_cyclicNormalByPGroupDecomposition_of_le
      (p := p) (C := C) (P := P) hCH hC hCP hCyclic hCoprime hP
  rcases hHdecomp with ⟨hC0, hC0P0, hC0cyc, hC0cop, hP0⟩
  letI : W.toRepresentation.IsIrreducible := hWirred
  have hLiftH :
      ∃ (W0 : Type u) (_ : AddCommGroup W0) (_ : Module A W0)
        (_ : Module.Free A W0) (_ : Module.Finite A W0)
        (ρA_H : Representation A H W0)
        (red_H : W0 →ₗ[A] W.toSubmodule),
          IsResidueFieldLift W.toRepresentation ρA_H red_H := by
    exact hrecSame hHlt hC0 hC0P0 hC0cyc hC0cop hP0 W.toRepresentation
  rcases hLiftH with ⟨W0, hW0add, hW0mod, hW0free, hW0finite, ρA_H, red_H, hLiftH⟩
  letI : AddCommGroup W0 := hW0add
  letI : Module A W0 := hW0mod
  letI : Module.Free A W0 := hW0free
  letI : Module.Finite A W0 := hW0finite
  exact
    exists_residueFieldLift_of_isInducedFromSubrepresentation
      (A := A) (G := G) (V := V) ρ W ρA_H red_H hLiftH hInd

end

end Representation
