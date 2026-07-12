import Mathlib

noncomputable section
universe u

namespace Serre.SplitBaseChange

open Module

/-- A finite-dimensional semisimple `F`-algebra all of whose simple modules have
1-dimensional endomorphism algebra ("split") is isomorphic to a product of matrix algebras
over `F`. -/
theorem split_of_finrank_end_eq_one
    {F : Type u} [Field F] (B : Type u) [Ring B] [Algebra F B] [Module.Finite F B]
    [IsSemisimpleRing B]
    (h : ∀ (M : Type u) [AddCommGroup M] [Module B M] [Module F M] [IsScalarTower F B M]
          [Module.Finite F M], IsSimpleModule B M → Module.finrank F (Module.End B M) = 1) :
    ∃ (ι : Type u) (_ : Fintype ι) (d : ι → ℕ),
      Nonempty (B ≃ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F) := by
  classical
  obtain ⟨n, S, d, hS, hd, ⟨e⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite F B
  -- For each `i`, the opposite endomorphism algebra of the simple module `S i` is `F`.
  have entry : ∀ i, (Module.End B (S i))ᵐᵒᵖ ≃ₐ[F] F := by
    intro i
    haveI : IsSimpleModule B (S i) := hS i
    -- `S i` as an `F`-module: restrict scalars along `F → B`.
    haveI hfin : Module.Finite F (S i) :=
      Module.Finite.of_injective ((S i).subtype.restrictScalars F)
        (Subtype.coe_injective)
    have hf : Module.finrank F (Module.End B (S i)) = 1 := h (S i) (hS i)
    have hbij : Function.Bijective (algebraMap F (Module.End B (S i))) :=
      Module.Free.bijective_algebraMap_of_finrank_eq_one hf
    have g : Module.End B (S i) ≃ₐ[F] F :=
      (AlgEquiv.ofBijective (Algebra.ofId F (Module.End B (S i))) hbij).symm
    exact (AlgEquiv.op g).trans (AlgEquiv.toOpposite F F).symm
  -- Reindex over `ULift (Fin n)` to land in `Type u`.
  refine ⟨ULift.{u} (Fin n), inferInstance, fun j => d j.down, ⟨?_⟩⟩
  refine e.trans (AlgEquiv.piCongrRight (fun i => (entry i).mapMatrix)) |>.trans ?_
  exact AlgEquiv.piCongrLeft' F (fun i => Matrix (Fin (d i)) (Fin (d i)) F) Equiv.ulift.symm

end Serre.SplitBaseChange
