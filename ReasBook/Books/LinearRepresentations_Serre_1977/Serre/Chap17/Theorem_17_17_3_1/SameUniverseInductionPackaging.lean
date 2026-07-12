import Mathlib

open scoped MonoidAlgebra

universe u v w

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Finite G]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Theorem 17-17.3-1: conjugating a representation through a finite basis preserves
the identity endomorphism. -/
private theorem finBasis_model_map_one_local
    (ρ : Representation k G V) :
    ((Module.finBasis k V).equivFun).conj (ρ 1) = 1 := by
  -- Conjugation carries the identity action to the identity matrix.
  calc
    ((Module.finBasis k V).equivFun).conj (ρ 1) =
        ((Module.finBasis k V).equivFun).conj 1 := by rw [map_one]
    _ = 1 := LinearEquiv.conj_id _

/-- Helper for Theorem 17-17.3-1: conjugating a representation through a finite basis preserves
multiplication of the action operators. -/
private theorem finBasis_model_map_mul_local
    (ρ : Representation k G V) (g h : G) :
    ((Module.finBasis k V).equivFun).conj (ρ (g * h)) =
      (((Module.finBasis k V).equivFun).conj (ρ g)) *
        (((Module.finBasis k V).equivFun).conj (ρ h)) := by
  -- Conjugation is multiplicative, so the transported action is still a representation.
  rw [map_mul]
  ext x
  simp [LinearEquiv.conj_apply_apply]

/-- Helper for Theorem 17-17.3-1: every finite-dimensional residue representation can be moved to
the same-universe coordinate model `Fin (finrank V) → k` without changing the representation up to
equivalence, even when the group universe differs from the coefficient-field universe. -/
theorem exists_same_universe_finite_rep_model_local
    (ρ : Representation k G V) :
    ∃ ρW : Representation k G (Fin (Module.finrank k V) → k),
      Nonempty (ρW.Equiv ρ) := by
  let e := (Module.finBasis k V).equivFun
  let ρW : Representation k G (Fin (Module.finrank k V) → k) :=
    { toFun := fun g ↦ e.conj (ρ g)
      map_one' := by
        -- Conjugation carries the identity action to the coordinate identity operator.
        simpa [e] using finBasis_model_map_one_local (ρ := ρ)
      map_mul' := by
        intro g h
        -- The transported action remains multiplicative after conjugation.
        simpa [e] using finBasis_model_map_mul_local (ρ := ρ) g h }
  refine ⟨ρW, ?_⟩
  refine ⟨Representation.Equiv.mk e.symm ?_⟩
  intro g
  -- The chosen basis equivalence intertwines the original action with its coordinate transport.
  ext x
  simp [ρW, e, LinearEquiv.conj_apply_apply]

end

section

variable {A : Type u} [CommRing A]
variable {G : Type v} [Group G] [Finite G]
variable {H : Subgroup G}
variable {W0 : Type w} [AddCommGroup W0] [Module A W0]
variable [Module.Free A W0] [Module.Finite A W0]

/-- Helper for Theorem 17-17.3-1: every free finite `A[G]`-representation can be moved to a
same-universe finite coordinate model without changing the action up to equivalence. -/
private theorem exists_same_universe_finite_free_rep_model_local
    {G' : Type*} [Group G']
    {W1 : Type*} [AddCommGroup W1] [Module A W1]
    [Module.Free A W1] [Module.Finite A W1]
    (ρA : Representation A G' W1) :
    ∃ (W' : Type u) (_ : AddCommGroup W') (_ : Module A W')
      (_ : Module.Free A W') (_ : Module.Finite A W')
      (ρW : Representation A G' W'),
        Nonempty (ρW.Equiv ρA) := by
  let ι : Type _ := Module.Free.ChooseBasisIndex A W1
  letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype A W1
  let b : Module.Basis ι A W1 := Module.Free.chooseBasis A W1
  let n := Fintype.card ι
  let W' : Type u := Fin n → A
  letI : AddCommGroup W' := Pi.addCommGroup
  letI : Module A W' := Pi.Function.module (Fin n) A A
  letI : Module.Free A W' := Module.Free.of_basis (Pi.basisFun A (Fin n))
  letI : Module.Finite A W' := Module.Finite.of_basis (Pi.basisFun A (Fin n))
  let eIndex : ι ≃ Fin n := Fintype.equivFin ι
  let eFun : (ι → A) ≃ₗ[A] W' := (LinearEquiv.funCongrLeft A A eIndex).symm
  let e : W1 ≃ₗ[A] W' := (b.equivFun).trans eFun
  let ρW : Representation A G' W' :=
    { toFun := fun g ↦ e.conj (ρA g)
      map_one' := by
        -- Conjugation carries the identity action to the coordinate identity operator.
        calc
          e.conj (ρA 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id _
      map_mul' := by
        intro g h
        -- The transported action remains multiplicative after conjugation.
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  refine
    ⟨W', inferInstance, inferInstance, inferInstance, inferInstance, ρW, ?_⟩
  refine ⟨Representation.Equiv.mk e.symm ?_⟩
  intro g
  -- The chosen basis equivalence intertwines the original action with its coordinate transport.
  apply LinearMap.ext
  intro x
  change e.symm (e (ρA g (e.symm x))) = ρA g (e.symm x)
  simp

/-- Helper for Theorem 17-17.3-1: evaluating a coinduced function on inverse representatives
identifies the coinduced model over a commutative ring with functions on a finite left
transversal. -/
private noncomputable def coind_representative_equiv_local
    (ρA_H : Representation A H W0)
    (R : Finset G) (hR : Subgroup.IsComplement (R : Set G) (H : Set G)) :
    Representation.coindV H.subtype ρA_H ≃ₗ[A] (↥(R : Set G) → W0) where
  toFun f r := f.1 ((r : G)⁻¹)
  invFun ξ :=
    ⟨fun g ↦
        let x := hR.equiv g⁻¹
        ρA_H x.2⁻¹ (ξ x.1), by
        intro h g
        -- Move the subgroup factor in the complement decomposition to the coefficient action.
        simpa [mul_assoc, ← Module.End.mul_apply, ← map_mul] using
          congrArg
            (fun x : ↥(R : Set G) × H ↦ ρA_H x.2⁻¹ (ξ x.1))
            (hR.equiv_mul_right g⁻¹ h⁻¹)⟩
  map_add' _ _ := by
    ext r
    simp
  map_smul' _ _ := by
    ext r
    simp
  left_inv f := by
    ext g
    let x := hR.equiv g⁻¹
    have hg : ((x.2 : H) : G)⁻¹ * ((x.1 : (R : Set G)) : G)⁻¹ = g := by
      simpa [x, mul_inv_rev] using congrArg Inv.inv (hR.equiv_fst_mul_equiv_snd g⁻¹)
    -- Rewrite `g` through the complement decomposition of `g⁻¹`.
    change ρA_H x.2⁻¹ (f.1 (((x.1 : ↥(R : Set G)) : G)⁻¹)) = f.1 g
    simpa [hg] using
      ((f.2 x.2⁻¹ (((x.1 : (R : Set G)) : G)⁻¹)).symm)
  right_inv ξ := by
    ext r
    have hfst :
        (hR.equiv (r : G)).fst = r :=
      hR.equiv_fst_eq_self_of_mem_of_one_mem (show (1 : G) ∈ H by simp) r.property
    have hsnd :
        (hR.equiv (r : G)).snd = (1 : H) :=
      hR.equiv_snd_eq_one_of_mem_of_one_mem (show (1 : G) ∈ H by simp) r.property
    -- At a representative inverse, the complement decomposition is the trivial one `r * 1`.
    dsimp
    simp [hfst, hsnd]

/-- Helper for Theorem 17-17.3-1: after inducing a free finite `A[H]`-model, one can still move
the induced source to a same-universe coordinate carrier without changing the induced
representation up to equivalence. -/
theorem exists_same_universe_finite_free_induced_model_local
    {W1 : Type u} [AddCommGroup W1] [Module A W1]
    [Module.Free A W1] [Module.Finite A W1]
    (ρA_H : Representation A H W1) :
    ∃ (W_ind : Type u) (_ : AddCommGroup W_ind) (_ : Module A W_ind)
      (_ : Module.Free A W_ind) (_ : Module.Finite A W_ind)
      (ρA_ind : Representation A G W_ind),
        Nonempty (ρA_ind.Equiv (Representation.ind H.subtype ρA_H)) := by
  classical
  obtain ⟨S, hS, _⟩ := H.exists_isComplement_left (1 : G)
  let R : Finset G := (Set.toFinite S).toFinset
  have hR : Subgroup.IsComplement (R : Set G) (H : Set G) := by
    simpa [R] using hS
  let eIndCoind :
      (Representation.ind H.subtype ρA_H).Equiv
        (Representation.coind H.subtype ρA_H) :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of ρA_H))
  let eCoind :
      Representation.coindV H.subtype ρA_H ≃ₗ[A] (↥(R : Set G) → W1) :=
    coind_representative_equiv_local (A := A) (G := G) ρA_H R hR
  let ρR : Representation A G (↥(R : Set G) → W1) :=
    { toFun := fun g ↦ eCoind.conj ((Representation.coind H.subtype ρA_H) g)
      map_one' := by
        -- Transport the coinduced identity action to the representative-coordinate model.
        calc
          eCoind.conj ((Representation.coind H.subtype ρA_H) 1) = eCoind.conj 1 := by
            rw [map_one]
          _ = 1 := LinearEquiv.conj_id _
      map_mul' := by
        intro g h
        -- Conjugation keeps the coinduced action multiplicative on the coordinate model.
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let eR : ρR.Equiv (Representation.coind H.subtype ρA_H) :=
    Representation.Equiv.mk eCoind.symm fun g ↦ by
      -- The representative-coordinate equivalence intertwines the coinduced action pointwise.
      apply LinearMap.ext
      intro x
      change
        eCoind.symm (eCoind ((Representation.coind H.subtype ρA_H) g (eCoind.symm x))) =
          (Representation.coind H.subtype ρA_H) g (eCoind.symm x)
      simp [ρR]
  letI : Finite ↥(R : Set G) := Set.toFinite (R : Set G)
  letI : Fintype ↥(R : Set G) := Fintype.ofFinite _
  rcases
      exists_same_universe_finite_free_rep_model_local
        (A := A) (G' := G) (ρA := ρR) with
    ⟨W_ind, hWadd, hWmod, hWfree, hWfinite, ρA_ind, hEquiv⟩
  rcases hEquiv with ⟨ePack⟩
  refine ⟨W_ind, hWadd, hWmod, hWfree, hWfinite, ρA_ind, ?_⟩
  -- Assemble the packaged source equivalence with the coinduced representative model and the
  -- standard `ind ≃ coind` comparison.
  exact ⟨ePack.trans (eR.trans eIndCoind.symm)⟩

end

end Representation
