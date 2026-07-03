import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.SingletonOffIdentityBoundary

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientSingletonOffIdentityNotBijective (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: under irreducibility of the induced representation, a
nonzero Mackey singleton supported away from the identity double coset cannot be represented by a
bijective induced endomorphism. -/
theorem off_identity_singleton_not_bijective_of_ind_isIrreducible
    (H : Subgroup G) (ρ : Representation k H V)
    (hInd : (Rep.ind H.subtype (of ρ)).ρ.IsIrreducible)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (hf : f ≠ 0)
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f) :
    ¬ Function.Bijective F.hom := by
  classical
  intro hbij
  let τ : Rep k G := Rep.ind H.subtype (of ρ)
  let e := induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ
  letI : τ.ρ.IsIrreducible := hInd
  letI : FiniteDimensional k (Representation.IndV H.subtype ρ) :=
    IsIrreducible.finiteDimensional_of_finite τ.ρ
  have hscalar_surj :
      Function.Surjective
        (algebraMap k (τ.ρ.IntertwiningMap τ.ρ)) :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := τ.ρ)).2
  rcases hscalar_surj ((Rep.homLinearEquiv τ τ) F) with ⟨a, ha⟩
  have hF_scalar : F = a • (𝟙 τ) := by
    apply (Rep.homLinearEquiv τ τ).injective
    simpa [Representation.IntertwiningMap.algebraMap_apply] using ha.symm
  have hidentity_zero :
      (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        ((e F) (DoubleCoset.mk H H (1 : G))) = 0 := by
    simpa [e] using
      singleton_off_identity_identity_self_hom_eq_zero H ρ hq f F hF
  have hind_id : Rep.indMap H.subtype (𝟙 (Rep.of ρ)) = (𝟙 τ) := by
    simpa [τ] using (Rep.indFunctor (k := k) H.subtype).map_id (Rep.of ρ)
  have hidentity_scalar :
      (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        ((e F) (DoubleCoset.mk H H (1 : G))) =
        a • (𝟙 (Rep.of ρ)) := by
    calc
      (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
          ((e F) (DoubleCoset.mk H H (1 : G))) =
          (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
            ((e (a • (𝟙 τ))) (DoubleCoset.mk H H (1 : G))) := by
            rw [hF_scalar]
      _ =
          a •
            (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
              ((e (𝟙 τ)) (DoubleCoset.mk H H (1 : G))) := by
            simp [e]
      _ = a • (𝟙 (Rep.of ρ)) := by
            simpa [e, hind_id] using
              congrArg (fun g : Rep.of ρ ⟶ Rep.of ρ => a • g)
                (induced_self_map_identity_coordinate (k := k) H ρ (𝟙 (Rep.of ρ)))
  have hscalar_zero : a • (𝟙 (Rep.of ρ)) = 0 := by
    simpa [hidentity_scalar] using hidentity_zero
  have hρ : ρ.IsIrreducible := isIrreducible_of_ind_isIrreducible H ρ hInd
  letI : ρ.IsIrreducible := hρ
  letI : Nontrivial V := irreducible_nontrivial (k := k) ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hav_eval : (a • (𝟙 (Rep.of ρ))).hom v = 0 := by
    simpa using congrArg (fun g : Rep.of ρ ⟶ Rep.of ρ => g.hom v) hscalar_zero
  have hav : a • v = 0 := by
    simpa [Rep.smul_hom] using hav_eval
  have ha0 : a = 0 := by
    rcases smul_eq_zero.mp hav with ha | hv0
    · exact ha
    · exact False.elim (hv hv0)
  have hF_zero : F = 0 := by
    simpa [hF_scalar, ha0]
  have hf_zero : f = 0 := by
    have hcoord : (e F) q = f := by
      simpa [e, singleton_mackey_coordinate_family_self] using congrFun hF q
    have hcoord_zero : (e F) q = 0 := by
      simp [e, hF_zero]
    simpa [hcoord] using hcoord_zero
  exact hf hf_zero

end MackeyIrreducibilityCriterion

end Representation
