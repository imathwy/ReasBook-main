import Mathlib

/-!
# Dimension of an induced representation

For a finite group `G`, a subgroup `H`, and a finite-dimensional `k`-representation `W` of `H`, the
induced representation `IndV H.subtype W.ρ` has dimension `[G : H] · dim W`.

The proof identifies `Ind` with `Coind` (Mathlib's `Rep.indToCoind`/`coindToInd`, which are mutually
inverse `k`-linear maps), and identifies `Coind` (equivariant functions `G → W`) with functions on
the right cosets `Quotient (rightRel H)` via evaluation at coset representatives.

This is the dimension input needed to upgrade the surjection `Ψ : Ind(reduction L) → reduction(Ind L)`
(in `ReductionInductionIso.lean`) to an isomorphism (part 2 of `hind`, step (D) of Theorem 17-17.2-1).
-/

noncomputable section

universe u

open Finsupp TensorProduct CategoryTheory

namespace Representation

variable {k : Type u} [Field k] {G : Type u} [Group G] [Finite G]

/-- For a right coset, `g` and the chosen representative `⟦g⟧.out` differ by an element of `H` on the
left: `g * ⟦g⟧.out⁻¹ ∈ H`. -/
theorem rightRel_out_mem {H : Subgroup G} (g : G) :
    g * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) g))⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq _))

/-- Coinduction from a subgroup, as equivariant functions `G → W`, is linearly equivalent to all
functions on the right cosets `Quotient (rightRel H)`, via evaluation at / extension from coset
representatives. -/
def coindPiEquiv {H : Subgroup G} (W : FDRep k H) :
    Representation.coindV H.subtype W.ρ ≃ₗ[k]
      (Quotient (QuotientGroup.rightRel H) → W.V) where
  toFun f := fun q => f.1 (Quotient.out q)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun φ := ⟨fun g => W.ρ ⟨g * (Quotient.out (Quotient.mk _ g))⁻¹, rightRel_out_mem g⟩
      (φ (Quotient.mk _ g)), by
    intro s g
    rw [Subgroup.subtype_apply]
    have hq : Quotient.mk (QuotientGroup.rightRel H) ((↑s : G) * g) = Quotient.mk _ g :=
      Quotient.sound (QuotientGroup.rightRel_apply.mpr (by
        rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]; exact H.inv_mem s.2))
    have hout : Quotient.out (Quotient.mk (QuotientGroup.rightRel H) ((↑s : G) * g))
        = Quotient.out (Quotient.mk (QuotientGroup.rightRel H) g) := congrArg _ hq
    show W.ρ ⟨(↑s : G) * g * _, _⟩ (φ (Quotient.mk _ ((↑s : G) * g)))
      = W.ρ s (W.ρ ⟨g * _, _⟩ (φ (Quotient.mk _ g)))
    rw [show φ (Quotient.mk (QuotientGroup.rightRel H) ((↑s : G) * g))
          = φ (Quotient.mk (QuotientGroup.rightRel H) g) from congrArg φ hq,
      show W.ρ s (W.ρ ⟨g * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) g))⁻¹,
            rightRel_out_mem g⟩ (φ (Quotient.mk _ g)))
          = (W.ρ s * W.ρ ⟨g * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) g))⁻¹,
              rightRel_out_mem g⟩) (φ (Quotient.mk _ g)) from rfl,
      ← map_mul]
    refine congrArg (fun a : H => W.ρ a (φ (Quotient.mk (QuotientGroup.rightRel H) g))) ?_
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mk, Subgroup.coe_mk, hout, mul_assoc]⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    have hf : ∀ (a : H) (b : G), f.1 (H.subtype a * b) = W.ρ a (f.1 b) := f.2
    show W.ρ ⟨g * _, _⟩ (f.1 (Quotient.out (Quotient.mk _ g))) = f.1 g
    rw [← hf ⟨g * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) g))⁻¹, rightRel_out_mem g⟩
      (Quotient.out (Quotient.mk (QuotientGroup.rightRel H) g))]
    refine congrArg f.1 ?_
    rw [Subgroup.subtype_apply, Subgroup.coe_mk, inv_mul_cancel_right]
  right_inv φ := by
    funext q
    show W.ρ ⟨Quotient.out q * _, _⟩ (φ (Quotient.mk _ (Quotient.out q))) = φ q
    have hqe : Quotient.mk (QuotientGroup.rightRel H) (Quotient.out q) = q := Quotient.out_eq q
    have hone : (⟨Quotient.out q * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H)
        (Quotient.out q)))⁻¹, rightRel_out_mem (Quotient.out q)⟩ : H) = 1 := by
      refine Subtype.ext ?_
      show Quotient.out q * (Quotient.out (Quotient.mk (QuotientGroup.rightRel H)
        (Quotient.out q)))⁻¹ = 1
      rw [hqe, mul_inv_cancel]
    rw [hone, map_one]
    show φ (Quotient.mk (QuotientGroup.rightRel H) (Quotient.out q)) = φ q
    rw [hqe]

/-- **Dimension of an induced representation**: `dim (Ind_H^G W) = [G : H] · dim W`, where the index
is realized as `Nat.card (Quotient (rightRel H))`. -/
theorem finrank_indV {H : Subgroup G} (W : FDRep k H) :
    Module.finrank k (Representation.IndV H.subtype W.ρ)
      = Nat.card (Quotient (QuotientGroup.rightRel H)) * Module.finrank k W.V := by
  classical
  haveI : Fintype (Quotient (QuotientGroup.rightRel H)) := Fintype.ofFinite _
  have e1 : Representation.IndV H.subtype W.ρ ≃ₗ[k] ↥(Representation.coindV H.subtype W.ρ) :=
    LinearEquiv.ofLinear (Rep.indToCoind (Rep.of W.ρ)) (Rep.coindToInd (Rep.of W.ρ))
      (Rep.coindToInd_indToCoind _) (Rep.indToCoind_coindToInd _)
  rw [e1.finrank_eq, (coindPiEquiv W).finrank_eq, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul]

end Representation
