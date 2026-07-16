import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanSmithRange
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.TypeTags.Finite

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section PPrimaryLatticeBridge

/-- Pure p-primary lattice bridge. If `N ≤ D` inside an additive abelian group `M`, the quotient
`M / N` is finite and `p`-primary, and the intermediate quotient `D / N` has cardinality prime to
`p`, then the intermediate subgroup was trivial: `N = D`.

The proof is the formal index argument `#(M / N) = #(M / D) * #(D / N)`: the second factor divides
a power of `p`, and is also coprime to `p`. -/
theorem addSubgroup_eq_of_quotient_isPGroup_of_quotient_card_coprime
    {M : Type u} [AddCommGroup M] {p : ℕ} [Fact p.Prime]
    (N D : AddSubgroup M) (hND : N ≤ D)
    [Finite (M ⧸ N)]
    (hP : IsPGroup p (Multiplicative (M ⧸ N)))
    (hcop : Nat.Coprime p (Nat.card (D ⧸ N.addSubgroupOf D))) :
    N = D := by
  classical
  obtain ⟨n, hMNcard_mul⟩ :=
    IsPGroup.exists_card_eq (p := p) (G := Multiplicative (M ⧸ N)) hP
  have hMNcard : Nat.card (M ⧸ N) = p ^ n := by
    simpa using hMNcard_mul
  have hMNcard_fintype : Fintype.card (M ⧸ N) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hMNcard
  have hcard_prod :
      Nat.card (M ⧸ N) =
        Nat.card (M ⧸ D) * Nat.card (D ⧸ N.addSubgroupOf D) := by
    simpa [Nat.card_prod] using
      Nat.card_congr (AddSubgroup.quotientEquivProdOfLE hND)
  have hdiv : Nat.card (D ⧸ N.addSubgroupOf D) ∣ p ^ n := by
    have : Nat.card (D ⧸ N.addSubgroupOf D) ∣ Nat.card (M ⧸ N) := by
      rw [hcard_prod]
      exact dvd_mul_left _ _
    simpa [Nat.card_eq_fintype_card, hMNcard_fintype] using this
  have hcard_one : Nat.card (D ⧸ N.addSubgroupOf D) = 1 :=
    Nat.Coprime.eq_one_of_dvd (hcop.symm.pow_right n) hdiv
  have hindex_one : (N.addSubgroupOf D).index = 1 := by
    rw [AddSubgroup.index_eq_card]
    exact hcard_one
  have htop : N.addSubgroupOf D = ⊤ := (AddSubgroup.index_eq_one).mp hindex_one
  have hDN : D ≤ N := (AddSubgroup.addSubgroupOf_eq_top).mp htop
  exact le_antisymm hND hDN

/-- Version of `addSubgroup_eq_of_quotient_isPGroup_of_quotient_card_coprime` for
`N ≤ D ≤ M` as additive subgroups of a larger ambient abelian group `A`. The p-primary quotient
is phrased inside `M`, while the prime-to-`p` quotient is the visible quotient inside `D`. -/
theorem addSubgroup_eq_of_subgroupOf_quotient_isPGroup_of_subgroupOf_quotient_card_coprime
    {A : Type u} [AddCommGroup A] {p : ℕ} [Fact p.Prime]
    (N D M : AddSubgroup A) (hND : N ≤ D) (hDM : D ≤ M)
    [Finite (M ⧸ N.addSubgroupOf M)]
    (hP : IsPGroup p (Multiplicative (M ⧸ N.addSubgroupOf M)))
    (hcop : Nat.Coprime p (Nat.card (D ⧸ N.addSubgroupOf D))) :
    N = D := by
  classical
  have hNM : N ≤ M := hND.trans hDM
  let Nₘ : AddSubgroup M := N.addSubgroupOf M
  let Dₘ : AddSubgroup M := D.addSubgroupOf M
  have hNDₘ : Nₘ ≤ Dₘ := by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf] at hx ⊢
    exact hND hx
  let e : Dₘ ≃+ D := AddSubgroup.addSubgroupOfEquivOfLe hDM
  have he : AddSubgroup.map (e : Dₘ →+ D) (Nₘ.addSubgroupOf Dₘ) = N.addSubgroupOf D := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      rw [AddSubgroup.mem_addSubgroupOf]
      rw [← hxy]
      change (y : Dₘ) ∈ Nₘ.addSubgroupOf Dₘ at hy
      rw [AddSubgroup.mem_addSubgroupOf] at hy
      simpa [e] using hy
    · intro hx
      refine ⟨e.symm x, ?_, by simp [e]⟩
      change (e.symm x : Dₘ) ∈ Nₘ.addSubgroupOf Dₘ
      rw [AddSubgroup.mem_addSubgroupOf]
      rw [AddSubgroup.mem_addSubgroupOf] at hx
      simpa [e] using hx
  have hcard_m :
      Nat.card (Dₘ ⧸ Nₘ.addSubgroupOf Dₘ) =
        Nat.card (D ⧸ N.addSubgroupOf D) := by
    exact Nat.card_congr
      (QuotientAddGroup.congr
        (Nₘ.addSubgroupOf Dₘ) (N.addSubgroupOf D) e he).toEquiv
  have hcop_m : Nat.Coprime p (Nat.card (Dₘ ⧸ Nₘ.addSubgroupOf Dₘ)) := by
    simpa [hcard_m] using hcop
  have hEq_m : Nₘ = Dₘ :=
    addSubgroup_eq_of_quotient_isPGroup_of_quotient_card_coprime
      (p := p) Nₘ Dₘ hNDₘ hP hcop_m
  have hEq_inf : N ⊓ M = D ⊓ M := by
    simpa [Nₘ, Dₘ] using (AddSubgroup.addSubgroupOf_inj.mp hEq_m)
  rwa [inf_eq_left.mpr hNM, inf_eq_left.mpr hDM] at hEq_inf

end PPrimaryLatticeBridge

section CartanPPrimaryBridge

variable {p : ℕ}
variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

/-- Cartan-range adapter for the p-primary bridge.

For a coordinate equivalence `e`, let
`N = (cartanHom k G).range.map e.toAddMonoidHom` and let `D` be the regular centralizer-`p`-part
integer diagonal lattice. If `N ≤ D`, the coordinate cokernel is a finite p-group, and `D / N`
has cardinality prime to `p`, then the coordinate Cartan range already equals the diagonal
lattice.

This theorem intentionally isolates the final pure algebra step. The missing `hcop` input should
come from the projective-character lattice branch: compare the cast integer diagonal lattice with
`regularValueDivisibilitySubmodule`, use the span equality after regular restriction and Brauer
coordinate readback, and show that the residual quotient controlling `D / N` has invariant
factors prime to `p`. -/
theorem cartanRange_map_eq_regularIntegerDiagonal_of_pgroup_quotient_and_coprime
    (e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ))
    (hND : (cartanHom k G).range.map e.toAddMonoidHom ≤
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    [Finite ((PRegularConjClass G p → ℤ) ⧸
      ((cartanHom k G).range.map e.toAddMonoidHom))]
    (hP : IsPGroup p (Multiplicative ((PRegularConjClass G p → ℤ) ⧸
      ((cartanHom k G).range.map e.toAddMonoidHom))))
    (hcop : Nat.Coprime p
      (Nat.card
        ((regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup ⧸
          ((cartanHom k G).range.map e.toAddMonoidHom).addSubgroupOf
            (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup))) :
    (cartanHom k G).range.map e.toAddMonoidHom =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  exact
    addSubgroup_eq_of_quotient_isPGroup_of_quotient_card_coprime
      (p := p)
      ((cartanHom k G).range.map e.toAddMonoidHom)
      ((regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
      hND hP hcop

end CartanPPrimaryBridge

end Representation
