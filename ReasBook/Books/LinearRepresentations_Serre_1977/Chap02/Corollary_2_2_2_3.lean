import LinearRepresentations_Serre_1977.Chap02.Corollary_2_2_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
universe u v w u₁ u₂

namespace Representation

noncomputable section

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {V1 : Type v} [AddCommGroup V1] [Module k V1]
variable {V2 : Type w} [AddCommGroup V2] [Module k V2]
variable {ι1 : Type u₁} [Fintype ι1]
variable {ι2 : Type u₂} [Fintype ι2]

local instance : Fintype G := Fintype.ofFinite G

variable [Invertible (Nat.card G : k)]

/- Source-facing bridge: the core/canonical owner is the averaged intertwiner
`(ρ1.linHom ρ2).averageMap`; the new owner-level bridge
`averageMap_linHom_basis_entry_eq` computes its matrix entry on the canonical basis vector
`b1.linearMap b2 (j2, j1)`. This corollary is the vanishing specialization of that bridge for
nonisomorphic irreducibles. -/
-- Proof sketch: apply `averageMap_linHom_eq_zero_of_not_isomorphic` to the canonical basis vector
-- `b1.linearMap b2 (j2, j1)`, then read off its `(i2, i1)` matrix entry through
-- `averageMap_linHom_basis_entry_eq`.
open scoped Classical in
/-- Corollary 2-2.2-3: for nonisomorphic irreducible representations of a finite group over a
field in which `|G|` is invertible, the normalized sum of the corresponding matrix-coefficient
products is zero for arbitrary basis indices. -/
theorem matrix_coefficient_orthogonality_of_not_isomorphic
    (ρ1 : Representation k G V1) (ρ2 : Representation k G V2)
    [ρ1.IsIrreducible] [ρ2.IsIrreducible]
    (hρ : ¬ Nonempty (ρ1.Equiv ρ2))
    (b1 : Module.Basis ι1 k V1) (b2 : Module.Basis ι2 k V2)
    (i1 j1 : ι1) (i2 j2 : ι2) :
    (Nat.card G : k)⁻¹ *
      ∑ t : G, (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1 = 0 := by
  letI : Invertible (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  let e := b1.linearMap b2 (j2, j1)
  have hbridge :
      (Nat.card G : k)⁻¹ *
          ∑ t : G, (ρ2 t⁻¹).toMatrix b2 b2 i2 j2 * (ρ1 t).toMatrix b1 b1 j1 i1 =
        (((ρ1.linHom ρ2).averageMap e).toMatrix b1 b2 i2 i1) := by
    simpa [e, Nat.card_eq_fintype_card] using
      (averageMap_linHom_basis_entry_eq ρ1 ρ2 b1 b2 i1 j1 i2 j2).symm
  have hzero :
      (((ρ1.linHom ρ2).averageMap e).toMatrix b1 b2 i2 i1) = 0 := by
    simpa [e] using congrArg (fun f ↦ f.toMatrix b1 b2 i2 i1) <|
      averageMap_linHom_eq_zero_of_not_isomorphic ρ1 ρ2 e hρ
  exact hbridge.trans hzero

end

end

end Representation
