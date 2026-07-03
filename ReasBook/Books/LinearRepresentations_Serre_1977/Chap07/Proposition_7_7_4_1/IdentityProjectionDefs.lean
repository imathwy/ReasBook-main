import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.SelfMapCoordinates

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientIdentityProjectionDefs (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: the identity double-coset index as stable concrete data. -/
abbrev identity_mackey_double_coset (H : Subgroup G) :
    DoubleCoset.Quotient (H : Set G) H :=
  DoubleCoset.mk H H (1 : G)

/-- Helper for Proposition 7-7.4-1: the lifted identity double-coset index. -/
abbrev identity_mackey_lifted_double_coset (H : Subgroup G) :
    ULift (DoubleCoset.Quotient (H : Set G) H) :=
  ⟨identity_mackey_double_coset H⟩

/-- Helper for Proposition 7-7.4-1: the concrete Mackey subgroup at the identity double coset. -/
abbrev identity_mackey_subgroup (H : Subgroup G) : Subgroup H :=
  mackeySubgroup H H (doubleCosetRepresentative H (identity_mackey_double_coset H))

/-- Helper for Proposition 7-7.4-1: the concrete representation on the identity Mackey subgroup. -/
abbrev identity_mackey_representation
    (H : Subgroup G) (ρ : Representation k H V) :
    Representation k (identity_mackey_subgroup H) V :=
  (mackeyTwist H H (of ρ)
    (doubleCosetRepresentative H (identity_mackey_double_coset H))).ρ

/-- Helper for Proposition 7-7.4-1: the concrete identity Mackey block. -/
abbrev identity_mackey_block
    (H : Subgroup G) (ρ : Representation k H V) : Type _ :=
  Representation.IndV (identity_mackey_subgroup H).subtype
    (identity_mackey_representation (k := k) H ρ)

/-- Helper for Proposition 7-7.4-1: the unit-copy projection from the identity Mackey block. -/
abbrev identity_mackey_unit_projection
    (H : Subgroup G) (ρ : Representation k H V)
    [NeZero (Nat.card H : k)] :
    identity_mackey_block (k := k) H ρ →ₗ[k] V :=
  inducedIdentityCopyProjection (identity_mackey_subgroup H)
    (identity_mackey_representation (k := k) H ρ)

/-- Helper for Proposition 7-7.4-1: the Mackey direct-sum family with the `ULift`
index named once. -/
abbrev mackey_block_family
    (H : Subgroup G) (ρ : Representation k H V) :
    ULift (DoubleCoset.Quotient (H : Set G) H) → Type _ :=
  fun q ↦ Representation.IndV
    (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
    ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)

/-- Helper for Proposition 7-7.4-1: the Mackey direct-sum family before removing
`ULift` from coefficients. -/
abbrev mackey_ulift_block_family
    (H : Subgroup G) (ρ : Representation k H V) :
    ULift (DoubleCoset.Quotient (H : Set G) H) → Type _ :=
  fun q ↦ Representation.IndV
    (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
    ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ))
      (doubleCosetRepresentative H q.down)).ρ)

end MackeyIrreducibilityCriterion

end Representation
