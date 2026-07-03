import Mathlib
import LinearRepresentations_Serre_1977.Chap08.Definition_8_8_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Source/core/bridge triage:
-- * source-facing: `IsPElement` and `IsPRegular` are the textbook order-theoretic predicates on
--   individual elements.
-- * core/canonical: `IsPGroup p G` and, in the commutative setting, `CommGroup.primaryComponent`.
-- * bridge/view: the comparison lemmas below connect the source-facing elementwise predicates to
--   those owner-level declarations.

section Monoid

variable {G : Type u} [Monoid G]

/-- Definition 10-10.1-1 (1): an element `x` is a `p`-element, or `p`-unipotent, if its order is
a power of `p`. -/
abbrev IsPElement (p : ℕ) (x : G) : Prop :=
  ∃ n : ℕ, orderOf x = p ^ n

/-- Definition 10-10.1-1 (2): an element `x` is a `p'`-element, or `p`-regular, if its order is
prime to `p`. -/
abbrev IsPRegular (p : ℕ) (x : G) : Prop :=
  Nat.Coprime p (orderOf x)

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- For prime `p`, the source-facing `p`-element predicate matches mathlib's canonical
prime-power torsion criterion. -/
theorem isPElement_iff_exists_pow_eq_one (x : G) :
    IsPElement p x ↔ ∃ n : ℕ, x ^ p ^ n = 1 := by
  simpa [IsPElement] using
    (exists_orderOf_eq_prime_pow_iff :
      (∃ n : ℕ, orderOf x = p ^ n) ↔ ∃ n : ℕ, x ^ p ^ n = 1)

/-- An element is `p`-regular exactly when `p` does not divide its order. -/
theorem isPRegular_iff_not_dvd_orderOf (x : G) :
    IsPRegular p x ↔ ¬ p ∣ orderOf x := by
  simpa [IsPRegular] using
    ((Fact.out : Nat.Prime p).coprime_iff_not_dvd :
      Nat.Coprime p (orderOf x) ↔ ¬ p ∣ orderOf x)

end Prime

/-- The identity element is `p`-regular. -/
theorem isPRegular_one (p : ℕ) : IsPRegular p (1 : G) := by
  simp [IsPRegular]

end Monoid

section GroupRegular

variable {G : Type u} [Group G]

/-- Conjugation preserves `p`-regularity. -/
theorem isPRegular_conj (p : ℕ) (s t : G) (hs : IsPRegular p s) :
    IsPRegular p (t * s * t⁻¹) := by
  rw [IsPRegular, ← (SemiconjBy.conj_mk t s).orderOf_eq t]
  exact hs

end GroupRegular

section CommGroup

variable {G : Type u} [CommGroup G] {p : ℕ} [Fact p.Prime]

open CommGroup

/-- In the commutative setting, `p`-elements are exactly the elements of the canonical owner
`primaryComponent G p`. -/
theorem isPElement_iff_mem_primaryComponent (x : G) :
    IsPElement p x ↔ x ∈ primaryComponent G p :=
  Iff.rfl

end CommGroup

section Group

variable {G : Type u} [Group G] {p : ℕ}

/- Definition 10-10.1-1 (3) reuses the canonical owner `IsPGroup p G` already fixed in
Definition 8-8.3-4. -/
recall IsPGroup

section Prime

variable [Fact p.Prime]

/-- Companion source-facing characterization: a group is a `p`-group exactly when each of its
elements is a `p`-element. -/
theorem isPGroup_iff_forall_isPElement :
    IsPGroup p G ↔ ∀ x : G, IsPElement p x := by
  simpa [IsPElement] using
    (IsPGroup.iff_orderOf : IsPGroup p G ↔ ∀ g : G, ∃ k, orderOf g = p ^ k)

end Prime

end Group
