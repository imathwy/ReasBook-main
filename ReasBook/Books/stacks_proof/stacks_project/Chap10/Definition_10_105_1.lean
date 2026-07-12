import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_105_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Order Set

section

variable {R : Type u} [CommRing R]

/- Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace X`
- prime-spectrum/irreducible-closed bridge: `PrimeSpectrum.pointsEquivIrreducibleCloseds`
- ring-level owner: `IsCatenaryRing R`
- prime-spectrum owner equivalence: `isCatenaryRing_iff_catenarySpace_primeSpectrum`

Layer triage:
- `source-facing`: Definition 10.105.1 phrases catenarity through bounded prime chains and common
  lengths of maximal prime chains in intervals of `Spec R`
- `core/canonical`: the chapter owner is already `IsCatenaryRing R` from
  `Lemma_10_105_2`, together with its bridge to `CatenarySpace (PrimeSpectrum R)`
- `bridge/view`: `PrimeSpectrum.pointsEquivIrreducibleCloseds` transports the Chapter 5
  irreducible-closed catenary API to the prime-order formulation used in the source

Primitive data belongs to the owner abstraction `IsCatenaryRing R`; the interval-chain wording is
derived API and should stay as thin owner-derived companion theorems, not as a second public class
or a bundled replacement definition.
-/

/- Definition 10.105.1: the chapter owner for catenary commutative rings is
`IsCatenaryRing R`. -/
recall IsCatenaryRing

/-- Source-facing alias for Chap10 Definition 10 105 1: a commutative ring is catenary exactly
when its prime spectrum is catenary. This keeps `IsCatenaryRing` as the canonical owner name used
by the rest of the chapter. -/
theorem isCatenaryRing_def : IsCatenaryRing R ↔ CatenarySpace (PrimeSpectrum R) :=
  Iff.rfl

/- Companion recall: Lemma `10.105.2` identifies ring catenarity with catenarity of the prime
spectrum. -/
recall isCatenaryRing_iff_catenarySpace_primeSpectrum

/-
/-- Validator bridge for Chap10 Definition 10 105 1: records the two public interval-chain
declarations that together form the planned source-facing result for this item. -/
theorem IsCatenaryRing.primeChainsBounded / IsCatenaryRing.maximalPrimeChainsHaveSameLength
-/

namespace IsCatenaryRing

/-- Helper for Chap10 Definition 10 105 1: the irreducible closed subset of `Spec R`
corresponding to a prime. -/
private abbrev primeIrreducibleClosed (R : Type u) [CommRing R] (p : PrimeSpectrum R) :
    TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) :=
  show TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) from
    PrimeSpectrum.pointsEquivIrreducibleCloseds R p

/-- Helper for Chap10 Definition 10 105 1: a prime in `[p, q]` maps to the corresponding
irreducible closed subset in `[V(q), V(p)]`. -/
private lemma primeIntervalIrreducibleClosedMem (p q : PrimeSpectrum R) (x : Set.Icc p q) :
    primeIrreducibleClosed R x.1 ∈
      Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) := by
  -- The order is reversed after passing from primes to irreducible closed subsets.
  constructor
  · exact (PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone x.2.2
  · exact (PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone x.2.1

/-- Helper for Chap10 Definition 10 105 1: a member of `[V(q), V(p)]` maps back to a prime in
`[p, q]`. -/
private lemma irreducibleClosedIntervalPrimeMem (p q : PrimeSpectrum R)
    (x : Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p)) :
    (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm
      (show (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from x.1) ∈ Set.Icc p q := by
  -- Endpoint inequalities in the ordinary irreducible-closed order become prime inequalities
  -- after applying the inverse order isomorphism.
  constructor
  · have hx :
        (PrimeSpectrum.pointsEquivIrreducibleCloseds R p) ≤
          (show (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from x.1) := by
      exact x.2.2
    simpa using (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm.monotone hx
  · have hx :
        (show (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from x.1) ≤
          PrimeSpectrum.pointsEquivIrreducibleCloseds R q := by
      exact x.2.1
    simpa using (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm.monotone hx

/-- Helper for Chap10 Definition 10 105 1: the forward map from prime intervals to irreducible
closed intervals. -/
private noncomputable def primeIntervalToIrreducibleClosed (p q : PrimeSpectrum R) :
    Set.Icc p q → Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) :=
  fun x ↦ ⟨primeIrreducibleClosed R x.1, primeIntervalIrreducibleClosedMem (p := p) (q := q) x⟩

/-- Helper for Chap10 Definition 10 105 1: the inverse map from irreducible closed intervals to
prime intervals. -/
private noncomputable def irreducibleClosedIntervalToPrime (p q : PrimeSpectrum R) :
    Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) → Set.Icc p q :=
  fun x ↦ ⟨(PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm
    (show (TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R))ᵒᵈ from x.1),
    irreducibleClosedIntervalPrimeMem (p := p) (q := q) x⟩

/-- Helper for Chap10 Definition 10 105 1: the interval maps are left inverses. -/
private lemma irreducibleClosedIntervalToPrime_leftInverse (p q : PrimeSpectrum R) :
    Function.LeftInverse (irreducibleClosedIntervalToPrime p q)
      (primeIntervalToIrreducibleClosed p q) := by
  -- Subtype extensionality reduces the inverse calculation to the underlying order isomorphism.
  intro x
  ext
  simp [primeIntervalToIrreducibleClosed, irreducibleClosedIntervalToPrime, primeIrreducibleClosed]

/-- Helper for Chap10 Definition 10 105 1: the interval maps are right inverses. -/
private lemma irreducibleClosedIntervalToPrime_rightInverse (p q : PrimeSpectrum R) :
    Function.RightInverse (irreducibleClosedIntervalToPrime p q)
      (primeIntervalToIrreducibleClosed p q) := by
  -- The same subtype extensionality proves the reverse inverse identity.
  intro x
  ext
  simp [primeIntervalToIrreducibleClosed, irreducibleClosedIntervalToPrime, primeIrreducibleClosed]

/-- Helper for Chap10 Definition 10 105 1: the interval map reverses the displayed order. -/
private lemma primeIntervalToIrreducibleClosed_rel_iff (p q : PrimeSpectrum R)
    (x y : Set.Icc p q) :
    flip (fun a b : Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) ↦ a ≤ b)
        (primeIntervalToIrreducibleClosed p q x)
        (primeIntervalToIrreducibleClosed p q y) ↔ x ≤ y := by
  -- The codomain of `pointsEquivIrreducibleCloseds` is an order dual, so ordinary
  -- irreducible-closed comparability is the flipped prime comparability.
  constructor
  · intro h
    have hdual :
        (PrimeSpectrum.pointsEquivIrreducibleCloseds R) x.1 ≤
          (PrimeSpectrum.pointsEquivIrreducibleCloseds R) y.1 := h
    exact (PrimeSpectrum.pointsEquivIrreducibleCloseds R).le_iff_le.mp hdual
  · intro h
    have hdual :
        (PrimeSpectrum.pointsEquivIrreducibleCloseds R) x.1 ≤
          (PrimeSpectrum.pointsEquivIrreducibleCloseds R) y.1 :=
      (PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone h
    exact hdual

/-- Helper for Chap10 Definition 10 105 1: prime intervals are relation-isomorphic to
irreducible-closed intervals with the relation flipped. -/
private noncomputable def primeIntervalRelIsoIrreducibleClosed (p q : PrimeSpectrum R) :
    (fun x y : Set.Icc p q ↦ x ≤ y) ≃r
      flip (fun x y : Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p) ↦ x ≤ y) :=
  { toEquiv :=
      { toFun := primeIntervalToIrreducibleClosed p q
        invFun := irreducibleClosedIntervalToPrime p q
        left_inv := irreducibleClosedIntervalToPrime_leftInverse p q
        right_inv := irreducibleClosedIntervalToPrime_rightInverse p q }
    map_rel_iff' := fun {x y} ↦ primeIntervalToIrreducibleClosed_rel_iff p q x y }

/-- Helper for Chap10 Definition 10 105 1: every chain is contained in a flag, so its cardinality
is bounded by that flag. -/
private lemma chainEncard_le_flagEncard {α : Type*} [Preorder α] {s : Set α}
    (hs : IsChain (· ≤ ·) s) :
    ∃ F : Flag α, s ⊆ F ∧ s.encard ≤ (F : Set α).encard := by
  -- Zorn extends the chain to a flag, and cardinality is monotone under inclusion.
  classical
  obtain ⟨F, hsub⟩ := hs.exists_subset_flag
  exact ⟨F, hsub, Set.encard_le_encard hsub⟩

variable [IsCatenaryRing R]

/-- Helper for Chap10 Definition 10 105 1: a maximal prime chain in `[p, q]` has the catenary
length of the corresponding irreducible-closed interval `[V(q), V(p)]`. -/
private lemma maximalPrimeChain_encard_eq (p q : PrimeSpectrum R) (hpq : p ≤ q)
    {s : Set (Set.Icc p q)} (hs : IsMaxChain (· ≤ ·) s) :
    s.encard =
      ENat.toNat
        (codimBetween (primeIrreducibleClosed R q) (primeIrreducibleClosed R p)
          ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone hpq)) + 1 := by
  -- Transport the maximal prime chain to a maximal irreducible-closed chain, correcting the
  -- order reversal by symmetrizing maximality.
  let e := primeIntervalRelIsoIrreducibleClosed p q
  have hsImage :
      IsMaxChain (· ≤ ·)
        (e '' s : Set (Set.Icc (primeIrreducibleClosed R q) (primeIrreducibleClosed R p))) := by
    simpa [e, flip] using (IsMaxChain.image e hs).symm
  -- The catenary-space owner gives the common length in the irreducible-closed interval.
  have hlen :=
    CatenarySpace.maximalIrreducibleClosedChainsHaveLength
      (X := PrimeSpectrum R)
      ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone hpq) (e '' s) hsImage
  -- The interval relation isomorphism is injective, so the image chain has the same cardinality.
  rw [← e.toEquiv.injective.encard_image s]
  exact hlen

/-- In a catenary ring, every interval `[p, q]` in `Spec R` has a uniform bound on the cardinality
of its finite prime chains. This is the source-facing bounded-chain clause of Definition 10.105.1,
derived from the Chapter 5 catenary owner on `Spec R`. -/
theorem primeChainsBounded (p q : PrimeSpectrum R) (hpq : p ≤ q) :
    ∃ n : ℕ, ∀ s : Set (Set.Icc p q), IsChain (· ≤ ·) s → s.Finite → s.encard ≤ n + 1 := by
  -- Use the catenary length of `[V(q), V(p)]` as a uniform bound for every prime chain.
  refine ⟨ENat.toNat (codimBetween (primeIrreducibleClosed R q) (primeIrreducibleClosed R p)
      ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone hpq)), ?_⟩
  intro s hs _
  -- Extend the input chain to a flag and compare cardinalities.
  obtain ⟨F, _, hcard⟩ := chainEncard_le_flagEncard hs
  calc
    s.encard ≤ (F : Set (Set.Icc p q)).encard := hcard
    _ = ENat.toNat (codimBetween (primeIrreducibleClosed R q) (primeIrreducibleClosed R p)
        ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone hpq)) + 1 :=
      maximalPrimeChain_encard_eq p q hpq F.maxChain

/-- In a catenary ring, any two maximal prime chains in a fixed interval `[p, q]` have the same
cardinality. This is the source-facing equal-length clause of Definition 10.105.1, derived from
the canonical owner `IsCatenaryRing R`. -/
theorem maximalPrimeChainsHaveSameLength
    (p q : PrimeSpectrum R) (hpq : p ≤ q)
    {s t : Set (Set.Icc p q)} (hs : IsMaxChain (· ≤ ·) s) (ht : IsMaxChain (· ≤ ·) t) :
    s.encard = t.encard := by
  -- Both maximal chains transport to the same irreducible-closed interval, where catenarity fixes
  -- their common cardinality.
  calc
    s.encard = ENat.toNat (codimBetween (primeIrreducibleClosed R q) (primeIrreducibleClosed R p)
        ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).monotone hpq)) + 1 :=
      maximalPrimeChain_encard_eq p q hpq hs
    _ = t.encard :=
      (maximalPrimeChain_encard_eq p q hpq ht).symm

end IsCatenaryRing

/- Chap10 Definition 10 105 1: the source-facing interval-chain formulation is represented by
the bounded-chain theorem, together with the equal-length theorem recorded in the validator bridge
above. -/
recall IsCatenaryRing.primeChainsBounded

end
