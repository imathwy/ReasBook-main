import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace SetRel

section

variable {X : Type u} {Y : Type v}
variable [Sub X]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 5.24.6 names those cyclically monotone multivalued mappings whose
  graphs are maximal under inclusion among cyclically monotone graphs.
- `core/canonical`: the owner abstraction is exactly the generic order-theoretic predicate
  `Maximal`, applied to the Chapter 5 owner `SetRel.CyclicallyMonotone`; no extra synonym owner is
  introduced in this file.
- `bridge/view`: the source phrase "graph is not properly contained" is exactly the order relation
  on `SetRel X Y`, so no extra wrapper or graph package belongs in the API.

Domain-style sampling used here:
- `SetRel.CyclicallyMonotone` from `Definition_5_24_5`;
- `Maximal` from mathlib's order-theoretic API;
- direct uses of `Maximal` elsewhere in the project, such as Theorem 18.2 and Corollary 37.5.2.

Primitive data vs derived API:
- primitive owner data already exist upstream: a relation `ρ : SetRel X Y`;
- primitive source-facing property reused here: `CMon[L](ρ)`;
- derived API in this file: source-facing notation for maximal cyclic monotonicity in default and
  canonical explicit-pairing forms (`MaxCMon[L](ρ)` and `MaxCMonPair[p](ρ)`), together with
  pairing-transport and strict-extension unpacking theorems.

Layer target: `core/canonical` reuse of `Maximal` on the existing cyclically monotone owner.
-/

/- Definition 5.24.6 reuses the canonical order owner `Maximal` on
`SetRel.CyclicallyMonotone`. -/
recall Maximal

/-- Source-facing notation for Definition 5.24.6: `MaxCMon[L](ρ)` means that `ρ` is maximal among
relations that are cyclically monotone with pairing codomain `L`. -/
scoped[SetRel] notation "MaxCMon[" L "](" ρ ")" =>
  Maximal (fun σ ↦ CMon[L](σ)) ρ

/-- Canonical explicit-pairing notation for maximal cyclic monotonicity. The codomain is
determined by the pairing instance, so this surface avoids redundant `L` noise. -/
scoped[SetRel] notation "MaxCMonPair[" pairing "](" ρ ")" =>
  Maximal (fun σ ↦ CMonPair[pairing](σ)) ρ

namespace MaxCMon

/-- If two pairing instances on the same `(X, Y, L)` are pointwise equal, maximal cyclic
monotonicity of `ρ` transfers from the first pairing to the second. -/
theorem of_pairing_eq {L : Type w}
    [LE L] [AddCommMonoid L]
    {pairing₁ pairing₂ : HasPairing X Y L}
    {ρ : SetRel X Y}
    (hρ : MaxCMonPair[pairing₁](ρ))
    (hpair : ∀ x : X, ∀ y : Y, pairing₁.pairing x y = pairing₂.pairing x y) :
    MaxCMonPair[pairing₂](ρ) := by
  rcases hρ with ⟨hρcyc, hmaxρ⟩
  refine ⟨?_, ?_⟩
  · exact SetRel.CyclicallyMonotone.of_pairing_eq
      (pairing₁ := pairing₁) (pairing₂ := pairing₂) hρcyc hpair
  · intro σ hσcyc hρσ
    exact hmaxρ
      (SetRel.CyclicallyMonotone.of_pairing_eq
        (pairing₁ := pairing₂) (pairing₂ := pairing₁) hσcyc (fun x y ↦ (hpair x y).symm))
      hρσ

/-- Maximal cyclic monotonicity is invariant under replacement of the pairing by a pointwise equal
one. -/
theorem iff_pairing_eq {L : Type w}
    [LE L] [AddCommMonoid L]
    {pairing₁ pairing₂ : HasPairing X Y L}
    {ρ : SetRel X Y}
    (hpair : ∀ x : X, ∀ y : Y, pairing₁.pairing x y = pairing₂.pairing x y) :
    MaxCMonPair[pairing₁](ρ) ↔
      MaxCMonPair[pairing₂](ρ) := by
  constructor
  · intro hρ
    exact of_pairing_eq (pairing₁ := pairing₁) (pairing₂ := pairing₂) hρ hpair
  · intro hρ
    exact of_pairing_eq (pairing₁ := pairing₂) (pairing₂ := pairing₁) hρ
      (fun x y ↦ (hpair x y).symm)

/-- Explicit-pairing strict-extension form of Definition 5.24.6. This owner-prefixed surface keeps
the API aligned with the `MaxCMon` notation family. -/
theorem pair_iff_forall_gt
    {L : Type w} [LE L] [AddCommMonoid L] {pairing : HasPairing X Y L} {ρ : SetRel X Y} :
    MaxCMonPair[pairing](ρ) ↔
      CMonPair[pairing](ρ) ∧
        ∀ ⦃σ : SetRel X Y⦄, ρ < σ → ¬CMonPair[pairing](σ) := by
  simpa using
    (maximal_iff_forall_gt (P := fun σ : SetRel X Y ↦ CMonPair[pairing](σ)) (x := ρ))

/-- Canonical relation-owner strict-extension form of Definition 5.24.6. -/
theorem iff_forall_gt
    {L : Type w} [LE L] [AddCommMonoid L] [HasPairing X Y L] {ρ : SetRel X Y} :
    MaxCMon[L](ρ) ↔
      CMon[L](ρ) ∧
        ∀ ⦃σ : SetRel X Y⦄, ρ < σ → ¬CMon[L](σ) := by
  simpa using
    (maximal_iff_forall_gt (P := fun σ : SetRel X Y ↦ CMon[L](σ)) (x := ρ))

end MaxCMon

/-- Explicit-pairing strict-extension form of Definition 5.24.6. -/
theorem maximalCyclicallyMonotone_iff_explicitPairing
    {L : Type w} [LE L] [AddCommMonoid L] {pairing : HasPairing X Y L} {ρ : SetRel X Y} :
    MaxCMonPair[pairing](ρ) ↔
      CMonPair[pairing](ρ) ∧
        ∀ ⦃σ : SetRel X Y⦄, ρ < σ → ¬CMonPair[pairing](σ) := by
  simpa using (MaxCMon.pair_iff_forall_gt (pairing := pairing) (ρ := ρ))

/-- Definition 5.24.6 at the canonical relation owner layer: `ρ` is maximal cyclically monotone
iff `ρ` is cyclically monotone and has no proper cyclically monotone extension. Here `<` on
`SetRel X Y` is strict graph inclusion. -/
theorem maximalCyclicallyMonotone_iff
    {L : Type w} [LE L] [AddCommMonoid L] [HasPairing X Y L] {ρ : SetRel X Y} :
    MaxCMon[L](ρ) ↔
      CMon[L](ρ) ∧
        ∀ ⦃σ : SetRel X Y⦄, ρ < σ → ¬CMon[L](σ) := by
  simpa using (MaxCMon.iff_forall_gt (L := L) (ρ := ρ))

end

end SetRel
