import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_58_1

-- Declarations for this item will be appended below by the statement pipeline.

open HomogeneousIdeal

universe u v

section

variable {S : Type u} [CommRing S]
variable {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Domain triage:
* source-facing: the Stacks finite-generation and Noetherian criteria phrased using the irrelevant
  ideal of a nonnegatively graded ring.
* core/canonical owners: `Algebra.FiniteType`, `HomogeneousIdeal.irrelevant`, and
  `GradedRing.GradeZero.isNoetherianRing`.
* bridge/view: `finiteType_iff_irrelevant_fg` converts between the owner finite-type datum and the
  source-facing finite generation of `𝒜₊.toIdeal`.

Primitive data are the graded ring and its canonical owner ideal `𝒜₊`. Finite type over `𝒜 0`,
Noetherianity of `𝒜 0`, and finite generation of `𝒜₊.toIdeal` are derived API and should be proved
from the owner declarations instead of being stored in a parallel wrapper.

Relevant owner declarations sampled for this refinement:
* `GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero`
* `homogeneous_adjoin_eq_top_iff_span_eq_irrelevant`
* `GradedRing.GradeZero.isNoetherianRing`
-/

/-- Library-facing form of Lemma 10.58.2 (Stacks, Tag `00JW`): a nonnegatively graded ring is of
finite type over its degree-zero part exactly when its irrelevant ideal is finitely generated. -/
-- Proof sketch: if `S` is finite type over `𝒜 0`, choose finitely many algebra generators and
-- decompose them into homogeneous components of positive degree; Lemma `10.58.1` then shows that
-- these homogeneous generators generate the irrelevant ideal. Conversely, if `𝒜₊` is finitely
-- generated, choose finitely many homogeneous generators for it, apply Lemma `10.58.1` to obtain
-- `Algebra.adjoin (𝒜 0) _ = ⊤`, and conclude that `S` is finite type over `𝒜 0`.
theorem finiteType_iff_irrelevant_fg :
    Algebra.FiniteType (𝒜 0) S ↔ 𝒜₊.toIdeal.FG := by
  constructor
  · intro
    classical
    obtain ⟨s, hs, hsdeg⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
    have hs_deg : ∀ ⦃x⦄, x ∈ (s : Set S) → ∃ n > 0, x ∈ 𝒜 n := by
      intro x hx
      rcases hsdeg x hx with ⟨n, hn, hi⟩
      exact ⟨n, Nat.pos_of_ne_zero hn, hi⟩
    have hspan : Ideal.span (s : Set S) = 𝒜₊.toIdeal := by
      exact
        (homogeneous_adjoin_eq_top_iff_span_eq_irrelevant 𝒜 (s : Set S) hs_deg).1
          (by simpa using hs)
    rw [← hspan]
    exact ⟨s, rfl⟩
  · rintro ⟨s, hs⟩
    classical
    let u : Set S := ⋃ n > 0, (𝒜 n : Set S)
    have hs' : (s : Set S) ⊆ Ideal.span u := by
      intro x hx
      have hx' : x ∈ 𝒜₊.toIdeal := by
        rw [← hs]
        exact Ideal.subset_span hx
      rw [irrelevant_eq_span 𝒜] at hx'
      simpa [u] using hx'
    obtain ⟨t, ht_sub, hs_le⟩ :=
      Submodule.subset_span_finite_of_subset_span hs'
    have ht_deg : ∀ ⦃x⦄, x ∈ (t : Set S) → ∃ n > 0, x ∈ 𝒜 n := by
      intro x hx
      rcases Set.mem_iUnion.mp (ht_sub hx) with ⟨n, hn⟩
      rcases Set.mem_iUnion.mp hn with ⟨hn, hi⟩
      exact ⟨n, hn, hi⟩
    have hirr : 𝒜₊.toIdeal ≤ Ideal.span (t : Set S) := by
      rw [← hs]
      refine Ideal.span_le.2 ?_
      exact hs_le
    have hspan : Ideal.span (t : Set S) = 𝒜₊.toIdeal := by
      refine le_antisymm ?_ hirr
      refine Ideal.span_le.2 ?_
      intro x hx
      rcases ht_deg hx with ⟨n, hn, hx_n⟩
      exact mem_irrelevant_of_mem 𝒜 hn hx_n
    exact ⟨⟨t, by
      exact
        (homogeneous_adjoin_eq_top_iff_span_eq_irrelevant 𝒜 (t : Set S) ht_deg).2 hspan⟩⟩

/-- Lemma 10.58.2 (Stacks, Tag `00JW`): an `ℕ`-graded commutative ring `S` is Noetherian if and
only if its degree-zero piece `𝒜 0` is Noetherian and its irrelevant ideal `S₊` is finitely
generated. -/
-- Proof sketch: if `S` is Noetherian, then the degree-zero piece is Noetherian by the existing
-- mathlib instance `GradedRing.GradeZero.isNoetherianRing`, and the irrelevant ideal is finitely
-- generated because every ideal of a Noetherian ring is finitely generated. Conversely, if `𝒜 0`
-- is Noetherian and `𝒜₊` is finitely generated, then `finiteType_iff_irrelevant_fg` makes `S`
-- finite type over `𝒜 0`, so `Algebra.FiniteType.isNoetherianRing` yields that `S` is
-- Noetherian.
lemma isNoetherianRing_iff_degreeZero_isNoetherianRing_and_irrelevant_fg :
    IsNoetherianRing S ↔
      IsNoetherianRing (𝒜 0) ∧ 𝒜₊.toIdeal.FG := by
  constructor
  · intro
    exact ⟨inferInstance, 𝒜₊.toIdeal.fg_of_isNoetherianRing⟩
  · rintro ⟨h0, hfg⟩
    let _ : IsNoetherianRing (𝒜 0) := h0
    let _ : Algebra.FiniteType (𝒜 0) S := (finiteType_iff_irrelevant_fg 𝒜).2 hfg
    exact Algebra.FiniteType.isNoetherianRing (𝒜 0) S

/-- If a graded ring is Noetherian, then it is of finite type over its degree-zero part. -/
instance [IsNoetherianRing S] : Algebra.FiniteType (𝒜 0) S :=
  (finiteType_iff_irrelevant_fg 𝒜).2 (𝒜₊.toIdeal.fg_of_isNoetherianRing)

end
