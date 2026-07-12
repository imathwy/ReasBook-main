import Mathlib
import StacksProject_2024.Chap10.Lemma_10_72_7
import StacksProject_2024.Chap10.Proposition_10_103_4
import StacksProject_2024.Chap10.Definition_10_104_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open RingTheory Sequence IsLocalRing Ideal.Quotient

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [Module.CohenMacaulay R R]

/-
Source/core/bridge triage:
* primary domain: regular sequences and Cohen-Macaulay local rings in commutative algebra;
* source-facing: Lemma `10.104.2`, specialized from Proposition `10.103.4` to the self-module
  `R`, together with its quotient consequences stated at the local owner level from Definition
  `10.104.1`;
* core/canonical: `RingTheory.Sequence.IsRegular`, `Module.CohenMacaulay`, and the owner theorem
  `Module.exists_maximal_regularSequence_extension_of_supportDim_quotient_add_length_eq_of_cohenMacaulay`;
* bridge/view: the quotient rings `R ⧸ Ideal.ofList xs` and `R ⧸ Ideal.ofList (xs.take i)`.

Primitive data are only the list `xs`, its maximal-ideal membership when the source assumes it,
and the owner abstractions above. The quotient Cohen-Macaulay consequences are stated directly as
self-module properties of the quotient rings, not upgraded here to the later global ring owner.
-/

private theorem ofList_take_le_maximalIdeal_of_isRegular {xs : List R} (hreg : IsRegular R xs)
    {i : ℕ} : Ideal.ofList (xs.take i) ≤ maximalIdeal R := by
  have hxs : Ideal.ofList xs ≤ maximalIdeal R :=
    IsRegular.ofList_le_maximalIdeal hreg
  refine Ideal.span_le.mpr ?_
  intro x hx
  exact hxs <| Ideal.subset_span <| List.mem_of_mem_take hx

private theorem quotient_isLocalRing_of_isRegular_take {xs : List R} (hreg : IsRegular R xs)
    {i : ℕ} : IsLocalRing (R ⧸ Ideal.ofList (xs.take i)) := by
  have hI : Ideal.ofList (xs.take i) ≤ maximalIdeal R :=
    ofList_take_le_maximalIdeal_of_isRegular hreg
  have hne : Ideal.ofList (xs.take i) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hI
  have : Nontrivial (R ⧸ Ideal.ofList (xs.take i)) := by
    rw [Ideal.Quotient.nontrivial_iff]
    exact hne
  exact IsLocalRing.of_surjective' (mk _) mk_surjective

-- Proof sketch: this is Proposition `10.103.4` specialized to the self-module `R`, after
-- rewriting `supportDim R R` as `ringKrullDim R` and the quotient support dimension as the Krull
-- dimension of `R ⧸ Ideal.ofList xs`.
/-- Lemma 10.104.2: in a Noetherian local Cohen-Macaulay ring `R`, if
`ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R`, then `xs` extends to a regular
sequence of length `ringKrullDim R`. In a local ring, maximal-ideal containment of the extended
sequence is recovered from regularity by the auxiliary companion
`IsRegular.ofList_le_maximalIdeal`. -/
theorem exists_maximal_regularSequence_extension_of_ringKrullDim_quotient_add_length_eq
    {xs : List R} (hxs : ∀ x ∈ xs, x ∈ maximalIdeal R)
    (hquot : ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R) :
    ∃ xs' : List R,
      IsRegular R (xs ++ xs') ∧ ringKrullDim R = (xs ++ xs').length := sorry

-- Proof sketch: every prefix `xs.take i` of a regular sequence is regular, and quotienting a
-- Cohen-Macaulay local ring by a regular sequence stays Cohen-Macaulay at the local owner level
-- `Module.CohenMacaulay Q Q`. No separate bound `i ≤ xs.length` belongs in the public API, since
-- `xs.take i = xs` once `i` is past the end.
/-- If `xs` is a regular sequence, then every intermediate quotient
`R ⧸ Ideal.ofList (xs.take i)` is Cohen-Macaulay as a module over itself. -/
theorem selfModule_cohenMacaulay_quotient_take_of_isRegular {xs : List R}
    (hreg : IsRegular R xs) {i : ℕ} :
    let _ : IsLocalRing (R ⧸ Ideal.ofList (xs.take i)) :=
      quotient_isLocalRing_of_isRegular_take hreg
    Module.CohenMacaulay (R ⧸ Ideal.ofList (xs.take i)) (R ⧸ Ideal.ofList (xs.take i)) := sorry

-- Proof sketch: the prefix `xs.take i` of a regular sequence is regular, and mathlib already
-- supplies the additive dimension formula for quotienting by a regular sequence. Here the bound
-- `i ≤ xs.length` is part of the mathematical content because the conclusion is written with `+ i`
-- rather than `+ (xs.take i).length`.
/-- If `xs` is a regular sequence, then every intermediate quotient
`R ⧸ Ideal.ofList (xs.take i)` has dimension `ringKrullDim R - i`, written canonically as
`ringKrullDim (R ⧸ Ideal.ofList (xs.take i)) + i = ringKrullDim R`. -/
theorem ringKrullDim_quotient_take_add_eq_ringKrullDim_of_isRegular {xs : List R}
    (hreg : IsRegular R xs) {i : ℕ} (hi : i ≤ xs.length) :
    ringKrullDim (R ⧸ Ideal.ofList (xs.take i)) + i = ringKrullDim R := sorry

-- Proof sketch: the forward implication is the standard dimension formula for regular sequences.
-- For the converse, specialize Proposition `10.103.4` to the self-module `R`, as in the extension
-- theorem above, and pass from the maximal extension back to the initial segment `xs`.
/-- Companion criterion from Lemma 10.104.2: in a Noetherian local Cohen-Macaulay ring `R`, a
list `xs` of elements of `maximalIdeal R` is a regular sequence if and only if
`ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R`. -/
theorem isRegular_iff_ringKrullDim_quotient_add_length_eq {xs : List R}
    (hxs : ∀ x ∈ xs, x ∈ maximalIdeal R) :
    IsRegular R xs ↔ ringKrullDim (R ⧸ Ideal.ofList xs) + xs.length = ringKrullDim R := sorry

end
