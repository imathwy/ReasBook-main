import Mathlib.Data.ZMod.QuotientRing
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Quotient
import stacks_project.Chap15.Definition_15_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct
open IsLocalRing

noncomputable section

section

variable (p : ℕ) [Fact p.Prime]

/-
Domain-style sampling:
- primary domain: henselian pairs and local/non-local behavior of the tensor square of the
  `p`-adic integers;
- sampled owner declarations of the same kind:
  `HenselianRing`,
  `Ideal.le_ring_jacobson_of_henselianRing`,
  `isLocalHom_of_le_jacobson_bot`,
  `RingHom.domain_isLocalRing`,
  `PadicInt.residueField`,
  `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`;
- best owner abstraction: the source-facing statement is genuinely about the pair
  `(ℤ_[p] ⊗[ℤ] ℤ_[p], (p))`, so the main theorem should stay at the pair owner
  `HenselianRing Aₚ pAₚ`; the quotient-to-residue-field comparison and the non-locality
  contradiction are derived API, while the Moret-Bailly idempotent formula is a source-facing
  companion witness;
- primitive data: the prime `p`, the tensor square `Aₚ`, and the canonical extended maximal ideal
  `pAₚ = Ideal.map (algebraMap ℤ_[p] Aₚ) (maximalIdeal ℤ_[p])`, which is canonically the source
  ideal `(p)`;
- derived API: if `HenselianRing Aₚ pAₚ` held, then
  the owner field `HenselianRing.jac` and `isLocalHom_of_le_jacobson_bot` would make the quotient
  map `Aₚ → Aₚ ⧸ pAₚ` local, and
  `RingHom.domain_isLocalRing` would force `Aₚ` to be local because `Aₚ ⧸ pAₚ` is identified by
  `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` and `PadicInt.residueField` with the residue
  field `𝔽_p`; the odd-prime nontrivial idempotent is a companion witness rather than part of the
  main source-facing theorem.

Source/core/bridge triage:
- `source-facing`: `padicInteger_tensor_self_not_henselianRing`;
- `core/canonical`: `HenselianRing`, `IsLocalHom`, `IsLocalRing`,
  `Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, and `PadicInt.residueField`;
- `bridge/view`: the induced comparison `Aₚ ⧸ pAₚ ≃ κ(ℤ_[p])` and the explicit Moret-Bailly
  idempotent built from a square root of `1 + p`.
-/
local notation "Aₚ" => ℤ_[p] ⊗[ℤ] ℤ_[p]
local notation "mₚ" => maximalIdeal ℤ_[p]
local notation "κₚ" => ResidueField ℤ_[p]
local notation "pAₚ" => Ideal.map (algebraMap ℤ_[p] Aₚ) mₚ

-- Proof sketch: `Algebra.TensorProduct.quotIdealMapEquivQuotTensor Aₚ mₚ` identifies
-- `Aₚ ⧸ pAₚ` with `κₚ ⊗[ℤ_[p]] Aₚ`. Reassociating this tensor product and canceling the base
-- change along `ℤ_[p] → κₚ`, then applying `PadicInt.residueField`, identifies it with `κₚ`, so
-- it is local. If `(Aₚ, pAₚ)` were henselian, then the owner field `HenselianRing.jac` together
-- with `isLocalHom_of_le_jacobson_bot` would show that the quotient map `Aₚ → Aₚ ⧸ pAₚ` is a
-- local homomorphism. Since the target is local,
-- `RingHom.domain_isLocalRing` would force `Aₚ` to be local. Moret-Bailly shows that `Spec Aₚ` is
-- disconnected; for odd primes `p`, the companion idempotent theorem below gives an explicit
-- nontrivial idempotent witness.
private theorem padicInteger_tensor_self_quotient_isLocalRing :
    IsLocalRing (Aₚ ⧸ pAₚ) := by
  let _ : IsLocalRing κₚ := inferInstance
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor Aₚ mₚ
  -- The canonical quotient/tensor owner above is the correct bridge. The remaining identification
  -- with `κₚ` uses tensor reassociation, base-change cancellation, and `PadicInt.residueField`.
  sorry

private theorem padicInt_two_isUnit_of_two_lt (hp_odd : 2 < p) : IsUnit (2 : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  exact (PadicInt.norm_natCast_eq_one_iff).2 <|
    Nat.coprime_of_lt_prime (by decide) hp_odd Fact.out

private theorem exists_padicInt_unit_sq_eq_one_add_p_of_two_lt (hp_odd : 2 < p) :
    ∃ u : ℤ_[p]ˣ, (u : ℤ_[p]) ^ 2 = 1 + p := by
  sorry

/-- The canonical tensor-square ideal in Example 15.11.14 is the source ideal `(p)`. -/
theorem padicInteger_tensor_self_pIdeal_eq_span :
    pAₚ = Ideal.span ({algebraMap ℤ_[p] Aₚ p} : Set Aₚ) := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton]

-- Moret-Bailly's explicit tensor-square idempotent attached to a square root of `1 + p`.
def padicInteger_tensor_self_moretBaillyIdempotent [Invertible (2 : ℤ_[p])]
    (u : ℤ_[p]ˣ) : Aₚ :=
  ((⅟(2 : ℤ_[p])) ⊗ₜ[ℤ] (1 : ℤ_[p])) *
    (1 - ((↑u⁻¹ : ℤ_[p]) ⊗ₜ[ℤ] (↑u : ℤ_[p])))

-- If `u² = 1 + p`, Moret-Bailly's explicit tensor-square element is idempotent.
theorem padicInteger_tensor_self_moretBaillyIdempotent_isIdempotent
    [Invertible (2 : ℤ_[p])]
    (u : ℤ_[p]ˣ) (hu : (u : ℤ_[p]) ^ 2 = 1 + p) :
    IsIdempotentElem (padicInteger_tensor_self_moretBaillyIdempotent p u) := by
  sorry

-- If `u² = 1 + p`, Moret-Bailly's explicit tensor-square idempotent is nonzero.
theorem padicInteger_tensor_self_moretBaillyIdempotent_ne_zero
    [Invertible (2 : ℤ_[p])]
    (u : ℤ_[p]ˣ) (hu : (u : ℤ_[p]) ^ 2 = 1 + p) :
    padicInteger_tensor_self_moretBaillyIdempotent p u ≠ 0 := by
  sorry

-- If `u² = 1 + p`, Moret-Bailly's explicit tensor-square idempotent is not `1`.
theorem padicInteger_tensor_self_moretBaillyIdempotent_ne_one
    [Invertible (2 : ℤ_[p])]
    (u : ℤ_[p]ˣ) (hu : (u : ℤ_[p]) ^ 2 = 1 + p) :
    padicInteger_tensor_self_moretBaillyIdempotent p u ≠ 1 := by
  sorry

/-- For odd primes `p`, Moret-Bailly exhibits a nontrivial idempotent in
`ℤ_[p] ⊗[ℤ] ℤ_[p]`. -/
theorem padicInteger_tensor_self_exists_nontrivial_idempotent_of_two_lt (hp_odd : 2 < p) :
    ∃ e : Aₚ, IsIdempotentElem e ∧ e ≠ 0 ∧ e ≠ 1 := by
  let h2 : IsUnit (2 : ℤ_[p]) := padicInt_two_isUnit_of_two_lt p hp_odd
  letI := h2.invertible
  obtain ⟨u, hu⟩ := exists_padicInt_unit_sq_eq_one_add_p_of_two_lt p hp_odd
  refine ⟨padicInteger_tensor_self_moretBaillyIdempotent p u, ?_⟩
  exact ⟨
    padicInteger_tensor_self_moretBaillyIdempotent_isIdempotent p u hu,
    padicInteger_tensor_self_moretBaillyIdempotent_ne_zero p u hu,
    padicInteger_tensor_self_moretBaillyIdempotent_ne_one p u hu⟩

/-- Moret-Bailly's tensor square `ℤ_[p] ⊗[ℤ] ℤ_[p]` is not local. -/
theorem padicInteger_tensor_self_not_isLocalRing :
    ¬ IsLocalRing Aₚ := by
  -- `Spec (ℤ_[p] ⊗[ℤ] ℤ_[p])` is disconnected; for odd primes the companion theorem above gives
  -- an explicit nontrivial idempotent witnessing this.
  sorry

/-- Example 15.11.14 (Moret-Bailly): the coproduct of the henselian pairs `(ℤ_[p], (p))` and
`(ℤ_[p], (p))`, namely the pair `(ℤ_[p] ⊗[ℤ] ℤ_[p], (p))`, is not henselian. -/
theorem padicInteger_tensor_self_not_henselianRing :
    ¬ HenselianRing Aₚ (Ideal.span ({algebraMap ℤ_[p] Aₚ p} : Set Aₚ)) := by
  rw [← padicInteger_tensor_self_pIdeal_eq_span p]
  intro hH
  haveI : HenselianRing Aₚ pAₚ := hH
  haveI : IsLocalHom (Ideal.Quotient.mk pAₚ) :=
    isLocalHom_of_le_jacobson_bot pAₚ <| by
      simpa [Ideal.jacobson_bot] using Ideal.le_ring_jacobson_of_henselianRing pAₚ
  haveI : IsLocalRing (Aₚ ⧸ pAₚ) := padicInteger_tensor_self_quotient_isLocalRing p
  have hlocal : IsLocalRing Aₚ := RingHom.domain_isLocalRing (Ideal.Quotient.mk pAₚ)
  exact padicInteger_tensor_self_not_isLocalRing p hlocal

end
