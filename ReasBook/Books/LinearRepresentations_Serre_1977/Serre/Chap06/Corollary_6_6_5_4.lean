import LinearRepresentations_Serre_1977.Serre.Chap06.Corollary_6_6_5_3
import LinearRepresentations_Serre_1977.Serre.Chap06.Exercise_6_6_5_6
import LinearRepresentations_Serre_1977.Serre.Chap06.Proposition_6_6_5_1
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5
import Mathlib.NumberTheory.Niven

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators MonoidAlgebra Representation

noncomputable section

universe u v

namespace Representation

section

variable {k : Type*} [Field k]
variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module k V]

/-- Helper for Corollary 6-6.5-4: the inverse character of a finite-dimensional representation is
a class function. -/
lemma inverse_character_mem_classFunctionSubmodule [FiniteDimensional k V]
    (ρ : Representation k G V) :
    (fun s : G ↦ ρ.character s⁻¹) ∈ classFunctionSubmodule k G := by
  -- Conjugate elements have conjugate inverses, so the inverse character stays constant on
  -- conjugacy classes.
  rw [mem_classFunctionSubmodule_iff]
  refine ⟨?_⟩
  intro a b hab
  rcases isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hab) with ⟨g, hg⟩
  calc
    ρ.character a⁻¹ = ρ.character (g * a⁻¹ * g⁻¹) := by
      exact (ρ.char_conj a⁻¹ g).symm
    _ = ρ.character b⁻¹ := by
      -- Rewrite the conjugate of `a⁻¹` as `b⁻¹`.
      have hinv : g * a⁻¹ * g⁻¹ = b⁻¹ := by
        rw [← hg]
        simp [mul_assoc]
      simp [hinv]

end

section

variable {k : Type*} [Field k] [CharZero k]

/-- Helper for Corollary 6-6.5-4: if `(m : k) / n` is integral over `ℤ`, then `n` divides `m`.
-/
lemma nat_dvd_of_isIntegral_natCast_div (m n : ℕ) (hn : n ≠ 0)
    (h : IsIntegral ℤ ((m : k) / n)) :
    n ∣ m := by
  let q : ℚ := m / n
  have hq : IsIntegral ℤ q := by
    -- Descend integrality from the ambient field to the rational scalar itself.
    have hqk : IsIntegral ℤ (q : k) := by
      simpa [q] using h
    exact IsIntegral.ratCast_iff.mp hqk
  obtain ⟨z, hz : q = z⟩ := hq.exists_int_iff_exists_rat |>.mp ⟨q, rfl⟩
  have hden : q.den = 1 := by
    -- Once the rational is an integer, its denominator is `1`.
    rw [hz]
    simp
  exact (Rat.den_div_natCast_eq_one_iff m n hn).mp <| by
    simpa [q] using hden

end

section

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module k V]

-- Source/core/bridge triage: this corollary is source-facing. The core owner declarations reused
-- in the proof are the Chapter 6 center/class-function equivalence `centerClassFunctionEquiv`, the
-- Chapter 6 integrality theorem `isIntegral_finrank_inv_sum_coeff_mul_character`, and the mathlib
-- owner theorem `Representation.IsIrreducible.finrank_intertwiningMap_self`, applied through the
-- canonical character-pairing identity `card_inv_mul_sum_char_mul_char_eq_finrank`.
--
-- Primitive data: only the irreducible representation `ρ`; the group-algebra element used in the
-- proof is derived canonically from the class function `s ↦ ρ.character s⁻¹`.
-- Derived API: coefficientwise integrality from `char_isIntegral_of_isOfFinOrder`, then
-- `isIntegral_finrank_inv_sum_coeff_mul_character`, then the canonical character self-pairing.
--
-- Proof sketch: view `s ↦ ρ.character s⁻¹` as a class function and transport it through
-- `centerClassFunctionEquiv` to the corresponding central group-algebra element
-- `u = ∑ s : G, ρ.character s⁻¹ • s`, whose coefficients are algebraic integers by
-- Proposition `6-6.5-1`. Corollary `6-6.5-3` then shows that the scalar
-- `(Nat.card G : k) / Module.finrank k V` is an algebraic integer. Since this scalar is rational,
-- it is an integer, which is equivalent to `Module.finrank k V ∣ Nat.card G`.
/-- Corollary 6-6.5-4: the degree of an irreducible finite-dimensional representation of a finite
group over an algebraically closed field of characteristic zero divides the order of the group. -/
theorem finrank_dvd_card (ρ : Representation k G V) [ρ.IsIrreducible] :
    Module.finrank k V ∣ Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  -- Install the finite-dimensional and simple-module instances needed by the Chapter 6 API.
  letI : FiniteDimensional k V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Module k[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule k[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial k[G] V
  have hfinrank_ne_zero : (Module.finrank k V : k) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt Module.finrank_pos
  letI : NeZero (Module.finrank k V : k) := ⟨hfinrank_ne_zero⟩
  have hcard_ne_zero : (Nat.card G : k) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero hcard_ne_zero
  let f : classFunctionSubmodule k G :=
    ⟨fun s ↦ ρ.character s⁻¹, inverse_character_mem_classFunctionSubmodule ρ⟩
  let u : Subalgebra.center k (k[G]) :=
    (centerClassFunctionEquiv k).symm f
  have hu : ∀ s : G, ((u : k[G]) s) = ρ.character s⁻¹ := by
    -- The coefficients of the central element `u` are exactly the inverse character values.
    intro s
    rfl
  have hcoeff : ∀ s : G, IsIntegral ℤ ((u : k[G]) s) := by
    -- Proposition `6-6.5-1` gives algebraic integrality of each inverse character coefficient.
    intro s
    rw [hu s]
    exact char_isIntegral_of_isOfFinOrder ρ (isOfFinOrder_of_finite s⁻¹)
  have hsum : ∑ s : G, ρ.character s⁻¹ * ρ.character s = Nat.card G := by
    -- Orthogonality identifies the normalized self-pairing with the self-intertwining rank.
    have hpair :
        (Nat.card G : k)⁻¹ * ∑ s : G, ρ.character s⁻¹ * ρ.character s = 1 := by
      simpa [mul_comm, IsIrreducible.finrank_intertwiningMap_self ρ] using
        (card_inv_mul_sum_char_mul_char_eq_finrank ρ ρ)
    field_simp [hcard_ne_zero] at hpair
    simpa using hpair
  have hint :
      IsIntegral ℤ ((Nat.card G : k) / Module.finrank k V) := by
    have hint_raw := isIntegral_finrank_inv_sum_coeff_mul_character ρ u hcoeff
    have hsum' :
        (Module.finrank k V : k)⁻¹ * ∑ s : G, (u : k[G]) s * ρ.character s =
          (Nat.card G : k) / Module.finrank k V := by
      -- Rewrite Corollary `6-6.5-3` using the explicit coefficients of `u` and the self-pairing
      -- identity for `ρ.character`.
      calc
        (Module.finrank k V : k)⁻¹ * ∑ s : G, (u : k[G]) s * ρ.character s
          = (Module.finrank k V : k)⁻¹ * ∑ s : G, ρ.character s⁻¹ * ρ.character s := by
              simp [hu]
        _ = (Module.finrank k V : k)⁻¹ * Nat.card G := by rw [hsum]
        _ = (Nat.card G : k) / Module.finrank k V := by
              simp [div_eq_mul_inv, mul_comm]
    rw [hsum'] at hint_raw
    exact hint_raw
  -- A rational algebraic integer is an integer, so the denominator `dim V` divides `|G|`.
  exact nat_dvd_of_isIntegral_natCast_div
    (Nat.card G) (Module.finrank k V) (Nat.ne_of_gt Module.finrank_pos) hint

end

end Representation
