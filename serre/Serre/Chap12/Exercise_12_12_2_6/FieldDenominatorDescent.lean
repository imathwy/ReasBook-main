import Mathlib
import Serre.Chap02.Proposition_2_2_2_1
import Serre.Chap03.Theorem_3_3_2_1
import Serre.Chap06.Corollary_6_6_5_4
import Serre.Chap06.Proposition_6_6_5_5
import Serre.Chap07.Proposition_7_7_2_1
import Serre.Chap12.Exercise_12_12_2_3.API
import Serre.Chap12.Exercise_12_12_2_6.CharacterBasisCoefficients
import Serre.Chap12.Exercise_12_12_2_6.ComplexMinimalRealization
import Serre.Chap12.Exercise_12_12_2_6.FieldTensorCenterBridge
import Serre.Chap12.Exercise_12_12_2_6.ScalarExtensionConstituents
import Serre.Chap12.Proposition_12_12_2_1

noncomputable section

open scoped BigOperators
open scoped Representation
open scoped Representation.ExternalTensor
open scoped SubgroupInduction

universe u v w

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

attribute [local instance] ULift.algebra'

section FieldPart

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_field : Fintype G := Fintype.ofFinite G
/-- Helper for Exercise 12-12.2-6: over a common ambient universe, an irreducible
finite-dimensional representation admits a canonical Schur denominator. -/
theorem exists_schur_denominator_of_irreducible_rep_same_universe_local
    {K0 : Type (max u v)} [Field K0] [CharZero K0]
    {G0 : Type (max u v)} [Group G0] [Finite G0]
    (ρ : Rep K0 G0)
    [ρ.ρ.IsIrreducible] :
    ∃ n : ℕ+, FDRep.IsSchurDenominator (FDRep.of ρ.ρ) n := by
  letI : FiniteDimensional K0 ρ :=
    Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  let τ : FDRep K0 G0 := FDRep.of ρ.ρ
  have hτirr : Representation.IsIrreducible τ.ρ := by
    simpa [τ] using (inferInstance : Representation.IsIrreducible ρ.ρ)
  letI : Representation.IsIrreducible τ.ρ := hτirr
  letI : CategoryTheory.Simple τ := FDRep.simple_of_isIrreducible τ
  -- Once the owner lives in one universe, the field-side Schur-denominator theorem applies
  -- directly.
  exact
    exists_schur_denominator_of_simple_local
      (K := K0) (G := G0) (V := τ)

/-- Helper for Exercise 12-12.2-6: every admissible denominator for an irreducible character
still divides the degree even when the field and group live in different universes. -/
theorem scaled_character_denominator_dvd_finrank_universe_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (hscaled : ((((m : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G)) :
    (m : ℕ) ∣ Module.finrank K1 ρ := by
  letI : FiniteDimensional K1 ρ :=
    Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  have hscaled_closure :
      ((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((m : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈
        R[AlgebraicClosure K1](G) := by
    -- Unpack the source-side `R̄` witness as an honest character-ring element over the closure.
    exact
      (mem_overlineCharacterRingInExtension_iff K1 (AlgebraicClosure K1)
        ((((m : ℕ) : K1)⁻¹) • ρ.ρ.character)).1 hscaled
  obtain ⟨z, hz⟩ :
      ∃ z : ℤ,
        (((IsScalarTower.toAlgHom ℤ K1 (AlgebraicClosure K1)).compLeft G)
          ((((m : ℕ) : K1)⁻¹) • ρ.ρ.character)) 1 =
            (z : AlgebraicClosure K1) := by
    refine
      Algebra.adjoin_induction
        (p := fun χ _ ↦ ∃ z : ℤ, χ 1 = (z : AlgebraicClosure K1)) ?_ ?_ ?_ ?_ hscaled_closure
    · intro χ hχ
      rcases hχ with ⟨τ, hτfd, _hτirr, rfl⟩
      refine ⟨Module.finrank (AlgebraicClosure K1) τ, ?_⟩
      letI : FiniteDimensional (AlgebraicClosure K1) τ := hτfd
      simpa using
        (Representation.char_one (K := AlgebraicClosure K1) (G := G) τ.ρ)
    · intro n
      exact ⟨n, by simp⟩
    · intro χ ψ _ _ hχ hψ
      rcases hχ with ⟨a, ha⟩
      rcases hψ with ⟨b, hb⟩
      refine ⟨a + b, ?_⟩
      simp [ha, hb]
    · intro χ ψ _ _ hχ hψ
      rcases hχ with ⟨a, ha⟩
      rcases hψ with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      simp [ha, hb, Int.cast_mul]
  have hzK :
      ((((m : ℕ) : K1)⁻¹) • ρ.ρ.character) 1 = (z : K1) := by
    apply (algebraMap K1 (AlgebraicClosure K1)).injective
    simpa using hz
  have hscaled_one :
      (((m : ℕ) : K1)⁻¹) * (Module.finrank K1 ρ : K1) = (z : K1) := by
    -- Evaluating the scaled character at `1` converts the overline witness into an integral degree
    -- relation.
    simpa [Representation.char_one, smul_eq_mul] using hzK
  have hmK_ne : ((m : ℕ) : K1) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  have hmulK : ((m : ℕ) : K1) * (z : K1) = (Module.finrank K1 ρ : K1) := by
    calc
      ((m : ℕ) : K1) * (z : K1)
          = ((m : ℕ) : K1) * ((((m : ℕ) : K1)⁻¹) * (Module.finrank K1 ρ : K1)) := by
              rw [hscaled_one]
      _ = (Module.finrank K1 ρ : K1) := by
            field_simp [hmK_ne]
  have hdivZ : ((m : ℤ) : ℤ) ∣ (Module.finrank K1 ρ : ℤ) := by
    refine ⟨z, ?_⟩
    exact_mod_cast hmulK.symm
  exact Int.natCast_dvd_natCast.mp (by simpa using hdivZ)

/-- Helper for Exercise 12-12.2-6: hide the universe repair inside a source-facing canonical
denominator witness for the irreducible character itself. -/
theorem exists_schur_denominator_of_irreducible_rep_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible] :
    ∃ n : ℕ+,
      ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) ∧
        ∀ d : ℕ+, ((((d : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) → d ≤ n := by
  classical
  letI : FiniteDimensional K1 ρ :=
    Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  let P : ℕ → Prop := fun n ↦
    ∃ hn : 0 < n, ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G)
  have hP_one : P 1 := by
    refine ⟨zero_lt_one, ?_⟩
    -- The degree-one denominator is the character itself, hence already lies in `R̄[K1](G)`.
    simpa using
      characterRingOverField_le_overlineCharacterRing K1 G
        (rep_character_mem_characterRingOverField_universe_local
          (K' := K1) (H := G) (ρ := ρ.ρ))
  have hρ_nontriv : Nontrivial ρ := by
    -- An irreducible representation cannot have trivial carrier, or else `⊥ = ⊤`.
    by_contra hρ_trivial
    letI : Subsingleton ρ := not_nontrivial_iff_subsingleton.mp hρ_trivial
    have hbot : (⊥ : Subrepresentation ρ.ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        trivial
      · intro _
        simpa using (Subsingleton.elim x 0)
    exact bot_ne_top hbot
  have hdim_pos : 0 < Module.finrank K1 ρ := by
    simpa using (Module.finrank_pos_iff.mpr hρ_nontriv)
  have hbounded :
      ∀ n : ℕ+, ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) →
        (n : ℕ) ≤ Module.finrank K1 ρ := by
    intro n hn
    have hdiv :
        (n : ℕ) ∣ Module.finrank K1 ρ :=
      scaled_character_denominator_dvd_finrank_universe_local
        (K1 := K1) (G := G) (ρ := ρ) (m := n) hn
    exact Nat.le_of_dvd hdim_pos hdiv
  let nNat := Nat.findGreatest P (Module.finrank K1 ρ)
  have hn_prop : P nNat := by
    exact Nat.findGreatest_spec (Nat.succ_le_of_lt hdim_pos) hP_one
  rcases hn_prop with ⟨hn_pos, hn_mem⟩
  refine ⟨⟨nNat, hn_pos⟩, hn_mem, ?_⟩
  intro d hd
  have hPd : P (d : ℕ) := ⟨d.2, hd⟩
  exact Nat.le_findGreatest (hbounded d hd) hPd

/-- Helper for Exercise 12-12.2-6: the maximal Schur denominator dominates every other
admissible denominator by divisibility, not only by the order bound used to construct it. -/
theorem admissible_denominator_dvd_of_isSchurDenominator_local
    {V : FDRep K G} [Simple V]
    {m : ℕ+}
    (hm : FDRep.IsSchurDenominator V m)
    {n : ℕ+}
    (hn : FDRep.schurScaledCharacter V n ∈ R̄[K](G)) :
    (n : ℕ) ∣ (m : ℕ) := by
  let g : ℕ := Nat.gcd (m : ℕ) (n : ℕ)
  let a : ℕ := (n : ℕ) / g
  let b : ℕ := (m : ℕ) / g
  have hg_pos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_right _ n.pos
  have hga : a * g = (n : ℕ) := by
    dsimp [a, g]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right (m : ℕ) (n : ℕ))
  have hgb : b * g = (m : ℕ) := by
    dsimp [b, g]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left (m : ℕ) (n : ℕ))
  have hcop : Nat.Coprime a b := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hgdiv : ((n : ℕ) / g).gcd ((m : ℕ) / g) = (n : ℕ).gcd (m : ℕ) / g := by
      exact Nat.gcd_div (Nat.gcd_dvd_right (m : ℕ) (n : ℕ)) (Nat.gcd_dvd_left (m : ℕ) (n : ℕ))
    dsimp [g, a, b] at hgdiv ⊢
    simpa [Nat.gcd_comm, Nat.div_self hg_pos] using hgdiv
  let l : ℕ+ := ⟨Nat.lcm (m : ℕ) (n : ℕ), Nat.lcm_pos m.pos n.pos⟩
  have hma_assoc : (m : ℕ) * (a * g) = ((m : ℕ) * a) * g := by
    simp [Nat.mul_assoc]
  have hma_comm : ((m : ℕ) * a) * g = g * ((m : ℕ) * a) := by
    ac_rfl
  have hnb_assoc : (n : ℕ) * (b * g) = ((n : ℕ) * b) * g := by
    simp [Nat.mul_assoc]
  have hnb_comm : ((n : ℕ) * b) * g = g * ((n : ℕ) * b) := by
    ac_rfl
  have hmn_comm : (m : ℕ) * (n : ℕ) = (n : ℕ) * (m : ℕ) := by
    ac_rfl
  have hl_eq_ma : (l : ℕ) = (m : ℕ) * a := by
    -- Rewrite `lcm(m,n)` in the source Bézout form before clearing denominators.
    apply Nat.eq_of_mul_eq_mul_left hg_pos
    calc
      g * (l : ℕ) = (m : ℕ) * (n : ℕ) := by
        simp [l, g]
      _ = (m : ℕ) * (a * g) := by rw [hga]
      _ = ((m : ℕ) * a) * g := hma_assoc
      _ = g * ((m : ℕ) * a) := hma_comm
  have hl_eq_nb : (l : ℕ) = (n : ℕ) * b := by
    -- The symmetric rewrite expresses the same `lcm` through the other denominator.
    apply Nat.eq_of_mul_eq_mul_left hg_pos
    calc
      g * (l : ℕ) = (m : ℕ) * (n : ℕ) := by
        simp [l, g]
      _ = (n : ℕ) * (m : ℕ) := hmn_comm
      _ = (n : ℕ) * (b * g) := by rw [hgb]
      _ = ((n : ℕ) * b) * g := hnb_assoc
      _ = g * ((n : ℕ) * b) := hnb_comm
  have hbezout : ((1 : ℕ) : ℤ) = (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b := by
    -- Coprimality of the quotient factors turns the two admissible witnesses into a Bézout
    -- expression for the `lcm`-scaled character.
    simpa [Nat.coprime_iff_gcd_eq_one.mp hcop] using (Nat.gcd_eq_gcd_ab a b)
  have hl_mem : FDRep.schurScaledCharacter V l ∈ R̄[K](G) := by
    have hm_mem : FDRep.schurScaledCharacter V m ∈ R̄[K](G) := hm.1
    change FDRep.schurScaledCharacter V l ∈ (R̄[K](G)).toSubmodule
    have hm_eq :
        (FDRep.schurScaledCharacter V m : G → K) =
          (a : ℤ) • FDRep.schurScaledCharacter V l := by
      have ha_pos : 0 < a := by
        have hna : 0 < a * g := by
          simp [hga]
        exact Nat.pos_of_mul_pos_right hna
      have haK_ne : (a : K) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
      -- Clearing the factor `l / m` rewrites the `m`-scaled character as an integral multiple of
      -- the `lcm`-scaled character.
      ext x
      simp [FDRep.schurScaledCharacter, zsmul_eq_mul, hl_eq_ma, haK_ne, mul_left_comm, mul_comm]
    have hn_eq :
        (FDRep.schurScaledCharacter V n : G → K) =
          (b : ℤ) • FDRep.schurScaledCharacter V l := by
      have hb_pos : 0 < b := by
        have hmb : 0 < b * g := by
          simp [hgb]
        exact Nat.pos_of_mul_pos_right hmb
      have hbK_ne : (b : K) ≠ 0 := Nat.cast_ne_zero.mpr hb_pos.ne'
      -- The same rewrite holds for the `n`-scaled witness.
      ext x
      simp [FDRep.schurScaledCharacter, zsmul_eq_mul, hl_eq_nb, hbK_ne, mul_left_comm, mul_comm]
    have hm_mem' :
        ((a : ℤ) • FDRep.schurScaledCharacter V l : G → K) ∈
          (R̄[K](G)).toSubmodule := by
      simpa [hm_eq] using hm_mem
    have hn_mem' :
        ((b : ℤ) • FDRep.schurScaledCharacter V l : G → K) ∈
          (R̄[K](G)).toSubmodule := by
      simpa [hn_eq] using hn
    have hexpr :
        (FDRep.schurScaledCharacter V l : G → K) =
          Nat.gcdA a b • ((a : ℤ) • FDRep.schurScaledCharacter V l) +
            Nat.gcdB a b • ((b : ℤ) • FDRep.schurScaledCharacter V l) := by
      have hbezoutK : (1 : K) =
          (a : K) * (Nat.gcdA a b : K) + (b : K) * (Nat.gcdB a b : K) := by
        exact_mod_cast hbezout
      -- Route correction: use the source Bézout identity on the quotient factors instead of
      -- comparing packet coefficients first.
      ext x
      calc
        FDRep.schurScaledCharacter V l x = (1 : K) * (FDRep.schurScaledCharacter V l x) := by
          simp
        _ = ((a : K) * (Nat.gcdA a b : K) + (b : K) * (Nat.gcdB a b : K)) *
              (FDRep.schurScaledCharacter V l x) := by
                rw [hbezoutK]
        _ = (Nat.gcdA a b • ((a : ℤ) • FDRep.schurScaledCharacter V l) +
              Nat.gcdB a b • ((b : ℤ) • FDRep.schurScaledCharacter V l)) x := by
                simp [FDRep.schurScaledCharacter, zsmul_eq_mul, mul_add, add_mul, mul_assoc,
                  mul_left_comm, mul_comm]
    rw [hexpr]
    -- The owner `R̄[K](G)` is closed under the two integer multiples and their Bézout sum.
    exact (R̄[K](G)).toSubmodule.add_mem
      ((R̄[K](G)).toSubmodule.smul_mem _ hm_mem')
      ((R̄[K](G)).toSubmodule.smul_mem _ hn_mem')
  have hle_lcm : Nat.lcm (m : ℕ) (n : ℕ) ≤ (m : ℕ) := hm.2 l hl_mem
  have hl_eq_m : Nat.lcm (m : ℕ) (n : ℕ) = (m : ℕ) := by
    -- Maximality forces the `lcm` denominator back down to the canonical one.
    exact le_antisymm hle_lcm
      (Nat.le_of_dvd (Nat.lcm_pos m.pos n.pos) (Nat.dvd_lcm_left (m : ℕ) (n : ℕ)))
  -- Rewriting `lcm(m,n) = m` is exactly the divisibility statement `n ∣ m`.
  exact (Nat.lcm_eq_left_iff_dvd.mp hl_eq_m)

/-- Helper for Exercise 12-12.2-6: once a canonical denominator `n` is fixed, every other
source-side admissible denominator divides `n`. -/
theorem scaled_character_denominator_dvd_canonical_denominator_local
    {K1 : Type v} [Field K1] [CharZero K1]
    (ρ : Rep K1 G)
    [ρ.ρ.IsIrreducible]
    {m n : ℕ+}
    (hcanon : ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G))
    (hmax :
      ∀ d : ℕ+, ((((d : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) → d ≤ n)
    (hm : ((((m : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G)) :
    (m : ℕ) ∣ (n : ℕ) := by
  let g : ℕ := Nat.gcd (n : ℕ) (m : ℕ)
  let a : ℕ := (m : ℕ) / g
  let b : ℕ := (n : ℕ) / g
  have hg_pos : 0 < g := by
    dsimp [g]
    exact Nat.gcd_pos_of_pos_right _ m.pos
  have hga : a * g = (m : ℕ) := by
    dsimp [a, g]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_right (n : ℕ) (m : ℕ))
  have hgb : b * g = (n : ℕ) := by
    dsimp [b, g]
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left (n : ℕ) (m : ℕ))
  have hcop : Nat.Coprime a b := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hgdiv : ((m : ℕ) / g).gcd ((n : ℕ) / g) = (m : ℕ).gcd (n : ℕ) / g := by
      exact Nat.gcd_div (Nat.gcd_dvd_right (n : ℕ) (m : ℕ)) (Nat.gcd_dvd_left (n : ℕ) (m : ℕ))
    dsimp [g, a, b] at hgdiv ⊢
    simpa [Nat.gcd_comm, Nat.div_self hg_pos] using hgdiv
  let l : ℕ+ := ⟨Nat.lcm (n : ℕ) (m : ℕ), Nat.lcm_pos n.pos m.pos⟩
  have hna_assoc : (n : ℕ) * (a * g) = ((n : ℕ) * a) * g := by
    simp [Nat.mul_assoc]
  have hna_comm : ((n : ℕ) * a) * g = g * ((n : ℕ) * a) := by
    ac_rfl
  have hmb_assoc : (m : ℕ) * (b * g) = ((m : ℕ) * b) * g := by
    simp [Nat.mul_assoc]
  have hmb_comm : ((m : ℕ) * b) * g = g * ((m : ℕ) * b) := by
    ac_rfl
  have hnm_comm : (n : ℕ) * (m : ℕ) = (m : ℕ) * (n : ℕ) := by
    ac_rfl
  have hl_eq_na : (l : ℕ) = (n : ℕ) * a := by
    -- Rewrite `lcm(n,m)` so the canonical denominator remains visible.
    apply Nat.eq_of_mul_eq_mul_left hg_pos
    calc
      g * (l : ℕ) = (n : ℕ) * (m : ℕ) := by
        simp [l, g]
      _ = (n : ℕ) * (a * g) := by rw [hga]
      _ = ((n : ℕ) * a) * g := hna_assoc
      _ = g * ((n : ℕ) * a) := hna_comm
  have hl_eq_mb : (l : ℕ) = (m : ℕ) * b := by
    -- The same `lcm` rewrite through the other denominator gives the second scaling identity.
    apply Nat.eq_of_mul_eq_mul_left hg_pos
    calc
      g * (l : ℕ) = (n : ℕ) * (m : ℕ) := by
        simp [l, g]
      _ = (m : ℕ) * (n : ℕ) := hnm_comm
      _ = (m : ℕ) * (b * g) := by rw [hgb]
      _ = ((m : ℕ) * b) * g := hmb_assoc
      _ = g * ((m : ℕ) * b) := hmb_comm
  have hbezout : ((1 : ℕ) : ℤ) = (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b := by
    -- The coprime quotient factors produce the Bézout relation needed for the `lcm` witness.
    simpa [Nat.coprime_iff_gcd_eq_one.mp hcop] using (Nat.gcd_eq_gcd_ab a b)
  have hl_mem : ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G) := by
    change ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ (R̄[K1](G)).toSubmodule
    have hcanon_eq :
        ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character : G → K1) =
          (a : ℤ) • ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character) := by
      have ha_pos : 0 < a := by
        have hma : 0 < a * g := by
          simp [hga]
        exact Nat.pos_of_mul_pos_right hma
      have haK_ne : (a : K1) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
      -- Clearing the factor `l / n` rewrites the canonical scaled character through the `lcm`
      -- denominator.
      ext x
      have hlK : ((l : ℕ) : K1) = ((n : ℕ) : K1) * (a : K1) := by
        exact_mod_cast hl_eq_na
      have hmul :
          (a : K1) * ((a : K1)⁻¹ * ρ.ρ.character x) = ρ.ρ.character x := by
        field_simp [haK_ne]
      simpa [smul_eq_mul, zsmul_eq_mul, hlK, mul_assoc, mul_left_comm, mul_comm] using hmul.symm
    have hm_eq :
        ((((m : ℕ) : K1)⁻¹) • ρ.ρ.character : G → K1) =
          (b : ℤ) • ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character) := by
      have hb_pos : 0 < b := by
        have hnb : 0 < b * g := by
          simp [hgb]
        exact Nat.pos_of_mul_pos_right hnb
      have hbK_ne : (b : K1) ≠ 0 := Nat.cast_ne_zero.mpr hb_pos.ne'
      -- The same normalization holds for the other admissible denominator `m`.
      ext x
      have hlK : ((l : ℕ) : K1) = ((m : ℕ) : K1) * (b : K1) := by
        exact_mod_cast hl_eq_mb
      have hmul :
          (b : K1) * ((b : K1)⁻¹ * ρ.ρ.character x) = ρ.ρ.character x := by
        field_simp [hbK_ne]
      simpa [smul_eq_mul, zsmul_eq_mul, hlK, mul_assoc, mul_left_comm, mul_comm] using hmul.symm
    have hcanon_mem' :
        ((a : ℤ) • ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character) : G → K1) ∈
          (R̄[K1](G)).toSubmodule := by
      simpa [hcanon_eq] using hcanon
    have hm_mem' :
        ((b : ℤ) • ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character) : G → K1) ∈
          (R̄[K1](G)).toSubmodule := by
      simpa [hm_eq] using hm
    have hexpr :
        ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character : G → K1) =
          Nat.gcdA a b • ((a : ℤ) • ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character)) +
            Nat.gcdB a b • ((b : ℤ) • ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character)) := by
      have hbezoutK : (1 : K1) =
          (a : K1) * (Nat.gcdA a b : K1) + (b : K1) * (Nat.gcdB a b : K1) := by
        exact_mod_cast hbezout
      -- Route correction: the source Bézout identity closes the `lcm` witness without invoking
      -- any packet decomposition.
      ext x
      calc
        ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character) x
            = (1 : K1) * ((((l : ℕ) : K1)⁻¹) * ρ.ρ.character x) := by
                simp [smul_eq_mul]
        _ = ((a : K1) * (Nat.gcdA a b : K1) + (b : K1) * (Nat.gcdB a b : K1)) *
              ((((l : ℕ) : K1)⁻¹) * ρ.ρ.character x) := by
                rw [hbezoutK]
        _ = (Nat.gcdA a b • ((a : ℤ) • ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character)) +
              Nat.gcdB a b • ((b : ℤ) • ((((l : ℕ) : K1)⁻¹) • ρ.ρ.character))) x := by
                simp [zsmul_eq_mul, smul_eq_mul, mul_add, add_mul, mul_assoc, mul_left_comm,
                  mul_comm]
    rw [hexpr]
    -- Both admissible scaled characters lie in the owner, so the Bézout combination does as well.
    exact (R̄[K1](G)).toSubmodule.add_mem
      ((R̄[K1](G)).toSubmodule.smul_mem _ hcanon_mem')
      ((R̄[K1](G)).toSubmodule.smul_mem _ hm_mem')
  have hle_lcm : (l : ℕ) ≤ (n : ℕ) := hmax l hl_mem
  have hl_eq_n : Nat.lcm (n : ℕ) (m : ℕ) = (n : ℕ) := by
    -- Maximality forces the admissible `lcm` denominator back down to `n`.
    exact le_antisymm hle_lcm
      (Nat.le_of_dvd (Nat.lcm_pos n.pos m.pos) (Nat.dvd_lcm_left (n : ℕ) (m : ℕ)))
  -- Rewriting `lcm(n,m) = n` is equivalent to the desired divisibility `m ∣ n`.
  exact Nat.lcm_eq_left_iff_dvd.mp hl_eq_n

/-- Helper for Exercise 12-12.2-6: any source-side scaled-character witness transports to the
chosen algebraically closed extension. -/
theorem scaled_character_mem_extension_of_mem_overline_local
    {K1 : Type u} [Field K1] [CharZero K1]
    {L : Type w} [Field L] [CharZero L] [Algebra K1 L] [IsAlgClosed L]
    (ρ : Rep K1 G)
    (n : ℕ+)
    (hcanon : ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈ R̄[K1](G)) :
    ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) ∈
      overlineCharacterRingInExtension K1 L := by
  -- The extension-relative owner is defined by coefficientwise base change from the source owner.
  exact
    mem_overlineCharacterRingInExtension_of_mem_overlineCharacterRing_local
      (K := K1) (G := G) (L := L)
      ((((n : ℕ) : K1)⁻¹) • ρ.ρ.character) hcanon

/-- Helper for Exercise 12-12.2-6: after choosing a canonical denominator `n`, the `L`-valued
image of any other scaled character of the same irreducible representation is just the expected
scalar multiple of the canonical `n`-scaled image. -/
theorem map_scaled_character_eq_canonical_scaled_character_smul_local
    {K' : Type v} [Field K'] [CharZero K']
    {L : Type w} [Field L] [CharZero L] [Algebra K' L]
    (ρ : Rep K' G)
    [ρ.ρ.IsIrreducible]
    (m n : ℕ+) :
    ((IsScalarTower.toAlgHom ℤ K' L).compLeft G)
        ((((m : ℕ) : K')⁻¹) • ρ.ρ.character) =
      (((((n : ℕ) : L) * (((m : ℕ) : L)⁻¹))) •
        (((IsScalarTower.toAlgHom ℤ K' L).compLeft G)
          ((((n : ℕ) : K')⁻¹) • ρ.ρ.character))) := by
  -- Normalize both scaled characters pointwise before the later coefficient comparison in `R[L](G)`.
  ext g
  simp [smul_eq_mul, map_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 12-12.2-6: multiplying the mapped `m`-scaled character by `m` recovers
the mapped original character. -/
theorem zsmul_mapped_scaled_character_eq_map_character_local
    {K' : Type v} [Field K'] [CharZero K']
    {L : Type w} [Field L] [CharZero L] [Algebra K' L]
    (ρ : Rep K' G)
    (m : ℕ+) :
    ((m : ℤ) •
      (((IsScalarTower.toAlgHom ℤ K' L).compLeft G)
        ((((m : ℕ) : K')⁻¹) • ρ.ρ.character)) : G → L) =
      ((IsScalarTower.toAlgHom ℤ K' L).compLeft G) ρ.ρ.character := by
  -- This is the integral form used later for coefficient comparison inside `R[L](G)`.
  ext g
  have hm_ne : (((m : ℕ) : L)) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  simp [zsmul_eq_mul, smul_eq_mul, map_mul, mul_assoc, mul_left_comm, mul_comm, hm_ne]

/-- Helper for Exercise 12-12.2-6: if the mapped `m`-scaled character lies in `R[L](G)`, then so
does the mapped original character obtained by clearing the denominator `m`. -/
theorem mapped_character_mem_characterRing_of_scaled_mem_local
    {K' : Type v} [Field K'] [CharZero K']
    {L : Type w} [Field L] [CharZero L] [Algebra K' L]
    (ρ : Rep K' G)
    (m : ℕ+)
    (hscaled :
      ((IsScalarTower.toAlgHom ℤ K' L).compLeft G)
          ((((m : ℕ) : K')⁻¹) • ρ.ρ.character) ∈
        R[L](G)) :
    ((IsScalarTower.toAlgHom ℤ K' L).compLeft G) ρ.ρ.character ∈ R[L](G) := by
  -- Clear the denominator inside the character ring before later coefficient comparisons.
  simpa [zsmul_mapped_scaled_character_eq_map_character_local (G := G) (ρ := ρ) (m := m)] using
    Submodule.smul_mem (R[L](G)).toSubmodule (m : ℤ) hscaled

/-- Helper for Exercise 12-12.2-6: over an algebraically closed field, the honest and overline
character rings coincide because an algebraic-closure witness may be evaluated back in the base
field. -/
theorem characterRing_eq_overlineCharacterRing_of_algClosed_local
    {L : Type w} [Field L] [CharZero L] [IsAlgClosed L] :
    R[L](G) = R̄[L](G) := by
  apply le_antisymm
  · -- Honest `L`-characters are always algebraic over `L`.
    exact characterRingOverField_le_overlineCharacterRing L G
  · intro χ hχ
    let ι : AlgebraicClosure L →ₐ[L] L := IsAlgClosed.lift (R := L)
    let ιZ : AlgebraicClosure L →ₐ[ℤ] L := ι.restrictScalars ℤ
    have hχ_alg :
        ((IsScalarTower.toAlgHom ℤ L (AlgebraicClosure L)).compLeft G) χ ∈
          R[AlgebraicClosure L](G) :=
      (mem_overlineCharacterRingInExtension_iff L (AlgebraicClosure L) χ).1 hχ
    have hχ_lifted :
        (ιZ.compLeft G)
            (((IsScalarTower.toAlgHom ℤ L (AlgebraicClosure L)).compLeft G) χ) ∈
          R[L](G) :=
      map_mem_characterRingOverField_local
        (F := AlgebraicClosure L) (E := L) (G := G) (f := ιZ)
        (((IsScalarTower.toAlgHom ℤ L (AlgebraicClosure L)).compLeft G) χ) hχ_alg
    -- Evaluating the algebraic-closure witness through `ι` returns the original `L`-valued class
    -- function because `ι` is an `L`-algebra map.
    convert hχ_lifted using 1
    ext g
    simpa [ιZ] using (ι.commutes (χ g))

end FieldPart

end Representation
