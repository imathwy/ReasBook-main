import LinearRepresentations_Serre_1977.Chap10.Lemma_10_10_3_2
import LinearRepresentations_Serre_1977.Chap01.Definition_1_1_2_1
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Exercise 10-10.3-5.

Serre asks to prove the congruence `χ(x) ≡ χ(x_{p'}) (mod 𝔭)` for `χ` a character of `G`,
`x ∈ G`, `x_{p'}` the `p'`-component of `x`, and `𝔭` a prime ideal above `p` in the ring `A` of
algebraic integers — and then (part 2) to show that this congruence is *false in general* if the
prime ideal `𝔭` is replaced by the principal ideal `(p)A`.

* part (1) is the content of §10.3 Lemma 7, already owned by the chapter theorem
  `integerValued_tensorCharacter_modEq_pRegularComponent` (in `Serre.Chap10.Lemma_10_10_3_2`):
  for an integer-valued tensor character the chosen integer representatives of `χ(x)` and
  `χ(x_{p'})` are congruent modulo `p`, which is exactly the congruence modulo the prime `𝔭`
  specialised to integer values.
* part (2) is the counterexample to the stronger modulus `(p)A`. -/

open Representation
open scoped Representation IsLocalization

/- Exercise 10-10.3-5 (1): the congruence `χ(x) ≡ χ(x_{p'})` modulo the prime ideal above `p`,
owned by the chapter theorem `integerValued_tensorCharacter_modEq_pRegularComponent`. -/
recall integerValued_tensorCharacter_modEq_pRegularComponent

namespace Exercise_10_10_3_5

noncomputable section

-- Source/core/bridge triage for the counterexample data:
-- * source-facing: Serre's witness `G = ⟨x⟩` cyclic of order `p`, `χ` a faithful degree-1 character
--   and `x` a generator, so that `χ(x) = ζ_p` and `χ(x_{p'}) = χ(1) = 1`.
-- * core/canonical: the concrete realization `G = μ₃ ⊆ ℂˣ` (cube roots of unity) and the ring of
--   algebraic integers `A = integralClosure ℤ ℂ`; the prime is `p = 3` (the smallest prime for
--   which `ζ_p - 1` fails to be divisible by `p`, since `p - 1 ≥ 2`).
-- * bridge/view: the realized tensor character `1 ⊗ ψ ∈ A ⊗ R(G)` whose values are read through the
--   canonical coercion to `G → ℂ`.

/-- Helper for Exercise 10-10.3-5: a fixed primitive complex cube root of unity `ζ`. -/
def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- Helper for Exercise 10-10.3-5: `ζ` is a primitive cube root of unity. -/
theorem zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- Helper for Exercise 10-10.3-5: the minimal relation `ζ² + ζ + 1 = 0`, obtained from
`ζ³ = 1` and `ζ ≠ 1` through the factorisation `ζ³ - 1 = (ζ - 1)(ζ² + ζ + 1)`. -/
theorem zeta_sq_add_zeta_add_one : zeta ^ 2 + zeta + 1 = 0 := by
  have h3 : zeta ^ 3 = 1 := zeta_isPrimitiveRoot.pow_eq_one
  have hne : zeta ≠ 1 := zeta_isPrimitiveRoot.ne_one (by norm_num : 1 < 3)
  -- `ζ³ - 1 = (ζ - 1)(ζ² + ζ + 1)`, and the first factor is nonzero.
  have hfact : (zeta - 1) * (zeta ^ 2 + zeta + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp hfact with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- Helper for Exercise 10-10.3-5: `ζ` packaged as a complex unit. -/
def zetaUnit : ℂˣ := (zeta_isPrimitiveRoot.isUnit (by norm_num)).unit

/-- Helper for Exercise 10-10.3-5: the underlying complex number of `zetaUnit` is `ζ`. -/
theorem zetaUnit_coe : (zetaUnit : ℂ) = zeta := IsUnit.unit_spec _

/-- Helper for Exercise 10-10.3-5: `zetaUnit` is a cube root of unity. -/
theorem zetaUnit_mem : zetaUnit ∈ rootsOfUnity 3 ℂ := by
  rw [mem_rootsOfUnity]
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.val_one, zetaUnit_coe]
  exact zeta_isPrimitiveRoot.pow_eq_one

/-- Helper for Exercise 10-10.3-5: the witness group `G`, the cyclic group of order `3` realized as
the cube roots of unity in `ℂ`. -/
abbrev G : Type := ↥(rootsOfUnity 3 ℂ)

/-- Helper for Exercise 10-10.3-5: the chosen generator (a primitive cube root). -/
def x₀ : G := ⟨zetaUnit, zetaUnit_mem⟩

/-- Helper for Exercise 10-10.3-5: the faithful degree-one character of `G`, the inclusion
`G ↪ ℂˣ`. -/
def lc : G →* ℂˣ := (rootsOfUnity 3 ℂ).subtype

/-- Helper for Exercise 10-10.3-5: the ordinary character of `lc`, as an element of `R(G)`. A
one-dimensional representation is finite-dimensional, hence its character lies in the integral
character ring `R(G)`. -/
def psi : R(G) :=
  ⟨lc.toRepresentation.character,
    Representation.rep_character_mem_characterRingOverField (Rep.of lc.toRepresentation)⟩

/-- Helper for Exercise 10-10.3-5: the witness ring `A`, the ring of algebraic integers realized as
the integral closure of `ℤ` in `ℂ`. -/
abbrev Aι : Type := ↥(integralClosure ℤ ℂ)

/-- Helper for Exercise 10-10.3-5: the witness tensor character `χ = 1 ⊗ ψ ∈ A ⊗ R(G)`. -/
def chi : Aι ⊗R(G) := (1 : Aι) ⊗ₜ[ℤ] psi

/-- Helper for Exercise 10-10.3-5: `χ(x₀) = ζ`. -/
theorem chi_apply_x₀ : (chi : G → ℂ) x₀ = zeta := by
  -- `χ = 1 ⊗ ψ` coerces to the function `1 • ψ = ψ`, whose value at `x₀` is the linear character.
  simp only [chi, coe_tmul, one_smul, Pi.smul_apply]
  show (psi : G → ℂ) x₀ = zeta
  simp only [psi, MonoidHom.toRepresentation_character_apply]
  show (lc x₀ : ℂ) = zeta
  simp [lc, x₀, zetaUnit_coe]

/-- Helper for Exercise 10-10.3-5: `χ(1) = 1`. -/
theorem chi_apply_one : (chi : G → ℂ) 1 = 1 := by
  simp only [chi, coe_tmul, one_smul, Pi.smul_apply]
  show (psi : G → ℂ) 1 = 1
  simp only [psi, MonoidHom.toRepresentation_character_apply, map_one, Units.val_one]

local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- Helper for Exercise 10-10.3-5: the generator `x₀` has order `3`. -/
theorem orderOf_x₀ : orderOf x₀ = 3 := by
  have hou : orderOf zetaUnit = 3 := by
    rw [← orderOf_units, zetaUnit_coe]; exact zeta_isPrimitiveRoot.eq_orderOf.symm
  -- The subgroup inclusion is injective, so it preserves the order of `x₀`.
  have h : orderOf x₀ = orderOf zetaUnit := by
    rw [← orderOf_injective (rootsOfUnity 3 ℂ).subtype (Subgroup.subtype_injective _) x₀]; rfl
  rw [h, hou]

/-- Helper for Exercise 10-10.3-5: the `3'`-component of `x₀` is trivial, because `x₀` is a
`3`-element; hence `x₀ = (x₀)·1` is the canonical `3`-component decomposition and uniqueness forces
`pRegularComponent 3 x₀ = 1`. -/
theorem pRegularComponent_x₀ : pRegularComponent 3 x₀ = 1 := by
  have hpe : IsPElement 3 x₀ := ⟨1, by rw [orderOf_x₀]; norm_num⟩
  have hdec : IsPComponentDecomposition 3 x₀ x₀ 1 :=
    ⟨hpe, isPRegular_one 3, Commute.one_right x₀, mul_one x₀⟩
  exact ((p_component_decomposition_unique x₀ x₀ 1 hdec).2).symm

/-- Helper for Exercise 10-10.3-5: the heart of the counterexample. `ζ - 1` is **not** in the
complex image of the principal ideal `(3)A` (the literal image set `algebraMap A ℂ '' (3)A`).
Indeed, were `ζ - 1 = 3·s` with `s` the image of an algebraic integer, then substituting
`ζ = 3s + 1` into `ζ² + ζ + 1 = 0` gives `3s² + 3s + 1 = 0`, i.e. `3·(s² + s) = -1`. But `s² + s`
is an algebraic integer equal to the rational `-1/3`, and a rational algebraic integer must be a
genuine integer — impossible since `3 ∤ 1`. -/
theorem zeta_sub_one_not_mem_image :
    zeta - 1 ∉ (algebraMap Aι ℂ) '' (Ideal.span ({(3 : Aι)} : Set Aι) : Set Aι) := by
  rintro ⟨a, ha, hae⟩
  -- `a ∈ (3)` means `a = b·3` for some algebraic integer `b`; set `s := image of b`.
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
  set s : ℂ := algebraMap Aι ℂ b with hs
  have hsval : zeta - 1 = 3 * s := by
    have hmul : algebraMap Aι ℂ a = s * (3 : ℂ) := by
      rw [← hb]; simp only [map_mul, map_ofNat, hs]
    rw [← hae, hmul]; ring
  -- Substitute `ζ = 3s + 1` into `ζ² + ζ + 1 = 0`.
  have hzeq : zeta = 3 * s + 1 := by linear_combination hsval
  have hcubic : 3 * s ^ 2 + 3 * s + 1 = 0 := by
    have hr := zeta_sq_add_zeta_add_one
    rw [hzeq] at hr
    linear_combination (1 / 3 : ℂ) * hr
  -- Hence `3·(s² + s) = -1`, so `s² + s = -1/3` is a rational algebraic integer.
  have h3t : 3 * (s ^ 2 + s) = -1 := by linear_combination hcubic
  have hs_int : IsIntegral ℤ s :=
    (IsIntegralClosure.isIntegral_iff (A := Aι) (R := ℤ) (B := ℂ)).2 ⟨b, rfl⟩
  have ht_int : IsIntegral ℤ (s ^ 2 + s) := (hs_int.pow 2).add hs_int
  have hpC : (3 : ℂ) ≠ 0 := by norm_num
  have hQeq : algebraMap ℚ ℂ ((-1 : ℚ) / 3) = s ^ 2 + s := by
    have hcast : algebraMap ℚ ℂ ((-1 : ℚ) / 3) = (-1 : ℂ) / 3 := by norm_num [Rat.cast_def]
    rw [hcast, eq_comm, eq_div_iff hpC]; linear_combination h3t
  have hintQ : IsIntegral ℤ (((-1 : ℚ)) / 3) := by
    apply (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp
    rw [hQeq]; exact ht_int
  -- A rational integral over `ℤ` is an integer, contradicting `3 ∤ 1`.
  obtain ⟨z, hz⟩ : ∃ z : ℤ, algebraMap ℤ ℚ z = ((-1 : ℚ) / 3) := by
    simpa [IsLocalization.IsInteger] using UniqueFactorizationMonoid.integer_of_integral hintQ
  have hzq : (z : ℚ) = (-1) / 3 := by simpa using hz
  have h3z : (3 : ℚ) * z = -1 := by rw [hzq]; ring
  have hint : (3 : ℤ) * z = -1 := by exact_mod_cast h3z
  omega

end

end Exercise_10_10_3_5

-- Faithfulness note on the conclusion.  Serre's statement is `χ(x) ≢ χ(x_r) (mod pA)`, i.e. the
-- value-difference is not a member of the principal ideal `(p)A` of the algebraic integers `A`.
-- Because the values `χ(x)` live in the field `ℂ` (through the canonical coercion
-- `A ⊗ R(G) → (G → ℂ)`), "membership in `(p)A`" must be expressed as membership in the complex
-- *image* of that ideal, `algebraMap A ℂ '' (p)A` — exactly the "complex image of `(p)A`" named in
-- the docstring below.  (The generated complex *ideal* `(Ideal.span {(p:A)}).map (algebraMap A ℂ)`
-- would be all of `ℂ`, since `ℂ` is a field, so it cannot express Serre's congruence; the faithful
-- object is the image set.)
/-- Exercise 10-10.3-5 (2): the congruence of part (1) is *false in general* when the prime ideal
`𝔭` above `p` is replaced by the principal ideal `(p)A` generated by `p` in the ring `A` of
algebraic integers.  Concretely there exist a prime `p`, a finite group `G`, the ring `A` of
algebraic integers (the integral closure of `ℤ` in `ℂ`), a tensor character `χ : A ⊗R(G)` and an
element `x : G` for which the difference of values `χ(x) - χ(x_{p'})` does **not** lie in the
complex image of `(p)A`.  (The standard witness is `G` cyclic of order `p` with `χ` a faithful
character and `x` a generator: then `χ(x) = ζ_p`, `χ(x_{p'}) = χ(1) = 1`, and `ζ_p - 1` lies in the
prime `(1 - ζ_p)` but not in `(p)`, since `1 - ζ_p` has `𝔭`-valuation `1` while `p` has
valuation `p - 1`.) -/
theorem exists_tensorCharacter_value_sub_pRegularComponent_not_mem_pIdeal :
    ∃ (p : ℕ) (_ : Fact p.Prime) (G : Type) (_ : Group G) (_ : Finite G)
      (A : Type) (_ : CommRing A) (_ : Algebra A ℂ) (_ : IsIntegralClosure A ℤ ℂ)
      (χ : A ⊗R(G)) (x : G),
      (χ x - χ (pRegularComponent p x)) ∉
        (algebraMap A ℂ) '' (Ideal.span ({(p : A)} : Set A) : Set A) := by
  -- Witnesses: `p = 3`, `G = μ₃`, `A = integralClosure ℤ ℂ`, `χ = 1 ⊗ ψ`, `x = x₀`.
  refine ⟨3, ⟨by norm_num⟩, Exercise_10_10_3_5.G, inferInstance, inferInstance,
    Exercise_10_10_3_5.Aι, inferInstance, inferInstance, inferInstance,
    Exercise_10_10_3_5.chi, Exercise_10_10_3_5.x₀, ?_⟩
  -- The value-difference equals `ζ - 1`.
  have hdiff :
      (Exercise_10_10_3_5.chi Exercise_10_10_3_5.x₀ -
          Exercise_10_10_3_5.chi (pRegularComponent 3 Exercise_10_10_3_5.x₀)) =
        Exercise_10_10_3_5.zeta - 1 := by
    rw [Exercise_10_10_3_5.pRegularComponent_x₀, Exercise_10_10_3_5.chi_apply_x₀,
      Exercise_10_10_3_5.chi_apply_one]
  rw [hdiff]
  exact Exercise_10_10_3_5.zeta_sub_one_not_mem_image
