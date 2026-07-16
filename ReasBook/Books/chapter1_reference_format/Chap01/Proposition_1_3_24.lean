import Mathlib
import chapter1_reference_format.Chap01.Remark_1_3_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial
open Polynomial
open AdjoinRoot

variable {p : ℕ} [Fact p.Prime]

/-- Helper for Proposition 1.3.24: every element of the reduction kernel is killed by a
`p`-power. -/
lemma pow_unit_reduction_kernel_pow_eq_one
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+)
    (x : (powUnitReduction P e).ker) :
    x ^ (p ^ (e : ℕ)) = 1 := by
  let u : (AdjoinRoot (P ^ (e : ℕ)))ˣ := x
  -- Write the kernel element as a polynomial class.
  obtain ⟨Q, hQ⟩ :=
    AdjoinRoot.mk_surjective (g := P ^ (e : ℕ))
      ((u : (AdjoinRoot (P ^ (e : ℕ)))ˣ) : AdjoinRoot (P ^ (e : ℕ)))
  have hxred : (powReduction P e) (AdjoinRoot.mk (P ^ (e : ℕ)) Q) = 1 := by
    rw [hQ]
    exact congrArg Units.val x.2
  have hmk_one : AdjoinRoot.mk P Q = 1 := by
    rw [powReduction, AdjoinRoot.coe_algHomOfDvd, AdjoinRoot.liftAlgHom_mk] at hxred
    change aeval (AdjoinRoot.root P) Q = 1 at hxred
    simpa [AdjoinRoot.aeval_eq] using hxred
  have hdiv : P ∣ Q - 1 := by
    apply (AdjoinRoot.mk_eq_mk).mp
    rw [hmk_one]
    simp
  obtain ⟨T, hT⟩ := hdiv
  have hQeq : Q = 1 + P * T := by
    calc
      Q = P * T + 1 := eq_add_of_sub_eq hT
      _ = 1 + P * T := by rw [add_comm]
  have hx_eq :
      ((u : (AdjoinRoot (P ^ (e : ℕ)))ˣ) : AdjoinRoot (P ^ (e : ℕ))) =
        1 + AdjoinRoot.mk (P ^ (e : ℕ)) (P * T) := by
    rw [show
        ((u : (AdjoinRoot (P ^ (e : ℕ)))ˣ) : AdjoinRoot (P ^ (e : ℕ))) =
          AdjoinRoot.mk (P ^ (e : ℕ)) Q by
        exact hQ.symm]
    rw [hQeq]
    simp [AdjoinRoot.mk, map_add]
  let hp : Nat.Prime p := Fact.out
  have hle : (e : ℕ) ≤ p ^ (e : ℕ) := by
    exact
      (Nat.lt_two_pow_self : (e : ℕ) < 2 ^ (e : ℕ)).le.trans
        (Nat.pow_le_pow_left hp.two_le _)
  have hnil :
      (AdjoinRoot.mk (P ^ (e : ℕ)) (P * T) : AdjoinRoot (P ^ (e : ℕ))) ^ (p ^ (e : ℕ)) = 0 := by
    change AdjoinRoot.mk (P ^ (e : ℕ)) ((P * T) ^ (p ^ (e : ℕ))) = 0
    rw [mul_pow]
    exact (AdjoinRoot.mk_eq_zero).2 <|
      dvd_mul_of_dvd_left (pow_dvd_pow P hle) (T ^ (p ^ (e : ℕ)))
  have hnat : (P ^ (e : ℕ)).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_ne_zero e.ne_zero hP.natDegree_pos.ne'
  have hdeg : (P ^ (e : ℕ)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (pow_ne_zero _ hP.ne_zero)]
    exact_mod_cast hnat
  haveI : CharP (AdjoinRoot (P ^ (e : ℕ))) p :=
    charP_of_injective_algebraMap (AdjoinRoot.coe_injective hdeg) p
  -- The nilpotent part disappears after a large enough `p`-power.
  apply Subtype.ext
  apply Units.ext
  change
    (((u : (AdjoinRoot (P ^ (e : ℕ)))ˣ) : AdjoinRoot (P ^ (e : ℕ))) ^ (p ^ (e : ℕ))) = 1
  rw [hx_eq, add_pow_char_pow, one_pow, hnil, add_zero]

/-- Helper for Proposition 1.3.24: a `k`-th root modulo `P^e` exists exactly when a `k`-th root
exists after reduction modulo `P`. -/
lemma unit_exists_pow_iff_reduction_exists_pow
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) (k : ℕ+)
    (hk : (k : ℕ) ∣ Nat.card ((AdjoinRoot P)ˣ))
    (g : (AdjoinRoot (P ^ (e : ℕ)))ˣ) :
    (∃ x : (AdjoinRoot (P ^ (e : ℕ)))ˣ, x ^ (k : ℕ) = g) ↔
      ∃ y : (AdjoinRoot P)ˣ, y ^ (k : ℕ) = powUnitReduction P e g := by
  have hpk : ¬ p ∣ (k : ℕ) := by
    intro hk'
    exact residue_field_unit_card_not_dvd_char hP (dvd_trans hk' hk)
  constructor
  · rintro ⟨x, rfl⟩
    -- Reduction preserves the `k`-th power equation.
    refine ⟨powUnitReduction P e x, ?_⟩
    simp [powUnitReduction]
  · rintro ⟨y, hy⟩
    -- Lift a residue-field root, then correct the lift inside the reduction kernel.
    obtain ⟨z, hz⟩ := pow_unit_reduction_surjective hP e y
    let δ : (powUnitReduction P e).ker := by
      refine ⟨z ^ (k : ℕ) * g⁻¹, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hz, hy, mul_inv_cancel]
    obtain ⟨w, hw⟩ : ∃ w : (powUnitReduction P e).ker, w ^ (k : ℕ) = δ := by
      refine ⟨(pow_unit_reduction_ker_isPGroup hP e).powEquiv' hpk |>.symm δ, ?_⟩
      simpa using ((pow_unit_reduction_ker_isPGroup hP e).powEquiv' hpk).apply_symm_apply δ
    refine ⟨((w : (powUnitReduction P e).ker) : (AdjoinRoot (P ^ (e : ℕ)))ˣ)⁻¹ * z, ?_⟩
    have hw' :
        (((w : (powUnitReduction P e).ker) : (AdjoinRoot (P ^ (e : ℕ)))ˣ) ^ (k : ℕ)) =
          (δ : (AdjoinRoot (P ^ (e : ℕ)))ˣ) := by
      exact congrArg
        (fun t : (powUnitReduction P e).ker =>
          ((t : (powUnitReduction P e).ker) : (AdjoinRoot (P ^ (e : ℕ)))ˣ)) hw
    -- The correction term cancels the kernel error.
    rw [mul_pow, inv_pow, hw']
    change ((δ : (AdjoinRoot (P ^ (e : ℕ)))ˣ)⁻¹ * z ^ (k : ℕ)) = g
    change ((z ^ (k : ℕ) * g⁻¹)⁻¹ * z ^ (k : ℕ)) = g
    group

/-- Helper for Proposition 1.3.24: in the finite field `𝔽_p[X]/(P)`, an element is a `k`-th power
exactly when its complementary power is `1`. -/
lemma residue_field_unit_exists_pow_iff_pow_div_eq_one
    {P : (ZMod p)[X]} (hP : Irreducible P) (k : ℕ+)
    (hk : (k : ℕ) ∣ Nat.card ((AdjoinRoot P)ˣ))
    (u : (AdjoinRoot P)ˣ) :
    (∃ y : (AdjoinRoot P)ˣ, y ^ (k : ℕ) = u) ↔
      u ^ (Nat.card ((AdjoinRoot P)ˣ) / (k : ℕ)) = 1 := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Module.Finite (ZMod p) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  letI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod p)
  let G := (AdjoinRoot P)ˣ
  let H : Subgroup G := (powMonoidHom (k : ℕ)).range
  let K : Subgroup G := (powMonoidHom (Nat.card G / (k : ℕ))).ker
  have hHK : H ≤ K := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    -- Every `k`-th power lands in the kernel of the complementary power map.
    change (y ^ (k : ℕ)) ^ (Nat.card G / (k : ℕ)) = 1
    rw [← pow_mul, Nat.mul_div_cancel' hk, pow_card_eq_one']
  have hcardH : Nat.card H = Nat.card G / (k : ℕ) := by
    simpa [G, Nat.gcd_eq_right hk] using
      (IsCyclic.card_powMonoidHom_range (G := G) (k : ℕ))
  have hcardK : Nat.card K = Nat.card G / (k : ℕ) := by
    have hk' : Nat.card G / (k : ℕ) ∣ Nat.card G := Nat.div_dvd_of_dvd hk
    simpa [G, Nat.gcd_comm, Nat.gcd_eq_right hk'] using
      (IsCyclic.card_powMonoidHom_ker (G := G) (Nat.card G / (k : ℕ)))
  have hEq : H = K := Subgroup.eq_of_le_of_card_ge hHK (by rw [hcardH, hcardK])
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y ^ (k : ℕ) ∈ H := ⟨y, rfl⟩
    simpa [hEq] using hHK hy
  · intro hu
    have hu' : u ∈ K := by
      simpa using hu
    have hu'' : u ∈ H := by
      simpa [hEq] using hu'
    rcases hu'' with ⟨y, hy⟩
    exact ⟨y, hy⟩

/-- Helper for Proposition 1.3.24: reduction identifies the upstairs and downstairs kernels of the
`k`-th power maps. -/
lemma pow_kernel_reduction_bijective
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) (k : ℕ+)
    (hk : (k : ℕ) ∣ Nat.card ((AdjoinRoot P)ˣ)) :
    let G1 := (AdjoinRoot P)ˣ
    let Ge := (AdjoinRoot (P ^ (e : ℕ)))ˣ
    let Kdom : Subgroup Ge := (powMonoidHom (k : ℕ)).ker
    let Kcod : Subgroup G1 := (powMonoidHom (k : ℕ)).ker
    let ψ : Kdom → Kcod := fun x ↦
      ⟨powUnitReduction P e (x : Ge),
        by simpa [MonoidHom.mem_ker, map_pow] using congrArg (powUnitReduction P e) x.2⟩
    Function.Bijective ψ := by
  let G1 := (AdjoinRoot P)ˣ
  let Ge := (AdjoinRoot (P ^ (e : ℕ)))ˣ
  let Kdom : Subgroup Ge := (powMonoidHom (k : ℕ)).ker
  let Kcod : Subgroup G1 := (powMonoidHom (k : ℕ)).ker
  let ψ : Kdom → Kcod := fun x ↦
    ⟨powUnitReduction P e (x : Ge),
      by simpa [MonoidHom.mem_ker, map_pow] using congrArg (powUnitReduction P e) x.2⟩
  have hpk : ¬ p ∣ (k : ℕ) := by
    intro hk'
    exact residue_field_unit_card_not_dvd_char hP (dvd_trans hk' hk)
  change Function.Bijective ψ
  constructor
  · intro a b hab
    -- Two lifts of the same downstairs `k`-torsion element differ by a kernel element whose
    -- `k`-th power is `1`, hence by bijectivity on the `p`-group kernel they are equal.
    have hab' : powUnitReduction P e ((a : Kdom) : Ge) = powUnitReduction P e ((b : Kdom) : Ge) :=
      congrArg (fun t : Kcod => ((t : Kcod) : G1)) hab
    have ha1 : (((a : Kdom) : Ge) ^ (k : ℕ)) = 1 := by
      change (powMonoidHom (k : ℕ)) ((((a : Kdom) : Ge) : Ge)) = 1
      exact (a : Kdom).2
    have hb1 : (((b : Kdom) : Ge) ^ (k : ℕ)) = 1 := by
      change (powMonoidHom (k : ℕ)) ((((b : Kdom) : Ge) : Ge)) = 1
      exact (b : Kdom).2
    let δ : (powUnitReduction P e).ker := by
      refine ⟨(((a : Kdom) : Ge) * (((b : Kdom) : Ge)⁻¹)), ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab', mul_inv_cancel]
    have hδpow : δ ^ (k : ℕ) = 1 := by
      apply Subtype.ext
      change ((((a : Kdom) : Ge) * (((b : Kdom) : Ge)⁻¹)) ^ (k : ℕ)) = (1 : Ge)
      rw [mul_pow, inv_pow, ha1, hb1, inv_one, mul_one]
    have hδone : δ = 1 := by
      apply ((pow_unit_reduction_ker_isPGroup hP e).powEquiv' hpk).injective
      simpa using hδpow
    have hmul : (((a : Kdom) : Ge) * (((b : Kdom) : Ge)⁻¹)) = 1 :=
      congrArg
        (fun t : (powUnitReduction P e).ker =>
          ((t : (powUnitReduction P e).ker) : Ge)) hδone
    apply Subtype.ext
    exact mul_inv_eq_one.mp hmul
  · intro y
    -- Lift the downstairs `k`-torsion element and correct the `k`-power error inside the kernel.
    have hy1 : (((y : Kcod) : G1) ^ (k : ℕ)) = 1 := by
      change (powMonoidHom (k : ℕ)) ((((y : Kcod) : G1) : G1)) = 1
      exact (y : Kcod).2
    obtain ⟨z, hz⟩ := pow_unit_reduction_surjective hP e ((y : Kcod) : G1)
    let δ : (powUnitReduction P e).ker := by
      refine ⟨z ^ (k : ℕ), ?_⟩
      rw [MonoidHom.mem_ker, map_pow, hz, hy1]
    obtain ⟨w, hw⟩ : ∃ w : (powUnitReduction P e).ker, w ^ (k : ℕ) = δ := by
      refine ⟨(pow_unit_reduction_ker_isPGroup hP e).powEquiv' hpk |>.symm δ, ?_⟩
      simpa using ((pow_unit_reduction_ker_isPGroup hP e).powEquiv' hpk).apply_symm_apply δ
    refine ⟨⟨(((w : (powUnitReduction P e).ker) : Ge)⁻¹ * z), ?_⟩, ?_⟩
    · have hw' : ((((w : (powUnitReduction P e).ker) : Ge)) ^ (k : ℕ)) = (δ : Ge) := by
        exact congrArg
          (fun t : (powUnitReduction P e).ker =>
            ((t : (powUnitReduction P e).ker) : Ge)) hw
      change (powMonoidHom (k : ℕ)) ((((w : (powUnitReduction P e).ker) : Ge)⁻¹ * z) : Ge) = 1
      rw [powMonoidHom_apply]
      rw [mul_pow, inv_pow, hw']
      change (((δ : Ge)⁻¹ * z ^ (k : ℕ))) = (1 : Ge)
      change (((z ^ (k : ℕ))⁻¹ * z ^ (k : ℕ))) = (1 : Ge)
      exact inv_mul_cancel _
    · apply Subtype.ext
      change (powUnitReduction P e) ((((w : (powUnitReduction P e).ker) : Ge)⁻¹) * z) =
        ((y : Kcod) : G1)
      rw [map_mul, map_inv,
        show powUnitReduction P e (((w : (powUnitReduction P e).ker) : Ge)) = 1 by
          exact (w : (powUnitReduction P e).ker).2,
        inv_one, one_mul, hz]

/-- Helper for Proposition 1.3.24: the upstairs `k`-th power subgroup has cardinality
`|(𝔽_p[X]/(P^e))ˣ| / k`. -/
lemma kth_power_range_card_via_reduction
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) (k : ℕ+)
    (hk : (k : ℕ) ∣ Nat.card ((AdjoinRoot P)ˣ)) :
    Nat.card ((powMonoidHom (k : ℕ) : (AdjoinRoot (P ^ (e : ℕ)))ˣ →* _).range) =
      Nat.card ((AdjoinRoot (P ^ (e : ℕ)))ˣ) / (k : ℕ) := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Module.Finite (ZMod p) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  letI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod p)
  let G1 := (AdjoinRoot P)ˣ
  let Ge := (AdjoinRoot (P ^ (e : ℕ)))ˣ
  let Kdom : Subgroup Ge := (powMonoidHom (k : ℕ)).ker
  let Kcod : Subgroup G1 := (powMonoidHom (k : ℕ)).ker
  let ψ : Kdom → Kcod := fun x ↦
    ⟨powUnitReduction P e (x : Ge),
      by simpa [MonoidHom.mem_ker, map_pow] using congrArg (powUnitReduction P e) x.2⟩
  have hbij : Function.Bijective ψ := by
    simpa [G1, Ge, Kdom, Kcod, ψ] using pow_kernel_reduction_bijective hP e k hk
  have hcardKdom : Nat.card Kdom = (k : ℕ) := by
    have hcardKcod : Nat.card Kcod = (k : ℕ) := by
      simpa [G1, Nat.gcd_comm, Nat.gcd_eq_right hk] using
        (IsCyclic.card_powMonoidHom_ker (G := G1) (k : ℕ))
    exact Nat.card_congr (Equiv.ofBijective ψ hbij) ▸ hcardKcod
  -- Convert the usual `|H| * [G : H] = |G|` identity into the range-counting formula.
  have hmul0 :
      Nat.card ((powMonoidHom (k : ℕ) : Ge →* Ge).range) *
        ((powMonoidHom (k : ℕ) : Ge →* Ge).range.index) = Nat.card Ge := by
    exact Subgroup.card_mul_index (H := (powMonoidHom (k : ℕ) : Ge →* Ge).range)
  have hmul :
      Nat.card ((powMonoidHom (k : ℕ) : Ge →* Ge).range) * Nat.card Kdom = Nat.card Ge := by
    rw [Subgroup.index_range] at hmul0
    simpa [Kdom] using hmul0
  have hkGe : (k : ℕ) ∣ Nat.card Ge := by
    refine ⟨Nat.card ((powMonoidHom (k : ℕ) : Ge →* Ge).range), ?_⟩
    simpa [hcardKdom, mul_comm] using hmul.symm
  exact Nat.mul_right_cancel k.2 <| by
    change Nat.card ((powMonoidHom (k : ℕ) : Ge →* Ge).range) * (k : ℕ) =
      (Nat.card Ge / (k : ℕ)) * (k : ℕ)
    rw [Nat.div_mul_cancel hkGe]
    simpa [hcardKdom] using hmul

/-- Proposition 1.3.24: for an irreducible polynomial `P ∈ 𝔽_p[X]` and a positive exponent `e`,
if `k` divides the order of the multiplicative group of the residue field `𝔽_p[X] / (P)`, then a
unit class modulo `P^e` is a `k`-th power modulo `P^e` exactly when its reduction modulo `P`
raises to `1` after exponentiation by `|(𝔽_p[X] / (P))ˣ| / k`. -/
-- Proof sketch: reduce the equation from `(𝔽_p[X] / (P^e))ˣ` to `(𝔽_p[X] / (P))ˣ`; the kernel of
-- the reduction map is a finite `p`-group, and since `k ∣ (|P| - 1)` we have `gcd(k, p) = 1`, so
-- taking `k`-th powers is an automorphism on that kernel. The residue-field criterion then follows
-- from the cyclicity of `((𝔽_p[X] / (P))ˣ)`.
theorem polynomial_prime_power_unit_exists_pow_iff_reduction_pow_eq_one
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) (k : ℕ+)
    (hk : (k : ℕ) ∣ Nat.card ((AdjoinRoot P)ˣ))
    (g : (AdjoinRoot (P ^ (e : ℕ)))ˣ) :
    (∃ x : (AdjoinRoot (P ^ (e : ℕ)))ˣ, x ^ (k : ℕ) = g) ↔
      (powUnitReduction P e g) ^ (Nat.card ((AdjoinRoot P)ˣ) / (k : ℕ)) =
        (1 : (AdjoinRoot P)ˣ) := by
  -- First reduce the `k`-th power problem to the residue field.
  refine (unit_exists_pow_iff_reduction_exists_pow hP e k hk g).trans ?_
  -- Then use the cyclic structure of the residue-field unit group.
  exact residue_field_unit_exists_pow_iff_pow_div_eq_one hP k hk (powUnitReduction P e g)

/-- Among the units modulo `P^e`, the distinct `k`-th power residues form a subgroup of cardinality
`Φ(P^e) / k`, expressed canonically as the range of the `k`-th power map on
`(𝔽_p[X] / (P^e))ˣ`. -/
-- Proof sketch: the reduction map to `((𝔽_p[X] / (P))ˣ)` has `p`-group kernel, so the `k`-th
-- power map has kernel of size exactly `k` when `k ∣ |(𝔽_p[X] / (P))ˣ|`. Apply the finite-group
-- counting formula `|range| = |G| / |ker|` to `powMonoidHom (k : ℕ)`.
theorem polynomial_prime_power_card_kth_power_residues
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) (k : ℕ+)
    (hk : (k : ℕ) ∣ Nat.card ((AdjoinRoot P)ˣ)) :
    Nat.card ((powMonoidHom (k : ℕ) : (AdjoinRoot (P ^ (e : ℕ)))ˣ →* _).range) =
      Nat.card ((AdjoinRoot (P ^ (e : ℕ)))ˣ) / (k : ℕ) := by
  -- Count the image of the power map via the size of its kernel.
  exact kth_power_range_card_via_reduction hP e k hk
