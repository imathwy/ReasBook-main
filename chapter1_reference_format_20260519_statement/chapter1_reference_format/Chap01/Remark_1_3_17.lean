import Mathlib
import chapter1_reference_format.Chap01.Proposition_1_3_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Polynomial
open Polynomial
open AdjoinRoot

namespace AdjoinRoot

variable {R : Type*} [CommRing R] (P : R[X]) (e : ℕ+)

/-- The canonical reduction map from `R[X] / (P^e)` to `R[X] / (P)`. -/
noncomputable abbrev powReduction : AdjoinRoot (P ^ (e : ℕ)) →ₐ[R] AdjoinRoot P :=
  algHomOfDvd R (P ^ (e : ℕ)) P (dvd_pow_self P (Nat.ne_of_gt e.2))

/-- The induced map on unit groups for reduction modulo `P`. -/
noncomputable abbrev powUnitReduction : (AdjoinRoot (P ^ (e : ℕ)))ˣ →* (AdjoinRoot P)ˣ :=
  Units.map (powReduction P e).toMonoidHom

end AdjoinRoot

variable {p : ℕ} [Fact p.Prime]

instance polynomialPrimePowerAdjoinRoot_finite
    {P : (ZMod p)[X]} [Fact (Irreducible P)] (e : ℕ+) :
    Finite (AdjoinRoot (P ^ (e : ℕ))) := by
  let hP : Irreducible P := Fact.out
  letI : Module.Finite (ZMod p) (AdjoinRoot (P ^ (e : ℕ))) :=
    (AdjoinRoot.powerBasis (pow_ne_zero _ hP.ne_zero)).finite
  exact Module.finite_of_finite (ZMod p)

/-- For irreducible `P`, the unit group of `𝔽_p[X] / (P^e)` is finitely generated because the
ambient quotient ring is finite. This is derived API from the canonical quotient owner, not
primitive source-facing data. -/
instance polynomialPrimePowerUnitGroup_fg
    {P : (ZMod p)[X]} [Fact (Irreducible P)] (e : ℕ+) :
    Group.FG ((AdjoinRoot (P ^ (e : ℕ)))ˣ) := by
  letI : Finite (AdjoinRoot (P ^ (e : ℕ))) := polynomialPrimePowerAdjoinRoot_finite e
  infer_instance

/-- For irreducible `P`, the kernel of reduction on units modulo `P^e → P` is finitely generated
because it is a subgroup of the finite unit group of `𝔽_p[X] / (P^e)`. -/
instance polynomialPrimePowerUnitReductionKer_fg
    {P : (ZMod p)[X]} [Fact (Irreducible P)] (e : ℕ+) :
    Group.FG ((powUnitReduction P e).ker) := by
  letI : Finite (AdjoinRoot (P ^ (e : ℕ))) := polynomialPrimePowerAdjoinRoot_finite e
  infer_instance

/-- Bridge/view API: `Group.rank` for the unit group of `𝔽_p[X] / (P^e)`, with the irreducibility
hypothesis kept as an explicit mathematical binder rather than a public `Fact` parameter. The
canonical owner remains `Group.rank`. -/
noncomputable abbrev polynomialPrimePowerUnitGroupRank
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) : ℕ :=
  letI : Fact (Irreducible P) := ⟨hP⟩
  Group.rank ((AdjoinRoot (P ^ (e : ℕ)))ˣ)

/-- Bridge/view API: `Group.rank` for the kernel of the reduction map on units modulo `P^e → P`,
again keeping irreducibility explicit in the public surface while reusing the canonical owner
`Group.rank`. -/
noncomputable abbrev polynomialPrimePowerUnitReductionKerRank
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) : ℕ :=
  letI : Fact (Irreducible P) := ⟨hP⟩
  Group.rank ((powUnitReduction P e).ker)

/-- Helper for Remark 1.3.17: the residue field `𝔽_p[X] / (P)` has cardinality `p ^ deg(P)`. -/
lemma natCard_adjoinRoot_irreducible
    {P : (ZMod p)[X]} (hP : Irreducible P) :
    Nat.card (AdjoinRoot P) = p ^ P.natDegree := by
  letI : Module.Finite (ZMod p) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  -- Compute the quotient size from its `𝔽_p`-vector-space dimension.
  have hdim : Module.finrank (ZMod p) (AdjoinRoot P) = P.natDegree := by
    simpa [AdjoinRoot] using
      (finrank_quotient_span_eq_natDegree (K := ZMod p) (f := P))
  calc
    Nat.card (AdjoinRoot P) = Nat.card (ZMod p) ^ Module.finrank (ZMod p) (AdjoinRoot P) :=
      Module.natCard_eq_pow_finrank (K := ZMod p) (V := AdjoinRoot P)
    _ = p ^ P.natDegree := by rw [Nat.card_zmod, hdim]

/-- Helper for Remark 1.3.17: reduction on unit groups modulo `P^e → P` is surjective. -/
lemma pow_unit_reduction_surjective
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) :
    Function.Surjective (powUnitReduction P e) := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Nontrivial (AdjoinRoot P) := inferInstance
  intro y
  -- Lift the residue-field unit to a polynomial representative.
  obtain ⟨Q, hQ⟩ := AdjoinRoot.mk_surjective (g := P) (y : AdjoinRoot P)
  have hQnot : Q ∉ Ideal.span ({P} : Set (ZMod p)[X]) := by
    intro hmem
    have hdiv : P ∣ Q := Ideal.mem_span_singleton.mp hmem
    have hzero : (AdjoinRoot.mk P Q : AdjoinRoot P) = 0 := (AdjoinRoot.mk_eq_zero).2 hdiv
    exact y.ne_zero (hQ.symm.trans hzero)
  letI : (Ideal.span ({P} : Set (ZMod p)[X])).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hP
  have hQunitPow :
      IsUnit (Ideal.Quotient.mk ((Ideal.span ({P} : Set (ZMod p)[X])) ^ (e : ℕ)) Q) :=
    (Ideal.Quotient.isUnit_mk_pow_iff_notMem (I := Ideal.span ({P} : Set (ZMod p)[X]))
      (n := (e : ℕ)) (Nat.ne_of_gt e.2)).2 hQnot
  have hEq :
      (Ideal.span ({P} : Set (ZMod p)[X])) ^ (e : ℕ) =
        Ideal.span ({P ^ (e : ℕ)} : Set (ZMod p)[X]) := by
    simpa using (Ideal.span_singleton_pow P (e : ℕ))
  have hQunitPe : IsUnit (AdjoinRoot.mk (P ^ (e : ℕ)) Q) := by
    simpa [AdjoinRoot.mk] using hQunitPow.map (Ideal.quotEquivOfEq hEq)
  refine ⟨hQunitPe.unit, ?_⟩
  apply Units.ext
  -- Reduction sends the lifted polynomial class back to the original residue class.
  change
    (powReduction P e)
        (((hQunitPe.unit : (AdjoinRoot (P ^ (e : ℕ)))ˣ) :
          AdjoinRoot (P ^ (e : ℕ)))) = y
  rw [show
      (((hQunitPe.unit : (AdjoinRoot (P ^ (e : ℕ)))ˣ) :
          AdjoinRoot (P ^ (e : ℕ)))) = AdjoinRoot.mk (P ^ (e : ℕ)) Q by
      exact hQunitPe.unit_spec]
  rw [powReduction, AdjoinRoot.coe_algHomOfDvd, AdjoinRoot.liftAlgHom_mk]
  change aeval (AdjoinRoot.root P) Q = y
  rw [AdjoinRoot.aeval_eq, hQ]

/-- Helper for Remark 1.3.17: the reduction kernel on units has the expected `p`-power
cardinality. -/
lemma natCard_pow_unit_reduction_ker
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) :
    Nat.card ((powUnitReduction P e).ker) = p ^ (P.natDegree * ((e : ℕ) - 1)) := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Module.Finite (ZMod p) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  letI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod p)
  letI : Module.Finite (ZMod p) (AdjoinRoot (P ^ (e : ℕ))) :=
    (AdjoinRoot.powerBasis (pow_ne_zero _ hP.ne_zero)).finite
  letI : Finite (AdjoinRoot (P ^ (e : ℕ))) := Module.finite_of_finite (ZMod p)
  have hsurj : Function.Surjective (powUnitReduction P e) :=
    pow_unit_reduction_surjective hP e
  have hindex :
      ((powUnitReduction P e).ker).index = Nat.card ((AdjoinRoot P)ˣ) := by
    calc
      ((powUnitReduction P e).ker).index = Nat.card (powUnitReduction P e).range :=
        Subgroup.index_ker (powUnitReduction P e)
      _ = Nat.card ((⊤ : Subgroup ((AdjoinRoot P)ˣ))) := by
        rw [(powUnitReduction P e).range_eq_top.2 hsurj]
      _ = Nat.card ((AdjoinRoot P)ˣ) := Nat.card_congr Subgroup.topEquiv.toEquiv
  have hmul :
      Nat.card ((powUnitReduction P e).ker) * Nat.card ((AdjoinRoot P)ˣ) =
        Nat.card ((AdjoinRoot (P ^ (e : ℕ)))ˣ) := by
    simpa [hindex] using
      (Subgroup.card_mul_index (H := (powUnitReduction P e).ker))
  have htotient :
      Nat.card ((AdjoinRoot (P ^ (e : ℕ)))ˣ) =
        Nat.card (AdjoinRoot P) ^ ((e : ℕ) - 1) * Nat.card ((AdjoinRoot P)ˣ) := by
    simpa [Polynomial.totient] using
      (Polynomial.totient_pow_irreducible (f := P) hP e)
  have hpow :
      Nat.card (AdjoinRoot P) ^ ((e : ℕ) - 1) =
        p ^ (P.natDegree * ((e : ℕ) - 1)) := by
    rw [natCard_adjoinRoot_irreducible hP, pow_mul]
  have hpos : 0 < Nat.card ((AdjoinRoot P)ˣ) := Nat.card_pos
  exact Nat.mul_right_cancel hpos <| by
    calc
      Nat.card ((powUnitReduction P e).ker) * Nat.card ((AdjoinRoot P)ˣ) =
          Nat.card ((AdjoinRoot (P ^ (e : ℕ)))ˣ) := hmul
      _ = Nat.card (AdjoinRoot P) ^ ((e : ℕ) - 1) * Nat.card ((AdjoinRoot P)ˣ) := htotient
      _ = p ^ (P.natDegree * ((e : ℕ) - 1)) * Nat.card ((AdjoinRoot P)ˣ) := by
        rw [hpow]

/-- Helper for Remark 1.3.17: once `p^s` dominates `e`, every element of the principal-unit
kernel has `p^s`-power equal to `1`. -/
lemma pow_unit_reduction_kernel_pow_eq_one_of_le
    {P : (ZMod p)[X]} (hP : Irreducible P) (e s : ℕ+)
    (hs : (e : ℕ) ≤ p ^ (s : ℕ)) (x : (powUnitReduction P e).ker) :
    x ^ (p ^ (s : ℕ)) = 1 := by
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
  have hnil :
      (AdjoinRoot.mk (P ^ (e : ℕ)) (P * T) : AdjoinRoot (P ^ (e : ℕ))) ^ (p ^ (s : ℕ)) = 0 := by
    change AdjoinRoot.mk (P ^ (e : ℕ)) ((P * T) ^ (p ^ (s : ℕ))) = 0
    rw [mul_pow]
    exact (AdjoinRoot.mk_eq_zero).2 <|
      dvd_mul_of_dvd_left (pow_dvd_pow P hs) (T ^ (p ^ (s : ℕ)))
  have hnat : (P ^ (e : ℕ)).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_ne_zero e.ne_zero hP.natDegree_pos.ne'
  have hdeg : (P ^ (e : ℕ)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (pow_ne_zero _ hP.ne_zero)]
    exact_mod_cast hnat
  haveI : CharP (AdjoinRoot (P ^ (e : ℕ))) p :=
    charP_of_injective_algebraMap (AdjoinRoot.coe_injective hdeg) p
  -- The nilpotent correction disappears after the large enough `p`-power.
  apply Subtype.ext
  apply Units.ext
  change
    (((u : (AdjoinRoot (P ^ (e : ℕ)))ˣ) : AdjoinRoot (P ^ (e : ℕ))) ^ (p ^ (s : ℕ))) = 1
  rw [hx_eq, add_pow_char_pow, one_pow, hnil, add_zero]

/-- Helper for Remark 1.3.17: the reduction kernel is a finite `p`-group. -/
lemma pow_unit_reduction_ker_isPGroup
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) :
    IsPGroup p ((powUnitReduction P e).ker) := by
  have hp : Nat.Prime p := Fact.out
  rw [IsPGroup.iff_orderOf]
  intro x
  have hle : (e : ℕ) ≤ p ^ (e : ℕ) := by
    exact
      (Nat.lt_two_pow_self : (e : ℕ) < 2 ^ (e : ℕ)).le.trans
        (Nat.pow_le_pow_left hp.two_le _)
  -- Apply the exponent bound with `s = e`.
  have hxpow : x ^ (p ^ (e : ℕ)) = 1 :=
    pow_unit_reduction_kernel_pow_eq_one_of_le hP e e hle x
  have hdvd : orderOf x ∣ p ^ (e : ℕ) := orderOf_dvd_of_pow_eq_one hxpow
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact ⟨n, hn⟩

/-- Helper for Remark 1.3.17: the residue-field unit group has order prime to the
characteristic `p`. -/
lemma residue_field_unit_card_not_dvd_char
    {P : (ZMod p)[X]} (hP : Irreducible P) :
    ¬ p ∣ Nat.card ((AdjoinRoot P)ˣ) := by
  have hp : Nat.Prime p := Fact.out
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Module.Finite (ZMod p) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  letI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod p)
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite (AdjoinRoot P)
  haveI : CharP (AdjoinRoot P) p :=
    charP_of_injective_algebraMap (AdjoinRoot.coe_injective' (f := P)) p
  obtain ⟨n, _, hcard⟩ := FiniteField.card (AdjoinRoot P) p
  -- The order is `p^n - 1`, hence coprime to `p`.
  rw [Nat.card_eq_fintype_card, Fintype.card_units, hcard]
  have hcop_pow : Nat.Coprime (p ^ (n : ℕ)) (p ^ (n : ℕ) - 1) := by
    rw [Nat.coprime_self_sub_right (Nat.succ_le_of_lt (pow_pos hp.pos _))]
    exact Nat.coprime_one_right _
  have hcop : Nat.Coprime p (p ^ (n : ℕ) - 1) :=
    (Nat.coprime_pow_left_iff n.2 p (p ^ (n : ℕ) - 1)).mp hcop_pow
  exact hp.coprime_iff_not_dvd.mp hcop

/-- Helper for Remark 1.3.17: taking the `|(𝔽_p[X]/(P))ˣ|`-th power always lands in the
principal-unit kernel. -/
lemma unit_pow_residue_field_card_mem_ker
    {P : (ZMod p)[X]} (_hP : Irreducible P) (e : ℕ+)
    (g : (AdjoinRoot (P ^ (e : ℕ)))ˣ) :
    g ^ Nat.card ((AdjoinRoot P)ˣ) ∈ (powUnitReduction P e).ker := by
  -- The quotient by the kernel is the residue-field unit group, so its cardinal kills every image.
  rw [MonoidHom.mem_ker, map_pow, pow_card_eq_one']

/-- Helper for Remark 1.3.17: the power map by `|(𝔽_p[X]/(P))ˣ|` factors through the
principal-unit kernel. -/
noncomputable abbrev unit_power_to_reduction_kernel
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) :
    (AdjoinRoot (P ^ (e : ℕ)))ˣ →* (powUnitReduction P e).ker :=
  (powMonoidHom (Nat.card ((AdjoinRoot P)ˣ))).codRestrict
    ((powUnitReduction P e).ker) (unit_pow_residue_field_card_mem_ker hP e)

/-- Helper for Remark 1.3.17: the above power map is surjective onto the principal-unit kernel. -/
lemma unit_power_to_reduction_kernel_surjective
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) :
    Function.Surjective (unit_power_to_reduction_kernel hP e) := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Module.Finite (ZMod p) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  letI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod p)
  letI : Module.Finite (ZMod p) (AdjoinRoot (P ^ (e : ℕ))) :=
    (AdjoinRoot.powerBasis (pow_ne_zero _ hP.ne_zero)).finite
  letI : Finite (AdjoinRoot (P ^ (e : ℕ))) := Module.finite_of_finite (ZMod p)
  have hpk : ¬ p ∣ Nat.card ((AdjoinRoot P)ˣ) :=
    residue_field_unit_card_not_dvd_char hP
  intro x
  -- The `p`-group kernel sees the residue-field-card power map as an automorphism.
  refine ⟨((pow_unit_reduction_ker_isPGroup hP e).powEquiv' hpk).symm x, ?_⟩
  simpa [unit_power_to_reduction_kernel, MonoidHom.codRestrict_apply] using
    ((pow_unit_reduction_ker_isPGroup hP e).powEquiv' hpk).apply_symm_apply x

/-- Helper for Remark 1.3.17: the kernel rank is bounded above by the full unit-group rank via
the surjective power map. -/
lemma polynomialPrimePowerUnitReductionKerRank_le_unitGroupRank
    {P : (ZMod p)[X]} (hP : Irreducible P) (e : ℕ+) :
    polynomialPrimePowerUnitReductionKerRank hP e ≤ polynomialPrimePowerUnitGroupRank hP e := by
  letI : Fact (Irreducible P) := ⟨hP⟩
  letI : Module.Finite (ZMod p) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  letI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod p)
  letI : Module.Finite (ZMod p) (AdjoinRoot (P ^ (e : ℕ))) :=
    (AdjoinRoot.powerBasis (pow_ne_zero _ hP.ne_zero)).finite
  letI : Finite (AdjoinRoot (P ^ (e : ℕ))) := Module.finite_of_finite (ZMod p)
  -- A surjective homomorphism from the full unit group controls the subgroup rank.
  exact Group.rank_le_of_surjective (unit_power_to_reduction_kernel hP e)
    (unit_power_to_reduction_kernel_surjective hP e)

-- Proof sketch: identify the kernel with the additive group of `(P) / (P^2)`, which is an
-- `𝔽_p`-vector space of dimension `P.natDegree`; a finite elementary abelian `p`-group is cyclic
-- exactly when that dimension is `1`.
/-- The reduction kernel modulo `P²` is cyclic exactly for linear irreducible polynomials. -/
theorem polynomial_prime_power_units_reduction_ker_isCyclic_iff_natDegree_eq_one
    {P : (ZMod p)[X]} (hP : Irreducible P) :
    IsCyclic ((powUnitReduction P 2).ker) ↔
      P.natDegree = 1 := by
  have hp : Nat.Prime p := Fact.out
  constructor
  · intro hcyc
    -- Route correction: use exponent-vs-cardinality for the elementary abelian `p`-group kernel.
    letI : Fact (Irreducible P) := ⟨hP⟩
    letI : Module.Finite (ZMod p) (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
    letI : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod p)
    letI : Module.Finite (ZMod p) (AdjoinRoot (P ^ (2 : ℕ))) :=
      (AdjoinRoot.powerBasis (pow_ne_zero _ hP.ne_zero)).finite
    letI : Finite (AdjoinRoot (P ^ (2 : ℕ))) := Module.finite_of_finite (ZMod p)
    have hcard :
        Nat.card ((powUnitReduction P 2).ker) = p ^ P.natDegree := by
      simpa using natCard_pow_unit_reduction_ker hP (2 : ℕ+)
    have hpow :
        ∀ x : (powUnitReduction P 2).ker, x ^ p = 1 := by
      have hs2 : (2 : ℕ) ≤ p ^ (1 : ℕ) := by
        simpa using hp.two_le
      intro x
      simpa using
        (pow_unit_reduction_kernel_pow_eq_one_of_le (hP := hP) (e := (2 : ℕ+))
          (s := (1 : ℕ+)) hs2 x)
    have hexp_dvd : Monoid.exponent ((powUnitReduction P 2).ker) ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one hpow
    have hfinite : Finite ((powUnitReduction P 2).ker) := inferInstance
    have hexp_eq :
        Monoid.exponent ((powUnitReduction P 2).ker) =
          Nat.card ((powUnitReduction P 2).ker) :=
      (IsCyclic.iff_exponent_eq_card (α := (powUnitReduction P 2).ker)).mp hcyc
    have hcard_dvd_p' : Nat.card ((powUnitReduction P 2).ker) ∣ p := by
      rw [← hexp_eq]
      exact hexp_dvd
    have hcard_dvd_p : p ^ P.natDegree ∣ p := by
      rw [hcard] at hcard_dvd_p'
      exact hcard_dvd_p'
    have hcard_dvd_p1 : p ^ P.natDegree ∣ p ^ 1 := by
      simpa using hcard_dvd_p
    have hdeg_le_one :
        P.natDegree ≤ 1 := by
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hcard_dvd_p1
    exact le_antisymm hdeg_le_one hP.natDegree_pos
  · intro hdeg
    -- The kernel has prime cardinality when `deg(P) = 1`.
    have hcard :
        Nat.card ((powUnitReduction P 2).ker) = p := by
      simpa [hdeg] using natCard_pow_unit_reduction_ker hP (2 : ℕ+)
    exact isCyclic_of_prime_card hcard

section

variable {P : (ZMod p)[X]}

-- Proof sketch: the kernel has cardinality `p ^ (P.natDegree * (e - 1))`, and every element of
-- the kernel has order dividing `p ^ s` whenever `e ≤ p ^ s`. Apply
-- `card_dvd_exponent_pow_rank'` to the kernel and compare exponents of `p`.
/-- The reduction kernel modulo `P^e` has rank bounded below by the size and exponent estimates
coming from its finite `p`-group structure. -/
theorem polynomial_prime_power_units_reduction_ker_rank_lower_bound
    (hP : Irreducible P) (e s : ℕ+) (hs : (e : ℕ) ≤ p ^ (s : ℕ)) :
    P.natDegree * ((e : ℕ) - 1) ≤
      (s : ℕ) * polynomialPrimePowerUnitReductionKerRank hP e := by
  have hp : Nat.Prime p := Fact.out
  letI : Fact (Irreducible P) := ⟨hP⟩
  -- Apply Schreier's rank bound to the finite abelian kernel using the textbook `p^s` exponent.
  have hdiv :
      Nat.card ((powUnitReduction P e).ker) ∣
        (p ^ (s : ℕ)) ^ polynomialPrimePowerUnitReductionKerRank hP e := by
    refine card_dvd_exponent_pow_rank' (G := (powUnitReduction P e).ker) ?_
    intro x
    exact pow_unit_reduction_kernel_pow_eq_one_of_le hP e s hs x
  have hpow :
      (p ^ (s : ℕ)) ^ polynomialPrimePowerUnitReductionKerRank hP e =
        p ^ ((s : ℕ) * polynomialPrimePowerUnitReductionKerRank hP e) := by
    rw [pow_mul]
  have hdiv' :
      Nat.card ((powUnitReduction P e).ker) ∣
        p ^ ((s : ℕ) * polynomialPrimePowerUnitReductionKerRank hP e) := by
    simpa [MonoidHom.mem_ker, hpow] using hdiv
  have hcard :
      Nat.card ((powUnitReduction P e).ker) =
        p ^ (P.natDegree * ((e : ℕ) - 1)) :=
    natCard_pow_unit_reduction_ker hP e
  have hpow_dvd :
      p ^ (P.natDegree * ((e : ℕ) - 1)) ∣
        p ^ ((s : ℕ) * polynomialPrimePowerUnitReductionKerRank hP e) := by
    rw [hcard] at hdiv'
    exact hdiv'
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hpow_dvd

-- Proof sketch: choose `s` so that `p ^ s ≥ e` and apply the previous lower bound to the kernel of
-- reduction. Since an irreducible polynomial has positive degree, the canonical minimum number of
-- generators `Group.rank ((AdjoinRoot (P ^ e))ˣ)` becomes arbitrarily large as `e` increases.
/-- Remark 1.3.17: unlike the integer case, for an irreducible `P ∈ 𝔽_p[X]` the multiplicative
group of units of `𝔽_p[X] / (P^e)` has unbounded rank as the exponent `e` grows. -/
theorem polynomial_prime_power_unit_group_rank_unbounded
    (hP : Irreducible P) (N : ℕ) :
    ∃ e : ℕ+,
      N ≤ polynomialPrimePowerUnitGroupRank hP e := by
  have hp : Nat.Prime p := Fact.out
  by_cases hN : N = 0
  · refine ⟨1, ?_⟩
    simp [hN]
  · let s : ℕ+ := ⟨2 * N, Nat.mul_pos (by decide) (Nat.pos_of_ne_zero hN)⟩
    let e : ℕ+ := ⟨p ^ (s : ℕ), pow_pos hp.pos _⟩
    have hs : (e : ℕ) ≤ p ^ (s : ℕ) := by
      rfl
    have hkernel :=
      polynomial_prime_power_units_reduction_ker_rank_lower_bound
        (hP := hP) (e := e) (s := s) hs
    have hbridge := polynomialPrimePowerUnitReductionKerRank_le_unitGroupRank hP e
    have hdeg_ge_one : 1 ≤ P.natDegree := Nat.succ_le_of_lt hP.natDegree_pos
    have hquad :
        2 * N ^ 2 ≤ p ^ (2 * N) - 1 := by
      have hpow_two : 2 ^ (2 * N) ≤ p ^ (2 * N) :=
        Nat.pow_le_pow_left hp.two_le _
      have hstep : 2 * N ^ 2 + 1 ≤ p ^ (2 * N) := by
        exact (Nat.two_mul_sq_add_one_le_two_pow_two_mul N).trans hpow_two
      have hlt : 2 * N ^ 2 < p ^ (2 * N) := by
        exact lt_of_lt_of_le (Nat.lt_succ_self _) hstep
      exact Nat.le_pred_of_lt hlt
    have hstart :
        N * (s : ℕ) ≤ P.natDegree * ((e : ℕ) - 1) := by
      change N * (2 * N) ≤ P.natDegree * (p ^ (2 * N) - 1)
      calc
        N * (2 * N) = 2 * N ^ 2 := by
          ring
        _ ≤ p ^ (2 * N) - 1 := hquad
        _ ≤ P.natDegree * (p ^ (2 * N) - 1) := by
          simpa using Nat.mul_le_mul_right (p ^ (2 * N) - 1) hdeg_ge_one
    have hfinal :
        (s : ℕ) * N ≤ (s : ℕ) * polynomialPrimePowerUnitGroupRank hP e := by
      calc
        (s : ℕ) * N = N * (s : ℕ) := by rw [Nat.mul_comm]
        _ ≤ P.natDegree * ((e : ℕ) - 1) := hstart
        _ ≤ (s : ℕ) * polynomialPrimePowerUnitReductionKerRank hP e := hkernel
        _ ≤ (s : ℕ) * polynomialPrimePowerUnitGroupRank hP e := Nat.mul_le_mul_left _ hbridge
    refine ⟨e, Nat.le_of_mul_le_mul_left hfinal s.2⟩

end
