import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.EisensteinAdjoinRootPackage

/-!
# Exercise 18-18.3-2: the full mixed-characteristic model with enough roots of unity

Over an algebraically closed field `k` of characteristic `p`, and for a finite group `G`, this file
constructs a complete mixed-characteristic discrete valuation ring `A` with residue field `k`
whose fraction field `K` has characteristic zero and contains a primitive `(Monoid.exponent G)`-th
root of unity (so `HasEnoughRootsOfUnity K (Monoid.exponent G)`).

Writing `Monoid.exponent G = p ^ a * m` with `gcd(m, p) = 1`, the two root sources are:

* the prime-to-`p` part `m`: lifted from `k` to `A` by Henselianity (`X ^ m - 1` is separable mod
  the maximal ideal because `m` is invertible in `k`).  This is fully proven below in
  `Representation.exists_isPrimitiveRoot_of_henselianLocalRing`.

* the `p`-power part `p ^ a`: realized by the *totally ramified* extension
  `AdjoinRoot (shifted_prime_power_cyclotomic_polynomial …)` of the Witt vectors `W(k)`, whose
  defining polynomial is Eisenstein and irreducible (proven in `MixedCharacteristicModel.lean`),
  and whose fraction field contains the required primitive `p ^ (n+1)`-th root (also proven there:
  `shifted_prime_power_cyclotomic_root_isPrimitiveRoot`).

The totally-ramified-DVR residue-field-invariance is supplied by the local support files
`EisensteinAdjoinRootLocal`, `EisensteinAdjoinRootComplete`, and
`EisensteinAdjoinRootPackage`: for a positive-degree Eisenstein polynomial over a complete DVR,
the corresponding `AdjoinRoot` is again a complete DVR and has the same residue field.  The
prime-to-`p` Hensel lift, the coprime assembly into one primitive
`(Monoid.exponent G)`-th root, the residue equivalence, all
DVR/Henselian/complete/Noetherian instances and `CharZero` are proven below.
-/

noncomputable section

universe u

namespace Representation

open Polynomial

section FullMixedCharacteristicModel

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]

/-- Helper for Exercise 18-18.3-2: an `I`-adically complete local ring is a Henselian local ring,
specialized at the maximal ideal. -/
theorem henselianLocalRing_of_isAdicComplete_maximalIdeal
    (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : HenselianLocalRing R := by
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  have hH : HenselianRing R (IsLocalRing.maximalIdeal R) := inferInstance
  have h₂' :
      IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) (f.derivative.eval a₀)) :=
    h₂.map _
  simpa using hH.is_henselian f hf a₀ h₁ h₂'

/-- Helper for Exercise 18-18.3-2: the prime-to-`p` part of the roots of unity.  If `A` is a
Henselian local ring whose residue field is the algebraically closed characteristic-`p` field `k`,
then for any `m` coprime to `p` (with `m ≠ 0`) the ring `A` contains a primitive `m`-th root of
unity: it is lifted from the (separable, since `m` is invertible) polynomial `X ^ m - 1` over the
residue field by Hensel's lemma. -/
theorem exists_isPrimitiveRoot_of_henselianLocalRing
    (A : Type*) [CommRing A] [HenselianLocalRing A]
    (e1 : IsLocalRing.ResidueField A ≃+* k)
    {m : ℕ} (hm0 : m ≠ 0) (hmp : ¬ (p : ℕ) ∣ m) :
    ∃ ζ : A, IsPrimitiveRoot ζ m := by
  -- `m` is invertible in `k`.
  haveI hmne : NeZero (m : k) := ⟨fun h => hmp ((CharP.cast_eq_zero_iff k p m).mp h)⟩
  -- A primitive `m`-th root of unity exists in the separably closed field `k`.
  obtain ⟨ζk, hζk⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k m
  -- Transport it to the residue field of `A`.
  set η : IsLocalRing.ResidueField A := e1.symm ζk with hηdef
  have hηprim : IsPrimitiveRoot η m := hζk.map_of_injective e1.symm.injective
  -- Pick a lift `a₀` of `η` to `A`.
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective (R := A) η
  -- Hensel's lemma applied to `f = X ^ m - 1`.
  set f : A[X] := X ^ m - C 1 with hf
  have hmonic : f.Monic := monic_X_pow_sub_C (1 : A) hm0
  have heval : f.eval a₀ ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, hf, eval_sub, eval_pow, eval_X, eval_C,
      map_sub, map_pow, ha₀, map_one, hηprim.pow_eq_one, sub_self]
  have hderiv_eq : f.derivative.eval a₀ = (m : A) * a₀ ^ (m - 1) := by
    rw [hf]
    simp [derivative_sub, derivative_X_pow, eval_mul, eval_pow, eval_X]
  have hderiv_unit : IsUnit (f.derivative.eval a₀) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hderiv_eq, map_mul, map_pow, map_natCast, ha₀]
    apply mul_ne_zero
    · intro h
      apply hmne.out
      have hcontr := congrArg e1 h
      rwa [map_natCast, map_zero] at hcontr
    · exact pow_ne_zero _ (hηprim.isUnit hm0).ne_zero
  obtain ⟨a, haroot, hasub⟩ := HenselianLocalRing.is_henselian f hmonic a₀ heval hderiv_unit
  have ham : a ^ m = 1 := by
    have h := haroot
    rw [IsRoot, hf, eval_sub, eval_pow, eval_X, eval_C] at h
    exact sub_eq_zero.mp h
  have haresidue : IsLocalRing.residue A a = η := by
    have h0 : IsLocalRing.residue A (a - a₀) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hasub
    rw [map_sub, sub_eq_zero] at h0
    exact h0.trans ha₀
  refine ⟨a, ham, fun l hl => ?_⟩
  exact hηprim.dvd_of_pow_eq_one l (by rw [← haresidue, ← map_pow, hl, map_one])

/-- Totally-ramified DVR residue-field invariance for Serre's shifted cyclotomic branch.

For the proven-Eisenstein, proven-irreducible shifted `p`-power cyclotomic polynomial
`f = shifted_prime_power_cyclotomic_polynomial n` over the complete discrete valuation ring `W(k)`
(see `MixedCharacteristicModel.lean`: `shifted_prime_power_cyclotomic_isEisenstein_over_wittVector`
and `shifted_prime_power_cyclotomic_irreducible_over_wittVector`), the extension `AdjoinRoot f` is
again a complete (adically complete) discrete valuation ring whose residue field is *unchanged*,
i.e. canonically `k`.  This is the classical fact that adjoining a root of an Eisenstein polynomial
to a complete DVR produces a *totally ramified* discrete valuation ring extension with the same
residue field. -/
private theorem adjoinRoot_shifted_ramifiedDVR (n : ℕ)
    [IsDomain (AdjoinRoot (shifted_prime_power_cyclotomic_polynomial (p := p) (k := k) n))] :
    ∃ inst : IsDiscreteValuationRing
        (AdjoinRoot (shifted_prime_power_cyclotomic_polynomial (p := p) (k := k) n)),
      IsAdicComplete
          (@IsLocalRing.maximalIdeal
            (AdjoinRoot (shifted_prime_power_cyclotomic_polynomial (p := p) (k := k) n)) _
            inst.toIsLocalRing)
          (AdjoinRoot (shifted_prime_power_cyclotomic_polynomial (p := p) (k := k) n)) ∧
        Nonempty
          (@IsLocalRing.ResidueField
              (AdjoinRoot (shifted_prime_power_cyclotomic_polynomial (p := p) (k := k) n)) _
              inst.toIsLocalRing ≃+* k) :=
  by
    let f := shifted_prime_power_cyclotomic_polynomial (p := p) (k := k) n
    have hf :
        f.IsEisensteinAt (IsLocalRing.maximalIdeal (WittVector p k)) := by
      simpa [f, shifted_prime_power_cyclotomic_polynomial] using
        shifted_prime_power_cyclotomic_isEisenstein_over_wittVector
          (p := p) (k := k) n
    have hmonic : f.Monic := by
      dsimp [f, shifted_prime_power_cyclotomic_polynomial]
      simpa using
        (((cyclotomic.monic (p ^ (n + 1)) ℤ)).map
            (Int.castRingHom (WittVector p k))).comp
          (monic_X_add_C (1 : WittVector p k))
          (by
            rw [natDegree_X_add_C]
            exact one_ne_zero)
    have hdeg : 0 < f.natDegree := by
      dsimp [f, shifted_prime_power_cyclotomic_polynomial]
      rw [natDegree_comp, natDegree_X_add_C, Nat.mul_one]
      rw [((cyclotomic.monic (p ^ (n + 1)) ℤ)).natDegree_map
        (Int.castRingHom (WittVector p k))]
      rw [natDegree_cyclotomic]
      exact (Nat.totient_pos).2 (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _)
    haveI :
        IsAdicComplete (IsLocalRing.maximalIdeal (WittVector p k)) (WittVector p k) := by
      rw [wittVector_maximalIdeal_eq_span_prime (p := p) (k := k)]
      exact inferInstance
    rcases
        adjoinRoot_complete_dvr_residue_of_eisenstein
          (R := WittVector p k) (f := f) hf hmonic hdeg with
      ⟨inst, hcomplete, ⟨eres⟩⟩
    exact ⟨inst, hcomplete, ⟨eres.trans (wittVector_residueField_ringEquiv (p := p) (k := k))⟩⟩

variable {G : Type u} [Group G] [Finite G]

/-- Helper for Exercise 18-18.3-2: the `p`-power root source.  There is a complete (adically
complete) Henselian discrete valuation ring `A1`, an algebra over `W(k)`, whose residue field is
`k` and whose characteristic-zero fraction field contains a primitive root of unity of order equal
to the `p`-part `p ^ (Monoid.exponent G).factorization p` of the group exponent.

When the `p`-part is trivial this is the base `W(k)` itself.  In the remaining (positive) branch the
model is the totally ramified extension `AdjoinRoot (shifted_prime_power_cyclotomic_polynomial …)`;
its defining polynomial is Eisenstein and irreducible
(`shifted_prime_power_cyclotomic_*_over_wittVector`), so `AdjoinRoot` is a domain with characteristic
zero, and its root provides the primitive `p`-power root
(`shifted_prime_power_cyclotomic_root_isPrimitiveRoot`).  The complete-DVR structure with residue
field `k` is supplied by `adjoinRoot_shifted_ramifiedDVR`, assembled from the Eisenstein
`AdjoinRoot` support files. -/
theorem exists_totally_ramified_p_power_root_extension_over_wittVector :
    ∃ (A1 : Type u) (_ : CommRing A1) (_ : IsLocalRing A1) (_ : HenselianLocalRing A1)
      (_ : IsDomain A1) (_ : IsDiscreteValuationRing A1)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal A1) A1) (_ : Algebra (WittVector p k) A1)
      (K1 : Type u) (_ : Field K1) (_ : Algebra A1 K1) (_ : IsFractionRing A1 K1)
      (_ : CharZero K1) (_ : IsLocalRing.ResidueField A1 ≃+* k) (ζp : K1),
        IsPrimitiveRoot ζp (p ^ Nat.factorization (Monoid.exponent G) p) := by
  rcases Nat.eq_zero_or_pos (Nat.factorization (Monoid.exponent G) p) with hpow | hpow
  · -- `p ∤ exp G`: the base Witt-vector DVR already works.
    exact exists_totally_ramified_p_power_root_extension_over_wittVector_of_factorization_eq_zero
      (p := p) (k := k) (G := G) hpow
  · -- `p ∣ exp G`: the totally ramified `AdjoinRoot` extension.  Everything here is proven; the
    -- complete-DVR and residue-field input is supplied by `adjoinRoot_shifted_ramifiedDVR`.
    obtain ⟨n, hn⟩ : ∃ n, Nat.factorization (Monoid.exponent G) p = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpow).symm⟩
    rw [hn]
    set f := shifted_prime_power_cyclotomic_polynomial (p := p) (k := k) n with hfdef
    have hirr : Irreducible f := shifted_prime_power_cyclotomic_irreducible_over_wittVector n
    have hprime : Prime f := (UniqueFactorizationMonoid.irreducible_iff_prime).mp hirr
    haveI hdom : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hprime
    haveI : CharZero (WittVector p k) := wittVector_charZero (p := p) (k := k)
    have hfdeg : f.degree ≠ 0 := by
      have hnat : 0 < f.natDegree := by
        rw [hfdef]
        dsimp only [shifted_prime_power_cyclotomic_polynomial]
        rw [natDegree_comp, natDegree_X_add_C, Nat.mul_one,
          ((cyclotomic.monic (p ^ (n + 1)) ℤ)).natDegree_map (Int.castRingHom (WittVector p k)),
          natDegree_cyclotomic]
        exact (Nat.totient_pos).2 (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) _)
      exact (Polynomial.natDegree_pos_iff_degree_pos.mp hnat).ne'
    haveI : CharZero (AdjoinRoot f) :=
      charZero_of_injective_ringHom (AdjoinRoot.of.injective_of_degree_ne_zero hfdeg)
    -- The complete ramified DVR structure supplied by the Eisenstein `AdjoinRoot` package.
    obtain ⟨instDVR, hcomplete, ⟨e1⟩⟩ := adjoinRoot_shifted_ramifiedDVR (p := p) (k := k) n
    letI := instDVR
    letI := hcomplete
    haveI : HenselianLocalRing (AdjoinRoot f) :=
      henselianLocalRing_of_isAdicComplete_maximalIdeal _
    letI : CharZero (FractionRing (AdjoinRoot f)) :=
      charZero_of_injective_ringHom
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f)))
    -- The primitive `p`-power root, proven in `MixedCharacteristicModel.lean`.
    have hroot :
        IsPrimitiveRoot
          (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) (AdjoinRoot.root f + 1))
          (p ^ (n + 1)) :=
      shifted_prime_power_cyclotomic_root_isPrimitiveRoot (p := p) (k := k) n
        (FractionRing (AdjoinRoot f))
    exact ⟨AdjoinRoot f, inferInstance, inferInstance, inferInstance, hdom, instDVR,
      hcomplete, inferInstance, FractionRing (AdjoinRoot f), inferInstance, inferInstance,
      inferInstance, inferInstance, e1, _, hroot⟩

include p in
/-- **Exercise 18-18.3-2.**  Over an algebraically closed field `k` of characteristic `p` and for a
finite group `G`, there is a complete mixed-characteristic discrete valuation ring `A` with residue
field `k` whose characteristic-zero fraction field `K` has enough roots of unity for the full group
exponent `Monoid.exponent G`. -/
theorem existsFullMixedCharacteristicModel_with_all_roots :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : HenselianLocalRing A)
      (_ : IsDomain A) (_ : IsDiscreteValuationRing A) (_ : IsNoetherianRing A)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
      (K : Type u) (_ : Field K) (_ : Algebra A K) (_ : IsFractionRing A K) (_ : CharZero K)
      (_ : HasEnoughRootsOfUnity K (Monoid.exponent G)),
      Nonempty (IsLocalRing.ResidueField A ≃+* k) := by
  obtain ⟨A, instCR, instLR, instHLR, instID, instDVR, instAC, instAlg,
      K, instFK, instAlgK, instFR, instCZ, e1, ζp, hζp⟩ :=
    exists_totally_ramified_p_power_root_extension_over_wittVector (p := p) (k := k) (G := G)
  letI := instCR; letI := instLR; letI := instHLR; letI := instID; letI := instDVR
  letI := instAC; letI := instAlg; letI := instFK; letI := instAlgK; letI := instFR
  letI := instCZ
  haveI : IsNoetherianRing A := inferInstance
  -- Number-theoretic data: `exp G = p ^ a * m` with `gcd(p, m) = 1`.
  have hexp_ne : Monoid.exponent G ≠ 0 := Monoid.ExponentExists.of_finite.exponent_ne_zero
  have hp : p.Prime := Fact.out
  set a := Nat.factorization (Monoid.exponent G) p with ha
  set m := ordCompl[p] (Monoid.exponent G) with hm
  have hm0 : m ≠ 0 := (Nat.ordCompl_pos p hexp_ne).ne'
  have hmp : ¬ (p : ℕ) ∣ m := Nat.not_dvd_ordCompl hp hexp_ne
  -- Prime-to-`p` root, lifted into `A` then mapped to `K`.
  obtain ⟨ζmA, hζmA⟩ :=
    exists_isPrimitiveRoot_of_henselianLocalRing (p := p) (k := k) A e1 hm0 hmp
  have hζm : IsPrimitiveRoot (algebraMap A K ζmA) m :=
    hζmA.map_of_injective (IsFractionRing.injective A K)
  set ζm := algebraMap A K ζmA with hζmdef
  -- Assemble the two coprime roots into one primitive `(exp G)`-th root.
  have hco : (orderOf ζp).Coprime (orderOf ζm) := by
    rw [← hζp.eq_orderOf, ← hζm.eq_orderOf]
    exact (Nat.coprime_ordCompl hp hexp_ne).pow_left a
  have hmul : orderOf (ζp * ζm) = Monoid.exponent G := by
    rw [(Commute.all ζp ζm).orderOf_mul_eq_mul_orderOf_of_coprime hco,
      ← hζp.eq_orderOf, ← hζm.eq_orderOf]
    exact Nat.ordProj_mul_ordCompl_eq_self (Monoid.exponent G) p
  have hprim : IsPrimitiveRoot (ζp * ζm) (Monoid.exponent G) :=
    IsPrimitiveRoot.iff_orderOf.mpr hmul
  haveI : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    { prim := ⟨ζp * ζm, hprim⟩, cyc := inferInstance }
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, K, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨e1⟩⟩

end FullMixedCharacteristicModel

end Representation
