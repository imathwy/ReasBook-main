import Mathlib
import chapter1_reference_format.Chap01.Lemma_1_3_15

open scoped Polynomial
open Polynomial UniqueFactorizationMonoid

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {K : Type*} [Field K] [Finite K]

attribute [local instance] Classical.decEq

namespace Polynomial

/-- The polynomial Euler totient over a finite field is the cardinality of the unit group of the
quotient `K[X] / (f)`, expressed canonically via `AdjoinRoot f`. Concrete quotient presentations
are bridge/view lemmas rather than separate owners. -/
noncomputable abbrev totient (f : K[X]) : ℕ :=
  let _ := Fintype.ofFinite K
  Nat.card (AdjoinRoot f)ˣ

/-- For an irreducible polynomial over a finite field, the polynomial totient is `|K[X]/(f)| - 1`.
-/
theorem totient_irreducible {K : Type*} [Field K] [Finite K] (f : K[X]) (hf : Irreducible f) :
    totient f = Nat.card (AdjoinRoot f) - 1 := by
  letI : Fact (Irreducible f) := ⟨hf⟩
  letI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
  letI : Finite (AdjoinRoot f) := Module.finite_of_finite K
  simpa [totient] using Nat.card_units (AdjoinRoot f)

end Polynomial

section

variable (f : K[X]) (hf : Irreducible f)

/- Proposition 1.3.16 (1): if `f ∈ K[X]` is irreducible over a finite field `K`, then the unit
group of `K[X] / (f)` is cyclic. This item is `source-facing`, while the `core/canonical` owner is
the existing instance `IsCyclic (AdjoinRoot f)ˣ` once `AdjoinRoot f` is seen as a finite field. -/
#check
  (show IsCyclic (AdjoinRoot f)ˣ from
    letI : Fact (Irreducible f) := ⟨hf⟩
    letI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
    letI : Finite (AdjoinRoot f) := Module.finite_of_finite K
    inferInstance)

end

/-- Helper for Proposition 1.3.16: adjoining a root of `f ^ n` over a finite field has cardinality
`|AdjoinRoot f| ^ n`. -/
lemma natCard_adjoinRoot_pow (f : K[X]) (hf0 : f ≠ 0) (n : ℕ) :
    Nat.card (AdjoinRoot (f ^ n)) = Nat.card (AdjoinRoot f) ^ n := by
  -- Compute both quotient sizes from the `K`-vector-space dimensions of the corresponding
  -- `AdjoinRoot` constructions.
  have hsrc : Module.Finite K (AdjoinRoot (f ^ n)) :=
    (AdjoinRoot.powerBasis (pow_ne_zero _ hf0)).finite
  have htgt : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have hsrcdim : Module.finrank K (AdjoinRoot (f ^ n)) = (f ^ n).natDegree := by
    simpa [AdjoinRoot] using (finrank_quotient_span_eq_natDegree (K := K) (f := f ^ n))
  have htgtdim : Module.finrank K (AdjoinRoot f) = f.natDegree := by
    simpa [AdjoinRoot] using (finrank_quotient_span_eq_natDegree (K := K) (f := f))
  calc
    Nat.card (AdjoinRoot (f ^ n)) = Nat.card K ^ Module.finrank K (AdjoinRoot (f ^ n)) :=
      Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot (f ^ n))
    _ = Nat.card K ^ (f ^ n).natDegree := by rw [hsrcdim]
    _ = Nat.card K ^ (n * f.natDegree) := by rw [Polynomial.natDegree_pow]
    _ = Nat.card K ^ (f.natDegree * n) := by rw [Nat.mul_comm]
    _ = (Nat.card K ^ f.natDegree) ^ n := by rw [pow_mul]
    _ = Nat.card (AdjoinRoot f) ^ n := by
      rw [show Nat.card K ^ f.natDegree = Nat.card (AdjoinRoot f) by
        symm
        calc
          Nat.card (AdjoinRoot f) = Nat.card K ^ Module.finrank K (AdjoinRoot f) :=
            Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot f)
          _ = Nat.card K ^ f.natDegree := by rw [htgtdim]]

/-- Helper for Proposition 1.3.16: reduction modulo an irreducible `f` detects the units in
`AdjoinRoot (f ^ e)`. -/
lemma pow_reduction_isUnit_iff_ne_zero (f : K[X]) (hf : Irreducible f) (e : ℕ+)
    (x : AdjoinRoot (f ^ (e : ℕ))) :
    IsUnit x ↔
      AdjoinRoot.algHomOfDvd K (f ^ (e : ℕ)) f (dvd_pow_self f e.2.ne') x ≠ 0 := by
  -- Reduce to a polynomial representative, then apply the quotient-unit criterion and the
  -- irreducible/nondivisibility characterization of coprimality.
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective (g := f ^ (e : ℕ)) x
  rw [polynomial_quotient_mk_isUnit_iff]
  rw [show IsCoprime g (f ^ (e : ℕ)) ↔ IsCoprime g f from
    (IsCoprime.pow_right_iff (x := g) (y := f) e.2)]
  rw [show IsCoprime g f ↔ ¬ f ∣ g by
    rw [isCoprime_comm, Prime.coprime_iff_not_dvd hf.prime]]
  rw [show AdjoinRoot.algHomOfDvd K (f ^ (e : ℕ)) f (dvd_pow_self f e.2.ne')
        (AdjoinRoot.mk (f ^ (e : ℕ)) g) = AdjoinRoot.mk f g by
    rw [AdjoinRoot.coe_algHomOfDvd, AdjoinRoot.liftAlgHom_mk]
    simpa [Polynomial.aeval_def] using (AdjoinRoot.aeval_eq (f := f) g)]
  simp [AdjoinRoot.mk_eq_zero]

/-- Helper for Proposition 1.3.16: the kernel of reduction `AdjoinRoot (f^e) → AdjoinRoot f` has
cardinality `|AdjoinRoot f|^(e-1)`. -/
lemma natCard_pow_reduction_ker (f : K[X]) (hf : Irreducible f) (e : ℕ+) :
    Nat.card
        ↥((AdjoinRoot.algHomOfDvd K (f ^ (e : ℕ)) f (dvd_pow_self f e.2.ne')).toLinearMap.ker) =
      Nat.card (AdjoinRoot f) ^ ((e : ℕ) - 1) := by
  let ρ := AdjoinRoot.algHomOfDvd K (f ^ (e : ℕ)) f (dvd_pow_self f e.2.ne')
  -- Compute the kernel dimension by rank-nullity for the surjective reduction map.
  have hsrc : Module.Finite K (AdjoinRoot (f ^ (e : ℕ))) :=
    (AdjoinRoot.powerBasis (pow_ne_zero _ hf.ne_zero)).finite
  have htgt : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
  have hsrcdim : Module.finrank K (AdjoinRoot (f ^ (e : ℕ))) = (f ^ (e : ℕ)).natDegree := by
    simpa [AdjoinRoot] using (finrank_quotient_span_eq_natDegree (K := K) (f := f ^ (e : ℕ)))
  have htgtdim : Module.finrank K (AdjoinRoot f) = f.natDegree := by
    simpa [AdjoinRoot] using (finrank_quotient_span_eq_natDegree (K := K) (f := f))
  have hsurj : Function.Surjective ρ := by
    -- Every residue class modulo `f` is represented by the same polynomial modulo `f^e`.
    intro x
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective (g := f) x
    refine ⟨AdjoinRoot.mk (f ^ (e : ℕ)) g, ?_⟩
    rw [AdjoinRoot.coe_algHomOfDvd, AdjoinRoot.liftAlgHom_mk]
    simpa [Polynomial.aeval_def] using (AdjoinRoot.aeval_eq (f := f) g)
  have hrange : ρ.toLinearMap.range = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hpow :
      (e : ℕ) * f.natDegree = f.natDegree + f.natDegree * ((e : ℕ) - 1) := by
    -- Rewrite the positive exponent as `n + 1` to isolate one copy of `f.natDegree`.
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (e : ℕ) = n + 1 := by
      exact ⟨(e : ℕ) - 1, by
        simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, Nat.add_comm] using
          (Nat.succ_pred_eq_of_pos e.2).symm⟩
    rw [hn]
    rw [Nat.add_mul, one_mul, Nat.mul_comm]
    simp [Nat.add_comm]
  have hfinrank : Module.finrank K ρ.toLinearMap.ker = f.natDegree * ((e : ℕ) - 1) := by
    have hsum := LinearMap.finrank_range_add_finrank_ker ρ.toLinearMap
    rw [hrange, finrank_top, hsrcdim, htgtdim, Polynomial.natDegree_pow, hpow] at hsum
    exact Nat.add_left_cancel hsum
  have hkerFinite : Module.Finite K ↥ρ.toLinearMap.ker := inferInstance
  calc
    Nat.card ↥ρ.toLinearMap.ker = Nat.card K ^ Module.finrank K ρ.toLinearMap.ker :=
      Module.natCard_eq_pow_finrank (K := K) (V := ↥ρ.toLinearMap.ker)
    _ = Nat.card K ^ (f.natDegree * ((e : ℕ) - 1)) := by rw [hfinrank]
    _ = (Nat.card K ^ f.natDegree) ^ ((e : ℕ) - 1) := by rw [pow_mul]
    _ = Nat.card (AdjoinRoot f) ^ ((e : ℕ) - 1) := by
      rw [show Nat.card K ^ f.natDegree = Nat.card (AdjoinRoot f) by
        symm
        calc
          Nat.card (AdjoinRoot f) = Nat.card K ^ Module.finrank K (AdjoinRoot f) :=
            Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot f)
          _ = Nat.card K ^ f.natDegree := by rw [htgtdim]]

/-- Proposition 1.3.16 (2): if `f ∈ K[X]` is irreducible over a finite field `K` and `e` is
positive, then the polynomial Euler totient of `f ^ e` is `|f|^(e-1) (|f| - 1)`, expressed as the
cardinality formula `|f|^(e-1) * Φ(f)` on the owner `Polynomial.totient`. -/
-- Proof sketch: count all residue classes modulo `f ^ e`, identify the nonunits with the unique
-- maximal ideal generated by the image of `f`, and compute its size as `|f|^(e-1)`.
theorem Polynomial.totient_pow_irreducible
    (f : K[X]) (hf : Irreducible f) (e : ℕ+) :
    Polynomial.totient (f ^ (e : ℕ)) =
      Nat.card (AdjoinRoot f) ^ ((e : ℕ) - 1) * Polynomial.totient f := by
  let ρ := AdjoinRoot.algHomOfDvd K (f ^ (e : ℕ)) f (dvd_pow_self f e.2.ne')
  letI : Module.Finite K (AdjoinRoot (f ^ (e : ℕ))) :=
    (AdjoinRoot.powerBasis (pow_ne_zero _ hf.ne_zero)).finite
  letI : Finite (AdjoinRoot (f ^ (e : ℕ))) := Module.finite_of_finite K
  letI : Fintype (AdjoinRoot (f ^ (e : ℕ))) := Fintype.ofFinite (AdjoinRoot (f ^ (e : ℕ)))
  -- Replace units by the complementary nonzero fibers of reduction modulo `f`.
  have hunitSubtype :
      Nat.card {x : AdjoinRoot (f ^ (e : ℕ)) // IsUnit x} = Polynomial.totient (f ^ (e : ℕ)) := by
    unfold Polynomial.totient
    exact Nat.card_congr
      { toFun := fun x ↦ x.2.unit
        invFun := fun u ↦ ⟨u, u.isUnit⟩
        left_inv := by
          intro x
          apply Subtype.ext
          exact x.2.unit_spec
        right_inv := by
          intro u
          ext
          rfl }
  have hnonzeroSubtype :
      Nat.card {x : AdjoinRoot (f ^ (e : ℕ)) // ρ x ≠ 0} = Polynomial.totient (f ^ (e : ℕ)) := by
    rw [← hunitSubtype]
    exact Nat.card_congr
      { toFun := fun x ↦ ⟨x.1, (pow_reduction_isUnit_iff_ne_zero (f := f) hf e x.1).mpr x.2⟩
        invFun := fun x ↦ ⟨x.1, (pow_reduction_isUnit_iff_ne_zero (f := f) hf e x.1).mp x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  have hkerSubtype :
      Nat.card {x : AdjoinRoot (f ^ (e : ℕ)) // ρ x = 0} = Nat.card ↥ρ.toLinearMap.ker := by
    exact Nat.card_congr
      { toFun := fun x ↦ ⟨x.1, x.2⟩
        invFun := fun x ↦ ⟨x.1, x.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  -- Count nonzero fibers as the complement of the kernel inside the finite quotient ring.
  have hsub :
      Fintype.card {x : AdjoinRoot (f ^ (e : ℕ)) // ρ x ≠ 0} =
        Fintype.card (AdjoinRoot (f ^ (e : ℕ))) -
          Fintype.card {x : AdjoinRoot (f ^ (e : ℕ)) // ρ x = 0} := by
    simpa using (Fintype.card_subtype_compl (p := fun x : AdjoinRoot (f ^ (e : ℕ)) ↦ ρ x = 0))
  have htotal : Nat.card (AdjoinRoot (f ^ (e : ℕ))) = Nat.card (AdjoinRoot f) ^ (e : ℕ) :=
    natCard_adjoinRoot_pow (f := f) hf.ne_zero (e : ℕ)
  have hker : Nat.card ↥ρ.toLinearMap.ker = Nat.card (AdjoinRoot f) ^ ((e : ℕ) - 1) :=
    natCard_pow_reduction_ker (f := f) hf e
  have hkerSubtype' :
      Fintype.card {x : AdjoinRoot (f ^ (e : ℕ)) // ρ x = 0} = Nat.card ↥ρ.toLinearMap.ker := by
    simpa [Nat.card_eq_fintype_card] using hkerSubtype
  have htotient :
      Polynomial.totient (f ^ (e : ℕ)) =
        Nat.card (AdjoinRoot (f ^ (e : ℕ))) - Nat.card ↥ρ.toLinearMap.ker := by
    calc
      Polynomial.totient (f ^ (e : ℕ)) = Nat.card {x : AdjoinRoot (f ^ (e : ℕ)) // ρ x ≠ 0} := by
        exact hnonzeroSubtype.symm
      _ = Fintype.card {x : AdjoinRoot (f ^ (e : ℕ)) // ρ x ≠ 0} := by
        rw [Nat.card_eq_fintype_card]
      _ = Fintype.card (AdjoinRoot (f ^ (e : ℕ))) -
            Fintype.card {x : AdjoinRoot (f ^ (e : ℕ)) // ρ x = 0} := hsub
      _ = Nat.card (AdjoinRoot (f ^ (e : ℕ))) - Nat.card ↥ρ.toLinearMap.ker := by
        rw [← Nat.card_eq_fintype_card, hkerSubtype']
  rw [htotient, htotal, hker]
  -- The remaining arithmetic is exactly the irreducible case `|f| - 1`.
  rw [Polynomial.totient_irreducible f hf]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (e : ℕ) = n + 1 := by
    exact ⟨(e : ℕ) - 1, by
      simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.succ_pred_eq_of_pos e.2).symm⟩
  rw [hn]
  norm_num
  calc
    Nat.card (AdjoinRoot f) ^ (n + 1) - Nat.card (AdjoinRoot f) ^ n =
        Nat.card (AdjoinRoot f) ^ n * Nat.card (AdjoinRoot f) - Nat.card (AdjoinRoot f) ^ n := by
      rw [pow_succ]
    _ = Nat.card (AdjoinRoot f) ^ n * Nat.card (AdjoinRoot f) -
          Nat.card (AdjoinRoot f) ^ n * 1 := by
      rw [Nat.mul_one]
    _ = Nat.card (AdjoinRoot f) ^ n * (Nat.card (AdjoinRoot f) - 1) := by
      rw [← Nat.mul_sub_left_distrib]

/-- Helper for Proposition 1.3.16: every factor in the support of `factorization f` is a monic
irreducible polynomial. -/
lemma monic_irreducible_support_factorization (f P : K[X]) (hf : f ≠ 0)
    (hP : P ∈ (factorization f).support) :
    Irreducible P ∧ P.Monic := by
  -- Membership in the factorization support is exactly membership among the normalized factors.
  have hmem : P ∈ normalizedFactors f := by
    simpa [support_factorization] using hP
  exact
    let h := (Polynomial.mem_normalizedFactors_iff hf).mp hmem
    ⟨h.1, h.2.1⟩

/-- Helper for Proposition 1.3.16: the canonical product of prime powers coming from
`factorization f` is associated to `f`. -/
lemma associated_prod_factorization_powers (f : K[X]) (hf : f ≠ 0) :
    Associated (∏ P ∈ (factorization f).support, P ^ factorization f P) f := by
  -- Rewrite the support product as the canonical `Finsupp.prod`, then compare with
  -- `normalizedFactors`.
  have hprod' : (factorization f).prod (fun p n ↦ p ^ n) = (normalizedFactors f).prod := by
    rw [factorization]
    simpa using (Finsupp.prod_toMultiset (Multiset.toFinsupp (normalizedFactors f))).symm
  have hprod : (∏ P ∈ (factorization f).support, P ^ factorization f P) = (normalizedFactors f).prod := by
    rw [← hprod']
    simp [Finsupp.prod]
  have hassoc₁ :
      Associated (∏ P ∈ (factorization f).support, P ^ factorization f P) ((normalizedFactors f).prod) :=
    Associated.of_eq hprod
  have hassoc₂ : Associated ((normalizedFactors f).prod) (normalize f) := by
    rw [prod_normalizedFactors_eq hf]
  exact hassoc₁.trans (hassoc₂.trans (normalize_associated f))

/-- Helper for Proposition 1.3.16: the distinct prime-power factors arising from `factorization f`
are pairwise coprime. -/
lemma pairwise_coprime_factorization_powers (f : K[X]) (hf : f ≠ 0) :
    Pairwise (Function.onFun IsCoprime fun P : (factorization f).support ↦
      ((P : K[X]) ^ factorization f P)) := by
  intro P Q hPQ
  -- Distinct monic irreducible factors cannot divide one another, hence they are coprime; powers
  -- preserve coprimality.
  change IsCoprime ((P : K[X]) ^ factorization f P) ((Q : K[X]) ^ factorization f Q)
  have hP := monic_irreducible_support_factorization (f := f) (P := (P : K[X])) hf P.2
  have hQ := monic_irreducible_support_factorization (f := f) (P := (Q : K[X])) hf Q.2
  have hcop : IsCoprime (P : K[X]) (Q : K[X]) := by
    change IsCoprime (P : K[X]) (Q : K[X])
    rw [Prime.coprime_iff_not_dvd hP.1.prime]
    intro hdiv
    have hassoc : Associated (P : K[X]) (Q : K[X]) := by
      rcases (Irreducible.dvd_iff hQ.1).mp hdiv with hunit | hassoc
      · exact (hP.1.1 hunit).elim
      · exact hassoc.symm
    have hdvd : (P : K[X]) ∣ (Q : K[X]) ∧ (Q : K[X]) ∣ (P : K[X]) :=
      dvd_dvd_iff_associated.mpr hassoc
    have hnorm : normalize (P : K[X]) = normalize (Q : K[X]) :=
      normalize_eq_normalize hdvd.1 hdvd.2
    rw [hP.2.normalize_eq_self, hQ.2.normalize_eq_self] at hnorm
    exact hPQ (Subtype.ext hnorm)
  simpa using
    (hcop.pow_left.pow_right :
      IsCoprime ((P : K[X]) ^ factorization f P) ((Q : K[X]) ^ factorization f Q))

/-- Helper for Proposition 1.3.16: the prime-power totient formula can be written directly in the
Euler-factor form over `ℚ`. -/
lemma totient_pow_irreducible_rat (f : K[X]) (hf : Irreducible f) (e : ℕ+) :
    (Polynomial.totient (f ^ (e : ℕ)) : ℚ) =
      (Nat.card (AdjoinRoot f) : ℚ) ^ (e : ℕ) *
        (1 - 1 / (Nat.card (AdjoinRoot f) : ℚ)) := by
  -- Combine the prime-power count with the irreducible base case, then factor out one copy of
  -- `Nat.card (AdjoinRoot f)`.
  letI : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
  letI : Finite (AdjoinRoot f) := Module.finite_of_finite K
  have hq : Nat.card (AdjoinRoot f) ≠ 0 := Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  have hqQ : (Nat.card (AdjoinRoot f) : ℚ) ≠ 0 := by exact_mod_cast hq
  have hq1 : 1 ≤ Nat.card (AdjoinRoot f) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq)
  rw [Polynomial.totient_pow_irreducible (f := f) hf e, Polynomial.totient_irreducible f hf]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (e : ℕ) = n + 1 := by
    exact ⟨(e : ℕ) - 1, by
      simpa [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.succ_pred_eq_of_pos e.2).symm⟩
  rw [hn]
  calc
    ((Nat.card (AdjoinRoot f) ^ n * (Nat.card (AdjoinRoot f) - 1) : ℕ) : ℚ) =
        (Nat.card (AdjoinRoot f) : ℚ) ^ n * ((Nat.card (AdjoinRoot f) : ℚ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hq1, Nat.cast_one]
    _ =
        (Nat.card (AdjoinRoot f) : ℚ) ^ n *
          ((Nat.card (AdjoinRoot f) : ℚ) * (1 - 1 / (Nat.card (AdjoinRoot f) : ℚ))) := by
      field_simp [hqQ]
    _ = (Nat.card (AdjoinRoot f) : ℚ) ^ (n + 1) *
          (1 - 1 / (Nat.card (AdjoinRoot f) : ℚ)) := by
      rw [pow_succ]
      ring

/-- Helper for Proposition 1.3.16: associated polynomials have quotient rings with the same
cardinality. -/
lemma natCard_adjoinRoot_associated_eq (f g : K[X]) (hfg : Associated f g) :
    Nat.card (AdjoinRoot f) = Nat.card (AdjoinRoot g) := by
  -- Transport the quotient along the canonical algebra equivalence for associated polynomials.
  exact Nat.card_congr (AdjoinRoot.algEquivOfAssociated K f g hfg).toEquiv

/-- Helper for Proposition 1.3.16: polynomial totient is invariant under replacing a polynomial by
an associated one. -/
lemma Polynomial.totient_associated_eq (f g : K[X]) (hfg : Associated f g) :
    Polynomial.totient f = Polynomial.totient g := by
  -- Transport the unit group along the same equivalence and then unfold `totient`.
  unfold Polynomial.totient
  exact Nat.card_congr
    (((Units.mapEquiv (AdjoinRoot.algEquivOfAssociated K f g hfg).toMulEquiv)).toEquiv)

/-- Helper for Proposition 1.3.16: the quotient by a product of pairwise coprime polynomials has
cardinality equal to the product of the local quotient cardinalities. -/
lemma natCard_adjoinRoot_prod_pairwise_coprime {ι : Type*} [Fintype ι] (g : ι → K[X])
    (hg : Pairwise (Function.onFun IsCoprime fun i ↦ g i)) :
    Nat.card (AdjoinRoot (∏ i, g i)) = ∏ i, Nat.card (AdjoinRoot (g i)) := by
  let e : AdjoinRoot (∏ i, g i) ≃+* Π i, AdjoinRoot (g i) :=
    (Ideal.quotEquivOfEq ((Ideal.iInf_span_singleton (fun _ _ hij ↦ hg hij)).symm)).trans
      (Ideal.quotientInfRingEquivPiQuotient
        (fun i ↦ Ideal.span {g i})
        (fun _ _ hij ↦ (Ideal.isCoprime_span_singleton_iff _ _).mpr (hg hij)))
  -- Count the quotient after replacing it by the CRT product.
  calc
    Nat.card (AdjoinRoot (∏ i, g i)) = Nat.card (Π i, AdjoinRoot (g i)) := by
      exact Nat.card_congr e.toEquiv
    _ = ∏ i, Nat.card (AdjoinRoot (g i)) := Nat.card_pi

/-- Helper for Proposition 1.3.16: polynomial totient is multiplicative on a finite family of
pairwise coprime polynomials. -/
lemma Polynomial.totient_prod_pairwise_coprime {ι : Type*} [Fintype ι] (g : ι → K[X])
    (hg : Pairwise (Function.onFun IsCoprime fun i ↦ g i)) :
    Polynomial.totient (∏ i, g i) = ∏ i, Polynomial.totient (g i) := by
  let e : AdjoinRoot (∏ i, g i) ≃+* Π i, AdjoinRoot (g i) :=
    (Ideal.quotEquivOfEq ((Ideal.iInf_span_singleton (fun _ _ hij ↦ hg hij)).symm)).trans
      (Ideal.quotientInfRingEquivPiQuotient
        (fun i ↦ Ideal.span {g i})
        (fun _ _ hij ↦ (Ideal.isCoprime_span_singleton_iff _ _).mpr (hg hij)))
  -- Pass the CRT equivalence to units and then count cardinalities.
  unfold Polynomial.totient
  calc
    Nat.card (AdjoinRoot (∏ i, g i))ˣ = Nat.card (Π i, (AdjoinRoot (g i))ˣ) := by
      exact Nat.card_congr (((Units.mapEquiv e.toMulEquiv).trans MulEquiv.piUnits).toEquiv)
    _ = ∏ i, Nat.card (AdjoinRoot (g i))ˣ := Nat.card_pi

/-- Proposition 1.3.16 (3): for a nonzero polynomial `f ∈ K[X]` over a finite field `K`, the
polynomial Euler totient of `f` satisfies the Euler product formula over the distinct monic
irreducible divisors of `f`, represented by `(normalizedFactors f).toFinset`. -/
-- Proof sketch: factor `f` into prime powers using `normalizedFactors`, use the prime-power count
-- from the previous clause, and combine the factors by multiplicativity via the Chinese remainder
-- theorem.
theorem Polynomial.totient_eq_eulerProduct
    (f : K[X]) (hf : f ≠ 0) :
    (Polynomial.totient f : ℚ) =
      (Nat.card (AdjoinRoot f) : ℚ) *
        ((normalizedFactors f).toFinset.prod fun P ↦ 1 - 1 / (Nat.card (AdjoinRoot P) : ℚ)) := by
  let g : (factorization f).support → K[X] := fun P ↦ (P : K[X]) ^ factorization f P
  have hpair : Pairwise (Function.onFun IsCoprime fun P ↦ g P) := by
    -- The prime-power factors coming from `factorization f` are pairwise coprime.
    simpa [g] using pairwise_coprime_factorization_powers (f := f) hf
  have hassoc : Associated (∏ P : (factorization f).support, g P) f := by
    -- The product over the support of the factorization recovers `f` up to association.
    simpa [g] using associated_prod_factorization_powers (f := f) hf
  have htotient_transport :
      Polynomial.totient f = Polynomial.totient (∏ P : (factorization f).support, g P) := by
    -- Transport `totient` from `f` to the canonical prime-power product.
    symm
    exact Polynomial.totient_associated_eq (f := ∏ P : (factorization f).support, g P)
      (g := f) hassoc
  have hcard_transport :
      Nat.card (AdjoinRoot f) = Nat.card (AdjoinRoot (∏ P : (factorization f).support, g P)) := by
    -- Transport the ambient quotient cardinality across the same association.
    symm
    exact natCard_adjoinRoot_associated_eq (f := ∏ P : (factorization f).support, g P)
      (g := f) hassoc
  have htotient_prod :
      (Polynomial.totient (∏ P : (factorization f).support, g P) : ℚ) =
        ∏ P : (factorization f).support, (Polynomial.totient (g P) : ℚ) := by
    -- The CRT turns the global totient into the product of the local prime-power totients.
    rw [Polynomial.totient_prod_pairwise_coprime (g := g) hpair, Nat.cast_prod]
  have hcard_prod :
      (Nat.card (AdjoinRoot (∏ P : (factorization f).support, g P)) : ℚ) =
        ∏ P : (factorization f).support, (Nat.card (AdjoinRoot (g P)) : ℚ) := by
    -- The same CRT decomposition identifies the product of the local quotient sizes.
    rw [natCard_adjoinRoot_prod_pairwise_coprime (g := g) hpair, Nat.cast_prod]
  have hlocal_totient :
      (fun P : (factorization f).support ↦ (Polynomial.totient (g P) : ℚ)) =
        (fun P : (factorization f).support ↦
          (Nat.card (AdjoinRoot (P : K[X])) : ℚ) ^ factorization f P *
            (1 - 1 / (Nat.card (AdjoinRoot (P : K[X])) : ℚ))) := by
    -- Each local factor is the prime-power formula from clause (2).
    funext P
    have hP := monic_irreducible_support_factorization (f := f) (P := (P : K[X])) hf P.2
    have hpow_ne : factorization f P ≠ 0 := Finsupp.mem_support_iff.mp P.2
    have hpow_pos : 0 < factorization f P := Nat.pos_of_ne_zero hpow_ne
    let eP : ℕ+ := ⟨factorization f P, hpow_pos⟩
    simpa [g, eP] using totient_pow_irreducible_rat (f := (P : K[X])) hP.1 eP
  have hlocal_card :
      (fun P : (factorization f).support ↦
          (Nat.card (AdjoinRoot (P : K[X])) : ℚ) ^ factorization f P) =
        (fun P : (factorization f).support ↦ (Nat.card (AdjoinRoot (g P)) : ℚ)) := by
    -- Rewrite the local powers as the sizes of the prime-power quotient rings.
    funext P
    have hP := monic_irreducible_support_factorization (f := f) (P := (P : K[X])) hf P.2
    rw [show g P = (P : K[X]) ^ factorization f P by rfl]
    rw [← Nat.cast_pow]
    rw [← natCard_adjoinRoot_pow (f := (P : K[X])) hP.1.ne_zero (factorization f P)]
  -- Route correction: the endgame is now split into transport, CRT multiplicativity,
  -- and the final support-to-`normalizedFactors` rewrite.
  calc
    (Polynomial.totient f : ℚ) = (Polynomial.totient (∏ P : (factorization f).support, g P) : ℚ) := by
      rw [htotient_transport]
    _ = ∏ P : (factorization f).support, (Polynomial.totient (g P) : ℚ) := htotient_prod
    _ = ∏ P : (factorization f).support,
          ((Nat.card (AdjoinRoot (P : K[X])) : ℚ) ^ factorization f P *
            (1 - 1 / (Nat.card (AdjoinRoot (P : K[X])) : ℚ))) := by
      rw [hlocal_totient]
    _ = (∏ P : (factorization f).support,
            (Nat.card (AdjoinRoot (P : K[X])) : ℚ) ^ factorization f P) *
          ∏ P : (factorization f).support, (1 - 1 / (Nat.card (AdjoinRoot (P : K[X])) : ℚ)) := by
      simpa using
        (Finset.prod_mul_distrib :
          (∏ P : (factorization f).support,
              (Nat.card (AdjoinRoot (P : K[X])) : ℚ) ^ factorization f P *
                (1 - 1 / (Nat.card (AdjoinRoot (P : K[X])) : ℚ))) =
            (∏ P : (factorization f).support,
                (Nat.card (AdjoinRoot (P : K[X])) : ℚ) ^ factorization f P) *
              ∏ P : (factorization f).support, (1 - 1 / (Nat.card (AdjoinRoot (P : K[X])) : ℚ)))
    _ = (∏ P : (factorization f).support, (Nat.card (AdjoinRoot (g P)) : ℚ)) *
          ∏ P : (factorization f).support, (1 - 1 / (Nat.card (AdjoinRoot (P : K[X])) : ℚ)) := by
      rw [hlocal_card]
    _ = (Nat.card (AdjoinRoot (∏ P : (factorization f).support, g P)) : ℚ) *
          ∏ P : (factorization f).support, (1 - 1 / (Nat.card (AdjoinRoot (P : K[X])) : ℚ)) := by
      rw [← hcard_prod]
    _ = (Nat.card (AdjoinRoot f) : ℚ) *
          ∏ P : (factorization f).support, (1 - 1 / (Nat.card (AdjoinRoot (P : K[X])) : ℚ)) := by
      rw [hcard_transport]
    _ = (Nat.card (AdjoinRoot f) : ℚ) *
          ((normalizedFactors f).toFinset.prod fun P ↦ 1 - 1 / (Nat.card (AdjoinRoot P) : ℚ)) := by
      congr 1
      symm
      exact Finset.prod_subtype ((normalizedFactors f).toFinset) (fun P ↦ by
        simpa [support_factorization]) fun P ↦ 1 - 1 / (Nat.card (AdjoinRoot P) : ℚ)

end
