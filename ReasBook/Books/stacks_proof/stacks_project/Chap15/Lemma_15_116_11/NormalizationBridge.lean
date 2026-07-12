import Mathlib
import StacksProject_2024.Chap10.Definition_10_143_1
import StacksProject_2024.Chap10.Lemma_10_37_12
import StacksProject_2024.Chap10.Lemma_10_143_5
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Lemma_15_44_4

open Polynomial
open IsLocalRing
open scoped IntermediateField

universe u v

namespace stacks_project.Chap15.Lemma_15_116_11

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable {p : ℕ} [Fact p.Prime] [CharP (FractionRing A) p]
variable {ξ : FractionRing A}

local notation "K" => FractionRing A

/-- Helper for Lemma 15.116.11: once the Artin-Schreier parameter `ξ` comes from `A`, the chosen
root is integral over `A`. -/
theorem artin_schreier_root_isIntegral_over_base_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    IsIntegral A z := by
  rcases hξ with ⟨a, ha⟩
  let f : A[X] := X ^ p - X - C a
  have hf_monic : f.Monic := by
    -- The Artin-Schreier polynomial over `A` is monic of degree `p`.
    have hp_degree : degree (X + C a : A[X]) < p := by
      have hp_one : (1 : WithBot ℕ) < p := by
        exact_mod_cast (((Fact.out : p.Prime).one_lt) : 1 < p)
      have hp_zero : (0 : WithBot ℕ) < p := by
        exact_mod_cast ((Fact.out : p.Prime).pos : 0 < p)
      have hC_degree : degree (C a : A[X]) < p := by
        exact lt_of_le_of_lt Polynomial.degree_C_le hp_zero
      refine lt_of_le_of_lt (degree_add_le (X : A[X]) (C a)) ?_
      rw [show degree (X : A[X]) = 1 by simp, max_lt_iff]
      exact ⟨by simpa using hp_one, hC_degree⟩
    simpa [f, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Polynomial.monic_X_pow_sub (p := (X + C a : A[X])) (n := p) hp_degree)
  have hz_aeval : aeval z f = 0 := by
    -- Rewrite the Artin-Schreier equation as a polynomial evaluation identity over `A`.
    simpa [f, ha, Polynomial.aeval_def, sub_eq_add_neg, add_assoc,
      IsScalarTower.algebraMap_eq A K L] using (sub_eq_zero.mpr hz)
  -- A root of a monic polynomial is integral over the base ring.
  exact ⟨f, hf_monic, hz_aeval⟩

/-- Helper for Lemma 15.116.11: the monogenic owner `A[z]` is integral over `A` once `ξ` comes
from the base ring. -/
theorem artin_schreier_adjoin_isIntegral_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    Algebra.IsIntegral A (Algebra.adjoin A ({z} : Set L)) := by
  -- Route correction: package the source-faithful monogenic owner `A[z]` directly, instead of
  -- redoing integrality after transporting to the normalization.
  have hz_integral :
      IsIntegral A z :=
    artin_schreier_root_isIntegral_over_base_of_mem_ring
      (A := A) (L := L) (p := p) (ξ := ξ) z hz hξ
  exact
    Algebra.IsIntegral.adjoin (R := A) (A := L) (S := ({z} : Set L)) <|
      fun x hx ↦ by
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact hz_integral

/-- Helper for Lemma 15.116.11: once `ξ` comes from `A`, the Artin-Schreier minimal polynomial
of the chosen root is separable over the base discrete valuation ring. -/
private theorem artin_schreier_minpoly_separable_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    (minpoly A z).Separable := by
  letI : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
  have hz_integral :
      IsIntegral A z :=
    artin_schreier_root_isIntegral_over_base_of_mem_ring
      (A := A) (L := L) (p := p) (ξ := ξ) z hz hξ
  rcases hξ with ⟨a, ha⟩
  let f : A[X] := X ^ p - X - C a
  have hf_sep : f.Separable := by
    -- The Artin-Schreier polynomial has derivative `-1`, so it is separable over `A`.
    rw [Polynomial.separable_def']
    refine ⟨0, -1, ?_⟩
    calc
      0 * f + (-1) * derivative f = -derivative f := by ring
      _ = -(-1 : A[X]) := by
            congr 1
            calc
              derivative f = derivative (X ^ p : A[X]) - derivative X - derivative (C a) := by
                  simp [f, sub_eq_add_neg, add_assoc]
              _ = C (p : A) * X ^ (p - 1) - 1 := by
                  simp [Polynomial.derivative_X_pow]
              _ = -1 := by
                  have hp_cast : (p : A) = 0 := by
                    apply IsFractionRing.injective A K
                    simpa using (CharP.cast_eq_zero K p)
                  simp [hp_cast]
      _ = 1 := by simp
  have hz_aeval : aeval z f = 0 := by
    -- Repackage the Artin-Schreier equation with coefficients in `A`.
    simpa [f, ha, Polynomial.aeval_def, sub_eq_add_neg, add_assoc,
      IsScalarTower.algebraMap_eq A K L] using (sub_eq_zero.mpr hz)
  -- The minimal polynomial inherits separability from the ambient Artin-Schreier polynomial.
  exact Polynomial.Separable.of_dvd hf_sep (minpoly.isIntegrallyClosed_dvd hz_integral hz_aeval)

/-- Helper for Lemma 15.116.11: the monogenic owner `A[z]` is already étale over `A` once the
Artin-Schreier derivative is invertible modulo the minimal polynomial. -/
theorem artin_schreier_adjoin_etale_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    let S : Subalgebra A L := Algebra.adjoin A ({z} : Set L)
    Algebra.Etale A S := by
  let S : Subalgebra A L := Algebra.adjoin A ({z} : Set L)
  change Algebra.Etale A S
  letI : Module.IsTorsionFree A L := Module.IsTorsionFree.trans_faithfulSMul A K L
  have hz_integral :
      IsIntegral A z :=
    artin_schreier_root_isIntegral_over_base_of_mem_ring
      (A := A) (L := L) (p := p) (ξ := ξ) z hz hξ
  have hsep :
      (minpoly A z).Separable :=
    artin_schreier_minpoly_separable_of_mem_ring
      (A := A) (L := L) (p := p) (ξ := ξ) z hz hξ
  let f : A[X] := minpoly A z
  let P : StandardEtalePair A :=
    { f := f
      monic_f := minpoly.monic hz_integral
      g := 1
      cond := by
        -- Separability gives the Bezout identity needed for a standard étale presentation.
        rcases (Polynomial.separable_def' f).1 hsep with ⟨u, v, huv⟩
        refine ⟨v, u, 0, ?_⟩
        simpa [f, mul_comm, add_comm, add_left_comm, add_assoc] using huv }
  let eAdjoin : AdjoinRoot f ≃ₐ[A] S :=
    minpoly.equivAdjoin (R := A) (x := z) hz_integral
  letI : IsLocalization.Away (1 : AdjoinRoot f)
      (Localization.Away (AdjoinRoot.mk f 1)) := by
    -- Localizing away from the image of `1` is the same as localizing away from `1`.
    simpa [AdjoinRoot.mk_self] using
      (inferInstance :
        IsLocalization.Away (AdjoinRoot.mk f 1)
          (Localization.Away (AdjoinRoot.mk f 1)))
  let eLoc : AdjoinRoot f ≃ₐ[A] Localization.Away (AdjoinRoot.mk f 1) :=
    (IsLocalization.atOne
      (R := AdjoinRoot f) (S := Localization.Away (AdjoinRoot.mk f 1))).restrictScalars A
  let e : P.Ring ≃ₐ[A] S :=
    (P.equivAwayAdjoinRoot.trans eLoc.symm).trans eAdjoin
  letI : Algebra.Etale A P.Ring := inferInstance
  -- Transport the standard étale owner from the quotient presentation to `A[z]`.
  exact Algebra.Etale.of_equiv e

/-- Helper for Lemma 15.116.11: the remaining normalization bridge should identify the monogenic
owner `A[z]` with the normalization of `A` in `L`. -/
theorem artin_schreier_adjoin_isIntegralClosure_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    let S : Subalgebra A L := Algebra.adjoin A ({z} : Set L)
    IsIntegralClosure S A L := by
  let S : Subalgebra A L := Algebra.adjoin A ({z} : Set L)
  -- Route correction: the next step is to prove `S` is étale over `A`, deduce normality of `S`,
  -- and then add the still-missing fraction-field bridge `Frac(S) = L`.
  -- TODO: combine `artin_schreier_adjoin_etale_of_mem_ring` with an explicit `IsFractionRing S L`
  -- bridge, then invoke `IsIntegralClosure.of_isIntegrallyClosed`.
  sorry

/-- Helper for Lemma 15.116.11: once the local étale neighborhood argument is carried out on the
monogenic owner `A[z]`, every branch over `maximalIdeal A` is unramified there. -/
theorem artin_schreier_adjoin_branch_isUnramifiedAt_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    let S : Subalgebra A L := Algebra.adjoin A ({z} : Set L)
    ∀ Q : Ideal S, [Q.IsMaximal] → [Q.LiesOver (maximalIdeal A)] →
      Algebra.IsUnramifiedAt A Q := by
  let S : Subalgebra A L := Algebra.adjoin A ({z} : Set L)
  change ∀ Q : Ideal S, [Q.IsMaximal] → [Q.LiesOver (maximalIdeal A)] →
      Algebra.IsUnramifiedAt A Q
  have hEt : Algebra.Etale A S :=
    artin_schreier_adjoin_etale_of_mem_ring
      (A := A) (L := L) (p := p) (ξ := ξ) z hz hξ
  intro Q _ _
  letI : Q.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  letI : Q.LiesOver (Ideal.under A Q) := Ideal.over_under Q
  letI : Algebra.Etale A S := hEt
  -- Global étaleness gives the `g = 1` neighborhood required by Lemma `10.143.5`.
  refine (Algebra.isUnramifiedAt_iff_map_eq A (Ideal.under A Q) Q).2 ?_
  refine ⟨?_, ?_⟩
  · exact
      (residueField_finite_and_separable_of_exists_etale_away (R := A) (S := S) Q
        ⟨1, by
          simpa [Ideal.eq_top_iff_one] using
            (show Q ≠ ⊤ from Ideal.IsPrime.ne_top (I := Q) inferInstance),
          inferInstance⟩).2
  · simpa using
      map_eq_maximalIdeal_of_exists_etale_away (R := A) (S := S) Q
        ⟨1, by
          simpa [Ideal.eq_top_iff_one] using
            (show Q ≠ ⊤ from Ideal.IsPrime.ne_top (I := Q) inferInstance),
          inferInstance⟩

/-- Helper for Lemma 15.116.11: the final transport step back to `integralClosure A L` should be
done once, after the normalization owner `A[z]` has been identified with the integral closure. -/
theorem artin_schreier_integralClosure_branch_isUnramifiedAt_of_mem_ring
    (z : L) (hz : z ^ p - z = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤)
    (hξ : ∃ a : A, algebraMap A K a = ξ) :
    ∀ P : Ideal (integralClosure A L), [P.IsMaximal] → [P.LiesOver (maximalIdeal A)] →
      Algebra.IsUnramifiedAt A P := by
  intro P _ _
  -- Route correction: first obtain `IsIntegralClosure (A[z]) A L`, then rewrite the owner once
  -- and transport the already-proved branchwise unramified statement from `Ideal (A[z])`.
  -- TODO: finish the single owner-change from `A[z]` to `integralClosure A L`.
  sorry

end

end stacks_project.Chap15.Lemma_15_116_11
