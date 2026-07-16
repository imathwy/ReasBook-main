import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.RealizationCore
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.KSideSpanning
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.CommutatorFrobenius
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.MixedRealizationAssembly
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.FiniteTransportCore

/-!
Assembly of Serre part `(b)` of Theorem 18-18.2-1.

The spanning statement is proved first over the residue field `k` itself, by Brauer's classical
commutator argument: a linear functional annihilating all tautological Brauer characters yields a
group-algebra element `u`, supported on `p`-regular representatives, whose traces on all simple
modules vanish.  Then `u` is congruent, modulo additive commutators, to a nilpotent element
(`exists_commutator_realization_of_traces_zero`, `isNilpotent_of_forall_asAlgebraHom_eq_zero`),
so a high `p`-power of `u` lies in the commutator subgroup (`CommutatorFrobenius`).  The
class-coefficient functional finally extracts the (Frobenius power of the) functional's
coefficients, forcing them all to vanish.

The resulting `k`-basis property yields the cardinality identity between the index family and the
`p`-regular classes; spanning over an arbitrary admissible coefficient field then follows from
linear independence (Serre part `(a)`) by dimension count.
-/

noncomputable section

universe u x

open CategoryTheory
open scoped Representation

namespace Representation

variable {p : ℕ} [Fact p.Prime]
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

section PowFix

/-- `p`-power exponents congruent to one modulo the `p`-regular exponent fix all `p`-regular
elements. -/
private theorem exists_pow_prime_fix (N : ℕ) :
    ∃ n : ℕ, N ≤ p ^ n ∧
      ∀ t : G, IsPRegular p t → t ^ (p ^ n) = t := by
  have hm₀ : pRegularExponent p G ≠ 0 := pRegularExponent_ne_zero (p := p) (G := G)
  have hco : Nat.Coprime p (pRegularExponent p G) :=
    coprime_pRegularExponent (G := G) Fact.out
  -- `p ^ totient m₀ ≡ 1 [MOD m₀]`, and powers of that exponent grow without bound.
  have hmod : p ^ Nat.totient (pRegularExponent p G) ≡ 1 [MOD pRegularExponent p G] :=
    Nat.ModEq.pow_totient hco
  set n₀ := Nat.totient (pRegularExponent p G) with hn₀def
  have hn₀pos : 0 < n₀ := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm₀)
  refine ⟨n₀ * N, ?_, ?_⟩
  · -- growth: `N ≤ p ^ (n₀ * N)`
    calc
      N ≤ p ^ N := Nat.le_of_lt (Nat.lt_pow_self (Fact.out : p.Prime).one_lt)
      _ ≤ p ^ (n₀ * N) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos
        (Nat.le_mul_of_pos_left N hn₀pos)
  · intro t ht
    -- `p ^ (n₀ * N) ≡ 1 [MOD m₀]`
    have hmodN : p ^ (n₀ * N) ≡ 1 [MOD pRegularExponent p G] := by
      rw [pow_mul]
      calc
        (p ^ n₀) ^ N ≡ 1 ^ N [MOD pRegularExponent p G] := hmod.pow N
        _ = 1 := one_pow N
    -- reduce the congruence to the order of `t` and conclude
    have hdvd : orderOf t ∣ pRegularExponent p G := orderOf_dvd_pRegularExponent ht
    have hmodt : p ^ (n₀ * N) ≡ 1 [MOD orderOf t] := hmodN.of_dvd hdvd
    calc
      t ^ (p ^ (n₀ * N)) = t ^ 1 := (pow_eq_pow_iff_modEq).mpr hmodt
      _ = t := pow_one t

end PowFix

section Independence

/-- Serre part `(a)` packaged for an arbitrary admissible coefficient field: the Brauer
characters of pairwise nonisomorphic simple representations are linearly independent. -/
theorem linearIndependent_brauer_of_pairwiseNonisomorphic_realization
    {K : Type u} [Field K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E) :
    LinearIndependent K
      (fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  rw [linearIndependent_iff']
  intro s a hsum i hi
  by_contra hai
  obtain ⟨aNorm, _haNorm_def, hsumNorm, haNorm_i⟩ :=
    normalized_supported_brauer_relation_local
      (p := p) (k := k) (K := K) (G := G) lift E s a hsum hi hai
  exact
    supported_normalized_brauer_relation_contradiction_realization
      (p := p) (k := k) (K := K) (G := G)
      lift hlift E hE_simple hE_pairwise s aNorm hsumNorm hi haNorm_i

/-- Specialization to the residue field itself, with the tautological lift. -/
theorem linearIndependent_brauer_value
    (E : ι → FDRep k G)
    (hE_simple : ∀ i, Simple (E i))
    (hE_pairwise : PairwiseNonisomorphic E) :
    LinearIndependent k
      (fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) (⇑(valueLift p k))) := by
  have h :=
    linearIndependent_brauer_of_pairwiseNonisomorphic_realization
      (p := p) (k := k) (K := k) (G := G)
      ((primeToPRoots p k).subtype) (primeToPRoots p k).subtype_injective
      E hE_simple hE_pairwise
  exact h

end Independence

section KSideSpan

/-- Serre part `(b)` over the residue field itself: the tautological Brauer characters of a
complete pairwise nonisomorphic simple family span all functions on the `p`-regular classes. -/
theorem span_brauer_value_eq_top
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Submodule.span k
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) (⇑(valueLift p k))) = ⊤ := by
  classical
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  letI : Finite ι :=
    (linearIndependent_brauer_value (p := p) (k := k) (G := G) E
      (fun i ↦ hE_complete.isSimple i) hE_pairwise).finite
  letI : Fintype ι := Fintype.ofFinite ι
  by_contra hne
  set W := Submodule.span k
    (Set.range fun i ↦
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E i) (⇑(valueLift p k)))
    with hWdef
  have hlt : W < ⊤ := lt_top_iff_ne_top.mpr hne
  obtain ⟨v₀, -, hv₀⟩ := SetLike.exists_of_lt hlt
  -- A nonzero functional vanishing on the Brauer span.
  have hq : W.mkQ v₀ ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hv₀
  obtain ⟨φQ, hφQ⟩ :=
    (not_forall.mp (fun h ↦ hq ((Module.forall_dual_apply_eq_zero_iff k (W.mkQ v₀)).mp h)))
  set ℓ : (PRegularConjClass G p → k) →ₗ[k] k := φQ.comp W.mkQ with hℓdef
  have hℓW : ∀ w ∈ W, ℓ w = 0 := by
    intro w hw
    have : W.mkQ w = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hw
    rw [hℓdef]
    simp [this]
  -- Its coefficients against the standard basis.
  set β : PRegularConjClass G p → k := fun c ↦ ℓ (Pi.single c 1) with hβdef
  have hℓexpand : ∀ f : PRegularConjClass G p → k, ℓ f = ∑ c, f c * β c := by
    intro f
    have hf : f = ∑ c, f c • (Pi.single c (1 : k) : PRegularConjClass G p → k) := by
      funext j
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single j]
      · simp
      · intro c _ hcj
        simp [Pi.single_apply, hcj]
      · intro h
        exact absurd (Finset.mem_univ j) h
    conv_lhs => rw [hf]
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    rw [map_smul, smul_eq_mul]
  have hβne : ∃ c₀, β c₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : ℓ v₀ = 0 := by
      rw [hℓexpand]
      refine Finset.sum_eq_zero fun c _ ↦ ?_
      rw [hall c, mul_zero]
    apply hφQ
    rw [hℓdef] at this
    simpa using this
  obtain ⟨c₀, hc₀⟩ := hβne
  -- Vanishing against every Brauer row.
  have hβrow : ∀ j : ι,
      (∑ c, FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) (⇑(valueLift p k)) c
        * β c) = 0 := by
    intro j
    rw [← hℓexpand]
    exact hℓW _ (Submodule.subset_span ⟨j, rfl⟩)
  -- The associated group-algebra element.
  set uβ : MonoidAlgebra k G := ∑ c : PRegularConjClass G p,
    MonoidAlgebra.single ((PRegularConjClass.representative (G := G) (p := p) c).1) (β c)
    with huβdef
  -- Brauer rows evaluate at chosen representatives.
  have hrow_repr : ∀ (j : ι) (c : PRegularConjClass G p),
      FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) (⇑(valueLift p k)) c =
        LinearMap.trace k (E j).V
          ((E j).ρ (PRegularConjClass.representative (G := G) (p := p) c).1) := by
    intro j c
    have hc : PRegularConjClass.ofSubtype (G := G) p
        (PRegularConjClass.representative (G := G) (p := p) c) = c := by
      apply Subtype.ext
      simpa using PRegularConjClass.mk_representative (G := G) (p := p) c
    have hofsub :=
      FDRep.modularCharacterOnPRegularConjClass_ofSubtype (p := p)
        (E j) (⇑(valueLift p k)) (PRegularConjClass.representative (G := G) (p := p) c)
    rw [hc] at hofsub
    rw [hofsub]
    exact modularCharacter_value_eq_trace (p := p) (E j).ρ _
  -- All simple traces of `uβ` vanish.
  have htr : ∀ j : ι,
      LinearMap.trace k (E j).V (Representation.asAlgebraHom (E j).ρ uβ) = 0 := by
    intro j
    rw [huβdef, map_sum, map_sum]
    have hterm : ∀ c : PRegularConjClass G p,
        LinearMap.trace k (E j).V
          (Representation.asAlgebraHom (E j).ρ
            (MonoidAlgebra.single
              ((PRegularConjClass.representative (G := G) (p := p) c).1) (β c))) =
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E j) (⇑(valueLift p k)) c
            * β c := by
      intro c
      rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul, hrow_repr j c]
      rw [mul_comm]
    rw [Finset.sum_congr rfl fun c _ ↦ hterm c]
    exact hβrow j
  -- Realize the commutator part and the nilpotent part.
  obtain ⟨vC, hvC, hvz⟩ :=
    exists_commutator_realization_of_traces_zero E
      (fun i ↦ hE_complete.isSimple i) hE_pairwise uβ htr
  obtain ⟨N, hN⟩ :=
    isNilpotent_of_forall_asAlgebraHom_eq_zero E hE_complete (x := uβ - vC) hvz
  obtain ⟨n, hnN, hnfix⟩ := exists_pow_prime_fix (p := p) (G := G) (N + 1)
  haveI : CharP (MonoidAlgebra k G) p := by
    constructor
    intro m
    rw [← CharP.cast_eq_zero_iff k p m]
    constructor
    · intro h
      have hm : ((m : k) • (1 : MonoidAlgebra k G)) = 0 := by
        rw [← h]
        simp [Algebra.smul_def]
      by_contra hk
      have := smul_eq_zero.mp hm
      rcases this with h0 | h0
      · exact hk h0
      · exact one_ne_zero h0
    · intro h
      have : ((m : MonoidAlgebra k G)) = (m : k) • (1 : MonoidAlgebra k G) := by
        simp [Algebra.smul_def]
      rw [this, h, zero_smul]
  -- A high Frobenius power of `uβ` lies in the commutator subgroup.
  have hxpow : (uβ - vC) ^ (p ^ n) = 0 := by
    have hN1 : (uβ - vC) ^ (N + 1) = 0 := by
      rw [pow_succ, hN, zero_mul]
    exact pow_eq_zero_of_le hnN hN1
  have hu_sub : uβ - (uβ - vC) ∈ ringCommutatorAddSubgroup (MonoidAlgebra k G) := by
    have : uβ - (uβ - vC) = vC := by abel
    rw [this]
    exact hvC
  have hu_pow_mem : uβ ^ (p ^ n) ∈ ringCommutatorAddSubgroup (MonoidAlgebra k G) := by
    have hcong :=
      pow_prime_pow_sub_pow_mem_ringCommutatorAddSubgroup
        (A := MonoidAlgebra k G) (p := p) hu_sub n
    rw [hxpow, sub_zero] at hcong
    exact hcong
  -- Expand the Frobenius power of the supported sum.
  have hsplit :=
    sum_pow_prime_pow_sub_sum_mem_ringCommutatorAddSubgroup
      (A := MonoidAlgebra k G) (p := p) Finset.univ
      (fun c : PRegularConjClass G p ↦
        MonoidAlgebra.single
          ((PRegularConjClass.representative (G := G) (p := p) c).1) (β c)) n
  rw [← huβdef] at hsplit
  have hsingles : (∑ c : PRegularConjClass G p,
      (MonoidAlgebra.single
        ((PRegularConjClass.representative (G := G) (p := p) c).1) (β c)) ^ (p ^ n)) ∈
      ringCommutatorAddSubgroup (MonoidAlgebra k G) := by
    have := AddSubgroup.sub_mem _ hu_pow_mem hsplit
    have heq : uβ ^ p ^ n -
        (uβ ^ p ^ n - ∑ c : PRegularConjClass G p,
          (MonoidAlgebra.single
            ((PRegularConjClass.representative (G := G) (p := p) c).1) (β c)) ^ (p ^ n)) =
        ∑ c : PRegularConjClass G p,
          (MonoidAlgebra.single
            ((PRegularConjClass.representative (G := G) (p := p) c).1) (β c)) ^ (p ^ n) := by
      abel
    rw [heq] at this
    exact this
  -- Identify each Frobenius power of a supported single.
  have hsingle_pow : ∀ c : PRegularConjClass G p,
      (MonoidAlgebra.single
        ((PRegularConjClass.representative (G := G) (p := p) c).1) (β c)) ^ (p ^ n) =
        MonoidAlgebra.single
          ((PRegularConjClass.representative (G := G) (p := p) c).1) (β c ^ (p ^ n)) := by
    intro c
    rw [MonoidAlgebra.single_pow]
    congr 1
    exact hnfix _ (PRegularConjClass.representative (G := G) (p := p) c).2
  rw [Finset.sum_congr rfl fun c _ ↦ hsingle_pow c] at hsingles
  -- Extract the `c₀`-coefficient with the class-coefficient functional.
  have hzero := classCoeffSum_eq_zero_of_mem_commutator (k := k) (c₀.1) hsingles
  rw [map_sum] at hzero
  have hcoeff : ∀ c : PRegularConjClass G p,
      classCoeffSum (k := k) (c₀.1)
        (MonoidAlgebra.single
          ((PRegularConjClass.representative (G := G) (p := p) c).1) (β c ^ (p ^ n))) =
        if c = c₀ then β c ^ (p ^ n) else 0 := by
    intro c
    rw [classCoeffSum_single]
    have hmem : ((PRegularConjClass.representative (G := G) (p := p) c).1 ∈
        (c₀.1 : ConjClasses G).carrier) ↔ c = c₀ := by
      rw [ConjClasses.mem_carrier_iff_mk_eq]
      rw [PRegularConjClass.mk_representative (G := G) (p := p) c]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        rw [h]
    by_cases hc : c = c₀
    · rw [if_pos (hmem.mpr hc), if_pos hc]
    · rw [if_neg (fun h ↦ hc (hmem.mp h)), if_neg hc]
  rw [Finset.sum_congr rfl fun c _ ↦ hcoeff c] at hzero
  rw [Finset.sum_ite_eq' Finset.univ c₀ (fun c ↦ β c ^ (p ^ n))] at hzero
  rw [if_pos (Finset.mem_univ c₀)] at hzero
  exact hc₀ (pow_eq_zero_iff (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
    |>.mp hzero)

end KSideSpan

section GeneralSpan

/-- Brauer's count: a complete pairwise nonisomorphic simple family is indexed by exactly as many
elements as there are `p`-regular conjugacy classes. -/
theorem card_complete_family_eq_card_pRegularConjClass
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    [Fintype ι] [Fintype (PRegularConjClass G p)] :
    Fintype.card ι = Fintype.card (PRegularConjClass G p) := by
  classical
  have hind :=
    linearIndependent_brauer_value (p := p) (k := k) (G := G) E
      (fun i ↦ hE_complete.isSimple i) hE_pairwise
  have hspan := span_brauer_value_eq_top (p := p) (k := k) (G := G) E hE_pairwise hE_complete
  let b : Module.Basis ι k (PRegularConjClass G p → k) := Module.Basis.mk hind hspan.ge
  have hfin : Module.finrank k (PRegularConjClass G p → k) = Fintype.card ι :=
    (Module.finrank_eq_card_basis b)
  rw [Module.finrank_pi] at hfin
  exact hfin.symm

/-- Serre part `(b)` over an arbitrary admissible coefficient field: every function on the
`p`-regular classes lies in the span of the Brauer characters of a complete family. -/
theorem finite_regular_and_brauer_table_span_transfer_realization
    {K : Type u} [Field K]
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K) :
    f ∈ Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  classical
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  letI : Finite ι :=
    (linearIndependent_brauer_value (p := p) (k := k) (G := G) E
      (fun i ↦ hE_complete.isSimple i) hE_pairwise).finite
  letI : Fintype ι := Fintype.ofFinite ι
  have hind :=
    linearIndependent_brauer_of_pairwiseNonisomorphic_realization
      (p := p) (k := k) (K := K) (G := G) lift hlift E
      (fun i ↦ hE_complete.isSimple i) hE_pairwise
  have hcard :=
    card_complete_family_eq_card_pRegularConjClass (p := p) (k := k) (G := G)
      E hE_pairwise hE_complete
  rcases isEmpty_or_nonempty ι with hempty | hne
  · -- no simple representations means no `p`-regular classes, so the space is trivial
    have hzero : Fintype.card (PRegularConjClass G p) = 0 := by
      rw [← hcard]
      exact Fintype.card_eq_zero
    haveI : IsEmpty (PRegularConjClass G p) := Fintype.card_eq_zero_iff.mp hzero
    have hf0 : f = 0 := funext fun c ↦ (IsEmpty.false c).elim
    rw [hf0]
    exact Submodule.zero_mem _
  · have hspan := hind.span_eq_top_of_card_eq_finrank ?_
    · rw [hspan]
      exact Submodule.mem_top
    · rw [Module.finrank_pi]
      exact hcard

end GeneralSpan

end Representation
