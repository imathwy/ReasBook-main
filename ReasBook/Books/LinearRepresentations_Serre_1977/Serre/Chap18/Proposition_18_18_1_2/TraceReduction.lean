import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_2
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.ProjectiveScalarExtensionClasses
import LinearRepresentations_Serre_1977.Serre.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_1_2
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.FiniteOrderEigenbasis
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.QuotientCharpoly
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1.RealizationCore

noncomputable section

open CategoryTheory
open scoped Representation
open scoped TensorProduct

universe u v x y

namespace Representation

section TraceReduction

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {A : Type v} [CommRing A]
variable {G : Type u} [Group G] [Fact p.Prime] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Proposition 18-18.1-2: on the `p`-regular locus, reducing the modular-character
value recovers the ordinary trace. -/
private theorem trace_eq_reduction_modularCharacter_of_pRegular
    (lift : PrimeToPRoot p k →* A) (red : A →+* k)
    (hred : ∀ x : PrimeToPRoot p k, red (lift x) = ((x : kˣ) : k))
    (ρ : Representation k G V) (s : { t : G // IsPRegular p t }) :
    LinearMap.trace k V (ρ s.1) =
      red (φ[lift](ρ) s) := by
  classical
  -- Rewrite the trace as the sum of the characteristic roots of `ρ s.1`.
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  -- Then push `red` through the defining modular-character root sum termwise.
  simp only [Representation.modularCharacter]
  rw [map_multiset_sum]
  congr
  ext μ
  simp [hred, charpolyRoot_primeToPRoot_coe]

/-- Helper for Proposition 18-18.1-2: in characteristic `p`, the `p ^ n`-th power of the
negation endomorphism acts as negation. -/
private theorem neg_one_end_pow_prime_apply_local (n : ℕ) (v : V) :
    ((-(1 : Module.End k V)) ^ p ^ n) v = -v := by
  have hp : Nat.Prime p := Fact.out
  -- Split according to whether the prime is `2` or odd.
  rcases hp.eq_two_or_odd' with rfl | hpodd
  · -- In characteristic `2`, negation is the identity on vectors.
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have htwo : (2 : k) • v = 0 := by
          simpa using
            (show ((2 : k) • v) = (0 : k) • v from
              congrArg (fun a : k => a • v) (CharP.cast_eq_zero (R := k) (p := 2)))
        have htwo' : (2 : ℕ) • v = 0 := by
          convert htwo using 1
          symm
          exact Nat.cast_smul_eq_nsmul k 2 v
        have hv : v = -v := by
          rw [eq_neg_iff_add_eq_zero]
          simpa [two_nsmul] using htwo'
        have heven : Even (2 ^ (n + 1)) := by
          refine ⟨2 ^ n, by omega⟩
        have hpow : (-(1 : Module.End k V)) ^ (2 ^ (n + 1)) = 1 :=
          heven.neg_one_pow
        rw [hpow]
        exact hv
  · -- For odd primes, `(-1)^(p^n) = -1`.
    have hpown : Odd (p ^ n) := hpodd.pow
    have hpow : (-(1 : Module.End k V)) ^ (p ^ n) = -1 :=
      hpown.neg_one_pow
    rw [hpow]
    rfl

/-- Helper for Proposition 18-18.1-2: the characteristic-`p` binomial identity rewrites
`(x - 1)^(p ^ n)` as `x^(p ^ n) - 1` on vectors. -/
private theorem sub_pow_prime_pow_apply_local
    (x : V ≃ₗ[k] V) (n : ℕ) (v : V) :
    (((x.toLinearMap - 1) ^ p ^ n) v) = ((x.toLinearMap ^ p ^ n - 1) v) := by
  have hp : Nat.Prime p := Fact.out
  have hcomm : Commute x.toLinearMap (-(1 : Module.End k V)) := by
    simpa using (Commute.all x.toLinearMap (-(1 : Module.End k V)))
  -- The noncommutative binomial expansion collapses because the intermediate `p`-multiple terms
  -- vanish in characteristic `p`.
  obtain ⟨r, hr⟩ := Commute.exists_add_pow_prime_pow_eq hp hcomm n
  have hterm : p • x (r v) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul k]
    simp
  have hv := congrArg (fun f : Module.End k V => f v) hr
  simpa [sub_eq_add_neg, Module.End.pow_apply,
    neg_one_end_pow_prime_apply_local (k := k) (p := p) (V := V) n v, hterm] using hv

/-- Helper for Proposition 18-18.1-2: a `p`-element linear automorphism becomes unipotent after
subtracting the identity, so the resulting endomorphism is nilpotent. -/
private theorem isPElement_linearEquiv_sub_one_isNilpotent
    (x : V ≃ₗ[k] V) (hx : IsPElement p x) :
    IsNilpotent (x.toLinearMap - 1) := by
  rcases (isPElement_iff_exists_pow_eq_one x).mp hx with ⟨n, hn⟩
  refine ⟨p ^ n, ?_⟩
  ext v
  rw [sub_pow_prime_pow_apply_local (k := k) (p := p) (V := V) x n v]
  have hval : (x ^ p ^ n) v = v := by
    simpa using congrArg (fun e : V ≃ₗ[k] V => e v) hn
  have hiter : (x.toLinearMap ^ p ^ n) v = v := by
    simpa [Module.End.pow_apply, LinearEquiv.pow_apply] using hval
  simpa using sub_eq_zero.mpr hiter

/-- Helper for Proposition 18-18.1-2: the trace is unchanged when replacing an element by its
`p`-regular component. -/
private theorem trace_eq_trace_pRegularComponent
    (ρ : Representation k G V) (t : G) :
    LinearMap.trace k V (ρ t) =
      LinearMap.trace k V (ρ (pRegularComponent p t)) := by
  let u := pUnipotentComponent p t
  let r := pRegularComponent p t
  have hdecomp := p_component_decomposition_exists (p := p) t (isOfFinOrder_of_finite t)
  have hu : IsPElement p u := by
    -- The canonical left factor in the `p`-component decomposition is a `p`-element.
    simpa [u] using hdecomp.isPElement
  have hcomm : Commute u r := by
    -- The two canonical factors commute inside the cyclic subgroup generated by `t`.
    simpa [u, r] using hdecomp.commute
  let eu : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ u) (ρ.apply_bijective u)
  have hnil : IsNilpotent (ρ u - 1) := by
    rcases (isPElement_iff_exists_pow_eq_one u).mp hu with ⟨n, hn⟩
    refine ⟨p ^ n, ?_⟩
    ext v
    -- The `p`-power identity for `u` turns the binomial expansion of `(ρ u - 1)^(p^n)` into `0`.
    have hsub :
        ((ρ u - 1) ^ p ^ n) v = ((eu.toLinearMap ^ p ^ n - 1) v) := by
      simpa [eu] using
        (sub_pow_prime_pow_apply_local (k := k) (p := p) (V := V) eu n v)
    rw [hsub]
    have hρ : ρ (u ^ p ^ n) = ρ (1 : G) := congrArg ρ hn
    have hval : (eu.toLinearMap ^ p ^ n) v = v := by
      simpa [eu, Module.End.pow_apply] using
        congrArg (fun f : Module.End k V => f v) hρ
    simpa using sub_eq_zero.mpr hval
  have hcommρ : Commute (ρ u) (ρ r) := by
    -- Applying the representation homomorphism preserves the commuting decomposition factors.
    simpa [u, r] using hcomm.map (ρ : G →* Module.End k V)
  have hcommSub : Commute (ρ u - 1) (ρ r) := by
    -- Subtracting the identity from the `p`-unipotent factor keeps it commuting with `ρ r`.
    exact hcommρ.sub_left (Commute.one_left (ρ r))
  have hnil' : IsNilpotent ((ρ u - 1) * ρ r) := by
    -- A commuting product with a nilpotent factor is nilpotent.
    exact hcommSub.isNilpotent_mul_right hnil
  have hzero : LinearMap.trace k V (((ρ u - 1) * ρ r)) = 0 := by
    -- Nilpotent endomorphisms have trace zero over a field.
    exact IsNilpotent.eq_zero <|
      LinearMap.isNilpotent_trace_of_isNilpotent hnil'
  have hmul : ρ t = (ρ u) * (ρ r) := by
    -- The canonical decomposition `t = u * r` transports through the representation map.
    simpa [u, r] using congrArg ρ hdecomp.eq_mul
  have hsplit : ρ t = ρ r + ((ρ u - 1) * ρ r) := by
    -- Expand the `p`-unipotent factor as `1 + (ρ u - 1)`.
    calc
      ρ t = (ρ u) * (ρ r) := hmul
      _ = ρ r + ((ρ u - 1) * ρ r) := by
        ext v
        simp [sub_eq_add_neg]
  -- The nilpotent correction has zero trace, so only the `p`-regular factor contributes.
  calc
    LinearMap.trace k V (ρ t) =
        LinearMap.trace k V (ρ r + ((ρ u - 1) * ρ r)) := by
          rw [hsplit]
    _ = LinearMap.trace k V (ρ r) +
          LinearMap.trace k V (((ρ u - 1) * ρ r)) := by
          rw [map_add]
    _ = LinearMap.trace k V (ρ r) := by
          rw [hzero, add_zero]
    _ = LinearMap.trace k V (ρ (pRegularComponent p t)) := by
          rfl

/-- Helper for Proposition 18-18.1-2: the trace is the reduction of the modular character
at the canonical `p`-regular component. -/
theorem trace_eq_reduction_modularCharacter_pRegularComponent_bridge
    (lift : PrimeToPRoot p k →* A) (red : A →+* k)
    (hred : ∀ x : PrimeToPRoot p k, red (lift x) = ((x : kˣ) : k))
    (ρ : Representation k G V) (t : G) :
    LinearMap.trace k V (ρ t) =
      red
        (φ[lift](ρ)
          ⟨pRegularComponent p t, isPRegular_pRegularComponent t⟩) :=
  -- Route correction: isolate the regular-locus trace computation first, then leave only the
  -- `p`-unipotent trace invariance as the remaining structural blocker.
  by
    -- First replace `t` by its canonical `p`-regular component on the trace side.
    rw [trace_eq_trace_pRegularComponent (p := p) (ρ := ρ) t]
    -- Then identify the resulting trace with the reduction of the modular-character root sum.
    exact trace_eq_reduction_modularCharacter_of_pRegular
      (p := p) (lift := lift) (red := red) hred ρ
      ⟨pRegularComponent p t, isPRegular_pRegularComponent t⟩


end TraceReduction

end Representation
