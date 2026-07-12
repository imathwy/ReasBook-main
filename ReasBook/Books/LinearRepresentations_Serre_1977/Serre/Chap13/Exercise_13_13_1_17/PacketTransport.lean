import Mathlib
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_2_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_2_1
import LinearRepresentations_Serre_1977.Chap08.Exercise_8_8_4_5
import LinearRepresentations_Serre_1977.RepresentationTheory.GroupFunctionPairing
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_3
import LinearRepresentations_Serre_1977.Chap12.Lemma_12_12_1_4
import LinearRepresentations_Serre_1977.Chap12.Corollary_12_12_4_2
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap13.Corollary_13_13_1_2
import LinearRepresentations_Serre_1977.Chap13.Exercise_13_13_1_17.AugmentationKernel
import LinearRepresentations_Serre_1977.Chap13.Exercise_13_13_1_17.RepresentativeSpan
import LinearRepresentations_Serre_1977.Chap13.Exercise_13_13_1_17.RepresentativeIndependence
import LinearRepresentations_Serre_1977.Chap13.Exercise_13_13_1_17.JenningsObstruction

namespace Serre.Chap13.Exercise_13_13_1_17

open Matrix
open Matrix.GeneralLinearGroup
open scoped MonoidAlgebra
open scoped Pointwise
open scoped Representation
open Representation

noncomputable section

open Polynomial

section Exercise137

variable (p : ℕ) [Fact p.Prime]

/-- Helper for Exercise 13-13.1-17: the common rational Artin-Wedderburn target shared by the
Heisenberg and semidirect models. -/
abbrev RationalPacketTarget :=
  ℚ × (Fin (p + 1) → CyclotomicField p ℚ) ×
    Matrix (Fin p) (Fin p) (CyclotomicField p ℚ)

/-- Helper for Exercise 13-13.1-17: the common rational Artin-Wedderburn target has total
`ℚ`-dimension `p^3`. -/
theorem rational_target_finrank_p_cubed :
    Module.finrank ℚ (RationalPacketTarget (p := p)) =
      p ^ 3 := by
  -- The cyclotomic field `ℚ(p)` has degree `φ(p) = p - 1` for prime `p`.
  have hcyclo : Module.finrank ℚ (CyclotomicField p ℚ) = p - 1 := by
    letI : NeZero (p : ℚ) := ⟨by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero⟩
    letI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
      CyclotomicField.isCyclotomicExtension (n := p) (K := ℚ)
    simpa [Nat.totient_prime (Fact.out : Nat.Prime p)] using
      IsCyclotomicExtension.Rat.finrank p (CyclotomicField p ℚ)
  -- Add the dimensions of the trivial factor, the `p + 1` cyclotomic field factors, and the
  -- `p × p` matrix algebra over that same cyclotomic field.
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, Module.finrank_pi_fintype,
    Module.finrank_matrix]
  simp [hcyclo]
  have hp : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  have hcalc : (1 + ((p + 1) * (p - 1) + p * p * (p - 1)) : ℤ) = p ^ 3 := by
    ring
  exact_mod_cast hcalc

/-- Helper for Exercise 13-13.1-17: once a rational packet map kills a complete complex family
after scalar extension, the packet map is injective over `ℚ`. -/
theorem rational_packet_map_injective_of_complex_family
    {G : Type} [Group G] [Finite G]
    {A : Type} [Ring A] [Algebra ℚ A]
    {ι : Type} (π : ι → Rep ℂ G) [∀ i, FiniteDimensional ℂ (π i)]
    (hπ_pairwise : CategoryTheory.PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily (fun i ↦ FDRep.of ((π i).ρ)))
    (Φ : ℚ[G] →ₐ[ℚ] A)
    (hΦ_family :
      ∀ z : ℚ[G], Φ z = 0 →
        familyEndAlgHom (π := π)
          (MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) z) = 0) :
    Function.Injective Φ := by
  intro x y hxy
  let z : ℚ[G] := x - y
  -- Pass to the difference so the packet map and the complete complex family both see a zero
  -- element.
  have hz_packet : Φ z = 0 := by
    simp [z, map_sub, hxy]
  have hfamily_zero :
      familyEndAlgHom (π := π)
          (MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) z) = 0 :=
    hΦ_family z hz_packet
  -- The complete-family injectivity theorem over `ℂ` needs the finite group order to be
  -- invertible, which is automatic in characteristic zero.
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have hinj_complex :
      Function.Injective (familyEndAlgHom (π := π)) :=
    familyEndAlgHom_injective_of_complete_family
      (π := π) hπ_pairwise hπ_complete
  have hmap_zero :
      MonoidAlgebra.mapRingHom G (algebraMap ℚ ℂ) z = 0 := by
    exact hinj_complex hfamily_zero
  have hz_zero : z = 0 := by
    -- Descend the complex zero equality coefficientwise through the injective scalar map
    -- `ℚ → ℂ`.
    ext g
    have hg0 := congrArg (fun w : ℂ[G] ↦ w g) hmap_zero
    change algebraMap ℚ ℂ (z g) = 0 at hg0
    exact RingHom.injective (algebraMap ℚ ℂ) (by simpa using hg0)
  exact sub_eq_zero.mp (by simpa [z] using hz_zero)

/-- Helper for Exercise 13-13.1-17: equal `ℚ`-dimensions upgrade an injective algebra map to an
algebra equivalence. -/
theorem algEquiv_of_injective_algHom_of_finrank_eq
    {A B : Type*} [Ring A] [Ring B] [Algebra ℚ A] [Algebra ℚ B]
    [FiniteDimensional ℚ A] [FiniteDimensional ℚ B]
    (Φ : A →ₐ[ℚ] B)
    (hdim : Module.finrank ℚ A = Module.finrank ℚ B)
    (hΦ : Function.Injective Φ) :
    Nonempty (A ≃ₐ[ℚ] B) := by
  -- Compare source and target dimensions on the underlying linear map.
  have hsurj : Function.Surjective Φ.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΦ
  exact ⟨AlgEquiv.ofBijective Φ ⟨hΦ, hsurj⟩⟩

/-- Helper for Exercise 13-13.1-17: an algebra equivalence identifies Jacobson radicals by
comap. This packages the membership-level transport from `JenningsObstruction` as an ideal
equality. -/
theorem jacobson_comap_eq_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) :
    Ideal.comap (e : A →+* B) (Ring.jacobson B) = Ring.jacobson A := by
  ext x
  -- Read comap membership through the already-proved Jacobson-membership transport.
  rw [Ideal.mem_comap]
  exact (mem_jacobson_iff_of_algEquiv (p := p) e (x := x)).symm

/-- Helper for Exercise 13-13.1-17: an algebra equivalence identifies Jacobson radicals by
map. This is the ideal-level rewrite needed before passing to Jennings quotients. -/
theorem jacobson_map_eq_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) :
    Ideal.map (e : A →+* B) (Ring.jacobson A) = Ring.jacobson B := by
  -- Compare after comapping along the surjective equivalence.
  apply (Ideal.comap_injective_of_surjective (f := (e : A →+* B)) e.surjective)
  rw [Ideal.comap_map_of_bijective (f := (e : A →+* B)) e.bijective]
  symm
  exact jacobson_comap_eq_of_algEquiv (p := p) e

/-- Helper for Exercise 13-13.1-17: an algebra equivalence transports products of two-sided
ideals exactly. This keeps the later Jennings-layer rewrites at the ideal level instead of
expanding quotient representatives. -/
theorem ideal_map_mul_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (I J : Ideal A) :
    Ideal.map (e : A →+* B) (I * J) =
      Ideal.map (e : A →+* B) I * Ideal.map (e : A →+* B) J := by
  apply le_antisymm
  · -- Forward inclusion is immediate from the product generators in `I * J`.
    rw [Ideal.map_le_iff_le_comap, Ideal.mul_le]
    intro r hr s hs
    rw [Ideal.mem_comap]
    simpa [map_mul] using
      (Ideal.mul_mem_mul
        (Ideal.mem_map_of_mem (e : A →+* B) hr)
        (Ideal.mem_map_of_mem (e : A →+* B) hs) :
        e r * e s ∈
          Ideal.map (e : A →+* B) I * Ideal.map (e : A →+* B) J)
  · -- For the reverse inclusion, pull both factors back through surjectivity of `e`.
    rw [Ideal.mul_le]
    intro y hy z hz
    rcases
        (Ideal.mem_map_iff_of_surjective (f := (e : A →+* B)) e.surjective).1 hy with
      ⟨r, hr, rfl⟩
    rcases
        (Ideal.mem_map_iff_of_surjective (f := (e : A →+* B)) e.surjective).1 hz with
      ⟨s, hs, rfl⟩
    simpa [map_mul] using
      (Ideal.mem_map_of_mem
        (e : A →+* B)
        (Ideal.mul_mem_mul hr hs) :
        e (r * s) ∈ Ideal.map (e : A →+* B) (I * J))

/-- Helper for Exercise 13-13.1-17: an algebra equivalence transports powers of the Jacobson
radical exactly. This closes the ideal-power rewrite step in the planned Jennings obstruction. -/
theorem jacobson_pow_map_eq_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) :
    Ideal.map (e : A →+* B) (Ring.jacobson A ^ n) = Ring.jacobson B ^ n := by
  have hmul :
      ∀ I J : Ideal A,
        Ideal.map (e : A →+* B) (I * J) =
          Ideal.map (e : A →+* B) I * Ideal.map (e : A →+* B) J :=
    ideal_map_mul_of_algEquiv (p := p) e
  have hjac :
      Ideal.map (e : A →+* B) (Ring.jacobson A) = Ring.jacobson B :=
    jacobson_map_eq_of_algEquiv (p := p) e
  induction n with
  | zero =>
      -- Both zeroth powers are the top ideal.
      change Ideal.map (e : A →+* B) (1 : Ideal A) = (1 : Ideal B)
      simpa [Ideal.one_eq_top] using (Ideal.map_top (e : A →+* B))
  | succ n ih =>
      -- Rewrite one Jacobson power by `I^(n+1) = I * I^n` and transport both factors.
      rw [(Ring.jacobson A).pow_succ, (Ring.jacobson B).pow_succ, hmul, hjac, ih]

/-- Helper for Exercise 13-13.1-17: the same algebra equivalence also identifies Jacobson
powers by comap. This is the form needed to compare quotient kernels. -/
theorem jacobson_pow_comap_eq_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) :
    Ideal.comap (e : A →+* B) (Ring.jacobson B ^ n) = Ring.jacobson A ^ n := by
  calc
    Ideal.comap (e : A →+* B) (Ring.jacobson B ^ n)
        = Ideal.comap (e : A →+* B)
            (Ideal.map (e : A →+* B) (Ring.jacobson A ^ n)) := by
              rw [jacobson_pow_map_eq_of_algEquiv (p := p) e n]
    _ = Ring.jacobson A ^ n := by
          rw [Ideal.comap_map_of_bijective (f := (e : A →+* B)) e.bijective]

/-- Helper for Exercise 13-13.1-17: vanishing of a Jacobson-power class is preserved by an
algebra equivalence. This isolates the quotient-kernel part of the Jennings obstruction from the
still-open compatibility with the `p`-th-power map. -/
theorem jacobson_pow_quotient_zero_iff_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) (x : A) :
    Ideal.Quotient.mk (Ring.jacobson B ^ n) (e x) = 0 ↔
      Ideal.Quotient.mk (Ring.jacobson A ^ n) x = 0 := by
  -- Convert both quotient equalities to ideal membership and then rewrite by comap.
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  rw [← jacobson_pow_comap_eq_of_algEquiv (p := p) e n, Ideal.mem_comap]
  simpa

/-- Helper for Exercise 13-13.1-17: the algebra equivalence itself respects the Jacobson-power
quotient kernels, so it induces the canonical map on the `n`-th Jennings layer. -/
theorem jacobson_pow_le_linear_comap_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) :
    Ring.jacobson A ^ n ≤
      Submodule.comap e.toRingHom.toSemilinearMap (Ring.jacobson B ^ n) := by
  -- Read the target submodule membership as ideal membership and rewrite it by the already-closed
  -- Jacobson-power comap theorem.
  intro x hx
  have hx' : x ∈ Ideal.comap (e : A →+* B) (Ring.jacobson B ^ n) := by
    rw [jacobson_pow_comap_eq_of_algEquiv (p := p) e n]
    exact hx
  simpa [Submodule.mem_comap, Ideal.mem_comap] using hx'

/-- Helper for Exercise 13-13.1-17: an algebra equivalence induces a linear map on the quotient by
the `n`-th Jacobson power. This is the concrete `Submodule.mapQ` owner needed for the Jennings
obstruction. -/
noncomputable def jacobson_pow_quotient_map_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) :
    A ⧸ Ring.jacobson A ^ n →ₛₗ[e.toRingHom] B ⧸ Ring.jacobson B ^ n :=
  (Ring.jacobson A ^ n).mapQ (Ring.jacobson B ^ n) e.toRingHom.toSemilinearMap
    (jacobson_pow_le_linear_comap_of_algEquiv (p := p) e n)

/-- Helper for Exercise 13-13.1-17: the induced quotient map sends the class of `x` to the class
of `e x`. This keeps the later Jennings comparison on representatives completely explicit. -/
theorem jacobson_pow_quotient_map_of_algEquiv_mk
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) (x : A) :
    jacobson_pow_quotient_map_of_algEquiv (p := p) e n
        (Ideal.Quotient.mk (Ring.jacobson A ^ n) x) =
      Ideal.Quotient.mk (Ring.jacobson B ^ n) (e x) := by
  -- Unfold the quotient map once and evaluate it on a class representative.
  simpa [jacobson_pow_quotient_map_of_algEquiv] using
    (Submodule.mapQ_apply
      (p := Ring.jacobson A ^ n)
      (q := Ring.jacobson B ^ n)
      (f := e.toRingHom.toSemilinearMap)
      (h := jacobson_pow_le_linear_comap_of_algEquiv (p := p) e n)
      x)

/-- Helper for Exercise 13-13.1-17: zero classes are preserved by the induced quotient map on
Jacobson powers. This is the quotient-level zero/nonzero transport needed before comparing the
Jennings `p`-th-power layer. -/
theorem jacobson_pow_quotient_map_eq_zero_iff_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (n : ℕ) (x : A) :
    jacobson_pow_quotient_map_of_algEquiv (p := p) e n
        (Ideal.Quotient.mk (Ring.jacobson A ^ n) x) = 0 ↔
      Ideal.Quotient.mk (Ring.jacobson A ^ n) x = 0 := by
  -- Reduce to the representative formula and then read zero through the earlier quotient-kernel
  -- transport theorem.
  rw [jacobson_pow_quotient_map_of_algEquiv_mk (p := p) e n x]
  exact jacobson_pow_quotient_zero_iff_of_algEquiv (p := p) e n x

/-- Helper for Exercise 13-13.1-17: the quotient map commutes with taking the representative
`p`-th power before passing to `J^(p+1)`. This is the stabilized quotient-level frontier of the
Jennings obstruction. -/
theorem jacobson_pth_power_quotient_map_of_algEquiv
    {A B : Type*} [Ring A] [Ring B]
    [Algebra (ZMod p) A] [Algebra (ZMod p) B]
    (e : A ≃ₐ[ZMod p] B) (x : A) :
    jacobson_pow_quotient_map_of_algEquiv (p := p) e (p + 1)
        (Ideal.Quotient.mk (Ring.jacobson A ^ (p + 1)) (x ^ p)) =
      Ideal.Quotient.mk (Ring.jacobson B ^ (p + 1)) (e x ^ p) := by
  -- The quotient map is defined on representatives, and the algebra equivalence carries `x^p`
  -- to `(e x)^p`.
  rw [jacobson_pow_quotient_map_of_algEquiv_mk (p := p) e (p + 1) (x ^ p)]
  simp [map_pow]

/-- Helper for Exercise 13-13.1-17: a multiplicative equivalence of groups transports to an
algebra equivalence of their group algebras over any coefficient semiring. -/
theorem groupAlgebra_equiv_of_mulEquiv
    {k G H : Type*} [CommSemiring k] [Group G] [Group H] (e : G ≃* H) :
    Nonempty (k[G] ≃ₐ[k] k[H]) := by
  -- The monoid-algebra domain congruence is the canonical transport owner.
  exact ⟨MonoidAlgebra.domCongr k k e⟩

/-- Helper for Exercise 13-13.1-17: finite group algebras have dimension equal to the group
cardinality. -/
theorem groupAlgebra_finrank_eq_natCard
    {k G : Type*} [Field k] [Group G] [Finite G] :
    Module.finrank k k[G] = Nat.card G := by
  let _ : Fintype G := Fintype.ofFinite G
  -- Rewrite the group algebra as a finitely supported function space on the group basis.
  rw [Nat.card_eq_fintype_card]
  change Module.finrank k (G →₀ k) = Fintype.card G
  exact Module.finrank_finsupp_self (R := k) (ι := G)

/-- Helper for Exercise 13-13.1-17: in characteristic `p`, the basis element `[g] - 1` has
`p`-th power `[g^p] - 1`. -/
theorem monoidAlgebra_of_sub_one_pow_p
    {G : Type*} [Group G] (g : G) :
    ((MonoidAlgebra.of (ZMod p) G g : (ZMod p)[G]) - 1) ^ p =
      MonoidAlgebra.of (ZMod p) G (g ^ p) - 1 := by
  let x : (ZMod p)[G] := MonoidAlgebra.of (ZMod p) G g
  have hp : Nat.Prime p := Fact.out
  have hpow : (x + -(1 : (ZMod p)[G])) ^ p = x ^ p + (-(1 : (ZMod p)[G])) ^ p := by
    obtain ⟨r, hr⟩ := (Commute.one_right x).neg_right.exists_add_pow_prime_eq hp
    have hpzero : ((p : ℕ) : (ZMod p)[G]) = 0 := by
      have hpzero' : ((p : ℕ) : ZMod p) = 0 := by
        simpa using (CharP.cast_eq_zero (R := ZMod p) (p := p))
      calc
        ((p : ℕ) : (ZMod p)[G]) =
            MonoidAlgebra.singleOneRingHom (R := ZMod p) (M := G) ((p : ℕ) : ZMod p) := rfl
        _ = MonoidAlgebra.singleOneRingHom (R := ZMod p) (M := G) 0 := by rw [hpzero']
        _ = 0 := by
              change MonoidAlgebra.single (1 : G) (0 : ZMod p) = 0
              exact Finsupp.single_zero _
    rw [hr, hpzero]
    simp
  have hxpow : x ^ p = MonoidAlgebra.of (ZMod p) G (g ^ p) := by
    simpa [x] using ((MonoidAlgebra.of (ZMod p) G).map_pow g p).symm
  -- The characteristic-`p` Frobenius identity turns `[g] - 1` into `[g^p] - 1`.
  calc
    ((MonoidAlgebra.of (ZMod p) G g : (ZMod p)[G]) - 1) ^ p
        = (x + -(1 : (ZMod p)[G])) ^ p := by simp [x, sub_eq_add_neg]
    _ = x ^ p + (-(1 : (ZMod p)[G])) ^ p := hpow
    _ = MonoidAlgebra.of (ZMod p) G (g ^ p) - 1 := by
          rw [hxpow]
          have hnegpow : (-(1 : (ZMod p)[G])) ^ p = -(1 : (ZMod p)[G]) := by
            have hnegcoeff : ((-1 : ZMod p) ^ p) = (-1 : ZMod p) := by
              by_cases hp2 : p = 2
              · subst hp2
                simp
              · have hpodd : Odd p := Nat.Prime.odd_of_ne_two hp hp2
                simpa using hpodd.neg_one_pow (α := ZMod p)
            have hsingle : (-(1 : (ZMod p)[G])) = MonoidAlgebra.single 1 (-1 : ZMod p) := by
              ext h
              by_cases hh : h = 1
              · subst hh
                simp [MonoidAlgebra.one_def]
              · simp [MonoidAlgebra.one_def, hh]
            rw [hsingle, MonoidAlgebra.single_pow]
            simpa [hnegcoeff]
          rw [hnegpow]
          simp [sub_eq_add_neg]

end Exercise137

end

end Exercise_13_13_1_17

end Chap13

end Serre
