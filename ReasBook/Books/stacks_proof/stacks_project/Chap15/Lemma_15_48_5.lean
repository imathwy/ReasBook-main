import Mathlib
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import StacksProject_2024.Chap10.Definition_10_160_1
import StacksProject_2024.Chap10.Lemma_10_115_7
import StacksProject_2024.Chap10.Lemma_10_158_2
import StacksProject_2024.Chap10.Lemma_10_160_2
import StacksProject_2024.Chap10.Lemma_10_160_10
import StacksProject_2024.Chap10.Lemma_10_160_11
import StacksProject_2024.Chap15.Lemma_15_46_4
import StacksProject_2024.Chap15.Lemma_15_46_5
import StacksProject_2024.Chap15.Lemma_15_48_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open KaehlerDifferential
open scoped BigOperators

section

variable {B : Type u} [CommRing B] [IsDomain B]

/- Domain-style sampling:
* primary domain: characteristic-`p` commutative algebra of domains, fraction fields, Kähler
  differentials, and absolute derivations;
* sampled owner declarations of the same kind:
  `Derivation`,
  `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`,
  `kaehlerDifferential_eq_zero_iff_exists_pth_root`,
  `Derivation.localizationExtension`;
* best owner abstraction: this numbered item stays `source-facing`; the canonical owner for the
  output is `Derivation ℤ B B`, while the non-`p`th-power input is measured intrinsically in the
  fraction field `FractionRing B`;
* primitive data: the ambient characteristic-`p` domain `B`, the finite-type-over-some-complete-
  local-ring hypothesis, the element `f : B`, and the fraction-field non-`p`th-power hypothesis on
  `f`;
* derived API: the fraction-field differential obstruction from
  `kaehlerDifferential_eq_zero_iff_exists_pth_root`, the existence of a fraction-field derivation
  not killing `f` via `KaehlerDifferential.linearMapEquivDerivation`, and the descent/clearing-
  denominators step yielding a derivation `B → B`.

Source/core/bridge triage:
* `source-facing`: `exists_derivation_with_nonzero_apply_of_not_exists_pth_root`;
* `core/canonical`: `Derivation ℤ B B`, `FractionRing B`, and the universal derivation
  `KaehlerDifferential.D`;
* `bridge/view`: the finite complete-local presentation supplied by `hB` and the fraction-field
  derivation construction/descent used in the proof sketch.
-/

-- Proof sketch: choose a Noetherian complete local ring `R` and a finite type map `R → B` from
-- the given existential hypothesis.
-- Replacing `R` by its image in `B` reduces to the case where `R` is a domain of characteristic
-- `p`. Cohen structure and the finite-type reduction from the source then replace `B` by a finite
-- extension of a mixed power-series/polynomial ring. Lemma `10.158.2` shows that the absolute
-- differential of `f` in `FractionRing B` is nonzero because `f` is not a `p`th power, and Lemma
-- `15.46.5` allows one to choose a derivation of the fraction field that does not kill `f`.
-- Clearing denominators yields the required derivation `B → B`.
/-- Helper for Lemma 15.48.5: if `g^(pN) * x` is a `p`th power in a field and `g ≠ 0`, then `x`
is already a `p`th power. -/
lemma exists_pth_root_of_mul_pth_power {K : Type*} [Field K] {p N : ℕ} {g x : K}
    (hg : g ≠ 0) (h : ∃ y : K, y ^ p = g ^ (p * N) * x) :
    ∃ z : K, z ^ p = x := by
  rcases h with ⟨y, hy⟩
  refine ⟨y / g ^ N, ?_⟩
  have hgN : (g ^ N) ^ p ≠ 0 := by
    exact pow_ne_zero p (pow_ne_zero N hg)
  -- Divide the chosen `p`th root by `g^N` and compare `p`th powers.
  calc
    (y / g ^ N) ^ p = y ^ p / (g ^ N) ^ p := by
      rw [div_eq_mul_inv, mul_pow, inv_pow, div_eq_mul_inv]
    _ = x := by
      rw [div_eq_iff hgN]
      calc
        y ^ p = g ^ (p * N) * x := hy
        _ = x * (g ^ N) ^ p := by
          rw [← pow_mul, Nat.mul_comm p N]
          ac_rfl

/-- Helper for Lemma 15.48.5: multiplying by a `p`th power cannot create a new `p`th root. -/
lemma not_exists_pth_root_of_mul_pth_power {K : Type*} [Field K] {p N : ℕ} {g x : K}
    (hg : g ≠ 0) (hx : ¬ ∃ z : K, z ^ p = x) :
    ¬ ∃ y : K, y ^ p = g ^ (p * N) * x := by
  intro hmul
  exact hx (exists_pth_root_of_mul_pth_power hg hmul)

/-- Helper for Lemma 15.48.5: the factorization package from Lemma `10.115.7` already contains
the away-localization bijectivity needed later in the proof. -/
lemma polynomial_factorization_away_bijective_for_subalgebra
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {d : ℕ} {S' : Subalgebra R S} {φ : MvPolynomial (Fin d) R →ₐ[R] S'} {g : R}
    (hfac : IsInjectivePolynomialFactorizationAway d S' φ g) :
    Function.Bijective (Localization.awayMapₐ S'.val (algebraMap R S' g)) :=
  hfac.awayMap_bijective

/-- Helper for Lemma 15.48.5: a nonzero Kähler differential can be detected by a derivation. -/
lemma exists_derivation_nonzero_of_differential_ne_zero
    {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K] {a : K}
    (ha : D k K a ≠ 0) :
    ∃ θ : Derivation k K K, θ a ≠ 0 := by
  classical
  let hs : LinearIndepOn K id ({D k K a} : Set Ω[K⁄k]) := by
    change LinearIndependent K (fun x : ({D k K a} : Set Ω[K⁄k]) ↦ (x : Ω[K⁄k]))
    rw [linearIndependent_unique_iff]
    simpa using ha
  let hst : ({D k K a} : Set Ω[K⁄k]) ⊆ Set.range (D k K) := by
    intro ω hω
    rcases Set.mem_singleton_iff.mp hω with rfl
    exact ⟨a, rfl⟩
  let ht : ⊤ ≤ Submodule.span K (Set.range (D k K)) := by
    rw [KaehlerDifferential.span_range_derivation k K]
  let b : Module.Basis (↑(hs.extend hst)) K Ω[K⁄k] := Module.Basis.extendLe hs hst ht
  have hsubset : ({D k K a} : Set Ω[K⁄k]) ⊆ ↑(hs.extend hst) := by
    -- The extended basis still contains the original singleton differential.
    intro ω hω
    exact LinearIndepOn.subset_extend hs hst hω
  let ei : ↑(hs.extend hst) := ⟨D k K a, hsubset (by simp)⟩
  let coord : Ω[K⁄k] →ₗ[K] K := (Finsupp.lapply ei).comp b.repr.toLinearMap
  let θ : Derivation k K K := (LinearMap.compDer coord) (D k K)
  have hb_apply (u : ↑(hs.extend hst)) : b u = u := by
    -- The `extendLe` basis is indexed by its underlying set, so evaluating the basis at `u`
    -- returns the vector represented by that index.
    simpa [b] using congrArg (fun f ↦ f u) (Module.Basis.coe_extendLe hs hst ht)
  have hcoord (u : ↑(hs.extend hst)) : coord (u : Ω[K⁄k]) = if u = ei then 1 else 0 := by
    -- The chosen coordinate functional is the Kronecker delta on the extended basis.
    calc
      coord (u : Ω[K⁄k]) =
          (Finsupp.lapply (R := K) (M := K) ei) (b.repr (b u)) := by
        simp [coord, hb_apply]
      _ = (Finsupp.lapply (R := K) (M := K) ei) (Finsupp.single u (1 : K)) := by
        rw [Module.Basis.repr_self]
      _ = (Finsupp.single u (1 : K)) ei := by
        rw [Finsupp.lapply_apply]
      _ = if u = ei then 1 else 0 := by
        by_cases h : u = ei
        · subst h
          rw [Finsupp.single_eq_same]
          rw [if_pos rfl]
        · have hei : ei ≠ u := by
            intro hEq
            exact h hEq.symm
          rw [Finsupp.single_eq_of_ne hei, if_neg h]
  refine ⟨θ, ?_⟩
  have hθa : θ a = 1 := by
    -- Evaluating the detecting derivation on `a` reads the chosen coordinate of `da`.
    calc
      θ a = coord (D k K a) := by
        rfl
      _ = if ei = ei then 1 else 0 := by
        exact hcoord ei
      _ = 1 := by
        rw [if_pos rfl]
  rw [hθa]
  exact one_ne_zero

/-- Helper for Lemma 15.48.5: finitely many fraction-field elements admit one common nonzero
denominator in the source domain. -/
lemma exists_common_nonzero_denominator
    {ι : Type*} [Fintype ι] {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K]
    (u : ι → K) :
    ∃ c : B, c ≠ 0 ∧ ∀ i, ∃ v : B, algebraMap B K v = algebraMap B K c * u i := by
  classical
  choose num den hden hrepr using fun i ↦ IsFractionRing.div_surjective B (u i)
  let c : B := ∏ i, den i
  have hden_ne_zero : ∀ i, den i ≠ 0 := by
    intro i hzero
    have hreg := (mem_nonZeroDivisors_iff.mp (hden i)).1
    have hone : (1 : B) = 0 := by
      apply hreg 1
      simpa [hzero]
    exact one_ne_zero hone
  have hc : c ≠ 0 := by
    -- The common denominator is a product of nonzero factors in the domain `B`.
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hden_ne_zero i
  refine ⟨c, hc, ?_⟩
  intro i
  let v : B := Finset.prod (Finset.univ.erase i) den * num i
  refine ⟨v, ?_⟩
  have hdenK : algebraMap B K (den i) ≠ 0 := by
    intro hzero
    have hzero' : algebraMap B K (den i) = algebraMap B K 0 := by
      simpa using hzero
    exact hden_ne_zero i ((IsFractionRing.injective B K) hzero')
  have hcross : algebraMap B K (den i) * u i = algebraMap B K (num i) := by
    have hrepr' := hrepr i
    rw [div_eq_iff hdenK] at hrepr'
    simpa [mul_comm] using hrepr'.symm
  have hprod : Finset.prod (Finset.univ.erase i) den * den i = c := by
    simpa [c] using Finset.prod_erase_mul (Finset.univ : Finset ι) den (by simp : i ∈ Finset.univ)
  -- Move the individual denominator `den i` into the common product `c`.
  calc
    algebraMap B K v =
        algebraMap B K (Finset.prod (Finset.univ.erase i) den) * algebraMap B K (num i) := by
      simp [v, mul_comm, mul_left_comm, mul_assoc]
    _ =
        algebraMap B K (Finset.prod (Finset.univ.erase i) den) *
          (algebraMap B K (den i) * u i) := by
      rw [hcross]
    _ = (algebraMap B K (Finset.prod (Finset.univ.erase i) den) * algebraMap B K (den i)) * u i := by
      ac_rfl
    _ = algebraMap B K c * u i := by
      rw [← map_mul, hprod]

/-- Helper for Lemma 15.48.5: once a scaled fraction-field derivation lands in the ring on a
generating set, it lands in the ring on the whole adjoined subalgebra. -/
lemma scaled_derivation_value_of_algebraMap
    {A : Type*} [CommRing A] [Algebra A B] {K : Type*} [Field K] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] (θ : Derivation A K K) (c : B) (a : A) :
    ∃ y : B, algebraMap B K y = algebraMap B K c * θ (algebraMap B K (algebraMap A B a)) := by
  refine ⟨0, ?_⟩
  -- Proof comment: scalars from `A` have zero derivative, so the zero witness already works once
  -- the tower map `A → B → K` is normalized to the direct map `A → K`.
  calc
    algebraMap B K (0 : B) = 0 := by
      simp
    _ = algebraMap B K c * θ (algebraMap A K a) := by
      rw [θ.map_algebraMap]
      simp
    _ = algebraMap B K c * θ (algebraMap B K (algebraMap A B a)) := by
      rw [IsScalarTower.algebraMap_eq A B K]
      simp [RingHom.comp_apply]

/-- Helper for Lemma 15.48.5: once a scaled fraction-field derivation lands in the ring on a
generating set, it lands in the ring on the whole adjoined subalgebra. -/
lemma exists_scaled_derivation_value_in_adjoin
    {A : Type*} [CommRing A] [Algebra A B] {K : Type*} [Field K] [Algebra B K] [Algebra A K]
    [IsScalarTower A B K] (θ : Derivation A K K) (c : B) {s : Set B}
    (hs : ∀ x ∈ s, ∃ y : B, algebraMap B K y = algebraMap B K c * θ (algebraMap B K x)) :
    ∀ x ∈ Algebra.adjoin A s, ∃ y : B,
      algebraMap B K y = algebraMap B K c * θ (algebraMap B K x) := by
  intro x hx
  -- Route correction: the previous attempt stalled on the scalar branch. We now normalize the
  -- tower map there first, then run the source-faithful adjoin induction unchanged.
  refine Algebra.adjoin_induction (s := s)
      (p := fun z _ ↦ ∃ y : B,
        algebraMap B K y = algebraMap B K c * θ (algebraMap B K z))
      ?_ ?_ ?_ ?_ hx
  · intro z hz
    exact hs z hz
  · intro a
    exact scaled_derivation_value_of_algebraMap (B := B) (K := K) θ c a
  · intro x y _ _ hx hy
    rcases hx with ⟨u, hu⟩
    rcases hy with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    -- Proof comment: add the two chosen witnesses and use additivity of both the ring map and
    -- the derivation.
    calc
      algebraMap B K (u + v)
          = algebraMap B K u + algebraMap B K v := by
              simp
      _ = algebraMap B K c * θ (algebraMap B K x) +
            algebraMap B K c * θ (algebraMap B K y) := by
              rw [hu, hv]
      _ = algebraMap B K c *
            (θ (algebraMap B K x) + θ (algebraMap B K y)) := by
              ring
      _ = algebraMap B K c * θ (algebraMap B K (x + y)) := by
              rw [map_add, θ.map_add]
  · intro x y _ _ hx hy
    rcases hx with ⟨u, hu⟩
    rcases hy with ⟨v, hv⟩
    refine ⟨u * y + x * v, ?_⟩
    -- Proof comment: the witness `u * y + x * v` is exactly the Leibniz combination of the two
    -- scaled values.
    calc
      algebraMap B K (u * y + x * v)
          = algebraMap B K u * algebraMap B K y +
              algebraMap B K x * algebraMap B K v := by
                simp [map_add, map_mul]
      _ = (algebraMap B K c * θ (algebraMap B K x)) * algebraMap B K y +
            algebraMap B K x * (algebraMap B K c * θ (algebraMap B K y)) := by
              rw [hu, hv]
      _ = algebraMap B K c *
            (θ (algebraMap B K x) * algebraMap B K y +
              algebraMap B K x * θ (algebraMap B K y)) := by
              ring
      _ = algebraMap B K c * θ (algebraMap B K (x * y)) := by
              rw [map_mul, Derivation.leibniz]
              ring

/-- Helper for Lemma 15.48.5: a fraction-field derivation over a finite-type domain can be scaled
so that all of its values on the domain land back in the domain. -/
lemma exists_scaled_fractionField_derivation_values_in_ring_of_finiteType
    {A : Type*} [CommRing A] [Algebra A B] [Algebra.FiniteType A B]
    {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    (θ : Derivation A K K) :
    ∃ c : B, c ≠ 0 ∧ ∀ x : B, ∃ y : B,
      algebraMap B K y = algebraMap B K c * θ (algebraMap B K x) := by
  classical
  let S : Subalgebra A B := ⊤
  let e : S ≃ₐ[A] B := Subalgebra.topEquiv
  have hSft : Algebra.FiniteType A S := by
    exact Algebra.FiniteType.of_surjective (R := A) e.symm.toAlgHom e.symm.surjective
  have hSfg : S.FG := (Subalgebra.fg_iff_finiteType S).2 hSft
  rcases (Subalgebra.fg_def.mp hSfg) with ⟨t, htfin, htop⟩
  let s : Finset B := htfin.toFinset
  have hs_top : Algebra.adjoin A (↑s : Set B) = ⊤ := by
    simpa [s] using htop
  obtain ⟨c, hc, hden⟩ := exists_common_nonzero_denominator
      (B := B) (K := K) (u := fun x : s ↦ θ (algebraMap B K x))
  refine ⟨c, hc, ?_⟩
  intro x
  have hs :
      ∀ z ∈ (↑s : Set B), ∃ y : B,
        algebraMap B K y = algebraMap B K c * θ (algebraMap B K z) := by
    intro z hz
    have hz' : z ∈ s := by
      simpa using hz
    rcases hden ⟨z, hz'⟩ with ⟨y, hy⟩
    exact ⟨y, by simpa using hy⟩
  have hx : x ∈ Algebra.adjoin A (↑s : Set B) := by
    simpa [hs_top] using (show x ∈ (⊤ : Subalgebra A B) from by simp)
  exact exists_scaled_derivation_value_in_adjoin (B := B) (K := K) θ c hs x hx

/-- Helper for Lemma 15.48.5: a fraction-field derivation on a finite-type domain descends, after
clearing denominators, to a derivation of the domain itself. -/
lemma exists_derivation_nonzero_apply_of_fractionField_derivation
    {A : Type*} [CommRing A] [Algebra A B] [Algebra.FiniteType A B]
    {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    (f : B) (θ : Derivation A K K) (hθf : θ (algebraMap B K f) ≠ 0) :
    ∃ D : Derivation A B B, D f ≠ 0 := by
  classical
  obtain ⟨c, hc, hscaled⟩ :=
    exists_scaled_fractionField_derivation_values_in_ring_of_finiteType
      (B := B) (K := K) θ
  choose D0 hD0 using hscaled
  have hadd : ∀ x y : B, D0 (x + y) = D0 x + D0 y := by
    intro x y
    apply (IsFractionRing.injective B K)
    -- Proof comment: after mapping to the fraction field, additivity becomes the already-proved
    -- equality for the scaled fraction-field values.
    calc
      algebraMap B K (D0 (x + y))
          = algebraMap B K c * θ (algebraMap B K (x + y)) := hD0 (x + y)
      _ = algebraMap B K c *
            (θ (algebraMap B K x) + θ (algebraMap B K y)) := by
              rw [map_add, θ.map_add]
      _ = algebraMap B K (D0 x) + algebraMap B K (D0 y) := by
              rw [hD0 x, hD0 y]
              ring
      _ = algebraMap B K (D0 x + D0 y) := by
              simp
  have hsmul : ∀ a : A, ∀ x : B, D0 (a • x) = a • D0 x := by
    intro a x
    apply (IsFractionRing.injective B K)
    -- Proof comment: the source-ring scalar acts through `A → K`, and the fraction-field
    -- derivation is `A`-linear.
    calc
      algebraMap B K (D0 (a • x))
          = algebraMap B K c * θ (algebraMap B K (a • x)) := hD0 (a • x)
      _ = algebraMap B K c * θ (algebraMap B K ((algebraMap A B a) * x)) := by
              rw [Algebra.smul_def]
      _ = algebraMap B K c * θ (algebraMap B K (algebraMap A B a) * algebraMap B K x) := by
              rw [map_mul]
      _ = algebraMap B K c * θ ((algebraMap A K a) * algebraMap B K x) := by
              simp [IsScalarTower.algebraMap_eq A B K, RingHom.comp_apply]
      _ = algebraMap B K c * ((algebraMap A K a) * θ (algebraMap B K x)) := by
              rw [Derivation.leibniz, θ.map_algebraMap]
              simp
      _ = (algebraMap A K a) * (algebraMap B K c * θ (algebraMap B K x)) := by
              ring
      _ = (algebraMap A K a) * algebraMap B K (D0 x) := by
              rw [hD0 x]
      _ = algebraMap B K ((algebraMap A B a) * D0 x) := by
              rw [map_mul]
              simp [IsScalarTower.algebraMap_eq A B K, RingHom.comp_apply]
      _ = algebraMap B K (a • D0 x) := by
              rw [Algebra.smul_def]
  have hmul : ∀ x y : B, D0 (x * y) = x • D0 y + y • D0 x := by
    intro x y
    apply (IsFractionRing.injective B K)
    -- Proof comment: the chosen preimages satisfy the same Leibniz identity after mapping to the
    -- fraction field, and injectivity pulls that identity back to `B`.
    calc
      algebraMap B K (D0 (x * y))
          = algebraMap B K c * θ (algebraMap B K (x * y)) := hD0 (x * y)
      _ = algebraMap B K c *
            (algebraMap B K x * θ (algebraMap B K y) +
              algebraMap B K y * θ (algebraMap B K x)) := by
              rw [map_mul, Derivation.leibniz]
              simp [Algebra.smul_def]
      _ = algebraMap B K x * algebraMap B K (D0 y) +
            algebraMap B K y * algebraMap B K (D0 x) := by
              rw [hD0 x, hD0 y]
              ring
      _ = algebraMap B K (x • D0 y + y • D0 x) := by
              simp [Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
  let Dlin : B →ₗ[A] B :=
    { toFun := D0
      map_add' := hadd
      map_smul' := hsmul }
  have hone : Dlin 1 = 0 := by
    apply (IsFractionRing.injective B K)
    -- Proof comment: the derivation of `1` vanishes in the fraction field, so the chosen
    -- preimage of the scaled value at `1` must be zero.
    calc
      algebraMap B K (Dlin 1) = algebraMap B K c * θ (algebraMap B K (1 : B)) := hD0 1
      _ = 0 := by
            simp
      _ = algebraMap B K (0 : B) := by
            simp
  let D : Derivation A B B := Derivation.mk Dlin hone hmul
  refine ⟨D, ?_⟩
  have hD_apply (x : B) : D x = D0 x := rfl
  have hcK : algebraMap B K c ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap B K) (IsFractionRing.injective B K)).2 hc
  intro hDf
  have hprod : algebraMap B K c * θ (algebraMap B K f) = 0 := by
    rw [← hD0 f, ← hD_apply f, hDf]
    simp
  exact hθf ((mul_eq_zero.mp hprod).resolve_left hcK)

/-- Helper for Lemma 15.48.5: quotienting the original complete-local source by the kernel of
its map to `B` produces an injective complete-local domain source without changing the finite-type
setup. -/
lemma exists_domain_completeLocal_source_of_hB
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (hB :
      ∃ (R : Type v) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : IsCompleteLocalRing R)
        (_ : Algebra R B), Algebra.FiniteType R B) :
    ∃ (R : Type v) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R)
      (_ : IsCompleteLocalRing R) (_ : Algebra R B) (_ : Algebra.FiniteType R B),
      Function.Injective (algebraMap R B) := by
  rcases hB with ⟨R₀, _, _, _, _, hft⟩
  let I : Ideal R₀ := RingHom.ker (algebraMap R₀ B)
  let R : Type v := R₀ ⧸ I
  letI : CommRing R := inferInstance
  have hI : I ≠ ⊤ := RingHom.ker_ne_top (algebraMap R₀ B)
  letI : IsCompleteLocalRing R := quotient_isCompleteLocalRing I hI
  letI : IsNoetherianRing R := inferInstance
  haveI : I.IsPrime := by
    -- The kernel is prime because it is the kernel of a map into the domain `B`.
    simpa [I] using (RingHom.ker_isPrime (algebraMap R₀ B))
  letI : IsDomain R := inferInstance
  let φ : R →ₐ[R₀] B := Ideal.kerLiftAlg (Algebra.ofId R₀ B)
  letI : Algebra R B := φ.toRingHom.toAlgebra
  letI : IsScalarTower R₀ R B := by
    refine ⟨?_⟩
    intro r x y
    -- The quotient comparison map is an `R₀`-algebra map, so the two scalar actions agree
    -- after rewriting everything through the corresponding algebra maps.
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
    have hcomm : algebraMap R B (algebraMap R₀ R r) = algebraMap R₀ B r := by
      simpa [φ, RingHom.algebraMap_toAlgebra] using φ.commutes r
    rw [hcomm]
    ring
  letI : Algebra.FiniteType R B :=
    Algebra.FiniteType.of_restrictScalars_finiteType R₀ R B
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  -- Proof comment: the quotient-by-kernel comparison map is the canonical injective map from the
  -- source image into `B`.
  simpa [φ, RingHom.algebraMap_toAlgebra] using
    (Ideal.kerLiftAlg_injective (Algebra.ofId R₀ B))

/-- Helper for Lemma 15.48.5: the universal differential of `f` in the fraction field is nonzero
whenever `f` is not a `p`th power there. -/
lemma fractionField_differential_ne_zero_of_not_exists_pth_root
    (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K] [CharP K p]
    [Algebra (ZMod p) K] (f : B) (hf : ¬ ∃ g : K, g ^ p = algebraMap B K f) :
    D (ZMod p) K (algebraMap B K f) ≠ 0 := by
  -- Proof comment: Lemma `10.158.2` identifies vanishing of the absolute differential over
  -- `𝔽_p` with being a `p`th power in the fraction field.
  intro hzero
  exact hf <|
    (kaehlerDifferential_eq_zero_iff_exists_pth_root
      (k := ZMod p) (K := K) (a := algebraMap B K f)).1 hzero

/-- Helper for Lemma 15.48.5: the nonzero absolute differential of `f` in the fraction field
produces a fraction-field derivation that does not kill `f`. -/
lemma exists_fractionField_absolute_derivation_nonzero_apply_of_not_exists_pth_root
    (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [Algebra B K] [IsFractionRing B K] [CharP K p]
    [Algebra (ZMod p) K] (f : B) (hf : ¬ ∃ g : K, g ^ p = algebraMap B K f) :
    ∃ θ : Derivation (ZMod p) K K, θ (algebraMap B K f) ≠ 0 := by
  -- Proof comment: once the universal differential is known to be nonzero, the coordinate-picking
  -- argument above turns it into a detecting derivation.
  have hdf_ne : D (ZMod p) K (algebraMap B K f) ≠ 0 :=
    fractionField_differential_ne_zero_of_not_exists_pth_root (B := B) (K := K) p f hf
  exact exists_derivation_nonzero_of_differential_ne_zero
    (k := ZMod p) (K := K) (a := algebraMap B K f) hdf_ne

/-- Helper for Lemma 15.48.5: a bijective ring homomorphism identifies ring characteristics. -/
private theorem ringChar_eq_of_bijective
    {R : Type*} {S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) (hf : Function.Bijective f) :
    ringChar R = ringChar S := by
  -- Pull the characteristic relation back along injectivity and forward along the ring map.
  apply Nat.dvd_antisymm
  · have hzeroS : ((ringChar S : ℕ) : S) = 0 :=
      (ringChar.spec S (ringChar S)).2 dvd_rfl
    have hmap : f ((ringChar S : ℕ) : R) = f 0 := by
      simpa using hzeroS
    have hzeroR : ((ringChar S : ℕ) : R) = 0 := hf.1 hmap
    exact (ringChar.spec R (ringChar S)).mp hzeroR
  · have hzeroR : ((ringChar R : ℕ) : R) = 0 :=
      (ringChar.spec R (ringChar R)).2 dvd_rfl
    have hzeroS' : f ((ringChar R : ℕ) : R) = 0 := by
      rw [hzeroR]
      simp
    have hmapNat : f ((ringChar R : ℕ) : R) = ((ringChar R : ℕ) : S) := by
      rw [map_natCast]
    have hzeroS : ((ringChar R : ℕ) : S) = 0 := by
      rw [hmapNat] at hzeroS'
      exact hzeroS'
    exact (ringChar.spec S (ringChar R)).mp hzeroS

/-- Helper for Lemma 15.48.5: an injective regular complete-local source inside a
characteristic-`p` domain is in equal characteristic, hence isomorphic to a finite-variable power
series ring over its residue field. -/
lemma exists_fin_mvPowerSeries_ringEquiv_of_injective_regular_completeLocal
    {R : Type*} [CommRing R] [IsCompleteLocalRing R] [IsRegularLocalRing R] [Algebra R B]
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (hinj : Function.Injective (algebraMap R B)) :
    ∃ d : ℕ, Nonempty (MvPowerSeries (Fin d) (IsLocalRing.ResidueField R) ≃+* R) := by
  letI : CharP R p := RingHom.charP (algebraMap R B) hinj p
  letI : CharP (IsLocalRing.ResidueField R) p :=
    CharP.quotient' p (IsLocalRing.maximalIdeal R) fun n hn ↦ by
      by_contra hnat
      have hnotunit : ¬ IsUnit (n : R) := by
        simpa [IsLocalRing.mem_maximalIdeal] using hn
      have hnotdvd : ¬ p ∣ n := by
        simpa [CharP.cast_eq_zero_iff R p n] using hnat
      exact hnotunit ((CharP.isUnit_natCast_iff (R := R) (p := p) (Fact.out)).2 hnotdvd)
  have heqchar : ringChar R = ringChar (IsLocalRing.ResidueField R) := by
    -- Both the regular source and its residue field have characteristic `p`, so the equal-
    -- characteristic presentation theorem applies.
    calc
      ringChar R = p := by
        simpa using (ringChar.eq R p)
      _ = ringChar (IsLocalRing.ResidueField R) := by
        symm
        simpa using (ringChar.eq (IsLocalRing.ResidueField R) p)
  obtain ⟨σ, _, hσ⟩ :=
    exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic (R := R) heqchar
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  rcases hσ with ⟨eσ⟩
  refine ⟨Fintype.card σ, ?_⟩
  -- Reindex the abstract finite variable set by `Fin d` to match the chapter's local API.
  refine ⟨(MvPowerSeries.renameEquiv (IsLocalRing.ResidueField R)
    (Fintype.equivFin σ).symm).toRingEquiv.trans eσ⟩

/-- Helper for Lemma 15.48.5: the away-localization bijectivity from the polynomial factorization
lets us clear a denominator and replace `f` by a numerator lying in the intermediate subalgebra,
after enlarging the exponent so it is divisible by `p`. -/
lemma exists_cleared_preimage_in_factorization_away
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : ℕ) [Fact p.Prime] {S' : Subalgebra R S} {g : R}
    (hAway : Function.Bijective (Localization.awayMapₐ S'.val (algebraMap R S' g)))
    (f : S) :
    ∃ N : ℕ, ∃ f' : S',
      (Localization.awayMapₐ S'.val (algebraMap R S' g))
          (algebraMap S' (Localization.Away (algebraMap R S' g)) f') =
        algebraMap S (Localization.Away (algebraMap R S g))
          ((algebraMap R S g) ^ (p * N) * f) := by
  let g' : S' := algebraMap R S' g
  let ψ : Localization.Away g' →ₐ[R] Localization.Away (algebraMap R S g) :=
    Localization.awayMapₐ S'.val g'
  obtain ⟨z, hz⟩ := hAway.2 (algebraMap S (Localization.Away (algebraMap R S g)) f)
  obtain ⟨n, a, hza⟩ := IsLocalization.Away.surj g' z
  let f' : S' := (g' ^ (n * (p - 1))) * a
  refine ⟨n, f', ?_⟩
  have hp_pos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  haveI : IsLocalization (Submonoid.powers g') (Localization.Away g') := inferInstance
  have hy :
      Submonoid.powers g' ≤
        Submonoid.comap (S'.val : S' →+* S) (Submonoid.powers (algebraMap R S g)) := by
    intro y hy'
    rcases hy' with ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    simp [g']
  have hψ_alg (x : S') :
      ψ (algebraMap S' (Localization.Away g') x) =
        algebraMap S (Localization.Away (algebraMap R S g)) (x : S) := by
    rw [show algebraMap S' (Localization.Away g') x =
        IsLocalization.mk' (Localization.Away g') x (1 : Submonoid.powers g') by
        rw [IsLocalization.mk'_one]]
    change IsLocalization.map (Localization.Away (algebraMap R S g)) (S'.val : S' →+* S) hy
        (IsLocalization.mk' (Localization.Away g') x (1 : Submonoid.powers g')) = _
    rw [IsLocalization.map_mk' (Q := Localization.Away (algebraMap R S g)) hy]
    show IsLocalization.mk' (Localization.Away (algebraMap R S g)) (x : S)
        (1 : Submonoid.powers (algebraMap R S g)) =
      algebraMap S (Localization.Away (algebraMap R S g)) (x : S)
    rw [IsLocalization.mk'_one]
  have hz' : ψ z = algebraMap S (Localization.Away (algebraMap R S g)) f := by
    simpa [ψ, g'] using hz
  have hgpow :
      ψ (algebraMap S' (Localization.Away g') g' ^ n) =
        algebraMap S (Localization.Away (algebraMap R S g)) ((algebraMap R S g) ^ n) := by
    calc
      ψ (algebraMap S' (Localization.Away g') g' ^ n) =
          ψ (algebraMap S' (Localization.Away g') g') ^ n := by
            rw [map_pow]
      _ =
          (algebraMap S (Localization.Away (algebraMap R S g)) ((g' : S))) ^ n := by
            rw [hψ_alg]
      _ =
          algebraMap S (Localization.Away (algebraMap R S g)) ((algebraMap R S g) ^ n) := by
            simp [g', map_pow]
  have hmap' :
      ψ z * algebraMap S (Localization.Away (algebraMap R S g)) ((algebraMap R S g) ^ n) =
        algebraMap S (Localization.Away (algebraMap R S g)) (a : S) := by
    -- Apply the away comparison map to the numerator equation and normalize its effect on
    -- numerators from `S'`.
    have hmap0 : ψ (z * algebraMap S' (Localization.Away g') g' ^ n) =
        ψ (algebraMap S' (Localization.Away g') a) := congrArg ψ hza
    calc
      ψ z * algebraMap S (Localization.Away (algebraMap R S g)) ((algebraMap R S g) ^ n) =
          ψ z * ψ (algebraMap S' (Localization.Away g') g' ^ n) := by
            rw [hgpow]
      _ = ψ (algebraMap S' (Localization.Away g') a) := by
            simpa [map_mul] using hmap0
      _ = algebraMap S (Localization.Away (algebraMap R S g)) (a : S) := hψ_alg a
  have hza_image :
      algebraMap S (Localization.Away (algebraMap R S g)) (a : S) =
        algebraMap S (Localization.Away (algebraMap R S g))
          ((algebraMap R S g) ^ n * f) := by
    -- Applying the away-map to the normalized numerator equation identifies `a`
    -- with the expected `g^n * f` in the target localization.
    calc
      algebraMap S (Localization.Away (algebraMap R S g)) (a : S) =
          ψ z * algebraMap S (Localization.Away (algebraMap R S g))
            ((algebraMap R S g) ^ n) := by
            exact hmap'.symm
      _ = algebraMap S (Localization.Away (algebraMap R S g)) f *
            algebraMap S (Localization.Away (algebraMap R S g))
              ((algebraMap R S g) ^ n) := by
            rw [hz']
      _ = algebraMap S (Localization.Away (algebraMap R S g))
            (((algebraMap R S g) ^ n) * f) := by
            rw [map_mul]
            ring
  have hpow_index : n * (p - 1) + n = p * n := by
    calc
      n * (p - 1) + n = n * (p - 1) + n * 1 := by rw [Nat.mul_one]
      _ = n * ((p - 1) + 1) := by rw [Nat.mul_add]
      _ = n * p := by rw [Nat.sub_add_cancel hp_pos]
      _ = p * n := by rw [Nat.mul_comm]
  -- Multiply the chosen numerator by the complementary power of `g` so that the total
  -- exponent becomes a multiple of `p`.
  calc
    ψ (algebraMap S' (Localization.Away g') f') =
        algebraMap S (Localization.Away (algebraMap R S g)) (f' : S) := by
            exact hψ_alg f'
    _ =
        algebraMap S (Localization.Away (algebraMap R S g))
          ((algebraMap R S g) ^ (n * (p - 1)) * (a : S)) := by
            simp [f', g']
    _ =
        algebraMap S (Localization.Away (algebraMap R S g))
          ((algebraMap R S g) ^ (n * (p - 1))) *
          algebraMap S (Localization.Away (algebraMap R S g)) ((a : S)) := by
            rw [map_mul]
    _ =
        algebraMap S (Localization.Away (algebraMap R S g))
          ((algebraMap R S g) ^ (n * (p - 1))) *
          algebraMap S (Localization.Away (algebraMap R S g))
            (((algebraMap R S g) ^ n) * f) := by
            rw [hza_image]
    _ =
        algebraMap S (Localization.Away (algebraMap R S g))
          (((algebraMap R S g) ^ (n * (p - 1))) * (((algebraMap R S g) ^ n) * f)) := by
            rw [← map_mul]
    _ =
        algebraMap S (Localization.Away (algebraMap R S g))
          ((((algebraMap R S g) ^ (n * (p - 1))) * (algebraMap R S g) ^ n) * f) := by
            ring
    _ =
        algebraMap S (Localization.Away (algebraMap R S g))
          ((algebraMap R S g) ^ (n * (p - 1) + n) * f) := by
            rw [← pow_add]
    _ =
        algebraMap S (Localization.Away (algebraMap R S g))
          ((algebraMap R S g) ^ (p * n) * f) := by
            rw [hpow_index]

/-- Helper for Lemma 15.48.5: once the cleared numerator `f'` from the away factorization is
identified with `g^(pN) * f` in the target localization, any `p`th root of `f'` in the
intermediate fraction field would force a `p`th root of `f` in the ambient fraction field. -/
lemma not_exists_pth_root_of_cleared_preimage_in_factorization_away
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    (p : ℕ) [Fact p.Prime] {S' : Subalgebra R S} {g : R}
    (hg : algebraMap R S g ≠ 0) {f : S} {N : ℕ} {f' : S'}
    (hf : ¬ ∃ z : FractionRing S, z ^ p = algebraMap S (FractionRing S) f)
    (hf'away :
      (Localization.awayMapₐ S'.val (algebraMap R S' g))
          (algebraMap S' (Localization.Away (algebraMap R S' g)) f') =
        algebraMap S (Localization.Away (algebraMap R S g))
          ((algebraMap R S g) ^ (p * N) * f)) :
    ¬ ∃ z : FractionRing S', z ^ p = algebraMap S' (FractionRing S') f' := by
  intro hroot
  let j : FractionRing S' →+* FractionRing S :=
    IsFractionRing.map (show Function.Injective S'.val from Subtype.coe_injective)
  let χ : Localization.Away (algebraMap R S g) →+* FractionRing S :=
    IsLocalization.lift
      (M := Submonoid.powers (algebraMap R S g))
      (S := Localization.Away (algebraMap R S g))
      (g := algebraMap S (FractionRing S))
      (by
        intro y
        rcases y.property with ⟨n, rfl⟩
        refine isUnit_iff_ne_zero.mpr ?_
        exact pow_ne_zero n <|
          (map_ne_zero_iff (algebraMap S (FractionRing S))
            (IsFractionRing.injective S (FractionRing S))).2 hg)
  have hjf' :
      j (algebraMap S' (FractionRing S') f') =
        algebraMap S (FractionRing S) (f' : S) := by
    -- The induced fraction-field map extends the original inclusion `S' ↪ S`.
    simp [j]
  have hχ_num (x : S) :
      χ (algebraMap S (Localization.Away (algebraMap R S g)) x) =
        algebraMap S (FractionRing S) x := by
    -- Evaluate the localization-to-fraction-field map on a numerator.
    rw [show algebraMap S (Localization.Away (algebraMap R S g)) x =
        IsLocalization.mk' (Localization.Away (algebraMap R S g)) x
          (1 : Submonoid.powers (algebraMap R S g)) by
        rw [IsLocalization.mk'_one]]
    rw [IsLocalization.lift_mk']
    simp [χ]
  have hχ_away :
      χ ((Localization.awayMapₐ S'.val (algebraMap R S' g))
          (algebraMap S' (Localization.Away (algebraMap R S' g)) f')) =
        algebraMap S (FractionRing S) (f' : S) := by
    -- The away comparison map preserves numerators, and then `χ` embeds the target localization
    -- into the ambient fraction field.
    rw [show (Localization.awayMapₐ S'.val (algebraMap R S' g))
        (algebraMap S' (Localization.Away (algebraMap R S' g)) f') =
          algebraMap S (Localization.Away (algebraMap R S g)) (f' : S) by
        rfl]
    exact hχ_num (f' : S)
  have hf'_frac :
      algebraMap S (FractionRing S) (f' : S) =
        algebraMap S (FractionRing S) ((algebraMap R S g) ^ (p * N) * f) := by
    -- Pass the localization equality to the fraction field of `S`.
    have hloc := congrArg χ hf'away
    simpa [hχ_away, hχ_num] using hloc
  rcases hroot with ⟨z, hz⟩
  have hz_map :
      (j z) ^ p = algebraMap S (FractionRing S) (f' : S) := by
    -- Map the hypothetical `p`th root from `FractionRing S'` into `FractionRing S`.
    calc
      (j z) ^ p = j (z ^ p) := by
        rw [map_pow]
      _ = j (algebraMap S' (FractionRing S') f') := by
        rw [hz]
      _ = algebraMap S (FractionRing S) (f' : S) := hjf'
  have hgK :
      algebraMap S (FractionRing S) (algebraMap R S g) ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap S (FractionRing S))
      (IsFractionRing.injective S (FractionRing S))).2 hg
  have hmul :
      ∃ y : FractionRing S,
        y ^ p =
          (algebraMap S (FractionRing S) (algebraMap R S g)) ^ (p * N) *
            algebraMap S (FractionRing S) f := by
    refine ⟨j z, ?_⟩
    calc
      (j z) ^ p = algebraMap S (FractionRing S) (f' : S) := hz_map
      _ = algebraMap S (FractionRing S) ((algebraMap R S g) ^ (p * N) * f) := hf'_frac
      _ =
          (algebraMap S (FractionRing S) (algebraMap R S g)) ^ (p * N) *
            algebraMap S (FractionRing S) f := by
          rw [map_mul, map_pow]
  exact
    not_exists_pth_root_of_mul_pth_power
      (K := FractionRing S) (p := p) (N := N)
      (g := algebraMap S (FractionRing S) (algebraMap R S g))
      (x := algebraMap S (FractionRing S) f) hgK hf hmul

/-- Helper for Lemma 15.48.5: the explicit power-series model for `R₀` transports coefficients of
the polynomial ring by a ring equivalence. -/
lemma mvPolynomial_over_powerSeries_ringEquiv_of_model
    {R₀ : Type*} [CommRing R₀] [IsLocalRing R₀]
    {d n : ℕ}
    (e : MvPowerSeries (Fin n) (IsLocalRing.ResidueField R₀) ≃+* R₀) :
    Nonempty
      (MvPolynomial (Fin d) (MvPowerSeries (Fin n) (IsLocalRing.ResidueField R₀)) ≃+*
        MvPolynomial (Fin d) R₀) := by
  -- Proof comment: coefficient transport along a ring equivalence is bijective on polynomial
  -- algebras because `MvPolynomial.map` is injective and surjective along injective/surjective
  -- coefficient maps.
  refine ⟨RingEquiv.ofBijective (MvPolynomial.map e.toRingHom) ?_⟩
  exact ⟨MvPolynomial.map_injective e.toRingHom e.injective,
    MvPolynomial.map_surjective e.toRingHom e.surjective⟩

/-- Helper for Lemma 15.48.5: composing the polynomial factorization with the transported
coefficient equivalence yields the mixed-model finite injective ring map into `S'`. -/
lemma finite_mixed_model_of_powerSeries_equiv
    {R₀ : Type*} [CommRing R₀] [IsLocalRing R₀]
    {S : Type*} [CommRing S] [Algebra R₀ S]
    {d n : ℕ} {S' : Subalgebra R₀ S}
    (e : MvPowerSeries (Fin n) (IsLocalRing.ResidueField R₀) ≃+* R₀)
    {φ : MvPolynomial (Fin d) R₀ →ₐ[R₀] S'} {g : R₀}
    (hfac : IsInjectivePolynomialFactorizationAway d S' φ g) :
    ∃ ψ : MvPolynomial (Fin d) (MvPowerSeries (Fin n) (IsLocalRing.ResidueField R₀)) →+* S',
      Function.Injective ψ ∧ RingHom.Finite ψ := by
  obtain ⟨ePoly⟩ := mvPolynomial_over_powerSeries_ringEquiv_of_model (R₀ := R₀) (d := d) e
  let ψ :
      MvPolynomial (Fin d) (MvPowerSeries (Fin n) (IsLocalRing.ResidueField R₀)) →+* S' :=
    φ.toRingHom.comp ePoly.toRingHom
  have hψ_injective : Function.Injective ψ := by
    intro x y hxy
    exact ePoly.injective <| hfac.polynomialToIntermediate_injective <| by
      simpa [ψ] using hxy
  have hePoly_finite : RingHom.Finite ePoly.toRingHom := RingEquiv.finite ePoly
  have hφ_finite : RingHom.Finite φ.toRingHom := by
    simpa [AlgHom.Finite, RingHom.Finite] using hfac.polynomialToIntermediate_finite
  have hψ_finite : RingHom.Finite ψ := by
    simpa [ψ] using RingHom.Finite.comp hφ_finite hePoly_finite
  refine ⟨ψ, hψ_injective, hψ_finite⟩

/-- Lemma 15.48.5: if `B` is a domain of characteristic `p` which is of finite type over some
Noetherian complete local ring, and `f` is not a `p`th power in `FractionRing B`, then there
exists a derivation `D : B → B` with `D(f) ≠ 0`. -/
@[stacks 07PH]
theorem exists_derivation_with_nonzero_apply_of_not_exists_pth_root
    (p : ℕ) [Fact p.Prime] [CharP B p]
    (hB :
      ∃ (R : Type v) (_ : CommRing R) (_ : IsNoetherianRing R) (_ : IsCompleteLocalRing R)
        (_ : Algebra R B), Algebra.FiniteType R B)
    (f : B)
    (hf : ¬ ∃ g : FractionRing B, g ^ p = algebraMap B (FractionRing B) f) :
    ∃ D : Derivation ℤ B B, D f ≠ 0 := by
  -- Route correction: the previous attempt kept the arbitrary complete-local source `R`. We first
  -- replace it by an injective domain source and then pass to a finite regular complete-local
  -- subring before rebuilding the polynomial factorization over that regular source.
  obtain ⟨R, _, _, _, _, _, _, hRinj⟩ :=
    exists_domain_completeLocal_source_of_hB (B := B) p hB
  obtain ⟨R₀, hR₀complete, hR₀regular, hR₀local, hR₀res, hRfinite, _⟩ :=
    exists_finite_regular_completeLocalSubring (R := R)
  letI : IsCompleteLocalRing R₀ := hR₀complete
  letI : IsRegularLocalRing R₀ := hR₀regular
  letI : Algebra R₀ B := RingHom.toAlgebra ((algebraMap R B).comp R₀.subtype)
  letI : IsScalarTower R₀ R B := by
    refine ⟨?_⟩
    intro r x y
    -- Normalize both scalar actions to the composite map `R₀ → R → B`.
    rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
    have hcomm : algebraMap R B (algebraMap R₀ R r) = algebraMap R₀ B r := by
      calc
        algebraMap R B (algebraMap R₀ R r) = algebraMap R B ((r : R)) := by
          rfl
        _ = algebraMap R₀ B r := by
          rfl
    rw [hcomm]
    ring
  letI : Algebra.FiniteType R₀ R := hRfinite.finiteType
  letI : Algebra.FiniteType R₀ B := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R₀ R)
    (inferInstance : Algebra.FiniteType R B)
  have hR₀inj : Function.Injective (algebraMap R₀ B) := by
    intro x y hxy
    apply Subtype.ext
    exact hRinj <| by
      simpa [RingHom.algebraMap_toAlgebra] using hxy
  obtain ⟨d, S', φ, g, hfac⟩ :=
    exists_injective_polynomial_factorization_of_injective_finiteType
      (R := R₀) (S := B) hR₀inj
  have hAway :
      Function.Bijective (Localization.awayMapₐ S'.val (algebraMap R₀ S' g)) :=
    polynomial_factorization_away_bijective_for_subalgebra hfac
  obtain ⟨n, ⟨eR₀⟩⟩ :=
    exists_fin_mvPowerSeries_ringEquiv_of_injective_regular_completeLocal
      (B := B) (R := R₀) p hR₀inj
  -- Proof comment: the source-faithful verified frontier is now:
  -- 1. `B` is finite type over the regular complete-local subring `R₀ ⊆ R`,
  -- 2. the finite-type map `R₀ ⟶ B` has been refactored away from the nonzero element `g`,
  -- 3. the equal-characteristic power-series model `eR₀` for `R₀` is now explicit.
  obtain ⟨N, f', hf'away⟩ :=
    exists_cleared_preimage_in_factorization_away (R := R₀) (S := B) p hAway f
  obtain ⟨ψ, hψinj, hψfinite⟩ :=
    finite_mixed_model_of_powerSeries_equiv (R₀ := R₀) (S := B) (d := d) (n := n)
      (S' := S') eR₀ hfac
  --
  -- TODO: the mixed-model transport is now completed by `ψ`. The remaining source-faithful work
  -- is to package the 15.46.4 coefficient-subfield argument over this explicit mixed base so as
  -- to obtain a derivation on `S'` not killing the cleared numerator `f'`, and then extend that
  -- derivation back to `B` using the original away bijectivity `hAway`.
  let _ := d
  let _ := g
  let _ := hAway
  let _ := n
  let _ := N
  let _ := f'
  let _ := hf'away
  let _ := ψ
  let _ := hψinj
  let _ := hψfinite
  sorry

end
