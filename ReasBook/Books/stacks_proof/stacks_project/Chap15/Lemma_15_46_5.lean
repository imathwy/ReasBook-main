import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_46_1
import stacks_proof.stacks_project.Chap15.Lemma_15_46_2
import stacks_proof.stacks_project.Chap10.Lemma_10_158_2
import stacks_proof.stacks_project.Chap10.Lemma_10_97_7

noncomputable section

open MvPowerSeries
open KaehlerDifferential
open scoped FrobeniusSubfield

universe u v w z

/- 
Domain triage:
* primary domain: characteristic-`p` fields with `p`-bases, Frobenius subfields, and the
  canonical `IntermediateField.adjoin`, `expand`, and fraction-field image maps on multivariable
  power-series/polynomial rings;
* sampled owner declarations:
  - `frobeniusSubfield` / `K^[p]`,
  - `IntermediateField.adjoin`,
  - `MvPowerSeries.expand`,
  - `MvPolynomial.expand`,
  - `RingHom.range` / `Subring.subtype`,
  - `IsFractionRing.map`;
* best owner abstraction:
  - `source-facing`: the intrinsic subring `A_J ⊂ A` and its induced fraction subfield `K_J`;
  - `core/canonical`: the coefficient field generated over `k^[p]` by the omitted-basis
    complement via `IntermediateField.adjoin`, together with `RingHom.range` for the fresh-variable
    presentation map and the induced fraction-field map;
  - `bridge/view`: the fresh-variable presentation ring and its map to `A`, which are
    implementation data and should not remain the public owner layer;
* primitive data: the finite variable types `σ` and `τ`, the mixed ambient ring
  `mixedPowerSeriesPolynomialRing σ τ k`, the coefficient intermediate field `k_J`, and the
  intrinsic subring `pthPowerMixedSubring`;
* derived API: the fresh-variable presentation map, the local instances needed to form fraction
  fields, the induced fraction subfields, and the intersection, directedness, and finiteness
  theorems below.
-/

/-- The coefficient intermediate field generated over `k^[p]` by the basis elements `x i` with
`i ∉ J`. -/
private abbrev pbasisComplementField {p : ℕ} [Fact p.Prime] {ι : Type z} [DecidableEq ι]
    (k : Type u) [Field k] [CharP k p] (x : ι → k) (J : Finset ι) :
    IntermediateField (k^[p]) k :=
  IntermediateField.adjoin (k^[p]) (x '' {i | i ∉ J})

/-- The ambient ring `k[[x_i]]_{i ∈ σ}[y_j]_{j ∈ τ}`, modeled as a multivariable polynomial ring
over a multivariable power series ring with finite variable types `σ` and `τ`. -/
abbrev mixedPowerSeriesPolynomialRing (σ : Type v) (τ : Type w) (k : Type u)
    [Finite σ] [Finite τ] [CommRing k] : Type _ :=
  MvPolynomial τ (MvPowerSeries σ k)

private abbrev pthPowerMixedSubringModel (σ : Type v) (τ : Type w) {p : ℕ} [Fact p.Prime]
    [Finite σ] [Finite τ] {ι : Type z} [DecidableEq ι] (k : Type u) [Field k] [CharP k p]
    (x : ι → k) (J : Finset ι) : Type _ :=
  MvPolynomial τ (MvPowerSeries σ (pbasisComplementField k x J))

-- Proof sketch: the coefficient field is a domain, multivariable power series over a domain have
-- no zero divisors, and multivariable polynomial rings over a domain are domains.
private instance {σ : Type v} {τ : Type w} [Finite σ] [Finite τ] (k : Type u) [Field k] :
    IsDomain (mixedPowerSeriesPolynomialRing σ τ k) := by
  -- The ambient mixed ring is a polynomial ring over a power-series domain, so typeclass search
  -- supplies `NoZeroDivisors`; combine it with nontriviality to build the domain structure.
  exact (isDomain_iff_noZeroDivisors_and_nontrivial _).2 ⟨inferInstance, inferInstance⟩

-- Proof sketch: the same domain argument applies to the coefficient subfield `k_J`, giving that
-- the fresh-variable presentation of `A_J` is also a domain.
private instance (σ : Type v) (τ : Type w) {p : ℕ} [Fact p.Prime] [Finite σ] [Finite τ]
    {ι : Type z} [DecidableEq ι] (k : Type u) [Field k] [CharP k p] (x : ι → k) (J : Finset ι) :
    IsDomain (pthPowerMixedSubringModel σ τ k x J) := by
  -- The same no-zero-divisors argument applies after replacing `k` by the intermediate field.
  exact (isDomain_iff_noZeroDivisors_and_nontrivial _).2 ⟨inferInstance, inferInstance⟩

-- Proof sketch: the ambient ring has characteristic `p`, and characteristic is inherited by the
-- fraction field of a domain.
private instance {p : ℕ} {σ : Type v} {τ : Type w} [Finite σ] [Finite τ] (k : Type u)
    [Field k] [CharP k p] : CharP (FractionRing (mixedPowerSeriesPolynomialRing σ τ k)) p := by
  -- Transport characteristic from the coefficient field along the injective ambient algebra map.
  exact charP_of_injective_algebraMap
    (R := k)
    (A := FractionRing (mixedPowerSeriesPolynomialRing σ τ k))
    (algebraMap k (FractionRing (mixedPowerSeriesPolynomialRing σ τ k))).injective p

private abbrev pthPowerMixedSubringToAmbient (σ : Type v) (τ : Type w) {p : ℕ} [Fact p.Prime]
    [Finite σ] [Finite τ] {ι : Type z} [DecidableEq ι] (k : Type u) [Field k] [CharP k p]
    (x : ι → k) (J : Finset ι) : pthPowerMixedSubringModel σ τ k x J →+*
      mixedPowerSeriesPolynomialRing σ τ k :=
  let hp : p ≠ 0 := Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
  let kJ := pbasisComplementField k x J
  let _ : DecidableEq σ := Classical.decEq σ
  let _ : DecidableEq τ := Classical.decEq τ
  let φ : MvPowerSeries σ kJ →+* MvPowerSeries σ k :=
    (MvPowerSeries.map (algebraMap kJ k)).comp (MvPowerSeries.expand p hp).toRingHom
  (MvPolynomial.map φ).comp
    (MvPolynomial.expand p).toRingHom

/-- The intrinsic subring `A_J ⊂ A` of `p`-power series/polynomials over the coefficient
subfield `k_J`. The fresh-variable presentation is only a bridge to this owner subring. -/
abbrev pthPowerMixedSubring (σ : Type v) (τ : Type w) {p : ℕ} [Fact p.Prime] [Finite σ]
    [Finite τ] {ι : Type z} [DecidableEq ι] (k : Type u) [Field k] [CharP k p] (x : ι → k)
    (J : Finset ι) : Subring (mixedPowerSeriesPolynomialRing σ τ k) :=
  (pthPowerMixedSubringToAmbient σ τ k x J).range

/-- The subfield of the ambient fraction field generated by the fraction field of `A_J`. -/
abbrev pthPowerMixedFractionSubfield (σ : Type v) (τ : Type w) {p : ℕ} [Fact p.Prime]
    [Finite σ] [Finite τ] {ι : Type z} [DecidableEq ι] (k : Type u) [Field k] [CharP k p]
    (x : ι → k) (J : Finset ι) : Subfield (FractionRing (mixedPowerSeriesPolynomialRing σ τ k)) :=
  let A_J : Subring (mixedPowerSeriesPolynomialRing σ τ k) := pthPowerMixedSubring σ τ k x J
  ((IsFractionRing.map
      (show Function.Injective A_J.subtype from Subtype.coe_injective) :
    FractionRing A_J →+* FractionRing (mixedPowerSeriesPolynomialRing σ τ k))).fieldRange

section

variable {p : ℕ} [Fact p.Prime] {ι : Type z} [DecidableEq ι]
variable {σ : Type v} [Finite σ] {τ : Type w} [Finite τ]
variable (k : Type u) [Field k] [CharP k p]

local instance : Algebra (ZMod p) k := ZMod.algebra k p
local notation "A" => mixedPowerSeriesPolynomialRing σ τ k
local notation "K" => FractionRing A
local instance : CharP A p := by
  exact charP_of_injective_algebraMap
    (R := k) (A := A) (algebraMap k A).injective p
local instance : ExpChar A p := expChar_prime p
variable (x : ι → k)

/- Textbook notation for the intrinsic mixed `p`-power subring `A_J ⊂ A`. The ambient parameters
are fixed by the current section, so the notation stays local to the owner theorem surface. -/
local notation "A_[" J "]" => pthPowerMixedSubring σ τ k x J

/- Textbook notation for the induced fraction subfield `K_J` of the ambient fraction field. -/
local notation "K_[" J "]" => pthPowerMixedFractionSubfield σ τ k x J

/-- Helper for Lemma 15.46.5: enlarging the omitted finite set shrinks the coefficient field
generated over `k^[p]`. -/
private lemma pbasisComplementField_antitone {J J' : Finset ι} (hJJ' : J ⊆ J') :
    pbasisComplementField k x J' ≤ pbasisComplementField k x J := by
  -- The larger omitted set leaves fewer basis elements available to adjoin.
  rw [IntermediateField.adjoin_le_iff]
  intro y hy
  rcases hy with ⟨i, hiJ', rfl⟩
  have hiJ : i ∉ J := by
    intro hi
    exact hiJ' (hJJ' hi)
  have hmem : x i ∈ x '' {j | j ∉ J} := by
    refine ⟨i, hiJ, ?_⟩
    rfl
  exact IntermediateField.subset_adjoin (k^[p]) (x '' {j | j ∉ J}) hmem

/-- Helper for Lemma 15.46.5: the coefficient field attached to `J ∪ J'` is contained in the
one attached to `J`. -/
private lemma pbasisComplementField_union_le_left (J J' : Finset ι) :
    pbasisComplementField k x (J ∪ J') ≤ pbasisComplementField k x J := by
  -- Apply antitonicity to the obvious inclusion `J ⊆ J ∪ J'`.
  have hsubset : J ⊆ J ∪ J' := by
    intro i hi
    exact Finset.mem_union.mpr (Or.inl hi)
  exact pbasisComplementField_antitone (k := k) (x := x) hsubset

/-- Helper for Lemma 15.46.5: the coefficient field attached to `J ∪ J'` is contained in the
one attached to `J'`. -/
private lemma pbasisComplementField_union_le_right (J J' : Finset ι) :
    pbasisComplementField k x (J ∪ J') ≤ pbasisComplementField k x J' := by
  -- Apply antitonicity to the second union inclusion.
  have hsubset : J' ⊆ J ∪ J' := by
    intro i hi
    exact Finset.mem_union.mpr (Or.inr hi)
  exact pbasisComplementField_antitone (k := k) (x := x) hsubset

/-- Helper for Lemma 15.46.5: coefficient-field inclusion induces the corresponding map between
the mixed presentation rings. -/
private abbrev pthPowerMixedSubringModelMap {J J' : Finset ι} (hJJ' : J ⊆ J') :
    pthPowerMixedSubringModel σ τ k x J' →+* pthPowerMixedSubringModel σ τ k x J :=
  let coeffInclusion :
      pbasisComplementField k x J' →+* pbasisComplementField k x J :=
    (IntermediateField.inclusion
      (pbasisComplementField_antitone (k := k) (x := x) hJJ')).toRingHom
  MvPolynomial.map (MvPowerSeries.map coeffInclusion)

/-- Helper for Lemma 15.46.5: the coefficient-side map to the ambient power-series ring factors
through the smaller omitted-set coefficient field. -/
private lemma pthPowerMixedSubringToAmbient_coeff_factor {J J' : Finset ι} (hJJ' : J ⊆ J') :
    let hp : p ≠ 0 := Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
    let coeffInclusion :
        pbasisComplementField k x J' →+* pbasisComplementField k x J :=
      (IntermediateField.inclusion
        (pbasisComplementField_antitone (k := k) (x := x) hJJ')).toRingHom
    ((MvPowerSeries.map (σ := σ) (R := pbasisComplementField k x J') (S := k)
          (algebraMap (pbasisComplementField k x J') k)).comp
        (MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J') p hp).toRingHom) =
      (((MvPowerSeries.map (σ := σ) (R := pbasisComplementField k x J) (S := k)
            (algebraMap (pbasisComplementField k x J) k)).comp
          (MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J) p hp).toRingHom).comp
        (MvPowerSeries.map (σ := σ)
          (R := pbasisComplementField k x J') (S := pbasisComplementField k x J)
          coeffInclusion)) := by
  -- Compare both coefficient maps after commuting `expand` with `map`; the only remaining datum
  -- is that the ambient algebra map from `k_J'` to `k` factors through the inclusion `k_J' → k_J`.
  dsimp
  let hp : p ≠ 0 := Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
  let coeffInclusion :
      pbasisComplementField k x J' →+* pbasisComplementField k x J :=
    (IntermediateField.inclusion
      (pbasisComplementField_antitone (k := k) (x := x) hJJ')).toRingHom
  have hscalar :
      algebraMap (pbasisComplementField k x J') k =
        (algebraMap (pbasisComplementField k x J) k).comp coeffInclusion := by
    -- Both maps are the same inclusion into the ambient field `k`.
    ext a
    rfl
  ext φ d
  have hexpand :
      MvPowerSeries.map coeffInclusion
          ((MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J') p hp) φ) =
        (MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J) p hp)
          (MvPowerSeries.map coeffInclusion φ) := by
    simpa using
      (MvPowerSeries.map_expand (σ := σ) (p := p) (hp := hp) coeffInclusion φ)
  have hcoeff :
      coeffInclusion
          ((MvPowerSeries.coeff d)
            ((MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J') p hp) φ)) =
        (MvPowerSeries.coeff d)
          ((MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J) p hp)
            (MvPowerSeries.map coeffInclusion φ)) := by
    exact congrArg (MvPowerSeries.coeff d) hexpand
  change (algebraMap (pbasisComplementField k x J') k)
      ((MvPowerSeries.coeff d)
        ((MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J') p hp) φ)) =
    (algebraMap (pbasisComplementField k x J) k)
      ((MvPowerSeries.coeff d)
        ((MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J) p hp)
          (MvPowerSeries.map coeffInclusion φ)))
  rw [hscalar]
  exact congrArg (algebraMap (pbasisComplementField k x J) k) hcoeff

/-- Helper for Lemma 15.46.5: after enlarging the omitted set, the ambient presentation map
factors through the smaller owner ring via the induced coefficient-field inclusion. -/
private lemma pthPowerMixedSubringToAmbient_factor {J J' : Finset ι} (hJJ' : J ⊆ J') :
    pthPowerMixedSubringToAmbient σ τ k x J' =
      (pthPowerMixedSubringToAmbient σ τ k x J).comp
        (pthPowerMixedSubringModelMap (k := k) (x := x) (σ := σ) (τ := τ) hJJ') := by
  -- Compare the two polynomial-layer maps on coefficients and variables separately.
  apply MvPolynomial.ringHom_ext
  · intro φ
    -- The coefficient case is exactly the previously established power-series factorization.
    simpa [pthPowerMixedSubringToAmbient, pthPowerMixedSubringModelMap] using
      congrArg (fun f => f φ)
        (pthPowerMixedSubringToAmbient_coeff_factor
          (k := k) (x := x) (σ := σ) (J := J) (J' := J') hJJ')
  · intro t
    -- Both maps send each polynomial variable to its `p`th power in the ambient ring.
    simp [pthPowerMixedSubringToAmbient, pthPowerMixedSubringModelMap]

/-- Helper for Lemma 15.46.5: enlarging the omitted finite set shrinks the intrinsic owner subring
`A_[J] ⊂ A`. -/
private lemma pthPowerMixedSubring_antitone {J J' : Finset ι} (hJJ' : J ⊆ J') :
    A_[J'] ≤ A_[J] := by
  -- Convert the factorization of the presentation maps into a range inclusion on the owner
  -- subrings.
  rintro y ⟨z, rfl⟩
  refine ⟨pthPowerMixedSubringModelMap (k := k) (x := x) (σ := σ) (τ := τ) hJJ' z, ?_⟩
  exact (congrArg (fun f => f z)
    (pthPowerMixedSubringToAmbient_factor (k := k) (x := x) (σ := σ) (τ := τ) hJJ')).symm

/-- Helper for Lemma 15.46.5: enlarging the omitted finite set also shrinks the induced fraction
subfield inside the ambient fraction field. -/
private lemma pthPowerMixedFractionSubfield_antitone {J J' : Finset ι} (hJJ' : J ⊆ J') :
    K_[J'] ≤ K_[J] := by
  let hA : A_[J'] ≤ A_[J] :=
    pthPowerMixedSubring_antitone (k := k) (x := x) (σ := σ) (τ := τ) hJJ'
  let iA : A_[J'] →+* A_[J] := Subring.inclusion hA
  let iK : FractionRing A_[J'] →+* FractionRing A_[J] :=
    IsFractionRing.map (Subring.inclusion_injective hA)
  let j' : FractionRing A_[J'] →+* K :=
    IsFractionRing.map (show Function.Injective (A_[J']).subtype from Subtype.coe_injective)
  let j : FractionRing A_[J] →+* K :=
    IsFractionRing.map (show Function.Injective (A_[J]).subtype from Subtype.coe_injective)
  have hcomp : j' = j.comp iK := by
    -- Both fraction-field maps extend the same owner inclusion `A_[J'] → A → K`.
    apply (IsFractionRing.ringHom_ext (A := A_[J']))
    intro a
    simp [j', j, iK, iA, RingHom.comp_apply, IsFractionRing.map]
  intro y hy
  rcases RingHom.mem_fieldRange.mp hy with ⟨z, rfl⟩
  -- Reuse the same fraction element after transporting it along the induced map `iK`.
  refine RingHom.mem_fieldRange.mpr ⟨iK z, ?_⟩
  simpa [RingHom.comp_apply] using (congrArg (fun f => f z) hcomp).symm

/-- Helper for Lemma 15.46.5: a scalar derivation of `k` kills every element of the Frobenius
subfield `k^[p]`. -/
private lemma scalar_derivation_eq_zero_of_mem_frobeniusSubfield
    (θ : Derivation (ZMod p) k k) {a : k} (ha : a ∈ k^[p]) :
    θ a = 0 := by
  -- Unpack membership in the Frobenius subfield as an explicit `p`th power in `k`.
  change a ∈ (_root_.frobenius k p).fieldRange at ha
  rcases ha with ⟨b, rfl⟩
  -- In characteristic `p`, the derivation of a `p`th power vanishes by the power rule.
  change θ (b ^ p) = 0
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul k]
  simp

/-- Helper for Lemma 15.46.5: the kernel of a scalar derivation on `k` is closed under
inversion. -/
private lemma scalar_derivation_inv_eq_zero_of_eq_zero
    (θ : Derivation (ZMod p) k k) {a : k} (ha : θ a = 0) :
    θ a⁻¹ = 0 := by
  -- Differentiate `a * a⁻¹ = 1`; once the source element already lies in the kernel, the inverse
  -- term is forced to vanish as well.
  by_cases ha0 : a = 0
  · simp [ha0]
  · have hmul : θ (a * a⁻¹) = a * θ a⁻¹ + a⁻¹ * θ a := by
      simpa [smul_eq_mul, add_comm, mul_comm, mul_left_comm] using θ.leibniz a⁻¹ a
    have hone : θ (a * a⁻¹) = 0 := by
      simp [ha0]
    have hzero : a * θ a⁻¹ = 0 := by
      calc
        a * θ a⁻¹ = θ (a * a⁻¹) := by
          simpa [ha, smul_eq_mul, add_comm, mul_comm, mul_left_comm] using hmul.symm
        _ = 0 := hone
    rcases mul_eq_zero.mp hzero with ha' | hinv
    · exact False.elim (ha0 ha')
    · exact hinv

/-- Helper for Lemma 15.46.5: a derivation dual to `x i` kills the coefficient field obtained by
omitting `i`. -/
private lemma derivation_eq_zero_of_mem_pbasisComplementField_singleton
    {i : ι} (θ : Derivation (ZMod p) k k)
    (hθ_other : ∀ j, j ≠ i → θ (x j) = 0) {a : k}
    (ha : a ∈ pbasisComplementField k x ({i} : Finset ι)) :
    θ a = 0 := by
  -- Route correction: the coefficient intersection argument should first isolate the singleton
  -- omitted set `{i}` and kill that adjoin by induction, before attempting any global `iInf`.
  refine IntermediateField.adjoin_induction
      (F := k^[p]) (s := x '' {j | j ∉ ({i} : Finset ι)})
      (p := fun z _ ↦ θ z = 0) ?_ ?_ ?_ ?_ ?_ ha
  · intro y hy
    rcases hy with ⟨j, hj, rfl⟩
    have hji : j ≠ i := by
      simpa using hj
    exact hθ_other j hji
  · intro y
    exact scalar_derivation_eq_zero_of_mem_frobeniusSubfield (k := k) (p := p) θ y.property
  · intro y z _ _ hy hz
    simpa [hy, hz] using θ.map_add y z
  · intro y _ hy
    exact scalar_derivation_inv_eq_zero_of_eq_zero (k := k) (p := p) θ hy
  · intro y z _ _ hy hz
    simpa [hy, hz, smul_eq_mul, add_comm, mul_comm, mul_left_comm] using θ.leibniz y z

/-- Helper for Lemma 15.46.5: for each omitted singleton `{i}`, the dual derivation coming from
the `p`-basis kills the corresponding coefficient field. -/
private lemma exists_dual_derivation_kills_pbasisComplementField_singleton
    (hx : IsPBasis p (ZMod p) k x) (i : ι) :
    ∃ θ : Derivation (ZMod p) k k,
      θ (x i) = 1 ∧
      (∀ j, j ≠ i → θ (x j) = 0) ∧
      ∀ a ∈ pbasisComplementField k x ({i} : Finset ι), θ a = 0 := by
  -- Extract a dual derivation from the differential independence supplied by the `p`-basis.
  have hlin : LinearIndependent k (D (ZMod p) k ∘ x) :=
    @linearIndependent_differentials_of_isPBasis p (ZMod p) k _ _ _ _ _ ι x hx
  obtain ⟨θ, hθi, hθother⟩ :=
    @exists_dual_derivation_of_linearIndependent_differentials
      (ZMod p) k _ _ _ ι x hlin i
  -- Then the singleton omission lemma shows that the same derivation kills the coefficient field.
  refine ⟨θ, hθi, hθother, ?_⟩
  intro a ha
  exact derivation_eq_zero_of_mem_pbasisComplementField_singleton
    (k := k) (p := p) (x := x) (i := i) θ hθother ha

/-- Helper for Lemma 15.46.5: any element of the coefficient-field intersection is killed by the
dual derivation attached to each basis index `i`. -/
private lemma exists_dual_derivation_apply_eq_zero_of_mem_iInf_pbasisComplementField
    (hx : IsPBasis p (ZMod p) k x) {a : k}
    (ha : a ∈ (⨅ J : Finset ι, pbasisComplementField k x J)) (i : ι) :
    ∃ θ : Derivation (ZMod p) k k,
      θ (x i) = 1 ∧
      (∀ j, j ≠ i → θ (x j) = 0) ∧
      θ a = 0 := by
  -- Membership in the full intersection specializes to the singleton omitted field `{i}`.
  have ha_singleton : a ∈ pbasisComplementField k x ({i} : Finset ι) :=
    (show (⨅ J : Finset ι, pbasisComplementField k x J) ≤
        pbasisComplementField k x ({i} : Finset ι) from
      iInf_le (fun J : Finset ι ↦ pbasisComplementField k x J) ({i} : Finset ι)) ha
  obtain ⟨θ, hθi, hθother, hθkill⟩ :=
    exists_dual_derivation_kills_pbasisComplementField_singleton
      (k := k) (p := p) (x := x) hx i
  -- The singleton helper now applies directly to `a`.
  exact ⟨θ, hθi, hθother, hθkill a ha_singleton⟩

/-- Helper for Lemma 15.46.5: a singleton family is `p`-independent over `𝔽_p` exactly when its
generator is not a `p`th power. -/
private lemma pIndependent_singleton_iff_not_mem_frobeniusSubfield (a : k) :
    PIndependent p (ZMod p) k (fun _ : Unit => a) ↔ a ∉ k^[p] := by
  -- Reduce singleton `p`-independence to linear independence of the unique differential.
  rw [pIndependent_iff_linearIndependent_differentials
    (p := p) (k := ZMod p) (x := fun _ : Unit => a)]
  change LinearIndependent k (fun _ : Unit => D (ZMod p) k a) ↔ a ∉ k^[p]
  rw [linearIndependent_unique_iff]
  have hmem_iff : a ∈ k^[p] ↔ ∃ b : k, b ^ p = a := by
    change a ∈ (_root_.frobenius k p).fieldRange ↔ ∃ b : k, b ^ p = a
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, hb⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, rfl⟩
  -- The unique differential is nonzero exactly when `a` is not a `p`th power.
  constructor
  · intro hDa ha
    exact hDa <|
      (kaehlerDifferential_eq_zero_iff_exists_pth_root
        (k := ZMod p) (a := a)).2 ((hmem_iff.mp ha))
  · intro ha hDa
    exact ha <|
      hmem_iff.mpr <|
        (kaehlerDifferential_eq_zero_iff_exists_pth_root
          (k := ZMod p) (a := a)).1 hDa

/-- Helper for Lemma 15.46.5: the linear functional attached to a dual derivation is exactly the
coordinate functional of the differential basis coming from the `p`-basis. -/
private lemma dual_derivation_lift_eq_basis_coord
    {hlin : LinearIndependent k (D (ZMod p) k ∘ x)}
    {hspan : ⊤ ≤ Submodule.span k (Set.range (D (ZMod p) k ∘ x))}
    {i : ι} (θ : Derivation (ZMod p) k k)
    (hθi : θ (x i) = 1)
    (hθother : ∀ j, j ≠ i → θ (x j) = 0) :
    θ.liftKaehlerDifferential =
      (Finsupp.lapply (R := k) (M := k) i).comp
        ((Module.Basis.mk hlin hspan).repr : Ω[k⁄ZMod p] →ₗ[k] ι →₀ k) := by
  let b : Module.Basis ι k Ω[k⁄ZMod p] := Module.Basis.mk hlin hspan
  -- Compare both linear forms on the differential basis produced by `x`; that basis already
  -- spans all Kähler differentials, so agreement there determines the map globally.
  change θ.liftKaehlerDifferential = b.coord i
  refine b.ext fun j => ?_
  -- Evaluate each side on the basis vector `D (x j)` and use the dual-derivation hypotheses.
  by_cases hji : j = i
  · subst hji
    calc
      θ.liftKaehlerDifferential (b j) = θ (x j) := by
        simp [b, Function.comp_apply, Derivation.liftKaehlerDifferential_comp_D]
      _ = 1 := hθi
      _ = b.coord j (b j) := by
        symm
        simpa [b] using
          (Module.Basis.mk_coord_apply_eq (hli := hlin) (hsp := hspan) j)
  · calc
      θ.liftKaehlerDifferential (b j) = θ (x j) := by
        simp [b, Function.comp_apply, Derivation.liftKaehlerDifferential_comp_D]
      _ = 0 := hθother j hji
      _ = b.coord i (b j) := by
        symm
        simpa [b] using
          (Module.Basis.mk_coord_apply_ne (hli := hlin) (hsp := hspan) (i := i) (j := j) hji)

/-- Helper for Lemma 15.46.5: if every basis-dual derivation kills `a`, then `da` has zero
coordinates in the differential basis and hence vanishes. -/
private lemma kaehlerDifferential_eq_zero_of_vanishing_pbasis_dual_derivations
    (hx : IsPBasis p (ZMod p) k x) {a : k}
    (hkill : ∀ i : ι, ∃ θ : Derivation (ZMod p) k k,
      θ (x i) = 1 ∧
      (∀ j, j ≠ i → θ (x j) = 0) ∧
      θ a = 0) :
    D (ZMod p) k a = 0 := by
  obtain ⟨hlin, hspan_eq⟩ :=
    (@isPBasis_iff_differentials_formBasis p (ZMod p) k _ _ _ _ _ ι x).1 hx
  let hspan : ⊤ ≤ Submodule.span k (Set.range (D (ZMod p) k ∘ x)) := by
    simpa [hspan_eq]
  let b : Module.Basis ι k Ω[k⁄ZMod p] := Module.Basis.mk hlin hspan
  -- Route correction: once the basis-coordinate formula for dual derivations is available, the
  -- source vanishing argument is just coordinatewise evaluation on `D a`.
  refine (b.forall_coord_eq_zero_iff).1 ?_
  intro i
  obtain ⟨θ, hθi, hθother, hθa⟩ := hkill i
  -- Evaluate the identifying linear-map equality on `D a`; the left side is `θ a`, which is zero.
  have hcoord :=
    congrArg (fun ψ : Ω[k⁄ZMod p] →ₗ[k] k ↦ ψ (D (ZMod p) k a))
      (dual_derivation_lift_eq_basis_coord
        (k := k) (p := p) (x := x) (hlin := hlin) (hspan := hspan) θ hθi hθother)
  simpa [b, Derivation.liftKaehlerDifferential_comp_D, hθa] using hcoord.symm

/-- Helper for Lemma 15.46.5: intersecting the coefficient fields `k_J` over all finite omitted
sets recovers exactly the Frobenius subfield `k^[p]`. -/
private lemma iInf_pbasisComplementField_eq_frobeniusSubfield
    (hx : IsPBasis p (ZMod p) k x) :
    (show Subfield k from (⨅ J : Finset ι, (pbasisComplementField k x J).toSubfield)) =
      k^[p] := by
  -- Follow the source route: the intersection element lies in every singleton omission field, so
  -- every dual derivation kills it; then its differential vanishes, forcing it into `k^[p]`.
  ext a
  constructor
  · intro ha
    have hkill :
        ∀ i : ι, ∃ θ : Derivation (ZMod p) k k,
          θ (x i) = 1 ∧
          (∀ j, j ≠ i → θ (x j) = 0) ∧
          θ a = 0 :=
      fun i ↦ by
        have ha_singleton : a ∈ pbasisComplementField k x ({i} : Finset ι) := by
          have ha_all :
              ∀ J : Finset ι, a ∈ (pbasisComplementField k x J).toSubfield := by
            simpa [Subfield.mem_iInf] using ha
          exact ha_all {i}
        obtain ⟨θ, hθi, hθother, hθkill⟩ :=
          exists_dual_derivation_kills_pbasisComplementField_singleton
            (k := k) (p := p) (x := x) hx i
        exact ⟨θ, hθi, hθother, hθkill a ha_singleton⟩
    have hDa : D (ZMod p) k a = 0 :=
      kaehlerDifferential_eq_zero_of_vanishing_pbasis_dual_derivations
        (k := k) (p := p) (x := x) hx hkill
    by_contra ha_not_frob
    have hPInd :
        PIndependent p (ZMod p) k (fun _ : Unit ↦ a) :=
      (pIndependent_singleton_iff_not_mem_frobeniusSubfield
        (k := k) (p := p) a).2 ha_not_frob
    have hlin :
        LinearIndependent k (D (ZMod p) k ∘ fun _ : Unit ↦ a) :=
      (@pIndependent_iff_linearIndependent_differentials
        p (ZMod p) k _ _ _ _ _ Unit (fun _ : Unit ↦ a)).1 hPInd
    rw [linearIndependent_unique_iff] at hlin
    exact hlin (by simpa [Function.comp_apply] using hDa)
  · intro ha
    -- Every coefficient field `k_J` contains the base Frobenius field `k^[p]`.
    simp only [Subfield.mem_iInf]
    intro J
    change a ∈ Subfield.closure (Set.range ⇑(algebraMap (↥k^[p]) k) ∪ x '' {i | i ∉ J})
    exact Subfield.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)

/-- Helper for Lemma 15.46.5: the Frobenius subfield contains the prime field `𝔽_p ⊂ k`. -/
private lemma algebraMap_zmod_mem_frobeniusSubfield (a : ZMod p) :
    algebraMap (ZMod p) k a ∈ k^[p] := by
  -- The Frobenius on `𝔽_p` is the identity, so the image of `a` is itself a `p`th power in `k`.
  change algebraMap (ZMod p) k a ∈ (_root_.frobenius k p).fieldRange
  refine ⟨algebraMap (ZMod p) k a, ?_⟩
  change (algebraMap (ZMod p) k a) ^ p = algebraMap (ZMod p) k a
  rw [← map_pow]
  simpa [ZMod.card] using congrArg (algebraMap (ZMod p) k) (ZMod.pow_card a)

/-- Helper for Lemma 15.46.5: adjoining the finitely omitted basis elements back to `k_J`
recovers the whole field `k`. -/
private lemma pbasisComplementField_adjoin_omitted_eq_top
    (hx : IsPBasis p (ZMod p) k x) (J : Finset ι) :
    IntermediateField.adjoin (pbasisComplementField k x J) (x '' (↑J : Set ι)) = ⊤ := by
  -- First upgrade the source `p`-basis generation statement from `𝔽_p(k^p)` to `k^p`.
  have hpcomp_le :
      (pPowerCompositum p (ZMod p) k).toSubfield ≤ k^[p] := by
    -- Here the source set being adjoined is already `k^[p]`, so `adjoin_le_iff` closes the goal
    -- directly.
    rw [show pPowerCompositum p (ZMod p) k = IntermediateField.adjoin (ZMod p) (k^[p] : Set k) by
      rfl]
    rw [IntermediateField.adjoin_le_iff]
    intro y hy
    exact hy
  letI : Algebra (pPowerCompositum p (ZMod p) k) ↥(k^[p]) :=
    (IntermediateField.inclusion hpcomp_le).toAlgebra
  have hxp_top : IntermediateField.adjoin (k^[p]) (Set.range x) = ⊤ := by
    -- Once `k^[p]` contains `𝔽_p(k^p)`, the same generating family `x` still generates all of
    -- `k`.
    exact IntermediateField.adjoin_eq_top_of_adjoin_eq_top (pPowerCompositum p (ZMod p) k) hx.2
  -- Then rewrite the adjoin over `k_J` as an adjoin over `k^[p]` and observe that the union of
  -- the complement generators with the omitted generators contains the full basis family.
  apply IntermediateField.restrictScalars_injective (F := k^[p])
  rw [IntermediateField.restrictScalars_top, IntermediateField.restrictScalars_adjoin]
  rw [show (pbasisComplementField k x J : Set k) =
      IntermediateField.adjoin (k^[p]) (x '' {i | i ∉ J}) by
    rfl]
  rw [IntermediateField.restrictScalars_adjoin]
  apply top_unique
  rw [← hxp_top]
  exact IntermediateField.adjoin.mono (k^[p]) (Set.range x) _ (fun y hy ↦ by
    rcases hy with ⟨i, rfl⟩
    by_cases hi : i ∈ J
    · exact Or.inr ⟨i, hi, rfl⟩
    · exact Or.inl <|
        IntermediateField.subset_adjoin (k^[p]) (x '' {j | j ∉ J}) ⟨i, hi, rfl⟩)

/-- Helper for Lemma 15.46.5: every omitted basis generator is integral over the coefficient
field obtained by adjoining the complementary basis elements to `k^[p]`. -/
private lemma omitted_generator_integral_over_pbasisComplementField
    (hx : IsPBasis p (ZMod p) k x) {J : Finset ι} {i : ι} (hi : i ∈ J) :
    IsIntegral (pbasisComplementField k x J) (x i) := by
  -- Its `p`th power already lies in the Frobenius subfield, hence in `k_J`; integrality then
  -- descends along `IsIntegral.of_pow`.
  let xp : pbasisComplementField k x J :=
    ⟨x i ^ p, pow_mem_pbasisComplementField (k := k) (p := p) (x := x) J (x i)⟩
  have hxp_integral :
      IsIntegral (pbasisComplementField k x J)
        ((algebraMap (pbasisComplementField k x J) k) xp) := by
    simpa using
      (isIntegral_algebraMap : IsIntegral (pbasisComplementField k x J)
        ((algebraMap (pbasisComplementField k x J) k) xp))
  -- Route correction: package the source polynomial `X^p - C((x i)^p)` through the generic
  -- `IsIntegral.of_pow` API rather than rebuilding the polynomial witness by hand.
  simpa [xp] using
    IsIntegral.of_pow (R := pbasisComplementField k x J) (x := x i) (n := p)
      (Fact.out.pos) hxp_integral

/-- Helper for Lemma 15.46.5: omitting only finitely many basis elements leaves a coefficient
field of finite codimension inside `k`. -/
private lemma pbasisComplementField_finiteDimensional
    (hx : IsPBasis p (ZMod p) k x) (J : Finset ι) :
    FiniteDimensional (pbasisComplementField k x J) k := by
  let s : Set k := x '' (↑J : Set ι)
  have hs_finite : s.Finite := (Finset.finite_toSet J).image x
  letI : Fintype s := hs_finite.fintype
  have hs_integral : ∀ z ∈ s, IsIntegral (pbasisComplementField k x J) z := by
    intro z hz
    rcases hz with ⟨i, hi, rfl⟩
    -- The previous helper packages the omitted-generator integrality for exactly these elements.
    exact omitted_generator_integral_over_pbasisComplementField
      (k := k) (p := p) (x := x) hx hi
  have hfd :
      FiniteDimensional (pbasisComplementField k x J)
        (IntermediateField.adjoin (pbasisComplementField k x J) s) :=
    IntermediateField.finiteDimensional_adjoin hs_integral
  -- Replacing the adjoin by `⊤` identifies the resulting finite extension with `k`.
  let e :
      IntermediateField.adjoin (pbasisComplementField k x J) s ≃ₐ[pbasisComplementField k x J]
        (⊤ : IntermediateField (pbasisComplementField k x J) k) :=
    AlgEquiv.ofEq _ _ (pbasisComplementField_adjoin_omitted_eq_top (k := k) (p := p) (x := x) hx J).symm
  letI : FiniteDimensional (pbasisComplementField k x J)
      (IntermediateField.adjoin (pbasisComplementField k x J) s) := hfd
  let hfd_top : FiniteDimensional (pbasisComplementField k x J)
      (⊤ : IntermediateField (pbasisComplementField k x J) k) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  letI : FiniteDimensional (pbasisComplementField k x J)
      (⊤ : IntermediateField (pbasisComplementField k x J) k) := hfd_top
  exact FiniteDimensional.of_injective
    (IntermediateField.topEquiv : (⊤ : IntermediateField (pbasisComplementField k x J) k) ≃ₐ[pbasisComplementField k x J] k).toLinearMap
    (IntermediateField.topEquiv : (⊤ : IntermediateField (pbasisComplementField k x J) k) ≃ₐ[pbasisComplementField k x J] k).injective

/-- Helper for Lemma 15.46.5: every scalar `p`th power already belongs to the coefficient field
`k_J`. -/
private lemma pow_mem_pbasisComplementField (J : Finset ι) (a : k) :
    a ^ p ∈ pbasisComplementField k x J := by
  -- The coefficient field is generated over `k^[p]`, so every scalar `p`th power lies there from
  -- the outset.
  exact IntermediateField.set_range_subset (pbasisComplementField k x J)
    ⟨⟨a ^ p, ⟨a, rfl⟩⟩, rfl⟩

/-- Helper for Lemma 15.46.5: the scalar Frobenius on `k` factors through the omitted-coefficient
field `k_J`. -/
private lemma frobenius_factor_through_pbasisComplementField (J : Finset ι) :
    ∃ FJ : k →+* pbasisComplementField k x J,
      (algebraMap (pbasisComplementField k x J) k).comp FJ = _root_.frobenius k p := by
  -- Restrict the scalar Frobenius codomain using that every `p`th power already lies in `k_J`.
  refine ⟨RingHom.codRestrict (_root_.frobenius k p) (pbasisComplementField k x J) ?_, ?_⟩
  · intro a
    simpa [frobenius_def] using pow_mem_pbasisComplementField (k := k) (p := p) (x := x) J a
  · ext a
    rfl

/-- Helper for Lemma 15.46.5: the coefficient Frobenius on multivariable power series factors
through the omitted-coefficient field `k_J`. -/
private lemma mvPowerSeries_expand_frobenius_factor (J : Finset ι) (φ : MvPowerSeries σ k) :
    let hp : p ≠ 0 := Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
    let FJ :=
      Classical.choose
        (frobenius_factor_through_pbasisComplementField (k := k) (p := p) (x := x) J)
    (((MvPowerSeries.map (σ := σ) (R := pbasisComplementField k x J) (S := k)
          (algebraMap (pbasisComplementField k x J) k)).comp
        (MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J) p hp).toRingHom)
      ((MvPowerSeries.map (σ := σ) (R := k) (S := pbasisComplementField k x J) FJ) φ)) = φ ^ p := by
  -- Rewrite the owner coefficient map as the scalar Frobenius after commuting `expand` with
  -- `map`, then close by the characteristic-`p` expand identity.
  let hp : p ≠ 0 := Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
  let FJ :=
    Classical.choose
      (frobenius_factor_through_pbasisComplementField (k := k) (p := p) (x := x) J)
  have hFJ :
      (algebraMap (pbasisComplementField k x J) k).comp FJ = _root_.frobenius k p :=
    Classical.choose_spec
      (frobenius_factor_through_pbasisComplementField (k := k) (p := p) (x := x) J)
  have hexpand :
      (MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J) p hp)
          ((MvPowerSeries.map (σ := σ) (R := k) (S := pbasisComplementField k x J) FJ) φ) =
        (MvPowerSeries.map (σ := σ) (R := k) (S := pbasisComplementField k x J) FJ)
          ((MvPowerSeries.expand (σ := σ) (R := k) p hp) φ) := by
    simpa using
      (MvPowerSeries.map_expand (σ := σ) (p := p) (hp := hp) FJ φ).symm
  calc
    (((MvPowerSeries.map (σ := σ) (R := pbasisComplementField k x J) (S := k)
          (algebraMap (pbasisComplementField k x J) k)).comp
        (MvPowerSeries.expand (σ := σ) (R := pbasisComplementField k x J) p hp).toRingHom)
      ((MvPowerSeries.map (σ := σ) (R := k) (S := pbasisComplementField k x J) FJ) φ))
        =
      (MvPowerSeries.map (σ := σ) (R := pbasisComplementField k x J) (S := k)
        (algebraMap (pbasisComplementField k x J) k))
          ((MvPowerSeries.map (σ := σ) (R := k) (S := pbasisComplementField k x J) FJ)
            ((MvPowerSeries.expand (σ := σ) (R := k) p hp) φ)) := by
      simpa [RingHom.comp_apply] using
        congrArg
          (MvPowerSeries.map (σ := σ) (R := pbasisComplementField k x J) (S := k)
            (algebraMap (pbasisComplementField k x J) k))
          hexpand
    _ =
      (MvPowerSeries.map (σ := σ) (R := k) (S := k)
        ((algebraMap (pbasisComplementField k x J) k).comp FJ))
          ((MvPowerSeries.expand (σ := σ) (R := k) p hp) φ) := by
      rw [MvPowerSeries.map_map]
    _ = (MvPowerSeries.map (σ := σ) (R := k) (S := k) (_root_.frobenius k p))
          ((MvPowerSeries.expand (σ := σ) (R := k) p hp) φ) := by
      rw [hFJ]
    _ = φ ^ p := by
      simpa using
        (MvPowerSeries.map_frobenius_expand (σ := σ) (R := k) (p := p) (hp := hp) (f := φ))

/-- Helper for Lemma 15.46.5: the owner mixed-ring Frobenius factors through the presentation map
to `A_[J]`. -/
private lemma pthPowerMixedSubringToAmbient_frobenius_factor (J : Finset ι) :
    let FJ :=
      Classical.choose
        (frobenius_factor_through_pbasisComplementField (k := k) (p := p) (x := x) J)
    (pthPowerMixedSubringToAmbient σ τ k x J).comp
        (MvPolynomial.map (MvPowerSeries.map FJ)) = _root_.frobenius A p := by
  -- Compare both ring homs on coefficients and polynomial variables separately.
  let FJ :=
    Classical.choose
      (frobenius_factor_through_pbasisComplementField (k := k) (p := p) (x := x) J)
  letI : ExpChar A p := inferInstance
  apply MvPolynomial.ringHom_ext
  · intro φ
    -- The coefficient case is exactly the power-series factorization proved just above.
    simpa [pthPowerMixedSubringToAmbient, FJ] using
      (mvPowerSeries_expand_frobenius_factor (k := k) (p := p) (x := x) (σ := σ) J φ)
  · intro t
    -- Each polynomial variable maps to its `p`th power on both sides.
    simp [pthPowerMixedSubringToAmbient, frobenius_def]

/-- Helper for Lemma 15.46.5: every ambient `p`th power belongs to the intrinsic mixed
`p`-power subring `A_[J]`. -/
private lemma pow_mem_pthPowerMixedSubring (J : Finset ι) (f : A) :
    f ^ p ∈ A_[J] := by
  -- Route correction: prove range membership by the owner-level Frobenius factorization, rather
  -- than by a transport-heavy direct search in the fraction-field image.
  let FJ :=
    Classical.choose
      (frobenius_factor_through_pbasisComplementField (k := k) (p := p) (x := x) J)
  refine ⟨(MvPolynomial.map (MvPowerSeries.map FJ)) f, ?_⟩
  have hfactor :=
    pthPowerMixedSubringToAmbient_frobenius_factor
      (k := k) (p := p) (x := x) (σ := σ) (τ := τ) J
  change
      ((pthPowerMixedSubringToAmbient σ τ k x J).comp
        (MvPolynomial.map (MvPowerSeries.map FJ))) f = f ^ p
  simpa [FJ, RingHom.comp_apply] using congrArg (fun ψ : A →+* A ↦ ψ f) hfactor

/-- Helper for Lemma 15.46.5: every element of the Frobenius subfield of the ambient fraction
field lies in each source-facing mixed fraction subfield `K_[J]`. -/
private lemma frobeniusSubfield_le_pthPowerMixedFractionSubfield (J : Finset ι) :
    K^[p] ≤ K_[J] := by
  intro z hz
  change z ∈ (_root_.frobenius K p).fieldRange at hz
  rcases hz with ⟨y, rfl⟩
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective A y
  let aJ : A_[J] := ⟨a ^ p, pow_mem_pthPowerMixedSubring (k := k) (p := p) (x := x) (σ := σ) (τ := τ) J a⟩
  let bJ : A_[J] := ⟨b ^ p, pow_mem_pthPowerMixedSubring (k := k) (p := p) (x := x) (σ := σ) (τ := τ) J b⟩
  let j : FractionRing A_[J] →+* K :=
    IsFractionRing.map (show Function.Injective (A_[J]).subtype from Subtype.coe_injective)
  have ha_map :
      j (algebraMap A_[J] (FractionRing A_[J]) aJ) = (algebraMap A K a) ^ p := by
    simp [j, aJ]
  have hb_map :
      j (algebraMap A_[J] (FractionRing A_[J]) bJ) = (algebraMap A K b) ^ p := by
    simp [j, bJ]
  -- Represent the ambient `p`th power by the corresponding numerator and denominator inside
  -- `FractionRing A_[J]`.
  refine RingHom.mem_fieldRange.mpr
    ⟨algebraMap A_[J] (FractionRing A_[J]) aJ / algebraMap A_[J] (FractionRing A_[J]) bJ, ?_⟩
  change
      j (algebraMap A_[J] (FractionRing A_[J]) aJ / algebraMap A_[J] (FractionRing A_[J]) bJ) =
        y ^ p
  calc
    j (algebraMap A_[J] (FractionRing A_[J]) aJ / algebraMap A_[J] (FractionRing A_[J]) bJ)
        = j (algebraMap A_[J] (FractionRing A_[J]) aJ) /
            j (algebraMap A_[J] (FractionRing A_[J]) bJ) := by
          rw [map_div₀]
    _ = (algebraMap A K a) ^ p / (algebraMap A K b) ^ p := by
      rw [ha_map, hb_map]
    _ = (algebraMap A K a / algebraMap A K b) ^ p := by
      rw [div_pow]
    _ = y ^ p := by
      rw [hfrac]

-- Proof sketch: the omitted basis elements are exactly those indexed by the finite set `J`, so
-- the complements define a downward directed family. Taking `p`-th powers of the formal and
-- polynomial variables transports this reverse-direction directedness to the source-facing
-- fraction subfields `K_[J]` of the ambient fraction field.
/-- For a field `k` of characteristic `p` with `p`-basis `x` over `𝔽_p`, the source-facing
fraction subfields `K_[J]` intersect in the Frobenius subfield of the ambient fraction field. -/
theorem iInf_pthPowerMixedFractionSubfield_eq_frobeniusSubfield
    (hx : IsPBasis p (ZMod p) k x) :
    (⨅ J, K_[J]) = K^[p] :=
by
  -- Route correction: the source proof separates into two inclusions. The easy direction is
  -- `K^[p] ≤ K_[J]` for every `J`, while the hard direction first descends numerators into every
  -- `A_[J]` and only then intersects coefficients through the singleton-field argument above.
  refine le_antisymm ?_ ?_
  · -- TODO: after extracting normalized representatives `f / g^p ∈ K_[J]`, use the three source
    -- derivation families to descend `f` into each `A_[J]`; the remaining blocker is the final
    -- coefficient intersection step turning the helpers above into
    -- `(⨅ J, pbasisComplementField k x J) = k^[p]`.
    sorry
  · -- TODO: after extracting normalized representatives `f / g^p ∈ K_[J]`, use the three source
    -- owner lemma `pow_mem_pthPowerMixedSubring` is exactly the remaining input needed to place
    -- `a ^ p` and `b ^ p` in `A_[J]` and close this easy inclusion without transport-heavy
    -- `fieldRange` elaboration.
    exact le_iInf fun J =>
      frobeniusSubfield_le_pthPowerMixedFractionSubfield
        (k := k) (p := p) (x := x) (σ := σ) (τ := τ) J

/-- For a family `x` in a field `k` of characteristic `p`, the source-facing fraction subfields
`K_[J]` are downward directed under inclusion. -/
theorem directed_pthPowerMixedFractionSubfield
    : Directed (· ≥ ·) fun J : Finset ι ↦ K_[J] := by
  -- Use the owner-level antitonicity proved above and the canonical witness `J ∪ J'`.
  intro J J'
  refine ⟨J ∪ J', ?_, ?_⟩
  · have hsubset : J ⊆ J ∪ J' := by
      intro i hi
      exact Finset.mem_union.mpr (Or.inl hi)
    exact pthPowerMixedFractionSubfield_antitone (k := k) (x := x) hsubset
  · have hsubset : J' ⊆ J ∪ J' := by
      intro i hi
      exact Finset.mem_union.mpr (Or.inr hi)
    exact pthPowerMixedFractionSubfield_antitone (k := k) (x := x) hsubset

-- Proof sketch: because only finitely many basis elements are omitted from `k_J`, the extension
-- `k_J ⊆ k` is finite. Lemma `10.97.7` gives finiteness for the corresponding extension on formal
-- power series, and adjoining finitely many polynomial variables preserves module-finiteness.
/-- The ambient ring `A` is finite over each source-facing intrinsic subring `A_[J] ⊂ A`. -/
theorem pthPowerMixedSubring_finite
    (hx : IsPBasis p (ZMod p) k x) (J : Finset ι) :
    Module.Finite (A_[J]) A := by
  -- First isolate the finite coefficient-field extension coming from the finitely omitted basis
  -- coordinates.
  let _ : FiniteDimensional (pbasisComplementField k x J) k :=
    pbasisComplementField_finiteDimensional (k := k) (p := p) (x := x) hx J
  -- TODO: lift the finite coefficient extension through the `p`-power presentation of the
  -- power-series and polynomial variables, prove module-finiteness for the presentation ring over
  -- `pthPowerMixedSubringModel σ τ k x J`, and then transfer that statement across the range map
  -- `pthPowerMixedSubringToAmbient`.
  sorry

end
