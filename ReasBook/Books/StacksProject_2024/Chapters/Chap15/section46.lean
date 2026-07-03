import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_46_1 (from Chap15) -/
open scoped BigOperators

universe u v w

/-- The subfield `K^p` of `p`-th powers in `K`. -/
abbrev frobeniusSubfield (p : ℕ) (K : Type u) [Field K] [ExpChar K p] : Subfield K :=
  (_root_.frobenius K p).fieldRange

namespace FrobeniusSubfield

/- Textbook notation for the subfield `K^p` of `p`-th powers in `K`. -/
scoped notation:max K "^[" p "]" => frobeniusSubfield p K

end FrobeniusSubfield

open scoped FrobeniusSubfield

/-- The `p`-restricted monomials attached to a family in a field. -/
abbrev pMonomial (p : ℕ) {K : Type v} [CommMonoidWithZero K] [NeZero p] {ι : Type w}
    (x : ι → K) :
    (ι →₀ Fin p) → K :=
  fun e ↦ e.support.prod fun i ↦ x i ^ (e i : ℕ)

section

variable (p : ℕ) (k : Type u) (K : Type v) {ι : Type w}
variable [Field k] [Field K] [Algebra k K]
variable [Fact p.Prime] [CharP K p]

/-- The compositum `kK^p` of `k` and `K^p` inside `K`. -/
abbrev pPowerCompositum : IntermediateField k K :=
  IntermediateField.adjoin k (K^[p] : Set K)

/-- Definition 15.46.1 (1): a family in `K` is `p`-independent over `k` when its
`p`-restricted monomials are linearly independent over the compositum `kK^p`. -/
abbrev PIndependent (x : ι → K) : Prop :=
  LinearIndependent (pPowerCompositum p k K) (pMonomial p x)

/-- Definition 15.46.1 (2): a family in `K` is a `p`-basis of `K` over `k` when its
`p`-restricted monomials are linearly independent and the family generates `K` over the
compositum `kK^p`. -/
def IsPBasis (x : ι → K) : Prop :=
  PIndependent p k K x ∧
    IntermediateField.adjoin (pPowerCompositum p k K) (Set.range x) = ⊤

end

/-! ### Lemma_15_46_2 (from Chap15) -/
open scoped BigOperators
open KaehlerDifferential

universe u v w

section PBasis

variable (p : ℕ) (k : Type u) (K : Type v)
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {ι : Type w}

/- Domain triage:
- primary domain: `p`-bases of characteristic-`p` field extensions and their characterization via
  the universal derivation `D k K`;
- sampled owner declarations:
  `PIndependent`,
  `IsPBasis`,
  `Module.Basis.mk`,
  `Module.Basis.span_eq`,
  `D k K`;
- best owner abstraction: the source-facing owners are the chapter declarations `PIndependent` and
  `IsPBasis`, while any actual `Module.Basis` witness is derived data supplied canonically by
  `Module.Basis.mk`;
- primitive data: `p`-independence and generation over `pPowerCompositum p k K`;
- derived API: the differential criteria and existence statements below.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma `15.46.2`;
- `core/canonical`: `PIndependent`, `IsPBasis`, `Module.Basis.mk`, and `D k K`;
- `bridge/view`: the textbook basis wording is expressed directly through the owner `IsPBasis`,
  rather than through any parallel local restatement or existential `Module.Basis` wrapper.
-/

-- Proof sketch: identify `k`-derivations of `K` with `K`-linear maps out of `Ω[K⁄k]`, then use
-- the standard characteristic-`p` argument that `p`-restricted monomial relations are detected by
-- derivations.
/-- Lemma 15.46.2 (1): a family in a characteristic-`p` field extension is `p`-independent over
`k` if and only if its differentials are `K`-linearly independent in `Ω[K⁄k]`. -/
theorem pIndependent_iff_linearIndependent_differentials (x : ι → K) :
    PIndependent p k K x ↔
      LinearIndependent K (D k K ∘ x) := sorry

-- Proof sketch: apply Zorn's lemma to enlarge a `p`-independent family to a maximal one, then
-- show that maximal `p`-independent families generate `K` over `k(K^p)`.
/-- Lemma 15.46.2 (2): every `p`-independent family in `K` extends to a `p`-basis of `K` over
`k`. -/
theorem exists_isPBasis_extension (x : ι → K) (hx : PIndependent p k K x) :
    ∃ (ι' : Type (max v w)) (y : ι' → K) (e : ι ↪ ι'),
      (∀ i, y (e i) = x i) ∧ IsPBasis p k K y := sorry

-- Proof sketch: start from the empty `p`-independent family and apply the extension statement.
/-- Lemma 15.46.2 (3): the field `K` admits a `p`-basis over `k`. -/
theorem exists_isPBasis :
    ∃ (ι : Type v) (x : ι → K), IsPBasis p k K x := sorry

-- Proof sketch: combine the first equivalence with the spanning criterion for `Ω[K⁄k]`; a
-- `p`-basis gives a linearly independent spanning family of differentials, and conversely such a
-- family is a maximal `p`-independent family.
/-- Lemma 15.46.2 (4): a family is a `p`-basis of `K` over `k` if and only if its differentials
are `K`-linearly independent and span `Ω[K⁄k]`. -/
theorem isPBasis_iff_differentials_formBasis (x : ι → K) :
    IsPBasis p k K x ↔
      LinearIndependent K (D k K ∘ x) ∧
        Submodule.span K (Set.range (D k K ∘ x)) = ⊤ := sorry

end PBasis

/-! ### Lemma_15_46_3 (from Chap15) -/
universe u v

section

variable {K : Type u} [Field K] {A : Type v} [Nonempty A]

/-
Domain triage:
* primary domain: linear algebra over subfields and directed intersections of subfields;
* sampled owner declarations:
  - `Subfield.mem_iInf`,
  - `Submodule.restrictScalars`,
  - `Submodule.pi`,
  - `Subalgebra.mem_bot`;
* best owner abstraction: for a subfield `k ≤ K`, the vectors of `K^n` with all coordinates in `k`
  are the canonical `k`-submodule `k.vectorSubmodule n`;
* primitive data: the family of subfields `Kα` and the `K`-subspace `V`;
* derived API: existence of a nonzero vector in `V` whose coordinates lie in a given subfield;
* layer triage:
  - `source-facing`: the existence criterion of Lemma `15.46.3`;
  - `core/canonical`: `Submodule.restrictScalars`, `Submodule.pi`, and `Subfield.mem_iInf`;
  - `bridge/view`: `Subfield.vectorSubmodule`, the coordinatewise copy of `k` in `K^n`.
-/

namespace Subfield

/-- The coordinatewise copy of `k` inside `K^n`, viewed as a `k`-submodule of `K^n`. -/
abbrev vectorSubmodule (k : Subfield K) (n : ℕ) : Submodule k (Fin n → K) :=
  Submodule.pi Set.univ (fun _ : Fin n ↦ (⊥ : Subalgebra k K).toSubmodule)

end Subfield

-- Proof sketch: for `n = 0`, the coordinatewise submodule `k.vectorSubmodule 0` is trivial, so
-- both
-- sides are false. For `n = 1`, the claim is exactly the statement that membership in
-- `k = ⨅ α, Kα α` is equivalent to membership in every `Kα α` via `Subfield.mem_iInf`; the
-- nonemptiness hypothesis rules out the degenerate empty intersection `⨅ α, Kα α = ⊤`. For the
-- inductive step, first study the intersection of `V` with the last `n - 1` coordinates, then
-- choose an index `α` for which this smaller intersection over `Kα α` is trivial. A nonzero
-- vector in `V` with coordinates in `Kα α` can then be normalized so that its first coordinate is
-- `1`, forcing every other `Kα α`-rational vector in `V` to be a scalar multiple of it. The
-- downward directedness of the family and the hypothesis `k = ⨅ α, Kα α` then show that the
-- remaining coordinates already lie in `k`.
/-- Lemma 15.46.3: for a nonempty downward directed family of subfields of `K` whose intersection
is `k`, a `K`-subspace of `K^n` contains a nonzero vector with all coordinates in `k` if and only
if it contains such a vector over every subfield in the family. -/
theorem exists_nonzero_vector_in_base_subfield_iff_forall_exists_nonzero_vector_in_family
    (k : Subfield K) (Kα : A → Subfield K) (h_inter : k = ⨅ α, Kα α)
    (h_directed : Directed (· ≥ ·) Kα) {n : ℕ} (V : Submodule K (Fin n → K)) :
    (∃ v ∈ V.restrictScalars k ⊓ k.vectorSubmodule n, v ≠ 0) ↔
      ∀ α, ∃ v ∈ V.restrictScalars (Kα α) ⊓ (Kα α).vectorSubmodule n, v ≠ 0 := sorry

end

/-! ### Lemma_15_46_4 (from Chap15) -/
open KaehlerDifferential
open scoped FrobeniusSubfield

universe u v w

section

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]

local instance : Algebra (ZMod p) K := ZMod.algebra K p

variable {A : Type v} (Kα : A → Subfield K)

private instance instSMulSubfield (k : Subfield K) : SMul (ZMod p) k :=
  (inferInstance : Algebra (ZMod p) k).toSMul

private theorem coe_algebraMap_zmod_subfield (k : Subfield K) (x : ZMod p) :
    (((algebraMap (ZMod p) k) x : k) : K) = algebraMap (ZMod p) K x :=
  congrArg (fun f : ZMod p →+* K ↦ f x)
    (RingHom.ext_zmod ((algebraMap k K).comp (algebraMap (ZMod p) k)) (algebraMap (ZMod p) K))

private theorem coe_zmod_smul_subfield (k : Subfield K) (x : ZMod p) (y : k) :
    ((x • y : k) : K) = x • (y : K) := by
  simpa [Algebra.smul_def] using
    congrArg (fun z : K ↦ z * (y : K)) (coe_algebraMap_zmod_subfield k x)

private instance instIsScalarTowerSubfield (k : Subfield K) : IsScalarTower (ZMod p) k K where
  smul_assoc x y z := by
    change (((x • y : k) : K) * z) = x • y • z
    rw [coe_zmod_smul_subfield k x y]
    exact smul_mul_assoc x (y : K) z

local notation "kaehlerDifferentialMapTo" α =>
  @KaehlerDifferential.map (ZMod p) (Kα α) _ _
    (inferInstance : Algebra (ZMod p) (Kα α)) K K _ _
    (inferInstance : Algebra (ZMod p) K) (inferInstance : Algebra K K)
    (inferInstance : Algebra (Kα α) K) (inferInstance : Algebra (ZMod p) K)
    (inferInstance : IsScalarTower (ZMod p) K K) (instIsScalarTowerSubfield (Kα α))
    (inferInstance : SMulCommClass (Kα α) K K)

/-
Domain triage:
* primary domain: fields of characteristic `p`, Frobenius subfields, and the canonical
  Kähler-differential maps induced by `𝔽_p ⊆ K_α ⊆ K`, together with the chapter owner
  `pPowerCompositum` for the compositum `L^p K_α`;
* sampled owner declarations:
  - `frobeniusSubfield`,
  - `pPowerCompositum`,
  - `KaehlerDifferential.map`,
  - `Subfield.map`,
  - `Subfield.mem_iInf`;
* best owner abstraction: the primitive owner data are the family of subfields `Kα` and the
  canonical owner map `KaehlerDifferential.map (ZMod p) k K K`; the
  intersection-of-kernels and
  Frobenius-compositum statements are derived API, with the latter expressed through
  `pPowerCompositum` rather than a parallel raw `⊔`/`Subfield.map` spelling;
* layer triage:
  - `source-facing`: the two clauses of Lemma `15.46.4`;
  - `core/canonical`: `K^[p]`, `pPowerCompositum`, `KaehlerDifferential.map`, and the
    lattice operations on subfields;
  - `bridge/view`: no extra bridge owner is needed beyond the reusable comparison-map owner
  above; the source-facing statements use it together with `pPowerCompositum`.
-/

-- Proof sketch: choose a `p`-basis of `K` over `𝔽_p` using Lemma `15.46.2`, identify an element of
-- the intersection of all kernels with a finite linear relation over every `K_α`, and apply the
-- directed-intersection criterion of Lemma `15.46.3` to force the coefficients into `K^p`, where
-- Lemma `15.46.2` rules out any nontrivial relation.
/-- Lemma 15.46.4 (1): if the subfields `K_α` intersect in `K^p` and are downward directed as a
nonempty family, then the intersection of the kernels of the canonical maps
`Ω[K⁄𝔽_p] → Ω[K⁄K_α]` is zero. -/
theorem iInf_ker_kaehlerDifferentialMap_eq_bot
    (h_nonempty : Nonempty A) (h_inter : K^[p] = ⨅ α, Kα α) (h_directed : Directed (· ≥ ·) Kα) :
    (⨅ α, LinearMap.ker (kaehlerDifferentialMapTo α)) = ⊥ := by
  sorry

-- Proof sketch: reduce along intermediate fields to the primitive-extension case, then treat the
-- separable and purely inseparable degree-`p` cases separately. In each case, a basis of `L` over
-- `K` adapted to a primitive generator shows that intersecting the composita `L^p K_α` recovers
-- exactly `L^p` because the coefficients intersect back to `K^p`.
section FiniteExtension

variable {L : Type w} [Field L] [Algebra K L] [FiniteDimensional K L] [CharP L p]

/-- Lemma 15.46.4 (2): for every finite extension `L / K` over a field `K` of characteristic `p`,
the `p`-th-power subfield `L^p` is the
intersection of the composita `L^p K_α` inside `L` for a downward directed family `(K_α)` with
intersection `K^p`. -/
theorem frobeniusSubfield_eq_iInf_pPowerCompositum_of_finiteExtension
    (h_inter : K^[p] = ⨅ α, Kα α) (h_directed : Directed (· ≥ ·) Kα) :
    L^[p] = ⨅ α, (pPowerCompositum p ((Kα α).map (algebraMap K L)) L).toSubfield := by
  sorry

end FiniteExtension

end

/-! ### Lemma_15_46_5 (from Chap15) -/
noncomputable section

open MvPowerSeries
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
    IsDomain (mixedPowerSeriesPolynomialRing σ τ k) := sorry

-- Proof sketch: the same domain argument applies to the coefficient subfield `k_J`, giving that
-- the fresh-variable presentation of `A_J` is also a domain.
private instance (σ : Type v) (τ : Type w) {p : ℕ} [Fact p.Prime] [Finite σ] [Finite τ]
    {ι : Type z} [DecidableEq ι] (k : Type u) [Field k] [CharP k p] (x : ι → k) (J : Finset ι) :
    IsDomain (pthPowerMixedSubringModel σ τ k x J) := sorry

-- Proof sketch: the ambient ring has characteristic `p`, and characteristic is inherited by the
-- fraction field of a domain.
private instance {p : ℕ} {σ : Type v} {τ : Type w} [Finite σ] [Finite τ] (k : Type u)
    [Field k] [CharP k p] : CharP (FractionRing (mixedPowerSeriesPolynomialRing σ τ k)) p := sorry

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
variable (x : ι → k)

/- Textbook notation for the intrinsic mixed `p`-power subring `A_J ⊂ A`. The ambient parameters
are fixed by the current section, so the notation stays local to the owner theorem surface. -/
local notation "A_[" J "]" => pthPowerMixedSubring σ τ k x J

/- Textbook notation for the induced fraction subfield `K_J` of the ambient fraction field. -/
local notation "K_[" J "]" => pthPowerMixedFractionSubfield σ τ k x J

-- Proof sketch: the omitted basis elements are exactly those indexed by the finite set `J`, so
-- the complements define a downward directed family. Taking `p`-th powers of the formal and
-- polynomial variables transports this reverse-direction directedness to the source-facing
-- fraction subfields `K_[J]` of the ambient fraction field.
/-- For a field `k` of characteristic `p` with `p`-basis `x` over `𝔽_p`, the source-facing
fraction subfields `K_[J]` intersect in the Frobenius subfield of the ambient fraction field. -/
theorem iInf_pthPowerMixedFractionSubfield_eq_frobeniusSubfield
    (hx : IsPBasis p (ZMod p) k x) :
    (⨅ J, K_[J]) = K^[p] := sorry

/-- For a family `x` in a field `k` of characteristic `p`, the source-facing fraction subfields
`K_[J]` are downward directed under inclusion. -/
theorem directed_pthPowerMixedFractionSubfield
    : Directed (· ≥ ·) fun J : Finset ι ↦ K_[J] :=
  sorry

-- Proof sketch: because only finitely many basis elements are omitted from `k_J`, the extension
-- `k_J ⊆ k` is finite. Lemma `10.97.7` gives finiteness for the corresponding extension on formal
-- power series, and adjoining finitely many polynomial variables preserves module-finiteness.
/-- The ambient ring `A` is finite over each source-facing intrinsic subring `A_[J] ⊂ A`. -/
theorem pthPowerMixedSubring_finite
    (hx : IsPBasis p (ZMod p) k x) (J : Finset ι) :
    Module.Finite (A_[J]) A := sorry

end
