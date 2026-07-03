import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_10_82_6 (from Chap10) -/
noncomputable section

universe u

open CategoryTheory Limits
open scoped DirectSum

/-
Domain triage:
- primary domain: universally exact short complexes of modules, specialized to explicit
  `ℤ`-module examples built from a direct sum, a product, and a quotient;
- sampled owner declarations: `CategoryTheory.ShortComplex.UniversallyExact`,
  `CategoryTheory.ShortComplex.ShortExact.universallyExact_of_flat_X₃`,
  `CategoryTheory.ShortComplex.Splitting.ofHasBinaryBiproduct`,
  `CategoryTheory.ShortComplex.UniversallyExact.flat_X₁`;
- owner choice: `ShortComplex.UniversallyExact` is the core/canonical owner abstraction, while the
  explicit quotient short complex and its distinguished class are the source-facing data for this
  example;
- primitive data vs. derived API: `integerProductModuloDirectSum`,
  `integerDirectSumProductShortComplex`, and `integerDivisibilityWitnessClass` are the primitive
  source-facing objects, while universal exactness, flatness consequences, and non-splitting are
  derived statements about that owner.
-/

local notation "directSumToProduct" =>
  (DirectSum.coeFnLinearMap ℤ : (⨁ _ : ℕ, ℤ) →ₗ[ℤ] (ℕ → ℤ))

/-- The quotient map
`\prod_{n \ge 1} \mathbf Z ⟶ (\prod_{n \ge 1} \mathbf Z)/(\bigoplus_{n \ge 1} \mathbf Z)`. -/
def integerProductModuloDirectSum :
    (ℕ → ℤ) →ₗ[ℤ] ((ℕ → ℤ) ⧸ LinearMap.range directSumToProduct) :=
  (LinearMap.range directSumToProduct).mkQ

/-- The canonical short complex
`⨁_{n \ge 1} \mathbf Z ⟶ \prod_{n \ge 1} \mathbf Z ⟶
(\prod_{n \ge 1} \mathbf Z)/(\bigoplus_{n \ge 1} \mathbf Z)`. -/
def integerDirectSumProductShortComplex : ShortComplex (ModuleCat ℤ) :=
  ModuleCat.shortComplexOfCompEqZero
    directSumToProduct
    integerProductModuloDirectSum
    (LinearMap.range_mkQ_comp directSumToProduct)

/-- The image of `(2,2^2,2^3,\ldots)` in the quotient module. -/
def integerDivisibilityWitness : ℕ → ℤ :=
  fun n ↦ (2 : ℤ) ^ (n + 1)

/-- The class of `(2,2^2,2^3,\ldots)` in the quotient module. -/
def integerDivisibilityWitnessClass : integerDirectSumProductShortComplex.X₃ :=
  integerProductModuloDirectSum integerDivisibilityWitness

/-- Helper for Example 10.82.6: every finitely supported integer sequence comes from the direct
sum inside the product. -/
theorem mem_range_directSumToProduct_of_hasFiniteSupport (x : ℕ → ℤ)
    (hx : x.HasFiniteSupport) : x ∈ LinearMap.range directSumToProduct := by
  classical
  -- Realize the finitely supported sequence as a `DFinsupp`, hence as an element of the direct sum.
  refine ⟨DFinsupp.mk hx.toFinset (fun i ↦ x i), ?_⟩
  ext n
  simp only [DirectSum.coeFnLinearMap_apply, DFinsupp.mk_apply]
  by_cases hn : n ∈ hx.toFinset
  · simp [hn]
  · have hxn : x n = 0 := by
      simpa [Set.Finite.mem_toFinset] using hn
    simp [hn, hxn]

/-- Helper for Example 10.82.6: every element of the direct sum image has finite support as an
integer sequence. -/
theorem hasFiniteSupport_of_mem_range_directSumToProduct {x : ℕ → ℤ}
    (hx : x ∈ LinearMap.range directSumToProduct) : x.HasFiniteSupport := by
  classical
  rcases hx with ⟨y, rfl⟩
  -- The ambient direct-sum element already carries a finite support.
  refine y.support.finite_toSet.subset ?_
  intro n hn
  simpa [DirectSum.coeFnLinearMap_apply, DFinsupp.mem_support_iff, Function.mem_support] using hn

/-- Helper for Example 10.82.6: the quotient
`(\prod \mathbf Z)/(\bigoplus \mathbf Z)` is torsion-free. -/
theorem integerProductQuotient_isTorsionFree :
    Module.IsTorsionFree ℤ integerDirectSumProductShortComplex.X₃ := by
  refine Module.IsTorsionFree.of_smul_eq_zero ?_
  intro a q hq
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range directSumToProduct) q
    -- Pull the vanishing scalar multiple back to the product, where it becomes a finite-support
    -- statement.
    have haxZero : integerProductModuloDirectSum (a • x) = 0 := by
      simpa [integerProductModuloDirectSum] using hq
    have haxRange : a • x ∈ LinearMap.range directSumToProduct := by
      simpa [integerProductModuloDirectSum] using
        (Submodule.Quotient.mk_eq_zero (LinearMap.range directSumToProduct)).mp haxZero
    have haxFinite : (a • x).HasFiniteSupport :=
      hasFiniteSupport_of_mem_range_directSumToProduct haxRange
    have hxFinite : x.HasFiniteSupport := by
      refine haxFinite.subset ?_
      intro n hn
      have haxn : (a • x) n ≠ 0 := by
        simpa [Pi.smul_apply, smul_eq_mul] using Int.mul_ne_zero ha hn
      simpa [Function.mem_support] using haxn
    -- Once the representative has finite support, it already lies in the direct sum.
    have hxRange : x ∈ LinearMap.range directSumToProduct :=
      mem_range_directSumToProduct_of_hasFiniteSupport x hxFinite
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range directSumToProduct)).2 hxRange

/-- Flatness of the product `\prod_{n \ge 1} \mathbf Z`. -/
-- Proof sketch: over `ℤ`, torsion-free modules are flat; the product of copies of `ℤ` is
-- torsion-free because scalar multiplication is coordinatewise.
theorem integerProduct_flat : Module.Flat ℤ (ℕ → ℤ) := by
  -- Over `ℤ`, torsion-free modules are flat.
  infer_instance

/-- Flatness of the quotient `(\prod \mathbf Z)/(\bigoplus \mathbf Z)`. -/
-- Proof sketch: over `ℤ`, it suffices to show the quotient is torsion-free and then apply the
-- torsion-free criterion for flatness of modules over a PID.
theorem integerProductQuotient_flat : Module.Flat ℤ integerDirectSumProductShortComplex.X₃ := by
  -- The Dedekind-domain criterion turns the torsion-free quotient into a flat module.
  let _ : Module.IsTorsionFree ℤ integerDirectSumProductShortComplex.X₃ :=
    integerProductQuotient_isTorsionFree
  infer_instance

/-- Example 10.82.6 (1): the sequence
`0 → \bigoplus \mathbf Z → \prod \mathbf Z → (\prod \mathbf Z)/(\bigoplus \mathbf Z) → 0`
is universally exact. -/
-- Proof sketch: combine short exactness of the quotient sequence with flatness of the quotient
-- term, then apply the flat-cokernel owner theorem
-- `ShortComplex.ShortExact.universallyExact_of_flat_X₃`.
theorem integer_direct_sum_product_sequence_universally_exact :
    integerDirectSumProductShortComplex.UniversallyExact :=
  by
  -- First package the canonical quotient row as a short exact sequence.
  have hShortExact : integerDirectSumProductShortComplex.ShortExact := by
    refine ModuleCat.shortComplex_shortExact integerDirectSumProductShortComplex ?_ ?_ ?_
    · simpa [integerDirectSumProductShortComplex, integerProductModuloDirectSum] using
        LinearMap.exact_map_mkQ_range directSumToProduct
    · intro x y hxy
      exact DFinsupp.ext fun n ↦ congrArg (fun f ↦ f n) hxy
    · simpa [integerDirectSumProductShortComplex, integerProductModuloDirectSum] using
        Submodule.mkQ_surjective (LinearMap.range directSumToProduct)
  -- Then apply the flat-cokernel universal-exactness criterion.
  let _ : Module.Flat ℤ integerDirectSumProductShortComplex.X₃ := integerProductQuotient_flat
  exact CategoryTheory.ShortComplex.ShortExact.universallyExact_of_flat_X₃ hShortExact

/-- Helper for Example 10.82.6: an integer divisible by every power of `2` is zero. -/
theorem int_zero_of_divisible_by_all_two_powers (z : ℤ)
    (hz : ∀ n : ℕ, ∃ w : ℤ, ((2 : ℤ) ^ n) • w = z) : z = 0 := by
  rcases hz (Int.natAbs z) with ⟨w, hw⟩
  -- The exponent `natAbs z` already forces the divisor to be larger than `|z|`.
  have hdiv : ((2 : ℤ) ^ Int.natAbs z) ∣ z := by
    exact ⟨w, by simpa [smul_eq_mul, eq_comm] using hw⟩
  have hlt : |z| < (2 : ℤ) ^ Int.natAbs z := by
    have hpow_nat : Int.natAbs z < 2 ^ Int.natAbs z := Nat.lt_two_pow_self
    have hpow : (Int.natAbs z : ℤ) < (2 : ℤ) ^ Int.natAbs z := by
      exact_mod_cast hpow_nat
    rw [Int.abs_eq_natAbs]
    exact hpow
  exact Int.eq_zero_of_abs_lt_dvd hdiv hlt

/-- Helper for Example 10.82.6: a product element divisible by every power of `2` is zero. -/
theorem pi_zero_of_divisible_by_all_two_powers (v : ℕ → ℤ)
    (hv : ∀ n : ℕ, ∃ w : ℕ → ℤ, ((2 : ℤ) ^ n) • w = v) : v = 0 := by
  ext k
  -- Reduce to the one-coordinate integer statement.
  apply int_zero_of_divisible_by_all_two_powers
  intro n
  rcases hv n with ⟨w, hw⟩
  refine ⟨w k, ?_⟩
  exact congrArg (fun f ↦ f k) hw

/-- Helper for Example 10.82.6: the distinguished quotient class is nonzero. -/
theorem integerDivisibilityWitnessClass_ne_zero :
    integerDivisibilityWitnessClass ≠ 0 := by
  intro hZero
  -- If the quotient class vanished, the witness sequence would already lie in the direct sum.
  have hRange : integerDivisibilityWitness ∈ LinearMap.range directSumToProduct := by
    simpa [integerDivisibilityWitnessClass, integerProductModuloDirectSum] using
      (Submodule.Quotient.mk_eq_zero (LinearMap.range directSumToProduct)).mp hZero
  have hFinite : integerDivisibilityWitness.HasFiniteSupport :=
    hasFiniteSupport_of_mem_range_directSumToProduct hRange
  let s := hFinite.toFinset
  let m : ℕ := s.sup fun n : ℕ ↦ n
  have hNotMem : m + 1 ∉ s := by
    intro hMem
    have hLe : m + 1 ≤ s.sup (fun n : ℕ ↦ n) := by
      simpa using (Finset.le_sup (f := fun n : ℕ ↦ n) hMem)
    have hLe' : m + 1 ≤ m := by
      simpa [m] using hLe
    exact Nat.not_succ_le_self m hLe'
  have hZeroCoord : integerDivisibilityWitness (m + 1) = 0 := by
    simpa [s, m, Set.Finite.mem_toFinset] using hNotMem
  have hNeCoord : integerDivisibilityWitness (m + 1) ≠ 0 := by
    simp [integerDivisibilityWitness]
  exact hNeCoord hZeroCoord

/-- Helper for Example 10.82.6: modulo the direct sum, the distinguished class is divisible by
every power of `2`. -/
theorem integerDivisibilityWitnessClass_two_pow_divisible (n : ℕ) :
    ∃ y : integerDirectSumProductShortComplex.X₃,
      ((2 : ℤ) ^ n) • y = integerDivisibilityWitnessClass := by
  let divided : ℕ → ℤ :=
    fun k ↦ if h : n ≤ k + 1 then (2 : ℤ) ^ (k + 1 - n) else 0
  refine ⟨integerProductModuloDirectSum divided, ?_⟩
  -- The tail divides exactly, and the finite initial discrepancy lies in the direct sum.
  rw [← sub_eq_zero]
  have hmkQ :
      (LinearMap.range directSumToProduct).mkQ
        (((2 : ℤ) ^ n) • divided - integerDivisibilityWitness) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply mem_range_directSumToProduct_of_hasFiniteSupport
    refine (Set.toFinite {k : ℕ | k < n}).subset ?_
    intro k hk
    have hkNe : (((2 : ℤ) ^ n) • divided - integerDivisibilityWitness) k ≠ 0 := by
      simpa [Function.mem_support] using hk
    by_contra hkn
    have hkge : n ≤ k := Nat.not_lt.mp hkn
    have hk' : n ≤ k + 1 := Nat.le_trans hkge (Nat.le_succ k)
    have hCoord :
        (((2 : ℤ) ^ n) • divided - integerDivisibilityWitness) k = 0 := by
      have hpow :
          (2 : ℤ) ^ n * (2 : ℤ) ^ (k + 1 - n) = (2 : ℤ) ^ (k + 1) := by
        rw [← pow_add, Nat.add_sub_of_le hk']
      calc
        (((2 : ℤ) ^ n) • divided - integerDivisibilityWitness) k
            = (2 : ℤ) ^ n * (2 : ℤ) ^ (k + 1 - n) - (2 : ℤ) ^ (k + 1) := by
                simp [divided, integerDivisibilityWitness, hk']
        _ = (2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ (k + 1) := by rw [hpow]
        _ = 0 := sub_self _
    exact hkNe hCoord
  have hmk :
      integerProductModuloDirectSum (((2 : ℤ) ^ n) • divided - integerDivisibilityWitness) = 0 := by
    simpa [integerProductModuloDirectSum] using hmkQ
  simpa [map_sub, map_smul, integerDivisibilityWitnessClass] using hmk

/-- Companion to Example 10.82.6 (1): every `\mathbf Z`-linear map from
`(\prod \mathbf Z)/(\bigoplus \mathbf Z)` to `\prod \mathbf Z` kills the class of
`(2,2^2,2^3,\ldots)`. -/
-- Proof sketch: the quotient class lies in `2^n M_3` for every `n`, so its image under any
-- linear map is a vector in `\prod \mathbf Z` divisible by every `2^n`, hence zero
-- coordinatewise.
theorem integer_direct_sum_product_hom_kills_witness
    (φ : integerDirectSumProductShortComplex.X₃ →ₗ[ℤ] (ℕ → ℤ)) :
    φ integerDivisibilityWitnessClass = 0 := by
  -- The image remains divisible by every power of `2`, so the coordinatewise arithmetic lemma
  -- forces it to vanish.
  apply pi_zero_of_divisible_by_all_two_powers
  intro n
  rcases integerDivisibilityWitnessClass_two_pow_divisible n with ⟨y, hy⟩
  refine ⟨φ y, ?_⟩
  simpa using congrArg φ hy

/-- Companion to Example 10.82.6 (1): the quotient map admits no section. -/
-- Proof sketch: if `s` were a section, the previous theorem would give
-- `s integerDivisibilityWitnessClass = 0`; applying the quotient map and using the section identity
-- would force the distinguished class itself to vanish, contradiction.
theorem integer_direct_sum_product_quotientMap_has_no_section :
    ¬ ∃ s : integerDirectSumProductShortComplex.X₃ →ₗ[ℤ] (ℕ → ℤ),
      integerProductModuloDirectSum.comp s = LinearMap.id := by
  intro hs
  rcases hs with ⟨s, hs⟩
  have hs_eval : ∀ x, integerProductModuloDirectSum (s x) = x := by
    intro x
    exact DFunLike.congr_fun hs x
  have hkills : s integerDivisibilityWitnessClass = 0 :=
    integer_direct_sum_product_hom_kills_witness s
  have hZero : integerDivisibilityWitnessClass = 0 := by
    calc
      integerDivisibilityWitnessClass = integerProductModuloDirectSum (s integerDivisibilityWitnessClass) := by
        symm
        exact hs_eval integerDivisibilityWitnessClass
      _ = 0 := by simpa [hkills]
  exact integerDivisibilityWitnessClass_ne_zero hZero

/-- Companion to Example 10.82.6 (1): the quotient sequence does not split. -/
-- Proof sketch: a splitting datum of the canonical quotient short complex provides a
-- section `σ.s` of the quotient map, contradicting
-- `integer_direct_sum_product_quotientMap_has_no_section`.
theorem integer_direct_sum_product_sequence_not_split :
    ¬ Nonempty integerDirectSumProductShortComplex.Splitting := by
  intro hSplit
  rcases hSplit with ⟨σ⟩
  apply integer_direct_sum_product_quotientMap_has_no_section
  refine ⟨σ.s.hom, ?_⟩
  ext x
  exact congrArg (fun f ↦ f x) σ.s_g

/-- The split short complex `0 → M → M \oplus M → M → 0` from Example 10.82.6 (2). -/
def selfSumShortComplex {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (biprod.inl : M ⟶ M ⊞ M)
    (biprod.snd : M ⊞ M ⟶ M)
    (by simp)

/-- Example 10.82.6 (2): the split self-sum sequence is universally exact. -/
-- Proof sketch: apply `ShortComplex.Splitting.ofHasBinaryBiproduct` to the canonical binary
-- biproduct sequence `0 → M → M ⊞ M → M → 0`, then use that splittings are universally exact.
theorem selfSumShortComplex_universallyExact
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    (selfSumShortComplex M).UniversallyExact := by
  let s : (selfSumShortComplex M).Splitting := ShortComplex.Splitting.ofHasBinaryBiproduct M M
  -- The canonical biproduct splitting is universally exact by Example `10.82.2`.
  exact CategoryTheory.ShortComplex.Splitting.universallyExact (R := R) s

/-- In Example 10.82.6 (2), the left term of the self-sum sequence is non-flat when `M` is. -/
theorem selfSumShortComplex_not_flat_X₁
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R (selfSumShortComplex M).X₁ := by
  -- Here `X₁` is definitionally the chosen module `M`.
  simpa [selfSumShortComplex] using hM

/-- In Example 10.82.6 (2), the middle term of the self-sum sequence is non-flat when `M` is. -/
-- Proof sketch: if `M ⊞ M` were flat, then universal exactness of the split sequence would imply
-- flatness of `X₁ = M` by `ShortComplex.UniversallyExact.flat_X₁`, contradicting `hM`.
theorem selfSumShortComplex_not_flat_X₂
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R (selfSumShortComplex M).X₂ := by
  intro hFlat
  let _ : Module.Flat R (selfSumShortComplex M).X₂ := hFlat
  -- Universal exactness of the split row propagates flatness back to the left term.
  have hFlatLeft : Module.Flat R (selfSumShortComplex M).X₁ :=
    flat_left_term_of_universallyExact (selfSumShortComplex_universallyExact M)
  exact hM (by simpa [selfSumShortComplex] using hFlatLeft)

/-- In Example 10.82.6 (2), the right term of the self-sum sequence is non-flat when `M` is. -/
theorem selfSumShortComplex_not_flat_X₃
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R (selfSumShortComplex M).X₃ := by
  -- Here `X₃` is again definitionally `M`.
  simpa [selfSumShortComplex] using hM

/-- Helper for Example 10.82.6: binary biproducts of short exact short complexes of modules should
again be short exact. -/
theorem shortExact_biprod {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (hT : T.ShortExact) :
    (S ⊞ T).ShortExact := by
  -- TODO: transport the biproduct short complex to the product-model row using the pointwise
  -- `ShortComplex.πᵢ.mapBiprod` isomorphisms and `ModuleCat.biprodIsoProd`, then read exactness,
  -- injectivity, and surjectivity off `LinearMap.prodMap`.
  sorry

/-- Helper for Example 10.82.6: binary biproducts of universally exact short complexes of modules
should again be universally exact. -/
theorem universallyExact_biprod {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{u} R)} (hS : S.UniversallyExact) (hT : T.UniversallyExact) :
    (S ⊞ T).UniversallyExact := by
  -- TODO: first use `shortExact_biprod` for the short-exact part. Then, for each tensor module,
  -- either transport the tensorized biproduct row through the same pointwise biproduct/product
  -- identifications or use the functorial biproduct comparison for `tensorLeft`.
  sorry

/-- The concrete short complex from Example 10.82.6 (3), obtained by taking the direct sum of the
non-split universally exact quotient sequence from clause `(1)` with the split self-sum sequence
from clause `(2)` specialized to `ZMod 2`. -/
def universallyExactNonsplitNonflatShortComplex : ShortComplex (ModuleCat.{0} ℤ) :=
  integerDirectSumProductShortComplex ⊞ selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))

/-- Example 10.82.6 (3): the direct-sum short complex constructed above is universally exact. -/
-- Proof sketch: clause `(1)` gives universal exactness of
-- `integerDirectSumProductShortComplex`, clause `(2)` gives universal exactness of the `ZMod 2`
-- self-sum sequence, and binary direct sums preserve the universal exactness criterion.
theorem universallyExactNonsplitNonflatShortComplex_universallyExact :
    universallyExactNonsplitNonflatShortComplex.UniversallyExact := by
  -- Apply the general biproduct stability result to clause `(1)` and the split clause `(2)`.
  simpa [universallyExactNonsplitNonflatShortComplex] using
    universallyExact_biprod integer_direct_sum_product_sequence_universally_exact
      (selfSumShortComplex_universallyExact (ModuleCat.of ℤ (ZMod 2)))

/-- Example 10.82.6 (3): the direct-sum short complex constructed above does not split. -/
-- Proof sketch: a splitting of the direct sum would restrict along the canonical inclusion of the
-- first summand and project back to a splitting of
-- `integerDirectSumProductShortComplex`, contradicting
-- `integer_direct_sum_product_sequence_not_split`.
theorem universallyExactNonsplitNonflatShortComplex_not_split :
    ¬ Nonempty universallyExactNonsplitNonflatShortComplex.Splitting := by
  intro hSplit
  rcases hSplit with ⟨σ⟩
  let ι₃ : integerDirectSumProductShortComplex.X₃ ⟶
      universallyExactNonsplitNonflatShortComplex.X₃ :=
    (biprod.inl : integerDirectSumProductShortComplex ⟶
      universallyExactNonsplitNonflatShortComplex).τ₃
  let π₂ : universallyExactNonsplitNonflatShortComplex.X₂ ⟶
      integerDirectSumProductShortComplex.X₂ :=
    (biprod.fst : universallyExactNonsplitNonflatShortComplex ⟶
      integerDirectSumProductShortComplex).τ₂
  let π₃ : universallyExactNonsplitNonflatShortComplex.X₃ ⟶
      integerDirectSumProductShortComplex.X₃ :=
    (biprod.fst : universallyExactNonsplitNonflatShortComplex ⟶
      integerDirectSumProductShortComplex).τ₃
  have hcomm :
      π₂ ≫ integerDirectSumProductShortComplex.g =
        universallyExactNonsplitNonflatShortComplex.g ≫ π₃ := by
    simpa [π₂, π₃] using
      (biprod.fst : universallyExactNonsplitNonflatShortComplex ⟶
        integerDirectSumProductShortComplex).comm₂₃
  have hinl_fst : ι₃ ≫ π₃ = 𝟙 _ := by
    simpa only [ShortComplex.comp_τ₃, ShortComplex.id_τ₃, ι₃, π₃] using congrArg
      (fun k => (ShortComplex.π₃ : ShortComplex (ModuleCat.{0} ℤ) ⥤ ModuleCat.{0} ℤ).map k)
      (biprod.inl_fst : (biprod.inl : integerDirectSumProductShortComplex ⟶
        universallyExactNonsplitNonflatShortComplex) ≫
          (biprod.fst : universallyExactNonsplitNonflatShortComplex ⟶
            integerDirectSumProductShortComplex) = 𝟙 _)
  -- Project the putative splitting to a section of the nonsplit quotient sequence.
  apply integer_direct_sum_product_quotientMap_has_no_section
  refine ⟨(ι₃ ≫ σ.s ≫ π₂).hom, ?_⟩
  ext x
  -- The section identity survives after restricting to the first summand and projecting back.
  have hsection :
      ι₃ ≫ σ.s ≫ π₂ ≫ integerDirectSumProductShortComplex.g = 𝟙 _ := by
    calc
      ι₃ ≫ σ.s ≫ π₂ ≫ integerDirectSumProductShortComplex.g
          = ι₃ ≫ σ.s ≫ (π₂ ≫ integerDirectSumProductShortComplex.g) := by
              simp
      _ = ι₃ ≫ σ.s ≫ (universallyExactNonsplitNonflatShortComplex.g ≫ π₃) := by rw [hcomm]
      _ = ι₃ ≫ (σ.s ≫ universallyExactNonsplitNonflatShortComplex.g) ≫ π₃ := by
            simp
      _ = ι₃ ≫ π₃ := by simp [σ.s_g]
      _ = 𝟙 _ := hinl_fst
  simpa using congrArg (fun f : integerDirectSumProductShortComplex.X₃ ⟶
    integerDirectSumProductShortComplex.X₃ => f x) hsection

/-- Example 10.82.6 (3): the left term of the constructed direct-sum short complex is non-flat. -/
-- Proof sketch: the `ZMod 2` summand is a retract of `X₁`, so flatness of `X₁` would imply
-- flatness of `ZMod 2`, contradiction.
theorem universallyExactNonsplitNonflatShortComplex_not_flat_X₁ :
    ¬ Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₁ := by
  intro hFlat
  let _ : Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₁ := hFlat
  let ι₁ : ModuleCat.of ℤ (ZMod 2) ⟶ universallyExactNonsplitNonflatShortComplex.X₁ :=
    (biprod.inr : selfSumShortComplex (ModuleCat.of ℤ (ZMod 2)) ⟶
      universallyExactNonsplitNonflatShortComplex).τ₁
  let π₁ : universallyExactNonsplitNonflatShortComplex.X₁ ⟶ ModuleCat.of ℤ (ZMod 2) :=
    (biprod.snd : universallyExactNonsplitNonflatShortComplex ⟶
      selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))).τ₁
  have hRetractEq : π₁.hom.comp ι₁.hom = LinearMap.id := by
    have hComp : ι₁ ≫ π₁ = 𝟙 _ := by
      simpa only [ShortComplex.comp_τ₁, ShortComplex.id_τ₁, ι₁, π₁] using congrArg
        (fun k => (ShortComplex.π₁ : ShortComplex (ModuleCat.{0} ℤ) ⥤ ModuleCat.{0} ℤ).map k)
        (biprod.inr_snd : (biprod.inr : selfSumShortComplex (ModuleCat.of ℤ (ZMod 2)) ⟶
          universallyExactNonsplitNonflatShortComplex) ≫
            (biprod.snd : universallyExactNonsplitNonflatShortComplex ⟶
              selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))) = 𝟙 _)
    ext x
    simpa using congrArg (fun f : ModuleCat.of ℤ (ZMod 2) ⟶ ModuleCat.of ℤ (ZMod 2) => f.hom x)
      hComp
  -- Retract the left term onto the `ZMod 2` summand of the split row.
  have hRetract :
      Module.Flat ℤ (ModuleCat.of ℤ (ZMod 2)) :=
    Module.Flat.of_retract ι₁.hom π₁.hom hRetractEq
  exact zmodTwo_not_flat (by simpa using hRetract)

/-- Example 10.82.6 (3): the middle term of the constructed direct-sum short complex is non-flat. -/
theorem universallyExactNonsplitNonflatShortComplex_not_flat_X₂ :
    ¬ Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₂ := by
  intro hFlat
  let _ : Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₂ := hFlat
  let ι₂ : (selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))).X₂ ⟶
      universallyExactNonsplitNonflatShortComplex.X₂ :=
    (biprod.inr : selfSumShortComplex (ModuleCat.of ℤ (ZMod 2)) ⟶
      universallyExactNonsplitNonflatShortComplex).τ₂
  let π₂ : universallyExactNonsplitNonflatShortComplex.X₂ ⟶
      (selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))).X₂ :=
    (biprod.snd : universallyExactNonsplitNonflatShortComplex ⟶
      selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))).τ₂
  have hRetractEq : π₂.hom.comp ι₂.hom = LinearMap.id := by
    have hComp : ι₂ ≫ π₂ = 𝟙 _ := by
      simpa only [ShortComplex.comp_τ₂, ShortComplex.id_τ₂, ι₂, π₂] using congrArg
        (fun k => (ShortComplex.π₂ : ShortComplex (ModuleCat.{0} ℤ) ⥤ ModuleCat.{0} ℤ).map k)
        (biprod.inr_snd : (biprod.inr : selfSumShortComplex (ModuleCat.of ℤ (ZMod 2)) ⟶
          universallyExactNonsplitNonflatShortComplex) ≫
            (biprod.snd : universallyExactNonsplitNonflatShortComplex ⟶
              selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))) = 𝟙 _)
    ext x
    simpa using congrArg
      (fun f : (selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))).X₂ ⟶
        (selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))).X₂ => f.hom x) hComp
  -- Retract the middle term onto the middle term of the `ZMod 2` self-sum sequence.
  have hRetract :
      Module.Flat ℤ (selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))).X₂ :=
    Module.Flat.of_retract ι₂.hom π₂.hom hRetractEq
  exact
    selfSumShortComplex_not_flat_X₂ (ModuleCat.of ℤ (ZMod 2))
      (by simpa using zmodTwo_not_flat) hRetract

/-- Example 10.82.6 (3): the right term of the constructed direct-sum short complex is non-flat. -/
theorem universallyExactNonsplitNonflatShortComplex_not_flat_X₃ :
    ¬ Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₃ := by
  intro hFlat
  let _ : Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₃ := hFlat
  let ι₃ : ModuleCat.of ℤ (ZMod 2) ⟶ universallyExactNonsplitNonflatShortComplex.X₃ :=
    (biprod.inr : selfSumShortComplex (ModuleCat.of ℤ (ZMod 2)) ⟶
      universallyExactNonsplitNonflatShortComplex).τ₃
  let π₃ : universallyExactNonsplitNonflatShortComplex.X₃ ⟶ ModuleCat.of ℤ (ZMod 2) :=
    (biprod.snd : universallyExactNonsplitNonflatShortComplex ⟶
      selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))).τ₃
  have hRetractEq : π₃.hom.comp ι₃.hom = LinearMap.id := by
    have hComp : ι₃ ≫ π₃ = 𝟙 _ := by
      simpa only [ShortComplex.comp_τ₃, ShortComplex.id_τ₃, ι₃, π₃] using congrArg
        (fun k => (ShortComplex.π₃ : ShortComplex (ModuleCat.{0} ℤ) ⥤ ModuleCat.{0} ℤ).map k)
        (biprod.inr_snd : (biprod.inr : selfSumShortComplex (ModuleCat.of ℤ (ZMod 2)) ⟶
          universallyExactNonsplitNonflatShortComplex) ≫
            (biprod.snd : universallyExactNonsplitNonflatShortComplex ⟶
              selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))) = 𝟙 _)
    ext x
    simpa using congrArg (fun f : ModuleCat.of ℤ (ZMod 2) ⟶ ModuleCat.of ℤ (ZMod 2) => f.hom x)
      hComp
  -- Retract the right term onto the `ZMod 2` summand of the split row.
  have hRetract :
      Module.Flat ℤ (ModuleCat.of ℤ (ZMod 2)) :=
    Module.Flat.of_retract ι₃.hom π₃.hom hRetractEq
  exact zmodTwo_not_flat (by simpa using hRetract)

/-- Example 10.82.6 (3): there exists a universally exact non-split short exact sequence of
`\mathbf Z`-modules whose three terms are all non-flat. -/
theorem exists_universally_exact_nonsplit_nonflat_sequence :
    ∃ S : ShortComplex (ModuleCat.{0} ℤ),
      S.UniversallyExact ∧ ¬ Nonempty S.Splitting ∧
        ¬ Module.Flat ℤ S.X₁ ∧ ¬ Module.Flat ℤ S.X₂ ∧ ¬ Module.Flat ℤ S.X₃ := by
  refine ⟨universallyExactNonsplitNonflatShortComplex, ?_⟩
  exact ⟨universallyExactNonsplitNonflatShortComplex_universallyExact,
    universallyExactNonsplitNonflatShortComplex_not_split,
    universallyExactNonsplitNonflatShortComplex_not_flat_X₁,
    universallyExactNonsplitNonflatShortComplex_not_flat_X₂,
    universallyExactNonsplitNonflatShortComplex_not_flat_X₃⟩

/-! ### Lemma_10_82_7 (from Chap10) -/
universe u v

open CategoryTheory
open CategoryTheory.ShortComplex
open LinearMap

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{max u v} R)}

/-- Helper for Lemma 10.82.7: universal exactness makes every right tensor map by `S.f`
injective. -/
lemma rTensor_f_injective_of_universallyExact (hS : UniversallyExact S)
    (Q : Type (max u v)) [AddCommGroup Q] [Module R Q] :
    Function.Injective (S.f.hom.rTensor Q) := by
  -- This is exactly the universal injectivity built into `UniversallyExact`.
  exact hS.universallyInjective_f Q inferInstance inferInstance

/-- Helper for Lemma 10.82.7: if the middle term of a universally exact short complex is flat, then
the left term is flat. -/
lemma flat_left_term_of_universallyExact [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₁ := by
  -- Use the left-tensor flatness criterion so the source square matches the universally exact rows.
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ i hi
  have hNInj : Function.Injective (S.f.hom.rTensor N) :=
    rTensor_f_injective_of_universallyExact hS N
  have hMidInj : Function.Injective (i.lTensor S.X₂) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  -- Apply `S.f ⊗ P` to the proposed equality, then use injectivity in the middle and on the left.
  intro x y hxy
  have hxComm :
      (i.lTensor S.X₂) ((S.f.hom.rTensor N) x) =
        (S.f.hom.rTensor P) ((i.lTensor S.X₁) x) := by
    calc
      (i.lTensor S.X₂) ((S.f.hom.rTensor N) x)
          = TensorProduct.map S.f.hom i x := by
              simpa only [LinearMap.comp_apply] using
                DFunLike.congr_fun
                  (LinearMap.lTensor_comp_rTensor (f := S.f.hom) (g := i)) x
      _ = (S.f.hom.rTensor P) ((i.lTensor S.X₁) x) := by
            simpa only [LinearMap.comp_apply] using
              (DFunLike.congr_fun
                (LinearMap.rTensor_comp_lTensor (f := S.f.hom) (g := i)) x).symm
  have hyComm :
      (i.lTensor S.X₂) ((S.f.hom.rTensor N) y) =
        (S.f.hom.rTensor P) ((i.lTensor S.X₁) y) := by
    calc
      (i.lTensor S.X₂) ((S.f.hom.rTensor N) y)
          = TensorProduct.map S.f.hom i y := by
              simpa only [LinearMap.comp_apply] using
                DFunLike.congr_fun
                  (LinearMap.lTensor_comp_rTensor (f := S.f.hom) (g := i)) y
      _ = (S.f.hom.rTensor P) ((i.lTensor S.X₁) y) := by
            simpa only [LinearMap.comp_apply] using
              (DFunLike.congr_fun
                (LinearMap.rTensor_comp_lTensor (f := S.f.hom) (g := i)) y).symm
  exact hNInj <| hMidInj <| by
    calc
      (i.lTensor S.X₂) ((S.f.hom.rTensor N) x)
          = (S.f.hom.rTensor P) ((i.lTensor S.X₁) x) := hxComm
      _ = (S.f.hom.rTensor P) ((i.lTensor S.X₁) y) := by
            rw [hxy]
      _ = (i.lTensor S.X₂) ((S.f.hom.rTensor N) y) := by
            exact hyComm.symm

/-- Helper for Lemma 10.82.7: if the middle term of a universally exact short complex is flat, then
the right term is flat. -/
lemma flat_right_term_of_universallyExact [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₃ := by
  -- Use the tensor-left flatness criterion and chase the quotient diagram attached to an injective
  -- map `i : N → P`, exactly as in the textbook proof.
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ i hi
  let Q : Type (max u v) := P ⧸ LinearMap.range i
  let π : P →ₗ[R] Q := Submodule.mkQ (LinearMap.range i)
  have hExactCol : Function.Exact i π := LinearMap.exact_map_mkQ_range i
  have hSurjCol : Function.Surjective π := Submodule.mkQ_surjective _
  have hExactRow : Function.Exact S.f.hom S.g.hom := by
    simpa using (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.shortExact.exact
  have hSurjRow : Function.Surjective S.g.hom := hS.shortExact.moduleCat_surjective_g
  have hRightInj : Function.Injective (S.f.hom.rTensor Q) :=
    rTensor_f_injective_of_universallyExact hS Q
  have hMiddleInj : Function.Injective (i.lTensor S.X₂) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  -- The standard three-row diagram chase upgrades injectivity from `X₂` to `X₃`.
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    hExactRow hSurjRow hExactCol hSurjCol hRightInj hMiddleInj

-- Proof sketch: apply the owner abstraction `UniversallyExact S`. Its short exactness gives the
-- exact sequence, and its universal injectivity for `S.f` supplies the tensor-injectivity input.
-- Then use the tensor criterion for flatness together with exactness preservation for the flat
-- middle term `S.X₂` to deduce flatness of `S.X₁` and `S.X₃`.
/-- Lemma 10.82.7: if `S : ShortComplex (ModuleCat R)` is universally exact and the middle module
`S.X₂` is flat, then the first and third modules are flat. -/
theorem flat_X₁_and_X₃_of_universallyExact [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₁ ∧ Module.Flat R S.X₃ := by
  -- First recover flatness of the left term from the universally injective tensor square.
  have hFlatX₁ : Module.Flat R S.X₁ := flat_left_term_of_universallyExact hS
  -- Then tensor the quotient diagram of an injective map and chase exactness to reach the right.
  have hFlatX₃ : Module.Flat R S.X₃ := flat_right_term_of_universallyExact hS
  exact ⟨hFlatX₁, hFlatX₃⟩

/-- In a universally exact short complex of `R`-modules, flatness of the middle term implies
flatness of the first term. -/
theorem UniversallyExact.flat_X₁ [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₁ :=
  (flat_X₁_and_X₃_of_universallyExact hS).1

/-- In a universally exact short complex of `R`-modules, flatness of the middle term implies
flatness of the third term. -/
theorem UniversallyExact.flat_X₃ [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₃ :=
  (flat_X₁_and_X₃_of_universallyExact hS).2

end

/-! ### Lemma_10_82_8 (from Chap10) -/
open scoped TensorProduct

universe u v w x y

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} {M' : Type w} {N : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M']
variable [AddCommGroup N] [Module R N]
variable {f : M →ₗ[R] M'}

-- Proof sketch: for any `R`-module `Q`, use the tensor associativity isomorphism to identify
-- `((M ⊗[R] N) ⊗[R] Q)` with `M ⊗[R] (N ⊗[R] Q)` and similarly on the target. Under these
-- identifications, `(f.rTensor N).rTensor Q` is the tensor of `f` with `N ⊗[R] Q`, so its
-- injectivity follows from the universal injectivity of `f`.
/-- Helper for Lemma 10.82.8: the tensor associator identifies the iterated right tensor map
with tensoring `f` once by `N ⊗[R] Q`. -/
lemma rtensor_assoc_apply {Q : Type y} [AddCommGroup Q] [Module R Q]
    (x : (M ⊗[R] N) ⊗[R] Q) :
    TensorProduct.assoc R M' N Q (((f.rTensor N).rTensor Q) x) =
      (f.rTensor (N ⊗[R] Q)) (TensorProduct.assoc R M N Q x) := by
  let lhs : (M ⊗[R] N) ⊗[R] Q →ₗ[R] M' ⊗[R] (N ⊗[R] Q) :=
    (TensorProduct.assoc R M' N Q).toLinearMap.comp ((f.rTensor N).rTensor Q)
  let rhs : (M ⊗[R] N) ⊗[R] Q →ₗ[R] M' ⊗[R] (N ⊗[R] Q) :=
    (f.rTensor (N ⊗[R] Q)).comp (TensorProduct.assoc R M N Q).toLinearMap
  -- Check equality of the comparison maps on pure tensors in the outer and inner tensor factors.
  have hmaps : lhs = rhs := by
    refine TensorProduct.ext_threefold ?_
    intro m n q
    rfl
  -- Evaluate the linear-map equality at `x` to obtain the desired pointwise comparison.
  have hpoint :
      lhs x = rhs x := by
    exact congrArg
      (fun φ : (M ⊗[R] N) ⊗[R] Q →ₗ[R] M' ⊗[R] (N ⊗[R] Q) => φ x) hmaps
  simpa [lhs, rhs] using hpoint

/-- Helper for Lemma 10.82.8: after one more right tensor by a test module `Q`, the iterated
tensor map stays injective. -/
lemma injective_rtensor_rtensor_of_universallyInjective
    (hf : UniversallyInjective.{u, v, w, max x y} f) {Q : Type y}
    [AddCommGroup Q] [Module R Q] :
    Function.Injective (((f.rTensor N).rTensor Q)) := by
  intro x y hxy
  -- Transport the equality through the target associator to compare it with `f.rTensor (N ⊗[R] Q)`.
  have hxy_assoc :
      TensorProduct.assoc R M' N Q (((f.rTensor N).rTensor Q) x) =
        TensorProduct.assoc R M' N Q (((f.rTensor N).rTensor Q) y) := by
    exact congrArg (TensorProduct.assoc R M' N Q) hxy
  have hxy' :
      (f.rTensor (N ⊗[R] Q)) (TensorProduct.assoc R M N Q x) =
        (f.rTensor (N ⊗[R] Q)) (TensorProduct.assoc R M N Q y) := by
    rw [← rtensor_assoc_apply (f := f) (N := N) (x := x)]
    rw [← rtensor_assoc_apply (f := f) (N := N) (x := y)]
    exact hxy_assoc
  -- Apply universal injectivity to `N ⊗[R] Q` and pull the conclusion back through the source associator.
  have hTensorInjective : Function.Injective (f.rTensor (N ⊗[R] Q)) :=
    hf (N ⊗[R] Q) inferInstance inferInstance
  have hAssocEq : TensorProduct.assoc R M N Q x = TensorProduct.assoc R M N Q y :=
    hTensorInjective hxy'
  exact (TensorProduct.assoc R M N Q).injective <|
    hAssocEq

/-- Lemma 10.82.8: tensoring a universally injective `R`-linear map on the right with any
`R`-module again yields a universally injective map. -/
theorem universallyInjective_rTensor (hf : UniversallyInjective.{u, v, w, max x y} f) :
    UniversallyInjective.{u, max v x, max w x, y} (f.rTensor N) := by
  intro Q _ _
  -- Universal injectivity is tested after one more tensor factor, and the fixed-`Q` injectivity
  -- follows from the associator comparison proved above.
  exact injective_rtensor_rtensor_of_universallyInjective (f := f) (N := N) hf

end

end LinearMap

/-! ### Lemma_10_82_9 (from Chap10) -/
universe u v w x

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w} {P : Type x}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

-- Proof sketch: for any `R`-module `Q`, tensoring commutes with composition, so
-- `(g.comp f).rTensor Q = (g.rTensor Q).comp (f.rTensor Q)`. The composition of the
-- injective tensor maps supplied by `hf` and `hg` is injective.
/-- Lemma 10.82.9: a composition of universally injective `R`-module maps is universally
injective. -/
theorem universallyInjective_comp {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hg : UniversallyInjective.{u, w, x, max v w x} g)
    (hf : UniversallyInjective.{u, v, w, max v w x} f) :
    UniversallyInjective.{u, v, x, max v w x} (g.comp f) := by
  intro Q _ _
  simpa [LinearMap.rTensor_comp] using
    Function.Injective.comp (hg Q (inferInstance) (inferInstance))
      (hf Q (inferInstance) (inferInstance))

end

end LinearMap

/-! ### Lemma_10_82_10 (from Chap10) -/
universe u v w

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} {M' : Type w} {M'' : Type w}
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M'] [Module R M']
variable [AddCommGroup M''] [Module R M'']

-- Proof sketch: tensoring commutes with composition, so for every `R`-module `Q` the map
-- `(g.comp f).rTensor Q` factors as `(g.rTensor Q).comp (f.rTensor Q)`. If the composition is
-- injective, then `f.rTensor Q` is injective; hence `f` is universally injective.
/-- Lemma 10.82.10: if the composition `M → M''` of two `R`-linear maps `M → M'` and
`M' → M''` is universally injective, then the first map `M → M'` is universally injective. -/
theorem universallyInjective_of_comp {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hgf : UniversallyInjective.{u, v, w, w} (g.comp f)) : UniversallyInjective.{u, v, w, w} f := by
  intro Q _ _
  have hcomp : Function.Injective ((g.rTensor Q).comp (f.rTensor Q)) := by
    simpa [LinearMap.rTensor_comp] using hgf Q inferInstance inferInstance
  intro x y hxy
  apply hcomp
  exact congrArg (g.rTensor Q) hxy

end

end LinearMap

/-! ### Lemma_10_82_11 (from Chap10) -/
open scoped TensorProduct
open LocalizedModule TensorProduct
open TensorProduct.AlgebraTensorModule

universe u v w x

namespace LinearMap

noncomputable section

open IsLocalization

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]
variable {M' : Type x} [AddCommGroup M'] [Module S M']
variable [Module R M] [Module R M'] [IsScalarTower R S M] [IsScalarTower R S M']

/-- Helper for Lemma 10.82.11: the localized tensor map of `f ⊗[R] Q` is exactly the tensor map
of the localized morphism `f_q`. -/
lemma localized_rTensor_intertwines_localized_map
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    IsLocalizedModule.map q.asIdeal.primeCompl
      (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))
      (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M'))
      (AlgebraTensorModule.rTensor R Q f) =
      AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f) := by
  -- We compare the two maps after precomposing with the canonical localization map on
  -- `M ⊗[R] Q`, where both sides reduce to the same map on pure tensors.
  apply IsLocalizedModule.linearMap_ext q.asIdeal.primeCompl
    (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))
    (AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M'))
  rw [IsLocalizedModule.map_comp, ← AlgebraTensorModule.rTensor_comp, AlgebraTensorModule.rTensor_comp]
  ext x
  simp [LocalizedModule.map_mk]

/-- Helper for Lemma 10.82.11: localizing `f ⊗[R] Q` at `q` is injective exactly when the tensor
map of `f_q` with `Q` is injective. -/
lemma localized_rTensor_injective_iff
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Function.Injective (LocalizedModule.map q.asIdeal.primeCompl (AlgebraTensorModule.rTensor R Q f)) ↔
      Function.Injective (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)) :=
by
  -- We transfer injectivity from the canonical localized-module model of `M ⊗[R] Q`
  -- to the tensor of the localized map by the explicit intertwining identity above.
  simpa [localized_rTensor_intertwines_localized_map (R := R) (S := S) (M := M) (M' := M')
      (f := f) (q := q) (Q := Q)] using
    (IsLocalizedModule.map_injective_iff_localizedModuleMap_injective
      (S := q.asIdeal.primeCompl)
      (g₁ := AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M))
      (g₂ := AlgebraTensorModule.rTensor R Q (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M'))
      (l := AlgebraTensorModule.rTensor R Q f)).symm

/-- Helper for Lemma 10.82.11: for an `R_(q ∩ R)`-module `Q`, tensoring `M_q` with `Q` over the
localized base ring agrees with tensoring over `R`. -/
noncomputable def localized_rTensor_over_under_equiv
    (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q]
    [Module (Localization.AtPrime (q.asIdeal.under R)) Q]
    [Module R Q] [IsScalarTower R (Localization.AtPrime (q.asIdeal.under R)) Q] :
    LocalizedModule.AtPrime q.asIdeal M ⊗[Localization.AtPrime (q.asIdeal.under R)] Q
      ≃ₗ[Localization.AtPrime q.asIdeal]
      LocalizedModule.AtPrime q.asIdeal M ⊗[R] Q := sorry

/-- Helper for Lemma 10.82.11: the over-under tensor equivalence intertwines the tensor maps of
the localized morphism `f_q`. -/
lemma localized_rTensor_over_under_intertwines
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q]
    [Module (Localization.AtPrime (q.asIdeal.under R)) Q]
    [Module R Q] [IsScalarTower R (Localization.AtPrime (q.asIdeal.under R)) Q] :
    (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)).comp
        (localized_rTensor_over_under_equiv (R := R) (S := S) (M := M) (q := q) Q).toLinearMap =
      (localized_rTensor_over_under_equiv (R := R) (S := S) (M := M') (q := q) Q).toLinearMap.comp
        (AlgebraTensorModule.rTensor (Localization.AtPrime (q.asIdeal.under R)) Q
          (LocalizedModule.map q.asIdeal.primeCompl f)) := by
  -- TODO: express the source proof identity `M_q ⊗[R] Q = M_q ⊗[R_(q ∩ R)] Q`
  -- through a transport-stable `A_q`-linear equivalence, then rewrite both composites on
  -- pure tensors using the canonical comparison map.
  sorry

/-- Helper for Lemma 10.82.11: if `Q` is already an `R_(q ∩ R)`-module, then injectivity of the
tensor map of `f_q` is the same over `R` and over `R_(q ∩ R)`. -/
lemma localized_rTensor_injective_iff_over_under
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q]
    [Module (Localization.AtPrime (q.asIdeal.under R)) Q]
    [Module R Q] [IsScalarTower R (Localization.AtPrime (q.asIdeal.under R)) Q] :
    Function.Injective (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)) ↔
      Function.Injective
        (AlgebraTensorModule.rTensor (Localization.AtPrime (q.asIdeal.under R)) Q
          (LocalizedModule.map q.asIdeal.primeCompl f)) := by
  -- TODO: once `localized_rTensor_over_under_intertwines` is proved via the canonical over/under
  -- equivalence, transfer injectivity across that equivalence in both directions.
  sorry

/-- Helper for Lemma 10.82.11: after localizing the test module `Q` at `q ∩ R`, tensoring `M_q`
over `R_(q ∩ R)` identifies canonically with tensoring over `R`. -/
noncomputable def localized_rTensor_over_under_localizedModule_equiv
    (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    LocalizedModule.AtPrime q.asIdeal M ⊗[Localization.AtPrime (q.asIdeal.under R)]
        LocalizedModule.AtPrime (q.asIdeal.under R) Q
      ≃ₗ[Localization.AtPrime q.asIdeal]
      LocalizedModule.AtPrime q.asIdeal M ⊗[R] Q := sorry

/-- Helper for Lemma 10.82.11: the localized-module version of the over-under tensor equivalence
also intertwines the tensor maps of `f_q`. -/
lemma localized_rTensor_over_under_localizedModule_intertwines
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)).comp
        (localized_rTensor_over_under_localizedModule_equiv
          (R := R) (S := S) (M := M) (q := q) Q).toLinearMap =
      (localized_rTensor_over_under_localizedModule_equiv
          (R := R) (S := S) (M := M') (q := q) Q).toLinearMap.comp
        (AlgebraTensorModule.rTensor (Localization.AtPrime (q.asIdeal.under R))
          (LocalizedModule.AtPrime (q.asIdeal.under R) Q)
          (LocalizedModule.map q.asIdeal.primeCompl f)) := by
  -- TODO: factor the comparison through `LocalizedModule.equivTensorProduct` on the test module
  -- and `AlgebraTensorModule.cancelBaseChange`, then verify the two composites on generators.
  sorry

/-- Helper for Lemma 10.82.11: for an `R`-module `Q`, injectivity of the tensor map of `f_q`
against `Q` is equivalent to injectivity of the over-under tensor map against `Q_(q ∩ R)`. -/
lemma localized_rTensor_injective_iff_over_under_localizedModule
    (f : M →ₗ[S] M') (q : PrimeSpectrum S) (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Function.Injective (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)) ↔
      Function.Injective
        (AlgebraTensorModule.rTensor (Localization.AtPrime (q.asIdeal.under R))
          (LocalizedModule.AtPrime (q.asIdeal.under R) Q)
          (LocalizedModule.map q.asIdeal.primeCompl f)) := by
  -- TODO: transfer injectivity across `localized_rTensor_over_under_localizedModule_equiv`
  -- after the corresponding intertwining lemma is established.
  sorry

-- Proof sketch: localize the tensor map `M ⊗[R] Q → M' ⊗[R] Q` at primes or maximal ideals of
-- `S`, identify these localizations with the tensor maps of the localized morphisms, and then use
-- exactness of localization together with the local criterion that a module is zero iff all of its
-- maximal localizations are zero.
/-- Lemma 10.82.11: for an `R`-algebra `S` and an `S`-linear map `M → M'`, universal injectivity
over `R` is equivalent to universal injectivity after localizing at every prime or maximal ideal of
`S`, either as a map of `R`-modules or as a map over the local rings `R_(q ∩ R)` and `R_(m ∩ R)`.
-/
theorem universallyInjective_localizedModule_atPrime_over_under_tfae (f : M →ₗ[S] M') :
    letI : Module R M := Module.restrictScalars R S M
    letI : Module R M' := Module.restrictScalars R S M'
    letI : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
    letI : IsScalarTower R S M' := IsScalarTower.restrictScalars R S M'
    List.TFAE [
      UniversallyInjective.{u, w, x, max u v w x} (f.restrictScalars R),
      ∀ q : PrimeSpectrum S,
        UniversallyInjective.{u, max v w, max v x, max u v w x}
          ((LocalizedModule.map q.asIdeal.primeCompl f).restrictScalars R),
      ∀ m : MaximalSpectrum S,
        UniversallyInjective.{u, max v w, max v x, max u v w x}
          ((LocalizedModule.map m.asIdeal.primeCompl f).restrictScalars R),
      ∀ q : PrimeSpectrum S,
        UniversallyInjective.{u, max v w, max v x, max u v w x}
          ((LocalizedModule.map q.asIdeal.primeCompl f).restrictScalars
            (Localization.AtPrime (q.asIdeal.under R))),
      ∀ m : MaximalSpectrum S,
        UniversallyInjective.{u, max v w, max v x, max u v w x}
          ((LocalizedModule.map m.asIdeal.primeCompl f).restrictScalars
            (Localization.AtPrime (m.asIdeal.under R)))
    ] := by
  classical
  letI : Module R M := Module.restrictScalars R S M
  letI : Module R M' := Module.restrictScalars R S M'
  letI : IsScalarTower R S M := IsScalarTower.restrictScalars R S M
  letI : IsScalarTower R S M' := IsScalarTower.restrictScalars R S M'
  -- We use the tensor map `f ⊗[R] Q` as the main controlled object.
  tfae_have 1 → 2 := by
    intro hf q
    unfold UniversallyInjective at hf ⊢
    intro Q _ _
    -- We first tensor the global map with `Q`, then localize the resulting injective map at `q`.
    have hTensor : Function.Injective (AlgebraTensorModule.rTensor R Q f) := by
      simpa [restrictScalars_rTensor] using hf Q inferInstance inferInstance
    have hLocalized :
        Function.Injective (LocalizedModule.map q.asIdeal.primeCompl
          (AlgebraTensorModule.rTensor R Q f)) :=
      LocalizedModule.map_injective q.asIdeal.primeCompl (AlgebraTensorModule.rTensor R Q f) hTensor
    -- The localized tensor map is the same as tensoring the localized morphism.
    simpa [restrictScalars_rTensor] using
      (localized_rTensor_injective_iff (R := R) (S := S) (M := M) (M' := M')
        (f := f) (q := q) (Q := Q)).1 hLocalized
  tfae_have 2 → 3 := by
    intro h m
    -- Maximal ideals are special cases of prime ideals.
    simpa using h m.toPrimeSpectrum
  tfae_have 3 → 1 := by
    intro h
    unfold UniversallyInjective at h ⊢
    intro Q _ _
    -- We test injectivity of `f ⊗[R] Q` at every maximal ideal of `S`.
    have hLocal :
        ∀ (J : Ideal S) [J.IsMaximal],
          Function.Injective (LocalizedModule.map J.primeCompl (AlgebraTensorModule.rTensor R Q f)) := by
      intro J _
      let m : MaximalSpectrum S := ⟨J, inferInstance⟩
      have hm : UniversallyInjective ((LocalizedModule.map J.primeCompl f).restrictScalars R) := by
        simpa using h m
      have hmTensor :
          Function.Injective (AlgebraTensorModule.rTensor R Q (LocalizedModule.map J.primeCompl f)) := by
        simpa [restrictScalars_rTensor] using hm Q inferInstance inferInstance
      -- The maximal localization of `f ⊗[R] Q` is the tensor map of `f_m`.
      simpa using
        (localized_rTensor_injective_iff (R := R) (S := S) (M := M) (M' := M')
          (f := f) (q := m.toPrimeSpectrum) (Q := Q)).2 hmTensor
    simpa [restrictScalars_rTensor] using
      (injective_of_localized_maximal (f := AlgebraTensorModule.rTensor R Q f) hLocal)
  tfae_have 1 → 4 := by
    intro hf q
    unfold UniversallyInjective at hf ⊢
    intro Q _ _
    letI : Module R Q := Module.restrictScalars R (Localization.AtPrime (q.asIdeal.under R)) Q
    letI : IsScalarTower R (Localization.AtPrime (q.asIdeal.under R)) Q :=
      IsScalarTower.restrictScalars R (Localization.AtPrime (q.asIdeal.under R)) Q
    -- First tensor the global map with `Q` viewed as an `R`-module, then localize at `q`.
    have hTensor : Function.Injective (AlgebraTensorModule.rTensor R Q f) := by
      simpa [restrictScalars_rTensor] using hf Q inferInstance inferInstance
    have hLocalized :
        Function.Injective (LocalizedModule.map q.asIdeal.primeCompl
          (AlgebraTensorModule.rTensor R Q f)) :=
      LocalizedModule.map_injective q.asIdeal.primeCompl
        (AlgebraTensorModule.rTensor R Q f) hTensor
    have hTensorLocalized :
        Function.Injective
          (AlgebraTensorModule.rTensor R Q (LocalizedModule.map q.asIdeal.primeCompl f)) := by
      exact (localized_rTensor_injective_iff (R := R) (S := S) (M := M) (M' := M')
        (f := f) (q := q) (Q := Q)).1 hLocalized
    -- The source identity `M_q ⊗[R] Q = M_q ⊗[R_(q ∩ R)] Q` is the remaining bridge.
    simpa [restrictScalars_rTensor] using
      (localized_rTensor_injective_iff_over_under (R := R) (S := S) (M := M) (M' := M')
        (f := f) (q := q) (Q := Q)).1 hTensorLocalized
  tfae_have 4 → 5 := by
    intro h m
    -- Maximal ideals are special cases of prime ideals on the over-under side as well.
    simpa using h m.toPrimeSpectrum
  tfae_have 5 → 1 := by
    -- Route correction: test the maximal-local hypothesis on `Q_(m ∩ R)` and then transport back
    -- via `localized_rTensor_injective_iff_over_under_localizedModule`.
    intro h
    unfold UniversallyInjective at h ⊢
    intro Q _ _
    -- It is enough to test the tensor map after localizing at every maximal ideal of `S`.
    have hLocal :
        ∀ (J : Ideal S) [J.IsMaximal],
          Function.Injective (LocalizedModule.map J.primeCompl (AlgebraTensorModule.rTensor R Q f)) := by
      intro J _
      let m : MaximalSpectrum S := ⟨J, inferInstance⟩
      have hm :
          UniversallyInjective
            ((LocalizedModule.map J.primeCompl f).restrictScalars
              (Localization.AtPrime (J.under R))) := by
        simpa using h m
      have hmTensor :
          Function.Injective
            (AlgebraTensorModule.rTensor (Localization.AtPrime (J.under R))
              (LocalizedModule.AtPrime (J.under R) Q)
              (LocalizedModule.map J.primeCompl f)) := by
        simpa [restrictScalars_rTensor] using
          hm (LocalizedModule.AtPrime (J.under R) Q) inferInstance inferInstance
      have hmTensorR :
          Function.Injective
            (AlgebraTensorModule.rTensor R Q (LocalizedModule.map J.primeCompl f)) := by
        exact
          (localized_rTensor_injective_iff_over_under_localizedModule
            (R := R) (S := S) (M := M) (M' := M')
            (f := f) (q := m.toPrimeSpectrum) (Q := Q)).2 hmTensor
      -- The maximal localization of `f ⊗[R] Q` is again the tensor map of `f_m`.
      simpa using
        (localized_rTensor_injective_iff (R := R) (S := S) (M := M) (M' := M')
          (f := f) (q := m.toPrimeSpectrum) (Q := Q)).2 hmTensorR
    simpa [restrictScalars_rTensor] using
      (injective_of_localized_maximal (f := AlgebraTensorModule.rTensor R Q f) hLocal)
  tfae_finish

end

end

end LinearMap
