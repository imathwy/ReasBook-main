import Mathlib
import stacks_project.Chap10.Definition_10_82_1

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

/-- Flatness of the product `\prod_{n \ge 1} \mathbf Z`. -/
-- Proof sketch: over `ℤ`, torsion-free modules are flat; the product of copies of `ℤ` is
-- torsion-free because scalar multiplication is coordinatewise.
theorem integerProduct_flat : Module.Flat ℤ (ℕ → ℤ) := sorry

/-- Flatness of the quotient `(\prod \mathbf Z)/(\bigoplus \mathbf Z)`. -/
-- Proof sketch: over `ℤ`, it suffices to show the quotient is torsion-free and then apply the
-- torsion-free criterion for flatness of modules over a PID.
theorem integerProductQuotient_flat : Module.Flat ℤ integerDirectSumProductShortComplex.X₃ := sorry

/-- Example 10.82.6 (1): the sequence
`0 → \bigoplus \mathbf Z → \prod \mathbf Z → (\prod \mathbf Z)/(\bigoplus \mathbf Z) → 0`
is universally exact. -/
-- Proof sketch: combine short exactness of the quotient sequence with flatness of the quotient
-- term, then apply the flat-cokernel owner theorem
-- `ShortComplex.ShortExact.universallyExact_of_flat_X₃`.
theorem integer_direct_sum_product_sequence_universally_exact :
    integerDirectSumProductShortComplex.UniversallyExact :=
  sorry

/-- Companion to Example 10.82.6 (1): every `\mathbf Z`-linear map from
`(\prod \mathbf Z)/(\bigoplus \mathbf Z)` to `\prod \mathbf Z` kills the class of
`(2,2^2,2^3,\ldots)`. -/
-- Proof sketch: the quotient class lies in `2^n M_3` for every `n`, so its image under any
-- linear map is a vector in `\prod \mathbf Z` divisible by every `2^n`, hence zero
-- coordinatewise.
theorem integer_direct_sum_product_hom_kills_witness
    (φ : integerDirectSumProductShortComplex.X₃ →ₗ[ℤ] (ℕ → ℤ)) :
    φ integerDivisibilityWitnessClass = 0 := sorry

/-- Companion to Example 10.82.6 (1): the quotient map admits no section. -/
-- Proof sketch: if `s` were a section, the previous theorem would give
-- `s integerDivisibilityWitnessClass = 0`; applying the quotient map and using the section identity
-- would force the distinguished class itself to vanish, contradiction.
theorem integer_direct_sum_product_quotientMap_has_no_section :
    ¬ ∃ s : integerDirectSumProductShortComplex.X₃ →ₗ[ℤ] (ℕ → ℤ),
      integerProductModuloDirectSum.comp s = LinearMap.id := sorry

/-- Companion to Example 10.82.6 (1): the quotient sequence does not split. -/
-- Proof sketch: a splitting datum of the canonical quotient short complex provides a
-- section `σ.s` of the quotient map, contradicting
-- `integer_direct_sum_product_quotientMap_has_no_section`.
theorem integer_direct_sum_product_sequence_not_split :
    ¬ Nonempty integerDirectSumProductShortComplex.Splitting := sorry

/-- The split short complex `0 → M → M \oplus M → M → 0` from Example 10.82.6 (2). -/
def selfSumShortComplex {R : Type u} [CommRing R] (M : ModuleCat R) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (biprod.inl : M ⟶ M ⊞ M)
    (biprod.snd : M ⊞ M ⟶ M)
    (by simp)

/-- Example 10.82.6 (2): the split self-sum sequence is universally exact. -/
-- Proof sketch: apply `ShortComplex.Splitting.ofHasBinaryBiproduct` to the canonical binary
-- biproduct sequence `0 → M → M ⊞ M → M → 0`, then use that splittings are universally exact.
theorem selfSumShortComplex_universallyExact
    {R : Type u} [CommRing R] (M : ModuleCat R) :
    (selfSumShortComplex M).UniversallyExact := sorry

/-- In Example 10.82.6 (2), the left term of the self-sum sequence is non-flat when `M` is. -/
theorem selfSumShortComplex_not_flat_X₁
    {R : Type u} [CommRing R] (M : ModuleCat R) (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R (selfSumShortComplex M).X₁ := sorry

/-- In Example 10.82.6 (2), the middle term of the self-sum sequence is non-flat when `M` is. -/
-- Proof sketch: if `M ⊞ M` were flat, then universal exactness of the split sequence would imply
-- flatness of `X₁ = M` by `ShortComplex.UniversallyExact.flat_X₁`, contradicting `hM`.
theorem selfSumShortComplex_not_flat_X₂
    {R : Type u} [CommRing R] (M : ModuleCat R) (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R (selfSumShortComplex M).X₂ := sorry

/-- In Example 10.82.6 (2), the right term of the self-sum sequence is non-flat when `M` is. -/
theorem selfSumShortComplex_not_flat_X₃
    {R : Type u} [CommRing R] (M : ModuleCat R) (hM : ¬ Module.Flat R M) :
    ¬ Module.Flat R (selfSumShortComplex M).X₃ := sorry

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
    universallyExactNonsplitNonflatShortComplex.UniversallyExact := sorry

/-- Example 10.82.6 (3): the direct-sum short complex constructed above does not split. -/
-- Proof sketch: a splitting of the direct sum would restrict along the canonical inclusion of the
-- first summand and project back to a splitting of
-- `integerDirectSumProductShortComplex`, contradicting
-- `integer_direct_sum_product_sequence_not_split`.
theorem universallyExactNonsplitNonflatShortComplex_not_split :
    ¬ Nonempty universallyExactNonsplitNonflatShortComplex.Splitting := sorry

/-- Example 10.82.6 (3): the left term of the constructed direct-sum short complex is non-flat. -/
-- Proof sketch: the `ZMod 2` summand is a retract of `X₁`, so flatness of `X₁` would imply
-- flatness of `ZMod 2`, contradiction.
theorem universallyExactNonsplitNonflatShortComplex_not_flat_X₁ :
    ¬ Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₁ := sorry

/-- Example 10.82.6 (3): the middle term of the constructed direct-sum short complex is non-flat. -/
theorem universallyExactNonsplitNonflatShortComplex_not_flat_X₂ :
    ¬ Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₂ := sorry

/-- Example 10.82.6 (3): the right term of the constructed direct-sum short complex is non-flat. -/
theorem universallyExactNonsplitNonflatShortComplex_not_flat_X₃ :
    ¬ Module.Flat ℤ universallyExactNonsplitNonflatShortComplex.X₃ := sorry

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
