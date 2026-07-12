import Mathlib
import StacksProject_2024.Chap10.Definition_10_82_1
import StacksProject_2024.Chap10.Example_10_82_2
import StacksProject_2024.Chap10.Example_10_12_12
import StacksProject_2024.Chap10.Lemma_10_39_12
import StacksProject_2024.Chap10.Lemma_10_82_7

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
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
@[stacks 058N]
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
@[stacks 058N]
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

/-- Helper for Chap10 Example 10 82 6: the explicit `ModuleCat` product comparison sends a
binary biproduct to the first product projection. -/
private lemma biprodIsoProd_hom_comp_fst {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.fst R M N) = biprod.fst := by
  -- Compare the canonical biproduct cone with the explicit product cone in its first component.
  simpa [ModuleCat.binaryProductLimitCone_cone_π_app_left] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (BinaryBiproduct.isLimit M N) (ModuleCat.binaryProductLimitCone M N).isLimit
      (Discrete.mk WalkingPair.left)

/-- Helper for Chap10 Example 10 82 6: the explicit `ModuleCat` product comparison sends a
binary biproduct to the second product projection. -/
private lemma biprodIsoProd_hom_comp_snd {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) :
    (ModuleCat.biprodIsoProd M N).hom ≫ ModuleCat.ofHom (LinearMap.snd R M N) = biprod.snd := by
  -- The same cone comparison gives the second component of the product model.
  simpa [ModuleCat.binaryProductLimitCone_cone_π_app_right] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (BinaryBiproduct.isLimit M N) (ModuleCat.binaryProductLimitCone M N).isLimit
      (Discrete.mk WalkingPair.right)

/-- Helper for Chap10 Example 10 82 6: under the explicit product model of a biproduct,
`biprod.map` becomes the product linear map. -/
private lemma biprod_map_comp_biprodIsoProd_hom {R : Type u} [CommRing R]
    {M₁ M₂ N₁ N₂ : ModuleCat.{u} R} (f : M₁ ⟶ N₁) (g : M₂ ⟶ N₂) :
    biprod.map f g ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom =
      (ModuleCat.biprodIsoProd M₁ M₂).hom ≫ ModuleCat.ofHom (f.hom.prodMap g.hom) := by
  -- Check the equality after applying the two ordinary product projections.
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · have hleft := congrArg (fun k : M₁ ⊞ M₂ ⟶ N₁ => k.hom x)
      (by
        calc
          biprod.map f g ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom ≫
              ModuleCat.ofHom (LinearMap.fst R N₁ N₂)
              = biprod.map f g ≫ biprod.fst := by
                  rw [biprodIsoProd_hom_comp_fst]
          _ = biprod.fst ≫ f := by
                  rw [biprod.map_fst])
    have hright := congrArg (fun k : M₁ ⊞ M₂ ⟶ M₁ => k.hom x)
      (biprodIsoProd_hom_comp_fst M₁ M₂)
    simpa [LinearMap.prodMap_apply] using hleft.trans (congrArg f.hom hright).symm
  · have hleft := congrArg (fun k : M₁ ⊞ M₂ ⟶ N₂ => k.hom x)
      (by
        calc
          biprod.map f g ≫ (ModuleCat.biprodIsoProd N₁ N₂).hom ≫
              ModuleCat.ofHom (LinearMap.snd R N₁ N₂)
              = biprod.map f g ≫ biprod.snd := by
                  rw [biprodIsoProd_hom_comp_snd]
          _ = biprod.snd ≫ g := by
                  rw [biprod.map_snd])
    have hright := congrArg (fun k : M₁ ⊞ M₂ ⟶ M₂ => k.hom x)
      (biprodIsoProd_hom_comp_snd M₁ M₂)
    simpa [LinearMap.prodMap_apply] using hleft.trans (congrArg g.hom hright).symm

/-- Helper for Chap10 Example 10 82 6: exactness is preserved by taking the product of two
exact rows of linear maps. -/
private lemma functionExact_prodMap {R : Type u} [CommRing R]
    {M₁ M₂ M₃ N₁ N₂ N₃ : Type u}
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    [Module R N₁] [Module R N₂] [Module R N₃]
    (f₁ : M₁ →ₗ[R] M₂) (g₁ : M₂ →ₗ[R] M₃)
    (f₂ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃)
    (hf : Function.Exact f₁ g₁) (hg : Function.Exact f₂ g₂) :
    Function.Exact (f₁.prodMap f₂) (g₁.prodMap g₂) := by
  intro x
  constructor
  · intro hx
    -- Exactness of each component supplies a preimage in the product source.
    have hx₁ : g₁ x.1 = 0 := by
      simpa [LinearMap.prodMap_apply] using congrArg Prod.fst hx
    have hx₂ : g₂ x.2 = 0 := by
      simpa [LinearMap.prodMap_apply] using congrArg Prod.snd hx
    obtain ⟨y₁, hy₁⟩ := (hf x.1).1 hx₁
    obtain ⟨y₂, hy₂⟩ := (hg x.2).1 hx₂
    refine ⟨(y₁, y₂), ?_⟩
    ext
    · simp [LinearMap.prodMap_apply, hy₁]
    · simp [LinearMap.prodMap_apply, hy₂]
  · rintro ⟨y, rfl⟩
    -- The reverse implication is just the two componentwise zero-composition statements.
    have hf_zero : g₁.comp f₁ = 0 := hf.linearMap_comp_eq_zero
    have hg_zero : g₂.comp f₂ = 0 := hg.linearMap_comp_eq_zero
    ext
    · simpa [LinearMap.comp_apply] using LinearMap.congr_fun hf_zero y.1
    · simpa [LinearMap.comp_apply] using LinearMap.congr_fun hg_zero y.2

/-- Helper for Chap10 Example 10 82 6: exact module rows remain exact after applying
`biprod.map` to the two rows. -/
private lemma functionExact_biprodMap {R : Type u} [CommRing R]
    {A₁ A₂ A₃ B₁ B₂ B₃ : ModuleCat.{u} R}
    (f₁ : A₁ ⟶ A₂) (g₁ : A₂ ⟶ A₃)
    (f₂ : B₁ ⟶ B₂) (g₂ : B₂ ⟶ B₃)
    (hf : Function.Exact f₁.hom g₁.hom) (hg : Function.Exact f₂.hom g₂.hom) :
    Function.Exact (biprod.map f₁ f₂).hom (biprod.map g₁ g₂).hom := by
  have hprod : Function.Exact (f₁.hom.prodMap f₂.hom) (g₁.hom.prodMap g₂.hom) :=
    functionExact_prodMap f₁.hom g₁.hom f₂.hom g₂.hom hf hg
  -- Transport exactness through the explicit product model of each biproduct object.
  have h₁₂ :
      (f₁.hom.prodMap f₂.hom).comp (ModuleCat.biprodIsoProd A₁ B₁).toLinearEquiv.toLinearMap =
        (ModuleCat.biprodIsoProd A₂ B₂).toLinearEquiv.toLinearMap.comp (biprod.map f₁ f₂).hom := by
    ext x
    · have h := congrArg (fun k : A₁ ⊞ B₁ ⟶ ModuleCat.of R (A₂ × B₂) => k.hom x)
        (biprod_map_comp_biprodIsoProd_hom f₁ f₂).symm
      simpa [LinearMap.comp_apply] using congrArg Prod.fst h
    · have h := congrArg (fun k : A₁ ⊞ B₁ ⟶ ModuleCat.of R (A₂ × B₂) => k.hom x)
        (biprod_map_comp_biprodIsoProd_hom f₁ f₂).symm
      simpa [LinearMap.comp_apply] using congrArg Prod.snd h
  have h₂₃ :
      (g₁.hom.prodMap g₂.hom).comp (ModuleCat.biprodIsoProd A₂ B₂).toLinearEquiv.toLinearMap =
        (ModuleCat.biprodIsoProd A₃ B₃).toLinearEquiv.toLinearMap.comp (biprod.map g₁ g₂).hom := by
    ext x
    · have h := congrArg (fun k : A₂ ⊞ B₂ ⟶ ModuleCat.of R (A₃ × B₃) => k.hom x)
        (biprod_map_comp_biprodIsoProd_hom g₁ g₂).symm
      simpa [LinearMap.comp_apply] using congrArg Prod.fst h
    · have h := congrArg (fun k : A₂ ⊞ B₂ ⟶ ModuleCat.of R (A₃ × B₃) => k.hom x)
        (biprod_map_comp_biprodIsoProd_hom g₁ g₂).symm
      simpa [LinearMap.comp_apply] using congrArg Prod.snd h
  exact (Function.Exact.iff_of_ladder_linearEquiv h₁₂ h₂₃).1 hprod

/-- Helper for Chap10 Example 10 82 6: the componentwise biproduct row has zero composite. -/
private lemma componentwiseBiprodShortComplex_zero {R : Type u} [CommRing R]
    (S T : ShortComplex (ModuleCat.{u} R)) :
    biprod.map S.f T.f ≫ biprod.map S.g T.g = 0 := by
  -- Test the composite on the two summand inclusions and use the two original zero composites.
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc, biprod.inl_map]
    rw [← Category.assoc, S.zero, zero_comp]
    simp
  · simp only [biprod.inr_map_assoc, biprod.inr_map]
    rw [← Category.assoc, T.zero, zero_comp]
    simp

/-- Helper for Chap10 Example 10 82 6: the short complex obtained by taking biproducts in each
degree and using the componentwise biproduct maps. -/
private def componentwiseBiprodShortComplex {R : Type u} [CommRing R]
    (S T : ShortComplex (ModuleCat.{u} R)) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g)
    (componentwiseBiprodShortComplex_zero S T)

/-- Helper for Chap10 Example 10 82 6: the componentwise biproduct short complex is short exact
when both summand short complexes are short exact. -/
private lemma componentwiseBiprodShortComplex_shortExact {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (hT : T.ShortExact) :
    (componentwiseBiprodShortComplex S T).ShortExact := by
  letI : Mono S.f := hS.mono_f
  letI : Mono T.f := hT.mono_f
  letI : Epi S.g := hS.epi_g
  letI : Epi T.g := hT.epi_g
  -- Exactness is checked on the product model; mono and epi are inherited by `biprod.map`.
  refine ModuleCat.shortComplex_shortExact (componentwiseBiprodShortComplex S T) ?_ ?_ ?_
  · exact functionExact_biprodMap S.f S.g T.f T.g
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT.exact)
  · simpa [componentwiseBiprodShortComplex] using
      (ModuleCat.mono_iff_injective (biprod.map S.f T.f)).1 (biprod.map_mono S.f T.f)
  · simpa [componentwiseBiprodShortComplex] using
      (ModuleCat.epi_iff_surjective (biprod.map S.g T.g)).1 (biprod.map_epi S.g T.g)

/-- Helper for Chap10 Example 10 82 6: mapping short complexes by a zero-preserving functor is
again zero-preserving as a functor on short complexes. -/
private instance mapShortComplexPreservesZeroMorphisms {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.PreservesZeroMorphisms] :
    F.mapShortComplex.PreservesZeroMorphisms := by
  have hMapZero : ∀ X Y : ShortComplex (ModuleCat.{u} R),
      F.mapShortComplex.map (0 : X ⟶ Y) = 0 := by
    intro X Y
    apply ShortComplex.hom_ext
    · exact Functor.map_zero F X.X₁ Y.X₁
    · exact Functor.map_zero F X.X₂ Y.X₂
    · exact Functor.map_zero F X.X₃ Y.X₃
  exact ⟨hMapZero⟩

/-- Helper for Chap10 Example 10 82 6: an additive functor on modules induces an additive
functor on short complexes. -/
private instance mapShortComplexAdditive {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.PreservesZeroMorphisms] [F.Additive] :
    F.mapShortComplex.Additive := by
  have hMapAdd : ∀ {X Y : ShortComplex (ModuleCat.{u} R)} {f g : X ⟶ Y},
      F.mapShortComplex.map (f + g) = F.mapShortComplex.map f + F.mapShortComplex.map g := by
    intro X Y f g
    apply ShortComplex.hom_ext
    · exact Functor.map_add F
    · exact Functor.map_add F
    · exact Functor.map_add F
  exact ⟨@hMapAdd⟩

/-- Helper for Example 10.82.6: binary biproducts of short exact short complexes of modules should
again be short exact. -/
theorem shortExact_biprod {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) (hT : T.ShortExact) :
    (S ⊞ T).ShortExact := by
  letI : PreservesBinaryBiproduct S T
      (ShortComplex.π₁ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R) :=
    preservesBinaryBiproduct_of_preservesBinaryProduct _
  letI : PreservesBinaryBiproduct S T
      (ShortComplex.π₂ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R) :=
    preservesBinaryBiproduct_of_preservesBinaryProduct _
  letI : PreservesBinaryBiproduct S T
      (ShortComplex.π₃ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R) :=
    preservesBinaryBiproduct_of_preservesBinaryProduct _
  -- Transport the categorical biproduct to the componentwise row, where exactness is explicit.
  refine ShortComplex.shortExact_of_iso ?_ (componentwiseBiprodShortComplex_shortExact hS hT)
  refine (ShortComplex.isoMk
    ((ShortComplex.π₁ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapBiprod S T)
    ((ShortComplex.π₂ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapBiprod S T)
    ((ShortComplex.π₃ : ShortComplex (ModuleCat.{u} R) ⥤ ModuleCat.{u} R).mapBiprod S T) ?_ ?_).symm
  · -- The first differential is componentwise after projecting to both summands.
    apply biprod.hom_ext
    · simpa [componentwiseBiprodShortComplex, Category.assoc] using
        (biprod.fst : S ⊞ T ⟶ S).comm₁₂
    · simpa [componentwiseBiprodShortComplex, Category.assoc] using
        (biprod.snd : S ⊞ T ⟶ T).comm₁₂
  · -- The same componentwise comparison applies to the second differential.
    apply biprod.hom_ext
    · simpa [componentwiseBiprodShortComplex, Category.assoc] using
        (biprod.fst : S ⊞ T ⟶ S).comm₂₃
    · simpa [componentwiseBiprodShortComplex, Category.assoc] using
        (biprod.snd : S ⊞ T ⟶ T).comm₂₃

/-- Chap10 Example 10 82 6: binary biproducts of universally exact short complexes of modules
are again universally exact. -/
theorem universallyExact_biprod {R : Type u} [CommRing R]
    {S T : ShortComplex (ModuleCat.{u} R)} (hS : S.UniversallyExact) (hT : T.UniversallyExact) :
    (S ⊞ T).UniversallyExact := by
  constructor
  · -- The short-exact part is the biproduct stability result just proved.
    exact shortExact_biprod hS.shortExact hT.shortExact
  · intro Q _ _
    let N : ModuleCat.{u} R := ModuleCat.of R Q
    have hTensorShortExact : ((S ⊞ T).map (tensorLeft N)).ShortExact := by
      letI : PreservesFiniteBiproducts (tensorLeft N) :=
        Functor.preservesFiniteBiproductsOfAdditive (tensorLeft N)
      letI : PreservesBinaryBiproducts (tensorLeft N) :=
        preservesBinaryBiproducts_of_preservesBiproducts (tensorLeft N)
      letI : PreservesFiniteBiproducts ((tensorLeft N).mapShortComplex) :=
        Functor.preservesFiniteBiproductsOfAdditive ((tensorLeft N).mapShortComplex)
      letI : PreservesBinaryBiproducts ((tensorLeft N).mapShortComplex) :=
        preservesBinaryBiproducts_of_preservesBiproducts ((tensorLeft N).mapShortComplex)
      have hBiprod : ((S.map (tensorLeft N)) ⊞ (T.map (tensorLeft N))).ShortExact :=
        shortExact_biprod (hS.tensorLeft_shortExact N) (hT.tensorLeft_shortExact N)
      -- Tensoring preserves the binary biproduct, so exactness transports back across `mapBiprod`.
      exact ShortComplex.shortExact_of_iso
        (((tensorLeft N).mapShortComplex).mapBiprod S T).symm hBiprod
    -- Convert the tensor-left mono statement to the right-tensor injectivity in the definition.
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    simpa [N, ModuleCat.hom_whiskerLeft] using
      (ModuleCat.mono_iff_injective (((S ⊞ T).map (tensorLeft N)).f)).1
        hTensorShortExact.mono_f

/-- The concrete short complex from Example 10.82.6 (3), obtained by taking the direct sum of the
non-split universally exact quotient sequence from clause `(1)` with the split self-sum sequence
from clause `(2)` specialized to `ZMod 2`. -/
def universallyExactNonsplitNonflatShortComplex : ShortComplex (ModuleCat.{0} ℤ) :=
  integerDirectSumProductShortComplex ⊞ selfSumShortComplex (ModuleCat.of ℤ (ZMod 2))

/-- Example 10.82.6 (3): the direct-sum short complex constructed above is universally exact. -/
-- Proof sketch: clause `(1)` gives universal exactness of
-- `integerDirectSumProductShortComplex`, clause `(2)` gives universal exactness of the `ZMod 2`
-- self-sum sequence, and binary direct sums preserve the universal exactness criterion.
@[stacks 058N]
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
@[stacks 058N]
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
@[stacks 058N]
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
@[stacks 058N]
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
@[stacks 058N]
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

/-- Consequence of Chap10 Example 10 82 6: there exists a universally exact non-split short exact
sequence of `\mathbf Z`-modules whose three terms are all non-flat. -/
@[stacks 058N]
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
