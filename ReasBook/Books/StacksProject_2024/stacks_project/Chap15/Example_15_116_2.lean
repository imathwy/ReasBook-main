import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_44_2
import StacksProject_2024.stacks_project.Chap10.Definition_10_119_8
import StacksProject_2024.stacks_project.Chap15.Definition_15_116_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_115_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

universe u v

open IsLocalRing PowerSeries
open scoped UniformizerRoot IntermediateField

/-
Domain-style sampling for Example `15.116.2`.

- primary domain: finite base change of extensions of discrete valuation rings, specialized to the
  canonical radical extension `k[[x]] ⊂ k[[x]][x^{1/p}]`;
- sampled owner declarations:
  `IsWeakSolutionFor`,
  `IsSolutionFor`,
  `uniformizerRootExtensionRing`,
  `uniformizerRootExtension`;
- best owner abstraction: the source-facing example should reuse the chapter owners
  `IsWeakSolutionFor` / `IsSolutionFor` from `Definition_15_116_1` and the radical-extension owner
  API from `Lemma_15_115_2`, rather than rebuilding parallel local algebra/module wrappers;
- primitive-vs-derived split: the primitive data here are the power-series DVR `A = k[[x]]`, the
  canonical radical extension ring/field `A[π^(1/p)]` and `K[π^(1/p)]`, and the base-change field
  `K₁`; field, module, finite-dimensionality, DVR, fraction-field, and extension-of-DVR structure
  on `A[π^(1/p)]` and `K[π^(1/p)]` are derived API from the upstream owners.

Source/core/bridge triage:
- `source-facing`: the two example theorems about weak solutions and solutions for
  `k[[x]] ⊂ k[[x]][x^{1/p}]`;
- `core/canonical`: `IsWeakSolutionFor`, `IsSolutionFor`, `uniformizerRootExtensionRing`,
  `uniformizerRootExtension`;
- `bridge/view`: the owner-provided radical-extension tower, fraction-field, and
  `IsExtensionOfDiscreteValuationRings` bridges, specialized here to `π = X`.
-/

section

variable (k : Type u) [Field k]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectField k]

local notation "A" => PowerSeries k
local notation "K" => FractionRing A
local notation "π" => (X : A)

private lemma hp : 0 < p :=
  Nat.Prime.pos (Fact.out : Nat.Prime p)

omit [PerfectField k] in
private lemma hπ : Irreducible π :=
  (maximalIdeal_eq_span_singleton_iff_irreducible π).mp PowerSeries.maximalIdeal_eq_span_X

section BaseChange

variable (K₁ : Type v) [Field K₁] [Algebra (PowerSeries k) K₁]
variable [Algebra (FractionRing (PowerSeries k)) K₁]
variable [IsScalarTower (PowerSeries k) (FractionRing (PowerSeries k)) K₁]
variable [FiniteDimensional (FractionRing (PowerSeries k)) K₁]

local notation "B" => uniformizerRootExtensionRing π p
local notation "L" => AdjoinRoot (uniformizerRootFractionPolynomial π p)

local instance : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : Nat.Prime p)⟩

local instance : Fact (Irreducible π) := ⟨hπ k⟩

local instance : Field L := inferInstance

local instance : Algebra K L := by
  change Algebra K
    (Polynomial K ⧸
      (Ideal.span {uniformizerRootFractionPolynomial π p} : Ideal (Polynomial K)))
  let _ : Algebra K K := Algebra.id K
  infer_instance

local instance : Algebra A L := by
  change Algebra A
    (Polynomial K ⧸
      (Ideal.span {uniformizerRootFractionPolynomial π p} : Ideal (Polynomial K)))
  infer_instance

local instance : IsScalarTower A K L := by
  change IsScalarTower A K
    (Polynomial K ⧸
      (Ideal.span {uniformizerRootFractionPolynomial π p} : Ideal (Polynomial K)))
  infer_instance

local instance : FiniteDimensional K L := by
  change FiniteDimensional K (AdjoinRoot (uniformizerRootFractionPolynomial π p))
  have hmonic : (uniformizerRootFractionPolynomial π p).Monic := by
    simpa [uniformizerRootPolynomial] using
      (Polynomial.monic_X_pow_sub_C (algebraMap A K π) (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
  exact hmonic.finite_adjoinRoot

local instance : IsDomain B := inferInstance

local instance : IsDiscreteValuationRing B := inferInstance

local instance : Algebra B L := inferInstance

local instance : IsScalarTower A B L := inferInstance

local instance : IsIntegralClosure B A L := by
  -- Use the canonical integral-closure theorem from Lemma `15.115.2`, rather than the deleted
  -- irreducible-context wrapper instance.
  exact
    uniformizerRootExtensionRing_isIntegralClosure
      (A := A) (π := π) (n := p) (hπ := hπ k) (hn := hp k p)

local instance : IsFractionRing B L := by
  -- The fraction-field owner is already the canonical instance specialized to `π = X`.
  exact
    uniformizerRootExtensionRing_isFractionRing
      (A := A) (π := π) (n := p) (hπ := hπ k) (hn := hp k p)

local instance : IsExtensionOfDiscreteValuationRings A B := by
  -- Reuse the canonical extension-of-DVR owner directly, without a parallel compatibility layer.
  exact
    uniformizerRootExtensionRing_isExtensionOfDiscreteValuationRings
      (A := A) (π := π) (n := p) (hπ := hπ k) (hn := hp k p)

/-- Helper for Example 15.116.2: one localized branch with nontrivial ramification already rules
out the weak-solution condition. -/
private theorem not_isWeakSolutionFor_of_exists_bad_branch
    (hbad :
      ∃ p : Ideal (integralClosure A K₁), p.IsMaximal ∧
        ∃ q : Ideal (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))),
          q.IsMaximal ∧ q.LiesOver p ∧
            Ideal.map
                (Localization.localRingHom p q
                  (algebraMap (integralClosure A K₁)
                    (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
                  (q.over_def p))
                (maximalIdeal (Localization.AtPrime p)) ≠
              maximalIdeal (Localization.AtPrime q)) :
    ¬ IsWeakSolutionFor A B K L K₁ := by
  intro hWeak
  -- A single branch violating the maximal-ideal equality contradicts the owner characterization
  -- of weak solutions.
  rcases hbad with ⟨p, hp, q, hq, hq_over, hneq⟩
  letI : p.IsMaximal := hp
  letI : q.IsMaximal := hq
  letI : q.LiesOver p := hq_over
  exact
    hneq
      ((isWeakSolutionFor_iff_map_maximalIdeal
        (A := A) (B := B) (K := K) (L := L) (K1 := K₁)).1 hWeak p q)

/-- Helper for Example 15.116.2: on a localized DVR branch, ramification index `p` forces the
maximal ideals not to match. -/
private theorem map_maximalIdeal_ne_of_ramificationIndex_eq_prime
    {R : Type*} {S : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtensionOfDiscreteValuationRings R S]
    (hram : ramificationIndex R S = p) :
    Ideal.map (algebraMap R S) (maximalIdeal R) ≠ maximalIdeal S := by
  -- If the maximal ideals agreed, the branch would be weakly unramified.
  intro hmap
  have hweak : WeaklyUnramified R S := by
    rw [weaklyUnramified_iff_map_maximalIdeal]
    exact hmap
  -- A weakly unramified branch has ramification index `1`, contradicting primality of `p`.
  have hram_one : ramificationIndex R S = 1 :=
    (weaklyUnramified_iff_ramificationIndex_eq_one).1 hweak
  exact (Nat.Prime.ne_one (Fact.out : Nat.Prime p)) (hram.symm.trans hram_one)

/-- Helper for Example 15.116.2: the canonical extension `k[[x]] ⊂ k[[x]][x^(1/p)]` already has
ramification index `p`. -/
private theorem ramificationIndex_powerSeries_pth_root_extension :
    ramificationIndex A B = p := by
  -- This is the direct specialization of the owner ramification computation from
  -- Lemma `15.115.2`.
  simpa using
    (ramificationIndex_uniformizerRootExtensionRing
      (A := A) (π := π) (n := p) (hπ := hπ k) (hn := hp k p))

/-- Helper for Example 15.116.2: the fraction-field extension `k((x))[x^(1/p)] / k((x))` has
degree exactly `p`. -/
private theorem finrank_powerSeries_pth_root_extension :
    Module.finrank K L = p := by
  -- The canonical radical-extension owner already computes the degree of `K[x^(1/p)] / K`.
  simpa using
    (uniformizerRootExtensionField_finrank_eq
      (A := A) (π := π) (n := p) (hπ := hπ k) (hn := hp k p))

/-- Helper for Example 15.116.2: the canonical pth-root extension is totally ramified with
respect to `k[[x]]`. -/
private theorem powerSeries_pth_root_extension_isTotallyRamified :
    IsTotallyRamifiedWithRespectTo A L := by
  -- Package the canonical unique-branch and residue-field-triviality data once, so the remaining
  -- proof only needs to transport them through base change.
  simpa using
    (uniformizerRootExtensionField_isTotallyRamifiedWithRespectTo
      (A := A) (π := π) (n := p))

/-- Helper for Example 15.116.2: the canonical extension `k[[x]] ⊂ k[[x]][x^(1/p)]` induces no
residue-field extension above the maximal ideal. -/
private theorem residueFieldMap_bijective_powerSeries_pth_root_extension :
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal A) (maximalIdeal B) (algebraMap A B)
        ((Ideal.liesOver_iff _ _).2 rfl)) := by
  -- The canonical radical extension has a unique branch above the closed point, and the owner
  -- theorem computes that branch's residue-field map.
  simpa using
    (uniformizerRootExtensionRing_residueFieldMap_bijective
      (A := A) (π := π) (n := p) (hπ := hπ k) (hn := hp k p)
      (P := maximalIdeal B) (hP := maximalIdeal.isMaximal B) (hPOver := (Ideal.liesOver_iff _ _).2 rfl))

/-- Helper for Example 15.116.2: in a separable characteristic-`p` extension, a displayed `p`th
root of a base element already lies in the base field. -/
private theorem exists_pth_root_in_base_of_isSeparable
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    {a : F} {y : E} [CharP F p] [Algebra.IsSeparable F E]
    (hy : y ^ p = algebraMap F E a) :
    ∃ x : F, x ^ p = a := by
  have hpow_mem : ∃ n : ℕ, y ^ p ^ n ∈ (algebraMap F E).range := by
    -- The displayed relation already witnesses that the simple extension generated by `y` is
    -- purely inseparable over `F`.
    refine ⟨1, ?_⟩
    refine ⟨a, ?_⟩
    simpa [hy, pow_one]
  haveI : IsPurelyInseparable F F⟮y⟯ := by
    rw [IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem (F := F) (E := E) p]
    simpa using hpow_mem
  have hy_sep : IsSeparable F y := Algebra.IsSeparable.isSeparable F y
  haveI : Algebra.IsSeparable F F⟮y⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F E).2 hy_sep
  have hadjoin_bot : F⟮y⟯ = (⊥ : IntermediateField F E) :=
    IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable (F := F) (E := E) F⟮y⟯
  have hy_mem : y ∈ (⊥ : IntermediateField F E) := by
    -- The simple extension collapses to the base field because it is both separable and purely
    -- inseparable.
    rw [← hadjoin_bot]
    exact IntermediateField.mem_adjoin_simple_self F y
  rcases (IntermediateField.mem_bot (F := F) (E := E)).mp hy_mem with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- Compare the displayed equality after rewriting `y` as the image of the recovered base point.
  apply FaithfulSMul.algebraMap_injective F E
  simpa [hx] using hy

/-- Helper for Example 15.116.2: the uniformizer `x` is not already a `p`th power in the
fraction field `k((x))`. -/
private theorem uniformizer_not_pth_power_in_fractionField :
    ¬ ∃ y : K, y ^ p = (π : K) := by
  intro hroot
  rcases hroot with ⟨y, hy⟩
  let f : Polynomial K := X ^ p - C (π : K)
  have hirr : Irreducible f := by
    -- The canonical Kummer polynomial over `k((x))` is irreducible.
    simpa [f, uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
      (uniformizerRootFractionPolynomial_irreducible
        (A := A) (π := π) (n := p) (hπ := hπ k) (hn := (hp k p).ne'))
  have hy_aeval : aeval y f = 0 := by
    -- The chosen element `y` is a root of `X ^ p - x`.
    rw [Polynomial.aeval_def, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    exact sub_eq_zero.mpr hy
  have hmin : minpoly K y = f := by
    -- Irreducibility identifies the minimal polynomial of a root in any extension.
    exact
      (minpoly.eq_of_irreducible_of_monic hirr hy_aeval
        (Polynomial.monic_X_pow_sub_C (π : K) (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))).symm
  have hlin : minpoly K y = X - C y := by
    -- Over the base field itself, the minimal polynomial is linear.
    simpa using (minpoly.eq_X_sub_C y)
  have hp_eq_one : p = 1 := by
    have hdegf : f.natDegree = p := by
      simpa [f] using
        (Polynomial.natDegree_X_pow_sub_C (π : K) (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
    have hdegxy : (X - C y : Polynomial K).natDegree = 1 := by
      simpa using (Polynomial.natDegree_X_sub_C y)
    -- Compare the two descriptions of the same minimal polynomial.
    calc
      p = f.natDegree := hdegf.symm
      _ = (minpoly K y).natDegree := by rw [hmin]
      _ = (X - C y : Polynomial K).natDegree := by rw [hlin]
      _ = 1 := hdegxy
  exact (Nat.Prime.ne_one (Fact.out : Nat.Prime p)) hp_eq_one

/-- Helper for Example 15.116.2: a separable finite extension of `k((x))` cannot already contain
a `p`th root of the uniformizer `x`. -/
private theorem uniformizer_not_pth_power_of_isSeparable
    [Algebra.IsSeparable K K₁] :
    ¬ ∃ y : K₁, y ^ p = algebraMap K K₁ (π : K) := by
  rintro ⟨y, hy⟩
  -- Route correction: descend the displayed `p`th root through separability first, then rule it
  -- out already over `k((x))`.
  obtain ⟨x, hx⟩ :=
    exists_pth_root_in_base_of_isSeparable
      (p := p) (F := K) (E := K₁) (a := (π : K)) hy
  exact uniformizer_not_pth_power_in_fractionField (k := k) (p := p) ⟨x, hx⟩

/-- Helper for Example 15.116.2: the distinguished root in `K[x^(1/p)]` has minimal polynomial
`X^p - x` over `K`. -/
private theorem uniformizerRoot_minpoly :
    minpoly K (uniformizerRoot π p : L) = uniformizerRootFractionPolynomial π p := by
  let f : Polynomial K := uniformizerRootFractionPolynomial π p
  have hirr : Irreducible f := by
    -- The owner irreducibility theorem already identifies the defining Kummer polynomial.
    simpa [f, uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
      (uniformizerRootFractionPolynomial_irreducible
        (A := A) (π := π) (n := p) (hπ := hπ k) (hn := (hp k p).ne'))
  have hroot : aeval (uniformizerRoot π p : L) f = 0 := by
    -- The distinguished root satisfies its defining polynomial by construction.
    simpa [f, uniformizerRoot] using (AdjoinRoot.eval₂_root f)
  have hmonic : f.Monic := by
    -- The polynomial `X^p - x` is monic, so irreducibility pins down the minimal polynomial.
    simpa [f, uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
      (Polynomial.monic_X_pow_sub_C (π : K) (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
  exact (minpoly.eq_of_irreducible_of_monic hirr hroot hmonic).symm

/-- Helper for Example 15.116.2: the ambient field presentation `K[x^(1/p)]` is already the
simple extension generated by its distinguished root. -/
private noncomputable theorem powerSeries_pth_root_equiv_adjoin_simple :
    L ≃ₐ[K] K⟮(uniformizerRoot π p : L)⟯ := by
  have hroot_integral : IsIntegral K (uniformizerRoot π p : L) := by
    -- The adjoined root is integral over `K` because it satisfies the defining monic polynomial.
    simpa [L, uniformizerRootExtension, uniformizerRoot] using
      (AdjoinRoot.isIntegral_root (f := uniformizerRootFractionPolynomial π p))
  -- Route correction: use the canonical simple-extension owner from Chapter 9, rather than
  -- reopening the `AdjoinRoot` presentation every time on the inseparable side.
  simpa [uniformizerRoot_minpoly (k := k) (p := p), L, uniformizerRootExtension] using
    (IntermediateField.adjoinRootEquivAdjoin K hroot_integral :
      AdjoinRoot (minpoly K (uniformizerRoot π p : L)) ≃ₐ[K]
        K⟮(uniformizerRoot π p : L)⟯)

/-- Helper for Example 15.116.2: adjoining a chosen `p`th root of `x` already gives a purely
inseparable simple extension of `K`. -/
private theorem adjoin_uniformizer_root_isPurelyInseparable
    {r : AlgebraicClosure K}
    (hr : r ^ p = algebraMap K (AlgebraicClosure K) (π : K)) :
    IsPurelyInseparable K K⟮r⟯ := by
  -- The source-faithful input is exactly that the chosen generator has its `p`th power back in
  -- the base field.
  rw [IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem (F := K)
    (E := AlgebraicClosure K) p]
  refine ⟨1, ?_⟩
  refine ⟨(π : K), ?_⟩
  simpa [pow_one] using hr

/-- Helper for Example 15.116.2: any displayed `p`th root of the uniformizer `x` belongs to the
chosen model `K^{1/p}`. -/
private theorem uniformizer_root_mem_onePthRootExtension
    {r : AlgebraicClosure K}
    (hr : r ^ p = algebraMap K (AlgebraicClosure K) (π : K)) :
    r ∈ onePthRootExtension K p := by
  -- The defining membership criterion for `K^{1/p}` is exactly that the `p`th power comes from
  -- the base field.
  rw [mem_onePthRootExtension_iff]
  exact ⟨(π : K), hr.symm⟩

/-- Helper for Example 15.116.2: adjoining a chosen `p`th root of `x` gives an intermediate field
contained in the chapter model `K^{1/p}`. -/
private theorem adjoin_uniformizer_root_le_onePthRootExtension
    {r : AlgebraicClosure K}
    (hr : r ^ p = algebraMap K (AlgebraicClosure K) (π : K)) :
    K⟮r⟯ ≤ onePthRootExtension K p := by
  -- Once the root itself lies in `K^{1/p}`, the simple extension it generates is contained in the
  -- same intermediate field.
  exact
    (IntermediateField.adjoin_simple_le_iff).2
      (uniformizer_root_mem_onePthRootExtension (k := k) (p := p) hr)

/-- Helper for Example 15.116.2: every Laurent-series element of `k((x))` acquires a `p`th root
inside the simple extension generated by a chosen `p`th root of `x`. -/
private theorem powerSeries_baseElement_has_pth_root_in_adjoin_uniformizer_root
    {r : AlgebraicClosure K}
    (hr : r ^ p = algebraMap K (AlgebraicClosure K) (π : K))
    (a : K) :
    ∃ s : K⟮r⟯, ((s : AlgebraicClosure K) ^ p = algebraMap K (AlgebraicClosure K) a) := by
  -- TODO: split `a` into a Laurent monomial in `x` times a power series with coefficients in the
  -- perfect field `k`, build the coefficientwise `p`th root after replacing `x` by `r ^ p`, and
  -- then absorb the Laurent monomial as a power of `r`.
  sorry

/-- Helper for Example 15.116.2: every element of the chapter model `K^{1/p}` already lies in the
simple extension generated by a chosen `p`th root of `x`. -/
private theorem onePthRootExtension_le_adjoin_uniformizer_root
    {r : AlgebraicClosure K}
    (hr : r ^ p = algebraMap K (AlgebraicClosure K) (π : K)) :
    onePthRootExtension K p ≤ K⟮r⟯ := by
  -- Route correction: once the Laurent-series `p`th-root existence statement is isolated, the
  -- reverse inclusion is just the Frobenius-injectivity argument from the source proof.
  intro z hz
  rcases (mem_onePthRootExtension_iff (k := K) (p := p)).mp hz with ⟨a, hza⟩
  rcases powerSeries_baseElement_has_pth_root_in_adjoin_uniformizer_root
      (k := k) (p := p) hr a with ⟨s, hs⟩
  have hpow_eq : z ^ p = ((s : K⟮r⟯) : AlgebraicClosure K) ^ p := by
    simpa [hza] using hs.symm
  have hsub_pow : (z - ((s : K⟮r⟯) : AlgebraicClosure K)) ^ p = 0 := by
    rw [sub_pow_char]
    exact sub_eq_zero.mpr hpow_eq
  have hsub : z - ((s : K⟮r⟯) : AlgebraicClosure K) = 0 := pow_eq_zero hsub_pow
  have hz_eq : z = ((s : K⟮r⟯) : AlgebraicClosure K) := sub_eq_zero.mp hsub
  exact hz_eq.symm ▸ s.2

/-- Helper for Example 15.116.2: the explicit radical extension `K[x^(1/p)]` agrees with the
chapter's chosen model `K^{1/p}` used in Lemma `10.44.2`. -/
private noncomputable theorem powerSeries_pth_root_equiv_onePthRootExtension :
    L ≃ₐ[K] onePthRootExtension K p := by
  let f : Polynomial K := X ^ p - C (π : K)
  have hirr : Irreducible f := by
    -- The Kummer polynomial `X ^ p - x` remains irreducible over `K = k((x))`.
    simpa [f, uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
      (uniformizerRootFractionPolynomial_irreducible
        (A := A) (π := π) (n := p) (hπ := hπ k) (hn := (hp k p).ne'))
  obtain ⟨r, hrroot⟩ := IsAlgClosed.exists_root f (degree_pos_of_irreducible hirr).ne'
  have hrpow : r ^ p = algebraMap K (AlgebraicClosure K) (π : K) := by
    -- Unfold the root equation back to the source-facing relation `r ^ p = x`.
    rw [Polynomial.IsRoot.def] at hrroot
    simpa [f, sub_eq_zero] using hrroot
  have hr_integral : IsIntegral K r := by
    -- The chosen root is integral because it satisfies the monic Kummer polynomial.
    refine ⟨f, ?_, ?_⟩
    · simpa [f] using
        (Polynomial.monic_X_pow_sub_C (π : K) (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
    · simpa [Polynomial.aeval_def, f] using hrroot
  have hmin : minpoly K r = f := by
    -- Irreducibility pins down the minimal polynomial of the chosen root.
    exact
      (minpoly.eq_of_irreducible_of_monic
        hirr
        (by simpa [Polynomial.aeval_def, f] using hrroot)
        (by
          simpa [f] using
            (Polynomial.monic_X_pow_sub_C (π : K)
              (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))))).symm
  let eAdjoin : L ≃ₐ[K] K⟮r⟯ := by
    -- Compare the explicit quotient `K[x^(1/p)]` with the simple extension generated by the
    -- chosen algebraic-closure root.
    simpa [hmin, f, L, uniformizerRootExtension] using
      (IntermediateField.adjoinRootEquivAdjoin K hr_integral :
        AdjoinRoot (minpoly K r) ≃ₐ[K] K⟮r⟯)
  have hle : K⟮r⟯ ≤ onePthRootExtension K p :=
    adjoin_uniformizer_root_le_onePthRootExtension (k := k) (p := p) hrpow
  have hEq : K⟮r⟯ = onePthRootExtension K p := by
    -- The remaining source-faithful content is exactly the reverse inclusion helper isolated
    -- above.
    exact le_antisymm hle
      (onePthRootExtension_le_adjoin_uniformizer_root (k := k) (p := p) hrpow)
  -- The only remaining task is the reverse inclusion identifying the chapter model `K^{1/p}`
  -- with the simple extension generated by a root of `X ^ p - x`.
  exact hEq ▸ eAdjoin

/-- Helper for Example 15.116.2: the generic fiber `K[x^(1/p)]` maps to the explicit Kummer
quotient over `K₁` by sending the distinguished `p`th root of `x` to the adjoined root. -/
private noncomputable def powerSeries_pth_root_to_adjoinRoot :
    L →ₐ[K]
      AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) := by
  let T := AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)
  refine
    AdjoinRoot.liftAlgHom
      (uniformizerRootFractionPolynomial π p)
      (algebraMap K T)
      (AdjoinRoot.root (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁))
      ?_
  -- Evaluating the original Kummer polynomial after base change to `K₁` kills the target root.
  simpa [uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
    (AdjoinRoot.eval₂_root (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁))

/-- Helper for Example 15.116.2: base changing the generic fiber to `K₁` gives a canonical map to
the explicit Kummer quotient over `K₁`. -/
private noncomputable def tensor_powerSeries_pth_root_to_adjoinRoot :
    L ⊗[K] K₁ →ₐ[K]
      AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) :=
  Algebra.TensorProduct.lift
    (powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁))
    (algebraMap K₁
      (AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)))
    (fun _ _ ↦ Commute.all _ _)

/-- Helper for Example 15.116.2: the generic-fiber comparison sends the distinguished tensor root
to the Kummer root over `K₁`. -/
private theorem tensor_powerSeries_pth_root_to_adjoinRoot_tmul_uniformizerRoot :
    tensor_powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁)
        (uniformizerRoot π p ⊗ₜ[K] (1 : K₁)) =
      AdjoinRoot.root (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) := by
  -- Evaluate the tensor universal-property map on the distinguished pure tensor.
  rw [Algebra.TensorProduct.lift_tmul]
  -- The left factor is the defining root map, and the right factor contributes the unit.
  simp [tensor_powerSeries_pth_root_to_adjoinRoot, powerSeries_pth_root_to_adjoinRoot,
    AdjoinRoot.liftAlgHom_root]

/-- Helper for Example 15.116.2: the generic-fiber comparison is the canonical scalar map on the
right tensor factor. -/
private theorem tensor_powerSeries_pth_root_to_adjoinRoot_tmul_right
    (x : K₁) :
    tensor_powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁)
        ((1 : L) ⊗ₜ[K] x) =
      algebraMap K₁
        (AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)) x := by
  -- On the right tensor generator, the universal map is just the scalar structure map.
  rw [Algebra.TensorProduct.lift_tmul]
  simp [tensor_powerSeries_pth_root_to_adjoinRoot, powerSeries_pth_root_to_adjoinRoot]

/-- Helper for Example 15.116.2: the explicit Kummer quotient over `K₁` maps back to the tensor
product by sending the adjoined root to `x^(1/p) ⊗ 1`. -/
private noncomputable def adjoinRoot_to_tensor_powerSeries_pth_root :
    AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) →ₐ[K]
      L ⊗[K] K₁ := by
  refine
    AdjoinRoot.liftAlgHom
      (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)
      (Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁)
      (uniformizerRoot π p ⊗ₜ[K] (1 : K₁))
      ?_
  -- Evaluate the Kummer polynomial on the chosen tensor root and then use the tensor balancing
  -- relation to identify the two copies of `x`.
  calc
    Polynomial.eval₂
        (↑(Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁))
        (uniformizerRoot π p ⊗ₜ[K] (1 : K₁))
        (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) =
      (uniformizerRoot π p ⊗ₜ[K] (1 : K₁)) ^ p -
        ((1 : L) ⊗ₜ[K] algebraMap K K₁ (π : K)) := by
          simp [Algebra.TensorProduct.includeRight_apply]
    _ = (uniformizerRoot π p ^ p) ⊗ₜ[K] ((1 : K₁) ^ p) -
        ((1 : L) ⊗ₜ[K] algebraMap K K₁ (π : K)) := by
          rw [Algebra.TensorProduct.tmul_pow]
    _ = (algebraMap A L π) ⊗ₜ[K] (1 : K₁) -
        ((1 : L) ⊗ₜ[K] algebraMap K K₁ (π : K)) := by
          simp
    _ = 0 := by
          have hbalance :
              (algebraMap A L π) ⊗ₜ[K] (1 : K₁) =
                (1 : L) ⊗ₜ[K] algebraMap K K₁ (π : K) := by
            -- The two tensor factors represent the same base scalar from `K = k((x))`.
            rw [show algebraMap A L π = algebraMap K L (π : K) by rfl]
            rw [show algebraMap K L (π : K) = (π : K) • (1 : L) by
              rw [Algebra.smul_def, mul_one]]
            rw [show algebraMap K K₁ (π : K) = (π : K) • (1 : K₁) by
              rw [Algebra.smul_def, mul_one]]
            simpa using (TensorProduct.smul_tmul (R := K) (π : K) (1 : L) (1 : K₁))
          rw [hbalance, sub_self]

/-- Helper for Example 15.116.2: the inverse Kummer map sends the adjoined root back to the
distinguished tensor root. -/
private theorem adjoinRoot_to_tensor_powerSeries_pth_root_root :
    adjoinRoot_to_tensor_powerSeries_pth_root (k := k) (p := p) (K₁ := K₁)
        (AdjoinRoot.root (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)) =
      uniformizerRoot π p ⊗ₜ[K] (1 : K₁) := by
  -- This is the defining generator formula of `AdjoinRoot.liftAlgHom`.
  simp [adjoinRoot_to_tensor_powerSeries_pth_root, AdjoinRoot.liftAlgHom_root]

/-- Helper for Example 15.116.2: the inverse Kummer map is the canonical scalar map on the
coefficient field `K₁`. -/
private theorem adjoinRoot_to_tensor_powerSeries_pth_root_algebraMap
    (x : K₁) :
    adjoinRoot_to_tensor_powerSeries_pth_root (k := k) (p := p) (K₁ := K₁)
        (algebraMap K₁
          (AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)) x) =
      (1 : L) ⊗ₜ[K] x := by
  -- On coefficients, the inverse lift is exactly `includeRight`.
  simp [adjoinRoot_to_tensor_powerSeries_pth_root, AdjoinRoot.algebraMap_eq,
    Algebra.TensorProduct.includeRight_apply, AdjoinRoot.liftAlgHom_of]

/-- Helper for Example 15.116.2: restricting the tensor/`AdjoinRoot` comparison to the left tensor
factor recovers the original map `L → AdjoinRoot`. -/
private theorem tensor_powerSeries_pth_root_to_adjoinRoot_comp_includeLeft :
    (tensor_powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁)).comp
        (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) =
      powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁) := by
  -- Both `K`-algebra maps out of `L = K[x^(1/p)]` are determined by the image of the
  -- distinguished root.
  apply AdjoinRoot.algHom_ext
  rw [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply]
  exact tensor_powerSeries_pth_root_to_adjoinRoot_tmul_uniformizerRoot
    (k := k) (p := p) (K₁ := K₁)

/-- Helper for Example 15.116.2: after passing from `L` to the tensor product and back, the
left tensor factor is unchanged. -/
private theorem adjoinRoot_to_tensor_powerSeries_pth_root_comp_powerSeries_pth_root_to_adjoinRoot :
    (adjoinRoot_to_tensor_powerSeries_pth_root (k := k) (p := p) (K₁ := K₁)).comp
        (powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁)) =
      (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) := by
  -- Both `K`-algebra maps out of `L` again agree on the distinguished root, hence are equal.
  apply AdjoinRoot.algHom_ext
  rw [AlgHom.comp_apply,
    tensor_powerSeries_pth_root_to_adjoinRoot_tmul_uniformizerRoot,
    adjoinRoot_to_tensor_powerSeries_pth_root_root, Algebra.TensorProduct.includeLeft_apply]

/-- Helper for Example 15.116.2: package the round trip on the explicit Kummer quotient as a
`K₁`-algebra endomorphism so `AdjoinRoot.algHom_ext` applies directly. -/
private noncomputable def tensor_powerSeries_pth_root_adjoinRoot_roundTrip :
    AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) →ₐ[K₁]
      AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) where
  toRingHom :=
    (tensor_powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁)).toRingHom.comp
      (adjoinRoot_to_tensor_powerSeries_pth_root (k := k) (p := p) (K₁ := K₁)).toRingHom
  commutes' x := by
    -- The inverse sends coefficients to `1 ⊗ x`, and the forward map returns the same scalar.
    rw [RingHom.comp_apply, adjoinRoot_to_tensor_powerSeries_pth_root_algebraMap]
    exact tensor_powerSeries_pth_root_to_adjoinRoot_tmul_right
      (k := k) (p := p) (K₁ := K₁) x

/-- Helper for Example 15.116.2: the explicit Kummer quotient survives the tensor/quotient
comparison unchanged. -/
private theorem tensor_powerSeries_pth_root_to_adjoinRoot_comp_adjoinRoot_to_tensor_powerSeries_pth_root :
    (tensor_powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁)).comp
        (adjoinRoot_to_tensor_powerSeries_pth_root (k := k) (p := p) (K₁ := K₁)) =
      AlgHom.id K
        (AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)) := by
  let φ :
      AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) →ₐ[K₁]
        AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) :=
    tensor_powerSeries_pth_root_adjoinRoot_roundTrip (k := k) (p := p) (K₁ := K₁)
  have hφ : φ = AlgHom.id K₁
      (AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)) := by
    -- The round trip on the Kummer quotient fixes the adjoined root, so it is the identity.
    apply AdjoinRoot.algHom_ext
    change
      tensor_powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁)
          (adjoinRoot_to_tensor_powerSeries_pth_root (k := k) (p := p) (K₁ := K₁)
            (AdjoinRoot.root (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁))) =
        AdjoinRoot.root (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)
    rw [adjoinRoot_to_tensor_powerSeries_pth_root_root]
    exact tensor_powerSeries_pth_root_to_adjoinRoot_tmul_uniformizerRoot
      (k := k) (p := p) (K₁ := K₁)
  ext z
  -- Restrict the `K₁`-algebra identity to the underlying `K`-algebra maps.
  change φ z = z
  simpa using congrArg (fun ψ : _ →ₐ[K₁] _ ↦ ψ z) hφ

/-- Helper for Example 15.116.2: the tensor product also survives the comparison unchanged after
passing to the explicit Kummer quotient and back. -/
private theorem adjoinRoot_to_tensor_powerSeries_pth_root_comp_tensor_powerSeries_pth_root_to_adjoinRoot :
    (adjoinRoot_to_tensor_powerSeries_pth_root (k := k) (p := p) (K₁ := K₁)).comp
        (tensor_powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁)) =
      AlgHom.id K (L ⊗[K] K₁) := by
  -- Use the tensor-product universal property: compare the two composites on the left and right
  -- tensor generators separately.
  apply Algebra.TensorProduct.ext
  · calc
      ((adjoinRoot_to_tensor_powerSeries_pth_root (k := k) (p := p) (K₁ := K₁)).comp
          (tensor_powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁))).comp
          (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) =
          (adjoinRoot_to_tensor_powerSeries_pth_root (k := k) (p := p) (K₁ := K₁)).comp
            (powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁)) := by
              rw [← AlgHom.comp_assoc,
                tensor_powerSeries_pth_root_to_adjoinRoot_comp_includeLeft]
      _ = (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) :=
            adjoinRoot_to_tensor_powerSeries_pth_root_comp_powerSeries_pth_root_to_adjoinRoot
              (k := k) (p := p) (K₁ := K₁)
      _ = (AlgHom.id K (L ⊗[K] K₁)).comp
            (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) := by
              rw [AlgHom.id_comp]
  · ext x
    -- The round trip fixes the right tensor factor because both maps are the scalar structure map
    -- on `K₁`.
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      tensor_powerSeries_pth_root_to_adjoinRoot_tmul_right,
      adjoinRoot_to_tensor_powerSeries_pth_root_algebraMap,
      AlgHom.id_comp, Algebra.TensorProduct.includeRight_apply]

/-- Helper for Example 15.116.2: the generic fiber `L ⊗[K] K₁` is canonically the explicit
Kummer quotient `K₁[X] / (X^p - x)`. -/
private noncomputable def tensor_powerSeries_pth_root_equiv_adjoinRoot :
    L ⊗[K] K₁ ≃ₐ[K]
      AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) :=
  AlgEquiv.ofAlgHom
    (tensor_powerSeries_pth_root_to_adjoinRoot (k := k) (p := p) (K₁ := K₁))
    (adjoinRoot_to_tensor_powerSeries_pth_root (k := k) (p := p) (K₁ := K₁))
    (tensor_powerSeries_pth_root_to_adjoinRoot_comp_adjoinRoot_to_tensor_powerSeries_pth_root
      (k := k) (p := p) (K₁ := K₁))
    (adjoinRoot_to_tensor_powerSeries_pth_root_comp_tensor_powerSeries_pth_root_to_adjoinRoot
      (k := k) (p := p) (K₁ := K₁))

/-- Helper for Example 15.116.2: after separable base change, the generic fiber remains a field
because the explicit Kummer polynomial stays irreducible over `K₁`. -/
private theorem tensor_powerSeries_pth_root_isField_of_isSeparable
    [Algebra.IsSeparable K K₁] :
    IsField (L ⊗[K] K₁) := by
  let f : Polynomial K₁ := X ^ p - C (algebraMap K K₁ (π : K))
  have hno_root : ¬ ∃ y : K₁, y ^ p = algebraMap K K₁ (π : K) :=
    uniformizer_not_pth_power_of_isSeparable (k := k) (p := p) (K₁ := K₁)
  have hirr : Irreducible f :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p) hno_root
  letI : Fact (Irreducible f) := ⟨hirr⟩
  let e : L ⊗[K] K₁ ≃ₐ[K] AdjoinRoot f :=
    tensor_powerSeries_pth_root_equiv_adjoinRoot (k := k) (p := p) (K₁ := K₁)
  -- Transport the field structure back across the explicit tensor/`AdjoinRoot` equivalence.
  let _ : Field (L ⊗[K] K₁) := e.toRingEquiv.field
  exact inferInstance

/-- Helper for Example 15.116.2: after separable base change, the reduced tensor quotient already
is the tensor field itself. -/
private noncomputable theorem reduced_tensor_equiv_tensor_of_isSeparable
    [Algebra.IsSeparable K K₁] :
    ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K] (L ⊗[K] K₁) := by
  letI : IsField (L ⊗[K] K₁) :=
    tensor_powerSeries_pth_root_isField_of_isSeparable (k := k) (p := p) (K₁ := K₁)
  have hnil :
      nilradical (L ⊗[K] K₁) = (⊥ : Ideal (L ⊗[K] K₁)) := by
    -- A field is reduced, so its nilradical is the zero ideal.
    simpa using (nilradical_eq_zero (R := L ⊗[K] K₁))
  let eQuot :
      ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K]
        ((L ⊗[K] K₁) ⧸ (⊥ : Ideal (L ⊗[K] K₁))) :=
    Ideal.quotientEquivAlgOfEq K hnil
  let eBot :
      ((L ⊗[K] K₁) ⧸ (⊥ : Ideal (L ⊗[K] K₁))) ≃ₐ[K] (L ⊗[K] K₁) :=
    AlgEquiv.ofRingEquiv (RingEquiv.quotientBot (L ⊗[K] K₁)) (fun x ↦ rfl)
  -- Compose the quotient-by-nilradical identification with the standard quotient-by-zero
  -- equivalence.
  exact eQuot.trans eBot

/-- Helper for Example 15.116.2: after separable base change, the normalization over the reduced
tensor quotient identifies with the normalization over the tensor field. -/
private noncomputable theorem reduced_tensor_integralClosure_equiv_tensor_integralClosure_of_isSeparable
    [Algebra.IsSeparable K K₁] :
    integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
      integralClosure B (L ⊗[K] K₁) := by
  let eTensor :
      ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B] (L ⊗[K] K₁) :=
    (reduced_tensor_equiv_tensor_of_isSeparable (k := k) (p := p) (K₁ := K₁)).restrictScalars B
  -- Transport integral closures along the global reduced-quotient collapse before localizing.
  exact AlgEquiv.mapIntegralClosure eTensor

/-- Helper for Example 15.116.2: localizing at a prime ideal commutes with transport across a ring
equivalence, provided the target prime is the image ideal. -/
private noncomputable theorem localization_atPrime_ringEquiv_of_map_prime
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal R) [q.IsPrime] :
    Localization.AtPrime q ≃+* Localization.AtPrime (Ideal.map e.toRingHom q) := by
  have hPrimeCompl :
      Submonoid.map e.toMonoidHom q.primeCompl =
        (Ideal.map e.toRingHom q).primeCompl := by
    -- The prime complement is transported exactly by the ring equivalence on the ambient ring.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hy
      rcases hy with ⟨z, hz, hzx⟩
      exact hx (e.injective hzx ▸ hz)
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      intro hx
      exact hy (Ideal.mem_map_of_mem e.toRingHom hx)
  -- Once the prime complements agree, the universal property of localization supplies the
  -- canonical ring equivalence.
  exact
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime q)
      (Localization.AtPrime (Ideal.map e.toRingHom q))
      e hPrimeCompl

/-- Helper for Example 15.116.2: maximality of an ideal is preserved under a ring equivalence. -/
private theorem ideal_map_isMaximal_of_ringEquiv
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal R) [q.IsMaximal] :
    (Ideal.map e.toRingHom q).IsMaximal := by
  -- Map maximality through the surjective equivalence map, using that equivalences have zero
  -- kernel.
  refine Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := e.toRingHom) e.surjective ?_
  simpa using (show RingHom.ker e.toRingHom ≤ q from by simp)

/-- Helper for Example 15.116.2: contracting an ideal after transporting it across a ring
equivalence agrees with contracting the original ideal, provided the base maps intertwine through
the equivalence. -/
private theorem ideal_map_comap_eq_of_ringEquiv_comp
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : R →+* T) (e : S ≃+* T)
    (he : e.toRingHom.comp f = g) (q : Ideal S) :
    (Ideal.map e.toRingHom q).comap g = q.comap f := by
  ext x
  -- Rewrite the target contraction through `e`; surjectivity of the equivalence then turns
  -- membership in the mapped ideal into membership in the original ideal.
  rw [Ideal.mem_comap, ← he, RingHom.comp_apply]
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact e.injective hyx ▸ hy
  · intro hx
    exact ⟨f x, hx, rfl⟩

/-- Helper for Example 15.116.2: if a prime of the source ring lies over `p`, then its image
under a compatible ring equivalence also lies over `p`. -/
private theorem ideal_map_liesOver_of_ringEquiv
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (e : S ≃+* T)
    (he : e.toRingHom.comp (algebraMap R S) = algebraMap R T)
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] :
    (Ideal.map e.toRingHom q).LiesOver p := by
  -- Compare contractions through the equivalence first, then reuse the original lies-over
  -- equality for `q`.
  rw [Ideal.liesOver_iff]
  simpa [Ideal.liesOver_iff] using
    (ideal_map_comap_eq_of_ringEquiv_comp
      (f := algebraMap R S) (g := algebraMap R T) e he q).trans (q.over_def p)

/-- Helper for Example 15.116.2: a residue-field extension that is both purely inseparable and
separable has residue degree `1`. -/
private theorem residueDegree_eq_one_of_purelyInseparable_and_separable
    {R : Type*} {S : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [IsExtensionOfDiscreteValuationRings R S]
    (hpi : IsPurelyInseparable (ResidueField R) (ResidueField S))
    (hsep : Algebra.IsSeparable (ResidueField R) (ResidueField S)) :
    residueDegree R S = 1 := by
  have hfinSep_one : Field.finSepDegree (ResidueField R) (ResidueField S) = 1 := by
    -- Purely inseparable extensions have separable degree `1`.
    rw [Field.isPurelyInseparable_iff_finSepDegree_eq_one]
    exact hpi
  have hsep_eq :
      Field.finSepDegree (ResidueField R) (ResidueField S) =
        Module.finrank (ResidueField R) (ResidueField S) := by
    -- For separable extensions, the separable degree is the full vector-space dimension.
    exact (Field.finSepDegree_eq_finrank_iff (ResidueField R) (ResidueField S)).2 hsep
  -- Replace residue degree by the residue-field dimension, then compare with the separable degree.
  calc
    residueDegree R S = Module.finrank (ResidueField R) (ResidueField S) :=
      residueDegree_eq_finrank (A := R) (B := S)
    _ = 1 := by rw [← hsep_eq, hfinSep_one]

/-- Helper for Example 15.116.2: a ring equivalence between local rings carries the maximal ideal
to the maximal ideal. -/
private theorem ringEquiv_map_maximalIdeal_eq
    {R : Type*} {S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) :
    Ideal.map e.toRingHom (maximalIdeal R) = maximalIdeal S := by
  -- Compare membership through the equivalence, rewriting both maximal ideals as the nonunits.
  ext x
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    simpa using hx

/-- Helper for Example 15.116.2: transporting a DVR branch through a codomain ring equivalence
does not change the ramification index. -/
private theorem ramificationIndex_eq_of_ringEquiv_codomain
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra R S] [Algebra R T]
    [IsExtensionOfDiscreteValuationRings R S]
    [IsExtensionOfDiscreteValuationRings R T]
    (e : S ≃+* T)
    (he : e.toRingHom.comp (algebraMap R S) = algebraMap R T) :
    ramificationIndex R T = ramificationIndex R S := by
  have hramS :
      Ideal.map (algebraMap R S) (maximalIdeal R) =
        maximalIdeal S ^ ramificationIndex R S :=
    (ramificationIndex_eq_iff (A := R) (B := S) (ramificationIndex R S)).mp rfl |>.2
  have hramT :
      Ideal.map (algebraMap R T) (maximalIdeal R) =
        maximalIdeal T ^ ramificationIndex R S := by
    -- Rewrite the target branch map through the equivalence, then transport the defining
    -- maximal-ideal equality for the source branch.
    calc
      Ideal.map (algebraMap R T) (maximalIdeal R) =
          Ideal.map (e.toRingHom.comp (algebraMap R S)) (maximalIdeal R) := by
            rw [← he]
      _ = Ideal.map e.toRingHom (Ideal.map (algebraMap R S) (maximalIdeal R)) := by
            rw [Ideal.map_map]
      _ = Ideal.map e.toRingHom (maximalIdeal S ^ ramificationIndex R S) := by
            rw [hramS]
      _ = (Ideal.map e.toRingHom (maximalIdeal S)) ^ ramificationIndex R S := by
            rw [Ideal.map_pow]
      _ = maximalIdeal T ^ ramificationIndex R S := by
            rw [ringEquiv_map_maximalIdeal_eq (e := e)]
  -- Repackage the transported maximal-ideal identity as the ramification-index equality.
  exact
    (ramificationIndex_eq_iff (A := R) (B := T) (ramificationIndex R S)).mpr
      ⟨(ramificationIndex_eq_iff (A := R) (B := S) (ramificationIndex R S)).mp rfl |>.1, hramT⟩

/-- Helper for Example 15.116.2: transporting a maximal branch ideal across the reduced/tensor
normalization equivalence preserves maximality. -/
private theorem localized_tensor_branch_isMaximal_of_isSeparable
    [Algebra.IsSeparable K K₁]
    (n : Ideal (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
    [n.IsMaximal] :
    let eClosure :
        integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
          integralClosure B (L ⊗[K] K₁) :=
      reduced_tensor_integralClosure_equiv_tensor_integralClosure_of_isSeparable
        (k := k) (p := p) (K₁ := K₁)
    let nTensor : Ideal (integralClosure B (L ⊗[K] K₁)) :=
      Ideal.map eClosure.toRingHom n
    nTensor.IsMaximal := by
  let eClosure :
      integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
        integralClosure B (L ⊗[K] K₁) :=
    reduced_tensor_integralClosure_equiv_tensor_integralClosure_of_isSeparable
      (k := k) (p := p) (K₁ := K₁)
  let nTensor : Ideal (integralClosure B (L ⊗[K] K₁)) :=
    Ideal.map eClosure.toRingHom n
  -- Transport maximality first, so the remaining blocker is only the localization-map comparison.
  simpa [nTensor] using
    (ideal_map_isMaximal_of_ringEquiv eClosure.toRingEquiv n)

/-- Helper for Example 15.116.2: the localization equivalence induced by
`mapIntegralClosure` conjugates the original branch map to the transported tensor branch map. -/
private theorem mapIntegralClosure_localization_localRingHom_conjugation
    [Algebra.IsSeparable K K₁]
    (m : Ideal (integralClosure A K₁)) [m.IsMaximal]
    (n : Ideal (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
    [n.IsMaximal] [n.LiesOver m] :
    let eClosure :
        integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
          integralClosure B (L ⊗[K] K₁) :=
      reduced_tensor_integralClosure_equiv_tensor_integralClosure_of_isSeparable
        (k := k) (p := p) (K₁ := K₁)
    let nTensor : Ideal (integralClosure B (L ⊗[K] K₁)) :=
      Ideal.map eClosure.toRingHom n
    let eLoc :
        Localization.AtPrime n ≃+* Localization.AtPrime nTensor :=
      localization_atPrime_ringEquiv_of_map_prime eClosure.toRingEquiv n
    eLoc.toRingHom.comp
        (Localization.localRingHom m n
          (algebraMap (integralClosure A K₁)
            (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
          (n.over_def m)) =
      Localization.localRingHom m nTensor
        (algebraMap (integralClosure A K₁)
          (integralClosure B (L ⊗[K] K₁)))
        (nTensor.over_def m) := by
  let eClosure :
      integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
        integralClosure B (L ⊗[K] K₁) :=
    reduced_tensor_integralClosure_equiv_tensor_integralClosure_of_isSeparable
      (k := k) (p := p) (K₁ := K₁)
  let eClosureA :
      integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[integralClosure A K₁]
        integralClosure B (L ⊗[K] K₁) :=
    eClosure.restrictScalars (integralClosure A K₁)
  let nTensor : Ideal (integralClosure B (L ⊗[K] K₁)) :=
    Ideal.map eClosure.toRingHom n
  have hnTensor_over : nTensor.LiesOver m := by
    -- Transport the lies-over relation through the normalization equivalence before localizing.
    exact
      ideal_map_liesOver_of_ringEquiv
        (R := integralClosure A K₁)
        (S := integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
        (T := integralClosure B (L ⊗[K] K₁))
        eClosure.toRingEquiv
        (by
          ext x
          simpa [eClosureA] using eClosureA.commutes x)
        m n
  let eLoc :
      Localization.AtPrime n ≃+* Localization.AtPrime nTensor :=
    localization_atPrime_ringEquiv_of_map_prime eClosure.toRingEquiv n
  -- Both localized branch maps are the unique local maps induced by the same normalized composite.
  refine Localization.localRingHom_unique
    m nTensor
    (algebraMap (integralClosure A K₁)
      (integralClosure B (L ⊗[K] K₁)))
    (nTensor.over_def m) fun x ↦ ?_
  simp only [eLoc, RingHom.comp_apply, Localization.localRingHom_to_map]
  simpa [eClosureA] using eClosureA.commutes x

/-- Helper for Example 15.116.2: after transporting to the tensor-field branch, the localized map
sends the downstairs maximal ideal to the `p`th power of the upstairs maximal ideal. -/
private theorem localized_tensor_branch_ramificationIndex_eq_p_of_isSeparable
    [Algebra.IsSeparable K K₁]
    (m : Ideal (integralClosure A K₁)) [m.IsMaximal]
    (nTensor : Ideal (integralClosure B (L ⊗[K] K₁)))
    [nTensor.IsMaximal] [nTensor.LiesOver m] :
    ramificationIndex (Localization.AtPrime m) (Localization.AtPrime nTensor) = p := by
  -- TODO: transport the tensor branch to the explicit `AdjoinRoot (X ^ p - C x)` model, compare
  -- the localized normalization with the canonical radical extension over the localized DVR, and
  -- then invoke the owner ramification computation there.
  sorry

/-- Helper for Example 15.116.2: after transporting to the tensor-field branch, the localized map
sends the downstairs maximal ideal to the `p`th power of the upstairs maximal ideal. -/
private theorem localized_tensor_branch_map_maximalIdeal_eq_pow_of_isSeparable
    [Algebra.IsSeparable K K₁]
    (m : Ideal (integralClosure A K₁)) [m.IsMaximal]
    (nTensor : Ideal (integralClosure B (L ⊗[K] K₁)))
    [nTensor.IsMaximal] [nTensor.LiesOver m] :
    Ideal.map
        (Localization.localRingHom m nTensor
          (algebraMap (integralClosure A K₁)
            (integralClosure B (L ⊗[K] K₁)))
          (nTensor.over_def m))
        (maximalIdeal (Localization.AtPrime m)) =
      maximalIdeal (Localization.AtPrime nTensor) ^ p := by
  -- Route correction: keep the ideal identity as a thin adapter, so the arithmetic blocker stays
  -- on the ramification-index statement where the owner API is naturally phrased.
  exact
    (ramificationIndex_eq_iff
      (A := Localization.AtPrime m) (B := Localization.AtPrime nTensor) p).mp
      (localized_tensor_branch_ramificationIndex_eq_p_of_isSeparable
        (k := k) (p := p) (K₁ := K₁) m nTensor) |>.2

/-- Helper for Example 15.116.2: every localized branch after separable base change still has
ramification index exactly `p`. -/
private theorem localized_branch_ramificationIndex_eq_p_of_isSeparable
    [Algebra.IsSeparable K K₁]
    (m : Ideal (integralClosure A K₁)) [m.IsMaximal]
    (n : Ideal (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
    [n.IsMaximal] [n.LiesOver m] :
    ramificationIndex (Localization.AtPrime m) (Localization.AtPrime n) = p := by
  -- Route correction: isolate the branchwise ramification computation before constructing the bad
  -- branch witness used in the weak-solution contradiction.
  let eRed :
      ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K] (L ⊗[K] K₁) :=
    reduced_tensor_equiv_tensor_of_isSeparable (k := k) (p := p) (K₁ := K₁)
  let eClosure :
      integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
        integralClosure B (L ⊗[K] K₁) :=
    reduced_tensor_integralClosure_equiv_tensor_integralClosure_of_isSeparable
      (k := k) (p := p) (K₁ := K₁)
  let nTensor : Ideal (integralClosure B (L ⊗[K] K₁)) :=
    Ideal.map eClosure.toRingHom n
  have hnTensor_max : nTensor.IsMaximal := by
    -- Move the chosen branch ideal across the normalization equivalence before localizing.
    simpa [eClosure, nTensor] using
      localized_tensor_branch_isMaximal_of_isSeparable
        (k := k) (p := p) (K₁ := K₁) n
  let eLoc :
      Localization.AtPrime n ≃+* Localization.AtPrime nTensor :=
    localization_atPrime_ringEquiv_of_map_prime eClosure.toRingEquiv n
  have hcomp :
      eLoc.toRingHom.comp
          (Localization.localRingHom m n
            (algebraMap (integralClosure A K₁)
              (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
            (n.over_def m)) =
        Localization.localRingHom m nTensor
          (algebraMap (integralClosure A K₁)
            (integralClosure B (L ⊗[K] K₁)))
          (nTensor.over_def m) :=
    mapIntegralClosure_localization_localRingHom_conjugation
      (k := k) (p := p) (K₁ := K₁) m n
  have hnTensor_over : nTensor.LiesOver m := by
    -- The transported tensor branch still lies over the chosen maximal ideal downstairs.
    exact
      ideal_map_liesOver_of_ringEquiv
        (R := integralClosure A K₁)
        (S := integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
        (T := integralClosure B (L ⊗[K] K₁))
        eClosure.toRingEquiv
        (by
          ext x
          simpa [eClosure.restrictScalars (integralClosure A K₁)] using
            (eClosure.restrictScalars (integralClosure A K₁)).commutes x)
        m n
  letI : nTensor.IsMaximal := hnTensor_max
  letI : nTensor.LiesOver m := hnTensor_over
  have hramTensor :
      ramificationIndex (Localization.AtPrime m) (Localization.AtPrime nTensor) = p :=
    localized_tensor_branch_ramificationIndex_eq_p_of_isSeparable
      (k := k) (p := p) (K₁ := K₁) m nTensor
  have hramTransport :
      ramificationIndex (Localization.AtPrime m) (Localization.AtPrime nTensor) =
        ramificationIndex (Localization.AtPrime m) (Localization.AtPrime n) :=
    ramificationIndex_eq_of_ringEquiv_codomain
      (R := Localization.AtPrime m)
      (S := Localization.AtPrime n)
      (T := Localization.AtPrime nTensor)
      eLoc hcomp
  -- Transport the ramification computation across the localization equivalence, so the only
  -- remaining arithmetic is the tensor-branch computation isolated above.
  calc
    ramificationIndex (Localization.AtPrime m) (Localization.AtPrime n) =
        ramificationIndex (Localization.AtPrime m) (Localization.AtPrime nTensor) :=
          hramTransport.symm
    _ = p := hramTensor

/-- Helper for Example 15.116.2: after a separable base change, each localized branch still fails
the weakly-unramified maximal-ideal test. -/
private theorem localized_branch_map_maximalIdeal_ne_of_isSeparable
    [Algebra.IsSeparable K K₁]
    (m : Ideal (integralClosure A K₁)) [m.IsMaximal]
    (n : Ideal (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
    [n.IsMaximal] [n.LiesOver m] :
    Ideal.map
        (Localization.localRingHom m n
          (algebraMap (integralClosure A K₁)
            (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
          (n.over_def m))
        (maximalIdeal (Localization.AtPrime m)) ≠
      maximalIdeal (Localization.AtPrime n) := by
  letI : Algebra (Localization.AtPrime m) (Localization.AtPrime n) :=
    (Localization.localRingHom m n
      (algebraMap (integralClosure A K₁)
        (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
      (n.over_def m)).toAlgebra
  letI :
      IsExtensionOfDiscreteValuationRings (Localization.AtPrime m) (Localization.AtPrime n) :=
    isExtensionOfDiscreteValuationRings_localizationBranch m n
  -- Consume the branchwise ramification computation only in the exact weak-solution contradiction
  -- shape needed downstream.
  simpa using
    (map_maximalIdeal_ne_of_ramificationIndex_eq_prime
      (R := Localization.AtPrime m) (S := Localization.AtPrime n)
      (localized_branch_ramificationIndex_eq_p_of_isSeparable (K₁ := K₁) m n))

/-- Helper for Example 15.116.2: under a separable base change, some localized branch of the
canonical `p`th-root extension still has nontrivial ramification, so it cannot satisfy the
maximal-ideal equality of a weak solution. -/
private theorem exists_bad_branch_of_isSeparable
    [Algebra.IsSeparable K K₁] :
    ∃ p : Ideal (integralClosure A K₁), p.IsMaximal ∧
      ∃ q : Ideal (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))),
        q.IsMaximal ∧ q.LiesOver p ∧
          Ideal.map
              (Localization.localRingHom p q
                (algebraMap (integralClosure A K₁)
                  (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
                (q.over_def p))
              (maximalIdeal (Localization.AtPrime p)) ≠
            maximalIdeal (Localization.AtPrime q) := by
  classical
  -- Choose a maximal ideal downstairs in the integral closure over `K₁`.
  obtain ⟨p, hp⟩ := Ideal.exists_maximal (integralClosure A K₁)
  let pSpec : PrimeSpectrum (integralClosure A K₁) := ⟨p, hp.isPrime⟩
  -- Lift that maximal point to the reduced tensor-product integral closure.
  obtain ⟨qSpec, hqSpec⟩ :=
    primeSpectrumComap_surjective_of_reducedTensorBaseChangeIntegralClosure
      (A := A) (K := K) (K1 := K₁) (B := B) (L := L) pSpec
  let q : Ideal (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))) := qSpec.asIdeal
  have hq_over :
      q.LiesOver p := by
    -- Convert the spectrum-level lift into the ideal-theoretic lies-over statement.
    rw [Ideal.liesOver_iff]
    exact
      (PrimeSpectrum.comap_asIdeal
        (algebraMap (integralClosure A K₁)
          (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))) qSpec).trans
        (congrArg PrimeSpectrum.asIdeal hqSpec)
  have hq : q.IsMaximal := by
    -- Integral lying-over upgrades the lifted prime over a maximal ideal to a maximal ideal.
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q ((Ideal.liesOver_iff _ _).mp hq_over)
  letI : p.IsMaximal := hp
  letI : q.IsMaximal := hq
  letI : q.LiesOver p := hq_over
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q
      (algebraMap (integralClosure A K₁)
        (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
      (q.over_def p)).toAlgebra
  letI :
      IsExtensionOfDiscreteValuationRings (Localization.AtPrime p) (Localization.AtPrime q) :=
    isExtensionOfDiscreteValuationRings_localizationBranch p q
  refine ⟨p, hp, q, hq, hq_over, ?_⟩
  -- The remaining separable-side input is now isolated in the direct bad-branch inequality.
  exact localized_branch_map_maximalIdeal_ne_of_isSeparable (K₁ := K₁) p q

/-- Helper for Example 15.116.2: if `AdjoinRoot (X^p - C a)` is not reduced, then `a` already has
a `p`th root in the ground field. -/
private theorem exists_pth_root_of_not_isReduced_adjoinRoot_pth_power
    (a : K₁) (hred : ¬ IsReduced (AdjoinRoot (X ^ p - C a : Polynomial K₁))) :
    ∃ y : K₁, y ^ p = a := by
  -- Contrapositively, if `a` has no `p`th root then `X ^ p - C a` is irreducible.
  by_contra hnot
  push_neg at hnot
  have hirr : Irreducible (X ^ p - C a : Polynomial K₁) :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p) hnot
  letI : Fact (Irreducible (X ^ p - C a : Polynomial K₁)) := ⟨hirr⟩
  -- The quotient by an irreducible polynomial over a field is again a field, hence reduced.
  exact hred inferInstance

/-- Helper for Example 15.116.2: after choosing a `p`th root `y` of `a`, the defining polynomial
rewrites as a pure `p`th power. -/
private theorem X_pow_sub_C_eq_sub_C_pow_of_pth_root
    {a y : K₁} (hy : y ^ p = a) :
    (X ^ p - C a : Polynomial K₁) = (X - C y) ^ p := by
  -- In characteristic `p`, Frobenius kills the mixed binomial terms.
  calc
    (X ^ p - C a : Polynomial K₁) = X ^ p - (C y) ^ p := by
      simp [hy]
    _ = (X - C y) ^ p := by
      rw [sub_pow_char]

/-- Helper for Example 15.116.2: after adjoining a chosen `p`th root, the reduced Kummer quotient
collapses back to the base field. -/
private noncomputable theorem reduced_adjoinRoot_equiv_baseField_of_pth_root
    {a y : K₁} (hy : y ^ p = a) :
    ((AdjoinRoot (X ^ p - C a : Polynomial K₁)) ⧸
      nilradical (AdjoinRoot (X ^ p - C a : Polynomial K₁))) ≃ₐ[K₁] K₁ := by
  let f : Polynomial K₁ := X ^ p - C a
  let φ : AdjoinRoot f →ₐ[K₁] K₁ :=
    AdjoinRoot.liftAlgHom f (AlgHom.id K₁ K₁) y (by
      -- Evaluating the defining polynomial at the chosen root kills it.
      change eval y f = 0
      simp [f, hy])
  have hker_eq : RingHom.ker φ.toRingHom = nilradical (AdjoinRoot f) := by
    apply le_antisymm
    · intro z hz
      rw [mem_nilradical]
      -- An element in the evaluation kernel is divisible by `X - C y`, hence nilpotent modulo
      -- `(X - C y)^p = X^p - C a`.
      revert hz
      refine AdjoinRoot.induction_on (f := f) (x := z) ?_
      intro P hP
      rw [RingHom.mem_ker] at hP
      have hroot : P.IsRoot y := by
        change eval y P = 0
        simpa [φ, f] using hP
      obtain ⟨Q, hQ⟩ := (Polynomial.dvd_iff_isRoot).2 hroot
      refine ⟨p, ?_⟩
      rw [show ((AdjoinRoot.mk f) P) ^ p = (AdjoinRoot.mk f) (P ^ p) by
        rw [map_pow]]
      rw [hQ, mul_pow]
      have hf : f = (X - C y) ^ p := by
        -- Rewrite the Kummer polynomial as the pure `p`th power from the chosen root.
        calc
          f = X ^ p - C (y ^ p) := by
            simp [f, hy]
          _ = X ^ p - (C y) ^ p := by
            rw [Polynomial.C_pow]
          _ = (X - C y) ^ p := by
            rw [sub_pow_char]
      rw [AdjoinRoot.mk_eq_zero]
      exact ⟨Q ^ p, by rw [hf]⟩
    · intro z hz
      rw [mem_nilradical] at hz
      rcases hz with ⟨n, hn⟩
      -- Nilpotents always map to zero in the field `K₁`.
      rw [RingHom.mem_ker]
      have hphi_pow : φ z ^ n = 0 := by
        simpa [map_pow] using congrArg φ hn
      exact eq_zero_of_pow_eq_zero hphi_pow
  let ψ : (AdjoinRoot f ⧸ nilradical (AdjoinRoot f)) →ₐ[K₁] K₁ :=
    Ideal.Quotient.liftₐ (R₁ := K₁) (I := nilradical (AdjoinRoot f)) φ <| by
      intro z hz
      have hz' : z ∈ RingHom.ker φ.toRingHom := by
        rw [hker_eq]
        exact hz
      exact RingHom.mem_ker.mp hz'
  have hψbij : Function.Bijective ψ := by
    refine ⟨?_, ?_⟩
    · intro u v huv
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective v
      -- Equality after evaluation means the representatives differ by an element of the
      -- nilradical, so they define the same quotient class.
      rw [Ideal.Quotient.eq]
      have hab : φ a = φ b := by
        simpa [ψ] using huv
      have hsub : φ (a - b) = 0 := by
        simpa [map_sub] using sub_eq_zero.mpr hab
      have hker : a - b ∈ RingHom.ker φ.toRingHom := RingHom.mem_ker.mpr hsub
      rw [hker_eq] at hker
      exact hker
    · intro z
      -- Surjectivity is immediate because the quotient still contains the constant classes.
      refine ⟨Ideal.Quotient.mkₐ K₁ (nilradical (AdjoinRoot f))
        (algebraMap K₁ (AdjoinRoot f) z), ?_⟩
      simpa [ψ] using φ.commutes z
  exact AlgEquiv.ofBijective ψ hψbij

/-- Helper for Example 15.116.2: ring equivalences transport the nilradical exactly to the
nilradical of the target ring. -/
private theorem ideal_map_nilradical_of_ringEquiv
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Ideal.map e.toRingHom (nilradical R) = nilradical S := by
  ext y
  constructor
  · intro hy
    rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [mem_nilradical] at hx ⊢
    rcases hx with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [map_pow] using congrArg e hn
  · intro hy
    have hpre : e.symm y ∈ nilradical R := by
      rw [mem_nilradical] at hy ⊢
      rcases hy with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      apply e.injective
      simpa [map_pow] using hn
    exact Ideal.mem_map_of_mem e.toRingHom hpre

/-- Helper for Example 15.116.2: once `x` becomes a `p`th power in `K₁`, the reduced tensor
product itself already identifies with `K₁`. -/
private noncomputable theorem reduced_tensor_pth_root_equiv_baseField_of_uniformizer_pth_root
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K)) :
    ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K] K₁ := by
  let eTensor :
      L ⊗[K] K₁ ≃ₐ[K]
        AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) :=
    tensor_powerSeries_pth_root_equiv_adjoinRoot (k := k) (p := p) (K₁ := K₁)
  have hnil :
      nilradical (AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)) =
        Ideal.map eTensor.toRingHom (nilradical (L ⊗[K] K₁)) := by
    -- Transport the nilradical across the explicit tensor/`AdjoinRoot` comparison before
    -- passing to the reduced quotient.
    symm
    exact ideal_map_nilradical_of_ringEquiv eTensor.toRingEquiv
  let eQuot :
      ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K]
        ((AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)) ⧸
          nilradical (AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁))) :=
    Ideal.quotientEquivAlg
      (nilradical (L ⊗[K] K₁))
      (nilradical (AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)))
      eTensor hnil
  let eBase :
      ((AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)) ⧸
        nilradical (AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁))) ≃ₐ[K]
        K₁ :=
    (reduced_adjoinRoot_equiv_baseField_of_pth_root
      (K₁ := K₁) (a := algebraMap K K₁ (π : K)) hy).restrictScalars K
  -- Compose the explicit tensor/`AdjoinRoot` reduced-quotient comparison with the base-field
  -- collapse coming from the chosen `p`th root.
  exact eQuot.trans eBase

/-- Helper for Example 15.116.2: a chosen `p`th root of `x` in `K₁` kills the defining polynomial
of the explicit ring extension `A[x^(1/p)]`. -/
private theorem uniformizerRootPolynomial_eval_eq_zero_of_pth_root
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K)) :
    Polynomial.eval y (uniformizerRootPolynomial π p) = 0 := by
  have hyA : y ^ p = algebraMap A K₁ π := by
    simpa using hy
  -- Rewrite the defining polynomial evaluation to the displayed `p`th-power relation.
  rw [uniformizerRootPolynomial, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]
  exact sub_eq_zero.mpr hyA

/-- Helper for Example 15.116.2: a chosen `p`th root of `x` equips `K₁` with the expected
`A[x^(1/p)]`-algebra structure. -/
private noncomputable def uniformizerRootExtensionRing_to_baseField_of_uniformizer_pth_root
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K)) :
    B →ₐ[A] K₁ :=
  AdjoinRoot.liftAlgHom
    (uniformizerRootPolynomial π p)
    (algebraMap A K₁)
    y
    (uniformizerRootPolynomial_eval_eq_zero_of_pth_root
      (k := k) (p := p) (K₁ := K₁) hy)

/-- Helper for Example 15.116.2: the induced `A[x^(1/p)] → K₁` map lands in the integral closure
of `A` inside `K₁`. -/
private theorem uniformizerRootExtensionRing_to_integralClosure_mem_of_pth_root
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K)) (b : B) :
    uniformizerRootExtensionRing_to_baseField_of_uniformizer_pth_root
        (k := k) (p := p) (K₁ := K₁) hy b ∈ integralClosure A K₁ := by
  let _ : Algebra.IsIntegral A B := inferInstance
  have hbA : IsIntegral A b := Algebra.IsIntegral.isIntegral (R := A) b
  have himage :
      IsIntegral A
        (uniformizerRootExtensionRing_to_baseField_of_uniformizer_pth_root
          (k := k) (p := p) (K₁ := K₁) hy b) := by
    exact
      IsIntegral.map
        (uniformizerRootExtensionRing_to_baseField_of_uniformizer_pth_root
          (k := k) (p := p) (K₁ := K₁) hy)
        hbA
  simpa using himage

/-- Helper for Example 15.116.2: a chosen `p`th root of `x` in `K₁` induces the expected
`K[x^(1/p)] → K₁` map on fraction fields. -/
private noncomputable def powerSeries_pth_root_to_baseField_of_uniformizer_pth_root
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K)) :
    L →ₐ[K] K₁ :=
  AdjoinRoot.liftAlgHom
    (uniformizerRootFractionPolynomial π p)
    (algebraMap K K₁)
    y
    (by
      -- Evaluating `X ^ p - x` at the chosen `p`th root kills the defining polynomial.
      simpa [uniformizerRootFractionPolynomial, uniformizerRootPolynomial] using
        (show Polynomial.eval y (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁) = 0 by
          rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
          exact sub_eq_zero.mpr hy))

/-- Helper for Example 15.116.2: the fraction-field comparison sends the distinguished root to the
chosen `p`th root in `K₁`. -/
private theorem powerSeries_pth_root_to_baseField_of_uniformizer_pth_root_root
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K)) :
    powerSeries_pth_root_to_baseField_of_uniformizer_pth_root
        (k := k) (p := p) (K₁ := K₁) hy (uniformizerRoot π p) =
      y := by
  -- This is the defining generator formula of `AdjoinRoot.liftAlgHom`.
  simp [powerSeries_pth_root_to_baseField_of_uniformizer_pth_root, AdjoinRoot.liftAlgHom_root]

/-- Helper for Example 15.116.2: the chosen field-level map restricts to the expected
`A[x^(1/p)] → K₁` map on the explicit ring extension. -/
private theorem powerSeries_pth_root_to_baseField_comp_uniformizerRootExtensionRing_algebraMap
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K)) :
    ((powerSeries_pth_root_to_baseField_of_uniformizer_pth_root
          (k := k) (p := p) (K₁ := K₁) hy).restrictScalars A).comp
        (algebraMap B L : B →ₐ[A] L) =
      uniformizerRootExtensionRing_to_baseField_of_uniformizer_pth_root
        (k := k) (p := p) (K₁ := K₁) hy := by
  -- Both `A`-algebra maps out of `B = A[x^(1/p)]` are determined by the image of the adjoined
  -- root, so compare only that generator.
  apply AdjoinRoot.algHom_ext
  change
    powerSeries_pth_root_to_baseField_of_uniformizer_pth_root
        (k := k) (p := p) (K₁ := K₁) hy
        (algebraMap B L (AdjoinRoot.root (uniformizerRootPolynomial π p))) =
      y
  rw [powerSeries_pth_root_to_baseField_of_uniformizer_pth_root_root]
  simp

/-- Helper for Example 15.116.2: the chosen `A[x^(1/p)] → integralClosure A K₁` map is the
codomain-restricted version of the corresponding field map. -/
private noncomputable def uniformizerRootExtensionRing_to_integralClosure_of_uniformizer_pth_root
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K)) :
    B →ₐ[A] integralClosure A K₁ :=
  AlgHom.codRestrict
    (uniformizerRootExtensionRing_to_baseField_of_uniformizer_pth_root
      (k := k) (p := p) (K₁ := K₁) hy)
    (integralClosure A K₁)
    (uniformizerRootExtensionRing_to_integralClosure_mem_of_pth_root
      (k := k) (p := p) (K₁ := K₁) hy)

/-- Helper for Example 15.116.2: the chosen `A[x^(1/p)] → integralClosure A K₁` map is
injective. -/
private theorem uniformizerRootExtensionRing_to_integralClosure_of_uniformizer_pth_root_injective
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K)) :
    Function.Injective
      (uniformizerRootExtensionRing_to_integralClosure_of_uniformizer_pth_root
        (k := k) (p := p) (K₁ := K₁) hy) := by
  intro b₁ b₂ h
  have hbase :
      uniformizerRootExtensionRing_to_baseField_of_uniformizer_pth_root
          (k := k) (p := p) (K₁ := K₁) hy b₁ =
        uniformizerRootExtensionRing_to_baseField_of_uniformizer_pth_root
          (k := k) (p := p) (K₁ := K₁) hy b₂ := by
    -- Forget the codomain restriction to compare in the ambient field `K₁`.
    exact congrArg (algebraMap (integralClosure A K₁) K₁) h
  have hcomp :
      ((powerSeries_pth_root_to_baseField_of_uniformizer_pth_root
            (k := k) (p := p) (K₁ := K₁) hy).restrictScalars A).comp
          (algebraMap B L : B →ₐ[A] L) =
        uniformizerRootExtensionRing_to_baseField_of_uniformizer_pth_root
          (k := k) (p := p) (K₁ := K₁) hy :=
    powerSeries_pth_root_to_baseField_comp_uniformizerRootExtensionRing_algebraMap
      (k := k) (p := p) (K₁ := K₁) hy
  have hL :
      algebraMap B L b₁ = algebraMap B L b₂ := by
    -- After identifying the ring map with the restricted field map, injectivity comes from the
    -- field-hom target.
    apply (powerSeries_pth_root_to_baseField_of_uniformizer_pth_root
      (k := k) (p := p) (K₁ := K₁) hy).injective
    simpa [hcomp] using hbase
  exact IsFractionRing.injective B L hL

/-- Helper for Example 15.116.2: once `x` becomes a `p`th power in `K₁`, the integral closure of
`B = A[x^(1/p)]` inside `K₁` is already `integralClosure A K₁`. -/
private theorem uniformizerRoot_extension_integralClosure_equiv_base
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K)) :
    integralClosure B K₁ ≃ₐ[B] integralClosure A K₁ := by
  letI : Algebra B (integralClosure A K₁) :=
    (uniformizerRootExtensionRing_to_integralClosure_of_uniformizer_pth_root
      (k := k) (p := p) (K₁ := K₁) hy).toAlgebra
  letI : IsScalarTower A B (integralClosure A K₁) := by
    -- Both `A`-actions on the target are induced by the same chosen `B`-algebra structure.
    exact IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  letI : IsIntegralClosure (integralClosure A K₁) B K₁ := by
    refine IsIntegralClosure.mk ?_ ?_
    · -- Injectivity comes from the restriction of the corresponding field map.
      exact
        uniformizerRootExtensionRing_to_integralClosure_of_uniformizer_pth_root_injective
          (k := k) (p := p) (K₁ := K₁) hy
    · intro z
      constructor
      · intro hz
        -- Integrality descends from `B` to `A` because `B / A` is integral.
        exact Algebra.IsIntegral.trans B hz
      · rintro ⟨w, rfl⟩
        -- Every element already integral over `A` remains integral over the larger ring `B`.
        exact IsIntegral.tower_top (A := A) (B := B) w.2
  -- Use the canonical uniqueness of integral closures once the induced `B`-algebra structure is
  -- installed on `integralClosure A K₁`.
  exact IsIntegralClosure.equiv B (integralClosure B K₁) K₁ (integralClosure A K₁)

/-- Helper for Example 15.116.2: once the reduced tensor product collapses to `K₁`, transporting
the chosen branch across the resulting integral-closure equivalence identifies it with the
downstairs branch and conjugates the localized branch map to the identity. -/
private theorem collapsed_branch_localRingHom_eq_id_of_uniformizer_pth_root
    {y : K₁} (hy : y ^ p = algebraMap K K₁ (π : K))
    (m : Ideal (integralClosure A K₁)) [m.IsMaximal]
    (n : Ideal (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
    [n.IsMaximal] [n.LiesOver m] :
    let eRedBase :
        ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K] K₁ :=
      reduced_tensor_pth_root_equiv_baseField_of_uniformizer_pth_root
        (k := k) (p := p) (K₁ := K₁) hy
    let eClosure :
        integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
          integralClosure B K₁ :=
      AlgEquiv.mapIntegralClosure (eRedBase.restrictScalars B)
    let eBase :
        integralClosure B K₁ ≃ₐ[B] integralClosure A K₁ :=
      uniformizerRoot_extension_integralClosure_equiv_base
        (k := k) (p := p) (K₁ := K₁) hy
    let eTotal :
        integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
          integralClosure A K₁ :=
      eClosure.trans eBase
    let nBase : Ideal (integralClosure A K₁) :=
      Ideal.map eTotal.toRingHom n
    let eLoc :
        Localization.AtPrime n ≃+* Localization.AtPrime nBase :=
      localization_atPrime_ringEquiv_of_map_prime eTotal.toRingEquiv n
    nBase = m ∧
      eLoc.toRingHom.comp
          (Localization.localRingHom m n
            (algebraMap (integralClosure A K₁)
              (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
            (n.over_def m)) =
        RingHom.id (Localization.AtPrime m) := by
  let eRedBase :
      ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K] K₁ :=
    reduced_tensor_pth_root_equiv_baseField_of_uniformizer_pth_root
      (k := k) (p := p) (K₁ := K₁) hy
  let eClosure :
      integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
        integralClosure B K₁ :=
    AlgEquiv.mapIntegralClosure (eRedBase.restrictScalars B)
  let eBase :
      integralClosure B K₁ ≃ₐ[B] integralClosure A K₁ :=
    uniformizerRoot_extension_integralClosure_equiv_base
      (k := k) (p := p) (K₁ := K₁) hy
  let eTotal :
      integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
        integralClosure A K₁ :=
    eClosure.trans eBase
  let eTotalA :
      integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[integralClosure A K₁]
        integralClosure A K₁ :=
    eTotal.restrictScalars (integralClosure A K₁)
  let nBase : Ideal (integralClosure A K₁) :=
    Ideal.map eTotal.toRingHom n
  have hnBase_over : nBase.LiesOver m := by
    -- Transport the chosen branch through the collapse equivalence before comparing with the
    -- downstairs maximal ideal.
    exact
      ideal_map_liesOver_of_ringEquiv
        (R := integralClosure A K₁)
        (S := integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)))
        (T := integralClosure A K₁)
        eTotal.toRingEquiv
        (by
          ext x
          simpa [eTotalA] using eTotalA.commutes x)
        m n
  have hnBase_max : nBase.IsMaximal := by
    -- Maximality is preserved under the collapse equivalence.
    simpa [nBase] using ideal_map_isMaximal_of_ringEquiv eTotal.toRingEquiv n
  letI : nBase.IsMaximal := hnBase_max
  letI : nBase.LiesOver m := hnBase_over
  have hnBase_eq : nBase = m := by
    -- Both ideals are maximal in the same DVR, so each is the unique maximal ideal.
    calc
      nBase = maximalIdeal (integralClosure A K₁) := IsLocalRing.eq_maximalIdeal nBase
      _ = m := (IsLocalRing.eq_maximalIdeal m).symm
  let eLoc :
      Localization.AtPrime n ≃+* Localization.AtPrime nBase :=
    localization_atPrime_ringEquiv_of_map_prime eTotal.toRingEquiv n
  have hcomp :
      eLoc.toRingHom.comp
          (Localization.localRingHom m n
            (algebraMap (integralClosure A K₁)
              (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
            (n.over_def m)) =
        Localization.localRingHom m nBase
          (algebraMap (integralClosure A K₁) (integralClosure A K₁))
          (nBase.over_def m) := by
    -- Both localized maps are induced by the same collapsed normalization map.
    refine Localization.localRingHom_unique
      m nBase
      (algebraMap (integralClosure A K₁) (integralClosure A K₁))
      (nBase.over_def m) fun x ↦ ?_
    simp only [eLoc, RingHom.comp_apply, Localization.localRingHom_to_map]
    simpa [eTotalA] using eTotalA.commutes x
  have hid :
      Localization.localRingHom m nBase
          (algebraMap (integralClosure A K₁) (integralClosure A K₁))
          (nBase.over_def m) =
        RingHom.id (Localization.AtPrime m) := by
    -- Once the transported branch ideal is exactly `m`, the localized branch map is the identity.
    subst hnBase_eq
    refine Localization.localRingHom_unique m m (RingHom.id _) rfl fun x ↦ ?_
    simp [Localization.localRingHom_to_map]
  exact ⟨hnBase_eq, hcomp.trans hid⟩

/-- Helper for Example 15.116.2: a finite inseparable extension of `k((x))` contains a `p`th root
of the uniformizer `x`. -/
private theorem tensor_powerSeries_pth_root_not_isReduced_of_not_isSeparable
    (hK₁ : ¬ Algebra.IsSeparable K K₁) :
    ¬ IsReduced (L ⊗[K] K₁) := by
  intro hred
  let eRoot :
      L ≃ₐ[K] onePthRootExtension K p :=
    powerSeries_pth_root_equiv_onePthRootExtension (k := k) (p := p)
  let eTensor :
      L ⊗[K] K₁ ≃ₐ[K] (onePthRootExtension K p) ⊗[K] K₁ :=
    Algebra.TensorProduct.congr eRoot (AlgEquiv.refl : K₁ ≃ₐ[K] K₁)
  let eComm :
      (onePthRootExtension K p) ⊗[K] K₁ ≃ₐ[K] K₁ ⊗[K] onePthRootExtension K p :=
    Algebra.TensorProduct.comm K (onePthRootExtension K p) K₁
  letI : IsReduced ((onePthRootExtension K p) ⊗[K] K₁) :=
    -- Transport reducedness first from the explicit tensor product to the Chapter 10 tensor model.
    isReduced_of_injective eTensor.symm.toRingHom eTensor.symm.injective
  letI : IsReduced (K₁ ⊗[K] onePthRootExtension K p) :=
    -- The owner theorem is stated with the factors in the opposite order, so commute the tensor.
    isReduced_of_injective eComm.symm.toRingHom eComm.symm.injective
  have hsepOver : Algebra.IsSeparableOver K K₁ := by
    -- Apply the Chapter 10 reducedness criterion on the chosen `K^{1/p}` model.
    exact
      (isSeparableOver_iff_isReduced_tensorProduct_onePthRootExtension
        (k := K) (K := K₁) (p := p)).2 inferInstance
  -- Finite-dimensional field extensions are algebraic, so `IsSeparableOver` recovers the usual
  -- algebraic separability owner.
  exact hK₁ (Algebra.IsSeparableOver.isSeparable hsepOver)

/-- Helper for Example 15.116.2: a finite inseparable extension of `k((x))` contains a `p`th root
of the uniformizer `x`. -/
private theorem uniformizer_mem_pth_powers_of_not_isSeparable
    (hK₁ : ¬ Algebra.IsSeparable K K₁) :
    ∃ y : K₁, y ^ p = algebraMap K K₁ (π : K) := by
  have htensor :
      ¬ IsReduced (L ⊗[K] K₁) :=
    tensor_powerSeries_pth_root_not_isReduced_of_not_isSeparable (K₁ := K₁) hK₁
  have hadjoin :
      ¬ IsReduced (AdjoinRoot (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)) := by
    intro hred
    let e := tensor_powerSeries_pth_root_equiv_adjoinRoot (k := k) (p := p) (K₁ := K₁)
    have hred_tensor : IsReduced (L ⊗[K] K₁) := by
      refine ⟨?_⟩
      intro z hz
      apply e.injective
      have hnil : IsNilpotent (e z) := by
        rcases hz with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        simpa [map_pow] using congrArg e hn
      -- Reducedness is transported back through the explicit tensor/`AdjoinRoot` equivalence.
      exact IsReduced.eq_zero (R := AdjoinRoot
        (X ^ p - C (algebraMap K K₁ (π : K)) : Polynomial K₁)) (x := e z) hnil
    exact htensor hred_tensor
  -- Once the explicit Kummer quotient is known to be nonreduced, root extraction is the
  -- dedicated algebraic owner from the previous helper.
  exact
    exists_pth_root_of_not_isReduced_adjoinRoot_pth_power
      (K₁ := K₁) (algebraMap K K₁ (π : K)) hadjoin

/-- Helper for Example 15.116.2: once `x` becomes a `p`th power in `K₁`, the reduced tensor
product `(L ⊗[K] K₁)_red` collapses to `K₁`, so every localized branch is formally smooth. -/
private theorem localized_branch_formallySmooth_of_uniformizer_mem_pth_powers
    (hy : ∃ y : K₁, y ^ p = algebraMap K K₁ (π : K))
    (m : Ideal (integralClosure A K₁)) [m.IsMaximal]
    (n : Ideal (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
    [n.IsMaximal] [n.LiesOver m] :
    (Localization.localRingHom m n
      (algebraMap (integralClosure A K₁)
        (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
      (n.over_def m)).formally_smooth_for_adic
        (maximalIdeal (Localization.AtPrime n)) := by
  -- Route correction: keep the solution endgame branchwise. After collapsing the reduced Kummer
  -- quotient to `K₁`, the localized codomain should become the identity branch of the downstairs
  -- DVR, and formal smoothness follows by transport through ring equivalences.
  rcases hy with ⟨y, hy⟩
  let eRedBase :
      ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[K] K₁ :=
    reduced_tensor_pth_root_equiv_baseField_of_uniformizer_pth_root
      (k := k) (p := p) (K₁ := K₁) hy
  let eClosure :
      integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
        integralClosure B K₁ :=
    AlgEquiv.mapIntegralClosure (eRedBase.restrictScalars B)
  let eBase :
      integralClosure B K₁ ≃ₐ[B] integralClosure A K₁ :=
    uniformizerRoot_extension_integralClosure_equiv_base
      (k := k) (p := p) (K₁ := K₁) hy
  let eTotal :
      integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁)) ≃ₐ[B]
        integralClosure A K₁ :=
    eClosure.trans eBase
  let nBase : Ideal (integralClosure A K₁) :=
    Ideal.map eTotal.toRingHom n
  let eLoc :
      Localization.AtPrime n ≃+* Localization.AtPrime nBase :=
    localization_atPrime_ringEquiv_of_map_prime eTotal.toRingEquiv n
  obtain ⟨hnBase_eq, hcollapse⟩ :=
    collapsed_branch_localRingHom_eq_id_of_uniformizer_pth_root
      (k := k) (p := p) (K₁ := K₁) hy m n
  have hid_fs :
      (RingHom.id (Localization.AtPrime m)).formally_smooth_for_adic
        (maximalIdeal (Localization.AtPrime m)) := by
    -- The identity map is formally etale, hence formally smooth for the maximal-ideal-adic
    -- topology on the localized DVR branch.
    exact
      formally_smooth_for_adic_maximalIdeal_of_formallyEtale
        (A := Localization.AtPrime m) (B := Localization.AtPrime m) inferInstance
  have htransport :
      (eLoc.toRingHom.comp
        (Localization.localRingHom m n
          (algebraMap (integralClosure A K₁)
            (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
          (n.over_def m))).formally_smooth_for_adic
            (maximalIdeal (Localization.AtPrime m)) := by
    simpa [hcollapse] using hid_fs
  -- Transport formal smoothness back across the codomain equivalence and rewrite the transported
  -- branch ideal to the original maximal ideal upstairs.
  have hmap_max :
      Ideal.map eLoc.toRingHom (maximalIdeal (Localization.AtPrime n)) =
        maximalIdeal (Localization.AtPrime m) := by
    subst hnBase_eq
    simpa [eLoc] using
      congrArg maximalIdeal
        (show Localization.AtPrime nBase = Localization.AtPrime m by rfl)
  have hfinal :=
    formally_smooth_for_adic_of_codomain_ringEquiv
      (f := Localization.localRingHom m n
        (algebraMap (integralClosure A K₁)
          (integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))))
        (n.over_def m))
      (e := eLoc)
      (J := maximalIdeal (Localization.AtPrime n))
      (K := maximalIdeal (Localization.AtPrime m))
      hmap_max
      ?_
  simpa using hfinal

/-- Helper for Example 15.116.2: once `x` becomes a `p`th power in `K₁`, the reduced tensor
product `(L ⊗[K] K₁)_red` collapses to `K₁`, so every localized branch is formally smooth. -/
private theorem isSolutionFor_of_uniformizer_mem_pth_powers
    (hy : ∃ y : K₁, y ^ p = algebraMap K K₁ (π : K)) :
    IsSolutionFor A B K L K₁ := by
  intro m _ n _ _
  -- The global solution predicate is branchwise formal smoothness, so delegate to the localized
  -- collapse lemma.
  exact localized_branch_formallySmooth_of_uniformizer_mem_pth_powers (K₁ := K₁) hy m n

-- Proof sketch: if `K₁ / k((x))` were separable, then the canonical radical extension
-- `k[[x]] ⊂ k[[x]][x^{1/p}]` would remain outside the weak-solution range from
-- Definition `15.116.1`: after base change, every local branch still has ramification index
-- divisible by `p`, so no weak solution exists.
/-- Example 15.116.2 (1): for a perfect field `k` of characteristic `p > 0`, any weak solution for
the canonical extension `k[[x]] ⊂ k[[x]][x^{1/p}]` is inseparable over `k((x))`. -/
theorem not_isSeparable_of_weakSolutionForPowerSeriesPthRoot :
    IsWeakSolutionFor A B K L K₁ → ¬ Algebra.IsSeparable K K₁ := by
  intro hWeak
  intro hSep
  letI : Algebra.IsSeparable K K₁ := hSep
  -- Reduce the contradiction to the existence of one bad localized branch after separable base
  -- change.
  exact
    not_isWeakSolutionFor_of_exists_bad_branch
      (K₁ := K₁)
      (exists_bad_branch_of_isSeparable (K₁ := K₁))
      hWeak

-- Proof sketch: for a finite inseparable extension `K₁ / k((x))`, the canonical pth-root
-- extension `k[[x]] ⊂ k[[x]][x^{1/p}]` becomes a solution in the sense of
-- Definition `15.116.1`: the inseparability forces the local branches after base change to be
-- formally smooth over the localized normalization.
/-- Example 15.116.2 (2): every finite inseparable extension of `k((x))` is a solution for the
canonical extension `k[[x]] ⊂ k[[x]][x^{1/p}]`. -/
theorem isSolutionForPowerSeriesPthRoot_of_not_isSeparable :
    (¬ Algebra.IsSeparable K K₁) → IsSolutionFor A B K L K₁ := by
  intro hK₁
  -- First produce a `p`th root of the uniformizer in `K₁`.
  obtain ⟨y, hy⟩ := uniformizer_mem_pth_powers_of_not_isSeparable (K₁ := K₁) hK₁
  -- Then the reduced tensor-product branch collapses to the base field, so the solution criterion
  -- becomes the identity formal-smoothness statement.
  exact isSolutionFor_of_uniformizer_mem_pth_powers (K₁ := K₁) ⟨y, hy⟩

end BaseChange
end
