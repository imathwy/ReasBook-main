import Mathlib
import Mathlib.FieldTheory.KummerPolynomial
import StacksProject_2024.Chap09.Lemma_9_15_6
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Definition_15_112_7
import StacksProject_2024.Chap15.Lemma_15_116_13
import StacksProject_2024.Chap15.Lemma_15_124_2

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial IsLocalRing
open IsExtensionOfDiscreteValuationRings
open scoped IntermediateField

universe u v

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {p : ℕ} [Fact p.Prime] [MixedCharZero A p] {ζ : A}
variable {P : A[X]}
variable {L : Type v} [Field L] [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A (FractionRing A) L]
variable {ξ : FractionRing A}

local notation "K" => FractionRing A
local notation "B" => integralClosure A L
local notation "κA" => ResidueField A

/- Domain-style sampling:
* primary domain: ramification theory for finite Kummer-type extensions of the fraction field of a
  mixed-characteristic discrete valuation ring;
* sampled owner declarations:
  `IsAlgebraic`,
  `IntermediateField.adjoin.finiteDimensional`,
  `finiteDimensional_residueField_of_finiteDimensional_fractionField_extension`,
  `IsUnramifiedWithRespectTo`,
  `IsTotallyRamifiedWithRespectTo`,
  `WeaklyUnramified`,
  `residueDegree`;
* best owner abstraction: the chapter ramification owners on `L / FractionRing A` and on the
  induced extension `A ⊆ integralClosure A L`, with the Kummer root hypotheses kept as the
  source-facing primitive data;
* primitive data: the quotient-polynomial owner `IsOneSubZetaQuotientPolynomial` and the
  root-generation hypothesis for `P(z) = ξ`;
* derived API: the Galois conclusion, the unramified and totally ramified degree-`p`
  alternatives, and the weakly unramified purely inseparable residue-field alternative.

Layer triage:
* `source-facing`: the Kummer extension statements in this file;
* `core/canonical`: `IsUnramifiedWithRespectTo`, `IsTotallyRamifiedWithRespectTo`, and
  `WeaklyUnramified`;
* `bridge/view`: the separability and local-extension instances derived from the Galois conclusion
  and the integral-closure setup.
-/

private theorem isAlgebraic_of_primitiveRootElimination_generator
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ) :
    IsAlgebraic K z := by
  rcases hP.eq_polynomial with ⟨a, hshape⟩
  let q : K[X] :=
    (X : K[X]) -
      ∑ i ∈ Finset.Icc 1 (p - 1), C (algebraMap A K (a i)) * X ^ i + C ξ
  let f : K[X] := X ^ p - q
  have hqdeg_sum :
      degree
          (∑ i ∈ Finset.Icc 1 (p - 1), C (algebraMap A K (a i)) * X ^ i : K[X]) ≤ p - 1 := by
    refine le_trans (Polynomial.degree_sum_le _ _) ?_
    refine Finset.sup_le_iff.mpr ?_
    intro i hi
    exact le_trans (Polynomial.degree_C_mul_X_pow_le i _) (by exact_mod_cast Finset.mem_Icc.mp hi |>.2)
  have hqdeg : q.degree < p := by
    have hp_one : (1 : WithBot ℕ) < p := by
      exact_mod_cast (Fact.out.one_lt : 1 < p)
    have hqdeg_le :
        q.degree ≤ p - 1 := by
      refine le_trans (Polynomial.degree_add_le _ _) ?_
      refine max_le ?_ hqdeg_sum
      exact le_of_lt hp_one
    exact lt_of_le_of_lt hqdeg_le (by exact_mod_cast Nat.sub_lt (Fact.out.pos) zero_lt_one)
  have hf_monic : f.Monic := by
    -- Repackage the displayed source polynomial as `X ^ p - q` with `deg q < p`.
    simpa [f, q, hshape, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_sum,
      Polynomial.map_X, Polynomial.map_C, map_sub, map_add, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm] using (Polynomial.monic_X_pow_sub (p := q) (n := p) hqdeg)
  have hz_aeval : aeval z f = 0 := by
    -- Evaluating `f` at the chosen root is exactly the defining equation `P(z) = ξ`.
    simp [f, q, hshape, hz, Polynomial.aeval_def, Polynomial.eval₂_sum, map_sub, map_add,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  exact isAlgebraic_iff_isIntegral.2 ⟨f, hf_monic, hz_aeval⟩

private theorem finiteDimensional_of_primitiveRootElimination_generator
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    FiniteDimensional K L := by
  have hz_alg :
      IsAlgebraic K z :=
    isAlgebraic_of_primitiveRootElimination_generator (A := A) (p := p) (ζ := ζ)
      (P := P) (L := L) (ξ := ξ) hP z hz
  have hz_int : IsIntegral K z := isAlgebraic_iff_isIntegral.mp hz_alg
  have hfd_adjoin : FiniteDimensional K K⟮z⟯ :=
    IntermediateField.adjoin.finiteDimensional hz_int
  let e : K⟮z⟯ ≃ₐ[K] L :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  -- Transport finite-dimensionality across the simple-generator equivalence.
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

private theorem finiteDimensional_residueField_of_integralClosure
    [FiniteDimensional K L]
    [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) := by
  let _ : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  -- Reuse the generic valuation-ring residue-field finiteness theorem.
  exact finiteDimensional_residueField_of_finiteDimensional_fractionField_extension
    (A := A) (B := B)

/-- Helper for Lemma 15.116.14: the quotient-polynomial equation converts the chosen generator
into a Kummer radical equation `y ^ p = η`. -/
private lemma primitive_root_elimination_radical_presentation
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ) :
    let w : K := algebraMap A K (1 - ζ)
    let y : L := 1 + algebraMap K L w * z
    let η : K := 1 + w ^ p * ξ
    y ^ p = algebraMap K L η := by
  dsimp
  have hquot :=
    congrArg (Polynomial.map (algebraMap A K))
      (IsOneSubZetaQuotientPolynomial.quotient_eq (p := p) (ζ := ζ) hP)
  have hEval := congrArg (aeval z) hquot
  -- Evaluating the quotient identity is exactly the source-to-Kummer bridge.
  simpa [hz, Polynomial.aeval_def, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, map_sub, map_add, map_mul,
    map_pow, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
    mul_comm] using hEval

/-- Helper for Lemma 15.116.14: the affine-translated radical generator still generates the whole
extension field. -/
private lemma primitive_root_elimination_adjoin_top_of_radical_generator
    (hζ : IsPrimitiveRoot ζ p)
    (z : L)
    (hgen : K⟮z⟯ = ⊤) :
    let w : K := algebraMap A K (1 - ζ)
    let y : L := 1 + algebraMap K L w * z
    K⟮y⟯ = ⊤ := by
  dsimp
  have hζ_ne_one : ζ ≠ 1 := hζ.ne_one (Fact.out.one_lt)
  have hw_ne_zero : algebraMap A K (1 - ζ) ≠ 0 := by
    rw [map_ne_zero]
    exact sub_ne_zero.mpr hζ_ne_one
  have hwL_ne_zero : algebraMap A L (1 - ζ) ≠ 0 := by
    rw [show algebraMap A L (1 - ζ) = algebraMap K L (algebraMap A K (1 - ζ)) by rfl]
    rw [map_ne_zero]
    exact hw_ne_zero
  have hz_mem : z ∈ K⟮1 + algebraMap A L (1 - ζ) * z⟯ := by
    have hy_mem :
        1 + algebraMap A L (1 - ζ) * z ∈ K⟮1 + algebraMap A L (1 - ζ) * z⟯ :=
      IntermediateField.mem_adjoin_simple_self K (1 + algebraMap A L (1 - ζ) * z)
    have hsub_mem :
        (1 + algebraMap A L (1 - ζ) * z) - 1 ∈ K⟮1 + algebraMap A L (1 - ζ) * z⟯ :=
      (K⟮1 + algebraMap A L (1 - ζ) * z⟯).sub_mem hy_mem
        ((K⟮1 + algebraMap A L (1 - ζ) * z⟯).one_mem)
    have hinv_mem :
        (algebraMap A L (1 - ζ))⁻¹ ∈ K⟮1 + algebraMap A L (1 - ζ) * z⟯ :=
      (K⟮1 + algebraMap A L (1 - ζ) * z⟯).inv_mem <|
        (K⟮1 + algebraMap A L (1 - ζ) * z⟯).algebraMap_mem (algebraMap A K (1 - ζ))
    have hmul_mem :
        ((1 + algebraMap A L (1 - ζ) * z) - 1) * (algebraMap A L (1 - ζ))⁻¹ ∈
          K⟮1 + algebraMap A L (1 - ζ) * z⟯ :=
      (K⟮1 + algebraMap A L (1 - ζ) * z⟯).mul_mem hsub_mem hinv_mem
    have hz_eq :
        z = ((1 + algebraMap A L (1 - ζ) * z) - 1) * (algebraMap A L (1 - ζ))⁻¹ := by
      field_simp [hwL_ne_zero]
      ring
    exact hz_eq.symm ▸ hmul_mem
  have hle : K⟮z⟯ ≤ K⟮1 + algebraMap A L (1 - ζ) * z⟯ :=
    (IntermediateField.adjoin_simple_le_iff).2 hz_mem
  exact top_le_iff.mp (by simpa [hgen] using hle)

/-- Helper for Lemma 15.116.14: once the radical equation `y ^ p = η` is known, the Kummer
polynomial `X ^ p - η` splits in the ambient field. -/
private lemma x_pow_sub_C_splits_of_primitive_root_and_root
    (hζ : IsPrimitiveRoot ζ p)
    {η : K} {y : L}
    (hy : y ^ p = algebraMap K L η) :
    ((X ^ p - C η : K[X]).map (algebraMap K L)).Splits := by
  have hζL : IsPrimitiveRoot (algebraMap A L ζ) p :=
    hζ.map_of_injective (FaithfulSMul.algebraMap_injective A L)
  have hsplit_prod :
      (∏ i ∈ Finset.range p, (X - C ((algebraMap A L ζ) ^ i * y) : L[X])).Splits := by
    refine Polynomial.splits_prod ?_
    intro i hi
    exact Polynomial.splits_X_sub_C ((algebraMap A L ζ) ^ i * y)
  have hfactor :
      (X ^ p - C (algebraMap K L η) : L[X]) =
        ∏ i ∈ Finset.range p, (X - C ((algebraMap A L ζ) ^ i * y) : L[X]) := by
    exact X_pow_sub_C_eq_prod hζL Fact.out.pos hy
  -- The explicit Kummer factorization gives the required splitting statement.
  simpa using hfactor ▸ hsplit_prod

/-- Helper for Lemma 15.116.14: the mapped minimal polynomial of the radical generator splits in
the ambient field. -/
private lemma primitive_root_elimination_minpoly_splits_of_radical_generator
    (hζ : IsPrimitiveRoot ζ p)
    {η : K} {y : L}
    (hy : y ^ p = algebraMap K L η) :
    ((minpoly K y).map (algebraMap K L)).Splits := by
  let f : K[X] := X ^ p - C η
  have hsplit :
      (f.map (algebraMap K L)).Splits :=
    x_pow_sub_C_splits_of_primitive_root_and_root (A := A) (p := p) (ζ := ζ) hζ hy
  have hy_aeval : aeval y f = 0 := by
    -- The radical presentation makes the Kummer polynomial vanish at `y`.
    simpa [f, Polynomial.aeval_def] using (sub_eq_zero.mpr hy)
  have hdvd : (minpoly K y).map (algebraMap K L) ∣ f.map (algebraMap K L) := by
    exact Polynomial.map_dvd (algebraMap K L) (minpoly.dvd K y hy_aeval)
  have hf_ne_zero : f.map (algebraMap K L) ≠ 0 := by
    exact map_ne_zero (Polynomial.monic_X_pow_sub_C η Fact.out.ne_zero).ne_zero
  exact Polynomial.Splits.of_dvd hsplit hf_ne_zero hdvd

section PrimitiveRootEliminationGenerator

variable (hζ : IsPrimitiveRoot ζ p)
variable (hP : IsOneSubZetaQuotientPolynomial p ζ P)
variable (z : L)
variable (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ)
variable (hgen : K⟮z⟯ = ⊤)

-- Proof sketch: use Lemma `15.116.13` to convert the equation `P(z) = ξ` into a Kummer equation
-- `y ^ p = w ^ p * (1 + ξ)` over `K = FractionRing A`, where `K` already contains a primitive
-- `p`th root of unity `ζ`. Kummer theory shows that adjoining a root produces a finite normal
-- separable extension, hence a Galois extension.
/-- Lemma 15.116.14 (1): let `A` be a mixed-characteristic discrete valuation ring containing a
primitive `p`th root of unity `ζ`, let `P ∈ A[X]` be a polynomial satisfying the conclusion of
Lemma `15.116.13`, let `ξ : K = FractionRing A`, and let `L` be generated over `K` by a root `z`
of `P(z) = ξ`. Then `L / K` is Galois. -/
theorem primitiveRootElimination_extension_isGalois
    (hζ : IsPrimitiveRoot ζ p)
    (hP : IsOneSubZetaQuotientPolynomial p ζ P)
    (z : L)
    (hz : aeval z (P.map (algebraMap A K)) = algebraMap K L ξ)
    (hgen : K⟮z⟯ = ⊤) :
    IsGalois K L := by
  let w : K := algebraMap A K (1 - ζ)
  let y : L := 1 + algebraMap K L w * z
  let η : K := 1 + w ^ p * ξ
  have hy : y ^ p = algebraMap K L η :=
    primitive_root_elimination_radical_presentation
      (A := A) (p := p) (ζ := ζ) (P := P) (L := L) (ξ := ξ) hP z hz
  have hy_top : K⟮y⟯ = ⊤ :=
    primitive_root_elimination_adjoin_top_of_radical_generator
      (A := A) (p := p) (ζ := ζ) (L := L) hζ z hgen
  have hy_int : IsIntegral K y := by
    let f : K[X] := X ^ p - C η
    have hy_aeval : aeval y f = 0 := by
      -- The translated generator satisfies the Kummer polynomial by construction.
      simpa [f, Polynomial.aeval_def] using (sub_eq_zero.mpr hy)
    exact ⟨f, Polynomial.monic_X_pow_sub_C η Fact.out.ne_zero, hy_aeval⟩
  have hnormal : Normal K L := by
    let α : PUnit → L := fun _ ↦ y
    have hgen' : IntermediateField.adjoin K (Set.range α) = ⊤ := by
      -- The singleton family generated by `y` is exactly the whole extension.
      simpa [α, Set.range_const] using hy_top
    have hint : ∀ i : PUnit, IsIntegral K (α i) := by
      intro i
      simpa [α] using hy_int
    have hsplit : ∀ i : PUnit, ((minpoly K (α i)).map (algebraMap K L)).Splits := by
      intro i
      simpa [α] using
        primitive_root_elimination_minpoly_splits_of_radical_generator
          (A := A) (p := p) (ζ := ζ) (L := L) hζ hy
    exact normal_of_adjoin_range_minpoly_splits α hgen' hint hsplit
  let _ : FiniteDimensional K L :=
    finiteDimensional_of_primitiveRootElimination_generator
      (A := A) (p := p) (ζ := ζ) (P := P) (L := L) (ξ := ξ) hP z hz hgen
  have hsep : Algebra.IsSeparable K L := by
    -- The fraction field of a mixed-characteristic DVR has characteristic zero, so finite
    -- extensions are separable.
    infer_instance
  exact (isGalois_iff).2 ⟨hsep, hnormal⟩

local instance : FiniteDimensional K L := by
  exact
    finiteDimensional_of_primitiveRootElimination_generator
      (A := A) (p := p) (ζ := ζ) (P := P) (L := L) (ξ := ξ) hP z hz hgen

local instance : Algebra.IsSeparable K L :=
  by
    -- Once the extension is Galois, separability is part of the canonical owner API.
    exact (isGalois_iff.mp <|
      primitiveRootElimination_extension_isGalois
        (A := A) (p := p) (ζ := ζ) (P := P) (L := L) (ξ := ξ) hζ hP z hz hgen).1

local instance : Algebra.EssFiniteType A B := by
  let _ : Module.Finite A B := IsIntegralClosure.finite A K L B
  infer_instance

local instance [IsDiscreteValuationRing B] :
    FiniteDimensional κA (ResidueField B) := by
  exact finiteDimensional_residueField_of_integralClosure (A := A) (L := L)

-- Proof sketch: use the same Kummer-theoretic reduction as in part (1). The classification of
-- degree-`p` Kummer extensions over a mixed-characteristic discrete valuation ring yields the
-- four mutually exclusive possibilities recorded below.
/-- Lemma 15.116.14 (2): in the situation of part (1), either the extension is trivial, or it is
unramified of degree `p`, or it is totally ramified of degree `p`, or the integral closure of `A`
in `L` is a discrete valuation ring such that `A ⊆ integralClosure A L` is weakly unramified and
the residue-field extension is purely inseparable of degree `p`. -/
theorem primitiveRootElimination_has_ramification_case
    :
    Module.finrank K L = 1 ∨
      (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) ∨
      (Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L) ∨
      ∃ (_ : IsDiscreteValuationRing B),
        WeaklyUnramified A B ∧
          IsPurelyInseparable κA (ResidueField B) ∧
          residueDegree A B = p := sorry

-- Proof sketch: when `ξ` lies in `A`, the transformed Kummer equation is defined by a unit on the
-- right-hand side, so the corresponding degree-`p` algebra over `A` is finite étale. Over a
-- discrete valuation ring, this leaves only the trivial case or the unramified degree-`p` case.
/-- If `ξ` lies in `A`, then the extension defined by adjoining a root of `P(z) = ξ` is either
trivial or unramified of degree `p`. -/
theorem primitiveRootElimination_eq_or_unramified_of_mem_ring
    (hξ : ∃ a : A, algebraMap A K a = ξ)
    :
    Module.finrank K L = 1 ∨ (Module.finrank K L = p ∧ IsUnramifiedWithRespectTo A L) := sorry

-- Proof sketch: write the chosen root in a localization of the integral closure and compare
-- valuations in the transformed Kummer equation. If `ξ = a / π^n` with `n > 0` and `p ∤ n`, the
-- valuation of the root forces the ramification index to be divisible by `p`, hence equal to `p`
-- because the extension degree is at most `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∤ n`, and `a` a unit of `A`, then the extension defined by
adjoining a root of `P(z) = ξ` is in the totally ramified degree-`p` case. -/
theorem primitiveRootElimination_totally_ramified_of_uniformizer_denominator
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hndiv : ¬ p ∣ n) (a : Aˣ)
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n)
    :
    Module.finrank K L = p ∧ IsTotallyRamifiedWithRespectTo A L := sorry

-- Proof sketch: after multiplying the transformed Kummer equation by `π^n` with `p ∣ n`, rewrite
-- it as an integral equation over `A`. The resulting normalization is weakly unramified over `A`,
-- and the non-`p`th-power residue of `a` forces the residue-field extension to be purely
-- inseparable of degree `p`.
/-- If `ξ = π^{-n} a` with `n > 0`, `p ∣ n`, and the residue class of the unit `a` is not a `p`th
power, then the extension defined by adjoining a root of `P(z) = ξ` is in the weakly unramified
purely inseparable residue-field case of degree `p`. -/
theorem primitiveRootElimination_weakly_unramified_residue_case_of_uniformizer_denominator
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    {n : ℕ} (hn : 0 < n) (hdiv : p ∣ n) (a : Aˣ)
    (ha : ¬ ∃ b : κA, b ^ p = residue A (a : A))
    (hξ : ξ = algebraMap A K (a : A) / (algebraMap A K π) ^ n) :
    ∃ (_ : IsDiscreteValuationRing B),
      WeaklyUnramified A B ∧
        IsPurelyInseparable κA (ResidueField B) ∧
        residueDegree A B = p := sorry

end PrimitiveRootEliminationGenerator

end
