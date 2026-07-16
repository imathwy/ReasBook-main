import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import stacks_proof.stacks_project.Chap10.Definition_10_70_1
import stacks_proof.stacks_project.Chap10.«10_69_0_1»
import stacks_proof.stacks_project.Chap10.Definition_10_60_10
import stacks_proof.stacks_project.Chap10.Lemma_10_106_3
import stacks_proof.stacks_project.Chap10.Definition_10_160_5
import stacks_proof.stacks_project.Chap10.Remark_10_160_9
import stacks_proof.stacks_project.Chap15.Definition_15_36_1_Topological_rings
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open IsLocalRing MvPowerSeries
open scoped Topology BigOperators
open WithPiTopology

-- Domain-style sampling:
-- * primary domain: complete local power-series presentations determined by regular systems of
--   parameters;
-- * sampled owner declarations:
--   `IsPartOfRegularSystemOfParameters`,
--   `MvPowerSeries.hasSubst_of_constantCoeff_zero`,
--   `MvPowerSeries.substAlgHom`,
--   `MvPowerSeries.aeval`,
--   `Ideal.Quotient.liftₐ`,
--   `IsRegularSystemOfParameters`;
-- * owner abstraction: `parameterIdeal` and the source-facing existential owner
--   `IsPartOfRegularSystemOfParameters` capture the quotient determined by a partial parameter
--   family, while the actual presentation maps are owned canonically by `MvPowerSeries.substAlgHom`
--   in equal characteristic and `MvPowerSeries.aeval` in mixed characteristic or quotient targets.
-- * primitive data: a full regular system of parameters, or a prefix family together with the
--   source-facing property of being part of one;
-- * derived API: the induced substitution/evaluation maps and quotient power-series
--   presentations.
-- * source/core/bridge triage:
--   - `source-facing`: the four clauses of Lemma 15.39.2 about regular systems of parameters and
--     their induced quotient presentations;
--   - `core/canonical`: `parameterIdeal`, `IsRegularSystemOfParameters`,
--     `IsPartOfRegularSystemOfParameters`, `MvPowerSeries.substAlgHom`, and `MvPowerSeries.aeval`;
--   - `bridge/view`: the explicit quotient `AlgEquiv`s attached to a chosen complementary tail.

section AssociatedGradedHelpers

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {S : Type u} [CommRing S] {J : Ideal S}

/-- Helper for Lemma 15.39.2: the canonical associated-graded map sends a degree-one class to the
degree-one class of the image element. -/
private theorem idealAssociatedGradedMap_degreeOne
    (f : R →+* S) (hIJ : I ≤ Ideal.comap f J) (x : I) :
    idealAssociatedGradedMap f hIJ (idealAssociatedGradedDegreeOne x) =
      idealAssociatedGradedDegreeOne ⟨f x, hIJ x.2⟩ := by
  -- Unfold both constructions down to the quotient-Rees model and compare the underlying
  -- degree-one monomials after applying `reesAlgebraMap`.
  change
    Ideal.Quotient.mk _
        (reesAlgebraMap f hIJ
          ⟨Polynomial.monomial 1 (x : R), idealAssociatedGradedDegreeOne_mem x⟩) =
      Ideal.Quotient.mk _
        ⟨Polynomial.monomial 1 (f (x : R)),
          idealAssociatedGradedDegreeOne_mem ⟨f x, hIJ x.2⟩⟩
  congr
  apply Subtype.ext
  simp [reesAlgebraMap]

end AssociatedGradedHelpers

section LocalHelpers

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Helper for Lemma 15.39.2: restricting an appended family to its first block recovers the
original prefix family. -/
private theorem fin_append_comp_castLE_left
    {r s : ℕ} (z : Fin r → maximalIdeal R) (y : Fin s → maximalIdeal R) :
    (Fin.append z y) ∘ Fin.castLE (Nat.le_add_right r s) = z := by
  -- The canonical prefix embedding lands entirely in the left block of `Fin.append`.
  funext i
  simp

/-- Helper for Lemma 15.39.2: the parameter ideal of the prefixed part of an appended family is
the original prefix parameter ideal. -/
private theorem parameterIdeal_append_comp_castLE_left
    {r s : ℕ} (z : Fin r → maximalIdeal R) (y : Fin s → maximalIdeal R) :
    parameterIdeal ((Fin.append z y) ∘ Fin.castLE (Nat.le_add_right r s)) =
      parameterIdeal z := by
  -- Replace the prefixed family by the original one using the pointwise identification above.
  rw [fin_append_comp_castLE_left z y]

/-- Helper for Lemma 15.39.2: a maximally adically complete local-ring endomorphism is bijective
once it is bijective modulo every power of the maximal ideal. -/
private theorem adicComplete_endomorphism_bijective_of_powQuotient_bijective
    {R : Type u} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (φ : R →+* R)
    (hstable : ∀ n : ℕ, maximalIdeal R ^ n ≤ (maximalIdeal R ^ n).comap φ)
    (hquot : ∀ n : ℕ,
      Function.Bijective
        ((Ideal.quotientMap (maximalIdeal R ^ n) φ (hstable n)) :
          R ⧸ maximalIdeal R ^ n →+* R ⧸ maximalIdeal R ^ n)) :
    Function.Bijective φ := by
  classical
  let π : ∀ n : ℕ, R ⧸ maximalIdeal R ^ n →+* R ⧸ maximalIdeal R ^ n :=
    fun n ↦ Ideal.quotientMap (maximalIdeal R ^ n) φ (hstable n)
  let e : ∀ n : ℕ, R ⧸ maximalIdeal R ^ n ≃+* R ⧸ maximalIdeal R ^ n :=
    fun n ↦ RingEquiv.ofBijective (π n) (hquot n)
  let q : ∀ n : ℕ, R →+* R ⧸ maximalIdeal R ^ n :=
    fun n ↦ (e n).symm.toRingHom.comp (Ideal.Quotient.mk (maximalIdeal R ^ n))
  have hmk_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal R) hle).comp
            (Ideal.Quotient.mk (maximalIdeal R ^ n)) =
          Ideal.Quotient.mk (maximalIdeal R ^ m) := by
    intro m n hle
    -- The transition map forgets the higher-order quotient and leaves the residue class unchanged.
    ext x
    simp
  have hπ_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal R) hle).comp (π n) =
          (π m).comp (Ideal.Quotient.factorPow (maximalIdeal R) hle) := by
    intro m n hle
    -- Both routes send the class of `x` to the class of `φ x` in the smaller quotient.
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp [π]
  have hq_compat :
      ∀ {m n : ℕ} (hle : m ≤ n),
        (Ideal.Quotient.factorPow (maximalIdeal R) hle).comp (q n) = q m := by
    intro m n hle
    -- Compare the two candidate inverses after postcomposing with the bijection `π m`.
    ext x
    apply (hquot m).injective
    calc
      π m ((Ideal.Quotient.factorPow (maximalIdeal R) hle) (q n x))
          = (Ideal.Quotient.factorPow (maximalIdeal R) hle) (π n (q n x)) := by
              symm
              exact DFunLike.congr_fun (hπ_compat hle) (q n x)
      _ = (Ideal.Quotient.factorPow (maximalIdeal R) hle)
            (Ideal.Quotient.mk (maximalIdeal R ^ n) x) := by
              congr 1
              exact RingEquiv.apply_symm_apply (e n) (Ideal.Quotient.mk (maximalIdeal R ^ n) x)
      _ = Ideal.Quotient.mk (maximalIdeal R ^ m) x := by
              simpa using congrFun (DFunLike.congr_fun (hmk_compat hle) x)
      _ = π m (q m x) := by
              exact (RingEquiv.apply_symm_apply (e m) (Ideal.Quotient.mk (maximalIdeal R ^ m) x)).symm
  let ψ : R →+* R := IsAdicComplete.liftRingHom (maximalIdeal R) q hq_compat
  have hid :
      IsAdicComplete.liftRingHom
          (maximalIdeal R)
          (fun n ↦ Ideal.Quotient.mk (maximalIdeal R ^ n))
          hmk_compat =
        RingHom.id R := by
    symm
    apply IsAdicComplete.eq_liftRingHom (I := maximalIdeal R)
      (f := fun n ↦ Ideal.Quotient.mk (maximalIdeal R ^ n))
      (hf := hmk_compat)
      (F := RingHom.id R)
    intro n
    rfl
  have hleft : ψ.comp φ = RingHom.id R := by
    -- The lifted inverse recovers the identity on every quotient, hence globally by Hausdorffness.
    calc
      ψ.comp φ =
          IsAdicComplete.liftRingHom
            (maximalIdeal R)
            (fun n ↦ Ideal.Quotient.mk (maximalIdeal R ^ n))
            hmk_compat := by
              apply IsAdicComplete.eq_liftRingHom (I := maximalIdeal R)
                (f := fun n ↦ Ideal.Quotient.mk (maximalIdeal R ^ n))
                (hf := hmk_compat)
                (F := ψ.comp φ)
              intro n
              ext x
              calc
                Ideal.Quotient.mk (maximalIdeal R ^ n) ((ψ.comp φ) x)
                    = q n (φ x) := by
                        simp [ψ]
                _ = (e n).symm (Ideal.Quotient.mk (maximalIdeal R ^ n) (φ x)) := by
                        rfl
                _ = (e n).symm (π n (Ideal.Quotient.mk (maximalIdeal R ^ n) x)) := by
                        rfl
                _ = Ideal.Quotient.mk (maximalIdeal R ^ n) x := by
                        exact RingEquiv.symm_apply_apply (e n) (Ideal.Quotient.mk (maximalIdeal R ^ n) x)
      _ = RingHom.id R := hid
  have hright : φ.comp ψ = RingHom.id R := by
    -- The same quotient-by-quotient comparison proves the right-inverse identity.
    calc
      φ.comp ψ =
          IsAdicComplete.liftRingHom
            (maximalIdeal R)
            (fun n ↦ Ideal.Quotient.mk (maximalIdeal R ^ n))
            hmk_compat := by
              apply IsAdicComplete.eq_liftRingHom (I := maximalIdeal R)
                (f := fun n ↦ Ideal.Quotient.mk (maximalIdeal R ^ n))
                (hf := hmk_compat)
                (F := φ.comp ψ)
              intro n
              ext x
              calc
                Ideal.Quotient.mk (maximalIdeal R ^ n) ((φ.comp ψ) x)
                    = π n (Ideal.Quotient.mk (maximalIdeal R ^ n) (ψ x)) := by
                        rfl
                _ = π n (q n x) := by
                        simp [ψ]
                _ = π n ((e n).symm (Ideal.Quotient.mk (maximalIdeal R ^ n) x)) := by
                        rfl
                _ = Ideal.Quotient.mk (maximalIdeal R ^ n) x := by
                        exact RingEquiv.apply_symm_apply (e n) (Ideal.Quotient.mk (maximalIdeal R ^ n) x)
      _ = RingHom.id R := hid
  refine ⟨?_, ?_⟩
  · -- A left inverse gives injectivity.
    exact Function.LeftInverse.injective (fun x ↦ by
      simpa using DFunLike.congr_fun hleft x)
  · -- A right inverse gives surjectivity.
    exact Function.RightInverse.surjective (fun x ↦ by
      simpa using DFunLike.congr_fun hright x)

end LocalHelpers

section

variable {K : Type u} [Field K] {n : ℕ}

local notation "P" => MvPowerSeries (Fin n) K

private theorem field_constantCoeff_eq_zero (y : maximalIdeal P) :
    constantCoeff (y : P) = 0 := by
  by_contra hy0
  have hy_nonunit : ¬ IsUnit (y : P) := by
    intro hy_unit
    exact (IsLocalRing.notMem_maximalIdeal.mpr hy_unit) y.2
  exact hy_nonunit <| isUnit_iff_constantCoeff.2 <| isUnit_iff_ne_zero.mpr hy0

/-- Helper for Lemma 15.39.2: each coordinate variable lies in the maximal ideal of the
finite-variable power series ring over a field. -/
private theorem mvPowerSeries_fin_field_X_mem_maximalIdeal (j : Fin n) :
    (MvPowerSeries.X j : P) ∈ maximalIdeal P := by
  -- A unit power series has unit constant coefficient, but `X j` has constant coefficient `0`.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have hcoeff : IsUnit (MvPowerSeries.constantCoeff (MvPowerSeries.X j : P)) :=
    MvPowerSeries.isUnit_constantCoeff _ hunit
  simpa [MvPowerSeries.constantCoeff_X] using hcoeff

/-- Helper for Lemma 15.39.2: each coordinate variable lies in the parameter ideal generated by a
regular system of parameters. This is the source-faithful starting point for reading off the
linear coefficient matrix from `hy`. -/
private theorem mvPowerSeries_fin_field_X_mem_parameterIdeal_of_regularSystemOfParameters
    (y : Fin n → maximalIdeal P) (hy : IsRegularSystemOfParameters y) (j : Fin n) :
    (MvPowerSeries.X j : P) ∈ parameterIdeal y := by
  -- Rewrite the regular-system hypothesis to identify the parameter ideal with the maximal ideal,
  -- then use the coordinate-variable membership from the previous helper.
  rw [hy.2]
  exact mvPowerSeries_fin_field_X_mem_maximalIdeal (K := K) j

/-- Helper for Lemma 15.39.2: each coordinate variable is an explicit finite linear combination of
the chosen regular parameters. This packages the ideal-membership statement in the exact form
needed for the later degree-one coefficient computation. -/
private theorem
    mvPowerSeries_fin_field_exists_coordinate_representation_of_regularSystemOfParameters
    (y : Fin n → maximalIdeal P) (hy : IsRegularSystemOfParameters y) (j : Fin n) :
    ∃ a : Fin n → P, ∑ i, a i * (y i : P) = (MvPowerSeries.X j : P) := by
  have hX : (MvPowerSeries.X j : P) ∈ parameterIdeal y :=
    mvPowerSeries_fin_field_X_mem_parameterIdeal_of_regularSystemOfParameters
      (K := K) y hy j
  -- Convert membership in the span-generated parameter ideal into an actual finite sum.
  rw [parameterIdeal_eq_span] at hX
  exact Ideal.mem_span_range_iff_exists_fun.mp hX

/-- Helper for Lemma 15.39.2: in degree one, multiplying by a parameter from the maximal ideal
only retains the constant coefficient of the left factor. This is the coefficient-level bridge from
the source coordinate representation to the tangent-space matrix. -/
private theorem mvPowerSeries_fin_field_coeff_mul_parameter_degreeOne
    (a : P) (y : maximalIdeal P) (k : Fin n) :
    (a * (y : P)).coeff (Finsupp.single k 1) =
      MvPowerSeries.constantCoeff a * (y : P).coeff (Finsupp.single k 1) := by
  classical
  let δ : Fin n →₀ ℕ := Finsupp.single k 1
  have hy0 : (y : P).coeff 0 = 0 := by
    -- Parameters lie in the maximal ideal, so their constant coefficient vanishes.
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using
      field_constantCoeff_eq_zero (K := K) y
  rw [MvPowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (0, δ)]
  · -- The surviving antidiagonal term is the constant part of `a` times the linear coefficient of
    -- `y` in the chosen coordinate.
    simp [δ, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · intro de hde hne
    have hsum : de.1 + de.2 = δ := by
      simpa [δ] using (Finset.mem_antidiagonal.mp hde)
    by_cases hd0 : de.1 = 0
    · have heδ : de.2 = δ := by
        simpa [hd0] using hsum
      exact (hne (Prod.ext hd0 heδ)).elim
    · have hdk : de.1 k ≠ 0 := by
        intro hdk0
        apply hd0
        ext l
        by_cases hl : l = k
        · simpa [hl, hdk0]
        · have hsuml := congrArg (fun s : Fin n →₀ ℕ => s l) hsum
          simp [δ, hl] at hsuml
          exact hsuml.1
      have hsumk := congrArg (fun s : Fin n →₀ ℕ => s k) hsum
      simp [δ] at hsumk
      have hek : de.2 k = 0 := by
        omega
      have he0 : de.2 = 0 := by
        ext l
        by_cases hl : l = k
        · simpa [hl] using hek
        · have hsuml := congrArg (fun s : Fin n →₀ ℕ => s l) hsum
          simp [δ, hl] at hsuml
          exact hsuml.2
      simp [he0, hy0]
  · -- The constant/degree-one split is always one of the two antidiagonal summands.
    simpa [δ] using
      (show ((0 : Fin n →₀ ℕ), δ) ∈ Finset.antidiagonal δ from
        Finset.mem_antidiagonal.mpr (zero_add δ))

/-- Helper for Lemma 15.39.2: taking the degree-one coefficient of a coordinate representation
`∑ᵢ aᵢ yᵢ = Xⱼ` keeps only the constant parts of the `aᵢ`. This is the first verified tangent-space
equation needed to build the linear coefficient matrix of the regular system `y`. -/
private theorem mvPowerSeries_fin_field_coordinate_representation_coeff_degreeOne
    (y : Fin n → maximalIdeal P) {j : Fin n} {a : Fin n → P}
    (ha : ∑ i, a i * (y i : P) = (MvPowerSeries.X j : P))
    (k : Fin n) :
    ∑ i, MvPowerSeries.constantCoeff (a i) * (y i : P).coeff (Finsupp.single k 1) =
      (MvPowerSeries.X j : P).coeff (Finsupp.single k 1) := by
  -- Read the equality on the degree-one coefficient indexed by `X k`.
  have hcoeff := congrArg (fun f : P ↦ f.coeff (Finsupp.single k 1)) ha
  -- Each summand simplifies by the previous one-variable degree-one multiplication rule.
  simpa [mvPowerSeries_fin_field_coeff_mul_parameter_degreeOne (K := K),
    Finset.mul_sum] using hcoeff

/-- Helper for Lemma 15.39.2: the matrix recording the degree-one coefficients of a family of
parameters in the finite-variable power series ring over `K`. -/
private noncomputable def mvPowerSeries_fin_field_linearCoeffMatrix
    (y : Fin n → maximalIdeal P) : Matrix (Fin n) (Fin n) K :=
  fun i k ↦ (y i : P).coeff (Finsupp.single k 1)

/-- Helper for Lemma 15.39.2: the degree-one coefficient matrix of a regular system of parameters
admits a left inverse obtained from coordinate representations of the variables. -/
private theorem mvPowerSeries_fin_field_linear_part_has_left_inverse
    (y : Fin n → maximalIdeal P) (hy : IsRegularSystemOfParameters y) :
    ∃ M : Matrix (Fin n) (Fin n) K,
      M * mvPowerSeries_fin_field_linearCoeffMatrix (K := K) y = 1 := by
  classical
  choose a ha using
    mvPowerSeries_fin_field_exists_coordinate_representation_of_regularSystemOfParameters
      (K := K) y hy
  let L : Matrix (Fin n) (Fin n) K := mvPowerSeries_fin_field_linearCoeffMatrix (K := K) y
  let M : Matrix (Fin n) (Fin n) K :=
    fun j i ↦ MvPowerSeries.constantCoeff (a j i)
  refine ⟨M, ?_⟩
  ext j k
  -- Compare the `(j, k)` matrix entry with the degree-one coefficient of the coordinate identity
  -- `∑ᵢ aⱼᵢ yᵢ = Xⱼ`.
  have hcoeff :=
    mvPowerSeries_fin_field_coordinate_representation_coeff_degreeOne
      (K := K) y (ha j) k
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases h : j = k
  · simpa [L, M, mvPowerSeries_fin_field_linearCoeffMatrix, MvPowerSeries.coeff_X, h] using hcoeff
  · have hsingle :
        (Finsupp.single k 1 : Fin n →₀ ℕ) ≠ Finsupp.single j 1 := by
        intro hkj
        apply h
        exact
          (Finsupp.single_left_injective (show (1 : ℕ) ≠ 0 from one_ne_zero) hkj).symm
    simpa [L, M, mvPowerSeries_fin_field_linearCoeffMatrix, MvPowerSeries.coeff_X, hsingle, h]
      using hcoeff

/-- Helper for Lemma 15.39.2: the linear coefficient matrix of a regular system of parameters has
unit determinant. This is the matrix-level bridge needed to normalize the substitution map. -/
private theorem mvPowerSeries_fin_field_linear_part_isUnit_det
    (y : Fin n → maximalIdeal P) (hy : IsRegularSystemOfParameters y) :
    IsUnit (mvPowerSeries_fin_field_linearCoeffMatrix (K := K) y).det := by
  let L : Matrix (Fin n) (Fin n) K := mvPowerSeries_fin_field_linearCoeffMatrix (K := K) y
  rcases
      mvPowerSeries_fin_field_linear_part_has_left_inverse (K := K) y hy with
    ⟨M, hML⟩
  -- Taking determinants turns the left-inverse matrix identity into a unit equation.
  have hML' : M * L = 1 := by
    simpa [L] using hML
  have hdet : M.det * L.det = 1 := by
    have hdet' := congrArg Matrix.det hML'
    simpa [Matrix.det_mul] using hdet'
  have hdet' : L.det * M.det = 1 := by
    simpa [mul_comm] using hdet
  simpa [L] using IsUnit.of_mul_eq_one M.det hdet'

/-- Helper for Lemma 15.39.2: the field-side substitution endomorphism sends the maximal ideal of
`K[[x_1, \ldots, x_n]]` into itself. -/
private theorem mvPowerSeries_fin_field_substAlgHom_maximalIdeal_le_comap
    (y : Fin n → maximalIdeal P) :
    maximalIdeal P ≤
      (maximalIdeal P).comap
        ((MvPowerSeries.substAlgHom
          (MvPowerSeries.hasSubst_of_constantCoeff_zero
            fun i ↦ field_constantCoeff_eq_zero (y i))) :
            P →ₐ[K] P) := by
  let a : Fin n → P := fun i ↦ (y i : P)
  let ha : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ field_constantCoeff_eq_zero (y i)
  let φ : P →ₐ[K] P := MvPowerSeries.substAlgHom ha
  intro f hf
  change φ f ∈ maximalIdeal P
  -- The substitution preserves zero constant coefficient because every parameter lies in the
  -- maximal ideal, hence has zero constant coefficient over the field `K`.
  have hconst : constantCoeff (φ f) = 0 := by
    simpa [φ, a, MvPowerSeries.substAlgHom_apply] using
      (MvPowerSeries.constantCoeff_subst_eq_zero ha
        (fun i ↦ field_constantCoeff_eq_zero (y i))
        (hf := field_constantCoeff_eq_zero ⟨f, hf⟩))
  -- Over a field, zero constant coefficient is equivalent to nonunit, hence to maximal-ideal
  -- membership in the local power-series ring.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have hunitCoeff : IsUnit (constantCoeff (φ f)) := MvPowerSeries.isUnit_constantCoeff _ hunit
  simpa [hconst] using hunitCoeff

/-- Helper for Lemma 15.39.2: the field-side substitution endomorphism preserves every power of
the maximal ideal, which is the stability input needed for the adic-completeness bridge. -/
private theorem mvPowerSeries_fin_field_substAlgHom_pow_le_comap
    (y : Fin n → maximalIdeal P) (m : ℕ) :
    maximalIdeal P ^ m ≤
      (maximalIdeal P ^ m).comap
        ((MvPowerSeries.substAlgHom
          (MvPowerSeries.hasSubst_of_constantCoeff_zero
            fun i ↦ field_constantCoeff_eq_zero (y i))) :
            P →ₐ[K] P) := by
  let φ : P →ₐ[K] P :=
    MvPowerSeries.substAlgHom
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ field_constantCoeff_eq_zero (y i))
  have hmap :
      Ideal.map φ (maximalIdeal P) ≤ maximalIdeal P := by
    exact (Ideal.map_le_iff_le_comap).2
      (mvPowerSeries_fin_field_substAlgHom_maximalIdeal_le_comap y)
  -- Pass from the maximal ideal to its powers via monotonicity of ideal powers.
  exact (Ideal.map_le_iff_le_comap).1 <| by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hmap m

/-- Helper for Lemma 15.39.2: the linear change of variables attached to a matrix `L` sends `Xᵢ`
to `∑ⱼ Lᵢⱼ Xⱼ`. -/
private noncomputable def mvPowerSeries_fin_field_linearFamily
    (L : Matrix (Fin n) (Fin n) K) : Fin n → P :=
  fun i ↦ ∑ j, MvPowerSeries.C (L i j) * (MvPowerSeries.X j : P)

/-- Helper for Lemma 15.39.2: the linear family attached to a matrix has zero constant
coefficient termwise, so it is a valid substitution family. -/
private theorem mvPowerSeries_fin_field_linearFamily_constantCoeff_zero
    (L : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    MvPowerSeries.constantCoeff (mvPowerSeries_fin_field_linearFamily (K := K) L i) = 0 := by
  -- Every term is a scalar multiple of a coordinate variable, hence has vanishing constant term.
  simp [mvPowerSeries_fin_field_linearFamily]

/-- Helper for Lemma 15.39.2: each element of a linear substitution family already lies in the
maximal ideal. This packages the normalization family in the source-facing parameter format. -/
private theorem mvPowerSeries_fin_field_linearFamily_mem_maximalIdeal
    (L : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    mvPowerSeries_fin_field_linearFamily (K := K) L i ∈ maximalIdeal P := by
  -- A unit power series has unit constant coefficient, but every linear form has constant term `0`.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have hcoeff :
      IsUnit (MvPowerSeries.constantCoeff (mvPowerSeries_fin_field_linearFamily (K := K) L i)) :=
    MvPowerSeries.isUnit_constantCoeff _ hunit
  simpa [mvPowerSeries_fin_field_linearFamily_constantCoeff_zero (K := K) L i] using hcoeff

/-- Helper for Lemma 15.39.2: the linear family of a matrix defines a substitution endomorphism of
the finite-variable power series ring. -/
private theorem mvPowerSeries_fin_field_linearFamily_hasSubst
    (L : Matrix (Fin n) (Fin n) K) :
    MvPowerSeries.HasSubst (mvPowerSeries_fin_field_linearFamily (K := K) L) := by
  -- Finite-variable power series only need vanishing constant coefficients to admit substitution.
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro i
  exact mvPowerSeries_fin_field_linearFamily_constantCoeff_zero (K := K) L i

/-- Helper for Lemma 15.39.2: the degree-one coefficient of the `i`-th linear form attached to
`L` in the variable `Xₖ` is exactly the matrix entry `Lᵢₖ`. -/
private theorem mvPowerSeries_fin_field_linearFamily_coeff_degreeOne
    (L : Matrix (Fin n) (Fin n) K) (i k : Fin n) :
    (mvPowerSeries_fin_field_linearFamily (K := K) L i).coeff (Finsupp.single k 1) = L i k := by
  classical
  -- Only the `X k` summand contributes to the chosen degree-one coefficient.
  rw [mvPowerSeries_fin_field_linearFamily]
  calc
    (∑ j, MvPowerSeries.C (L i j) * (MvPowerSeries.X j : P)).coeff (Finsupp.single k 1) =
        ∑ j, (MvPowerSeries.C (L i j) * (MvPowerSeries.X j : P)).coeff (Finsupp.single k 1) := by
          simp
    _ = ∑ j, L i j * (MvPowerSeries.X j : P).coeff (Finsupp.single k 1) := by
            apply Finset.sum_congr rfl
            intro j hj
            simp [MvPowerSeries.coeff_C_mul]
    _ = L i k := by
          rw [Finset.sum_eq_single k]
          · simp [MvPowerSeries.coeff_X]
          · intro j hj hjk
            have hsingle :
                (Finsupp.single k 1 : Fin n →₀ ℕ) ≠ Finsupp.single j 1 := by
              intro hEq
              exact hjk <|
                (Finsupp.single_left_injective (show (1 : ℕ) ≠ 0 from one_ne_zero) hEq).symm
            simp [MvPowerSeries.coeff_X, hsingle]
          · simp [MvPowerSeries.coeff_X]

/-- Helper for Lemma 15.39.2: the linear coefficient matrix of the linear family attached to `L`
is exactly `L`. This is the concrete normalization datum used for the inverse linear change of
variables. -/
private theorem mvPowerSeries_fin_field_linearCoeffMatrix_linearFamily
    (L : Matrix (Fin n) (Fin n) K) :
    mvPowerSeries_fin_field_linearCoeffMatrix (K := K)
      (fun i ↦ ⟨mvPowerSeries_fin_field_linearFamily (K := K) L i,
        mvPowerSeries_fin_field_linearFamily_mem_maximalIdeal (K := K) L i⟩) = L := by
  -- Read each matrix entry as the corresponding degree-one coefficient of the linear form.
  ext i k
  exact mvPowerSeries_fin_field_linearFamily_coeff_degreeOne (K := K) L i k

/-- Helper for Lemma 15.39.2: substituting the linear family of `L` into the coordinate `Xⱼ`
recovers the `j`-th linear form of `L`. -/
private theorem mvPowerSeries_fin_field_subst_linearFamily_X
    (L : Matrix (Fin n) (Fin n) K)
    (hL : MvPowerSeries.HasSubst (mvPowerSeries_fin_field_linearFamily (K := K) L))
    (j : Fin n) :
    MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L)
        ((MvPowerSeries.X j : P)) =
      mvPowerSeries_fin_field_linearFamily (K := K) L j := by
  -- This is the defining `X`-computation for `MvPowerSeries.substAlgHom`.
  simpa using MvPowerSeries.substAlgHom_X hL j

/-- Helper for Lemma 15.39.2: substitution by a linear family acts termwise on a single linear
monomial `a * Xⱼ`. -/
private theorem mvPowerSeries_fin_field_substAlgHom_linear_term
    (L : Matrix (Fin n) (Fin n) K)
    (hL : MvPowerSeries.HasSubst (mvPowerSeries_fin_field_linearFamily (K := K) L))
    (a : K) (j : Fin n) :
    MvPowerSeries.substAlgHom hL (MvPowerSeries.C a * (MvPowerSeries.X j : P)) =
      MvPowerSeries.C a * mvPowerSeries_fin_field_linearFamily (K := K) L j := by
  -- Rewrite the algebra-hom application as substitution, then use multiplicativity and the `X`
  -- computation from the previous helper.
  calc
    MvPowerSeries.substAlgHom hL (MvPowerSeries.C a * (MvPowerSeries.X j : P)) =
        MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L)
          (MvPowerSeries.C a * (MvPowerSeries.X j : P)) := by
            rw [MvPowerSeries.substAlgHom_apply]
    _ = MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L)
          (MvPowerSeries.C a) *
        MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L)
          (MvPowerSeries.X j) := by
            rw [MvPowerSeries.subst_mul hL]
    _ = MvPowerSeries.C a * mvPowerSeries_fin_field_linearFamily (K := K) L j := by
            rw [MvPowerSeries.subst_C,
              mvPowerSeries_fin_field_subst_linearFamily_X (K := K) L hL j]

/-- Helper for Lemma 15.39.2: substituting the linear family of `M` into the `i`-th linear form
of `L` gives the expected linear combination of the rows of `M`. -/
private theorem mvPowerSeries_fin_field_subst_linearFamily_apply
    (L M : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) M)
        (mvPowerSeries_fin_field_linearFamily (K := K) L i) =
      ∑ j, MvPowerSeries.C (L i j) *
        mvPowerSeries_fin_field_linearFamily (K := K) M j := by
  classical
  let hM := mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) M
  -- Expand the source linear form and push substitution through the finite sum term by term.
  rw [← MvPowerSeries.substAlgHom_apply hM, mvPowerSeries_fin_field_linearFamily]
  calc
    MvPowerSeries.substAlgHom hM
        (∑ j, MvPowerSeries.C (L i j) * (MvPowerSeries.X j : P)) =
      ∑ j, MvPowerSeries.substAlgHom hM
        (MvPowerSeries.C (L i j) * (MvPowerSeries.X j : P)) := by
          simp
    _ = ∑ j, MvPowerSeries.C (L i j) *
        mvPowerSeries_fin_field_linearFamily (K := K) M j := by
          apply Finset.sum_congr rfl
          intro j hj
          exact mvPowerSeries_fin_field_substAlgHom_linear_term (K := K) M hM (L i j) j

/-- Helper for Lemma 15.39.2: composing two linear substitution families corresponds to matrix
multiplication. -/
private theorem mvPowerSeries_fin_field_subst_linearFamily_mul_apply
    (L M : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) M)
        (mvPowerSeries_fin_field_linearFamily (K := K) L i) =
      mvPowerSeries_fin_field_linearFamily (K := K) (L * M) i := by
  -- First expand substitution on the linear form, then regroup the double sum as the matrix
  -- product entry `(L * M) i j`.
  rw [mvPowerSeries_fin_field_subst_linearFamily_apply (K := K) L M i,
    mvPowerSeries_fin_field_linearFamily]
  simp_rw [mvPowerSeries_fin_field_linearFamily, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp [Matrix.mul_apply, Finset.sum_mul]

/-- Helper for Lemma 15.39.2: substituting the linear family of `M` into the linear family of `L`
multiplies the corresponding degree-one coefficient matrices. This records the matrix-level
special case of the normalization step already proved termwise above. -/
private theorem mvPowerSeries_fin_field_linearCoeffMatrix_subst_linearFamily_of_linearFamily
    (L M : Matrix (Fin n) (Fin n) K) :
    mvPowerSeries_fin_field_linearCoeffMatrix (K := K)
      (fun i ↦
        ⟨MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) M)
            (mvPowerSeries_fin_field_linearFamily (K := K) L i),
          by
            -- Replace the substituted series by the explicit product linear family, then reuse the
            -- maximal-ideal membership of linear forms.
            simpa [mvPowerSeries_fin_field_subst_linearFamily_mul_apply (K := K) L M i] using
              mvPowerSeries_fin_field_linearFamily_mem_maximalIdeal (K := K) (L * M) i⟩) =
      L * M := by
  -- Read each matrix entry as the chosen degree-one coefficient of the explicitly computed
  -- substituted linear form.
  ext i k
  change
    (MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) M)
      (mvPowerSeries_fin_field_linearFamily (K := K) L i)).coeff (Finsupp.single k 1) =
      (L * M) i k
  rw [mvPowerSeries_fin_field_subst_linearFamily_mul_apply (K := K) L M i]
  exact mvPowerSeries_fin_field_linearFamily_coeff_degreeOne (K := K) (L * M) i k

/-- Helper for Lemma 15.39.2: substituting a general series by the linear family of `M` transforms
its degree-one coefficients by right multiplication with `M`. This is the primitive coefficient
computation needed for the source-faithful normalization `ψ = τ ∘ φ`. -/
private theorem mvPowerSeries_fin_field_coeff_degreeOne_subst_linearFamily
    (f : P) (M : Matrix (Fin n) (Fin n) K) (k : Fin n) :
    (MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) M) f).coeff
        (Finsupp.single k 1) =
      ∑ j, f.coeff (Finsupp.single j 1) * M j k := by
  classical
  let a : Fin n → P := mvPowerSeries_fin_field_linearFamily (K := K) M
  let ha : MvPowerSeries.HasSubst a := mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) M
  let e : Fin n →₀ ℕ := Finsupp.single k 1
  let F : (Fin n →₀ ℕ) → K := fun d ↦
    f.coeff d * (d.prod fun s m ↦ (a s) ^ m).coeff e
  have hcoeff_large :
      ∀ d : Fin n →₀ ℕ, 2 ≤ d.degree → (d.prod fun s m ↦ (a s) ^ m).coeff e = 0 := by
    intro d hd
    -- Every substituted variable has order at least `1`, so any monomial of total degree at least
    -- `2` contributes only to coefficients of order at least `2`.
    apply MvPowerSeries.coeff_of_lt_order
    have hsum_le :
        (d.degree : ℕ∞) ≤ ∑ i ∈ d.support, (((a i : P) ^ d i).order) := by
      calc
        (d.degree : ℕ∞) = ∑ i ∈ d.support, (d i : ℕ∞) := by
          simp [Finsupp.degree]
        _ ≤ ∑ i ∈ d.support, (((a i : P) ^ d i).order) := by
          apply Finset.sum_le_sum
          intro i hi
          exact MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (d i)
            (mvPowerSeries_fin_field_linearFamily_constantCoeff_zero (K := K) M i)
    have hprod_order :
        (d.degree : ℕ∞) ≤ (d.prod fun s m ↦ (a s) ^ m).order := by
      calc
        (d.degree : ℕ∞) ≤ ∑ i ∈ d.support, (((a i : P) ^ d i).order) := hsum_le
        _ ≤ (d.prod fun s m ↦ (a s) ^ m).order := by
          simpa [a, Finsupp.prod] using
            (MvPowerSeries.le_order_prod
              (f := fun i : Fin n ↦ ((a i : P) ^ d i)) d.support)
    have htwo :
        (2 : ℕ∞) ≤ (d.prod fun s m ↦ (a s) ^ m).order := by
      exact (show (2 : ℕ∞) ≤ d.degree by exact_mod_cast hd).trans hprod_order
    have he_lt :
        (Finsupp.single k 1).degree < (d.prod fun s m ↦ (a s) ^ m).order := by
      rw [Finsupp.degree_single]
      exact lt_of_lt_of_le (by simp) htwo
    simpa [e] using he_lt
  have hsupp :
      F.support ⊆ (Finset.univ.image fun j : Fin n ↦ Finsupp.single j 1) := by
    intro d hdF
    have hcoeff_nonzero : (d.prod fun s m ↦ (a s) ^ m).coeff e ≠ 0 := by
      intro hzero
      have hFd : F d = 0 := by
        change f.coeff d * (d.prod fun s m ↦ (a s) ^ m).coeff e = 0
        rw [hzero, mul_zero]
      exact hdF hFd
    have hdeg_ne_zero : d.degree ≠ 0 := by
      intro hd0
      have hd_eq_zero : d = 0 := by
        exact (Finsupp.degree_eq_zero_iff d).mp hd0
      apply hcoeff_nonzero
      subst hd_eq_zero
      simpa [e] using (MvPowerSeries.coeff_one (R := K) (n := e))
    have hdeg_le_one : d.degree ≤ 1 := by
      by_contra hd_gt
      have hd_two : 2 ≤ d.degree := by omega
      exact hcoeff_nonzero (hcoeff_large d hd_two)
    have hdeg_one : d.degree = 1 := by omega
    have hd_range : d ∈ Set.range (fun j : Fin n ↦ Finsupp.single j 1) := by
      rwa [Finsupp.range_single_one]
    rcases Set.mem_range.mp hd_range with ⟨j, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  -- Restrict the coefficient formula to the finitely many degree-one monomials.
  have hsubst :
      (MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) M) f).coeff e =
        finsum F := by
    rw [MvPowerSeries.coeff_subst ha]
    simp [F, smul_eq_mul]
  rw [hsubst, finsum_eq_sum_of_support_subset F hsupp]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    have hprod : (Finsupp.single j 1).prod (fun s m ↦ (a s) ^ m) = a j := by
      simp [a]
    change
      f.coeff (Finsupp.single j 1) *
          ((Finsupp.single j 1).prod (fun s m ↦ (a s) ^ m)).coeff e =
        f.coeff (Finsupp.single j 1) * M j k
    rw [hprod, mvPowerSeries_fin_field_linearFamily_coeff_degreeOne (K := K) M j k]
  · intro i _ j _ hij
    exact Finsupp.single_left_injective (show (1 : ℕ) ≠ 0 from one_ne_zero) hij

/-- Helper for Lemma 15.39.2: substituting a family `y` by the linear family of `M` multiplies
its degree-one coefficient matrix by `M` on the right. This is the family-level normalization
identity used to make `ψ = τ ∘ φ` tangent to the identity. -/
private theorem mvPowerSeries_fin_field_linearCoeffMatrix_subst_linearFamily
    (y : Fin n → maximalIdeal P) (M : Matrix (Fin n) (Fin n) K) :
    mvPowerSeries_fin_field_linearCoeffMatrix (K := K)
      (fun i ↦
        ⟨MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i),
          by
            -- The substituted parameter still has zero constant coefficient, hence remains in the
            -- maximal ideal of the local power-series ring.
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            intro hunit
            have hconst :
                MvPowerSeries.constantCoeff
                    (MvPowerSeries.subst (R := K)
                      (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i)) = 0 := by
              exact MvPowerSeries.constantCoeff_subst_eq_zero
                (mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) M)
                (fun j ↦ mvPowerSeries_fin_field_linearFamily_constantCoeff_zero (K := K) M j)
                (hf := field_constantCoeff_eq_zero (K := K) (y i))
            have hunitCoeff :
                IsUnit
                  (MvPowerSeries.constantCoeff
                    (MvPowerSeries.subst (R := K)
                      (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i))) :=
              MvPowerSeries.isUnit_constantCoeff _ hunit
            simpa [hconst] using hunitCoeff⟩) =
      mvPowerSeries_fin_field_linearCoeffMatrix (K := K) y * M := by
  ext i k
  -- Read the `(i, k)` entry as the degree-one coefficient of the substituted parameter `y i`.
  rw [Matrix.mul_apply]
  simpa [mvPowerSeries_fin_field_linearCoeffMatrix] using
    mvPowerSeries_fin_field_coeff_degreeOne_subst_linearFamily (K := K) (f := (y i : P)) M k

/-- Helper for Lemma 15.39.2: vanishing of the constant term and all degree-one coefficients forces
order at least `2`. This is the coefficient-to-order half of the normalized tangent computation. -/
private theorem mvPowerSeries_fin_field_order_ge_two_of_constantCoeff_eq_zero_of_degreeOne_eq_zero
    (f : P) (hconst : MvPowerSeries.constantCoeff f = 0)
    (hdegreeOne : ∀ k : Fin n, f.coeff (Finsupp.single k 1) = 0) :
    (2 : ℕ∞) ≤ f.order := by
  -- Apply the owner lemma `nat_le_order` with `n = 2`, checking the only monomials of degree `< 2`
  -- are the constant monomial and the degree-one variables.
  refine MvPowerSeries.nat_le_order ?_
  intro d hd
  by_cases hd0 : d = 0
  · subst hd0
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hconst
  · have hdeg_ne_zero : Finsupp.degree d ≠ 0 := by
      intro hdeg0
      apply hd0
      exact (Finsupp.degree_eq_zero_iff d).mp hdeg0
    have hdeg_one : Finsupp.degree d = 1 := by
      refine le_antisymm (Nat.lt_succ_iff.mp hd) ?_
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hdeg_ne_zero)
    have hd_range : d ∈ Set.range (fun j : Fin n ↦ Finsupp.single j 1) := by
      rwa [Finsupp.range_single_one]
    rcases Set.mem_range.mp hd_range with ⟨j, rfl⟩
    exact hdegreeOne j

/-- Helper for Lemma 15.39.2: once the normalized linear part is the identity, each normalized
generator difference has order at least `2`. This isolates the coefficient bookkeeping before the
final bridge to `maximalIdeal P ^ 2`. -/
private theorem mvPowerSeries_fin_field_normalized_subst_order_ge_two
    (y : Fin n → maximalIdeal P) (M : Matrix (Fin n) (Fin n) K)
    (hM : mvPowerSeries_fin_field_linearCoeffMatrix (K := K) y * M = 1)
    (i : Fin n) :
    (2 : ℕ∞) ≤
      (MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i) -
        (MvPowerSeries.X i : P)).order := by
  have hconst_subst :
      MvPowerSeries.constantCoeff
          (MvPowerSeries.subst (R := K)
            (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i)) = 0 := by
    -- The normalized substitution still sends each parameter into the maximal ideal.
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) M)
      (fun j ↦ mvPowerSeries_fin_field_linearFamily_constantCoeff_zero (K := K) M j)
      (hf := field_constantCoeff_eq_zero (K := K) (y i))
  have hconst :
      MvPowerSeries.constantCoeff
          (MvPowerSeries.subst (R := K)
            (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i) -
            (MvPowerSeries.X i : P)) = 0 := by
    -- Both summands have zero constant term, so the normalized difference does as well.
    simp [hconst_subst]
  have hdegreeOne :
      ∀ k : Fin n,
        (MvPowerSeries.subst (R := K)
            (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i) -
            (MvPowerSeries.X i : P)).coeff (Finsupp.single k 1) = 0 := by
    intro k
    have hcoeff_X :
        (MvPowerSeries.X i : P).coeff (Finsupp.single k 1) =
          (1 : Matrix (Fin n) (Fin n) K) i k := by
      by_cases hik : i = k
      · subst hik
        simp [MvPowerSeries.coeff_X]
      · have hsingle :
            (Finsupp.single k 1 : Fin n →₀ ℕ) ≠ Finsupp.single i 1 := by
          intro hEq
          exact hik <|
            (Finsupp.single_left_injective (show (1 : ℕ) ≠ 0 from one_ne_zero) hEq).symm
        simp [MvPowerSeries.coeff_X, hik, hsingle]
    have hcoeff_subst :
        (MvPowerSeries.subst (R := K)
            (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i)).coeff
            (Finsupp.single k 1) =
          (1 : Matrix (Fin n) (Fin n) K) i k := by
      -- Read the normalized linear-part identity entrywise on the substituted family.
      have hentry :
          (MvPowerSeries.subst (R := K)
              (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i)).coeff
              (Finsupp.single k 1) =
            (mvPowerSeries_fin_field_linearCoeffMatrix (K := K) y * M) i k := by
        simpa [mvPowerSeries_fin_field_linearCoeffMatrix] using
          congrFun
            (congrFun
              (mvPowerSeries_fin_field_linearCoeffMatrix_subst_linearFamily (K := K) y M) i) k
      calc
        (MvPowerSeries.subst (R := K)
            (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i)).coeff
            (Finsupp.single k 1) =
          (mvPowerSeries_fin_field_linearCoeffMatrix (K := K) y * M) i k := hentry
        _ = (1 : Matrix (Fin n) (Fin n) K) i k := by rw [hM]
    -- The normalized matrix is the identity, so the degree-one coefficients match those of `X i`.
    calc
      (MvPowerSeries.subst (R := K)
          (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i) -
          (MvPowerSeries.X i : P)).coeff (Finsupp.single k 1) =
        (MvPowerSeries.subst (R := K)
            (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i)).coeff
            (Finsupp.single k 1) -
          (MvPowerSeries.X i : P).coeff (Finsupp.single k 1) := by
            simpa using
              (MvPowerSeries.coeff (Finsupp.single k 1)).map_sub
                (MvPowerSeries.subst (R := K)
                  (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i))
                (MvPowerSeries.X i : P)
      _ = (1 : Matrix (Fin n) (Fin n) K) i k -
          (MvPowerSeries.X i : P).coeff (Finsupp.single k 1) := by
            rw [hcoeff_subst]
      _ = 0 := by
            rw [hcoeff_X, sub_self]
  -- Feed the coefficient vanishing data through the owner-level order bound.
  exact
    mvPowerSeries_fin_field_order_ge_two_of_constantCoeff_eq_zero_of_degreeOne_eq_zero
      (K := K)
      (f := MvPowerSeries.subst (R := K)
        (mvPowerSeries_fin_field_linearFamily (K := K) M) (y i) - (MvPowerSeries.X i : P))
      hconst hdegreeOne

/-- Helper for Lemma 15.39.2: order at least `2` forces both the constant coefficient and every
degree-one coefficient to vanish. This packages the explicit coefficient data that the remaining
`maximalIdeal²` bridge must consume. -/
private theorem
    mvPowerSeries_fin_field_constantCoeff_eq_zero_and_degreeOne_eq_zero_of_order_ge_two
    (f : P) (horder : (2 : ℕ∞) ≤ f.order) :
    MvPowerSeries.constantCoeff f = 0 ∧
      ∀ k : Fin n, f.coeff (Finsupp.single k 1) = 0 := by
  constructor
  · -- The constant monomial has degree `0`, so it lies strictly below the assumed order bound.
    have hlt : (0 : ℕ∞) < f.order := by
      exact lt_of_lt_of_le (by simp) horder
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (MvPowerSeries.coeff_of_lt_order (f := f) (d := 0) hlt)
  · intro k
    -- Likewise every degree-one monomial is killed by an `order ≥ 2` estimate.
    have hlt : (((Finsupp.single k 1).degree : ℕ) : ℕ∞) < f.order := by
      rw [Finsupp.degree_single]
      exact lt_of_lt_of_le (by simp) horder
    simpa using
      (MvPowerSeries.coeff_of_lt_order (f := f) (d := Finsupp.single k 1) hlt)

/-- Helper for Lemma 15.39.2: the `i`-slice records precisely the monomials whose smallest
support index is `i`, after removing one copy of `X i`. This is the source-faithful decomposition
used to pass from coefficient vanishing to `maximalIdeal²` membership. -/
private noncomputable def mvPowerSeries_fin_field_firstIndexSlice
    (f : P) (i : Fin n) : P :=
  fun d ↦
    if ∀ j : Fin n, j < i → d j = 0 then
      f.coeff (d + Finsupp.single i 1)
    else
      0

/-- Helper for Lemma 15.39.2: the constant coefficient of the `i`-slice is the degree-one
coefficient of `f` in the variable `X i`. -/
private theorem mvPowerSeries_fin_field_constantCoeff_firstIndexSlice
    (f : P) (i : Fin n) :
    MvPowerSeries.constantCoeff
        (mvPowerSeries_fin_field_firstIndexSlice (K := K) f i) =
      f.coeff (Finsupp.single i 1) :=
by
  -- Evaluate the slice at the zero multi-index, where the side condition is vacuous and
  -- `0 + Finsupp.single i 1` simplifies to the target degree-one monomial.
  simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    mvPowerSeries_fin_field_firstIndexSlice]

/-- Helper for Lemma 15.39.2: every nonzero monomial has a smallest index where its exponent is
nonzero. This is the combinatorial pivot in the source decomposition by first support index. -/
private theorem mvPowerSeries_fin_field_exists_least_support_index
    {d : Fin n →₀ ℕ} (hd : d ≠ 0) :
    ∃ i : Fin n, d i ≠ 0 ∧ ∀ j : Fin n, j < i → d j = 0 := by
  have hsupp : d.support.Nonempty := by
    -- If the support were empty then all coefficients would vanish, contradicting `d ≠ 0`.
    by_contra hsupp
    apply hd
    ext i
    by_contra hi
    exact hsupp ⟨i, Finsupp.mem_support_iff.mpr hi⟩
  let i : Fin n := d.support.min' hsupp
  refine ⟨i, Finsupp.mem_support_iff.mp (Finset.min'_mem d.support hsupp), ?_⟩
  intro j hj
  -- Any smaller index cannot lie in the support, by minimality of `i`.
  by_contra hjnz
  have hjmem : j ∈ d.support := Finsupp.mem_support_iff.mpr hjnz
  exact (not_lt_of_ge (Finset.min'_le d.support j hjmem)) hj

/-- Helper for Lemma 15.39.2: a power series with zero constant coefficient splits as
`∑ᵢ Xᵢ * gᵢ`, where `gᵢ` collects the monomials whose first nonzero index is `i`. This is the
explicit decomposition behind the maximal-ideal-generation argument for the coordinate variables. -/
private theorem mvPowerSeries_fin_field_sum_X_mul_firstIndexSlice
    (f : P) (hconst : MvPowerSeries.constantCoeff f = 0) :
    (∑ i, (MvPowerSeries.X i : P) *
        mvPowerSeries_fin_field_firstIndexSlice (K := K) f i) = f :=
by
  classical
  ext d
  -- Compare the coefficient of each monomial and isolate the unique first nonzero index.
  by_cases hd : d = 0
  · subst hd
    -- The constant coefficient vanishes on both sides because `f` lies in the maximal ideal.
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hconst,
      MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
  · rcases mvPowerSeries_fin_field_exists_least_support_index (n := n) hd with
      ⟨i, hdi, hmin⟩
    have hsingle_le : Finsupp.single i 1 ≤ d := by
      intro j
      by_cases hji : j = i
      · subst hji
        simpa using Nat.succ_le_of_lt (Nat.pos_of_ne_zero hdi)
      · simp [Finsupp.single_eq_of_ne hji]
    have hi_term :
        ((MvPowerSeries.X i : P) * mvPowerSeries_fin_field_firstIndexSlice (K := K) f i).coeff d =
          f.coeff d := by
      -- For the least support index, subtracting one `X i` leaves a slice satisfying the guard.
      rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, if_pos hsingle_le, one_mul]
      have hslice :
          ∀ j : Fin n, j < i → ((d - Finsupp.single i 1 : Fin n →₀ ℕ) j) = 0 := by
        intro j hj
        have hji : j ≠ i := ne_of_lt hj
        simp [Finsupp.sub_apply, Finsupp.single_eq_of_ne hji, hmin j hj]
      simp [mvPowerSeries_fin_field_firstIndexSlice, hslice, tsub_add_cancel_of_le hsingle_le]
    have hother :
        ∀ j : Fin n,
          j ≠ i →
            ((MvPowerSeries.X j : P) * mvPowerSeries_fin_field_firstIndexSlice (K := K) f j).coeff d = 0 := by
      intro j hji
      by_cases hsingle : Finsupp.single j 1 ≤ d
      · rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, if_pos hsingle, one_mul]
        rcases lt_or_gt_of_ne hji with hji_lt | hij_lt
        · -- A smaller index than `i` cannot occur in the support of `d`.
          have hjpos : 1 ≤ d j := by
            simpa using hsingle j
          have : False := by
            simpa [hmin j hji_lt] using hjpos
          exact this.elim
        · -- A larger index than `i` fails the slice guard because `d i` is still nonzero.
          have hi_coord :
              ((d - Finsupp.single j 1 : Fin n →₀ ℕ) i) = d i := by
            simp [Finsupp.sub_apply, Finsupp.single_eq_of_ne hji.symm]
          have hguard :
              ¬ ∀ k : Fin n, k < j → ((d - Finsupp.single j 1 : Fin n →₀ ℕ) k) = 0 := by
            intro hguard
            exact hdi <| by
              simpa [hi_coord] using hguard i hij_lt
          simp [mvPowerSeries_fin_field_firstIndexSlice, hguard]
      · rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, if_neg hsingle]
    -- The coefficient sum collapses to the unique least-support slice.
    have hcoeff_sum :
        (∑ i, (MvPowerSeries.X i : P) *
            mvPowerSeries_fin_field_firstIndexSlice (K := K) f i).coeff d =
          ∑ i,
            ((MvPowerSeries.X i : P) * mvPowerSeries_fin_field_firstIndexSlice (K := K) f i).coeff d := by
      simpa using
        (MvPowerSeries.coeff d).map_sum
          (fun i ↦
            (MvPowerSeries.X i : P) * mvPowerSeries_fin_field_firstIndexSlice (K := K) f i)
          Finset.univ
    rw [hcoeff_sum]
    rw [Finset.sum_eq_single i]
    · simpa using hi_term
    · intro j _ hji
      simpa using hother j hji
    · intro hi
      exact (hi (Finset.mem_univ i)).elim

/-- Helper for Lemma 15.39.2: if a power series has vanishing constant term and vanishing
degree-one coefficients, then it lies in `maximalIdeal²`. The proof follows the source route by
factoring off one coordinate variable from each monomial and then observing that the remaining
slice still has zero constant term. -/
private theorem
    mvPowerSeries_fin_field_mem_maximalIdeal_sq_of_constantCoeff_eq_zero_of_degreeOne_eq_zero
    (f : P) (hconst : MvPowerSeries.constantCoeff f = 0)
    (hdegreeOne : ∀ k : Fin n, f.coeff (Finsupp.single k 1) = 0) :
    f ∈ maximalIdeal P ^ 2 := by
  let g : Fin n → P := mvPowerSeries_fin_field_firstIndexSlice (K := K) f
  have hdecomp :
      (∑ i, (MvPowerSeries.X i : P) * g i) = f := by
    -- First split `f` according to the first nonzero index of each monomial.
    simpa [g] using
      mvPowerSeries_fin_field_sum_X_mul_firstIndexSlice (K := K) f hconst
  have hgmem : ∀ i : Fin n, g i ∈ maximalIdeal P := by
    intro i
    -- The slice has zero constant coefficient because the corresponding degree-one coefficient of
    -- `f` vanishes by hypothesis.
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have hslice0 : MvPowerSeries.constantCoeff (g i) = 0 := by
      simpa [g] using
        (mvPowerSeries_fin_field_constantCoeff_firstIndexSlice (K := K) f i).trans (hdegreeOne i)
    have hunitCoeff : IsUnit (MvPowerSeries.constantCoeff (g i)) :=
      MvPowerSeries.isUnit_constantCoeff _ hunit
    simpa [hslice0] using hunitCoeff
  rw [← hdecomp]
  -- Each summand is a product of two maximal-ideal elements, hence lies in `maximalIdeal²`.
  refine (maximalIdeal P ^ 2).sum_mem ?_
  intro i hi
  have hXi : (MvPowerSeries.X i : P) ∈ maximalIdeal P :=
    mvPowerSeries_fin_field_X_mem_maximalIdeal (K := K) i
  have hg : g i ∈ maximalIdeal P := hgmem i
  simpa [pow_two, mul_comm] using Ideal.mul_mem_mul hXi hg

/-- Helper for Lemma 15.39.2: if an algebra endomorphism preserves the maximal ideal, then it is
the identity on the residue field, so every element changes by something in the maximal ideal. -/
private theorem mvPowerSeries_fin_field_sub_mem_maximalIdeal_of_comap_maximalIdeal
    (ψ : P →ₐ[K] P)
    (hψm : maximalIdeal P ≤ (maximalIdeal P).comap ψ)
    (g : P) :
    ψ g - g ∈ maximalIdeal P := by
  let g₀ : P := g - MvPowerSeries.C (MvPowerSeries.constantCoeff g)
  have hg₀const : MvPowerSeries.constantCoeff g₀ = 0 := by
    -- Removing the constant term produces a series in the maximal ideal.
    simp [g₀]
  have hg₀mem : g₀ ∈ maximalIdeal P := by
    -- Over a field, vanishing constant coefficient is equivalent to maximal-ideal membership.
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hg₀unit
    have hunitCoeff : IsUnit (MvPowerSeries.constantCoeff g₀) :=
      MvPowerSeries.isUnit_constantCoeff _ hg₀unit
    simpa [hg₀const] using hunitCoeff
  have hψg₀mem : ψ g₀ ∈ maximalIdeal P := hψm hg₀mem
  have hψC :
      ψ (MvPowerSeries.C (MvPowerSeries.constantCoeff g)) =
        MvPowerSeries.C (MvPowerSeries.constantCoeff g) := by
    -- A `K`-algebra endomorphism fixes constants.
    simpa [MvPowerSeries.c_eq_algebraMap] using ψ.commutes (MvPowerSeries.constantCoeff g)
  have hsplit :
      ψ g - g = ψ g₀ - g₀ := by
    -- Rewrite both copies of `g` as `g₀` plus its constant part and cancel that constant.
    calc
      ψ g - g = ψ (g₀ + MvPowerSeries.C (MvPowerSeries.constantCoeff g)) -
          (g₀ + MvPowerSeries.C (MvPowerSeries.constantCoeff g)) := by
            congr 1 <;> simp [g₀]
      _ = (ψ g₀ + ψ (MvPowerSeries.C (MvPowerSeries.constantCoeff g))) -
          (g₀ + MvPowerSeries.C (MvPowerSeries.constantCoeff g)) := by
            rw [map_add]
      _ = (ψ g₀ + MvPowerSeries.C (MvPowerSeries.constantCoeff g)) -
          (g₀ + MvPowerSeries.C (MvPowerSeries.constantCoeff g)) := by
            rw [hψC]
      _ = ψ g₀ - g₀ := by
            simpa using add_sub_add_right_eq_sub (ψ g₀) g₀
              (MvPowerSeries.C (MvPowerSeries.constantCoeff g))
  -- Both `g₀` and `ψ g₀` lie in the maximal ideal, so their difference does too.
  rw [hsplit]
  exact Ideal.sub_mem (maximalIdeal P) hψg₀mem hg₀mem

/-- Helper for Lemma 15.39.2: if a substitution endomorphism fixes each coordinate variable modulo
`maximalIdeal²`, then it fixes every element of the maximal ideal modulo `maximalIdeal²`. This is
the first ideal-filtration upgrade in the source proof. -/
private theorem
    mvPowerSeries_fin_field_sub_mem_maximalIdeal_sq_of_mem_maximalIdeal_of_normalized_generators
    (ψ : P →ₐ[K] P)
    (hψm : maximalIdeal P ≤ (maximalIdeal P).comap ψ)
    (hψsq : ∀ i : Fin n, ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P) ∈ maximalIdeal P ^ 2)
    {f : P} (hf : f ∈ maximalIdeal P) :
    ψ f - f ∈ maximalIdeal P ^ 2 :=
by
  classical
  let g : Fin n → P := mvPowerSeries_fin_field_firstIndexSlice (K := K) f
  have hconst : MvPowerSeries.constantCoeff f = 0 := field_constantCoeff_eq_zero (K := K) ⟨f, hf⟩
  have hdecomp :
      (∑ i, (MvPowerSeries.X i : P) * g i) = f := by
    -- Split `f` according to the least index appearing in each monomial.
    simpa [g] using
      mvPowerSeries_fin_field_sum_X_mul_firstIndexSlice (K := K) f hconst
  have hsummand :
      ∀ i : Fin n,
        ψ ((MvPowerSeries.X i : P) * g i) - ((MvPowerSeries.X i : P) * g i) ∈
          maximalIdeal P ^ 2 := by
    intro i
    have hXi : (MvPowerSeries.X i : P) ∈ maximalIdeal P :=
      mvPowerSeries_fin_field_X_mem_maximalIdeal (K := K) i
    have hgdiff : ψ (g i) - g i ∈ maximalIdeal P :=
      mvPowerSeries_fin_field_sub_mem_maximalIdeal_of_comap_maximalIdeal
        (K := K) ψ hψm (g i)
    have hfirst :
        (ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P)) * ψ (g i) ∈
          maximalIdeal P ^ 2 := by
      -- Multiplying an `maximalIdeal²` element by anything stays inside `maximalIdeal²`.
      exact (maximalIdeal P ^ 2).mul_mem_right (ψ (g i)) (hψsq i)
    have hsecond :
        (MvPowerSeries.X i : P) * (ψ (g i) - g i) ∈ maximalIdeal P ^ 2 := by
      -- This is the product of two maximal-ideal elements.
      simpa [pow_two, mul_comm] using Ideal.mul_mem_mul hXi hgdiff
    have hprod_sub :
        ψ ((MvPowerSeries.X i : P) * g i) - ((MvPowerSeries.X i : P) * g i) =
          (ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P)) * ψ (g i) +
            (MvPowerSeries.X i : P) * (ψ (g i) - g i) := by
      -- Expand the difference of products in the source-faithful tangent-to-identity form.
      calc
        ψ ((MvPowerSeries.X i : P) * g i) - ((MvPowerSeries.X i : P) * g i) =
            ψ (MvPowerSeries.X i : P) * ψ (g i) - ((MvPowerSeries.X i : P) * g i) := by
              rw [map_mul]
        _ = (ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P)) * ψ (g i) +
            (MvPowerSeries.X i : P) * (ψ (g i) - g i) := by
              ring
    rw [hprod_sub]
    exact Ideal.add_mem _ hfirst hsecond
  have hsum :
      ψ (∑ i, (MvPowerSeries.X i : P) * g i) - ∑ i, (MvPowerSeries.X i : P) * g i ∈
        maximalIdeal P ^ 2 := by
    -- Rewrite the total difference as the sum of the controlled summandwise differences.
    have hsum' :
        ∑ i,
            (ψ ((MvPowerSeries.X i : P) * g i) -
              ((MvPowerSeries.X i : P) * g i)) ∈
          maximalIdeal P ^ 2 := by
      exact (maximalIdeal P ^ 2).sum_mem fun i _ ↦ hsummand i
    simpa [map_sum, Finset.sum_sub_distrib] using hsum'
  simpa [hdecomp] using hsum

/-- Helper for Lemma 15.39.2: if a normalized substitution endomorphism is tangent to the
identity modulo `maximalIdeal²` on generators, then it improves the `maximalIdeal`-adic
filtration by one step on every power. -/
/-- Helper for Lemma 15.39.2: for any ideal, multiplying its square by its `m`-th power gives the
`(m + 2)`-nd power. -/
private theorem ideal_pow_two_mul_pow_eq_pow_add_two
    (I : Ideal P) (m : ℕ) :
    I ^ 2 * I ^ m = I ^ (m + 2) := by
  -- Rewrite both sides through the recursive power formula `I^(k + 1) = I * I^k`.
  calc
    I ^ 2 * I ^ m = (I * I) * I ^ m := by rw [pow_two]
    _ = I * (I * I ^ m) := by rw [mul_assoc]
    _ = I * I ^ (m + 1) := by rw [← pow_succ']
    _ = I ^ (m + 2) := by
          simpa [Nat.add_assoc] using (pow_succ' I (m + 1)).symm

/-- Helper for Lemma 15.39.2: for any ideal, multiplying it by its `(m + 1)`-st power gives the
`(m + 2)`-nd power. -/
private theorem ideal_mul_pow_succ_eq_pow_add_two
    (I : Ideal P) (m : ℕ) :
    I * I ^ (m + 1) = I ^ (m + 2) := by
  -- This is the recursive power identity at the next stage.
  simpa [Nat.add_assoc] using (pow_succ' I (m + 1)).symm

private theorem
    mvPowerSeries_fin_field_sub_mem_maximalIdeal_pow_succ_of_normalized_generators
    (ψ : P →ₐ[K] P)
    (hψm : maximalIdeal P ≤ (maximalIdeal P).comap ψ)
    (hψsq : ∀ i : Fin n, ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P) ∈ maximalIdeal P ^ 2) :
    ∀ m : ℕ, ∀ {f : P}, f ∈ maximalIdeal P ^ m → ψ f - f ∈ maximalIdeal P ^ (m + 1) := by
  intro m
  induction m with
  | zero =>
      intro f hf
      -- At stage `m = 0`, the source proof starts with the residue-field identity of `ψ`.
      simpa [pow_zero, pow_one] using
        mvPowerSeries_fin_field_sub_mem_maximalIdeal_of_comap_maximalIdeal
          (K := K) ψ hψm f
  | succ m ihm =>
      intro f hf
      have hf' : f ∈ maximalIdeal P * maximalIdeal P ^ m := by
        simpa [pow_succ'] using hf
      -- Expand elements of `maximalIdeal^(m+1)` as sums of products and control each product
      -- term by the tangent-to-identity formula.
      refine Submodule.mul_induction_on hf' ?_ ?_
      · intro a ha b hb
        have ha2 :
            ψ a - a ∈ maximalIdeal P ^ 2 :=
          mvPowerSeries_fin_field_sub_mem_maximalIdeal_sq_of_mem_maximalIdeal_of_normalized_generators
            (K := K) ψ hψm hψsq ha
        have hbnext :
            ψ b - b ∈ maximalIdeal P ^ (m + 1) :=
          ihm hb
        have hbmem : ψ b ∈ maximalIdeal P ^ m := by
          have hbdiff : ψ b - b ∈ maximalIdeal P ^ m :=
            (Ideal.pow_le_pow_right (Nat.le_succ m)) hbnext
          -- The inductive error term already lies in the current filtration step.
          simpa [sub_eq_add_neg, add_assoc] using (maximalIdeal P ^ m).add_mem hbdiff hb
        have hfirst :
            (ψ a - a) * ψ b ∈ maximalIdeal P ^ (m + 2) := by
          have hmul : (ψ a - a) * ψ b ∈ maximalIdeal P ^ 2 * maximalIdeal P ^ m :=
            Ideal.mul_mem_mul ha2 hbmem
          rw [ideal_pow_two_mul_pow_eq_pow_add_two (I := maximalIdeal P) (m := m)]
          exact hmul
        have hsecond :
            a * (ψ b - b) ∈ maximalIdeal P ^ (m + 2) := by
          have hmul : a * (ψ b - b) ∈ maximalIdeal P * maximalIdeal P ^ (m + 1) :=
            Ideal.mul_mem_mul ha hbnext
          rw [ideal_mul_pow_succ_eq_pow_add_two (I := maximalIdeal P) (m := m)]
          exact hmul
        have hprod_sub :
            ψ (a * b) - a * b =
              (ψ a - a) * ψ b + a * (ψ b - b) := by
          -- This is the standard source-proof identity comparing `ψ(ab)` with `ab`.
          calc
            ψ (a * b) - a * b = ψ a * ψ b - a * b := by
              rw [map_mul]
            _ = (ψ a - a) * ψ b + a * (ψ b - b) := by
              ring
        rw [hprod_sub]
        exact Ideal.add_mem _ hfirst hsecond
      · intro a b ha hb
        -- The filtration estimate is additive, so sums stay in the same step.
        simpa [map_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (maximalIdeal P ^ (m + 2)).add_mem ha hb

/-- Helper for Lemma 15.39.2: once the normalized endomorphism improves the `maximalIdeal`-adic
filtration by one step, its action on every power-quotient is bijective because the induced
difference from the identity is nilpotent. -/
private theorem mvPowerSeries_fin_field_powQuotient_bijective_of_normalized_subst
    (ψ : P →ₐ[K] P)
    (hψpow :
      ∀ m : ℕ, ∀ {f : P}, f ∈ maximalIdeal P ^ m → ψ f - f ∈ maximalIdeal P ^ (m + 1))
    (hψstable :
      ∀ m : ℕ, maximalIdeal P ^ m ≤ (maximalIdeal P ^ m).comap ψ) :
    ∀ m : ℕ,
      Function.Bijective
        ((Ideal.quotientMap (maximalIdeal P ^ m) ψ.toRingHom (hψstable m)) :
          P ⧸ maximalIdeal P ^ m →+* P ⧸ maximalIdeal P ^ m) := by
  -- TODO: source-faithful next step. Prove by induction on `m` that the quotient endomorphism
  -- `qψ_m : P ⧸ maximalIdeal^m → P ⧸ maximalIdeal^m` is bijective. Use the transition map
  -- `P ⧸ maximalIdeal^(m+1) → P ⧸ maximalIdeal^m`, show `qψ_(m+1)` commutes with it, and prove
  -- that `qψ_(m+1)` is the identity on the kernel
  -- `maximalIdeal^m / maximalIdeal^(m+1)` via `hψpow m`.
  sorry

/-- Helper for Lemma 15.39.2: substituting by the inverse linear family undoes the original
linear change on each coordinate variable. -/
private theorem mvPowerSeries_fin_field_subst_linearFamily_inv_apply
    (L : Matrix (Fin n) (Fin n) K) (hL : IsUnit L.det) (i : Fin n) :
    MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹)
        (mvPowerSeries_fin_field_linearFamily (K := K) L i) =
      (MvPowerSeries.X i : P) := by
  -- This is the previous matrix-multiplication rule with the inverse matrix.
  rw [mvPowerSeries_fin_field_subst_linearFamily_mul_apply (K := K) L L⁻¹ i,
    mvPowerSeries_fin_field_linearFamily, Matrix.mul_nonsing_inv _ hL]
  simpa [Matrix.one_apply]

/-- Helper for Lemma 15.39.2: substituting by the original linear family also undoes the inverse
linear change on each coordinate variable. -/
private theorem mvPowerSeries_fin_field_subst_inv_linearFamily_apply
    (L : Matrix (Fin n) (Fin n) K) (hL : IsUnit L.det) (i : Fin n) :
    MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L)
        (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹ i) =
      (MvPowerSeries.X i : P) := by
  -- Use the same computation but multiply in the opposite order.
  rw [mvPowerSeries_fin_field_subst_linearFamily_mul_apply (K := K) L⁻¹ L i,
    mvPowerSeries_fin_field_linearFamily, Matrix.nonsing_inv_mul _ hL]
  simpa [Matrix.one_apply]

/-- Helper for Lemma 15.39.2: an invertible linear change of variables gives a bijective
substitution endomorphism of `K[[x_1, \ldots, x_n]]`. -/
private theorem mvPowerSeries_fin_field_linear_substAlgEquiv_of_isUnit_det
    (L : Matrix (Fin n) (Fin n) K) (hL : IsUnit L.det) :
    Function.Bijective
      ((MvPowerSeries.substAlgHom
        (mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) L)) : P →ₐ[K] P) := by
  refine ⟨?_, ?_⟩
  · intro f g hfg
    have hfg' :
        MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L) f =
          MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L) g := by
      simpa [MvPowerSeries.substAlgHom_apply] using hfg
    -- Apply the inverse linear substitution to both sides and use the left-inverse computation.
    have hleftf :
        MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹)
            (MvPowerSeries.subst (R := K)
              (mvPowerSeries_fin_field_linearFamily (K := K) L) f) = f := by
      let h1 := mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) L
      let h2 := mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) L⁻¹
      calc
        MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹)
            (MvPowerSeries.subst (R := K)
              (mvPowerSeries_fin_field_linearFamily (K := K) L) f) =
          MvPowerSeries.subst (R := K)
            (fun i ↦ MvPowerSeries.subst (R := K)
              (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹)
              (mvPowerSeries_fin_field_linearFamily (K := K) L i)) f := by
                simpa using MvPowerSeries.subst_comp_subst_apply h1 h2 f
        _ = MvPowerSeries.subst (R := K) (fun i ↦ (MvPowerSeries.X i : P)) f := by
              congr 1
              funext i
              exact mvPowerSeries_fin_field_subst_linearFamily_inv_apply (K := K) L hL i
        _ = f := by
              simpa using congrFun (MvPowerSeries.subst_self (σ := Fin n) (R := K)) f
    have hleftg :
        MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹)
            (MvPowerSeries.subst (R := K)
              (mvPowerSeries_fin_field_linearFamily (K := K) L) g) = g := by
      let h1 := mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) L
      let h2 := mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) L⁻¹
      calc
        MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹)
            (MvPowerSeries.subst (R := K)
              (mvPowerSeries_fin_field_linearFamily (K := K) L) g) =
          MvPowerSeries.subst (R := K)
            (fun i ↦ MvPowerSeries.subst (R := K)
              (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹)
              (mvPowerSeries_fin_field_linearFamily (K := K) L i)) g := by
                simpa using MvPowerSeries.subst_comp_subst_apply h1 h2 g
        _ = MvPowerSeries.subst (R := K) (fun i ↦ (MvPowerSeries.X i : P)) g := by
              congr 1
              funext i
              exact mvPowerSeries_fin_field_subst_linearFamily_inv_apply (K := K) L hL i
        _ = g := by
              simpa using congrFun (MvPowerSeries.subst_self (σ := Fin n) (R := K)) g
    rw [← hleftf, ← hleftg, hfg']
  · intro f
    refine ⟨MvPowerSeries.subst (R := K)
      (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹) f, ?_⟩
    -- The inverse matrix provides an explicit preimage for every target series.
    have hright :
        MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L)
            (MvPowerSeries.subst (R := K)
              (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹) f) = f := by
      let h1 := mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) L
      let h2 := mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) L⁻¹
      calc
        MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L)
            (MvPowerSeries.subst (R := K)
              (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹) f) =
          MvPowerSeries.subst (R := K)
            (fun i ↦ MvPowerSeries.subst (R := K)
              (mvPowerSeries_fin_field_linearFamily (K := K) L)
              (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹ i)) f := by
                simpa using MvPowerSeries.subst_comp_subst_apply h2 h1 f
        _ = MvPowerSeries.subst (R := K) (fun i ↦ (MvPowerSeries.X i : P)) f := by
              congr 1
              funext i
              exact mvPowerSeries_fin_field_subst_inv_linearFamily_apply (K := K) L hL i
        _ = f := by
              simpa using congrFun (MvPowerSeries.subst_self (σ := Fin n) (R := K)) f
    simpa [MvPowerSeries.substAlgHom_apply] using hright

-- Proof sketch: the source-facing map is the canonical substitution map owned by
-- `MvPowerSeries.substAlgHom`; bijectivity is the content of the lemma.
/-- Lemma 15.39.2 (1): if `y₁, …, yₙ` is a regular system of parameters of
`K[[x_1, \ldots, x_n]]`, then the canonical substitution map
`K[[X_1, \ldots, X_n]] → K[[x_1, \ldots, x_n]]` sending `Xᵢ` to `yᵢ` is bijective. -/
@[stacks 07NM]
theorem mvPowerSeries_fin_field_substAlgHom_bijective_of_regularSystemOfParameters
    (y : Fin n → maximalIdeal P)
    (hy : IsRegularSystemOfParameters y) :
    Function.Bijective
      ((MvPowerSeries.substAlgHom
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ field_constantCoeff_eq_zero (y i))) :
          P →ₐ[K] P) := by
  let L : Matrix (Fin n) (Fin n) K := mvPowerSeries_fin_field_linearCoeffMatrix (K := K) y
  let φ : P →ₐ[K] P :=
    MvPowerSeries.substAlgHom
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ field_constantCoeff_eq_zero (y i))
  let τ : P →ₐ[K] P :=
    MvPowerSeries.substAlgHom
      (mvPowerSeries_fin_field_linearFamily_hasSubst (K := K) L⁻¹)
  let ψ : P →ₐ[K] P := τ.comp φ
  have hstable :
      ∀ m : ℕ, maximalIdeal P ^ m ≤ (maximalIdeal P ^ m).comap φ := by
    intro m
    -- This is the easy half of the adic-complete upgrade: substitution by maximal-ideal
    -- parameters preserves the `maximalIdeal`-adic filtration.
    simpa [φ] using mvPowerSeries_fin_field_substAlgHom_pow_le_comap y m
  have hlinear :
      IsUnit L.det := by
    -- The already-verified coordinate representations now give an actual left inverse to the
    -- linear coefficient matrix, so its determinant is a unit.
    simpa [L] using mvPowerSeries_fin_field_linear_part_isUnit_det (K := K) y hy
  let τFamily : Fin n → maximalIdeal P := fun i ↦
    ⟨mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹ i,
      mvPowerSeries_fin_field_linearFamily_mem_maximalIdeal (K := K) L⁻¹ i⟩
  have hτLinear :
      mvPowerSeries_fin_field_linearCoeffMatrix (K := K) τFamily = L⁻¹ := by
    -- The chosen normalizing family really has linear part `L⁻¹`, so it is the source-faithful
    -- inverse linear change of variables promised by the proof plan.
    simpa [τFamily] using mvPowerSeries_fin_field_linearCoeffMatrix_linearFamily (K := K) L⁻¹
  have hτInv :
      IsUnit (L⁻¹).det := by
    -- Inverting a unit determinant still gives a unit determinant for the normalizing matrix.
    rw [Matrix.det_nonsing_inv]
    exact isUnit_ringInverse.mpr hlinear
  have hτbij : Function.Bijective τ := by
    -- The inverse linear family defines the explicit normalizing automorphism from the source
    -- proof.
    simpa [τ] using
      mvPowerSeries_fin_field_linear_substAlgEquiv_of_isUnit_det (K := K) L⁻¹ hτInv
  have hreduce : Function.Bijective ψ → Function.Bijective φ := by
    intro hψ
    refine ⟨?_, ?_⟩
    · intro f g hfg
      apply hψ.1
      simpa [ψ, τ] using congrArg τ hfg
    · intro f
      rcases hψ.2 (τ f) with ⟨g, hg⟩
      refine ⟨g, ?_⟩
      apply hτbij.1
      simpa [ψ, τ] using hg
  -- Route correction: the explicit linear change-of-variables step is now available via
  -- `mvPowerSeries_fin_field_linear_substAlgEquiv_of_isUnit_det`; the remaining blocker is now
  -- isolated to the normalized endomorphism `ψ = τ ∘ φ`, which should be tangent to the identity.
  apply hreduce
  have hψorder :
      ∀ i : Fin n, (2 : ℕ∞) ≤ (ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P)).order := by
    intro i
    have hnormalized :
        (2 : ℕ∞) ≤
          (MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹)
              (y i) -
            (MvPowerSeries.X i : P)).order := by
      -- The source-faithful normalization already gives identity linear part on the generators.
      refine mvPowerSeries_fin_field_normalized_subst_order_ge_two (K := K) y L⁻¹ ?_ i
      -- The inverse matrix was chosen precisely to normalize the linear coefficient matrix.
      simpa [L] using Matrix.mul_nonsing_inv L hlinear
    have hψX :
        ψ (MvPowerSeries.X i : P) =
          MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹)
            (y i) := by
      have hφX : φ (MvPowerSeries.X i : P) = y i := by
        -- The original substitution sends the `i`-th coordinate variable to the chosen parameter.
        simpa [φ] using
          (MvPowerSeries.substAlgHom_X
            (MvPowerSeries.hasSubst_of_constantCoeff_zero
              fun j ↦ field_constantCoeff_eq_zero (K := K) (y j))
            i)
      have hτ_apply (f : P) :
          τ f =
            MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹) f := by
        simp [τ, MvPowerSeries.substAlgHom_apply]
      -- Expanding `ψ = τ ∘ φ` on a generator reduces the inner substitution to `y i`.
      calc
        ψ (MvPowerSeries.X i : P) = τ (φ (MvPowerSeries.X i : P)) := by
          rfl
        _ = τ (y i) := by rw [hφX]
        _ = MvPowerSeries.subst (R := K) (mvPowerSeries_fin_field_linearFamily (K := K) L⁻¹)
              (y i) := hτ_apply (y i)
    -- Expand `ψ = τ ∘ φ` on `X i` to reach the normalized substituted parameter.
    rwa [hψX]
  have hψcoeff :
      ∀ i : Fin n,
        MvPowerSeries.constantCoeff (ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P)) = 0 ∧
          ∀ k : Fin n,
            (ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P)).coeff
              (Finsupp.single k 1) = 0 := by
    intro i
    -- The normalized order estimate is now unpacked into the concrete constant/linear vanishing
    -- data needed for the cotangent or associated-graded step.
    exact
      mvPowerSeries_fin_field_constantCoeff_eq_zero_and_degreeOne_eq_zero_of_order_ge_two
        (K := K)
        (f := ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P))
        (horder := hψorder i)
  have hψsq :
      ∀ i : Fin n,
        ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P) ∈ maximalIdeal P ^ 2 := by
    intro i
    -- The newly proved coefficient-to-ideal bridge turns the normalized order estimate into the
    -- desired `maximalIdeal²` control on each generator difference.
    exact
      mvPowerSeries_fin_field_mem_maximalIdeal_sq_of_constantCoeff_eq_zero_of_degreeOne_eq_zero
        (K := K)
        (f := ψ (MvPowerSeries.X i : P) - (MvPowerSeries.X i : P))
        (hconst := (hψcoeff i).1)
        (hdegreeOne := (hψcoeff i).2)
  have hτstable :
      ∀ m : ℕ, maximalIdeal P ^ m ≤ (maximalIdeal P ^ m).comap τ := by
    intro m
    -- The inverse linear change is still substitution by maximal-ideal elements.
    simpa [τ, τFamily] using mvPowerSeries_fin_field_substAlgHom_pow_le_comap (K := K) τFamily m
  have hψm :
      maximalIdeal P ≤ (maximalIdeal P).comap ψ := by
    intro f hf
    have hφf : φ f ∈ maximalIdeal P := by
      simpa [pow_one] using hstable 1 (by simpa [pow_one] using hf)
    have hτφf : τ (φ f) ∈ maximalIdeal P := by
      simpa [pow_one] using hτstable 1 (by simpa [pow_one] using hφf)
    simpa [ψ] using hτφf
  have hψpow :
      ∀ m : ℕ, ∀ {f : P}, f ∈ maximalIdeal P ^ m → ψ f - f ∈ maximalIdeal P ^ (m + 1) := by
    -- This is the source-proof filtration upgrade from generator control.
    exact
      mvPowerSeries_fin_field_sub_mem_maximalIdeal_pow_succ_of_normalized_generators
        (K := K) ψ hψm hψsq
  have hψstable :
      ∀ m : ℕ, maximalIdeal P ^ m ≤ (maximalIdeal P ^ m).comap ψ := by
    intro m f hf
    have hdiff : ψ f - f ∈ maximalIdeal P ^ (m + 1) := hψpow m hf
    have hdiff' : ψ f - f ∈ maximalIdeal P ^ m :=
      (Ideal.pow_le_pow_right (Nat.le_succ m)) hdiff
    -- Rewrite `ψ f` as `(ψ f - f) + f` and keep both terms in the current filtration piece.
    simpa [sub_eq_add_neg, add_assoc] using (maximalIdeal P ^ m).add_mem hdiff' hf
  -- TODO: once quotientwise bijectivity is established in
  -- `mvPowerSeries_fin_field_powQuotient_bijective_of_normalized_subst`, feed it into
  -- `adicComplete_endomorphism_bijective_of_powQuotient_bijective` to conclude that the
  -- normalized endomorphism `ψ` is bijective, and then unwind `hreduce`.
  sorry

/-- Lemma 15.39.2 (2), inequality clause: if `z₁, …, zᵣ` is part of a regular system of
parameters of `K[[x_1, \ldots, x_n]]`, then `r ≤ n`. -/
@[stacks 07NM]
theorem mvPowerSeries_fin_field_part_regularSystemOfParameters_le
    {r : ℕ}
    (z : Fin r → maximalIdeal P)
    (hz : IsPartOfRegularSystemOfParameters n z) :
    r ≤ n := by
  -- Route correction: bound the prefix length through the regular-sequence dimension formula,
  -- rather than through the harder full automorphism construction.
  have hreg : RingTheory.Sequence.IsRegular P (List.ofFn fun i ↦ (z i : P)) :=
    IsPartOfRegularSystemOfParameters.isRegular hz
  -- The quotient by a regular sequence lowers Krull dimension by its length.
  have hdim :
      ringKrullDim (P ⧸ Ideal.ofList (List.ofFn fun i ↦ (z i : P))) + ↑r =
        ringKrullDim P := by
    simpa [List.length_ofFn] using
      ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
        (R := P) (rs := List.ofFn fun i ↦ (z i : P)) hreg
  have hP : ringKrullDim P = ↑n := by
    simpa using ringKrullDim_mvPowerSeries_fin_field K n
  rcases WithBot.add_eq_coe.mp (hdim.trans hP) with ⟨d, e, hd, he, hde⟩
  have he' : e = (r : ℕ∞) := WithBot.coe_eq_coe.mp (he.trans rfl)
  -- The right summand of a finite sum in `ℕ∞` is bounded by the total.
  have hle : e ≤ d + e := by
    exact le_add_of_nonneg_left (show (0 : ℕ∞) ≤ d from bot_le)
  rw [hde, he'] at hle
  exact ENat.coe_le_coe.mp hle

-- Internal presentation map used to construct the canonical quotient algebra equivalence.
private noncomputable def
    mvPowerSeries_fin_field_quotientPresentationMap_of_regularSystemOfParameters_append
    {r : ℕ}
    (z : Fin r → maximalIdeal P)
    (y : Fin (n - r) → maximalIdeal P) :
    MvPowerSeries (Fin (n - r)) K →ₐ[K] P ⧸ parameterIdeal z :=
  (Ideal.Quotient.mkₐ K (parameterIdeal z)).comp
    ((MvPowerSeries.substAlgHom
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ field_constantCoeff_eq_zero (y i))) :
        MvPowerSeries (Fin (n - r)) K →ₐ[K] P)

-- The internal presentation map above is bijective for an appended regular system of parameters.
private theorem
    mvPowerSeries_fin_field_quotientPresentationMap_bijective_of_regularSystemOfParameters_append
    {r : ℕ}
    (z : Fin r → maximalIdeal P)
    (y : Fin (n - r) → maximalIdeal P)
    (hy : IsRegularSystemOfParameters (Fin.append z y)) :
    Function.Bijective
      (mvPowerSeries_fin_field_quotientPresentationMap_of_regularSystemOfParameters_append z y) :=
  -- TODO: transport the standard quotient by the first `r` coordinates along the full-system
  -- automorphism from `mvPowerSeries_fin_field_substAlgHom_bijective_of_regularSystemOfParameters`.
  sorry

/-- The quotient by the ideal generated by the prefix `z` is canonically isomorphic to a formal
power series ring in the complementary variables. -/
noncomputable def mvPowerSeries_fin_field_quotientAlgEquiv_of_regularSystemOfParameters_append
    {r : ℕ}
    (z : Fin r → maximalIdeal P)
    (y : Fin (n - r) → maximalIdeal P)
    (hy : IsRegularSystemOfParameters (Fin.append z y)) :
    (P ⧸ parameterIdeal z) ≃ₐ[K] MvPowerSeries (Fin (n - r)) K :=
  (AlgEquiv.ofBijective
      (mvPowerSeries_fin_field_quotientPresentationMap_of_regularSystemOfParameters_append z y)
      (mvPowerSeries_fin_field_quotientPresentationMap_bijective_of_regularSystemOfParameters_append
        z y hy)).symm

/-- The canonical quotient presentation sends the class of each complementary parameter `yᵢ` to
the corresponding coordinate variable. -/
theorem mvPowerSeries_fin_field_quotientAlgEquiv_of_regularSystemOfParameters_append_apply
    {r : ℕ}
    (z : Fin r → maximalIdeal P)
    (y : Fin (n - r) → maximalIdeal P)
    (hy : IsRegularSystemOfParameters (Fin.append z y))
    (i : Fin (n - r)) :
    mvPowerSeries_fin_field_quotientAlgEquiv_of_regularSystemOfParameters_append z y hy
      (Ideal.Quotient.mk (parameterIdeal z) (y i : P)) = X i := by
  -- Compute the forward presentation map on the coordinate variable `X i`.
  have hforward :
      (mvPowerSeries_fin_field_quotientAlgEquiv_of_regularSystemOfParameters_append z y hy).symm
        (X i) =
          Ideal.Quotient.mk (parameterIdeal z) (y i : P) := by
    change
      mvPowerSeries_fin_field_quotientPresentationMap_of_regularSystemOfParameters_append z y
        (X i) =
          Ideal.Quotient.mk (parameterIdeal z) (y i : P)
    rw [mvPowerSeries_fin_field_quotientPresentationMap_of_regularSystemOfParameters_append]
    rw [AlgHom.comp_apply, MvPowerSeries.substAlgHom_X]
    rfl
  -- Invert the quotient presentation equivalence to move back to the source variable.
  exact
    ((AlgEquiv.symm_apply_eq
      (mvPowerSeries_fin_field_quotientAlgEquiv_of_regularSystemOfParameters_append z y hy)).1
      hforward).symm

/-- Lemma 15.39.2 (2): if `z₁, …, zᵣ` is part of a regular system of parameters of
`K[[x_1, \ldots, x_n]]`, then there is a complementary tail `y` and a `K`-algebra isomorphism from
the quotient by the ideal they generate to a formal power series ring in `n - r` variables over
`K`, carrying the classes of the `yᵢ` to the coordinate variables. -/
@[stacks 07NM]
theorem exists_quotient_mvPowerSeries_fin_field_algEquiv_of_part_regularSystemOfParameters
    {r : ℕ}
    (z : Fin r → maximalIdeal P)
    (hz : IsPartOfRegularSystemOfParameters n z) :
    ∃ y : Fin (n - r) → maximalIdeal P,
      ∃ φ : (P ⧸ parameterIdeal z) ≃ₐ[K] MvPowerSeries (Fin (n - r)) K,
        ∀ i, φ (Ideal.Quotient.mk (parameterIdeal z) (y i : P)) = X i := by
  rcases hz with ⟨y, hy⟩
  exact ⟨
    y,
    mvPowerSeries_fin_field_quotientAlgEquiv_of_regularSystemOfParameters_append z y hy,
    mvPowerSeries_fin_field_quotientAlgEquiv_of_regularSystemOfParameters_append_apply z y hy
  ⟩

end

section

variable {Λ : Type u} [CommRing Λ] [IsCohenRing Λ] {n : ℕ}

open IsCohenRing

local notation "P" => MvPowerSeries (Fin n) Λ

private def mixedResidueCharParameter : maximalIdeal P :=
  ⟨algebraMap Λ P (ringChar (ResidueField Λ)), by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    simpa [MvPowerSeries.c_eq_algebraMap, isUnit_iff_constantCoeff] using
      (residueChar_not_isUnit : ¬ IsUnit (ringChar (ResidueField Λ) : Λ))⟩

local instance : TopologicalSpace Λ := Ideal.adicTopology (maximalIdeal Λ)
local instance : UniformSpace Λ := IsTopologicalAddGroup.rightUniformSpace Λ
local instance : IsUniformAddGroup Λ := isUniformAddGroup_of_addCommGroup
local instance : IsTopologicalRing Λ := by infer_instance
local instance : WithIdeal Λ := ⟨maximalIdeal Λ⟩
local instance : CompleteSpace Λ :=
  (IsAdic.isAdicComplete_iff (show IsAdic (maximalIdeal Λ) by rfl)).mp
    (inferInstance : IsAdicComplete (maximalIdeal Λ) Λ) |>.1
local instance : T2Space Λ :=
  (IsAdic.isAdicComplete_iff (show IsAdic (maximalIdeal Λ) by rfl)).mp
    (inferInstance : IsAdicComplete (maximalIdeal Λ) Λ) |>.2

local notation "pP" => mixedResidueCharParameter

private theorem mixed_hasEval {σ : Type*} [Finite σ] (y : σ → maximalIdeal P) :
    MvPowerSeries.HasEval (fun i ↦ (y i : P)) := by
  refine ⟨?_, ?_⟩
  · intro i
    have hconst_mem : constantCoeff (y i : P) ∈ maximalIdeal Λ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hunit
      have hy_nonunit : ¬ IsUnit (y i : P) := by
        intro hy_unit
        exact (IsLocalRing.notMem_maximalIdeal.mpr hy_unit) (y i).2
      exact hy_nonunit <| isUnit_iff_constantCoeff.2 hunit
    exact MvPowerSeries.LinearTopology.isTopologicallyNilpotent_of_constantCoeff <|
      WithIdeal.isTopologicallyNilpotent_of_mem hconst_mem
  · rw [Filter.cofinite_eq_bot]
    exact
      (Filter.tendsto_bot :
        Filter.Tendsto (fun i ↦ (y i : P)) ⊥ (𝓝 (0 : P)))

private theorem isRegularSystemOfParameters_comp_cast
    {d d' : ℕ} (x : Fin d → maximalIdeal P) (h : d' = d) :
    IsRegularSystemOfParameters (x ∘ Fin.cast h) ↔ IsRegularSystemOfParameters x := by
  subst h
  simp

-- Proof sketch: the source-facing map is the canonical complete-local evaluation map owned by
-- `MvPowerSeries.aeval`; bijectivity is the content of the lemma.
/-- Lemma 15.39.2 (3): let `p = ringChar (ResidueField Λ)` generate the maximal ideal of the Cohen
ring `Λ`. If `p, y₁, …, yₙ` is a regular system of parameters of `Λ[[x_1, \ldots, x_n]]`, then the
canonical `Λ`-algebra evaluation map from `Λ[[X_1, \ldots, X_n]]` sending `Xᵢ` to `yᵢ` is
bijective. -/
@[stacks 07NM]
theorem mvPowerSeries_fin_cohenRing_aeval_bijective_of_regularSystemOfParameters
    (y : Fin n → maximalIdeal P)
    (hy : IsRegularSystemOfParameters
      (Fin.cons pP y)) :
    -- TODO: reduce the evaluation map modulo `pP`, identify the closed fiber with a residue-field
    -- power-series ring, apply the finished field theorem there, and lift the inverse through
    -- `int_to_mvPowerSeries_over_cohenRing_formally_smooth_for_madic`.
    Function.Bijective
      ((MvPowerSeries.aeval (mixed_hasEval y)) : MvPowerSeries (Fin n) Λ →ₐ[Λ] P) := sorry

/-- Lemma 15.39.2 (4), inequality clause: let `p = ringChar (ResidueField Λ)` generate the maximal
ideal of the Cohen ring `Λ`. If `p, z₁, …, zᵣ` is part of a regular system of parameters of
`Λ[[x_1, \ldots, x_n]]`, then `r ≤ n`. -/
@[stacks 07NM]
theorem mvPowerSeries_fin_cohenRing_part_regularSystemOfParameters_le
    {r : ℕ} (z : Fin r → maximalIdeal P)
    (hz : IsPartOfRegularSystemOfParameters (n + 1) (Fin.cons pP z)) :
    r ≤ n := by
  let w : Fin (r + 1) → maximalIdeal P := Fin.cons pP z
  have hreg : RingTheory.Sequence.IsRegular P
      (List.ofFn fun i : Fin (r + 1) ↦ (w i : P)) := by
    simpa [w] using IsPartOfRegularSystemOfParameters.isRegular hz
  rcases hz with ⟨y, hy⟩
  -- As in the field case, the regular sequence cuts the Krull dimension by its length.
  have hdim :
      ringKrullDim
          (P ⧸ Ideal.ofList (List.ofFn fun i : Fin (r + 1) ↦ (w i : P))) + ↑(r + 1) =
        ringKrullDim P := by
    simpa [List.length_ofFn] using
      ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
        (R := P) (rs := List.ofFn fun i : Fin (r + 1) ↦ (w i : P)) hreg
  have hP : ringKrullDim P = ↑(n + 1) := by
    -- The extension witness in `hz` is already a full regular system of total length `n + 1`.
    exact hy.1.1
  rw [hP] at hdim
  rcases WithBot.add_eq_coe.mp hdim with ⟨d, e, hd, he, hde⟩
  have he' : e = ((r + 1 : ℕ) : ℕ∞) := WithBot.coe_eq_coe.mp (he.trans rfl)
  -- The right summand of a finite sum in `ℕ∞` is bounded by the total.
  have hle : e ≤ d + e := by
    exact le_add_of_nonneg_left (show (0 : ℕ∞) ≤ d from bot_le)
  rw [hde, he'] at hle
  exact Nat.succ_le_succ_iff.mp <| ENat.coe_le_coe.mp hle

-- Internal presentation map used to construct the canonical quotient algebra equivalence.
private noncomputable def
    mvPowerSeries_fin_cohenRing_quotientPresentationMap_of_regularSystemOfParameters_append
    {r : ℕ}
    (z : Fin r → maximalIdeal P)
    (y : Fin (n - r) → maximalIdeal P) :
    MvPowerSeries (Fin (n - r)) Λ →ₐ[Λ] P ⧸ parameterIdeal z :=
  (Ideal.Quotient.mkₐ Λ (parameterIdeal z)).comp
    ((MvPowerSeries.aeval (mixed_hasEval y)) : MvPowerSeries (Fin (n - r)) Λ →ₐ[Λ] P)

-- The internal presentation map above is bijective for an appended regular system of parameters.
private theorem
    mvPowerSeries_fin_cohenRing_quotientPresentationMap_bijective_of_regularSystemOfParameters_append
    {r : ℕ} (z : Fin r → maximalIdeal P)
    (y : Fin (n - r) → maximalIdeal P)
    (hy : IsRegularSystemOfParameters (Fin.append (Fin.cons pP z) y)) :
    Function.Bijective
      (mvPowerSeries_fin_cohenRing_quotientPresentationMap_of_regularSystemOfParameters_append
        z y) := by
  -- TODO: after the mixed-characteristic automorphism is available, transport the standard
  -- quotient by the first `r` variables exactly as in the field case, identifying the prefix ideal
  -- through `parameterIdeal_append_comp_castLE_left`.
  sorry

/-- The quotient by the ideal generated by the prefix `z` is canonically isomorphic to a formal
power series ring in the complementary variables. -/
noncomputable def mvPowerSeries_fin_cohenRing_quotientAlgEquiv_of_regularSystemOfParameters_append
    {r : ℕ} (z : Fin r → maximalIdeal P)
    (y : Fin (n - r) → maximalIdeal P)
    (hy : IsRegularSystemOfParameters (Fin.append (Fin.cons pP z) y)) :
    (P ⧸ parameterIdeal z) ≃ₐ[Λ] MvPowerSeries (Fin (n - r)) Λ :=
  (AlgEquiv.ofBijective
      (mvPowerSeries_fin_cohenRing_quotientPresentationMap_of_regularSystemOfParameters_append
        z y)
      (mvPowerSeries_fin_cohenRing_quotientPresentationMap_bijective_of_regularSystemOfParameters_append
        z y hy)).symm

/-- The canonical quotient presentation sends the class of each complementary parameter `yᵢ` to
the corresponding coordinate variable. -/
theorem mvPowerSeries_fin_cohenRing_quotientAlgEquiv_of_regularSystemOfParameters_append_apply
    {r : ℕ} (z : Fin r → maximalIdeal P)
    (y : Fin (n - r) → maximalIdeal P)
    (hy : IsRegularSystemOfParameters (Fin.append (Fin.cons pP z) y))
    (i : Fin (n - r)) :
    mvPowerSeries_fin_cohenRing_quotientAlgEquiv_of_regularSystemOfParameters_append z y hy
      (Ideal.Quotient.mk (parameterIdeal z) (y i : P)) = X i := by
  -- Compute the forward presentation map on the coordinate variable `X i`.
  have hforward :
      (mvPowerSeries_fin_cohenRing_quotientAlgEquiv_of_regularSystemOfParameters_append z y hy).symm
        (X i) =
          Ideal.Quotient.mk (parameterIdeal z) (y i : P) := by
    change
      mvPowerSeries_fin_cohenRing_quotientPresentationMap_of_regularSystemOfParameters_append z y
        (X i) =
          Ideal.Quotient.mk (parameterIdeal z) (y i : P)
    rw [mvPowerSeries_fin_cohenRing_quotientPresentationMap_of_regularSystemOfParameters_append]
    rw [AlgHom.comp_apply, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X]
    rfl
  -- Invert the quotient presentation equivalence to recover the source variable.
  exact
    ((AlgEquiv.symm_apply_eq
      (mvPowerSeries_fin_cohenRing_quotientAlgEquiv_of_regularSystemOfParameters_append z y hy)).1
      hforward).symm

/-- Lemma 15.39.2 (4): let `p = ringChar (ResidueField Λ)` generate the maximal ideal of the Cohen
ring `Λ`. If `p, z₁, …, zᵣ` is part of a regular system of parameters of
`Λ[[x_1, \ldots, x_n]]`, then there is a complementary tail `y` and a `Λ`-algebra isomorphism
from the quotient by the ideal generated by the `zᵢ` to a formal power series ring in `n - r`
variables over `Λ`, carrying the classes of the `yᵢ` to the coordinate variables. -/
@[stacks 07NM]
theorem exists_quotient_mvPowerSeries_fin_cohenRing_algEquiv_of_part_regularSystemOfParameters
    {r : ℕ} (z : Fin r → maximalIdeal P)
    (hz : IsPartOfRegularSystemOfParameters (n + 1) (Fin.cons pP z)) :
    ∃ y : Fin (n - r) → maximalIdeal P,
      ∃ φ : (P ⧸ parameterIdeal z) ≃ₐ[Λ] MvPowerSeries (Fin (n - r)) Λ,
        ∀ i, φ (Ideal.Quotient.mk (parameterIdeal z) (y i : P)) = X i := by
  have hz' : ∃ y : Fin (n - r) → maximalIdeal P,
      IsRegularSystemOfParameters (Fin.append (Fin.cons pP z) y) := by
    -- The owner `hz` already provides the needed complementary tail; only the arithmetic
    -- simplification `n + 1 - (r + 1) = n - r` remains.
    simpa only [Nat.succ_sub_succ_eq_sub] using hz
  rcases hz' with ⟨y, hy⟩
  exact ⟨
    y,
    mvPowerSeries_fin_cohenRing_quotientAlgEquiv_of_regularSystemOfParameters_append z y hy,
    mvPowerSeries_fin_cohenRing_quotientAlgEquiv_of_regularSystemOfParameters_append_apply
      z y hy
  ⟩

end
