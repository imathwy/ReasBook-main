import Mathlib
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.LinearTopology
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_39_1 (from Chap15) -/
open IsLocalRing
open scoped Topology

universe u v w

section

/- Domain-style sampling for Lemma 15.39.1:
- primary domain: adic formal smoothness of coefficient maps into finite-variable formal power
  series rings over fields and Cohen rings.
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`,
  * `Algebra.formallySmooth_of_charZero`,
  * `Algebra.formallySmooth_of_isSeparableOver`,
  * `cohenRing_zmodPow_quotient_algebraMap_formallySmooth`.
- best owner abstraction: `RingHom.formally_smooth_for_adic` is the chapter owner for the adic
  lifting property used here, and the project’s canonical owner for “finitely many variables” is
  `MvPowerSeries σ _` with `[Finite σ]`, not the coordinate encoding `Fin n`;
  field-theoretic formal smoothness and the Cohen-ring quotient results are upstream bridge inputs
  rather than separate local owners.
- primitive data: the coefficient field or Cohen ring together with its characteristic
  hypotheses.
- derived API: the three maximal-ideal-adic formal smoothness statements for the corresponding
  multivariable formal power series rings.

Source/core/bridge triage:
- `source-facing`: the three textbook cases in Lemma 15.39.1.
- `core/canonical`: `Algebra.FormallySmooth` and the owner theorem
  `RingHom.formally_smooth_for_adic`.
- `bridge/view`: passage from the coefficient-ring formal smoothness statements to the power-series
  targets.
-/

section CharZeroField

variable {σ : Type v} [Finite σ] (K : Type u) [Field K] [CharZero K]

local notation "P" => MvPowerSeries σ K

-- Proof sketch: first use Proposition `10.158.9` to see that `ℚ → K` is formally smooth for a
-- characteristic-zero field `K`. Then apply the universal property of the finite-variable formal
-- power series ring to lift maps coefficientwise, giving formal smoothness for the maximal-ideal
-- adic topology on `MvPowerSeries σ K`.
/-- Lemma 15.39.1 (1): if `K` is a field of characteristic zero, then the canonical map
`ℚ → K[[x_i]]`, formalized as `algebraMap ℚ (MvPowerSeries σ K)` for a finite variable set `σ`, is
formally
smooth in the `maximalIdeal`-adic topology. -/
theorem rational_to_mvPowerSeries_formally_smooth_for_madic
    : RingHom.formally_smooth_for_adic (algebraMap ℚ P) (maximalIdeal P) := sorry

end CharZeroField

section CharPField

variable {σ : Type v} [Finite σ] (L : Type u) [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]

local instance : Algebra (ZMod p) L := ZMod.algebra L p
local notation "P" => MvPowerSeries σ L

-- Proof sketch: by Proposition `10.158.9`, a field `L` of characteristic `p` is formally smooth
-- over `𝔽_p = ZMod p`. The universal property of the finite-variable formal power series ring then
-- upgrades this coefficientwise lifting property to the maximal-ideal adic topology on
-- `MvPowerSeries σ L`.
/-- Lemma 15.39.1 (2): if `L` is a field of characteristic `p > 0`, then the canonical map
`𝔽_p → L[[x_i]]`, formalized as `algebraMap (ZMod p) (MvPowerSeries σ L)` for a finite variable
set `σ`, is formally smooth in the `maximalIdeal`-adic topology. -/
theorem zmod_to_mvPowerSeries_formally_smooth_for_madic
    : RingHom.formally_smooth_for_adic (algebraMap (ZMod p) P) (maximalIdeal P) := by
  sorry

end CharPField

section CohenRing

variable {σ : Type v} [Finite σ] (Λ : Type u) [CommRing Λ] [IsCohenRing Λ]

local notation "P" => MvPowerSeries σ Λ

-- Proof sketch: choose the prime `p` generating the maximal ideal of the Cohen ring `Λ`. Lemma
-- `10.160.7` gives formal smoothness of the maps `ZMod (p^m) → Λ ⧸ (p^m)` for all `m > 0`, and
-- Lemma `10.160.7` together with Definition `15.37.1` implies `ℤ → Λ` is formally smooth in the
-- `maximalIdeal Λ`-adic topology. The universal property of finite-variable formal power series
-- then yields the corresponding statement for `MvPowerSeries σ Λ`.
/-- Lemma 15.39.1 (3): if `Λ` is a Cohen ring, then the canonical map
`ℤ → Λ[[x_i]]`, formalized as `algebraMap ℤ (MvPowerSeries σ Λ)` for a finite variable set `σ`, is
formally
smooth in the `maximalIdeal`-adic topology. -/
theorem int_to_mvPowerSeries_over_cohenRing_formally_smooth_for_madic
    : RingHom.formally_smooth_for_adic (algebraMap ℤ P) (maximalIdeal P) := sorry

end CohenRing

end

/-! ### Lemma_15_39_2 (from Chap15) -/
noncomputable section

universe u

open IsLocalRing MvPowerSeries
open scoped Topology
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

-- Proof sketch: the source-facing map is the canonical substitution map owned by
-- `MvPowerSeries.substAlgHom`; bijectivity is the content of the lemma.
/-- Lemma 15.39.2 (1): if `y₁, …, yₙ` is a regular system of parameters of
`K[[x_1, \ldots, x_n]]`, then the canonical substitution map
`K[[X_1, \ldots, X_n]] → K[[x_1, \ldots, x_n]]` sending `Xᵢ` to `yᵢ` is bijective. -/
theorem mvPowerSeries_fin_field_substAlgHom_bijective_of_regularSystemOfParameters
    (y : Fin n → maximalIdeal P)
    (hy : IsRegularSystemOfParameters y) :
    Function.Bijective
      ((MvPowerSeries.substAlgHom
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i ↦ field_constantCoeff_eq_zero (y i))) :
          P →ₐ[K] P) :=
  sorry

/-- Lemma 15.39.2 (2), inequality clause: if `z₁, …, zᵣ` is part of a regular system of
parameters of `K[[x_1, \ldots, x_n]]`, then `r ≤ n`. -/
theorem mvPowerSeries_fin_field_part_regularSystemOfParameters_le
    {r : ℕ}
    (z : Fin r → maximalIdeal P)
    (hz : IsPartOfRegularSystemOfParameters n z) :
    r ≤ n := sorry

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
      (Ideal.Quotient.mk (parameterIdeal z) (y i : P)) = X i := sorry

/-- Lemma 15.39.2 (2): if `z₁, …, zᵣ` is part of a regular system of parameters of
`K[[x_1, \ldots, x_n]]`, then there is a complementary tail `y` and a `K`-algebra isomorphism from
the quotient by the ideal they generate to a formal power series ring in `n - r` variables over
`K`, carrying the classes of the `yᵢ` to the coordinate variables. -/
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
theorem mvPowerSeries_fin_cohenRing_aeval_bijective_of_regularSystemOfParameters
    (y : Fin n → maximalIdeal P)
    (hy : IsRegularSystemOfParameters
      (Fin.cons pP y)) :
    Function.Bijective
      ((MvPowerSeries.aeval (mixed_hasEval y)) : MvPowerSeries (Fin n) Λ →ₐ[Λ] P) := sorry

/-- Lemma 15.39.2 (4), inequality clause: let `p = ringChar (ResidueField Λ)` generate the maximal
ideal of the Cohen ring `Λ`. If `p, z₁, …, zᵣ` is part of a regular system of parameters of
`Λ[[x_1, \ldots, x_n]]`, then `r ≤ n`. -/
theorem mvPowerSeries_fin_cohenRing_part_regularSystemOfParameters_le
    {r : ℕ} (z : Fin r → maximalIdeal P)
    (hz : IsPartOfRegularSystemOfParameters (n + 1) (Fin.cons pP z)) :
    r ≤ n := sorry

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
        z y) := sorry

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
      (Ideal.Quotient.mk (parameterIdeal z) (y i : P)) = X i := sorry

/-- Lemma 15.39.2 (4): let `p = ringChar (ResidueField Λ)` generate the maximal ideal of the Cohen
ring `Λ`. If `p, z₁, …, zᵣ` is part of a regular system of parameters of
`Λ[[x_1, \ldots, x_n]]`, then there is a complementary tail `y` and a `Λ`-algebra isomorphism
from the quotient by the ideal generated by the `zᵢ` to a formal power series ring in `n - r`
variables over `Λ`, carrying the classes of the `yᵢ` to the coordinate variables. -/
theorem exists_quotient_mvPowerSeries_fin_cohenRing_algEquiv_of_part_regularSystemOfParameters
    {r : ℕ} (z : Fin r → maximalIdeal P)
    (hz : IsPartOfRegularSystemOfParameters (n + 1) (Fin.cons pP z)) :
    ∃ y : Fin (n - r) → maximalIdeal P,
      ∃ φ : (P ⧸ parameterIdeal z) ≃ₐ[Λ] MvPowerSeries (Fin (n - r)) Λ,
        ∀ i, φ (Ideal.Quotient.mk (parameterIdeal z) (y i : P)) = X i := by
  have hz' : ∃ y : Fin (n - r) → maximalIdeal P,
      IsRegularSystemOfParameters (Fin.append (Fin.cons pP z) y) := by
    rcases hz with ⟨y, hy⟩
    have hnr : n + 1 - (r + 1) = n - r := Nat.succ_sub_succ_eq_sub n r
    have hlen : r + 1 + (n - r) = r + 1 + (n + 1 - (r + 1)) := by
      rw [hnr.symm]
    let ytail : Fin (n - r) → maximalIdeal P := y ∘ Fin.cast hnr.symm
    refine ⟨ytail, ?_⟩
    have happend :
        Fin.append (Fin.cons pP z) ytail =
          Fin.append (Fin.cons pP z) y ∘ Fin.cast hlen := by
      simpa [ytail] using
        (Fin.append_cast_right (Fin.cons pP z) y (n - r) hnr.symm)
    rw [happend]
    exact (isRegularSystemOfParameters_comp_cast (Fin.append (Fin.cons pP z) y) hlen).2 hy
  rcases hz' with ⟨y, hy⟩
  exact ⟨
    y,
    mvPowerSeries_fin_cohenRing_quotientAlgEquiv_of_regularSystemOfParameters_append z y hy,
    mvPowerSeries_fin_cohenRing_quotientAlgEquiv_of_regularSystemOfParameters_append_apply
      z y hy
  ⟩

end

/-! ### Lemma_15_39_3 (from Chap15) -/
open IsLocalRing
open CategoryTheory CommRingCat

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B]
variable (f : A →+* B) [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsCompleteLocalRing A] [IsCompleteLocalRing B] [IsLocalHom f]

/- Domain-style sampling for Lemma 15.39.3:
- primary domain: local homomorphisms of Noetherian complete local rings presented by finite-index
  formal power series rings;
- sampled owner declarations:
  * `exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic`,
  * `exists_powerSeries_model_of_regular_completeLocalRing`,
  * `IsRegularSystemOfParameters`,
  * `IsPartOfRegularSystemOfParameters`;
- source/core/bridge triage:
  * `source-facing`: the existence of a commutative power-series presentation for a local map
    `A → B` with the parameter clause from the source and the flat/regular-fiber consequences used
    later in the chapter;
  * `core/canonical`: `MvPowerSeries σ R` with `[Finite σ]`, the owner predicates
    `IsRegularSystemOfParameters` and `IsPartOfRegularSystemOfParameters`, together with
    `RingHom.Flat`, `Ideal.Fiber`, and `IsRegularLocalRing`;
  * `bridge/view`: the chosen surjective maps `P → A`, `Q → B`, and `P → Q` forming the
    comparison square.
- best owner abstraction: the canonical owners here are the power-series rings themselves together
  with the regular-parameter predicates. The public theorem surface should therefore expose those
  primitive clauses directly instead of hiding them behind a local packaging predicate, and the
  equal-characteristic field branch should be stated with the canonical equal-characteristic
  condition rather than the narrower `CharZero` special case.
- primitive data: finite source and target variable types, coefficient field or Cohen-ring data,
  the three ring maps in the commutative square, and a chosen regular system of parameters on the
  source, indexed by `(maximalIdeal P).spanFinrank`, whose image is part of one on the target.
- derived API: flatness of the vertical map `rToS.Flat` and regularity of the closed fiber
  `(maximalIdeal P).Fiber Q`. -/

-- Proof sketch: in equal characteristic, use the Chapter 10 residue-field presentation owner
-- `exists_ringEquiv_mvPowerSeries_residueField_of_equalCharacteristic` on the regular complete
-- local source and target presentation rings; in residue characteristic `p > 0`, use the Chapter
-- 10 Cohen-ring owner `exists_powerSeries_model_of_regular_completeLocalRing`. In both cases
-- Lemmas `15.39.1` and `15.37.5` produce the comparison map `P → Q`, and the parameter,
-- flatness, and regular-fiber clauses are then expressed directly by the canonical owners
-- `IsRegularSystemOfParameters`, `IsPartOfRegularSystemOfParameters`, `RingHom.Flat`, and
-- `IsRegularLocalRing`.
/-- Lemma 15.39.3: a local homomorphism `A → B` of Noetherian complete local rings admits a
commutative surjective presentation by finite-index formal power series rings in which a regular
system of parameters of the source maps to part of one on the target, the vertical map is flat,
and its closed fiber is regular local. In equal characteristic the coefficient rings can be taken
to be fields; in residue characteristic `p > 0` they can be taken to be Cohen rings. -/
theorem exists_powerSeries_presentation_of_localHom_completeLocal :
    (∃ _ : ringChar A = ringChar (ResidueField A),
      ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
        (K L : Type u) (_ : Field K) (_ : Field L),
        let P := MvPowerSeries σ K
        let Q := MvPowerSeries τ L
        ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
          let _ : Algebra P Q := rToS.toAlgebra
          Function.Surjective rToA ∧
            Function.Surjective sToB ∧
            CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
            (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
              (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                IsRegularSystemOfParameters x ∧
                  (∀ i, rToS (x i : P) = (z i : Q)) ∧
                  IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
            rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q))
      ∨
      ∃ (p : ℕ) (_ : Nat.Prime p), CharP (ResidueField A) p ∧
        ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
          (R₀ S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
          (_ : IsCohenRing R₀) (_ : IsCohenRing S₀),
          let P := MvPowerSeries σ R₀
          let Q := MvPowerSeries τ S₀
          ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
            let _ : Algebra P Q := rToS.toAlgebra
            Function.Surjective rToA ∧
              Function.Surjective sToB ∧
              CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
              (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
                (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
                  IsRegularSystemOfParameters x ∧
                    (∀ i, rToS (x i : P) = (z i : Q)) ∧
                    IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
              rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  sorry

-- Proof sketch: this is the equal-characteristic branch of Lemma `15.39.3`, matching the Chapter
-- 10 field-presentation owner in arbitrary equal characteristic.
/-- Equal-characteristic companion to Lemma 15.39.3: if `A` has the same characteristic as its
residue field, then the coefficient rings in the presentation can be taken to be fields. -/
theorem exists_field_powerSeries_presentation_of_localHom_completeLocal
    (hAeqchar : ringChar A = ringChar (ResidueField A)) :
    ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
      (K L : Type u) (_ : Field K) (_ : Field L),
      let P := MvPowerSeries σ K
      let Q := MvPowerSeries τ L
      ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
        let _ : Algebra P Q := rToS.toAlgebra
        Function.Surjective rToA ∧
          Function.Surjective sToB ∧
          CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
          (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
            (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
              IsRegularSystemOfParameters x ∧
                (∀ i, rToS (x i : P) = (z i : Q)) ∧
                IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
          rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  sorry

-- Proof sketch: in positive residue characteristic, use the Cohen structure theorem to present
-- both `A` and `B` as quotients of finite-index power series rings over Cohen rings. As above,
-- Lemmas `15.39.1` and `15.37.5` lift the composite source presentation to the target power
-- series ring, and the parameter clause is expressed through the canonical owner
-- `IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank` after reordering the chosen
-- target regular system. Flatness and regularity of the closed fiber are then the same canonical
-- consequences as in the equal-characteristic case.
/-- Positive-residue-characteristic companion to Lemma 15.39.3: if the residue field of `A` has
characteristic `p > 0`, then the coefficient rings in the presentation can be taken to be Cohen
rings. -/
theorem exists_cohen_powerSeries_presentation_of_localHom_completeLocal
    (p : ℕ) (hp : Nat.Prime p) (hAp : CharP (ResidueField A) p) :
    ∃ (σ τ : Type u) (_ : Finite σ) (_ : Finite τ)
      (R₀ S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀)
      (_ : IsCohenRing R₀) (_ : IsCohenRing S₀),
      let P := MvPowerSeries σ R₀
      let Q := MvPowerSeries τ S₀
      ∃ (rToA : P →+* A) (sToB : Q →+* B) (rToS : P →+* Q),
        let _ : Algebra P Q := rToS.toAlgebra
        Function.Surjective rToA ∧
          Function.Surjective sToB ∧
          CommSq (ofHom rToS) (ofHom rToA) (ofHom sToB) (ofHom f) ∧
          (∃ (x : Fin (maximalIdeal P).spanFinrank → maximalIdeal P)
            (z : Fin (maximalIdeal P).spanFinrank → maximalIdeal Q),
              IsRegularSystemOfParameters x ∧
                (∀ i, rToS (x i : P) = (z i : Q)) ∧
                IsPartOfRegularSystemOfParameters (maximalIdeal Q).spanFinrank z) ∧
          rToS.Flat ∧ IsRegularLocalRing ((maximalIdeal P).Fiber Q) := by
  sorry

end

/-! ### Lemma_15_39_4 (from Chap15) -/
universe u

open IsLocalRing

section

variable {R S S' : Type u}
variable [CommRing R] [CommRing S] [CommRing S']
variable [IsCompleteLocalRing S] [IsNoetherianRing S]
variable [IsCompleteLocalRing S'] [IsNoetherianRing S']

/- Domain-style sampling:
- primary domain: surjective pullbacks of complete Noetherian local rings;
- sampled owner declarations:
  `IsCompleteLocalRing`,
  `quotient_isCompleteLocalRing`,
  `IsLocalRing.of_surjective'`,
  `Function.Surjective.isLocalHom`;
- best owner abstraction: the chapter pullback owner `SurjectiveRingPullbackSituation` with its
  derived fibre-product ring `Bprime`;
- primitive data: the two complete Noetherian local source rings `S`, `S'`, the pullback owner
  `T : SurjectiveRingPullbackSituation S R S'`, the built-in surjectivity of `T.fromAprime`, and
  the remaining surjectivity hypothesis on `T.toA`;
- derived API: `R` is a local ring by `IsLocalRing.of_surjective'` applied to `T.fromAprime`, both
  maps to `R` are local by `Function.Surjective.isLocalHom`, `R` is complete local and Noetherian as a
  quotient of `S'`, and the fibre-product ring `T.Bprime` is complete local and Noetherian.

Source/core/bridge triage:
- `source-facing`: the fibre-product ring of two surjective local maps to a common complete local
  base;
- `core/canonical`: the predicates `IsCompleteLocalRing` and `IsNoetherianRing`;
- `bridge/view`: `SurjectiveRingPullbackSituation`, which packages the surjective pullback owner
  already used earlier in the chapter. -/

-- Proof sketch: first note that `R` is already a local ring by surjectivity of
-- `T.fromAprime : S' → R`, and then both maps `T.toA` and `T.fromAprime` are local by the
-- canonical surjective-local API. The same surjective map `T.fromAprime` exhibits `R` as a
-- quotient of the complete Noetherian local ring `S'`, so `R` is complete local and Noetherian.
-- Then realize the fibre product `S ×_R S'` as the categorical pullback of `T.toA` and
-- `T.fromAprime`. Using the Cohen-structure-theorem argument from the source, one gets a
-- surjection from a formal power series ring onto this pullback ring; hence it is complete local.
-- The same presentation shows the pullback is a quotient of a power series ring over a Cohen ring
-- or residue field, hence Noetherian as well.
namespace SurjectiveRingPullbackSituation

variable (T : SurjectiveRingPullbackSituation S R S') (h_toA : Function.Surjective T.toA)

/-- Lemma 15.39.4: if `S → R` and `S' → R` are surjective local homomorphisms of complete
Noetherian local rings, then the fibre product `S ×_R S'`, formalized by the canonical pullback
owner `T.Bprime`, is again a complete local ring. -/
theorem bprime_isCompleteLocalRing_of_surjective :
    IsCompleteLocalRing T.Bprime := by
  sorry

/-- Under the same hypotheses, the pullback ring `T.Bprime = S ×_R S'` is Noetherian. -/
theorem bprime_isNoetherianRing_of_surjective :
    IsNoetherianRing T.Bprime := by
  sorry

end SurjectiveRingPullbackSituation

end
