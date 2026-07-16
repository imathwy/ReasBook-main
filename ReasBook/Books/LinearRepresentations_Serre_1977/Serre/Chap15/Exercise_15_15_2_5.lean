import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise

universe u v w x

namespace Representation

section StableLatticeRigidity

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {G : Type w} [Monoid G]
variable {E : Type x} [AddCommGroup E] [Module A E]

section FractionRingAmbient

variable {K : Type v} [CommRing K] [Algebra A K] [IsFractionRing A K]
variable [Module K E] [IsScalarTower A K E]

namespace StableLattice

/-- Helper for Exercise 15-15.2-5: after clearing finitely many denominator coordinates, some
homothetic copy of one stable lattice is contained in the other. -/
theorem exists_smul_le_of_lattices_monoid
    {ρ : Representation K G E} (L₁ L₂ : StableLattice A ρ) :
    ∃ a : Kˣ, (a • L₂).toSubmodule ≤ L₁.toSubmodule := by
  classical
  letI : Field K := IsFractionRing.toField (A := A) (K := K)
  letI : Module.IsTorsionFree A K :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := A) (A := K)).2
      (IsFractionRing.injective A K)
  let b₁ : Module.Basis (Module.Free.ChooseBasisIndex A L₁.toSubmodule) A L₁.toSubmodule :=
    Module.Free.chooseBasis A L₁.toSubmodule
  let e₁ : Module.Basis (Module.Free.ChooseBasisIndex A L₁.toSubmodule) K E :=
    b₁.extendOfIsLattice K
  let b₂ : Module.Basis (Module.Free.ChooseBasisIndex A L₂.toSubmodule) A L₂.toSubmodule :=
    Module.Free.chooseBasis A L₂.toSubmodule
  let coeff :
      Module.Free.ChooseBasisIndex A L₂.toSubmodule ×
          Module.Free.ChooseBasisIndex A L₁.toSubmodule → K :=
    fun ij ↦ e₁.repr ((b₂ ij.1 : L₂.toSubmodule) : E) ij.2
  -- Clear the finitely many coefficient denominators that describe the basis of `L₂`
  -- in the `K`-basis induced from `L₁`.
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (M := nonZeroDivisors A) coeff
  let a : Kˣ := (IsLocalization.map_units K d).unit
  refine ⟨a, ?_⟩
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  let yL₂ : L₂.toSubmodule := ⟨y, hy⟩
  change (algebraMap A K d) • (yL₂ : E) ∈ L₁.toSubmodule
  have hbasis_mem (i : Module.Free.ChooseBasisIndex A L₂.toSubmodule) :
      (algebraMap A K d) • ((b₂ i : L₂.toSubmodule) : E) ∈ L₁.toSubmodule := by
    let c : Module.Free.ChooseBasisIndex A L₁.toSubmodule → A :=
      fun j ↦ Classical.choose (hd (i, j))
    let z : L₁.toSubmodule := ∑ j, c j • b₁ j
    -- Reassemble the cleared coefficients along the `A`-basis of `L₁`.
    have hz : ((z : L₁.toSubmodule) : E) = (algebraMap A K d) • ((b₂ i : L₂.toSubmodule) : E) := by
      calc
        ((z : L₁.toSubmodule) : E)
            = ∑ j, (algebraMap A K (c j)) • (((b₁ j : L₁.toSubmodule) : E)) := by
                simp [z, c]
        _ = ∑ j, e₁.repr ((algebraMap A K d) • (((b₂ i : L₂.toSubmodule) : E))) j • e₁ j := by
              apply Finset.sum_congr rfl
              intro j _
              have hc : algebraMap A K (c j) =
                  e₁.repr ((algebraMap A K d) • (((b₂ i : L₂.toSubmodule) : E))) j := by
                calc
                  algebraMap A K (c j) = (algebraMap A K d) * coeff (i, j) := by
                    simpa [c, Algebra.smul_def] using (Classical.choose_spec (hd (i, j)))
                  _ = e₁.repr ((algebraMap A K d) • (((b₂ i : L₂.toSubmodule) : E))) j := by
                    simpa [coeff, Algebra.smul_def] using
                      ((congrArg (fun f => f j)
                        (LinearEquiv.map_smul e₁.repr (algebraMap A K d)
                          (((b₂ i : L₂.toSubmodule) : E)))).symm)
              simpa [e₁, Module.Basis.extendOfIsLattice_apply] using
                congrArg (fun t => t • (((b₁ j : L₁.toSubmodule) : E))) hc
        _ = (algebraMap A K d) • ((b₂ i : L₂.toSubmodule) : E) := by
              simpa [e₁, Module.Basis.extendOfIsLattice_apply] using
                (e₁.sum_repr ((algebraMap A K d) • (((b₂ i : L₂.toSubmodule) : E))))
    exact hz ▸ z.property
  have hy_expand_sub : (∑ i, (b₂.repr yL₂ i : A) • b₂ i : L₂.toSubmodule) = yL₂ := by
    simpa using b₂.sum_repr yL₂
  -- Expand `y` in the `A`-basis of `L₂` and use the basiswise containment just proved.
  rw [← hy_expand_sub]
  change (algebraMap A K d) •
        (((∑ i, (b₂.repr yL₂ i : A) • b₂ i : L₂.toSubmodule) : L₂.toSubmodule) : E) ∈
      L₁.toSubmodule
  simp_rw [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ ?_
  intro i _
  simpa [smul_smul, mul_comm] using
    L₁.toSubmodule.smul_mem (b₂.repr yL₂ i) (hbasis_mem i)

/-- Helper for Exercise 15-15.2-5: if one stable lattice is contained in another, then some power
of the maximal ideal sends the larger lattice into the smaller one. -/
theorem exists_maximalIdeal_pow_le_of_le_monoid
    {ρ : Representation K G E} {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) :
    ∃ n : ℕ, (IsLocalRing.maximalIdeal A ^ n) • L₁.toSubmodule ≤ L₂.toSubmodule := by
  classical
  by_cases hsub : Subsingleton L₁.toSubmodule
  · -- If the larger lattice is trivial, then both lattices are zero and the claim is immediate.
    have hL₁bot : L₁.toSubmodule = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      exact congrArg Subtype.val (hsub.elim ⟨x, hx⟩ 0)
    have hL₂bot : L₂.toSubmodule = ⊥ := by
      apply le_antisymm
      · exact h21.trans hL₁bot.le
      · exact bot_le
    use 0
    simp [hL₁bot, hL₂bot, Ideal.one_eq_top]
  · -- First clear denominators in the reverse inclusion `L₁ → L₂`.
    letI : Field K := IsFractionRing.toField (A := A) (K := K)
    letI : Module.IsTorsionFree A K :=
      (Module.isTorsionFree_iff_algebraMap_injective (R := A) (A := K)).2
        (IsFractionRing.injective A K)
    obtain ⟨a, ha⟩ :=
      exists_smul_le_of_lattices_monoid (A := A) (K := K) (L₁ := L₂) (L₂ := L₁)
    obtain ⟨x, y, hy, hfrac⟩ := IsFractionRing.div_surjective A (a : K)
    have hy0 : y ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
    have hy0K : (algebraMap A K y : K) ≠ 0 := by
      exact IsFractionRing.to_map_eq_zero_iff.not.mpr hy0
    have hx0K : (algebraMap A K x : K) ≠ 0 := by
      intro hx0
      apply Units.ne_zero a
      rw [← hfrac, hx0, zero_div]
    have hx0 : x ≠ 0 := by
      exact IsFractionRing.to_map_eq_zero_iff.not.mp hx0K
    have hx_le : x • L₁.toSubmodule ≤ L₂.toSubmodule := by
      intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      -- Rewrite the homothety scalar as `x / y` and clear the denominator by the
      -- `A`-submodule structure on `L₂`.
      have hz' : ((algebraMap A K x / algebraMap A K y : K) • z) ∈ L₂.toSubmodule := by
        have hsmul_mem : ((algebraMap A K x / algebraMap A K y : K) • z) ∈
            (a • L₁).toSubmodule := by
          rw [hfrac]
          exact ⟨z, hz, rfl⟩
        exact ha hsmul_mem
      have hyhz' : (y : A) • ((algebraMap A K x / algebraMap A K y : K) • z) ∈
          L₂.toSubmodule := by
        exact L₂.toSubmodule.smul_mem y hz'
      have hyhz'' :
          (((algebraMap A K y : K) * (algebraMap A K x / algebraMap A K y)) : K) • z ∈
            L₂.toSubmodule := by
        have hs :
            (y : A) • ((algebraMap A K x / algebraMap A K y : K) • z) =
              (((algebraMap A K y : K) * (algebraMap A K x / algebraMap A K y)) : K) • z := by
          calc
            (y : A) • ((algebraMap A K x / algebraMap A K y : K) • z) =
                ((y • (algebraMap A K x / algebraMap A K y : K)) • z) := by
                  symm
                  exact smul_assoc y (algebraMap A K x / algebraMap A K y : K) z
            _ =
                (((algebraMap A K y : K) * (algebraMap A K x / algebraMap A K y)) : K) • z := by
                  rw [Algebra.smul_def, mul_smul]
        simpa [hs] using hyhz'
      have hmul :
          (algebraMap A K y : K) * (algebraMap A K x / algebraMap A K y) =
            algebraMap A K x := by
        field_simp [hy0K]
      simpa [hmul] using hyhz''
    -- In a DVR, the principal ideal `(x)` is a power of the maximal ideal.
    have hspan_le : (Ideal.span {x} : Ideal A) • L₁.toSubmodule ≤ L₂.toSubmodule := by
      simpa [Submodule.ideal_span_singleton_smul] using hx_le
    obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal A
      (inferInstance : (IsLocalRing.maximalIdeal A).IsPrincipal)
      (Ideal.span {x})
      (mt Ideal.span_singleton_eq_bot.mp hx0)
    use n
    simpa [hn] using hspan_le

/-- Helper for Exercise 15-15.2-5: the maximal-ideal submodule of the smaller lattice maps into
the maximal-ideal submodule of the larger lattice under a nested inclusion. -/
theorem maximalIdealSubmodule_le_comap_inclusion_monoid
    {ρ : Representation K G E} {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) :
    L₂.maximalIdealSubmodule ≤
      Submodule.comap (Submodule.inclusion h21) L₁.maximalIdealSubmodule := by
  -- Rewrite membership in `𝔪_A • ⊤` by generators and transport each generator across the
  -- lattice inclusion.
  intro x hx
  change (Submodule.inclusion h21 x : L₁.toSubmodule) ∈ L₁.maximalIdealSubmodule
  rw [StableLattice.maximalIdealSubmodule] at hx ⊢
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y hy
    exact Submodule.smul_mem_smul ha
      (show (Submodule.inclusion h21 y : L₁.toSubmodule) ∈ ⊤ by trivial)
  · intro y z hy hz
    exact add_mem hy hz

/-- Helper for Exercise 15-15.2-5: the nested inclusion `L₂ ⊆ L₁` induces the canonical map on
reductions modulo `𝔪_A`. -/
noncomputable def reductionNestedMap_monoid
    {ρ : Representation K G E} {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) :
    L₂.reductionRepresentation.IntertwiningMap L₁.reductionRepresentation := by
  let mapA :=
    Submodule.mapQ L₂.maximalIdealSubmodule L₁.maximalIdealSubmodule
      (Submodule.inclusion h21)
      (maximalIdealSubmodule_le_comap_inclusion_monoid (A := A) (K := K) h21)
  let f : L₂.reduction →ₗ[IsLocalRing.ResidueField A] L₁.reduction :=
    { toFun :=
        mapA
      map_add' := mapA.map_add
      map_smul' := by
        intro c x
        refine Quotient.inductionOn' c ?_
        intro a
        refine Quotient.inductionOn' x ?_
        intro y
        -- Reduce the residue-field linearity claim to represented quotient classes.
        change
          Submodule.mapQ L₂.maximalIdealSubmodule L₁.maximalIdealSubmodule
              (Submodule.inclusion h21)
              (maximalIdealSubmodule_le_comap_inclusion_monoid
                (A := A) (K := K) (L₁ := L₁) (L₂ := L₂) h21)
              ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a :
                  IsLocalRing.ResidueField A) •
                (Submodule.Quotient.mk y : L₂.reduction)) = _
        rw [StableLattice.reduction_smul_mk (L := L₂) a y]
        rfl }
  -- Compare both sides on represented quotient classes to prove equivariance.
  exact f.intertwiningMap_of_isIntertwiningMap
    L₂.reductionRepresentation L₁.reductionRepresentation fun g x ↦ by
      refine Quotient.inductionOn' x ?_
      intro y
      change
        Submodule.Quotient.mk (Submodule.inclusion h21 ((L₂.toRepresentation g) y)) =
          (L₁.reductionRepresentation g)
            (Submodule.Quotient.mk (Submodule.inclusion h21 y) : L₁.reduction)
      rw [StableLattice.reductionRepresentation_apply_mk]
      rfl

/-- Helper for Exercise 15-15.2-5: on represented quotient classes, the bundled nested map is
the quotient class of the lattice inclusion `L₂ ↪ L₁`. -/
@[simp] theorem reductionNestedMap_monoid_apply_mk
    {ρ : Representation K G E} {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) (x : L₂.toSubmodule) :
    reductionNestedMap_monoid (A := A) (K := K) (L₁ := L₁) (L₂ := L₂) h21
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.inclusion h21 x) := by
  rfl

/-- Helper for Exercise 15-15.2-5: a point of `𝔪_A L` inside the subtype lattice also lies in the
ambient ideal multiple `𝔪_A • L`. -/
theorem coe_mem_maximalIdealSubmodule_monoid
    {ρ : Representation K G E} {L : StableLattice A ρ}
    {x : L.toSubmodule} (hx : x ∈ L.maximalIdealSubmodule) :
    ((x : L.toSubmodule) : E) ∈ (IsLocalRing.maximalIdeal A) • L.toSubmodule := by
  -- Expand membership in `𝔪_A • ⊤` inside the subtype and forget back to the ambient module.
  rw [StableLattice.maximalIdealSubmodule] at hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y hy
    exact Submodule.smul_mem_smul ha y.property
  · intro y z hy hz
    exact add_mem hy hz

/-- Helper for Exercise 15-15.2-5: the chosen generator of the maximal ideal stays nonzero in the
fraction field. -/
theorem maximalIdeal_generator_ne_zero_monoid :
    (algebraMap A K
      (Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)) : K) ≠ 0 := by
  let π : A := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)
  have hmax_ne_bot : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    simpa [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField A)
  have hπ0 : π ≠ 0 := by
    intro hπ
    exact hmax_ne_bot <|
      (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero
        (IsLocalRing.maximalIdeal A)).2 hπ
  exact IsFractionRing.to_map_eq_zero_iff.not.mpr hπ0

/-- Helper for Exercise 15-15.2-5: a stable lattice cannot be contained in its own maximal-ideal
multiple. -/
theorem not_le_maximalIdeal_smul_self_monoid
    {ρ : Representation K G E} [Nontrivial E] (L : StableLattice A ρ) :
    ¬ L.toSubmodule ≤ (IsLocalRing.maximalIdeal A) • L.toSubmodule := by
  have hne : L.toSubmodule ≠ (⊥ : Submodule A E) := by
    -- A lattice spans the ambient `K`-module, so it cannot be the zero submodule.
    intro hbot
    have hspan : Submodule.span K (L.toSubmodule : Set E) = (⊤ : Submodule K E) := by
      exact Submodule.IsLattice.span_eq_top (A := K) (M := L.toSubmodule)
    simp [hbot] at hspan
  intro hmax
  -- Nakayama collapses a finitely generated module contained in its maximal-ideal multiple.
  exact hne <|
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (I := IsLocalRing.maximalIdeal A) (N := L.toSubmodule)
      (Submodule.IsLattice.fg (A := K) (M := L.toSubmodule))
      hmax
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal A))

/-- Helper for Exercise 15-15.2-5: after repeatedly dividing by a generator of the maximal ideal,
some homothetic copy of a stable lattice lies in `E₁` but not in `𝔪_A E₁`. -/
theorem exists_homothety_le_not_le_maximalIdeal_smul_monoid
    {ρ : Representation K G E} [Nontrivial E]
    (E₁ L : StableLattice A ρ) :
    ∃ a : Kˣ,
      (a • L).toSubmodule ≤ E₁.toSubmodule ∧
        ¬ (a • L).toSubmodule ≤ (IsLocalRing.maximalIdeal A) • E₁.toSubmodule := by
  letI : Field K := IsFractionRing.toField (A := A) (K := K)
  let π : A := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)
  have hπK0 : (algebraMap A K π : K) ≠ 0 :=
    maximalIdeal_generator_ne_zero_monoid (A := A) (K := K)
  let uπ : Kˣ := Units.mk0 (algebraMap A K π) hπK0
  obtain ⟨a₀, ha₀⟩ :=
    exists_smul_le_of_lattices_monoid (A := A) (K := K) (L₁ := E₁) (L₂ := L)
  obtain ⟨n, hn⟩ :=
    exists_maximalIdeal_pow_le_of_le_monoid
      (A := A) (K := K) (L₁ := E₁) (L₂ := a₀ • L) ha₀
  have hnormalize :
      ∀ n : ℕ,
        ∀ {a : Kˣ},
          (IsLocalRing.maximalIdeal A ^ n) • E₁.toSubmodule ≤ (a • L).toSubmodule →
          (a • L).toSubmodule ≤ E₁.toSubmodule →
          ∃ b : Kˣ,
            (b • L).toSubmodule ≤ E₁.toSubmodule ∧
              ¬ (b • L).toSubmodule ≤ (IsLocalRing.maximalIdeal A) • E₁.toSubmodule := by
    intro n
    induction n with
    | zero =>
        intro a hpow hLE
        have hEL : E₁.toSubmodule ≤ (a • L).toSubmodule := by
          simpa [pow_zero, Ideal.one_eq_top] using hpow
        have hEq : (a • L).toSubmodule = E₁.toSubmodule := le_antisymm hLE hEL
        refine ⟨a, hLE, ?_⟩
        -- At exponent `0`, the normalized lattice is already all of `E₁`.
        rw [hEq]
        exact not_le_maximalIdeal_smul_self_monoid (A := A) (K := K) E₁
    | succ n ih =>
        intro a hpow hLE
        by_cases hbad :
            (a • L).toSubmodule ≤ (IsLocalRing.maximalIdeal A) • E₁.toSubmodule
        · let b : Kˣ := uπ⁻¹ * a
          have hLE' : (b • L).toSubmodule ≤ E₁.toSubmodule := by
            -- Divide once more by the chosen generator because the current lattice still lies in
            -- `𝔪_A E₁`.
            intro x hx
            rcases hx with ⟨y, hy, rfl⟩
            have hy' : (((a : Kˣ) : K) • y : E) ∈ (a • L).toSubmodule := by
              exact ⟨y, hy, rfl⟩
            have hy'' :
                (((a : Kˣ) : K) • y : E) ∈
                  (IsLocalRing.maximalIdeal A) • E₁.toSubmodule := hbad hy'
            rw [← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
              Submodule.ideal_span_singleton_smul] at hy''
            rcases hy'' with ⟨z, hz, hEq⟩
            have hxEq : (((b : Kˣ) : K) • y : E) = z := by
              calc
                (((b : Kˣ) : K) • y : E)
                    = ((↑uπ⁻¹ : K) • ((((a : Kˣ) : K) • y) : E)) := by
                        simp [b, smul_smul]
                _ = ((↑uπ⁻¹ : K) • ((π : A) • z) : E) := by
                      simpa using congrArg (fun t : E => ((↑uπ⁻¹ : K) • t : E)) hEq.symm
                _ = (((algebraMap A K π : K)⁻¹ • ((π : A) • z)) : E) := by
                      rfl
                _ = (((algebraMap A K π : K)⁻¹ • ((algebraMap A K π : K) • z)) : E) := by
                      rw [IsScalarTower.algebraMap_smul K π z]
                _ = z := by
                      rw [smul_smul]
                      simpa [hπK0]
            change ((((b : Kˣ) : K) • y : E)) ∈ E₁.toSubmodule
            rw [hxEq]
            exact hz
          have hpow' :
              (IsLocalRing.maximalIdeal A ^ n) • E₁.toSubmodule ≤ (b • L).toSubmodule := by
            -- Dividing also drops the maximal-ideal power bound by one.
            intro x hx
            have hπx0 :
                (π : A) • x ∈
                  (IsLocalRing.maximalIdeal A) •
                    ((IsLocalRing.maximalIdeal A ^ n) • E₁.toSubmodule) := by
              exact Submodule.smul_mem_smul
                (Submodule.IsPrincipal.generator_mem (IsLocalRing.maximalIdeal A)) hx
            have hπx1 :
                (π : A) • x ∈
                  ((IsLocalRing.maximalIdeal A) * (IsLocalRing.maximalIdeal A ^ n)) •
                    E₁.toSubmodule := by
              simpa [Submodule.mul_smul] using hπx0
            have hπx :
                (π : A) • x ∈
                  (IsLocalRing.maximalIdeal A ^ (n + 1)) • E₁.toSubmodule := by
              simpa [pow_succ, mul_comm] using hπx1
            have hx' : (π : A) • x ∈ (a • L).toSubmodule := hpow hπx
            rcases hx' with ⟨y, hy, hyEq⟩
            refine ⟨y, hy, ?_⟩
            calc
              (((b : Kˣ) : K) • y : E)
                  = ((↑uπ⁻¹ : K) • ((((a : Kˣ) : K) • y) : E)) := by
                      simp [b, smul_smul]
              _ = ((↑uπ⁻¹ : K) • ((π : A) • x) : E) := by
                    simpa using congrArg (fun t : E => ((↑uπ⁻¹ : K) • t : E)) hyEq
              _ = (((algebraMap A K π : K)⁻¹ • ((π : A) • x)) : E) := by
                    rfl
              _ = (((algebraMap A K π : K)⁻¹ • ((algebraMap A K π : K) • x)) : E) := by
                    rw [IsScalarTower.algebraMap_smul K π x]
              _ = x := by
                    rw [smul_smul]
                    simpa [hπK0]
          exact ih hpow' hLE'
        · exact ⟨a, hLE, hbad⟩
  exact hnormalize n hn ha₀

/-- Helper for Exercise 15-15.2-5: ambient membership in `𝔪_A • L` lifts back to membership in
the subtype maximal-ideal submodule. -/
theorem mem_maximalIdealSubmodule_of_coe_mem_monoid
    {ρ : Representation K G E} {L : StableLattice A ρ}
    {x : L.toSubmodule}
    (hx : ((x : L.toSubmodule) : E) ∈ (IsLocalRing.maximalIdeal A) • L.toSubmodule) :
    x ∈ L.maximalIdealSubmodule := by
  -- Unpack the ambient `𝔪_A • L` witness with the chosen generator and rebuild it inside the
  -- subtype module `L`.
  change x ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A L.toSubmodule)
  rw [← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
    Submodule.ideal_span_singleton_smul] at hx ⊢
  rcases hx with ⟨y, hy, hxy⟩
  refine ⟨⟨y, hy⟩, show (⟨y, hy⟩ : L.toSubmodule) ∈ (⊤ : Submodule A L.toSubmodule) by trivial, ?_⟩
  ext
  simpa using hxy

/-- Helper for Exercise 15-15.2-5: clearing denominators puts a single ambient vector into the
chosen stable lattice. -/
theorem exists_smul_mem_lattice_monoid
    {ρ : Representation K G E} (E₁ : StableLattice A ρ) (x : E) :
    ∃ a : Kˣ, ((a : K) • x : E) ∈ E₁.toSubmodule := by
  classical
  letI : Field K := IsFractionRing.toField (A := A) (K := K)
  letI : Module.IsTorsionFree A K :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := A) (A := K)).2
      (IsFractionRing.injective A K)
  let b : Module.Basis (Module.Free.ChooseBasisIndex A E₁.toSubmodule) A E₁.toSubmodule :=
    Module.Free.chooseBasis A E₁.toSubmodule
  let e : Module.Basis (Module.Free.ChooseBasisIndex A E₁.toSubmodule) K E :=
    b.extendOfIsLattice K
  let coeff : Module.Free.ChooseBasisIndex A E₁.toSubmodule → K := fun i ↦ e.repr x i
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (M := nonZeroDivisors A) coeff
  let a : Kˣ := (IsLocalization.map_units K d).unit
  refine ⟨a, ?_⟩
  let c : Module.Free.ChooseBasisIndex A E₁.toSubmodule → A :=
    fun i ↦ Classical.choose (hd i)
  let z : E₁.toSubmodule := ∑ i, c i • b i
  -- Reassemble the cleared coordinates in the `A`-basis of `E₁`.
  have hz : ((z : E₁.toSubmodule) : E) = (algebraMap A K d) • x := by
    calc
      ((z : E₁.toSubmodule) : E)
          = ∑ i, (algebraMap A K (c i)) • (((b i : E₁.toSubmodule) : E)) := by
              simp [z, c]
      _ = ∑ i, e.repr ((algebraMap A K d) • x) i • e i := by
            apply Finset.sum_congr rfl
            intro i _
            have hc : algebraMap A K (c i) = e.repr ((algebraMap A K d) • x) i := by
              calc
                algebraMap A K (c i) = (algebraMap A K d) * coeff i := by
                  simpa [c, coeff, Algebra.smul_def] using (Classical.choose_spec (hd i))
                _ = e.repr ((algebraMap A K d) • x) i := by
                  simpa [coeff, Algebra.smul_def] using
                    ((congrArg (fun f => f i)
                      (LinearEquiv.map_smul e.repr (algebraMap A K d) x)).symm)
            simpa [e, Module.Basis.extendOfIsLattice_apply] using
              congrArg (fun t => t • (((b i : E₁.toSubmodule) : E))) hc
      _ = (algebraMap A K d) • x := by
            simpa [e, Module.Basis.extendOfIsLattice_apply] using
              (e.sum_repr ((algebraMap A K d) • x))
  exact hz ▸ z.property

/-- Helper for Exercise 15-15.2-5: a reduced subrepresentation of `E₁` lifts to the canonical
intermediate stable lattice between `𝔪_A E₁` and `E₁`. -/
noncomputable def reduction_preimage_stableLattice_monoid
    {ρ : Representation K G E} (E₁ : StableLattice A ρ)
    (W : Subrepresentation E₁.reductionRepresentation) :
    StableLattice A ρ := by
  letI : Field K := IsFractionRing.toField (A := A) (K := K)
  let N₀ : Submodule A E₁.toSubmodule :=
    { carrier := { y | (Submodule.Quotient.mk y : E₁.reduction) ∈ W.toSubmodule }
      zero_mem' := by
        simpa using (show (0 : E₁.reduction) ∈ W.toSubmodule from W.toSubmodule.zero_mem)
      add_mem' := by
        intro y z hy hz
        change (Submodule.Quotient.mk (y + z) : E₁.reduction) ∈ W.toSubmodule
        simpa using W.toSubmodule.add_mem hy hz
      smul_mem' := by
        intro a y hy
        change (Submodule.Quotient.mk (a • y) : E₁.reduction) ∈ W.toSubmodule
        rw [← StableLattice.reduction_smul_mk (L := E₁) a y]
        exact W.toSubmodule.smul_mem (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a) hy }
  let N : Submodule A E := N₀.map (E₁.toSubmodule.subtype.restrictScalars A)
  refine
    { toSubmodule := N
      apply_mem_toSubmodule := ?_
      isLattice := ?_ }
  · intro g x hx
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨E₁.toRepresentation g y, ?_, ?_⟩
    · -- Stability of the preimage comes from stability of the reduced subrepresentation `W`.
      simpa [N₀, StableLattice.reductionRepresentation_apply_mk] using
        W.apply_mem_toSubmodule g hy
    · rfl
  · refine
      { fg := ?_
        span_eq_top := ?_ }
    · -- Finite generation descends from the ambient lattice `E₁`.
      have hfgN₀ : N₀.FG := by
        have htop_fg : (⊤ : Submodule A E₁.toSubmodule).FG := by
          exact
            (Submodule.fg_top (N := E₁.toSubmodule)).2
              (Submodule.IsLattice.fg (A := K) (M := E₁.toSubmodule))
        exact Submodule.FG.of_le
          htop_fg
          (fun _ _ ↦ by trivial)
      exact hfgN₀.map (E₁.toSubmodule.subtype.restrictScalars A)
    · -- Because `N` contains `𝔪_A E₁`, inverting a generator of the maximal ideal recovers all of
      -- `E₁`, hence the ambient `K`-span is still all of `E`.
      apply le_antisymm le_top
      change (⊤ : Submodule K E) ≤ Submodule.span K (N : Set E)
      have hsubset :
          (E₁.toSubmodule : Set E) ⊆ Submodule.span K (N : Set E) := by
        intro y hy
        let yL : E₁.toSubmodule := ⟨y, hy⟩
        let π : A := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)
        have hπy_mem_max :
            (π : A) • yL ∈ E₁.maximalIdealSubmodule := by
          rw [StableLattice.maximalIdealSubmodule,
            ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
            Submodule.ideal_span_singleton_smul]
          exact ⟨yL, show yL ∈ (⊤ : Submodule A E₁.toSubmodule) by trivial, rfl⟩
        have hπy_mem_N₀ : (π : A) • yL ∈ N₀ := by
          show (Submodule.Quotient.mk ((π : A) • yL) : E₁.reduction) ∈ W.toSubmodule
          have hzero :
              (Submodule.Quotient.mk ((π : A) • yL) : E₁.reduction) = 0 := by
            exact (Submodule.Quotient.mk_eq_zero _).2 hπy_mem_max
          simpa [hzero] using (show (0 : E₁.reduction) ∈ W.toSubmodule from W.toSubmodule.zero_mem)
        have hπy_mem_N : ((π : A) • y : E) ∈ N := by
          refine ⟨(π : A) • yL, hπy_mem_N₀, ?_⟩
          rfl
        have hπy_span :
            ((π : A) • y : E) ∈ Submodule.span K (N : Set E) := by
          exact Submodule.subset_span hπy_mem_N
        let πK : K := algebraMap A K π
        have hy_eq :
            y = (πK)⁻¹ •
              ((π : A) • y : E) := by
          have hπinv : (πK)⁻¹ * πK = (1 : K) := by
            exact inv_mul_cancel₀
              (StableLattice.maximalIdeal_generator_ne_zero_monoid (A := A) (K := K))
          calc
            y = (1 : K) • y := by simp
            _ = ((πK)⁻¹ * πK) • y := by rw [hπinv]
            _ = (πK)⁻¹ • (πK • y) := by rw [smul_smul]
            _ = (πK)⁻¹ • ((π : A) • y : E) := by
                  rw [IsScalarTower.algebraMap_smul K π y]
        rw [hy_eq]
        exact Submodule.smul_mem _ _ hπy_span
      intro x _
      have hxE₁ : x ∈ Submodule.span K (E₁.toSubmodule : Set E) := by
        rw [Submodule.IsLattice.span_eq_top (A := K) (M := E₁.toSubmodule)]
        trivial
      exact (Submodule.span_le.2 hsubset) hxE₁

/-- Helper for Exercise 15-15.2-5: a nonzero subrepresentation inherits the canonical stable
lattice given by its intersection with `E₁`. -/
noncomputable def subrepresentation_intersection_stableLattice_monoid
    {ρ : Representation K G E} (U : Subrepresentation ρ) (E₁ : StableLattice A ρ) :
    StableLattice A U.toRepresentation := by
  let N : Submodule A U.toSubmodule :=
    Submodule.comap (U.toSubmodule.subtype.restrictScalars A) E₁.toSubmodule
  refine
    { toSubmodule := N
      apply_mem_toSubmodule := ?_
      isLattice := ?_ }
  · intro g x hx
    -- The intersection is stable because both `U` and `E₁` are stable under the ambient action.
    change (((U.toRepresentation g) x : U.toSubmodule) : E) ∈ E₁.toSubmodule
    simpa using E₁.apply_mem_toSubmodule g hx
  · refine
      { fg := ?_
        span_eq_top := ?_ }
    · -- Finite generation is recovered from the injective inclusion `N ↪ E₁`.
      have hmap :
          (N.map (U.toSubmodule.subtype.restrictScalars A)).FG := by
        apply Submodule.FG.of_le (Submodule.IsLattice.fg (A := K) (M := E₁.toSubmodule))
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact hx
      exact Submodule.fg_of_fg_map_injective
        (U.toSubmodule.subtype.restrictScalars A) Subtype.val_injective hmap
    · -- Any vector of `U` can be rescaled into `E₁`, and the rescaled vector still lies in `U`.
      apply le_antisymm le_top
      change (⊤ : Submodule K U.toSubmodule) ≤ Submodule.span K (N : Set U.toSubmodule)
      intro x _
      obtain ⟨a, ha⟩ :=
        StableLattice.exists_smul_mem_lattice_monoid (A := A) (K := K) E₁ (x : E)
      have haxU : ((a : K) • (x : E) : E) ∈ U.toSubmodule := by
        exact U.toSubmodule.smul_mem (a : K) x.property
      let ax : U.toSubmodule := ⟨((a : K) • (x : E) : E), haxU⟩
      have haxN : ax ∈ N := by
        change (((a : K) • (x : E) : E)) ∈ E₁.toSubmodule
        exact ha
      have haxSpan : ax ∈ Submodule.span K (N : Set U.toSubmodule) := by
        exact Submodule.subset_span haxN
      have hx_eq : x = (↑a⁻¹ : K) • ax := by
        ext
        change (x : E) = (↑a⁻¹ : K) • (((a : K) • (x : E) : E))
        simp [smul_smul]
      rw [hx_eq]
      exact Submodule.smul_mem _ _ haxSpan

/-- Helper for Exercise 15-15.2-5: the canonical preimage lattice of a reduced
subrepresentation of `E₁` lies inside `E₁`. -/
theorem reduction_preimage_toSubmodule_le_monoid
    {ρ : Representation K G E} (E₁ : StableLattice A ρ)
    (W : Subrepresentation E₁.reductionRepresentation) :
    (reduction_preimage_stableLattice_monoid (A := A) (K := K) E₁ W).toSubmodule ≤
      E₁.toSubmodule := by
  -- Unpack the mapped-submodule definition of the canonical preimage lattice.
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact y.property

/-- Helper for Exercise 15-15.2-5: reducing the canonical preimage lattice and including it into
`E₁.reductionRepresentation` has range exactly the prescribed reduced subrepresentation. -/
theorem reduction_preimage_nested_range_eq_monoid
    {ρ : Representation K G E} (E₁ : StableLattice A ρ)
    (W : Subrepresentation E₁.reductionRepresentation) :
    let N := reduction_preimage_stableLattice_monoid (A := A) (K := K) E₁ W
    (reductionNestedMap_monoid (A := A) (K := K)
      (L₁ := E₁) (L₂ := N) (reduction_preimage_toSubmodule_le_monoid
        (A := A) (K := K) E₁ W)).range = W := by
  let N := reduction_preimage_stableLattice_monoid (A := A) (K := K) E₁ W
  let hNle := reduction_preimage_toSubmodule_le_monoid (A := A) (K := K) E₁ W
  apply Subrepresentation.toSubmodule_injective
  ext z
  constructor
  · intro hz
    rcases hz with ⟨w, rfl⟩
    rcases Quotient.exists_rep w with ⟨w', rfl⟩
    rcases w'.property with ⟨y, hy, hEq⟩
    -- A represented class in the range comes from a representative whose ambient quotient class
    -- already lies in `W`.
    change (Submodule.Quotient.mk (Submodule.inclusion hNle w') : E₁.reduction) ∈ W.toSubmodule
    have hwEq : Submodule.inclusion hNle w' = y := by
      ext
      simpa using hEq.symm
    simpa [hwEq] using hy
  · intro hz
    rcases Quotient.exists_rep z with ⟨y, rfl⟩
    let yN : N.toSubmodule := ⟨((y : E₁.toSubmodule) : E), ⟨y, hz, rfl⟩⟩
    -- Conversely, every represented class of `W` comes from the same representative upstairs in
    -- the canonical preimage lattice.
    have hyEq : (Submodule.inclusion hNle yN : E₁.toSubmodule) = y := by
      ext
      rfl
    exact ⟨Submodule.Quotient.mk yN, by
      change Submodule.Quotient.mk (Submodule.inclusion hNle yN) = Submodule.Quotient.mk y
      rw [hyEq]⟩

/-- Helper for Exercise 15-15.2-5: if `x E₁ ⊆ y E₁`, then `x` lies in the principal ideal
generated by `y`. -/
theorem scalar_mem_span_singleton_of_smul_le_monoid
    {ρ : Representation K G E} [Nontrivial E] (E₁ : StableLattice A ρ) {x y : A}
    (hxy : x • E₁.toSubmodule ≤ y • E₁.toSubmodule) :
    x ∈ Ideal.span ({y} : Set A) := by
  letI : Field K := IsFractionRing.toField (A := A) (K := K)
  letI : Module.IsTorsionFree A K :=
    (Module.isTorsionFree_iff_algebraMap_injective (R := A) (A := K)).2
      (IsFractionRing.injective A K)
  letI : Module.Free A E₁.toSubmodule := Submodule.IsLattice.free (K := K) E₁.toSubmodule
  have hE₁_ne_bot : E₁.toSubmodule ≠ (⊥ : Submodule A E) := by
    intro hbot
    have hspan : Submodule.span K (E₁.toSubmodule : Set E) = (⊤ : Submodule K E) := by
      exact Submodule.IsLattice.span_eq_top (A := K) (M := E₁.toSubmodule)
    simp [hbot] at hspan
  letI : Nontrivial E₁.toSubmodule :=
    (Submodule.nontrivial_iff_ne_bot (p := E₁.toSubmodule)).2 hE₁_ne_bot
  let b : Module.Basis (Module.Free.ChooseBasisIndex A E₁.toSubmodule) A E₁.toSubmodule :=
    Module.Free.chooseBasis A E₁.toSubmodule
  let i : Module.Free.ChooseBasisIndex A E₁.toSubmodule :=
    Classical.choice (Module.Basis.index_nonempty b)
  let bi : E := ((b i : E₁.toSubmodule) : E)
  have hbi : bi ∈ E₁.toSubmodule := by
    exact (b i).property
  have hxb : x • bi ∈ y • E₁.toSubmodule := by
    exact hxy ⟨bi, hbi, rfl⟩
  rcases hxb with ⟨z, hz, hEq⟩
  let zL : E₁.toSubmodule := ⟨z, hz⟩
  -- Compare a single basis vector along its own coordinate to read off divisibility of scalars.
  rw [Ideal.mem_span_singleton]
  refine ⟨b.repr zL i, ?_⟩
  have hEq' : (y : A) • zL = x • b i := by
    ext
    simpa [zL, bi] using hEq
  have hcoord := congrArg (fun w : E₁.toSubmodule => b.repr w i) hEq'
  simpa [b] using hcoord.symm

/-- Helper for Exercise 15-15.2-5: a unit of `A` acts trivially on stable lattices after viewing
it as a `K`-unit. -/
theorem unit_smul_eq_self_monoid
    {ρ : Representation K G E} (E₁ : StableLattice A ρ) (u : Aˣ) :
    (Units.map (algebraMap A K) u : Kˣ) • E₁ = E₁ := by
  apply StableLattice.ext_toSubmodule
  ext w
  constructor
  · intro hw
    rcases hw with ⟨z, hz, rfl⟩
    -- Multiplication by an `A`-unit preserves the lattice because `E₁` is an `A`-submodule.
    change (((algebraMap A K (↑u : A)) : K) • z : E) ∈ E₁.toSubmodule
    simpa [IsScalarTower.algebraMap_smul K (↑u : A) z] using
      E₁.toSubmodule.smul_mem (↑u : A) hz
  · intro hw
    refine ⟨((↑u⁻¹ : A) • w : E), E₁.toSubmodule.smul_mem (↑u⁻¹ : A) hw, ?_⟩
    -- The inverse `A`-unit gives the reverse containment.
    change (((Units.map (algebraMap A K) u : Kˣ) : K) • ((↑u⁻¹ : A) • w) : E) = w
    simpa [smul_smul]

/-- Helper for Exercise 15-15.2-5: a homothetic copy of `E₁` contained in `E₁` and not already in
`𝔪_A • E₁` must equal `E₁`. -/
theorem smul_eq_of_le_not_le_maximalIdeal_monoid
    {ρ : Representation K G E} [Nontrivial E] (E₁ : StableLattice A ρ) {a : Kˣ}
    (ha : (a • E₁).toSubmodule ≤ E₁.toSubmodule)
    (hnot : ¬ (a • E₁).toSubmodule ≤ (IsLocalRing.maximalIdeal A) • E₁.toSubmodule) :
    a • E₁ = E₁ := by
  letI : Field K := IsFractionRing.toField (A := A) (K := K)
  obtain ⟨x, y, hy, hfrac⟩ := IsFractionRing.div_surjective A (a : K)
  have hy0 : y ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
  have hy0K : (algebraMap A K y : K) ≠ 0 := by
    exact IsFractionRing.to_map_eq_zero_iff.not.mpr hy0
  have hx_le : x • E₁.toSubmodule ≤ y • E₁.toSubmodule := by
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    have hz' : ((algebraMap A K x / algebraMap A K y : K) • z : E) ∈ E₁.toSubmodule := by
      have : ((algebraMap A K x / algebraMap A K y : K) • z : E) ∈ (a • E₁).toSubmodule := by
        rw [hfrac]
        exact ⟨z, hz, rfl⟩
      exact ha this
    -- Clear the denominator `y` on each represented lattice vector.
    refine ⟨((algebraMap A K x / algebraMap A K y : K) • z : E), hz', ?_⟩
    calc
      (y : A) • (((algebraMap A K x / algebraMap A K y : K) • z : E))
          = (((algebraMap A K y : K) •
                (((algebraMap A K x / algebraMap A K y : K) • z : E))) : E) := by
              rw [IsScalarTower.algebraMap_smul K y
                (((algebraMap A K x / algebraMap A K y : K) • z : E))]
      _ = (((algebraMap A K y : K) * (algebraMap A K x / algebraMap A K y)) • z : E) := by
            rw [smul_smul]
      _ = ((algebraMap A K x : K) • z : E) := by
            field_simp [hy0K]
      _ = (x : A) • z := by
            rw [IsScalarTower.algebraMap_smul K x z]
  have hx_mem : x ∈ Ideal.span ({y} : Set A) :=
    scalar_mem_span_singleton_of_smul_le_monoid (A := A) (K := K) E₁ hx_le
  rcases (Ideal.mem_span_singleton.mp hx_mem) with ⟨c, hxc⟩
  have ha_eq : (a : K) = algebraMap A K c := by
    -- The containment forces the fraction scalar `a = x / y` to come from an element of `A`.
    calc
      (a : K) = algebraMap A K x / algebraMap A K y := by
        rw [← hfrac]
      _ = ((algebraMap A K y) * (algebraMap A K c)) / algebraMap A K y := by
        rw [hxc]
        rw [map_mul]
      _ = algebraMap A K c := by
            field_simp [hy0K]
  have hc_not_mem : c ∉ IsLocalRing.maximalIdeal A := by
    intro hc
    apply hnot
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    simpa [ha_eq, IsScalarTower.algebraMap_smul K c z] using
      Submodule.smul_mem_smul hc hz
  have hc_unit : IsUnit c := (IsLocalRing.notMem_maximalIdeal).1 hc_not_mem
  rcases hc_unit with ⟨u, rfl⟩
  have ha_unit : a = Units.map (algebraMap A K) u := by
    ext
    simpa using ha_eq
  rw [ha_unit]
  exact unit_smul_eq_self_monoid (A := A) (K := K) E₁ u

/-- Helper for Exercise 15-15.2-5: the intersection lattice `U ∩ E₁` includes naturally into
`E₁`. -/
def subrepresentation_intersection_inclusion_monoid
    {ρ : Representation K G E} (U : Subrepresentation ρ) (E₁ : StableLattice A ρ) :
    (subrepresentation_intersection_stableLattice_monoid (A := A) (K := K) U E₁).toSubmodule →ₗ[A]
      E₁.toSubmodule where
  toFun x :=
    ⟨((((x : (subrepresentation_intersection_stableLattice_monoid
      (A := A) (K := K) U E₁).toSubmodule) : U.toSubmodule) : E)), x.property⟩
  map_add' x y := by
    ext
    rfl
  map_smul' a x := by
    ext
    rfl

/-- Helper for Exercise 15-15.2-5: the maximal-ideal submodule of `U ∩ E₁` maps into the
maximal-ideal submodule of `E₁`. -/
theorem subrepresentation_intersection_maximalIdealSubmodule_le_comap_monoid
    {ρ : Representation K G E} (U : Subrepresentation ρ) (E₁ : StableLattice A ρ) :
    (subrepresentation_intersection_stableLattice_monoid
      (A := A) (K := K) U E₁).maximalIdealSubmodule ≤
        Submodule.comap (subrepresentation_intersection_inclusion_monoid
          (A := A) (K := K) U E₁) E₁.maximalIdealSubmodule := by
  intro x hx
  change subrepresentation_intersection_inclusion_monoid
      (A := A) (K := K) U E₁ x ∈ E₁.maximalIdealSubmodule
  rw [StableLattice.maximalIdealSubmodule] at hx ⊢
  -- Transport each generator across the literal inclusion `U ∩ E₁ ↪ E₁`.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y hy
    exact Submodule.smul_mem_smul ha
      (show subrepresentation_intersection_inclusion_monoid
        (A := A) (K := K) U E₁ y ∈ ⊤ by trivial)
  · intro y z hy hz
    exact add_mem hy hz

/-- Helper for Exercise 15-15.2-5: reducing `U ∩ E₁` and then including it into `E₁` defines the
canonical reduced inclusion. -/
noncomputable def subrepresentation_intersection_reduction_inclusion_monoid
    {ρ : Representation K G E} (U : Subrepresentation ρ) (E₁ : StableLattice A ρ) :
    (subrepresentation_intersection_stableLattice_monoid
      (A := A) (K := K) U E₁).reductionRepresentation.IntertwiningMap
        E₁.reductionRepresentation := by
  let N := subrepresentation_intersection_stableLattice_monoid (A := A) (K := K) U E₁
  let mapA :=
    Submodule.mapQ N.maximalIdealSubmodule E₁.maximalIdealSubmodule
      (subrepresentation_intersection_inclusion_monoid (A := A) (K := K) U E₁)
      (subrepresentation_intersection_maximalIdealSubmodule_le_comap_monoid
        (A := A) (K := K) U E₁)
  let f : N.reduction →ₗ[IsLocalRing.ResidueField A] E₁.reduction :=
    { toFun := mapA
      map_add' := mapA.map_add
      map_smul' := by
        intro c x
        refine Quotient.inductionOn' c ?_
        intro a
        refine Quotient.inductionOn' x ?_
        intro y
        -- Reduce residue-field linearity to represented quotient classes.
        change
          Submodule.mapQ N.maximalIdealSubmodule E₁.maximalIdealSubmodule
              (subrepresentation_intersection_inclusion_monoid
                (A := A) (K := K) U E₁)
              (subrepresentation_intersection_maximalIdealSubmodule_le_comap_monoid
                (A := A) (K := K) U E₁)
              ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a :
                  IsLocalRing.ResidueField A) •
                (Submodule.Quotient.mk y : N.reduction)) = _
        rw [StableLattice.reduction_smul_mk (L := N) a y]
        rfl }
  exact f.intertwiningMap_of_isIntertwiningMap
    (subrepresentation_intersection_stableLattice_monoid
      (A := A) (K := K) U E₁).reductionRepresentation
    E₁.reductionRepresentation fun g x ↦ by
      refine Quotient.inductionOn' x ?_
      intro y
      -- On represented classes, the reduced inclusion is literally the ambient quotient class.
      change
        (Submodule.Quotient.mk
          (subrepresentation_intersection_inclusion_monoid
            (A := A) (K := K) U E₁
            ((subrepresentation_intersection_stableLattice_monoid
              (A := A) (K := K) U E₁).toRepresentation g y)) :
            E₁.reduction) =
          E₁.reductionRepresentation g
            (Submodule.Quotient.mk
              (subrepresentation_intersection_inclusion_monoid
                (A := A) (K := K) U E₁ y))
      rw [StableLattice.reductionRepresentation_apply_mk]
      rfl

/-- Helper for Exercise 15-15.2-5: on represented quotient classes, the reduced inclusion
`\overline{U ∩ E₁} → \bar E₁` is the quotient class of the ambient inclusion. -/
@[simp] theorem subrepresentation_intersection_reduction_inclusion_monoid_apply_mk
    {ρ : Representation K G E} (U : Subrepresentation ρ) (E₁ : StableLattice A ρ)
    (x : (subrepresentation_intersection_stableLattice_monoid
      (A := A) (K := K) U E₁).toSubmodule) :
    subrepresentation_intersection_reduction_inclusion_monoid
        (A := A) (K := K) U E₁ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (subrepresentation_intersection_inclusion_monoid
          (A := A) (K := K) U E₁ x) := by
  rfl

/-- Helper for Exercise 15-15.2-5: the reduced inclusion `\overline{U ∩ E₁} → \bar E₁` is
injective. -/
theorem subrepresentation_intersection_reduction_inclusion_injective_monoid
    {ρ : Representation K G E} (U : Subrepresentation ρ) (E₁ : StableLattice A ρ) :
    Function.Injective
      (subrepresentation_intersection_reduction_inclusion_monoid
        (A := A) (K := K) U E₁).toLinearMap := by
  letI : Field K := IsFractionRing.toField (A := A) (K := K)
  let N := subrepresentation_intersection_stableLattice_monoid (A := A) (K := K) U E₁
  let i := subrepresentation_intersection_reduction_inclusion_monoid
    (A := A) (K := K) U E₁
  have hzero : ∀ z : N.reduction, i.toLinearMap z = 0 → z = 0 := by
    intro z hz
    rcases Submodule.Quotient.mk_surjective N.maximalIdealSubmodule z with ⟨x, rfl⟩
    change (Submodule.Quotient.mk
      (subrepresentation_intersection_inclusion_monoid
        (A := A) (K := K) U E₁ x) : E₁.reduction) = 0 at hz
    have hx :
        subrepresentation_intersection_inclusion_monoid
            (A := A) (K := K) U E₁ x ∈ E₁.maximalIdealSubmodule := by
      exact (Submodule.Quotient.mk_eq_zero _).1 hz
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul] at hx
    rcases hx with ⟨y, hy, hxy⟩
    let π : A := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)
    have hxyE :
        (π : A) • (y : E) = (((x : N.toSubmodule) : U.toSubmodule) : E) := by
      simpa [π, subrepresentation_intersection_inclusion_monoid] using
        congrArg Subtype.val hxy
    have hxU : ((((x : N.toSubmodule) : U.toSubmodule) : E)) ∈ U.toSubmodule := by
      exact (((x : N.toSubmodule) : U.toSubmodule)).property
    have hyU : (y : E) ∈ U.toSubmodule := by
      have hpiyU : ((π : A) • (y : E)) ∈ U.toSubmodule := by
        simpa [hxyE] using hxU
      -- Divide by the chosen generator inside the ambient `K`-submodule `U`.
      have hπinv :
          ((algebraMap A K π : K)⁻¹ * (algebraMap A K π : K)) = (1 : K) := by
        exact inv_mul_cancel₀ (maximalIdeal_generator_ne_zero_monoid (A := A) (K := K))
      have hy_eq : (y : E) =
          ((algebraMap A K π : K)⁻¹ • ((π : A) • (y : E)) : E) := by
        calc
          (y : E) = (1 : K) • (y : E) := by simp
          _ = (((algebraMap A K π : K)⁻¹ * (algebraMap A K π : K)) • (y : E)) := by
                rw [hπinv]
          _ = ((algebraMap A K π : K)⁻¹ • ((algebraMap A K π : K) • (y : E))) := by
                rw [smul_smul]
          _ = ((algebraMap A K π : K)⁻¹ • ((π : A) • (y : E)) : E) := by
                rw [IsScalarTower.algebraMap_smul K π (y : E)]
      rw [hy_eq]
      exact U.toSubmodule.smul_mem _ hpiyU
    let yU : U.toSubmodule := ⟨(y : E), hyU⟩
    have hyN_mem : yU ∈ N.toSubmodule := by
      change (y : E) ∈ E₁.toSubmodule
      exact y.property
    let yN : N.toSubmodule := ⟨yU, hyN_mem⟩
    have hxyN : (π : A) • yN = x := by
      ext
      change (π : A) • (y : E) = (((x : N.toSubmodule) : U.toSubmodule) : E)
      exact hxyE
    -- The represented class of `x` vanishes because `x = π • yN`.
    apply (Submodule.Quotient.mk_eq_zero _).2
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul]
    refine ⟨yN, show yN ∈ (⊤ : Submodule A N.toSubmodule) by trivial, ?_⟩
    exact hxyN
  intro x y hxy
  have hsub : i.toLinearMap (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hzero (x - y) hsub)

/-- Helper for Exercise 15-15.2-5: the reduction of a nonzero stable lattice is nontrivial. -/
theorem reduction_nontrivial_monoid
    {ρ : Representation K G E} [Nontrivial E] (E₁ : StableLattice A ρ) :
    Nontrivial E₁.reduction := by
  classical
  have hnot_all :
      ¬ ∀ x : E₁.toSubmodule, x ∈ E₁.maximalIdealSubmodule := by
    intro hall
    -- If every lattice vector reduced to zero, the whole lattice would lie in `𝔪_A E₁`.
    exact StableLattice.not_le_maximalIdeal_smul_self_monoid (A := A) (K := K) E₁ fun x hx ↦ by
      simpa using
        StableLattice.coe_mem_maximalIdealSubmodule_monoid
          (A := A) (K := K) (L := E₁) (hall ⟨x, hx⟩)
  push_neg at hnot_all
  rcases hnot_all with ⟨x, hx⟩
  have hxq : (Submodule.Quotient.mk x : E₁.reduction) ≠ 0 := by
    intro hx0
    exact hx ((Submodule.Quotient.mk_eq_zero _).1 hx0)
  -- A nonzero quotient class gives the required nontriviality witness.
  refine ⟨0, Submodule.Quotient.mk x, ?_⟩
  simpa [eq_comm] using hxq

/-- Helper for Exercise 15-15.2-5: if two stable lattices have the same underlying submodule,
then the induced nested reduction map is surjective. -/
theorem reductionNestedMap_range_eq_top_of_toSubmodule_eq_monoid
    {ρ : Representation K G E} {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule)
    (hEq : L₂.toSubmodule = L₁.toSubmodule) :
    (reductionNestedMap_monoid (A := A) (K := K)
      (L₁ := L₁) (L₂ := L₂) h21).range = ⊤ := by
  -- Compare represented quotient classes and lift each one back along the equality of lattices.
  rw [eq_top_iff]
  intro x _
  simp only [IntertwiningMap.range, LinearMap.mem_range]
  rcases Quotient.exists_rep x with ⟨x', rfl⟩
  have hxL₂ : ((x' : L₁.toSubmodule) : E) ∈ L₂.toSubmodule := by
    simpa [hEq] using x'.property
  let y : L₂.toSubmodule := ⟨(x' : E), hxL₂⟩
  have hyEq : (Submodule.inclusion h21 y : L₁.toSubmodule) = x' := by
    ext
    rfl
  refine ⟨Submodule.Quotient.mk y, ?_⟩
  -- On represented classes, the nested reduction map is the quotient of the lattice inclusion.
  change
    (Submodule.Quotient.mk (Submodule.inclusion h21 y) : L₁.reduction) =
      Submodule.Quotient.mk x'
  rw [hyEq]

/-- Helper for Exercise 15-15.2-5: irreducibility of the reduction forces the ambient
`K[G]`-module to be nonzero. -/
theorem nontrivial_ambient_of_irreducible_reduction_monoid
    {ρ : Representation K G E} (E₁ : StableLattice A ρ)
    (hE₁ : E₁.reductionRepresentation.IsIrreducible) :
    Nontrivial E := by
  by_contra hE
  letI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
  letI : Subsingleton E₁.toSubmodule := inferInstance
  letI : Subsingleton E₁.reduction := inferInstance
  have hbot_top : (⊥ : Subrepresentation E₁.reductionRepresentation) = ⊤ := by
    -- If the ambient module is subsingleton, then every reduced class is zero.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim x 0)
  exact bot_ne_top hbot_top

/-- Helper for Exercise 15-15.2-5: a nonzero stable subrepresentation meets `E₁` in a lattice
whose reduction maps onto all of `\bar E₁` when `\bar E₁` is irreducible. -/
theorem subrepresentation_intersection_reduction_range_eq_top_of_simple_monoid
    {ρ : Representation K G E} (U : Subrepresentation ρ) (E₁ : StableLattice A ρ)
    (hE₁ : E₁.reductionRepresentation.IsIrreducible) (hU : U ≠ ⊥) :
    (subrepresentation_intersection_reduction_inclusion_monoid
      (A := A) (K := K) U E₁).range = ⊤ := by
  letI : E₁.reductionRepresentation.IsIrreducible := hE₁
  have hU_sub : U.toSubmodule ≠ (⊥ : Submodule K E) := by
    intro hU_sub
    exact hU (Subrepresentation.toSubmodule_injective hU_sub)
  letI : Nontrivial U.toSubmodule :=
    (Submodule.nontrivial_iff_ne_bot (p := U.toSubmodule)).2 hU_sub
  let N := subrepresentation_intersection_stableLattice_monoid (A := A) (K := K) U E₁
  let i := subrepresentation_intersection_reduction_inclusion_monoid
    (A := A) (K := K) U E₁
  have hnot_all :
      ¬ ∀ x : N.toSubmodule, x ∈ N.maximalIdealSubmodule := by
    intro hall
    -- If every vector of `U ∩ E₁` reduced to zero, Nakayama would collapse that lattice.
    exact StableLattice.not_le_maximalIdeal_smul_self_monoid (A := A) (K := K) N fun x hx ↦ by
      simpa using
        StableLattice.coe_mem_maximalIdealSubmodule_monoid
          (A := A) (K := K) (L := N) (hall ⟨x, hx⟩)
  push_neg at hnot_all
  rcases hnot_all with ⟨x, hx⟩
  let xbar : N.reduction := Submodule.Quotient.mk x
  have hxbar_ne_zero : xbar ≠ 0 := by
    intro hx0
    exact hx ((Submodule.Quotient.mk_eq_zero _).1 hx0)
  have hixbar_ne_zero : i.toLinearMap xbar ≠ 0 := by
    intro hix0
    apply hxbar_ne_zero
    exact subrepresentation_intersection_reduction_inclusion_injective_monoid
      (A := A) (K := K) U E₁ hix0
  have hrange_ne_bot : i.range ≠ ⊥ := by
    intro hbot
    have hxbar_mem : i.toLinearMap xbar ∈ i.range := by
      exact ⟨xbar, rfl⟩
    have hzero : i.toLinearMap xbar = 0 := by
      have : i.toLinearMap xbar ∈ (⊥ : Subrepresentation E₁.reductionRepresentation) := by
        simpa [hbot] using hxbar_mem
      simpa using this
    exact hixbar_ne_zero hzero
  -- Irreducibility forces every nonzero reduced subrepresentation to be the whole reduction.
  exact (IsSimpleOrder.eq_bot_or_eq_top i.range).resolve_left hrange_ne_bot

end StableLattice

-- Source/core/bridge triage:
-- * source-facing: the exercise compares simple reduction with homothety of stable lattices over a
--   discrete valuation ring.
-- * core/canonical: `StableLattice`, the canonical `Kˣ`-action on `StableLattice A ρ`,
--   `MulAction.IsPretransitive`, `StableLattice.reductionRepresentation`, and
--   `Representation.IsIrreducible`, with `[IsDiscreteValuationRing A]` as the ring-side owner
--   abstraction governing lattice comparison.
-- * bridge/view: `MulAction.IsPretransitive Kˣ (StableLattice A ρ)` is the canonical owner-level
--   reformulation of the fixed-lattice homothety criterion `∀ L, ∃ a : Kˣ, L = a • E₁`; the
--   source-facing homothety statement remains the main public entry.
-- Proof sketch: for a stable lattice `E₁`, irreducibility of the reduction means its lattice of
-- `G`-stable submodules has no nontrivial element. The usual Nakayama argument upgrades this to
-- uniqueness of `G`-stable lattices up to homothety; equivalently, the canonical `Kˣ`-action on
-- `StableLattice A ρ` is pretransitive. Conversely compare any stable lattice with `E₁`
-- through their reductions. The ambient `K[G]`-module must be nonzero for the converse
-- direction.
/-- Exercise 15-15.2-5 (1): for a nonzero `K[G]`-module over a discrete valuation ring, the
reduction of a `G`-stable lattice `E₁` is irreducible if and only if every `G`-stable lattice is a
homothety of `E₁`. -/
theorem simple_reduction_iff_forall_isHomothetic
    (ρ : Representation K G E) [Nontrivial E] (E₁ : StableLattice A ρ) :
    E₁.reductionRepresentation.IsIrreducible ↔
      ∀ L : StableLattice A ρ, ∃ a : Kˣ, L = a • E₁ := by
  constructor
  · intro hSimple L
    letI : E₁.reductionRepresentation.IsIrreducible := hSimple
    -- Route correction: first normalize `L` inside `E₁` so its reduction class is visibly
    -- nonzero.
    obtain ⟨a, ha, hnota⟩ :=
      StableLattice.exists_homothety_le_not_le_maximalIdeal_smul_monoid
        (A := A) (K := K) E₁ L
    let f :=
      StableLattice.reductionNestedMap_monoid
        (A := A) (K := K) (L₁ := E₁) (L₂ := a • L) ha
    have hrange_ne_bot : f.range ≠ ⊥ := by
      intro hbot
      apply hnota
      intro x hx
      let x' : (a • L).toSubmodule := ⟨x, hx⟩
      have hx_range : f (Submodule.Quotient.mk x') ∈ f.range := by
        exact ⟨Submodule.Quotient.mk x', rfl⟩
      have hx_zero : f (Submodule.Quotient.mk x') = 0 := by
        have : f (Submodule.Quotient.mk x') ∈ (⊥ : Subrepresentation E₁.reductionRepresentation) := by
          simpa [hbot] using hx_range
        simpa using this
      have hx_max :
          (Submodule.inclusion ha x' : E₁.toSubmodule) ∈ E₁.maximalIdealSubmodule := by
        have hmk :
            (Submodule.Quotient.mk (Submodule.inclusion ha x') : E₁.reduction) = 0 := by
          change f (Submodule.Quotient.mk x') = 0
          simpa [f, StableLattice.reductionNestedMap_monoid_apply_mk] using hx_zero
        exact (Submodule.Quotient.mk_eq_zero _).1 hmk
      -- A vanishing reduction class means the original vector already lies in `𝔪_A E₁`.
      simpa using
        StableLattice.coe_mem_maximalIdealSubmodule_monoid
          (A := A) (K := K) (L := E₁) hx_max
    have hrange_top : f.range = ⊤ :=
      (IsSimpleOrder.eq_bot_or_eq_top f.range).resolve_left hrange_ne_bot
    have hmap_top :
        Submodule.map E₁.maximalIdealSubmodule.mkQ
            (LinearMap.range (Submodule.inclusion ha)) = ⊤ := by
      rw [eq_top_iff]
      intro x hx
      have hx_range : x ∈ f.range := by simpa [hrange_top]
      rcases hx_range with ⟨y, rfl⟩
      rcases Quotient.exists_rep y with ⟨y', rfl⟩
      refine ⟨Submodule.inclusion ha y', ⟨y', rfl⟩, ?_⟩
      simpa [f] using
        (StableLattice.reductionNestedMap_monoid_apply_mk
          (A := A) (K := K) (L₁ := E₁) (L₂ := a • L) ha y').symm
    letI : Module.Finite A E₁.toSubmodule :=
      Module.Finite.of_fg (Submodule.IsLattice.fg (A := K) (M := E₁.toSubmodule))
    have hrange_eq_top : LinearMap.range (Submodule.inclusion ha) = ⊤ := by
      -- Nakayama upgrades surjectivity on the quotient to equality of the nested lattices.
      simpa [StableLattice.maximalIdealSubmodule] using
        (IsLocalRing.map_mkQ_eq_top (R := A) (M := E₁.toSubmodule)
          (N := LinearMap.range (Submodule.inclusion ha))).1 hmap_top
    have hsurj : Function.Surjective (Submodule.inclusion ha) :=
      LinearMap.range_eq_top.mp hrange_eq_top
    have hEqSub : (a • L).toSubmodule = E₁.toSubmodule := by
      apply le_antisymm ha
      intro x hx
      rcases hsurj ⟨x, hx⟩ with ⟨y, hy⟩
      have hy' : ((y : (a • L).toSubmodule) : E) = x := by
        simpa using congrArg Subtype.val hy
      exact hy' ▸ y.property
    have hEqLat : a • L = E₁ := StableLattice.ext_toSubmodule hEqSub
    refine ⟨a⁻¹, ?_⟩
    calc
      L = a⁻¹ • (a • L) := by
        calc
          L = (1 : Kˣ) • L := by simp
          _ = a⁻¹ • (a • L) := by simp [mul_smul]
      _ = a⁻¹ • E₁ := by rw [hEqLat]
  · intro hHom
    letI : Nontrivial E₁.reduction :=
      StableLattice.reduction_nontrivial_monoid (A := A) (K := K) E₁
    letI : Nontrivial (Subrepresentation E₁.reductionRepresentation) :=
      ⟨⊥, ⊤, fun h ↦
        bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
    refine IsSimpleOrder.of_forall_eq_top fun W hW ↦ ?_
    let N := StableLattice.reduction_preimage_stableLattice_monoid
      (A := A) (K := K) E₁ W
    let hNle := StableLattice.reduction_preimage_toSubmodule_le_monoid
      (A := A) (K := K) E₁ W
    let f := StableLattice.reductionNestedMap_monoid
      (A := A) (K := K) (L₁ := E₁) (L₂ := N) hNle
    have hf_range_eq : f.range = W := by
      -- The canonical preimage lattice was built precisely so that its reduced image is `W`.
      simpa [N, hNle, f] using
        (StableLattice.reduction_preimage_nested_range_eq_monoid
          (A := A) (K := K) E₁ W)
    have hN_not_le :
        ¬ N.toSubmodule ≤ (IsLocalRing.maximalIdeal A) • E₁.toSubmodule := by
      intro hNbad
      have hf_zero : ∀ z : N.reduction, f z = 0 := by
        intro z
        rcases Quotient.exists_rep z with ⟨y, rfl⟩
        have hymax :
            (Submodule.inclusion hNle y : E₁.toSubmodule) ∈ E₁.maximalIdealSubmodule := by
          apply StableLattice.mem_maximalIdealSubmodule_of_coe_mem_monoid
            (A := A) (K := K) (L := E₁)
          -- Membership in `𝔪_A E₁` comes from the assumed containment of `N`.
          simpa using hNbad y.property
        have hmk :
            (Submodule.Quotient.mk (Submodule.inclusion hNle y) : E₁.reduction) = 0 := by
          exact (Submodule.Quotient.mk_eq_zero _).2 hymax
        change (Submodule.Quotient.mk (Submodule.inclusion hNle y) : E₁.reduction) = 0
        exact hmk
      have hf_bot : f.range = ⊥ := by
        apply le_antisymm
        · intro z hz
          simp only [IntertwiningMap.range, LinearMap.mem_range] at hz
          rcases hz with ⟨y, rfl⟩
          simpa using hf_zero y
        · exact bot_le
      exact hW (hf_range_eq.symm.trans hf_bot)
    obtain ⟨a, hNhom⟩ := hHom N
    have hNsub_eq : N.toSubmodule = (a • E₁).toSubmodule := by
      simpa using congrArg (fun L : StableLattice A ρ => L.toSubmodule) hNhom
    have ha_le : (a • E₁).toSubmodule ≤ E₁.toSubmodule := by
      rw [← hNsub_eq]
      exact hNle
    have ha_not_le :
        ¬ (a • E₁).toSubmodule ≤ (IsLocalRing.maximalIdeal A) • E₁.toSubmodule := by
      rw [← hNsub_eq]
      exact hN_not_le
    have hN_eq : N = E₁ := by
      calc
        N = a • E₁ := hNhom
        _ = E₁ := StableLattice.smul_eq_of_le_not_le_maximalIdeal_monoid
          (A := A) (K := K) E₁ ha_le ha_not_le
    have hf_top : f.range = ⊤ := by
      -- Route correction: prove surjectivity for the actual nested map from equality of the
      -- underlying lattices, instead of rewriting the map through a dependent equality.
      exact StableLattice.reductionNestedMap_range_eq_top_of_toSubmodule_eq_monoid
        (A := A) (K := K) (L₁ := E₁) (L₂ := N) hNle
        (congrArg (fun L : StableLattice A ρ => L.toSubmodule) hN_eq)
    exact hf_range_eq.symm.trans hf_top

/-- Companion canonical bridge for Exercise 15-15.2-5 (1). -/
theorem simple_reduction_iff_isPretransitive
    (ρ : Representation K G E) [Nontrivial E] (E₁ : StableLattice A ρ) :
    E₁.reductionRepresentation.IsIrreducible ↔
      MulAction.IsPretransitive Kˣ (StableLattice A ρ) := by
  rw [simple_reduction_iff_forall_isHomothetic ρ E₁]
  constructor
  · intro h
    refine ⟨?_⟩
    intro L M
    rcases h L with ⟨a, ha⟩
    rcases h M with ⟨b, hb⟩
    refine ⟨b * a⁻¹, ?_⟩
    calc
      (b * a⁻¹) • L = (b * a⁻¹) • (a • E₁) := by rw [ha]
      _ = b • E₁ := by simp [mul_smul]
      _ = M := by rw [← hb]
  · intro h L
    obtain ⟨a, ha⟩ := h.exists_smul_eq E₁ L
    exact ⟨a, ha.symm⟩

end FractionRingAmbient

section FieldAmbient

variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable [Module K E] [IsScalarTower A K E]

-- Proof sketch: if the reduction of `E₁` is irreducible, then every stable lattice is homothetic to
-- `E₁` by `simple_reduction_iff_forall_isHomothetic`; equivalently, the `Kˣ`-action on stable
-- lattices is pretransitive by `simple_reduction_iff_isPretransitive`. A nonzero proper `G`-stable
-- `K`-subspace of `E` would
-- then produce a second stable lattice not homothetic to `E₁`, giving a contradiction.
/-- Exercise 15-15.2-5 (2): over a discrete valuation ring, if the reduction of `E₁` is
irreducible, then `ρ` is irreducible as a `K[G]`-module, equivalently a simple object of
`Rep K G`. -/
theorem simple_reduction_implies_isIrreducible
    (ρ : Representation K G E) (E₁ : StableLattice A ρ)
    (hE₁ : E₁.reductionRepresentation.IsIrreducible) :
    ρ.IsIrreducible := by
  letI : Nontrivial E :=
    StableLattice.nontrivial_ambient_of_irreducible_reduction_monoid
      (A := A) (K := K) E₁ hE₁
  letI : Nontrivial (Subrepresentation ρ) :=
    ⟨⊥, ⊤, fun h ↦
      bot_ne_top <| by simpa using congrArg Subrepresentation.toSubmodule h⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  let N := StableLattice.subrepresentation_intersection_stableLattice_monoid
    (A := A) (K := K) U E₁
  let i := StableLattice.subrepresentation_intersection_reduction_inclusion_monoid
    (A := A) (K := K) U E₁
  have hi_range_top : i.range = ⊤ :=
    StableLattice.subrepresentation_intersection_reduction_range_eq_top_of_simple_monoid
      (A := A) (K := K) U E₁ hE₁ hU
  have hmap_top :
      Submodule.map E₁.maximalIdealSubmodule.mkQ
        (LinearMap.range
          (StableLattice.subrepresentation_intersection_inclusion_monoid
            (A := A) (K := K) U E₁)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx_range : x ∈ i.range := by
      simpa [hi_range_top]
    rcases hx_range with ⟨y, rfl⟩
    rcases Quotient.exists_rep y with ⟨y', rfl⟩
    refine ⟨StableLattice.subrepresentation_intersection_inclusion_monoid
      (A := A) (K := K) U E₁ y', ⟨y', rfl⟩, ?_⟩
    change
      (Submodule.Quotient.mk
        (StableLattice.subrepresentation_intersection_inclusion_monoid
          (A := A) (K := K) U E₁ y') : E₁.reduction) =
        i (Submodule.Quotient.mk y')
    rfl
  letI : Module.Finite A E₁.toSubmodule :=
    Module.Finite.of_fg (Submodule.IsLattice.fg (A := K) (M := E₁.toSubmodule))
  have hrange_eq_top :
      LinearMap.range
          (StableLattice.subrepresentation_intersection_inclusion_monoid
            (A := A) (K := K) U E₁) = ⊤ := by
    -- Nakayama upgrades surjectivity on the reduction to surjectivity on the lattice itself.
    simpa [StableLattice.maximalIdealSubmodule] using
      (IsLocalRing.map_mkQ_eq_top (R := A) (M := E₁.toSubmodule)
        (N := LinearMap.range
          (StableLattice.subrepresentation_intersection_inclusion_monoid
            (A := A) (K := K) U E₁))).1 hmap_top
  have hsurj :
      Function.Surjective
        (StableLattice.subrepresentation_intersection_inclusion_monoid
          (A := A) (K := K) U E₁) :=
    LinearMap.range_eq_top.mp hrange_eq_top
  have hE₁_le_U : ∀ ⦃x : E⦄, x ∈ E₁.toSubmodule → x ∈ U.toSubmodule := by
    intro x hx
    rcases hsurj ⟨x, hx⟩ with ⟨y, hy⟩
    have hyE : (((y : N.toSubmodule) : U.toSubmodule) : E) = x := by
      simpa using congrArg Subtype.val hy
    exact hyE ▸ (((y : N.toSubmodule) : U.toSubmodule)).property
  have hU_top : U.toSubmodule = ⊤ := by
    rw [eq_top_iff]
    intro x _
    -- Because `E₁` spans `E`, containing `E₁` already forces `U` to be all of `E`.
    have hx_span : x ∈ Submodule.span K (E₁.toSubmodule : Set E) := by
      rw [Submodule.IsLattice.span_eq_top (A := K) (M := E₁.toSubmodule)]
      trivial
    exact (Submodule.span_le.2 fun y hy ↦ hE₁_le_U hy) hx_span
  exact Subrepresentation.toSubmodule_injective hU_top

end FieldAmbient

end StableLatticeRigidity

end Representation
