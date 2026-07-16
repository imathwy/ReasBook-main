import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap13.Definition_13_11_3
import StacksProject_2024.stacks_project.Chap10.Definition_10_17_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_71_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_65_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_67_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_71_3
import StacksProject_2024.stacks_project.Chap15.Definition_15_89_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_85_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open PrimeSpectrum
open scoped PrimeSpectrum

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation:max "H^" i:max => DerivedCategory.homologyFunctor (ModuleCat R) i

/- Domain-style sampling for Lemma 15.85.10:
- primary domain: two-term derived `R`-complexes, `I`-projective cohomology, and finite
  basic-open localization criteria for projectivity on the open complement `Spec R \ V(I)`;
- sampled owner declarations in this domain:
  `Module.IsIdealProjective`,
  `Module.IsIdealPowerTorsion`,
  `Module.LocallyFree`,
  `twoTermExtOneAnnihilatedByIdeal`,
  `twoTermExtOneAnnihilatedByIdealOnFiniteModules`;
- best owner abstraction: the primitive source data is the pair of cohomology modules
  `H^(-1)(K)` and `H^0(K)` together with the chapter owners `Module.IsIdealProjective` and
  `Module.IsIdealPowerTorsion`; the localization-cover clauses are source-facing finite-set
  projectivity criteria for `H⁰(K)` on finite basic-open neighborhoods of `Spec R \ V(I)`, so
  they stay inline in the theorem statement rather than being promoted to separate public owners;
- primitive data vs. derived API: annihilator containment, ideal-projectivity, and localized
  projectivity of `H⁰(K)` are primitive clause data, while the `Ext¹` reformulations are derived
  API supplied upstream by Lemma `15.85.5`.

Source/core/bridge triage:
- `source-facing`: the TFAE statements below and their finite-localization clauses;
- `core/canonical`: `Module.IsIdealProjective`, `Module.IsIdealPowerTorsion`,
  `twoTermExtOneAnnihilatedByIdeal`, and `twoTermExtOneAnnihilatedByIdealOnFiniteModules`;
- `bridge/view`: the comparison between the cohomology-side conditions and the `Ext¹` conditions.
-/

-- Proof sketch: use the distinguished triangle
-- `H^{-1}(K)[1] ⟶ K ⟶ H^0(K)[0] ⟶ H^{-1}(K)[2]` to compare annihilation of `Ext^1_R(K, N)` by
-- powers of `I` with annihilation of `H^{-1}(K)` and `I^c`-projectivity of `H^0(K)`. In the
-- Noetherian finite case, combine Lemma `15.85.5` with the local criterion for `I`-projective
-- modules and the standard algebraic equivalences between `V(f_1, ..., f_s)` and powers of `I`.
/-- Helper for Lemma 15.85.10: a finite `I`-power-torsion module is annihilated by a single power
of `I`. -/
lemma finite_isIdealPowerTorsion_uniform_annihilator
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (hM : Module.IsIdealPowerTorsion I M) :
    ∃ c : ℕ, I ^ c ≤ Module.annihilator R M := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  -- Proof comment: record one annihilating power for each generator in a finite free cover.
  have hgen :
      ∀ i : Fin n,
        ∃ m : ℕ+, ∀ a : ↥(I ^ (m : ℕ)), (a : R) • π (Pi.basisFun R (Fin n) i) = 0 := by
    intro i
    exact (Module.isIdealPowerTorsion_iff I).1 hM (π (Pi.basisFun R (Fin n) i))
  choose exponent hexponent using hgen
  let c : ℕ := Finset.univ.sup fun i : Fin n ↦ (exponent i : ℕ)
  refine ⟨c, ?_⟩
  intro a ha
  rw [Module.mem_annihilator]
  intro x
  rcases hπ x with ⟨y, rfl⟩
  -- Proof comment: expand a chosen preimage in the standard basis of the finite free cover.
  have hy : y = ∑ i, Pi.single i (y i) := by
    ext i
    simp [Pi.single_apply]
  rw [hy, map_sum, Finset.smul_sum]
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hsingle :
      Pi.single i (y i) = y i • Pi.basisFun R (Fin n) i := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Pi.basisFun]
    · simp [Pi.basisFun, hj]
  rw [hsingle, LinearMap.map_smul]
  have hle : (exponent i : ℕ) ≤ c := by
    dsimp [c]
    exact Finset.le_sup (f := fun j : Fin n ↦ (exponent j : ℕ)) (by simp)
  have hkill : (a : R) • π (Pi.basisFun R (Fin n) i) = 0 := by
    exact hexponent i ⟨a, Ideal.pow_le_pow_right hle ha⟩
  calc
    (a : R) • (y i • π (Pi.basisFun R (Fin n) i))
        = y i • ((a : R) • π (Pi.basisFun R (Fin n) i)) := by
            rw [smul_smul, mul_comm, ← smul_smul]
    _ = 0 := by
      rw [hkill, smul_zero]

/-- Helper for Lemma 15.85.10: if a power of `I` annihilates a module, then the module is
`I`-power torsion. -/
private theorem isIdealPowerTorsion_of_pow_le_annihilator
    {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ)
    (hM : I ^ n ≤ Module.annihilator R M) :
    Module.IsIdealPowerTorsion I M := by
  rw [Module.isIdealPowerTorsion_iff]
  intro x
  refine ⟨⟨n + 1, Nat.succ_pos n⟩, ?_⟩
  intro a
  -- Proof comment: any element of `I^(n + 1)` already lies in `I^n`, so the fixed annihilator
  -- power kills every module element.
  exact Module.mem_annihilator.mp (hM (Ideal.pow_le_pow_right (Nat.le_succ n) a.2)) x

/-- Helper for Lemma 15.85.10: a retract of a projective module is projective. -/
private theorem module_projective_of_retract
    {M : Type u} [AddCommGroup M] [Module R M]
    {P : Type u} [AddCommGroup P] [Module R P]
    [Module.Projective R P]
    (i : M →ₗ[R] P) (r : P →ₗ[R] M)
    (hr : r.comp i = LinearMap.id) :
    Module.Projective R M := by
  rcases (Module.Projective.iff_split (R := R) (P := P)).mp inferInstance with
    ⟨F, hFAdd, hFModule, hFFree, j, s, hs⟩
  letI : AddCommMonoid F := hFAdd
  letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup R
  letI : Module R F := hFModule
  letI : Module.Projective R F := Module.Projective.of_free
  -- Proof comment: compose the given retract `M ↪ P ↠ M` with a free splitting of the
  -- projective module `P`, so `M` becomes a direct summand of a free module.
  have hsplit : (r.comp s).comp (j.comp i) = LinearMap.id := by
    ext x
    calc
      r (s (j (i x))) = r (i x) := by
        exact congrArg r (LinearMap.congr_fun hs (i x))
      _ = x := by
        simpa using LinearMap.congr_fun hr x
  exact Module.Projective.of_split (j.comp i) (r.comp s) hsplit

/-- Helper for Lemma 15.85.10: a module that is `⊤`-projective is projective. -/
private theorem projective_of_isIdealProjective_top
    {M : Type u} [AddCommGroup M] [Module R M]
    (hM : Module.IsIdealProjective (⊤ : Ideal R) M) :
    Module.Projective R M := by
  let oneTop : (⊤ : Ideal R) := ⟨1, by simp⟩
  rcases hM.factorsThroughProjective oneTop with ⟨P, hPAdd, hPModule, hPproj, i, r, hir⟩
  letI : AddCommMonoid P := hPAdd
  letI : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  letI : Module R P := hPModule
  letI : Module.Projective R P := hPproj
  -- Proof comment: the scalar action by `1` is the identity, so the factorization from
  -- `⊤`-projectivity already exhibits `M` as a retract of a projective module.
  have hsplit : r.comp i = LinearMap.id := by
    ext x
    have hx := congrArg (fun φ : M →ₗ[R] M ↦ φ x) hir.symm
    change r (i x) = (1 : R) • x at hx
    simpa using hx
  exact module_projective_of_retract (R := R) i r hsplit

/-- Helper for Lemma 15.85.10: localizing an `I^c`-projective module away from an element of `I`
produces a projective localized module. -/
private theorem localizedAway_projective_of_isIdealProjective_pow_mem
    {M : Type u} [AddCommGroup M] [Module R M]
    (I : Ideal R) (c : ℕ)
    (hM : Module.IsIdealProjective (I ^ c) M)
    {f : R} (hf : f ∈ I) :
    Module.Projective (Localization.Away f) (LocalizedModule.Away f M) := by
  let aPow : ↥(I ^ c) := ⟨f ^ c, Ideal.pow_mem_pow hf c⟩
  rcases hM.factorsThroughProjective aPow with ⟨P, hPAdd, hPModule, hPproj, i, r, hir⟩
  letI : AddCommMonoid P := hPAdd
  letI : AddCommGroup P := Module.addCommMonoidToAddCommGroup R
  letI : Module R P := hPModule
  letI : Module.Projective R P := hPproj
  have hPprojTensor :
      Module.Projective (Localization.Away f) (TensorProduct R (Localization.Away f) P) := by
    -- Proof comment: projectivity survives extension of scalars to the away-localization ring.
    exact Module.Projective.tensorProduct
  letI : Module.Projective (Localization.Away f) (TensorProduct R (Localization.Away f) P) :=
    hPprojTensor
  have hPprojLoc :
      Module.Projective (Localization.Away f) (LocalizedModule.Away f P) := by
    -- Proof comment: transport the tensor-product projective module to the canonical localized
    -- module model.
    exact Module.Projective.of_equiv
      (LocalizedModule.equivTensorProduct (Submonoid.powers f) P).symm
  letI : Module.Projective (Localization.Away f) (LocalizedModule.Away f P) := hPprojLoc
  let iLoc : LocalizedModule.Away f M →ₗ[Localization.Away f] LocalizedModule.Away f P :=
    (LocalizedModule.map (Submonoid.powers f)) i
  let rLoc : LocalizedModule.Away f P →ₗ[Localization.Away f] LocalizedModule.Away f M :=
    (LocalizedModule.map (Submonoid.powers f)) r
  have hmap_comp :
      (LocalizedModule.map (Submonoid.powers f)) (r.comp i) = rLoc.comp iLoc := by
    -- Proof comment: localization respects the chosen factorization of the scalar map.
    ext x
    induction x using LocalizedModule.induction_on with
    | h m s =>
        simp [iLoc, rLoc, LocalizedModule.map_mk]
  have hsmul_loc :
      (LocalizedModule.map (Submonoid.powers f)) (LinearMap.lsmul R M (f ^ c)) =
        LinearMap.lsmul (Localization.Away f) (LocalizedModule.Away f M)
          (algebraMap R (Localization.Away f) (f ^ c)) := by
    -- Proof comment: localizing multiplication by `f^c` is exactly multiplication by the image of
    -- `f^c` in the away-localization.
    ext x
    induction x using LocalizedModule.induction_on with
    | h m s =>
        rw [LocalizedModule.map_mk]
        simpa [Localization.mk_one_eq_algebraMap, RingHom.map_pow] using
          (LocalizedModule.mk_smul_mk (R := R) (S := Submonoid.powers f)
            (f ^ c) m (1 : Submonoid.powers f) s).symm
  have hscalar :
      LinearMap.lsmul (Localization.Away f) (LocalizedModule.Away f M)
          (algebraMap R (Localization.Away f) (f ^ c)) = rLoc.comp iLoc := by
    calc
      LinearMap.lsmul (Localization.Away f) (LocalizedModule.Away f M)
          (algebraMap R (Localization.Away f) (f ^ c))
          = (LocalizedModule.map (Submonoid.powers f)) (LinearMap.lsmul R M (f ^ c)) := by
              symm
              exact hsmul_loc
      _ = (LocalizedModule.map (Submonoid.powers f)) (r.comp i) := by
            rw [hir]
      _ = rLoc.comp iLoc := hmap_comp
  have hfPow : f ^ c ∈ Submonoid.powers f := by
    exact ⟨c, by simp⟩
  have hUnit : IsUnit (algebraMap R (Localization.Away f) (f ^ c)) := by
    -- Proof comment: the chosen scalar becomes invertible after localizing away from `f`.
    exact IsLocalization.map_units (Localization.Away f) ⟨f ^ c, hfPow⟩
  let sLoc : LocalizedModule.Away f P →ₗ[Localization.Away f] LocalizedModule.Away f M :=
    (LinearMap.lsmul (Localization.Away f) (LocalizedModule.Away f M) ↑(hUnit.unit⁻¹)).comp rLoc
  have hsplit : sLoc.comp iLoc = LinearMap.id := by
    -- Proof comment: after multiplying by the inverse of the now-unit scalar, the localized
    -- factorization becomes a genuine splitting of the identity.
    ext x
    have hx : rLoc (iLoc x) = (algebraMap R (Localization.Away f) (f ^ c)) • x := by
      simpa [LinearMap.lsmul_apply] using congrArg (fun φ ↦ φ x) hscalar.symm
    calc
      (sLoc.comp iLoc) x = (↑(hUnit.unit⁻¹) : Localization.Away f) • (rLoc (iLoc x)) := by
        simp [sLoc, iLoc, LinearMap.lsmul_apply]
      _ = (↑(hUnit.unit⁻¹) : Localization.Away f) •
            ((algebraMap R (Localization.Away f) (f ^ c)) • x) := by
              rw [hx]
      _ = ((↑(hUnit.unit⁻¹) : Localization.Away f) *
            algebraMap R (Localization.Away f) (f ^ c)) • x := by
              rw [smul_smul]
      _ = x := by
        have hmul :
            (↑(hUnit.unit⁻¹) : Localization.Away f) *
              algebraMap R (Localization.Away f) (f ^ c) = 1 := by
          simpa [hUnit.unit_spec] using Units.val_inv_mul hUnit.unit
        rw [hmul, one_smul]
  exact Module.Projective.of_split iLoc sLoc hsplit

/-- Helper for Lemma 15.85.10: a two-term free representative with the scalar-factorization
property forces the expected annihilator and `I`-projectivity statements on cohomology. -/
private theorem annihilator_and_isIdealProjective_of_two_term_factorization
    (K : DMod) {J : Ideal R}
    (hfactor : admits_two_term_free_representative_with_ideal_factorization K J) :
    J ≤ Module.annihilator R ((H^(-1)).obj K) ∧
      Module.IsIdealProjective J ((H^0).obj K) := by
  -- Route correction: the public theorem now delegates the source-faithful representative-to-
  -- cohomology comparison to a dedicated bridge lemma instead of leaving the whole TFAE proof
  -- opaque. The kernel/cokernel normalization layer needs to be rebuilt against the current API.
  sorry

/-- Helper for Lemma 15.85.10: the cohomological annihilator and `I`-projectivity hypotheses force
the `Ext¹` annihilation condition after squaring the ideal. -/
private theorem twoTermExtOneAnnihilatedByIdeal_of_annihilator_and_isIdealProjective
    (K : DMod) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) {J : Ideal R}
    (hcoh :
      J ≤ Module.annihilator R ((H^(-1)).obj K) ∧
        Module.IsIdealProjective J ((H^0).obj K)) :
    twoTermExtOneAnnihilatedByIdeal K (J ^ 2) := by
  -- Route correction: the reverse bridge needs the bounded two-term window on `K` in order to
  -- use `truncGE_step_homologyTriangle_local K (-1)` as the source triangle
  -- `H^{-1}(K)[1] ⟶ K ⟶ H^0(K)[0] ⟶ H^{-1}(K)[2]`.
  -- TODO for Lemma 15.85.10: factor the first scalar action through the triangle
  -- `truncGE_step_homologyTriangle_local K (-1)` using `Triangle.yoneda_exact₂`; then use
  -- `hAnnH0` to kill the resulting `Ext¹(H^0(K), N)` class and conclude that every
  -- `a ∈ J ^ 2` annihilates `e`.
  sorry

/-- Helper for Lemma 15.85.10: finite-test annihilation by a power of `I` forces projectivity of
`H^0(K)` after localizing away any element of `I`. -/
private theorem localized_projective_h0_of_annihilated_finite_test_modules
    [IsNoetherianRing R]
    (K : DMod) (I : Ideal R)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H^(-1)).obj K))
    (hH0 : Module.Finite R ((H^0).obj K))
    {c : ℕ}
    (hc : twoTermExtOneAnnihilatedByIdealOnFiniteModules K (I ^ c)) :
    ∀ f ∈ I,
      Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K)) := by
  intro f hf
  have hTFAE :=
      two_term_ext1_annihilated_tfae_of_isNoetherianRing
        K (I ^ c) hKGE hKLE hHneg1 hH0
  have hfactor : admits_two_term_free_representative_with_ideal_factorization K (I ^ c) :=
    (hTFAE.out 3 1).mp hc
  have hcoh :
      I ^ c ≤ Module.annihilator R ((H^(-1)).obj K) ∧
        Module.IsIdealProjective (I ^ c) ((H^0).obj K) :=
    annihilator_and_isIdealProjective_of_two_term_factorization (R := R) K hfactor
  -- Proof comment: after converting finite-test Ext-annihilation to the two-term factorization
  -- clause, the already-proved localization lemma applies directly to the `I^c`-projective
  -- cohomology module `H^0(K)`.
  exact localizedAway_projective_of_isIdealProjective_pow_mem (R := R) I c hcoh.2 hf

/-- Helper for Lemma 15.85.10: a finite localization cover of projective localizations and
`I`-power torsion on `H^{-1}(K)` produce a single power of `I` giving the cohomological clause
`(2)`. -/
private theorem annihilator_and_isIdealProjective_of_power_torsion_and_localized_cover
    [IsNoetherianRing R]
    (K : DMod) (I : Ideal R)
    (hHneg1 : Module.Finite R ((H^(-1)).obj K))
    (hH0 : Module.Finite R ((H^0).obj K))
    (hcover :
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∃ s : Finset R,
          V((↑s : Set R)) ⊆ V((I : Set R)) ∧
            ∀ f ∈ s,
              Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K))) :
    ∃ c : ℕ,
      I ^ c ≤ Module.annihilator R ((H^(-1)).obj K) ∧
        Module.IsIdealProjective (I ^ c) ((H^0).obj K) := by
  -- TODO for Lemma 15.85.10: first use finite `I`-power torsion of `H^{-1}(K)` to get a uniform
  -- annihilator power, then kill the chosen presentation class of `H^0(K)` after localizing at
  -- the cover elements and descend from the cover ideal to a power of `I` via the Noetherian
  -- radical-containment lemma.
  sorry

/-- Lemma 15.85.10: for a derived `R`-complex `K` with cohomology concentrated in degrees `-1`
and `0`, the existence of a power `I^c` satisfying the equivalent conditions `(1)`, `(2)`, `(3)`
of Lemma `15.85.5` is equivalent to the existence of a power `I^c` that annihilates `H^{-1}(K)`
and makes `H^0(K)` `I^c`-projective. -/
theorem two_term_ideal_power_projectivity_tfae
    (K : DMod) (I : Ideal R)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0) :
    List.TFAE [
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdeal K (I ^ c),
      ∃ c : ℕ,
        I ^ c ≤ Module.annihilator R ((H^(-1)).obj K) ∧
          Module.IsIdealProjective (I ^ c) ((H^0).obj K)
    ] := by
  tfae_have 1 → 2 := by
    intro hExt
    rcases hExt with ⟨c, hc⟩
    have hTFAE := two_term_ext1_annihilated_tfae K (I ^ c) hKGE hKLE
    have hfactor : admits_two_term_free_representative_with_ideal_factorization K (I ^ c) :=
      (hTFAE.out 0 1).mp hc
    -- Proof comment: Lemma `15.85.5` converts Ext-annihilation to the two-term free
    -- factorization clause, and the remaining bridge reads the desired cohomology statement off
    -- that representative.
    exact ⟨c, annihilator_and_isIdealProjective_of_two_term_factorization (R := R) K hfactor⟩
  tfae_have 2 → 1 := by
    intro hCoh
    rcases hCoh with ⟨c, hc⟩
    refine ⟨c * 2, ?_⟩
    -- Proof comment: the reverse bridge kills Ext¹ after squaring the ideal, and
    -- `(I ^ c) ^ 2 = I ^ (c * 2)` rewrites the result to the displayed power.
    simpa [pow_mul] using
      twoTermExtOneAnnihilatedByIdeal_of_annihilator_and_isIdealProjective
        (R := R) K hKGE hKLE hc
  tfae_finish

/-- Lemma 15.85.10, Noetherian finite case: if `R` is Noetherian and `H^{-1}(K)` and `H^0(K)` are
finite, then the two equivalent conditions of `two_term_ideal_power_projectivity_tfae` are also
equivalent to the finite-module version of Lemma `15.85.5` and to the local projectivity criteria
obtained from finite families cutting out `V(I)`, viewed as finite basic-open covers of
`Spec R \ V(I)`. -/
theorem two_term_ideal_power_projectivity_tfae_of_isNoetherianRing
    [IsNoetherianRing R]
    (K : DMod) (I : Ideal R)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H^(-1)).obj K))
    (hH0 : Module.Finite R ((H^0).obj K)) :
    List.TFAE [
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdeal K (I ^ c),
      ∃ c : ℕ,
        I ^ c ≤ Module.annihilator R ((H^(-1)).obj K) ∧
          Module.IsIdealProjective (I ^ c) ((H^0).obj K),
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdealOnFiniteModules K (I ^ c),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∃ s : Finset R,
          V((↑s : Set R)) ⊆ V((I : Set R)) ∧
            ∀ f ∈ s, Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K)),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∃ s : Finset R,
          (↑s : Set R) ⊆ I ∧
            V((↑s : Set R)) = V((I : Set R)) ∧
              ∀ f ∈ s,
                Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K)),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
      ∀ s : Finset R,
        (↑s : Set R) ⊆ I →
            V((↑s : Set R)) = V((I : Set R)) →
              ∀ f ∈ s,
                Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K))
    ] := by
  have hBase := two_term_ideal_power_projectivity_tfae (R := R) K I hKGE hKLE
  tfae_have 1 ↔ 2 := by
    exact hBase.out 0 1
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hExt
      rcases hExt with ⟨c, hc⟩
      have hTFAE :=
          two_term_ext1_annihilated_tfae_of_isNoetherianRing
            K (I ^ c) hKGE hKLE hHneg1 hH0
      -- Proof comment: the finite-test clause is exactly clause `(4)` of Lemma `15.85.5` in the
      -- Noetherian finite setting.
      exact ⟨c, (hTFAE.out 0 3).mp hc⟩
    · intro hFinite
      rcases hFinite with ⟨c, hc⟩
      have hTFAE :=
          two_term_ext1_annihilated_tfae_of_isNoetherianRing
            K (I ^ c) hKGE hKLE hHneg1 hH0
      exact ⟨c, (hTFAE.out 3 0).mp hc⟩
  tfae_have 2 → 6 := by
    intro hCoh
    rcases hCoh with ⟨c, hc⟩
    refine ⟨isIdealPowerTorsion_of_pow_le_annihilator (R := R) I c hc.1, ?_⟩
    intro s hsI hsV
    intro f hf
    -- Proof comment: every `f ∈ I` gives a projective localization of `H^0(K)` once
    -- `H^0(K)` is `I^c`-projective.
    exact localizedAway_projective_of_isIdealProjective_pow_mem (R := R) I c hc.2 (hsI hf)
  tfae_have 6 → 5 := by
    intro hLocal
    rcases hLocal with ⟨hTor, hLocal⟩
    obtain ⟨U, hUfinite, hUspan⟩ := Submodule.fg_def.mp (Ideal.fg_of_isNoetherianRing I)
    let s : Finset R := hUfinite.toFinset
    have hsU : (↑s : Set R) = U := by
      simpa [s] using hUfinite.coe_toFinset
    have hsI : (↑s : Set R) ⊆ I := by
      intro x hx
      have hxU : x ∈ U := by
        simpa [hsU] using hx
      simpa [hUspan] using (Ideal.subset_span hxU : x ∈ Ideal.span U)
    have hsV : V((↑s : Set R)) = V((I : Set R)) := by
      ext p
      rw [mem_V, mem_V]
      constructor
      · intro hp
        have hpU : U ⊆ p.asIdeal := by
          simpa [hsU] using hp
        have hspan : Ideal.span U ≤ p.asIdeal := Ideal.span_le.mpr hpU
        simpa [hUspan] using hspan
      · intro hp
        exact hsI.trans hp
    -- Proof comment: Noetherianity supplies one finite generating set of `I`, and the universal
    -- localization hypothesis specializes to that generating family.
    exact ⟨hTor, s, hsI, hsV, hLocal s hsI hsV⟩
  tfae_have 5 → 4 := by
    intro hCover
    rcases hCover with ⟨hTor, s, hsI, hsV, hsProj⟩
    exact ⟨hTor, s, hsV.le, hsProj⟩
  tfae_have 4 → 2 := by
    intro hCover
    rcases annihilator_and_isIdealProjective_of_power_torsion_and_localized_cover
        (R := R) K I hHneg1 hH0 hCover with
      ⟨c, hc⟩
    exact ⟨c, hc⟩
  tfae_finish

end

end CategoryTheory
