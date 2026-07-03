import Mathlib
import StacksProject_2024.Chap10.Definition_10_72_1
import StacksProject_2024.Chap10.Lemma_10_72_6
import StacksProject_2024.Chap10.Lemma_10_75_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory
open HomologicalComplex
open scoped ENat

noncomputable section

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/- Domain-style sampling:
* primary domain: bounded-above chain complexes of finite modules over a Noetherian local ring,
  with exactness organized by the owner predicate `HomologicalComplex.ExactAt`;
* sampled owner declarations in this domain: `HomologicalComplex.ExactAt`,
  `HomologicalComplex.ExactAt.iff_isZero_homology`, `moduleDepth`, and
  `CategoryTheory.ShortComplex.ShortExact.moduleDepth_middle_ge_min`;
* best owner abstraction: exactness should stay on `C.ExactAt j`, while local depth should be
  stated through the chapter owner `moduleDepth` rather than by repeating
  `Ideal.depth (IsLocalRing.maximalIdeal R)`;
* source/core/bridge triage: the acyclicity lemma below is `source-facing`, the owner notions are
  `C.ExactAt` and `moduleDepth`, and the homology-finiteness instance is only the bridge needed to
  make `moduleDepth R (C.homology i)` available;
* primitive vs. derived split: the primitive data are the chain complex `C`, the bounded-above
  index range, and the tail depth and exactness hypotheses on the truncated complex from degree
  `i` up to degree `e`. Finiteness of `C.homology j` is derived API from the termwise finiteness
  assumption, so it should not be restated as extra theorem data.
-/

namespace ChainComplex

/-- Homology of a chain complex of finite modules over a Noetherian ring is finite. -/
instance homology_finite
    (C : ChainComplex (ModuleCat.{u} R) ℕ) [∀ j, Module.Finite R (C.X j)] (j : ℕ) :
    Module.Finite R (C.homology j) :=
  ModuleCat.homology_finite_of_termwise_finite (R := R) C j

end ChainComplex

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): a linear equivalence preserves the set of
regular-sequence lengths inside a fixed ideal. -/
private theorem regularSequenceLengths_eq_of_linearEquiv {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.regularSequenceLengths I M = Ideal.regularSequenceLengths I N := by
  -- Transport the regular sequence across the linear equivalence in both directions.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): depth is invariant under a linear equivalence
of finite modules. -/
private theorem idealDepth_eq_of_linearEquiv {M : Type v} {N : Type w} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (I : Ideal R) (e : M ≃ₗ[R] N) :
    Ideal.depth I M = Ideal.depth I N := by
  -- The `I • M = M` branch is preserved by the equivalence, and otherwise the same
  -- regular-sequence lengths compute the depth on both sides.
  have htop : I • (⊤ : Submodule R M) = ⊤ ↔ I • (⊤ : Submodule R N) = ⊤ := by
    constructor
    · intro h
      have := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using this
    · intro h
      have := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using this
  by_cases hM : I • (⊤ : Submodule R M) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I M hM, Ideal.depth_eq_top_of_smul_top I N (htop.mp hM)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I M hM,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N (mt htop.mpr hM),
      regularSequenceLengths_eq_of_linearEquiv (R := R) (M := M) (N := N) I e]

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): depth is invariant under a linear equivalence
of finite modules. -/
private theorem moduleDepth_eq_of_linearEquiv {M : Type v} {N : Type w} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (e : M ≃ₗ[R] N) :
    moduleDepth R M = moduleDepth R N := by
  -- Specialize ideal-depth invariance to the maximal ideal of the local ring.
  simpa [moduleDepth] using
    idealDepth_eq_of_linearEquiv (R := R) (M := M) (N := N) (IsLocalRing.maximalIdeal R) e

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): a finite zero module has infinite depth. -/
private theorem moduleDepth_eq_top_of_subsingleton (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Subsingleton M] :
    moduleDepth R M = ⊤ := by
  -- Every element is zero, so the maximal ideal acts surjectively on the top submodule.
  have hsmul : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
    ext x
    simp [Subsingleton.elim x 0]
  change Ideal.depth (IsLocalRing.maximalIdeal R) M = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal R) M hsmul

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): exactness at a positive degree of a chain
complex of modules is exactness of the consecutive differentials as linear maps. -/
private lemma exactAt_iff_function_exact
    (C : ChainComplex (ModuleCat.{u} R) ℕ) {j : ℕ} (hj : 1 ≤ j) :
    C.ExactAt j ↔ Function.Exact (C.d (j + 1) j).hom (C.d j (j - 1)).hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hmid : 1 + k = k + 1 := by omega
  have hsucc : k + 1 + 1 = k + 2 := by omega
  have hpred : k + 1 - 1 = k := by omega
  -- Rewrite `ExactAt` through the explicit three-term short complex.
  rw [hmid, hsucc, hpred]
  rw [HomologicalComplex.exactAt_iff' C (k + 2) (k + 1) k (by simp) (by simp)]
  -- For modules, short-complex exactness is just `Function.Exact`.
  simpa [HomologicalComplex.sc'] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (C.sc' (k + 2) (k + 1) k))

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): in the chain-complex shape on `ℕ`, the next
index is the predecessor. -/
private lemma chainComplex_next_eq_pred (j : ℕ) :
    (ComplexShape.down ℕ).next j = j - 1 := by
  cases j with
  | zero => simp
  | succ j => simp

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the canonical row
`0 → N → M → M / N → 0` as a short complex of modules. -/
private abbrev submodule_quotient_shortComplex {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk N.subtype N.mkQ (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the canonical quotient row
`0 → N → M → M / N → 0` is short exact. -/
private theorem submodule_quotient_shortExact {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    (submodule_quotient_shortComplex (R := R) N).ShortExact := by
  -- The quotient row is exact by the standard kernel/range computation.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa [submodule_quotient_shortComplex] using LinearMap.exact_subtype_mkQ N
  · exact (ModuleCat.mono_iff_injective _).2 N.subtype_injective
  · exact (ModuleCat.epi_iff_surjective _).2 N.mkQ_surjective

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the canonical row
`0 → ker(f) → M → range(f) → 0` is short exact. -/
private theorem shortExact_ker_to_range {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (LinearMap.shortComplexKer f.rangeRestrict).ShortExact := by
  -- Replacing the codomain by the actual image makes the right map surjective.
  exact LinearMap.shortExact_shortComplexKer f.surjective_rangeRestrict

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the differential
`M_{j + 1} → M_j` codomain-restricted to the concrete kernel `K_j = ker(d_j)`. -/
private abbrev tail_to_kernel (C : ChainComplex (ModuleCat.{u} R) ℕ) (j : ℕ) :
    C.X (j + 1) →ₗ[R] LinearMap.ker (C.d j (j - 1)).hom :=
  LinearMap.codRestrict (LinearMap.ker (C.d j (j - 1)).hom) (C.d (j + 1) j).hom
    (fun x ↦ by
      -- Consecutive differentials compose to zero, so the image lands in the next kernel.
      change ((C.d j (j - 1)).hom) (((C.d (j + 1) j).hom) x) = 0
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (C.d_comp_d (j + 1) j (j - 1))) x)

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): exactness at degree `j` makes the concrete map
`M_{j + 1} → K_j` surjective. -/
private lemma tail_to_kernel_surjective_of_exactAt
    (C : ChainComplex (ModuleCat.{u} R) ℕ) {j : ℕ} (hj : 0 < j) (hexact : C.ExactAt j) :
    Function.Surjective (tail_to_kernel (R := R) C j) := by
  have hExact :
      Function.Exact (C.d (j + 1) j).hom (C.d j (j - 1)).hom :=
    (exactAt_iff_function_exact (R := R) C (j := j) (show 1 ≤ j by omega)).mp hexact
  intro y
  -- Exactness identifies each cycle in degree `j` with a boundary from degree `j + 1`.
  rcases (hExact y.1).mp y.2 with ⟨x, hx⟩
  refine ⟨x, Subtype.ext ?_⟩
  simpa [tail_to_kernel] using hx

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the source row
`0 → K_{j + 1} → M_{j + 1} → K_j → 0` obtained from exactness at degree `j`
is short exact in the owner form used by Lemma `10.72.6`. -/
private lemma tail_kernel_row_shortExact
    (C : ChainComplex (ModuleCat.{u} R) ℕ) {j : ℕ} (hj : 0 < j) (hexact : C.ExactAt j) :
    (LinearMap.shortComplexKer (tail_to_kernel (R := R) C j)).ShortExact := by
  -- The cod-restricted differential is surjective by exactness at `j`.
  exact LinearMap.shortExact_shortComplexKer
    (tail_to_kernel_surjective_of_exactAt (R := R) C hj hexact)

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the abstract cycles object has the same depth as
its concrete kernel model. -/
private theorem moduleDepth_cycles_eq_kernel
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (j : ℕ) [Module.Finite R (C.X j)] :
    letI : Module.Finite R (C.cycles j) :=
      Module.Finite.of_injective (C.iCycles j).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
    letI : Module.Finite R (LinearMap.ker (C.d j (j - 1)).hom) :=
      Module.Finite.of_injective (LinearMap.ker (C.d j (j - 1)).hom).subtype
        (LinearMap.ker (C.d j (j - 1)).hom).injective_subtype
    moduleDepth R (C.cycles j) = moduleDepth R (LinearMap.ker (C.d j (j - 1)).hom) := by
  have hnext : (ComplexShape.down ℕ).next j = j - 1 := chainComplex_next_eq_pred j
  letI : Module.Finite R (C.cycles j) :=
    Module.Finite.of_injective (C.iCycles j).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  letI : Module.Finite R ((C.sc j).moduleCatLeftHomologyData.K) := by
    change Module.Finite R (LinearMap.ker (C.d j ((ComplexShape.down ℕ).next j)).hom)
    exact
      Module.Finite.of_injective (LinearMap.ker (C.d j ((ComplexShape.down ℕ).next j)).hom).subtype
        (LinearMap.ker (C.d j ((ComplexShape.down ℕ).next j)).hom).injective_subtype
  -- Transport depth across the canonical identification of cycles with the concrete kernel.
  calc
    moduleDepth R (C.cycles j)
        = moduleDepth R ((C.sc j).moduleCatLeftHomologyData.K) := by
            simpa using
              moduleDepth_eq_of_linearEquiv (R := R)
                (((C.cyclesIsoSc' _ j _ rfl rfl) ≪≫ (C.sc j).moduleCatCyclesIso).toLinearEquiv)
    _ = moduleDepth R (LinearMap.ker (C.d j ((ComplexShape.down ℕ).next j)).hom) := by
          rfl
    _ = moduleDepth R (LinearMap.ker (C.d j (j - 1)).hom) := by
          rw [hnext]

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the abstract homology object has the same depth
as the concrete quotient of cycles by boundaries. -/
private theorem moduleDepth_homology_eq_concrete
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (j : ℕ) [Module.Finite R (C.X j)] [Module.Finite R (C.X (j + 1))]
    [Module.Finite R (C.homology j)] [Module.Finite R ((C.sc j).moduleCatLeftHomologyData.K)]
    [Module.Finite R ((C.sc j).moduleCatLeftHomologyData.H)] :
    moduleDepth R (C.homology j) = moduleDepth R ((C.sc j).moduleCatLeftHomologyData.H) := by
  -- Transport depth across the canonical identification of homology with the concrete quotient.
  simpa using
    moduleDepth_eq_of_linearEquiv (R := R)
      (((C.homologyIsoSc' _ j _ rfl rfl) ≪≫ (C.sc j).moduleCatHomologyIso).toLinearEquiv)

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the degree-`j` homology has the same depth as
the explicit quotient `ker(d_j) / range(M_{j + 1} → ker(d_j))`. -/
private theorem moduleDepth_homology_eq_kernel_quotient
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (j : ℕ) [Module.Finite R (C.X j)]
    [Module.Finite R (C.X (j + 1))] [Module.Finite R (C.homology j)] :
    let δ := tail_to_kernel (R := R) C j
    letI : Module.Finite R (LinearMap.ker (C.d j (j - 1)).hom) :=
      Module.Finite.of_injective (LinearMap.ker (C.d j (j - 1)).hom).subtype
        (LinearMap.ker (C.d j (j - 1)).hom).injective_subtype
    letI : Module.Finite R (LinearMap.ker (C.d j (j - 1)).hom ⧸ LinearMap.range δ) :=
      Module.Finite.of_surjective (LinearMap.range δ).mkQ (Submodule.mkQ_surjective _)
    moduleDepth R (C.homology j) =
      moduleDepth R (LinearMap.ker (C.d j (j - 1)).hom ⧸ LinearMap.range δ) := by
  dsimp
  -- Reuse the concrete kernel finiteness as the owner-form cycles object finiteness.
  letI : Module.Finite R ((C.sc j).moduleCatLeftHomologyData.K) := by
    change Module.Finite R (LinearMap.ker (C.d j ((ComplexShape.down ℕ).next j)).hom)
    rw [chainComplex_next_eq_pred]
    infer_instance
  -- The owner-form homology object is a quotient of the already-finite owner-form cycles object.
  letI : Module.Finite R ((C.sc j).moduleCatLeftHomologyData.H) := by
    exact Module.Finite.of_surjective ((C.sc j).moduleCatLeftHomologyData.π).hom
      (Submodule.mkQ_surjective _)
  -- First identify homology with the owner-form quotient attached to `C.sc j`.
  have hconcrete := moduleDepth_homology_eq_concrete (R := R) C j
  -- Then transport that quotient depth to the concrete `ker / range(tail_to_kernel)` model.
  have hquot :
      moduleDepth R ((C.sc j).moduleCatLeftHomologyData.H) =
        moduleDepth R
          (LinearMap.ker (C.d j (j - 1)).hom ⧸
            LinearMap.range (tail_to_kernel (R := R) C j)) := by
    change moduleDepth R
        (LinearMap.ker (C.d j ((ComplexShape.down ℕ).next j)).hom ⧸
          (LinearMap.range <|
            LinearMap.codRestrict (LinearMap.ker (C.d j ((ComplexShape.down ℕ).next j)).hom)
              (C.d ((ComplexShape.down ℕ).prev j) j).hom
              (fun x ↦ by
                change ((C.d j ((ComplexShape.down ℕ).next j)).hom)
                    (((C.d ((ComplexShape.down ℕ).prev j) j).hom) x) = 0
                exact LinearMap.congr_fun
                  (congrArg ModuleCat.Hom.hom
                    (C.d_comp_d ((ComplexShape.down ℕ).prev j) j
                      ((ComplexShape.down ℕ).next j))) x)))
      =
        moduleDepth R
          (LinearMap.ker (C.d j (j - 1)).hom ⧸
            LinearMap.range (tail_to_kernel (R := R) C j))
    rw [ChainComplex.prev, chainComplex_next_eq_pred]
  exact hconcrete.trans hquot

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): when the incoming differential is zero, the top
kernel has infinite depth because it is the zero module. -/
private lemma moduleDepth_top_kernel_eq_top
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {e : ℕ} [∀ j, Module.Finite R (C.X j)]
    (he : 0 < e) (hzero : C.d (e + 1) e = 0) (hexact_e : C.ExactAt e) :
    letI : Module.Finite R (LinearMap.ker (C.d e (e - 1)).hom) :=
      Module.Finite.of_injective (LinearMap.ker (C.d e (e - 1)).hom).subtype
        (LinearMap.ker (C.d e (e - 1)).hom).injective_subtype
    moduleDepth R (LinearMap.ker (C.d e (e - 1)).hom) = ⊤ := by
  have hExact :
      Function.Exact (C.d (e + 1) e).hom (C.d e (e - 1)).hom :=
    (exactAt_iff_function_exact (R := R) C (j := e) (show 1 ≤ e by omega)).mp hexact_e
  -- Exactness turns every cycle in degree `e` into the image of the zero incoming map.
  letI : Subsingleton (LinearMap.ker (C.d e (e - 1)).hom) := by
    refine ⟨fun x y ↦ ?_⟩
    have hx : x = 0 := by
      rcases (hExact x.1).mp x.2 with ⟨z, hz⟩
      apply Subtype.ext
      simpa [hzero] using hz.symm
    have hy : y = 0 := by
      rcases (hExact y.1).mp y.2 with ⟨z, hz⟩
      apply Subtype.ext
      simpa [hzero] using hz.symm
    simpa [hx, hy]
  -- A finite zero module has depth `⊤`.
  simpa using
    moduleDepth_eq_top_of_subsingleton (R := R) (LinearMap.ker (C.d e (e - 1)).hom)

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): replacing `d_{j + 1}` by its cod-restriction to
`K_j = ker(d_j)` does not change the source kernel, hence does not change its depth. -/
private theorem moduleDepth_eq_of_ker_tail_to_kernel
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (j : ℕ)
    [Module.Finite R (LinearMap.ker (tail_to_kernel (R := R) C j))]
    [Module.Finite R (LinearMap.ker (C.d (j + 1) j).hom)] :
    moduleDepth R (LinearMap.ker (tail_to_kernel (R := R) C j)) =
      moduleDepth R (LinearMap.ker (C.d (j + 1) j).hom) := by
  have hker :
      LinearMap.ker (tail_to_kernel (R := R) C j) =
        LinearMap.ker (C.d (j + 1) j).hom := by
    -- Cod-restricting `d_{j + 1}` into `K_j` leaves its kernel unchanged.
    simpa [tail_to_kernel] using
      LinearMap.ker_codRestrict (LinearMap.ker (C.d j (j - 1)).hom) (C.d (j + 1) j).hom
        (fun x ↦ by
          change ((C.d j (j - 1)).hom) (((C.d (j + 1) j).hom) x) = 0
          exact
            LinearMap.congr_fun
              (congrArg ModuleCat.Hom.hom (C.d_comp_d (j + 1) j (j - 1))) x)
  -- Transport depth across the resulting equality of kernel submodules.
  simpa using
    moduleDepth_eq_of_linearEquiv (R := R)
      (LinearEquiv.ofEq _ _ hker)

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): replacing a linear map by its range restriction
does not change the source kernel, hence does not change its depth. -/
private theorem moduleDepth_eq_of_ker_rangeRestrict
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    [Module.Finite R (LinearMap.ker f.rangeRestrict)]
    [Module.Finite R (LinearMap.ker f)] :
    moduleDepth R (LinearMap.ker f.rangeRestrict) =
      moduleDepth R (LinearMap.ker f) := by
  -- The range restriction has exactly the same source kernel as the original map.
  simpa using
    moduleDepth_eq_of_linearEquiv (R := R)
      (LinearEquiv.ofEq _ _ (LinearMap.ker_rangeRestrict f))

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): if a linear map is surjective, then the depth of
its range agrees with the depth of its codomain. -/
private theorem moduleDepth_eq_of_surjective_range
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    moduleDepth R (LinearMap.range f) = moduleDepth R N := by
  letI : Module.Finite R (⊤ : Submodule R N) :=
    Module.Finite.equiv (Submodule.topEquiv : (⊤ : Submodule R N) ≃ₗ[R] N).symm
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 hf
  -- First identify the range with the top submodule, then collapse `⊤` back to the codomain.
  calc
    moduleDepth R (LinearMap.range f) = moduleDepth R (⊤ : Submodule R N) := by
      simpa using
        moduleDepth_eq_of_linearEquiv (R := R) (LinearEquiv.ofEq _ _ hrange)
    _ = moduleDepth R N := by
      simpa using
        moduleDepth_eq_of_linearEquiv (R := R)
          (Submodule.topEquiv : (⊤ : Submodule R N) ≃ₗ[R] N)

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the right-hand depth estimate from
Lemma `10.72.6` specialized to the concrete row `0 → ker(f) → M → range(f) → 0`. -/
private theorem LinearMap.moduleDepth_range_ge_min_of_rangeRestrict_shortExact
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] (f : M →ₗ[R] N) :
    moduleDepth R (LinearMap.range f) ≥
      min (moduleDepth R M) (moduleDepth R (LinearMap.ker f) - 1) := by
  letI : Module.Finite R (LinearMap.ker f.rangeRestrict) :=
    Module.Finite.of_injective (LinearMap.ker f.rangeRestrict).subtype
      (LinearMap.ker f.rangeRestrict).injective_subtype
  -- Package `f` as the canonical short exact row `0 → ker(f) → M → range(f) → 0`.
  have hdepth :=
    CategoryTheory.ShortComplex.ShortExact.moduleDepth_right_ge_min
      (R := R) (S := LinearMap.shortComplexKer f.rangeRestrict)
      (shortExact_ker_to_range (R := R) f)
  -- The kernel does not change after passing to the range restriction.
  rw [moduleDepth_eq_of_ker_rangeRestrict (R := R) f] at hdepth
  simpa using hdepth

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the left-hand depth estimate from
Lemma `10.72.6` specialized to the concrete row `0 → ker(f) → M → range(f) → 0`. -/
private theorem LinearMap.moduleDepth_ker_ge_min_of_rangeRestrict_shortExact
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] (f : M →ₗ[R] N) :
    moduleDepth R (LinearMap.ker f) ≥
      min (moduleDepth R M) (moduleDepth R (LinearMap.range f) + 1) := by
  letI : Module.Finite R (LinearMap.ker f.rangeRestrict) :=
    Module.Finite.of_injective (LinearMap.ker f.rangeRestrict).subtype
      (LinearMap.ker f.rangeRestrict).injective_subtype
  -- Package `f` as the canonical short exact row `0 → ker(f) → M → range(f) → 0`.
  have hdepth :=
    CategoryTheory.ShortComplex.ShortExact.moduleDepth_left_ge_min
      (R := R) (S := LinearMap.shortComplexKer f.rangeRestrict)
      (shortExact_ker_to_range (R := R) f)
  -- The kernel term is unchanged by the range restriction.
  rw [moduleDepth_eq_of_ker_rangeRestrict (R := R) f] at hdepth
  simpa using hdepth

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the right-hand depth estimate from
Lemma `10.72.6` specialized to the quotient row `0 → N → M → M / N → 0`. -/
private theorem Submodule.moduleDepth_quotient_ge_min_of_submodule_row
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M) :
    moduleDepth R (M ⧸ N) ≥ min (moduleDepth R M) (moduleDepth R N - 1) := by
  letI : Module.Finite R N :=
    Module.Finite.of_injective N.subtype N.injective_subtype
  letI : Module.Finite R (M ⧸ N) :=
    Module.Finite.of_surjective N.mkQ (Submodule.mkQ_surjective _)
  letI : Module.Finite R ((submodule_quotient_shortComplex (R := R) N).X₁) := by
    simpa [submodule_quotient_shortComplex] using (inferInstance : Module.Finite R N)
  letI : Module.Finite R ((submodule_quotient_shortComplex (R := R) N).X₃) := by
    change Module.Finite R (M ⧸ N)
    exact Module.Finite.of_surjective N.mkQ (Submodule.mkQ_surjective _)
  -- Apply the owner theorem directly to the standard quotient short exact sequence.
  simpa [submodule_quotient_shortComplex] using
    (CategoryTheory.ShortComplex.ShortExact.moduleDepth_right_ge_min
      (R := R) (S := submodule_quotient_shortComplex (R := R) N)
      (submodule_quotient_shortExact (R := R) N))

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): in `ℕ∞`, a successor lower bound on `b`
implies the corresponding predecessor lower bound on `b - 1`. -/
private lemma enat_le_sub_one_of_succ_le {a : ℕ} {b : ℕ∞}
    (h : (((a + 1 : ℕ) : ℕ∞)) ≤ b) :
    ((a : ℕ) : ℕ∞) ≤ b - (1 : ℕ∞) := by
  by_cases hb : b = ⊤
  · simp [hb]
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hb
    exact ENat.coe_le_coe.mpr (by
      have hnat : a + 1 ≤ n := ENat.coe_le_coe.mp h
      omega)

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): in `ℕ∞`, adding `1` always raises the lower
bound from `0` to `1`. -/
private lemma enat_one_le_add_one (a : ℕ∞) : (1 : ℕ∞) ≤ a + (1 : ℕ∞) := by
  by_cases ha : a = ⊤
  · simp [ha]
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp ha
    norm_num

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the concrete exact row
`0 → K_{j + 1} → M_{j + 1} → K_j → 0` upgrades the depth bound on `K_{j + 1}` to one on
`K_j`. -/
private lemma moduleDepth_kernel_target_ge_of_tail_row
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {j : ℕ}
    [Module.Finite R (C.X j)] [Module.Finite R (C.X (j + 1))]
    [Module.Finite R (LinearMap.ker (C.d (j + 1) j).hom)]
    [Module.Finite R (LinearMap.ker (C.d j (j - 1)).hom)]
    (hj : 0 < j) (hexact : C.ExactAt j)
    (hsource : moduleDepth R (LinearMap.ker (C.d (j + 1) j).hom) ≥
      ((j + 2 : ℕ) : WithTop ℕ))
    (hmiddle : moduleDepth R (C.X (j + 1)) ≥ ((j + 1 : ℕ) : WithTop ℕ)) :
    moduleDepth R (LinearMap.ker (C.d j (j - 1)).hom) ≥ ((j + 1 : ℕ) : WithTop ℕ) := by
  let δ := tail_to_kernel (R := R) C j
  letI : Module.Finite R (LinearMap.ker δ) :=
    Module.Finite.of_injective (LinearMap.ker δ).subtype (LinearMap.ker δ).injective_subtype
  -- Apply the concrete range-depth adapter to the exact row
  -- `0 → ker(δ) → M_{j+1} → range(δ) → 0`.
  have hrow :
      moduleDepth R (LinearMap.range δ) ≥
        min (moduleDepth R (C.X (j + 1))) (moduleDepth R (LinearMap.ker δ) - 1) :=
    LinearMap.moduleDepth_range_ge_min_of_rangeRestrict_shortExact (R := R) δ
  -- Exactness at `j` identifies `range(δ)` with the target kernel `K_j`.
  rw [moduleDepth_eq_of_surjective_range (R := R) δ
    (tail_to_kernel_surjective_of_exactAt (R := R) C hj hexact)] at hrow
  -- Cod-restricting the differential does not change its source kernel.
  rw [moduleDepth_eq_of_ker_tail_to_kernel (R := R) C j] at hrow
  have hsource' :
      ((j + 1 : ℕ) : ℕ∞) ≤
        moduleDepth R (LinearMap.ker (C.d (j + 1) j).hom) - (1 : ℕ∞) := by
    -- Shift the source bound down by one.
    simpa [Nat.cast_add, add_assoc] using
      enat_le_sub_one_of_succ_le (a := j + 1) hsource
  have hmin :
      ((j + 1 : ℕ) : ℕ∞) ≤
        min (moduleDepth R (C.X (j + 1)))
          (moduleDepth R (LinearMap.ker (C.d (j + 1) j).hom) - (1 : ℕ∞)) := by
    -- Both terms in the minimum are already at least `j + 1`.
    exact le_min hmiddle hsource'
  exact le_trans hmin hrow

/-- Helper for Lemma 10.102.8 (Acyclicity lemma): the depth of the concrete kernels
`K_j = ker(d_j)` propagates downward through the exact tail. -/
private lemma moduleDepth_kernel_tail_ge
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {e i : ℕ} [∀ j, Module.Finite R (C.X j)]
    (hi : 0 < i) (hie : i < e)
    (hdepth : ∀ ⦃j : ℕ⦄, i ≤ j → j ≤ e → moduleDepth R (C.X j) ≥ (j : WithTop ℕ))
    (hbounded : ∀ j, e < j → Limits.IsZero (C.X j))
    (hexact : ∀ ⦃j : ℕ⦄, i < j → j ≤ e → C.ExactAt j) :
    ∀ {j : ℕ}, i + 1 ≤ j → j ≤ e →
      letI : Module.Finite R (LinearMap.ker (C.d j (j - 1)).hom) :=
        Module.Finite.of_injective (LinearMap.ker (C.d j (j - 1)).hom).subtype
          (LinearMap.ker (C.d j (j - 1)).hom).injective_subtype
      moduleDepth R (LinearMap.ker (C.d j (j - 1)).hom) ≥ ((j + 1 : ℕ) : WithTop ℕ) := by
  intro j hij hje
  let P : ℕ → Prop := fun k ↦
    letI : Module.Finite R (LinearMap.ker (C.d k (k - 1)).hom) :=
      Module.Finite.of_injective (LinearMap.ker (C.d k (k - 1)).hom).subtype
        (LinearMap.ker (C.d k (k - 1)).hom).injective_subtype
    moduleDepth R (LinearMap.ker (C.d k (k - 1)).hom) ≥ ((k + 1 : ℕ) : WithTop ℕ)
  have htop : P e := by
    letI : Module.Finite R (LinearMap.ker (C.d e (e - 1)).hom) :=
      Module.Finite.of_injective (LinearMap.ker (C.d e (e - 1)).hom).subtype
        (LinearMap.ker (C.d e (e - 1)).hom).injective_subtype
    have hzero : C.d (e + 1) e = 0 := by
      exact (hbounded (e + 1) (by omega)).eq_of_src _ _
    have hexact_e : C.ExactAt e := hexact (by omega) le_rfl
    -- The top kernel vanishes because the incoming differential is zero from an is-zero source.
    have htop' :
        moduleDepth R (LinearMap.ker (C.d e (e - 1)).hom) = ⊤ :=
      moduleDepth_top_kernel_eq_top (R := R) (C := C) (e := e) (by omega) hzero hexact_e
    change moduleDepth R (LinearMap.ker (C.d e (e - 1)).hom) ≥ ((e + 1 : ℕ) : WithTop ℕ)
    rw [htop']
    simp
  have hdesc : ∀ n {k : ℕ}, k ≤ e → e - k = n → i + 1 ≤ k → P k := by
    intro n
    induction n with
    | zero =>
        intro k hke hkdiff hik
        have hk : k = e := by omega
        subst hk
        simpa using htop
    | succ n ih =>
        intro k hke hkdiff hik
        have hklt : k < e := by omega
        have hk1le : k + 1 ≤ e := by omega
        have hik1 : i + 1 ≤ k + 1 := by omega
        have hk1diff : e - (k + 1) = n := by omega
        have hk1 : P (k + 1) := ih hk1le hk1diff hik1
        letI : Module.Finite R (LinearMap.ker (C.d (k + 1) k).hom) :=
          Module.Finite.of_injective (LinearMap.ker (C.d (k + 1) k).hom).subtype
            (LinearMap.ker (C.d (k + 1) k).hom).injective_subtype
        letI : Module.Finite R (LinearMap.ker (C.d k (k - 1)).hom) :=
          Module.Finite.of_injective (LinearMap.ker (C.d k (k - 1)).hom).subtype
            (LinearMap.ker (C.d k (k - 1)).hom).injective_subtype
        have hsource :
            moduleDepth R (LinearMap.ker (C.d (k + 1) k).hom) ≥
              ((k + 2 : ℕ) : WithTop ℕ) := by
          simpa using hk1
        have hmiddle : moduleDepth R (C.X (k + 1)) ≥ ((k + 1 : ℕ) : WithTop ℕ) :=
          hdepth (by omega) (by omega)
        -- One exact tail step propagates the kernel-depth bound from `K_{k+1}` to `K_k`.
        exact moduleDepth_kernel_target_ge_of_tail_row
          (R := R) (C := C) (j := k) (by omega) (hexact (by omega) (by omega))
          hsource hmiddle
  exact hdesc (e - j) hje rfl hij

-- Proof sketch: truncate the complex to the tail starting in degree `i`, use exactness in degrees
-- `> i` and the vanishing of the terms above `e` to build the successive short exact sequences of
-- kernels and images occurring in the standard proof, apply Lemma `10.72.6` repeatedly to
-- propagate the tail depth bounds downward, and finally deduce that the degree-`i` homology has
-- depth at least `1`.
/-- Lemma 10.102.8 (Acyclicity lemma): if a bounded-above chain complex of finite modules over a
Noetherian local ring has depth at least `j` in each degree `j` from `i` through `e`, and `i > 0`
is the largest degree at which the complex is not exact, then the degree-`i` homology module has
depth at least `1`. -/
theorem depth_homology_ge_one_of_largest_nonexact_index
    {C : ChainComplex (ModuleCat.{u} R) ℕ} {e i : ℕ} [∀ j, Module.Finite R (C.X j)]
    (hi : 0 < i) (hie : i ≤ e)
    (hdepth : ∀ ⦃j : ℕ⦄, i ≤ j → j ≤ e → moduleDepth R (C.X j) ≥ (j : WithTop ℕ))
    (hbounded : ∀ j, e < j → Limits.IsZero (C.X j))
    (hnotExact : ¬ C.ExactAt i)
    (hexact : ∀ ⦃j : ℕ⦄, i < j → j ≤ e → C.ExactAt j) :
    moduleDepth R (C.homology i) ≥ (1 : WithTop ℕ) := by
  -- Route correction: keep the textbook kernel/image argument on the concrete kernels
  -- `K_j = ker(d_j)` and boundaries `B_i = range(d_{i+1})`, then transport the final quotient
  -- back to the abstract homology object.
  rcases Nat.eq_or_lt_of_le hie with hEq | hie'
  · subst e
    let Ki := LinearMap.ker (C.d i (i - 1)).hom
    let δ := tail_to_kernel (R := R) C i
    letI : Module.Finite R Ki :=
      Module.Finite.of_injective Ki.subtype Ki.injective_subtype
    letI : Module.Finite R (Ki ⧸ LinearMap.range δ) :=
      Module.Finite.of_surjective (LinearMap.range δ).mkQ (Submodule.mkQ_surjective _)
    -- The source term in degree `i + 1` is zero by boundedness, so the boundary submodule is
    -- trivial and the concrete homology quotient is just the kernel `K_i`.
    haveI : Subsingleton (C.X (i + 1)) :=
      ModuleCat.subsingleton_of_isZero (hbounded (i + 1) (by omega))
    have hδzero : δ = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim x 0
      simpa [δ, hx]
    have hrange_bot : LinearMap.range δ = ⊥ := by
      rw [hδzero, LinearMap.range_zero]
    have hKi_row :
        moduleDepth R Ki ≥
          min (moduleDepth R (C.X i))
            (moduleDepth R (LinearMap.range (C.d i (i - 1)).hom) + 1) := by
      -- The concrete kernel row is `0 → K_i → M_i → range(d_i) → 0`.
      simpa [Ki] using
        LinearMap.moduleDepth_ker_ge_min_of_rangeRestrict_shortExact
          (R := R) ((C.d i (i - 1)).hom)
    have hXi_ge_one : (1 : WithTop ℕ) ≤ moduleDepth R (C.X i) := by
      exact le_trans (by exact_mod_cast hi) (hdepth le_rfl le_rfl)
    have hrange_succ_ge_one :
        (1 : ℕ∞) ≤ moduleDepth R (LinearMap.range (C.d i (i - 1)).hom) + (1 : ℕ∞) := by
      exact enat_one_le_add_one _
    have hKi_ge_one : moduleDepth R Ki ≥ (1 : WithTop ℕ) := by
      have hmin :
          (1 : ℕ∞) ≤
            min (moduleDepth R (C.X i))
              (moduleDepth R (LinearMap.range (C.d i (i - 1)).hom) + (1 : ℕ∞)) :=
        le_min hXi_ge_one hrange_succ_ge_one
      exact le_trans hmin hKi_row
    have hquot_eq :
        moduleDepth R (Ki ⧸ LinearMap.range δ) = moduleDepth R Ki := by
      letI : Module.Finite R (Ki ⧸ (⊥ : Submodule R Ki)) :=
        Module.Finite.of_surjective (Submodule.mkQ (⊥ : Submodule R Ki)) (Submodule.mkQ_surjective _)
      have hquot_bot :
          moduleDepth R (Ki ⧸ (⊥ : Submodule R Ki)) = moduleDepth R Ki := by
        simpa [Ki] using
          moduleDepth_eq_of_linearEquiv (R := R)
            ((⊥ : Submodule R Ki).quotEquivOfEqBot rfl)
      have hquot_transport :
          moduleDepth R (Ki ⧸ LinearMap.range δ) =
            moduleDepth R (Ki ⧸ (⊥ : Submodule R Ki)) := by
        simpa using
          moduleDepth_eq_of_linearEquiv (R := R)
            (Submodule.quotEquivOfEq (LinearMap.range δ) (⊥ : Submodule R Ki) hrange_bot)
      exact hquot_transport.trans hquot_bot
    -- Transport the concrete quotient computation back to the abstract homology object.
    calc
      moduleDepth R (C.homology i) = moduleDepth R (Ki ⧸ LinearMap.range δ) := by
        simpa [Ki, δ] using moduleDepth_homology_eq_kernel_quotient (R := R) C i
      _ = moduleDepth R Ki := hquot_eq
      _ ≥ (1 : WithTop ℕ) := hKi_ge_one
  · let Ki := LinearMap.ker (C.d i (i - 1)).hom
    let δ := tail_to_kernel (R := R) C i
    letI : Module.Finite R Ki :=
      Module.Finite.of_injective Ki.subtype Ki.injective_subtype
    letI : Module.Finite R (Ki ⧸ LinearMap.range δ) :=
      Module.Finite.of_surjective (LinearMap.range δ).mkQ (Submodule.mkQ_surjective _)
    have hKi1 :
        moduleDepth R (LinearMap.ker (C.d (i + 1) i).hom) ≥
          ((i + 2 : ℕ) : WithTop ℕ) :=
      moduleDepth_kernel_tail_ge (R := R) (C := C) hi hie' hdepth hbounded hexact
        (show i + 1 ≤ i + 1 by simp) (show i + 1 ≤ e by omega)
    have hBi_row :
        moduleDepth R (LinearMap.range δ) ≥
          min (moduleDepth R (C.X (i + 1)))
            (moduleDepth R (LinearMap.ker (C.d (i + 1) i).hom) - (1 : ℕ∞)) := by
      -- This is the concrete row `0 → K_{i+1} → M_{i+1} → B_i → 0`.
      have hBi_row' :
          moduleDepth R (LinearMap.range δ) ≥
            min (moduleDepth R (C.X (i + 1))) (moduleDepth R (LinearMap.ker δ) - (1 : ℕ∞)) := by
        simpa [δ] using
          LinearMap.moduleDepth_range_ge_min_of_rangeRestrict_shortExact
            (R := R) (tail_to_kernel (R := R) C i)
      rw [moduleDepth_eq_of_ker_tail_to_kernel (R := R) C i] at hBi_row'
      exact hBi_row'
    have hXi1 :
        moduleDepth R (C.X (i + 1)) ≥ ((i + 1 : ℕ) : WithTop ℕ) :=
      hdepth (by omega) (by omega)
    have hKi1_sub :
        ((i + 1 : ℕ) : ℕ∞) ≤
          moduleDepth R (LinearMap.ker (C.d (i + 1) i).hom) - (1 : ℕ∞) := by
      simpa [Nat.cast_add, add_assoc] using
        enat_le_sub_one_of_succ_le (a := i + 1) hKi1
    have hBi_ge :
        moduleDepth R (LinearMap.range δ) ≥ ((i + 1 : ℕ) : WithTop ℕ) := by
      have hmin :
          ((i + 1 : ℕ) : WithTop ℕ) ≤
            min (moduleDepth R (C.X (i + 1)))
              (moduleDepth R (LinearMap.ker (C.d (i + 1) i).hom) - 1) :=
        le_min hXi1 hKi1_sub
      exact le_trans hmin hBi_row
    have hKi_row :
        moduleDepth R Ki ≥
          min (moduleDepth R (C.X i))
            (moduleDepth R (LinearMap.range (C.d i (i - 1)).hom) + 1) := by
      -- This is the concrete row `0 → K_i → M_i → range(d_i) → 0`.
      simpa [Ki] using
        LinearMap.moduleDepth_ker_ge_min_of_rangeRestrict_shortExact
          (R := R) ((C.d i (i - 1)).hom)
    have hXi_ge_one : (1 : WithTop ℕ) ≤ moduleDepth R (C.X i) := by
      exact le_trans (by exact_mod_cast hi) (hdepth le_rfl (by omega))
    have hrange_succ_ge_one :
        (1 : ℕ∞) ≤ moduleDepth R (LinearMap.range (C.d i (i - 1)).hom) + (1 : ℕ∞) := by
      exact enat_one_le_add_one _
    have hKi_ge_one : moduleDepth R Ki ≥ (1 : WithTop ℕ) := by
      have hmin :
          (1 : ℕ∞) ≤
            min (moduleDepth R (C.X i))
              (moduleDepth R (LinearMap.range (C.d i (i - 1)).hom) + (1 : ℕ∞)) :=
        le_min hXi_ge_one hrange_succ_ge_one
      exact le_trans hmin hKi_row
    have hBi_sub_ge_one :
        (1 : ℕ∞) ≤ moduleDepth R (LinearMap.range δ) - (1 : ℕ∞) := by
      have htwo_le : (2 : ℕ) ≤ i + 1 := by omega
      have htwo :
          (2 : ℕ∞) ≤ moduleDepth R (LinearMap.range δ) := by
        exact le_trans (ENat.coe_le_coe.mpr htwo_le) hBi_ge
      simpa [Nat.cast_add, add_assoc] using
        enat_le_sub_one_of_succ_le (a := 1) htwo
    have hquot_row :
        moduleDepth R (Ki ⧸ LinearMap.range δ) ≥
          min (moduleDepth R Ki) (moduleDepth R (LinearMap.range δ) - (1 : ℕ∞)) := by
      -- This is the final concrete row `0 → B_i → K_i → H_i → 0`.
      simpa [Ki, δ] using
        Submodule.moduleDepth_quotient_ge_min_of_submodule_row
          (R := R) (M := Ki) (LinearMap.range δ)
    have hquot_ge_one : moduleDepth R (Ki ⧸ LinearMap.range δ) ≥ (1 : WithTop ℕ) := by
      have hmin :
          (1 : WithTop ℕ) ≤
            min (moduleDepth R Ki) (moduleDepth R (LinearMap.range δ) - 1) :=
        le_min hKi_ge_one hBi_sub_ge_one
      exact le_trans hmin hquot_row
    -- Transport the concrete quotient depth back to the owner homology object.
    calc
      moduleDepth R (C.homology i) = moduleDepth R (Ki ⧸ LinearMap.range δ) := by
        simpa [Ki, δ] using moduleDepth_homology_eq_kernel_quotient (R := R) C i
      _ ≥ (1 : WithTop ℕ) := hquot_ge_one

end
