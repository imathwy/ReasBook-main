import Mathlib
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Functor.OfSequence
import StacksProject_2024.stacks_project.Chap10.Definition_10_5_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_3_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_101_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w x y

/- Domain-style sampling for Lemma 15.101.4:
- primary domain: `I`-power quotient towers, adic completion, and Mittag-Leffler inverse systems
  attached to `Hom_A(M, N / I^(n + 1) N)` and quotient-level isomorphisms;
- sampled owner declarations:
  `idealPowerModuleQuotient` from `Lemma_15_101_1`,
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.Functor.IsMittagLeffler`,
  `AdicCompletion.transitionMap`;
- best owner abstraction: the quotient data live in sequential inverse systems, while the
  `Type`-valued Mittag-Leffler condition is already owned canonically by
  `CategoryTheory.Functor.IsMittagLeffler`, so a local `Type`-specific redefinition would be a
  duplicate wheel;
- primitive data: the modules `M`, `N`, the ideal `I`, and the canonical reduction/transition maps
  induced by `AdicCompletion.transitionMap`;
- derived API: the Hom tower, the quotient-isomorphism tower, the comparison maps on quotients, and
  the resulting Mittag-Leffler / inverse-limit statements.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma statements about the Hom tower, the isomorphism tower, and the
  completion comparisons;
- `core/canonical`: `idealPowerModuleQuotient`, `SequentialInverseSystem`, and
  `Functor.IsMittagLeffler`;
- `bridge/view`: the explicit quotient comparison maps and the stagewise reduction maps on
  isomorphisms. -/

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)

/-- The kernel of the transition `X / I^(n + 2) X → X / I^(n + 1) X`. -/
abbrev idealPowerModuleTransitionKer (X : Type x) [AddCommGroup X] [Module A X] (n : ℕ) :
    Submodule A (idealPowerModuleQuotient I X (n + 1)) :=
  LinearMap.ker (AdicCompletion.transitionMap I X (Nat.le_succ (n + 1)))

/-- The stage `Hom_A(M, N / I^(n + 1) N)`, which canonically models `Hom_A(M_n, N_n)`. -/
abbrev homIdealPowerStage
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) : Type (max v w) :=
  M →ₗ[A] idealPowerModuleQuotient I N n

/-- The transition map on the Hom tower induced by reduction modulo one lower power of `I`. -/
abbrev homIdealPowerStep
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    homIdealPowerStage I M N (n + 1) →ₗ[A] homIdealPowerStage I M N n :=
  LinearMap.compRight A (AdicCompletion.transitionMap I N (Nat.le_succ (n + 1)))

/-- The inverse system `(Hom_A(M_n, N_n))_n`, modeled as `(Hom_A(M, N / I^(n + 1) N))_n`. -/
abbrev homIdealPowerTower
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] :
    SequentialInverseSystem (ModuleCat A) :=
  @Functor.ofOpSequence (ModuleCat A) _
    (fun n ↦ ModuleCat.of A (homIdealPowerStage I M N n))
    (fun n ↦ ModuleCat.ofHom (homIdealPowerStep I M N n))

/-- The canonical map `Hom_A(M, N) → Hom_A(M, N / I^(n + 1) N)`. -/
abbrev homReductionLinearMap
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    (M →ₗ[A] N) →ₗ[A] homIdealPowerStage I M N n :=
  LinearMap.compRight A (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A N)))

-- Proof sketch: if `f` lies in `I^(n + 1) Hom_A(M, N)`, then every value of `f` lands in
-- `I^(n + 1) N`, so the composite `M → N → N / I^(n + 1) N` is zero.
/-- The canonical reduction `Hom_A(M, N) → Hom_A(M, N / I^(n + 1) N)` kills `I^(n + 1)`. -/
theorem idealPowerHomComparison_condition
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N)) ≤
      LinearMap.ker (homReductionLinearMap I M N n) := by
  -- The quotient-stage target is annihilated by `I^(n + 1)`, so the reduction map kills the
  -- corresponding smul submodule of `Hom_A(M, N)`.
  refine Submodule.smul_le.mpr ?_
  intro r hr f _hf
  ext x
  change (Submodule.Quotient.mk (r • f x) : idealPowerModuleQuotient I N n) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hr (by simp)

/-- The canonical comparison
`Hom_A(M, N) / I^(n + 1) Hom_A(M, N) → Hom_A(M, N / I^(n + 1) N)`. -/
abbrev homReductionComparison
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    idealPowerModuleQuotient I (M →ₗ[A] N) n →ₗ[A] homIdealPowerStage I M N n :=
  Submodule.liftQ
    (I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N)))
    (homReductionLinearMap I M N n)
    (idealPowerHomComparison_condition I M N n)

/-- The stage of `A`-linear isomorphisms `M_n ≃ N_n`. -/
abbrev moduleIsomorphismStage
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) : Type (max v w) :=
  idealPowerModuleQuotient I M n ≃ₗ[A] idealPowerModuleQuotient I N n

-- Proof sketch: every quotient map `X / I^(n + 2) X → X / I^(n + 1) X` is induced by the
-- universal quotient map, hence is surjective.
/-- The transition map on ideal-power quotients is surjective. -/
theorem idealPowerModuleTransition_surjective
    (X : Type x) [AddCommGroup X] [Module A X] (n : ℕ) :
    Function.Surjective (AdicCompletion.transitionMap I X (Nat.le_succ (n + 1))) := by
  intro x
  -- The same representative in the higher quotient maps to the prescribed lower-stage class.
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I ^ (n + 1) • (⊤ : Submodule A X)) x
  exact ⟨Submodule.Quotient.mk m, rfl⟩

/-- Helper for Lemma 15.101.4: the kernel of the transition between successive quotient stages is
exactly the `I^(n + 1)`-multiple submodule of the higher quotient stage. -/
private theorem idealPowerModuleTransitionKer_eq_pow_smul_top
    (X : Type x) [AddCommGroup X] [Module A X] (n : ℕ) :
    idealPowerModuleTransitionKer I X n =
      I ^ (n + 1) • (⊤ : Submodule A (idealPowerModuleQuotient I X (n + 1))) := by
  ext x
  constructor
  · intro hx
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I ^ (n + 2) • (⊤ : Submodule A X)) x
    change (Submodule.Quotient.mk m : idealPowerModuleQuotient I X n) = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    have hmem :
        (Submodule.Quotient.mk m : idealPowerModuleQuotient I X (n + 1)) ∈
          Submodule.map
            (Submodule.mkQ (I ^ (n + 2) • (⊤ : Submodule A X)))
            (I ^ (n + 1) • (⊤ : Submodule A X)) := by
      exact Submodule.mem_map_of_mem hx
    simpa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] using hmem
  · intro hx
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I ^ (n + 2) • (⊤ : Submodule A X)) x
    rw [show
      I ^ (n + 1) • (⊤ : Submodule A (idealPowerModuleQuotient I X (n + 1))) =
        Submodule.map
          (Submodule.mkQ (I ^ (n + 2) • (⊤ : Submodule A X)))
          (I ^ (n + 1) • (⊤ : Submodule A X)) by
      simp [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]] at hx
    rcases Submodule.mem_map.1 hx with ⟨y, hy, hy_eq⟩
    change (Submodule.Quotient.mk m : idealPowerModuleQuotient I X n) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have hdiff :
        y - m ∈ I ^ (n + 2) • (⊤ : Submodule A X) :=
      (Submodule.Quotient.eq _).1 hy_eq
    have hdiff' :
        y - m ∈ I ^ (n + 1) • (⊤ : Submodule A X) :=
      (Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) le_rfl) hdiff
    have hm : m = y - (y - m) := by
      simp
    rw [hm]
    exact Submodule.sub_mem _ hy hdiff'

-- Proof sketch: an isomorphism `e : M_(n+1) ≃ N_(n+1)` carries the kernel of the reduction map on
-- `M_(n+1)` onto the corresponding kernel on `N_(n+1)` because the reduction maps commute with `e`
-- and `e.symm`.
/-- An isomorphism of the higher quotient stages identifies the kernels of the next transition
maps. -/
theorem idealPowerModuleTransitionKer_map_eq
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N]
    (n : ℕ) (e : moduleIsomorphismStage I M N (n + 1)) :
    (idealPowerModuleTransitionKer I M n).map (e : _ →ₗ[A] _) =
      idealPowerModuleTransitionKer I N n := by
  -- Both kernels are the `I^(n + 1)`-multiple submodules of the higher quotient stages, and a
  -- linear equivalence carries that ideal-power submodule onto the corresponding one.
  calc
    (idealPowerModuleTransitionKer I M n).map (e : _ →ₗ[A] _) =
        Submodule.map (e : _ →ₗ[A] _)
          (I ^ (n + 1) •
            (⊤ : Submodule A (idealPowerModuleQuotient I M (n + 1)))) := by
          rw [idealPowerModuleTransitionKer_eq_pow_smul_top (I := I) (X := M) (n := n)]
    _ = I ^ (n + 1) •
          (⊤ : Submodule A (idealPowerModuleQuotient I N (n + 1))) := by
          rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 e.surjective]
    _ = idealPowerModuleTransitionKer I N n := by
          rw [idealPowerModuleTransitionKer_eq_pow_smul_top (I := I) (X := N) (n := n)]

/-- Reduction modulo one lower power of `I` sends an isomorphism `M_(n+1) ≃ N_(n+1)` to an
isomorphism `M_n ≃ N_n`. -/
abbrev moduleIsomorphismReduction
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    moduleIsomorphismStage I M N (n + 1) → moduleIsomorphismStage I M N n :=
  fun e ↦
    ((AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))).quotKerEquivOfSurjective
        (idealPowerModuleTransition_surjective I M n)).symm.trans
      ((Submodule.Quotient.equiv
          (idealPowerModuleTransitionKer I M n)
          (idealPowerModuleTransitionKer I N n)
          e
          (idealPowerModuleTransitionKer_map_eq I M N n e)).trans
        ((AdicCompletion.transitionMap I N (Nat.le_succ (n + 1))).quotKerEquivOfSurjective
          (idealPowerModuleTransition_surjective I N n)))

/-- The inverse system `(Isom_A(M_n, N_n))_n` of `A`-linear isomorphisms between the quotient
modules. -/
abbrev moduleIsomorphismTower
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] :
    SequentialInverseSystem (Type (max v w)) :=
  @Functor.ofOpSequence (Type (max v w)) _
    (fun n ↦ moduleIsomorphismStage I M N n)
    (fun n ↦ moduleIsomorphismReduction I M N n)

end

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N]

/-- Helper for Lemma 15.101.4: for an exact sequence `U ⟶ V ⟶ W ⟶ 0`, the maps `W →ₗ[A] P`
identify with the kernel of precomposition by `U ⟶ V`. -/
private theorem exists_kernel_precompose_equiv_linearMap_of_exact
    {U : Type*} [AddCommGroup U] [Module A U]
    {V : Type*} [AddCommGroup V] [Module A V]
    {W : Type*} [AddCommGroup W] [Module A W]
    {P : Type*} [AddCommGroup P] [Module A P]
    (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g) :
    Nonempty (LinearMap.ker (LinearMap.lcomp A P f) ≃ₗ[A] (W →ₗ[A] P)) := by
  let precompose : (W →ₗ[A] P) →ₗ[A] (V →ₗ[A] P) := LinearMap.lcomp A P g
  have hprecompose_injective : Function.Injective precompose :=
    LinearMap.lcomp_injective_of_surjective g hsurj
  have hprecompose_exact :
      Function.Exact precompose (LinearMap.lcomp A P f) :=
    LinearMap.exact_lcomp_of_exact_of_surjective P hexact hsurj
  have hker :
      LinearMap.ker (LinearMap.lcomp A P f) = LinearMap.range precompose :=
    hprecompose_exact.linearMap_ker_eq
  -- Route correction: use the exact `Hom_A(-, P)` owner theorem to identify the kernel with the
  -- range of precomposition by `g`, then collapse that range back to `Hom_A(W, P)` by injectivity.
  refine ⟨((LinearEquiv.ofInjective precompose hprecompose_injective).trans
    (LinearEquiv.ofEq _ _ hker.symm)).symm⟩

/-- Helper for Lemma 15.101.4: the exact-sequence kernel equivalence used in the fixed-presentation
bridge. -/
private noncomputable abbrev kernel_precompose_equiv_linearMap_of_exact
    {U : Type*} [AddCommGroup U] [Module A U]
    {V : Type*} [AddCommGroup V] [Module A V]
    {W : Type*} [AddCommGroup W] [Module A W]
    {P : Type*} [AddCommGroup P] [Module A P]
    (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g) :
    LinearMap.ker (LinearMap.lcomp A P f) ≃ₗ[A] (W →ₗ[A] P) :=
  let precompose : (W →ₗ[A] P) →ₗ[A] (V →ₗ[A] P) := LinearMap.lcomp A P g
  let hprecompose_injective : Function.Injective precompose :=
    LinearMap.lcomp_injective_of_surjective g hsurj
  let hprecompose_exact :
      Function.Exact precompose (LinearMap.lcomp A P f) :=
    LinearMap.exact_lcomp_of_exact_of_surjective P hexact hsurj
  let hker :
      LinearMap.ker (LinearMap.lcomp A P f) = LinearMap.range precompose :=
    hprecompose_exact.linearMap_ker_eq
  -- Route correction: keep the kernel/Hom equivalence in explicit range form so later naturality
  -- statements can compute directly on `ψ.comp g`.
  ((LinearEquiv.ofInjective precompose hprecompose_injective).trans
    (LinearEquiv.ofEq _ _ hker.symm)).symm

/-- Helper for Lemma 15.101.4: the inverse presentation-kernel equivalence sends
`ψ : W →ₗ[A] P` to precomposition by the surjection `g`. -/
private theorem kernel_precompose_equiv_linearMap_of_exact_symm_apply
    {U : Type*} [AddCommGroup U] [Module A U]
    {V : Type*} [AddCommGroup V] [Module A V]
    {W : Type*} [AddCommGroup W] [Module A W]
    {P : Type*} [AddCommGroup P] [Module A P]
    (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g)
    (ψ : W →ₗ[A] P) :
    (((kernel_precompose_equiv_linearMap_of_exact
        (A := A) (P := P) f g hexact hsurj).symm ψ :
          LinearMap.ker (LinearMap.lcomp A P f)) : V →ₗ[A] P) =
      LinearMap.lcomp A P g ψ := by
  -- The explicit equivalence was defined by identifying the kernel with the range of
  -- precomposition by `g`.
  rfl

/-- Helper for Lemma 15.101.4: postcomposition with a target map preserves the kernel of
precomposition by `f`. -/
private theorem kernel_precompose_compRight_condition
    {U : Type*} [AddCommGroup U] [Module A U]
    {V : Type*} [AddCommGroup V] [Module A V]
    {P : Type*} [AddCommGroup P] [Module A P]
    {P' : Type*} [AddCommGroup P'] [Module A P']
    (f : U →ₗ[A] V) (σ : P' →ₗ[A] P)
    (φ : LinearMap.ker (LinearMap.lcomp A P' f)) :
    LinearMap.compRight A σ φ.1 ∈ LinearMap.ker (LinearMap.lcomp A P f) := by
  -- Evaluating after `f` still vanishes because `φ` already lies in the kernel.
  ext u
  simp [LinearMap.mem_ker] at φ
  simp [LinearMap.mem_ker, φ]

/-- Helper for Lemma 15.101.4: postcomposition with a target map induces a linear map on the
presentation kernels. -/
private noncomputable abbrev kernel_precompose_compRight
    {U : Type*} [AddCommGroup U] [Module A U]
    {V : Type*} [AddCommGroup V] [Module A V]
    {P : Type*} [AddCommGroup P] [Module A P]
    {P' : Type*} [AddCommGroup P'] [Module A P']
    (f : U →ₗ[A] V) (σ : P' →ₗ[A] P) :
    LinearMap.ker (LinearMap.lcomp A P' f) →ₗ[A]
      LinearMap.ker (LinearMap.lcomp A P f) :=
  (LinearMap.compRight A σ).codRestrict _
    (kernel_precompose_compRight_condition (A := A) f σ)

/-- Helper for Lemma 15.101.4: the inverse presentation-kernel equivalence is natural in the
target module under postcomposition. -/
private theorem kernel_precompose_equiv_linearMap_of_exact_symm_compRight_naturality
    {U : Type*} [AddCommGroup U] [Module A U]
    {V : Type*} [AddCommGroup V] [Module A V]
    {W : Type*} [AddCommGroup W] [Module A W]
    {P : Type*} [AddCommGroup P] [Module A P]
    {P' : Type*} [AddCommGroup P'] [Module A P']
    (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hexact : Function.Exact f g) (hsurj : Function.Surjective g)
    (σ : P' →ₗ[A] P) :
    (kernel_precompose_compRight (A := A) f σ).comp
        ((kernel_precompose_equiv_linearMap_of_exact
          (A := A) (P := P') f g hexact hsurj).symm.toLinearMap) =
      ((kernel_precompose_equiv_linearMap_of_exact
        (A := A) (P := P) f g hexact hsurj).symm.toLinearMap).comp
        (LinearMap.compRight A σ) := by
  -- Both composites send `ψ` to the kernel element represented by `(σ ∘ ψ) ∘ g`.
  apply LinearMap.ext
  intro ψ
  ext v
  simp [kernel_precompose_compRight,
    kernel_precompose_equiv_linearMap_of_exact_symm_apply]

/-- Helper for Lemma 15.101.4: a finite module over a Noetherian ring admits one fixed finite
free presentation `A^m ⟶ A^n ⟶ M ⟶ 0`. -/
private theorem exists_finite_free_presentation_of_finite :
    ∃ n m : ℕ,
      ∃ (f : (Fin m → A) →ₗ[A] (Fin n → A)) (g : (Fin n → A) →ₗ[A] M),
        Function.Exact f g ∧ Function.Surjective g := by
  letI : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  -- Over a Noetherian ring, finite modules are finitely presented, so the canonical owner theorem
  -- already supplies the fixed finite free presentation needed by the source proof.
  rcases (Module.FinitePresentation.iff_exists_exact_free_sequence A M).mp inferInstance with
    ⟨n, m, f, g, hfg, hg⟩
  exact ⟨n, m, f, g, hfg, hg⟩

/-- Helper for Lemma 15.101.4: transporting a concrete left-homology quotient class back through
`leftHomologyIso.inv` recovers the corresponding abstract left-homology class. -/
private theorem moduleCatLeftHomologyIso_inv_pi_eq_leftHomologyπ
    (T : ShortComplex (ModuleCat A)) [T.HasLeftHomology]
    (x : T.moduleCatLeftHomologyData.K) :
    T.moduleCatLeftHomologyData.leftHomologyIso.inv.hom
        (T.moduleCatLeftHomologyData.π.hom x) =
      T.leftHomologyπ.hom (T.moduleCatCyclesIso.inv.hom x) := by
  -- Route correction: normalize the transport through the concrete quotient model first, so the
  -- later zero-left presentation bridge can compare representatives instead of unfolding homology.
  have hcomm :
      T.leftHomologyπ ≫ T.moduleCatLeftHomologyData.leftHomologyIso.hom =
        T.moduleCatCyclesIso.hom ≫ T.moduleCatLeftHomologyData.π := by
    -- The owner `commπ` relation is exactly the comparison between the abstract and concrete
    -- left-homology quotients.
    simpa using
      (ShortComplex.leftHomologyMapData
        (𝟙 T) T.leftHomologyData T.moduleCatLeftHomologyData).commπ
  have hpoint :=
    congrArg
      (fun f : T.cycles ⟶ T.moduleCatLeftHomologyData.H ↦
        f.hom (T.moduleCatCyclesIso.inv.hom x))
      hcomm
  change
    T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom
        (T.leftHomologyπ.hom (T.moduleCatCyclesIso.inv.hom x)) =
      T.moduleCatLeftHomologyData.π.hom
        (T.moduleCatCyclesIso.hom (T.moduleCatCyclesIso.inv.hom x)) at hpoint
  rw [T.moduleCatCyclesIso.inv_hom_id_apply] at hpoint
  have hinj :
      Function.Injective T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom :=
    (ModuleCat.mono_iff_injective T.moduleCatLeftHomologyData.leftHomologyIso.hom).1
      inferInstance
  have hpoint' :
      T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom
          (T.leftHomologyπ.hom (T.moduleCatCyclesIso.inv.hom x)) =
        T.moduleCatLeftHomologyData.π.hom x := by
    exact hpoint
  -- After applying `leftHomologyIso.hom`, both sides become the same concrete quotient class.
  apply hinj
  calc
    T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom
        (T.moduleCatLeftHomologyData.leftHomologyIso.inv.hom
          (T.moduleCatLeftHomologyData.π.hom x)) =
      T.moduleCatLeftHomologyData.π.hom x := by
        simpa using
          T.moduleCatLeftHomologyData.leftHomologyIso.inv_hom_id_apply
            (T.moduleCatLeftHomologyData.π.hom x)
    _ =
      T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom
        (T.leftHomologyπ.hom (T.moduleCatCyclesIso.inv.hom x)) := by
        exact hpoint'.symm

/-- Helper for Lemma 15.101.4: the zero-left presentation complex
`0 ⟶ Hom_A(V, P) ⟶ Hom_A(U, P)` has vanishing left differential. -/
private theorem zero_left_presentation_comp_eq_zero
    {U V : Type x} [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    {P : Type y} [AddCommGroup P] [Module A P]
    (f : U →ₗ[A] V) :
    (0 : ModuleCat.of A PUnit ⟶ ModuleCat.of A (V →ₗ[A] P)) ≫
        ModuleCat.ofHom (LinearMap.lcomp A P f) =
      0 := by
  -- The left arrow is already zero, so the short-complex compatibility is immediate.
  simp

/-- Helper for Lemma 15.101.4: the fixed source complex attached to `f` and a target module `P`
is the two-term complex `0 ⟶ Hom_A(V, P) ⟶ Hom_A(U, P)`. -/
private noncomputable abbrev zero_left_presentation_shortComplex
    {U V : Type x} [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    {P : Type y} [AddCommGroup P] [Module A P]
    (f : U →ₗ[A] V) :
    ShortComplex (ModuleCat A) :=
  ShortComplex.mk
    (0 : ModuleCat.of A PUnit ⟶ ModuleCat.of A (V →ₗ[A] P))
    (ModuleCat.ofHom (LinearMap.lcomp A P f))
    (zero_left_presentation_comp_eq_zero (A := A) (P := P) f)

/-- Helper for Lemma 15.101.4: the zero-left presentation complex has left homology in
`ModuleCat A`. -/
private instance zero_left_presentation_hasLeftHomology
    {U V : Type x} [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    {P : Type y} [AddCommGroup P] [Module A P]
    (f : U →ₗ[A] V) :
    (zero_left_presentation_shortComplex (A := A) (P := P) f).HasLeftHomology := by
  let T := zero_left_presentation_shortComplex (A := A) (P := P) f
  let _ : HasKernel T.g := inferInstance
  let _ : HasCokernel (kernel.lift T.g T.f T.zero) := inferInstance
  infer_instance

/-- Helper for Lemma 15.101.4: in the zero-left presentation complex, the concrete boundary map
into cycles is zero because the left term is the zero module. -/
private theorem zero_left_presentation_moduleCatToCycles_eq_zero
    {U V : Type x} [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    {P : Type y} [AddCommGroup P] [Module A P]
    (f : U →ₗ[A] V) :
    (zero_left_presentation_shortComplex (A := A) (P := P) f).moduleCatToCycles = 0 := by
  -- Evaluate on the unique element of the zero source to reduce both maps to `0`.
  ext x
  have hx : x = 0 := Subsingleton.elim _ _
  subst hx
  simp [zero_left_presentation_shortComplex]

/-- Helper for Lemma 15.101.4: the concrete boundary range of the zero-left presentation complex
is trivial. -/
private theorem zero_left_presentation_range_moduleCatToCycles_eq_bot
    {U V : Type x} [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    {P : Type y} [AddCommGroup P] [Module A P]
    (f : U →ₗ[A] V) :
    LinearMap.range
        (zero_left_presentation_shortComplex (A := A) (P := P) f).moduleCatToCycles =
      ⊥ := by
  -- Once the boundary map is zero, its range is the zero submodule.
  rw [zero_left_presentation_moduleCatToCycles_eq_zero (A := A) (P := P) f]
  simp

/-- Helper for Lemma 15.101.4: for the zero-left presentation complex, the concrete left-homology
quotient is just the kernel of precomposition by `f`. -/
private noncomputable abbrev zero_left_presentation_concrete_leftHomology_equiv_kernel
    {U V : Type x} [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    {P : Type y} [AddCommGroup P] [Module A P]
    (f : U →ₗ[A] V) :
    (zero_left_presentation_shortComplex (A := A) (P := P) f).moduleCatLeftHomologyData.H ≃ₗ[A]
      LinearMap.ker (LinearMap.lcomp A P f) :=
  let T := zero_left_presentation_shortComplex (A := A) (P := P) f
  -- The concrete quotient collapses because the zero-left complex has no nontrivial boundaries.
  (Submodule.quotEquivOfEqBot (LinearMap.range T.moduleCatToCycles)
      (zero_left_presentation_range_moduleCatToCycles_eq_bot (A := A) (P := P) f)).trans
    (LinearEquiv.ofEq _ _ rfl)

/-- Helper for Lemma 15.101.4: the abstract left homology of the zero-left presentation complex
identifies with the kernel of precomposition by `f`. -/
private noncomputable abbrev zero_left_presentation_leftHomology_iso_kernel
    {U V : Type x} [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
    {P : Type y} [AddCommGroup P] [Module A P]
    (f : U →ₗ[A] V) :
    (zero_left_presentation_shortComplex (A := A) (P := P) f).leftHomology ≅
      ModuleCat.of A (LinearMap.ker (LinearMap.lcomp A P f)) :=
  let T := zero_left_presentation_shortComplex (A := A) (P := P) f
  -- First move from abstract left homology to the concrete quotient model, then collapse the
  -- quotient by the zero boundary range.
  T.moduleCatLeftHomologyData.leftHomologyIso ≪≫
    (zero_left_presentation_concrete_leftHomology_equiv_kernel
      (A := A) (P := P) f).toModuleIso

/-- Helper for Lemma 15.101.4: an ideal-power multiple in a finite product is detected
coordinatewise. -/
private theorem mem_idealPower_smul_top_fin_fun_iff
    {P : Type y} [AddCommGroup P] [Module A P]
    (s n : ℕ) (x : Fin s → P) :
    x ∈ I ^ (n + 1) • (⊤ : Submodule A (Fin s → P)) ↔
      ∀ i, x i ∈ I ^ (n + 1) • (⊤ : Submodule A P) := by
  constructor
  · intro hx
    -- The coordinatewise ideal-membership statement is stable under the generators of
    -- `I^(n + 1) • ⊤`.
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y hy i
      exact Submodule.smul_mem_smul ha (by simp)
    · intro y z hy hz i
      exact Submodule.add_mem _ (hy i) (hz i)
  · intro hx
    have hsingle :
        ∀ i, Pi.single i (x i) ∈ I ^ (n + 1) • (⊤ : Submodule A (Fin s → P)) := by
      intro i
      -- Rebuild the `i`-th coordinate function from the corresponding membership in `P`.
      refine Submodule.smul_induction_on (hx i) ?_ ?_
      · intro a ha y hy
        have hsingle :
            a • (Pi.single i y : Fin s → P) = Pi.single i (a • y) := by
          ext j
          by_cases hji : j = i
          · subst hji
            simp
          · simp [Pi.single_apply, hji]
        rw [← hsingle]
        exact
          Submodule.smul_mem_smul
            (I := I ^ (n + 1))
            (N := (⊤ : Submodule A (Fin s → P)))
            ha
            (by simp : Pi.single i y ∈ (⊤ : Submodule A (Fin s → P)))
      · intro y z hy hz
        have hsingle :
            (Pi.single i y : Fin s → P) + Pi.single i z = Pi.single i (y + z) := by
          ext j
          by_cases hji : j = i
          · subst hji
            simp
          · simp [Pi.single_apply, hji]
        rw [← hsingle]
        exact Submodule.add_mem _ hy hz
    have hx_repr : x = ∑ i : Fin s, Pi.single i (x i) := by
      ext i
      simp
    rw [hx_repr]
    exact Submodule.sum_mem _ fun i _ ↦ hsingle i

/-- Helper for Lemma 15.101.4: the coordinatewise quotient map on a finite product of modules. -/
private theorem free_pi_module_idealPowerQuotient_map_add
    {P : Type y} [AddCommGroup P] [Module A P]
    (s n : ℕ) :
    ∀ x y : Fin s → P,
      (fun i ↦ (Submodule.Quotient.mk (x i + y i) : idealPowerModuleQuotient I P n)) =
        (fun i ↦
          (Submodule.Quotient.mk (x i) : idealPowerModuleQuotient I P n) +
            Submodule.Quotient.mk (y i)) := by
  intro x y
  ext i
  rfl

/-- Helper for Lemma 15.101.4: the coordinatewise quotient map is `A`-linear. -/
private theorem free_pi_module_idealPowerQuotient_map_smul
    {P : Type y} [AddCommGroup P] [Module A P]
    (s n : ℕ) :
    ∀ (a : A) (x : Fin s → P),
      (fun i ↦ (Submodule.Quotient.mk ((a • x) i) : idealPowerModuleQuotient I P n)) =
        (fun i ↦ a • (Submodule.Quotient.mk (x i) : idealPowerModuleQuotient I P n)) := by
  intro a x
  ext i
  rfl

/-- Helper for Lemma 15.101.4: quotienting a finite product coordinatewise gives a linear map to
the product of the stagewise quotients. -/
private noncomputable def free_pi_module_idealPowerQuotient_map
    {P : Type y} [AddCommGroup P] [Module A P]
    (s n : ℕ) :
    (Fin s → P) →ₗ[A] (Fin s → idealPowerModuleQuotient I P n) where
  toFun := fun x i ↦ Submodule.Quotient.mk (x i)
  map_add' := free_pi_module_idealPowerQuotient_map_add (I := I) s n
  map_smul' := free_pi_module_idealPowerQuotient_map_smul (I := I) s n

/-- Helper for Lemma 15.101.4: the kernel of the coordinatewise quotient map is the expected
ideal-power multiple submodule. -/
private theorem ker_free_pi_module_idealPowerQuotient_map
    {P : Type y} [AddCommGroup P] [Module A P]
    (s n : ℕ) :
    LinearMap.ker (free_pi_module_idealPowerQuotient_map (I := I) (P := P) s n) =
      I ^ (n + 1) • (⊤ : Submodule A (Fin s → P)) := by
  ext x
  constructor
  · intro hx
    change free_pi_module_idealPowerQuotient_map (I := I) (P := P) s n x = 0 at hx
    rw [mem_idealPower_smul_top_fin_fun_iff (I := I) s n x]
    intro i
    have hxi :
        (free_pi_module_idealPowerQuotient_map (I := I) (P := P) s n x) i = 0 := by
      exact congrFun hx i
    exact (Submodule.Quotient.mk_eq_zero _).mp <| by
      simpa [free_pi_module_idealPowerQuotient_map] using hxi
  · intro hx
    change free_pi_module_idealPowerQuotient_map (I := I) (P := P) s n x = 0
    ext i
    exact (Submodule.Quotient.mk_eq_zero _).mpr <|
      (mem_idealPower_smul_top_fin_fun_iff (I := I) s n x).mp hx i

/-- Helper for Lemma 15.101.4: the coordinatewise quotient map on a finite product is
surjective. -/
private theorem free_pi_module_idealPowerQuotient_map_surjective
    {P : Type y} [AddCommGroup P] [Module A P]
    (s n : ℕ) :
    Function.Surjective (free_pi_module_idealPowerQuotient_map (I := I) (P := P) s n) := by
  intro y
  choose x hx using fun i : Fin s ↦
    Submodule.mkQ_surjective (I ^ (n + 1) • (⊤ : Submodule A P)) (y i)
  refine ⟨x, ?_⟩
  ext i
  exact hx i

/-- Helper for Lemma 15.101.4: quotienting a finite product by `I^(n+1)` is the same as taking
the product of the quotient modules. -/
private noncomputable abbrev free_pi_module_idealPowerQuotient_equiv
    {P : Type y} [AddCommGroup P] [Module A P]
    (s n : ℕ) :
    idealPowerModuleQuotient I (Fin s → P) n ≃ₗ[A] (Fin s → idealPowerModuleQuotient I P n) :=
  let π := free_pi_module_idealPowerQuotient_map (I := I) (P := P) s n
  let hker :
      I ^ (n + 1) • (⊤ : Submodule A (Fin s → P)) = LinearMap.ker π :=
    (ker_free_pi_module_idealPowerQuotient_map (I := I) (P := P) s n).symm
  let hrange : LinearMap.range π = ⊤ :=
    LinearMap.range_eq_top.2
      (free_pi_module_idealPowerQuotient_map_surjective (I := I) (P := P) s n)
  -- Rewrite to the actual kernel of the quotient map, then collapse the full range back to the
  -- codomain.
  (Submodule.quotEquivOfEq _ _ hker).trans
    (π.quotKerEquivRange.trans ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))

/-- Helper for Lemma 15.101.4: after identifying the range of a linear map with `⊤`, the
resulting equivalence to the codomain forgets the proof component. -/
private theorem range_eq_top_collapse_apply
    {X : Type x} [AddCommGroup X] [Module A X]
    {Y : Type y} [AddCommGroup Y] [Module A Y]
    (π : X →ₗ[A] Y) (hrange : LinearMap.range π = ⊤) (z : LinearMap.range π) :
    (((LinearEquiv.ofEq (LinearMap.range π) (⊤ : Submodule A Y) hrange).trans
        Submodule.topEquiv) z : Y) =
      z.1 := by
  -- After rewriting the range to `⊤`, the remaining equivalence is the canonical forgetful map.
  change
    (((LinearEquiv.ofEq (LinearMap.range π) (⊤ : Submodule A Y) hrange) z :
        (⊤ : Submodule A Y)) : Y) =
      z.1
  rfl

/-- Helper for Lemma 15.101.4: the finite-product quotient equivalence sends a quotient class to
the tuple of coordinatewise quotient classes. -/
private theorem free_pi_module_idealPowerQuotient_equiv_apply_mk
    {P : Type y} [AddCommGroup P] [Module A P]
    (s n : ℕ) (x : Fin s → P) :
    free_pi_module_idealPowerQuotient_equiv (I := I) (P := P) s n (Submodule.Quotient.mk x) =
      fun i ↦ (Submodule.Quotient.mk (x i) : idealPowerModuleQuotient I P n) := by
  let π := free_pi_module_idealPowerQuotient_map (I := I) (P := P) s n
  let hker :
      I ^ (n + 1) • (⊤ : Submodule A (Fin s → P)) = LinearMap.ker π :=
    (ker_free_pi_module_idealPowerQuotient_map (I := I) (P := P) s n).symm
  let hrange : LinearMap.range π = ⊤ :=
    LinearMap.range_eq_top.2
      (free_pi_module_idealPowerQuotient_map_surjective (I := I) (P := P) s n)
  -- Evaluate the quotient generator through the kernel transport and `quotKerEquivRange`, then
  -- collapse the final range-to-`⊤` wrapper on the concrete representative `π x`.
  unfold free_pi_module_idealPowerQuotient_equiv
  simp only [LinearEquiv.trans_apply]
  rw [Submodule.quotEquivOfEq_mk]
  change
    (((LinearEquiv.ofEq (LinearMap.range π)
          (⊤ : Submodule A (Fin s → idealPowerModuleQuotient I P n)) hrange).trans
        Submodule.topEquiv) ⟨π x, LinearMap.mem_range_self π x⟩ :
        Fin s → idealPowerModuleQuotient I P n) =
      fun i ↦ (Submodule.Quotient.mk (x i) : idealPowerModuleQuotient I P n)
  rfl

/-- Helper for Lemma 15.101.4: a linear map out of `A^s` is determined by the images of the
standard basis vectors. -/
private theorem finite_free_hom_to_pi_map_add
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) :
    ∀ φ ψ : ((Fin s → A) →ₗ[A] P),
      (fun i ↦ (φ + ψ) (Pi.basisFun A (Fin s) i)) =
        (fun i ↦ φ (Pi.basisFun A (Fin s) i) + ψ (Pi.basisFun A (Fin s) i)) := by
  intro φ ψ
  ext i
  simp

/-- Helper for Lemma 15.101.4: evaluating on the standard basis is `A`-linear on
`Hom_A(A^s, P)`. -/
private theorem finite_free_hom_to_pi_map_smul
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) :
    ∀ (a : A) (φ : ((Fin s → A) →ₗ[A] P)),
      (fun i ↦ (a • φ) (Pi.basisFun A (Fin s) i)) =
        (fun i ↦ a • φ (Pi.basisFun A (Fin s) i)) := by
  intro a φ
  ext i
  simp

/-- Helper for Lemma 15.101.4: evaluation on the standard basis gives the forward finite-free Hom
equivalence. -/
private noncomputable def finite_free_hom_to_pi
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) :
    (((Fin s → A) →ₗ[A] P)) →ₗ[A] (Fin s → P) where
  toFun := fun φ i ↦ φ (Pi.basisFun A (Fin s) i)
  map_add' := finite_free_hom_to_pi_map_add (A := A) s
  map_smul' := finite_free_hom_to_pi_map_smul (A := A) s

/-- Helper for Lemma 15.101.4: the tuple of images of the basis vectors defines the corresponding
map `A^s → P`. -/
private def finite_free_hom_from_pi_fun
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) (x : Fin s → P) :
    (Fin s → A) →ₗ[A] P :=
  ∑ i : Fin s, (LinearMap.proj i).smulRight (x i)

/-- Helper for Lemma 15.101.4: converting a tuple to the corresponding free-module map is
additive. -/
private theorem finite_free_hom_from_pi_fun_add
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) :
    ∀ x y : Fin s → P,
      finite_free_hom_from_pi_fun (A := A) s (x + y) =
        finite_free_hom_from_pi_fun (A := A) s x +
          finite_free_hom_from_pi_fun (A := A) s y := by
  intro x y
  ext v
  simp [finite_free_hom_from_pi_fun, Finset.sum_add_distrib]

/-- Helper for Lemma 15.101.4: converting a tuple to the corresponding free-module map respects
scalar multiplication. -/
private theorem finite_free_hom_from_pi_fun_smul
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) :
    ∀ (a : A) (x : Fin s → P),
      finite_free_hom_from_pi_fun (A := A) s (a • x) =
        a • finite_free_hom_from_pi_fun (A := A) s x := by
  intro a x
  apply LinearMap.ext
  intro v
  calc
    finite_free_hom_from_pi_fun (A := A) s (a • x) v =
        ∑ i : Fin s, v i • (a • x i) := by
          simp [finite_free_hom_from_pi_fun]
    _ = ∑ i : Fin s, a • (v i • x i) := by
          simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
    _ = a • ∑ i : Fin s, v i • x i := by
          rw [Finset.smul_sum]
    _ = (a • finite_free_hom_from_pi_fun (A := A) s x) v := by
          simp [finite_free_hom_from_pi_fun]

/-- Helper for Lemma 15.101.4: the inverse finite-free Hom equivalence sending a tuple to the
corresponding map `A^s → P`. -/
private noncomputable def finite_free_hom_from_pi
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) :
    (Fin s → P) →ₗ[A] (((Fin s → A) →ₗ[A] P)) where
  toFun := finite_free_hom_from_pi_fun (A := A) s
  map_add' := finite_free_hom_from_pi_fun_add (A := A) s
  map_smul' := finite_free_hom_from_pi_fun_smul (A := A) s

/-- Helper for Lemma 15.101.4: converting a tuple to a map and then evaluating on the basis
recovers the original tuple. -/
private theorem finite_free_hom_to_pi_comp_from_pi
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) :
    (finite_free_hom_to_pi (A := A) (P := P) s).comp
        (finite_free_hom_from_pi (A := A) (P := P) s) =
      LinearMap.id := by
  ext x i
  -- Only the `i`-th basis vector contributes to the finite sum.
  simp [finite_free_hom_to_pi, finite_free_hom_from_pi, finite_free_hom_from_pi_fun]

/-- Helper for Lemma 15.101.4: converting a map to its basis tuple and rebuilding it gives the
original map. -/
private theorem finite_free_hom_from_pi_comp_to_pi
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) :
    (finite_free_hom_from_pi (A := A) (P := P) s).comp
        (finite_free_hom_to_pi (A := A) (P := P) s) =
      LinearMap.id := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro v
  -- Expand the source vector in the standard basis of `A^s` and use linearity of `φ`.
  have hv : v = ∑ i : Fin s, v i • Pi.basisFun A (Fin s) i := by
    simpa [Pi.basisFun_repr] using ((Pi.basisFun A (Fin s)).sum_repr v).symm
  calc
    ((finite_free_hom_from_pi (A := A) (P := P) s).comp
        (finite_free_hom_to_pi (A := A) (P := P) s)) φ v =
      ∑ i : Fin s, v i • φ (Pi.basisFun A (Fin s) i) := by
        simp [finite_free_hom_to_pi, finite_free_hom_from_pi, finite_free_hom_from_pi_fun]
    _ = φ (∑ i : Fin s, v i • Pi.basisFun A (Fin s) i) := by
        rw [map_sum]
        simp
    _ = φ v := by
        symm
        have hv' :
            ∑ i : Fin s, (∑ j : Fin s, v j • Pi.basisFun A (Fin s) j) i •
                Pi.basisFun A (Fin s) i =
              ∑ i : Fin s, v i • Pi.basisFun A (Fin s) i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hcoeff :
              (∑ j : Fin s, v j • Pi.basisFun A (Fin s) j) i = v i := by
            simpa [Pi.basisFun] using (congrArg (fun f : Fin s → A ↦ f i) hv).symm
          rw [hcoeff]
        rw [hv]
        exact congrArg φ hv'.symm

/-- Helper for Lemma 15.101.4: `Hom_A(A^s, P)` is canonically the product `P^s`. -/
private noncomputable abbrev finite_free_hom_equiv_pi
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) :
    (((Fin s → A) →ₗ[A] P)) ≃ₗ[A] (Fin s → P) :=
  LinearEquiv.ofLinear
    (finite_free_hom_to_pi (A := A) (P := P) s)
    (finite_free_hom_from_pi (A := A) (P := P) s)
    (finite_free_hom_to_pi_comp_from_pi (A := A) (P := P) s)
    (finite_free_hom_from_pi_comp_to_pi (A := A) (P := P) s)

/-- Helper for Lemma 15.101.4: a linear equivalence transports the `I^(n+1)`-quotient. -/
private theorem idealPowerModuleQuotient_congr_map
    {X : Type x} [AddCommGroup X] [Module A X]
    {Y : Type y} [AddCommGroup Y] [Module A Y]
    (e : X ≃ₗ[A] Y) (n : ℕ) :
    Submodule.map (e : X →ₗ[A] Y) (I ^ (n + 1) • (⊤ : Submodule A X)) =
      I ^ (n + 1) • (⊤ : Submodule A Y) := by
  -- The equivalence carries the full source module onto the full target module.
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 e.surjective]

/-- Helper for Lemma 15.101.4: ideal-power quotients are functorial under linear equivalence. -/
private noncomputable abbrev idealPowerModuleQuotient_congr
    {X : Type x} [AddCommGroup X] [Module A X]
    {Y : Type y} [AddCommGroup Y] [Module A Y]
    (e : X ≃ₗ[A] Y) (n : ℕ) :
    idealPowerModuleQuotient I X n ≃ₗ[A] idealPowerModuleQuotient I Y n :=
  Submodule.Quotient.equiv
    (I ^ (n + 1) • (⊤ : Submodule A X))
    (I ^ (n + 1) • (⊤ : Submodule A Y))
    e
    (idealPowerModuleQuotient_congr_map (I := I) e n)

/-- Helper for Lemma 15.101.4: the quotient equivalence induced by a linear equivalence acts on
quotient representatives by applying that equivalence. -/
private theorem idealPowerModuleQuotient_congr_apply_mk
    {X : Type x} [AddCommGroup X] [Module A X]
    {Y : Type y} [AddCommGroup Y] [Module A Y]
    (e : X ≃ₗ[A] Y) (n : ℕ) (x : X) :
    (idealPowerModuleQuotient_congr (I := I) e n) (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (e x) : idealPowerModuleQuotient I Y n) := by
  -- The induced quotient map is literally the linear equivalence applied to the chosen
  -- representative.
  rfl

/-- Helper for Lemma 15.101.4: quotienting `Hom_A(A^s, P)` by `I^(n+1)` agrees with taking
`Hom_A(A^s, P / I^(n+1) P)`. -/
private noncomputable abbrev free_linear_hom_idealPowerQuotient_equiv
    {P : Type y} [AddCommGroup P] [Module A P]
    (s n : ℕ) :
    idealPowerModuleQuotient I (((Fin s → A) →ₗ[A] P)) n ≃ₗ[A]
      (((Fin s → A) →ₗ[A] idealPowerModuleQuotient I P n)) :=
  (idealPowerModuleQuotient_congr
      (I := I)
      (finite_free_hom_equiv_pi (A := A) (P := P) s)
      n).trans
    ((free_pi_module_idealPowerQuotient_equiv (I := I) (P := P) s n).trans
      (finite_free_hom_equiv_pi (A := A) (P := idealPowerModuleQuotient I P n) s).symm)

/-- Helper for Lemma 15.101.4: rebuilding a map from its basis tuple evaluates as the expected
finite linear combination. -/
private theorem finite_free_hom_from_pi_fun_apply
    {P : Type y} [AddCommGroup P] [Module A P]
    (s : ℕ) (x : Fin s → P) (v : Fin s → A) :
    finite_free_hom_from_pi_fun (A := A) s x v = ∑ i : Fin s, v i • x i := by
  -- Expand the sum of `smulRight` basis projections and evaluate at `v`.
  simp [finite_free_hom_from_pi_fun]

/-- Helper for Lemma 15.101.4: after identifying the quotient of `Hom_A(A^s, P)` with
`Hom_A(A^s, P / I^(n+1) P)`, a quotient class acts on a vector by reducing the original value
coordinatewise. -/
private theorem free_linear_hom_idealPowerQuotient_equiv_apply_mk_apply
    {P : Type y} [AddCommGroup P] [Module A P]
    (s n : ℕ) (φ : ((Fin s → A) →ₗ[A] P)) (v : Fin s → A) :
    free_linear_hom_idealPowerQuotient_equiv (I := I) (P := P) s n
        (Submodule.Quotient.mk φ) v =
      (Submodule.Quotient.mk (φ v) : idealPowerModuleQuotient I P n) := by
  have hbasis :
      ∑ i : Fin s, v i • φ (Pi.basisFun A (Fin s) i) = φ v := by
    -- Reconstruct `φ` from its basis tuple before evaluating the rebuilt map at `v`.
    have hcomp :=
      LinearMap.congr_fun (finite_free_hom_from_pi_comp_to_pi (A := A) (P := P) s) φ
    have hpoint :=
      congrArg (fun ψ : ((Fin s → A) →ₗ[A] P) ↦ ψ v) hcomp
    simpa [finite_free_hom_to_pi, finite_free_hom_from_pi, finite_free_hom_from_pi_fun] using
      hpoint
  -- Send the quotient generator through the finite-free identifications, then evaluate the
  -- resulting quotient-valued map on `v`.
  unfold free_linear_hom_idealPowerQuotient_equiv
  simp only [LinearEquiv.trans_apply]
  rw [idealPowerModuleQuotient_congr_apply_mk]
  change
    finite_free_hom_from_pi_fun (A := A) s
        (free_pi_module_idealPowerQuotient_equiv (I := I) (P := P) s n
          (Submodule.Quotient.mk
            ((finite_free_hom_equiv_pi (A := A) (P := P) s) φ))) v =
      (Submodule.Quotient.mk (φ v) : idealPowerModuleQuotient I P n)
  rw [free_pi_module_idealPowerQuotient_equiv_apply_mk]
  change
    finite_free_hom_from_pi_fun (A := A) s
        (fun i ↦
          (Submodule.Quotient.mk
            ((finite_free_hom_equiv_pi (A := A) (P := P) s) φ i) :
              idealPowerModuleQuotient I P n)) v =
      (Submodule.Quotient.mk (φ v) : idealPowerModuleQuotient I P n)
  rw [finite_free_hom_from_pi_fun_apply]
  calc
    ∑ i : Fin s,
        v i •
          (Submodule.Quotient.mk
            ((finite_free_hom_equiv_pi (A := A) (P := P) s) φ i) :
              idealPowerModuleQuotient I P n) =
      ∑ i : Fin s,
        v i •
          (Submodule.Quotient.mk
            (φ (Pi.basisFun A (Fin s) i)) : idealPowerModuleQuotient I P n) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rfl
    _ =
      (Submodule.Quotient.mk
        (∑ i : Fin s, v i • φ (Pi.basisFun A (Fin s) i)) : idealPowerModuleQuotient I P n) := by
          -- Normalize both sides to the explicit quotient map and use its additive/linear simp
          -- rules.
          symm
          change
            Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A P))
              (∑ i : Fin s, v i • φ (Pi.basisFun A (Fin s) i)) =
            ∑ i : Fin s,
              Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A P))
                (v i • φ (Pi.basisFun A (Fin s) i))
          simp
    _ = (Submodule.Quotient.mk (φ v) : idealPowerModuleQuotient I P n) := by
          exact
            congrArg
              (fun z : P ↦ (Submodule.Quotient.mk z : idealPowerModuleQuotient I P n))
              hbasis

/-- Helper for Lemma 15.101.4: the free-source quotient/Hom equivalence intertwines quotienting
precomposition by `f` with literal precomposition on the quotient target. -/
private theorem free_linear_hom_idealPowerQuotient_equiv_lcomp_naturality
    {P : Type y} [AddCommGroup P] [Module A P]
    {m n : ℕ} (f : (Fin m → A) →ₗ[A] (Fin n → A)) (k : ℕ) :
    (free_linear_hom_idealPowerQuotient_equiv (I := I) (P := P) m k).toLinearMap.comp
        ((LinearMap.lcomp A P f).quotientMapByIdeal (I ^ (k + 1))) =
      (LinearMap.lcomp A (idealPowerModuleQuotient I P k) f).comp
        (free_linear_hom_idealPowerQuotient_equiv (I := I) (P := P) n k).toLinearMap := by
  apply DFunLike.ext
  intro x
  obtain ⟨φ, rfl⟩ := Submodule.mkQ_surjective
    (I ^ (k + 1) • (⊤ : Submodule A (((Fin n → A) →ₗ[A] P)))) x
  -- Check the conjugation identity on a quotient representative and then evaluate the resulting
  -- quotient-valued maps at `v`.
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply]
  rw [quotientMapByIdeal_apply_mkQ]
  have hleft :=
    free_linear_hom_idealPowerQuotient_equiv_apply_mk_apply
      (I := I) (P := P) m k ((LinearMap.lcomp A P f) φ) v
  have hright :=
    free_linear_hom_idealPowerQuotient_equiv_apply_mk_apply
      (I := I) (P := P) n k φ (f v)
  calc
    free_linear_hom_idealPowerQuotient_equiv (I := I) (P := P) m k
        ((I ^ (k + 1) •
            (⊤ : Submodule A (((Fin m → A) →ₗ[A] P)))).mkQ ((LinearMap.lcomp A P f) φ)) v =
      (Submodule.Quotient.mk (((LinearMap.lcomp A P f) φ) v) : idealPowerModuleQuotient I P k) := by
          simpa using hleft
    _ = (Submodule.Quotient.mk (φ (f v)) : idealPowerModuleQuotient I P k) := by
          rfl
    _ =
      (LinearMap.lcomp A (idealPowerModuleQuotient I P k) f)
        (free_linear_hom_idealPowerQuotient_equiv (I := I) (P := P) n k
          ((I ^ (k + 1) •
              (⊤ : Submodule A (((Fin n → A) →ₗ[A] P)))).mkQ φ)) v := by
          simpa using hright.symm

/-- Helper for Lemma 15.101.4: reducing the source Hom-quotient stage from `k + 2` to `k + 1`
commutes with the finite-free quotient/Hom equivalence. -/
private theorem free_linear_hom_idealPowerQuotient_equiv_transition_naturality
    {P : Type y} [AddCommGroup P] [Module A P]
    (s k : ℕ) :
    (homIdealPowerStep I (Fin s → A) P k).comp
        (free_linear_hom_idealPowerQuotient_equiv (I := I) (P := P) s (k + 1)).toLinearMap =
      (free_linear_hom_idealPowerQuotient_equiv (I := I) (P := P) s k).toLinearMap.comp
        (AdicCompletion.transitionMap I (((Fin s → A) →ₗ[A] P)) (Nat.le_succ (k + 1))) := by
  -- Evaluate both composites on a quotient representative and then on a basis-free vector `v`.
  apply LinearMap.ext
  intro x
  obtain ⟨φ, rfl⟩ := Submodule.mkQ_surjective
    (I ^ (k + 2) • (⊤ : Submodule A (((Fin s → A) →ₗ[A] P)))) x
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply]
  have hhigh :=
    free_linear_hom_idealPowerQuotient_equiv_apply_mk_apply
      (I := I) (P := P) s (k + 1) φ v
  have hlow :=
    free_linear_hom_idealPowerQuotient_equiv_apply_mk_apply
      (I := I) (P := P) s k φ v
  calc
    homIdealPowerStep I (Fin s → A) P k
        (free_linear_hom_idealPowerQuotient_equiv (I := I) (P := P) s (k + 1)
          ((I ^ (k + 2) •
              (⊤ : Submodule A (((Fin s → A) →ₗ[A] P)))).mkQ φ)) v =
      AdicCompletion.transitionMap I P (Nat.le_succ (k + 1))
        ((Submodule.Quotient.mk (φ v) : idealPowerModuleQuotient I P (k + 1))) := by
          simpa [homIdealPowerStep] using congrArg (fun ψ ↦ ψ v) hhigh
    _ = (Submodule.Quotient.mk (φ v) : idealPowerModuleQuotient I P k) := by
          rfl
    _ =
      free_linear_hom_idealPowerQuotient_equiv (I := I) (P := P) s k
        (AdicCompletion.transitionMap I (((Fin s → A) →ₗ[A] P)) (Nat.le_succ (k + 1))
          ((I ^ (k + 2) •
              (⊤ : Submodule A (((Fin s → A) →ₗ[A] P)))).mkQ φ)) v := by
          simpa using (congrArg (fun ψ ↦ ψ v) hlow).symm

/-- Helper for Lemma 15.101.4: the ideal-power quotient of the zero module is canonically the
zero module again. -/
private noncomputable abbrev idealPowerModuleQuotient_punit_iso
    (k : ℕ) :
    ModuleCat.of A (idealPowerModuleQuotient I PUnit k) ≅ ModuleCat.of A PUnit :=
  (LinearEquiv.ofSubsingleton _ _).toModuleIso

/-- Helper for Lemma 15.101.4: the explicit quotient-stage short complex attached to the fixed
zero-left presentation. -/
private theorem zero_left_presentation_idealPowerStageComplex_zero
    {m n : ℕ} (f : (Fin m → A) →ₗ[A] (Fin n → A)) (k : ℕ) :
    (0 :
      ModuleCat.of A (idealPowerModuleQuotient I PUnit k) ⟶
        ModuleCat.of A (idealPowerModuleQuotient I (((Fin n → A) →ₗ[A] N)) k)) ≫
      ModuleCat.ofHom ((LinearMap.lcomp A N f).quotientMapByIdeal (I ^ (k + 1))) =
        0 := by
  -- The quotient-stage complex is still zero on the left.
  simp

/-- Helper for Lemma 15.101.4: an explicit model for the quotient-stage complex of the fixed
zero-left presentation. -/
private noncomputable abbrev zero_left_presentation_idealPowerStageComplex
    {m n : ℕ} (f : (Fin m → A) →ₗ[A] (Fin n → A)) (k : ℕ) :
    ShortComplex (ModuleCat A) :=
  ShortComplex.mk
    (0 :
      ModuleCat.of A (idealPowerModuleQuotient I PUnit k) ⟶
        ModuleCat.of A (idealPowerModuleQuotient I (((Fin n → A) →ₗ[A] N)) k))
    (ModuleCat.ofHom ((LinearMap.lcomp A N f).quotientMapByIdeal (I ^ (k + 1))))
    (zero_left_presentation_idealPowerStageComplex_zero
      (A := A) (I := I) (N := N) f k)

/-- Helper for Lemma 15.101.4: the explicit quotient-stage complex is canonically the zero-left
presentation over the quotient target module. -/
private noncomputable abbrev zero_left_presentation_stageComplex_iso
    {m n : ℕ} (f : (Fin m → A) →ₗ[A] (Fin n → A)) (k : ℕ) :
    zero_left_presentation_idealPowerStageComplex (A := A) (I := I) (N := N) f k ≅
      zero_left_presentation_shortComplex
        (A := A) (P := idealPowerModuleQuotient I N k) f :=
  ShortComplex.isoMk
    (idealPowerModuleQuotient_punit_iso (A := A) (I := I) k)
    (ModuleCat.ofIso
      ((free_linear_hom_idealPowerQuotient_equiv (I := I) (P := N) n k).toModuleIso))
    (ModuleCat.ofIso
      ((free_linear_hom_idealPowerQuotient_equiv (I := I) (P := N) m k).toModuleIso))
    (by
      -- The left square is trivial because both differentials vanish.
      ext x
      simp)
    (by
      -- The right square is exactly the finite-free quotient/Hom naturality statement.
      ext x
      simp only [Category.assoc, ModuleCat.comp_hom, LinearMap.comp_assoc]
      simpa [zero_left_presentation_shortComplex, zero_left_presentation_idealPowerStageComplex]
        using
          free_linear_hom_idealPowerQuotient_equiv_lcomp_naturality
            (A := A) (I := I) (P := N) (m := m) (n := n) f k)

local notation "HomTower" => homIdealPowerTower I M N
local notation "IsoTower" => moduleIsomorphismTower I M N
local notation "HomComparison" => fun n ↦ homReductionComparison I M N n

-- Proof sketch: choose a finite presentation of `M`, rewrite `Hom_A(M_n, N_n)` as the middle
-- homology of the induced two-term quotient complex, and apply Lemma `15.101.1 (3)` to that
-- complex.
/-- Lemma 15.101.4 (1): for finite `A`-modules `M` and `N` over a Noetherian ring, the inverse
system `(\mathrm{Hom}_A(M_n, N_n))_n`, identified with
`(\mathrm{Hom}_A(M, N / I^(n + 1) N))_n`, is Mittag-Leffler. -/
theorem homIdealPowerTower_isMittagLeffler :
    SequentialInverseSystem.IsMittagLeffler HomTower := by
  -- TODO: fix one finite presentation `A^t → A^s → M → 0`, identify `HomTower` with the
  -- quotient-homology tower of the induced two-term complex `0 → N^s → N^t`, and transport
  -- `CategoryTheory.ShortComplex.idealPowerHomologyTower_isMittagLeffler` across that tower
  -- isomorphism.
  sorry

-- Proof sketch: apply the homomorphism case to both directions `M → N` and `N → M`, then use the
-- Nakayama argument from the Stacks proof to show that an inverse pair modulo a sufficiently low
-- stage lifts to a genuine inverse pair at every higher stage.
/-- Lemma 15.101.4 (2): the inverse system of `A`-linear isomorphisms
`(\operatorname{Isom}_A(M_n, N_n))_n` is Mittag-Leffler. -/
theorem moduleIsomorphismTower_isMittagLeffler :
    Functor.IsMittagLeffler IsoTower := by
  -- TODO: combine the Hom-tower Mittag-Leffler statements in both directions with the Nakayama
  -- lifting lemma that upgrades mutual inverses after reduction to genuine higher-stage
  -- isomorphisms.
  sorry

-- Proof sketch: use the same finite presentation of `M` and the Artin-Rees comparison from Lemma
-- `15.101.1 (5)` for the resulting two-term complex to obtain one constant `c` that annihilates
-- the kernel and cokernel at every stage.
/-- Lemma 15.101.4 (3): there is a single constant `c > 0` such that for every `n`, the kernel
and cokernel of the canonical comparison map
`Hom_A(M, N) / I^(n + 1) Hom_A(M, N) → Hom_A(M_n, N_n)` are killed by `I^c`. -/
theorem exists_homReductionComparison_annihilated_kernel_cokernel :
    ∃ c : ℕ, 0 < c ∧
      (∀ n : ℕ,
        I ^ c • (⊤ : Submodule A (LinearMap.ker (HomComparison n))) = ⊥) ∧
      ∀ n : ℕ,
        I ^ c •
            (⊤ :
              Submodule A
                (homIdealPowerStage I M N n ⧸ LinearMap.range (HomComparison n))) =
          ⊥ := by
  -- TODO: after the same presentation bridge as in part `(1)`, read off the kernel/cokernel
  -- annihilation constant from
  -- `CategoryTheory.ShortComplex.exists_kernel_cokernel_annihilation_for_leftHomologyComparison`.
  sorry

-- Proof sketch: the same Artin-Rees comparison identifies the Hom tower with the quotient tower
-- of `Hom_A(M, N)` as a pro-object, so Lemma `15.101.1 (2)` yields the inverse-limit comparison
-- with the `I`-adic completion of `Hom_A(M, N)`.
/-- Lemma 15.101.4 (4): the inverse limit of the system `(\mathrm{Hom}_A(M_n, N_n))_n`,
identified with `(\mathrm{Hom}_A(M, N / I^(n + 1) N))_n`, is canonically isomorphic to the
`I`-adic completion of `Hom_A(M, N)`. -/
theorem limit_homIdealPowerTower_iso_completedHom :
    IsIsomorphic
      (limit HomTower)
      (ModuleCat.of A (AdicCompletion I (M →ₗ[A] N))) := by
  -- TODO: reuse the presentation bridge from part `(1)` and transport
  -- `CategoryTheory.ShortComplex.limit_idealPowerHomologyTower_iso_limit_leftHomologyQuotientTower`
  -- to the canonical quotient tower of `Hom_A(M, N)`.
  sorry

-- Proof sketch: combine the inverse-limit description of completions with the fact that finite
-- modules satisfy `M^ = \varprojlim M_n` and `N^ = \varprojlim N_n`, then identify compatible
-- systems of maps with `A^`-linear maps between the completed modules as in Lemma `10.97.4`.
/-- Lemma 15.101.4 (5): the `I`-adic completion of `Hom_A(M, N)` is canonically isomorphic, as an
`A^`-module, to `Hom_{A^}(M^, N^)`, where completion is taken with respect to `I`. -/
theorem completedHom_iso_completedLinearMap :
    IsIsomorphic
      (ModuleCat.of (AdicCompletion I A) (AdicCompletion I (M →ₗ[A] N)))
      (ModuleCat.of (AdicCompletion I A)
        ((AdicCompletion I M) →ₗ[AdicCompletion I A] (AdicCompletion I N))) := by
  -- TODO: identify a compatible family in `HomTower` with a map `M →ₗ[A] AdicCompletion I N`,
  -- extend it across completion via `AdicCompletion.mapToComplete`, and prove the inverse
  -- reduction map using `adicCompletionQuotientPowLinearEquiv`.
  sorry

-- Proof sketch: an element of the inverse limit of the isomorphism tower is a compatible family
-- of stagewise inverses. Apply the previous Hom-limit comparison in both directions and use the
-- Nakayama argument from the Stacks proof to show that the two limiting maps are inverse.
/-- Lemma 15.101.4 (6): the inverse limit of the system `(\operatorname{Isom}_A(M_n, N_n))_n`
is canonically identified with the type of `A^`-linear isomorphisms `M^ ≃ N^`. -/
theorem limit_moduleIsomorphismTower_iso_completedLinearEquiv :
    IsIsomorphic
      (limit IsoTower)
      (AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N) := by
  -- TODO: apply the completed-Hom comparison in both directions to compatible inverse families and
  -- use the higher-stage Nakayama lifting step to show the two completed maps are inverse.
  sorry

end
