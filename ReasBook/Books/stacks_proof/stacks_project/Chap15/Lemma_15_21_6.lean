import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import StacksProject_2024.Chap10.Lemma_10_36_4
import StacksProject_2024.Chap10.Lemma_10_168_1
import StacksProject_2024.Chap10.Lemma_10_39_7
import StacksProject_2024.Chap15.Lemma_15_21_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.IsIntegral R S]
variable (n : ℕ)
local notation "P" => MvPolynomial (Fin n) R
variable {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M]
variable [Module.FinitePresentation (MvPolynomial (Fin n) R) M]

/- Domain triage:
- primary domain: flatness descent for modules finitely presented over a polynomial `R`-algebra
  along an injective integral base change `R → S`;
- sampled owner declarations:
  `Module.Flat`,
  `Module.FinitePresentation`,
  `MvPolynomial (Fin n) R`,
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`;
- best owner abstraction: the canonical flatness predicate `Module.Flat R M`, with the polynomial
  arity `n` kept explicit because it is not inferable from the module arguments;
- primitive data: the injective integral algebra map `R → S`, the polynomial owner ring `P`,
  the `P`-module structure on `M`, and the finite-presentation hypothesis
  `[Module.FinitePresentation P M]`;
- derived API: the base-change flatness hypothesis and flatness conclusion for the canonical
  restricted-scalar `R`-module `RestrictScalars R P M`.

Layering:
- `source-facing`: the polynomial finite-presentation descent statement from the source text;
- `core/canonical`: `Module.Flat` and `Module.FinitePresentation`;
- `bridge/view`: the Chapter 15 finite-base-change descent theorem
  `flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct`;
  this file is the source-facing polynomial finite-presentation specialization feeding into that
  bridge, not a second flatness owner.
-/

-- Proof sketch: choose a finite presentation of `M` over `R[x_1, ..., x_n]`, spread the finitely
-- many coefficients to a finitely generated `ℤ`-subalgebra `R₀ ⊆ R` and a finite `R₀`-subalgebra
-- `S₀ ⊆ S`, descend flatness of `S ⊗[R] RestrictScalars R P M` to some stage by finite
-- presentation, apply Lemma `15.21.5` to `R₀ → S₀`, and then recover flatness of
-- `RestrictScalars R P M` over `R` by base change via Lemma `10.39.7`.
/-- Helper for Lemma 15.21.6: flatness over a finite injective stage descends to the source stage
by Lemma `15.21.5`. -/
lemma flat_of_flat_finite_integral_stage
    {R₀ : Type*} {S₀ : Type*} [CommRing R₀] [CommRing S₀] [Algebra R₀ S₀]
    [IsNoetherianRing R₀] [Module.Finite R₀ S₀]
    {M₀ : Type*} [AddCommGroup M₀] [Module R₀ M₀]
    (hinj : Function.Injective (algebraMap R₀ S₀))
    (hflat : Module.Flat S₀ (S₀ ⊗[R₀] M₀)) :
    Module.Flat R₀ M₀ := by
  -- Proof comment: this is exactly the Chapter 15 finite-injective flatness descent theorem.
  exact
    flat_of_isNoetherianRing_of_moduleFinite_of_injective_algebraMap_of_flat_tensorProduct
      (R := R₀) (S := S₀) (M := M₀) hinj hflat

/-- Helper for Lemma 15.21.6: a source stage in the finite-presentation approximation is
Noetherian because it is of finite type over `ℤ`. -/
lemma source_stage_isNoetherian
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S']
    {f : R' →+* S'} {N : Type*} [AddCommGroup N] [Module S' N]
    (A : DirectedFinitePresentationModuleApproximation f N) (i : A.Λ) :
    IsNoetherianRing (A.RStage i) := by
  -- Proof comment: every source stage in the approximation is finite type over `ℤ`, hence
  -- Noetherian by the standard finite-type theorem.
  let _ : Algebra ℤ (A.RStage i) := (Int.castRingHom (A.RStage i)).toAlgebra
  let _ : Algebra.FiniteType ℤ (A.RStage i) := A.source_finiteType i
  exact Algebra.FiniteType.isNoetherianRing ℤ (A.RStage i)

/-- Helper for Lemma 15.21.6: each target stage in the finite-presentation approximation is
Noetherian because it is of finite type over a Noetherian source stage. -/
lemma target_stage_isNoetherian
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S']
    {f : R' →+* S'} {N : Type*} [AddCommGroup N] [Module S' N]
    (A : DirectedFinitePresentationModuleApproximation f N) (i : A.Λ) :
    IsNoetherianRing (A.SStage i) := by
  -- Proof comment: finite type over the Noetherian source stage forces the target stage to be
  -- Noetherian as well.
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra.FiniteType (A.RStage i) (A.SStage i) := A.target_finiteType i
  let _ : IsNoetherianRing (A.RStage i) := source_stage_isNoetherian A i
  exact Algebra.FiniteType.isNoetherianRing (A.RStage i) (A.SStage i)

/-- Helper for Lemma 15.21.6: each approximating stage module is finitely presented over its
target stage because the approximation stores it as a finite module. -/
lemma stage_module_finitePresentation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S']
    {f : R' →+* S'} {N : Type*} [AddCommGroup N] [Module S' N]
    (A : DirectedFinitePresentationModuleApproximation f N) (i : A.Λ) :
    Module.FinitePresentation (A.SStage i) (A.moduleStage i) := by
  -- Proof comment: over a commutative ring, finite modules are finitely presented in the
  -- approximation API used here.
  let _ : IsNoetherianRing (A.SStage i) := target_stage_isNoetherian A i
  exact Module.finitePresentation_of_finite (A.SStage i) (A.moduleStage i)

/-- Helper for Lemma 15.21.6: each stage map in the finite-presentation approximation is itself
of finite presentation. -/
lemma stageMap_finitePresentation
    {R' : Type*} {S' : Type*} [CommRing R'] [CommRing S']
    {f : R' →+* S'} {N : Type*} [AddCommGroup N] [Module S' N]
    (A : DirectedFinitePresentationModuleApproximation f N) (i : A.Λ) :
    (A.stageMap i).FinitePresentation := by
  -- Proof comment: finite type over a Noetherian source stage upgrades to finite presentation,
  -- and then we convert back to the ring-hom formulation used by the approximation API.
  let _ : Algebra (A.RStage i) (A.SStage i) := (A.stageMap i).toAlgebra
  let _ : Algebra.FiniteType (A.RStage i) (A.SStage i) := A.target_finiteType i
  let _ : IsNoetherianRing (A.RStage i) := source_stage_isNoetherian A i
  have hAlg : Algebra.FinitePresentation (A.RStage i) (A.SStage i) :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  exact RingHom.finitePresentation_algebraMap.mpr hAlg

/-- Helper for Lemma 15.21.6: the finitely presented `P`-module descends to one Noetherian source
stage together with its descended owner algebra `P₀` and module `M₀`. -/
lemma exists_descended_mvPolynomial_stage_model :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (r : R₀ →+* R) (_ : IsNoetherianRing R₀)
      (P₀ : Type u) (_ : CommRing P₀) (_ : Algebra R₀ P₀) (stageMap : R₀ →+* P₀)
      (_ : Algebra.FinitePresentation R₀ P₀) (targetMap : P₀ →+* P)
      (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module P₀ M₀)
      (_ : Module.FinitePresentation P₀ M₀),
      targetMap.comp stageMap = (algebraMap R P).comp r ∧
        Nonempty
          (let _ : Algebra P₀ P := targetMap.toAlgebra
           P ⊗[P₀] M₀ ≃ₗ[P] M) ∧
        Nonempty
          (let _ : Algebra R₀ R := r.toAlgebra
           let _ : Module R₀ M₀ := Module.compHom M₀ stageMap
           R ⊗[R₀] M₀ ≃ₗ[R] RestrictScalars R P M) := by
  classical
  letI : Algebra.FinitePresentation R P := by
    exact
      Algebra.FinitePresentation.mvPolynomial_of_finitePresentation
        (R := R) (A := R) (Fin n)
  let hfP : (algebraMap R P).FinitePresentation := by
    exact RingHom.finitePresentation_algebraMap.mpr (inferInstance : Algebra.FinitePresentation R P)
  obtain ⟨A⟩ :=
    exists_directedFinitePresentationModuleApproximation
      (f := algebraMap R P) (M := M) hfP
  obtain ⟨i⟩ := A.instNonempty
  -- Proof comment: choose one stage of the canonical finite-presentation approximation of the
  -- polynomial algebra map `R → P`; that stage already keeps both the descended owner algebra and
  -- the descended module needed by the source proof.
  refine ⟨A.RStage i, inferInstance, A.sourceStageToLimit i,
    source_stage_isNoetherian A i, A.SStage i, inferInstance, (A.stageMap i).toAlgebra,
    A.stageMap i,
    RingHom.finitePresentation_algebraMap.mp (stageMap_finitePresentation A i),
    A.targetStageToLimit i, A.moduleStage i, inferInstance,
    inferInstance, stage_module_finitePresentation A i, ?_⟩
  refine ⟨A.targetStageToLimit_comp_stageMap i, ?_, ?_⟩
  · exact ⟨A.finalBaseChange i⟩
  · exact ⟨A.finalBaseChangeSource i⟩

/-- Helper for Lemma 15.21.6: the descended polynomial-stage model can be chosen together with
the original finite-type-over-`ℤ` witness on the source stage. -/
lemma exists_descended_mvPolynomial_stage_model_finiteType :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (r : R₀ →+* R)
      (_ : (Int.castRingHom R₀).FiniteType)
      (P₀ : Type u) (_ : CommRing P₀) (_ : Algebra R₀ P₀) (stageMap : R₀ →+* P₀)
      (_ : Algebra.FinitePresentation R₀ P₀) (targetMap : P₀ →+* P)
      (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module P₀ M₀)
      (_ : Module.FinitePresentation P₀ M₀),
      targetMap.comp stageMap = (algebraMap R P).comp r ∧
        Nonempty
          (let _ : Algebra P₀ P := targetMap.toAlgebra
           P ⊗[P₀] M₀ ≃ₗ[P] M) ∧
        Nonempty
          (let _ : Algebra R₀ R := r.toAlgebra
           let _ : Module R₀ M₀ := Module.compHom M₀ stageMap
           R ⊗[R₀] M₀ ≃ₗ[R] RestrictScalars R P M) := by
  classical
  letI : Algebra.FinitePresentation R P := by
    exact
      Algebra.FinitePresentation.mvPolynomial_of_finitePresentation
        (R := R) (A := R) (Fin n)
  let hfP : (algebraMap R P).FinitePresentation := by
    exact RingHom.finitePresentation_algebraMap.mpr (inferInstance : Algebra.FinitePresentation R P)
  obtain ⟨A⟩ :=
    exists_directedFinitePresentationModuleApproximation
      (f := algebraMap R P) (M := M) hfP
  obtain ⟨i⟩ := A.instNonempty
  -- Proof comment: this is the same descended stage as above, but we now keep the finite-type
  -- witness on the source ring instead of immediately collapsing it to the Noetherian corollary.
  refine ⟨A.RStage i, inferInstance, A.sourceStageToLimit i, A.source_finiteType i,
    A.SStage i, inferInstance, (A.stageMap i).toAlgebra, A.stageMap i,
    RingHom.finitePresentation_algebraMap.mp (stageMap_finitePresentation A i),
    A.targetStageToLimit i, A.moduleStage i, inferInstance, inferInstance,
    stage_module_finitePresentation A i, ?_⟩
  refine ⟨A.targetStageToLimit_comp_stageMap i, ?_, ?_⟩
  · exact ⟨A.finalBaseChange i⟩
  · exact ⟨A.finalBaseChangeSource i⟩

/-- Helper for Lemma 15.21.6: the richer descended polynomial-stage model above still yields the
underlying descended `R₀`-module comparison used by the closing flatness transport. -/
lemma exists_descended_mvPolynomial_base_module_model :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R₀ R) (_ : IsNoetherianRing R₀)
      (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module R₀ M₀),
      Nonempty
        (R ⊗[R₀] M₀ ≃ₗ[R] RestrictScalars R P M) := by
  obtain ⟨R₀, _, r, _, P₀, _, _, stageMap, _, _, M₀, _, _, _, _, _, hsource⟩ :=
    exists_descended_mvPolynomial_stage_model (R := R) (n := n) (M := M)
  -- Proof comment: forget only the owner algebra `P₀`; the source-side comparison survives
  -- unchanged as an `R₀`-module statement.
  refine ⟨R₀, inferInstance, r.toAlgebra, inferInstance, M₀, inferInstance,
    Module.compHom M₀ stageMap, hsource⟩

/-- Helper for Lemma 15.21.6: two finite-type source subalgebras inside `R` admit a common
finite-type upper bound. -/
lemma exists_common_finiteType_subalgebra
    {R₀ : Type*} {R' : Type*} [CommRing R₀] [CommRing R'] [Algebra R₀ R']
    (A B : Subalgebra R₀ R') [Algebra.FiniteType R₀ A] [Algebra.FiniteType R₀ B] :
    ∃ C : Subalgebra R₀ R', Algebra.FiniteType R₀ C ∧ A ≤ C ∧ B ≤ C := by
  have hfgA : A.FG := (Subalgebra.fg_iff_finiteType A).2 inferInstance
  have hfgB : B.FG := (Subalgebra.fg_iff_finiteType B).2 inferInstance
  rcases (Subalgebra.fg_def.mp hfgA) with ⟨sA, hsAfinite, hsAeq⟩
  rcases (Subalgebra.fg_def.mp hfgB) with ⟨sB, hsBfinite, hsBeq⟩
  have hfgSup : (A ⊔ B).FG := by
    refine Subalgebra.fg_def.mpr ?_
    refine ⟨sA ∪ sB, hsAfinite.union hsBfinite, le_antisymm ?_ ?_⟩
    · refine Algebra.adjoin_le ?_
      intro x hx
      rcases hx with hx | hx
      · have hA : x ∈ A := by
          rw [← hsAeq]
          exact Algebra.subset_adjoin hx
        exact (show A ≤ A ⊔ B from le_sup_left) hA
      · have hB : x ∈ B := by
          rw [← hsBeq]
          exact Algebra.subset_adjoin hx
        exact (show B ≤ A ⊔ B from le_sup_right) hB
    · refine sup_le ?_ ?_
      · rw [← hsAeq]
        exact Algebra.adjoin_le fun x hx ↦ Algebra.subset_adjoin (Or.inl hx)
      · rw [← hsBeq]
        exact Algebra.adjoin_le fun x hx ↦ Algebra.subset_adjoin (Or.inr hx)
  -- Proof comment: the join is generated by the union of the two chosen finite generating sets.
  exact ⟨A ⊔ B, (Subalgebra.fg_iff_finiteType (A ⊔ B)).1 hfgSup, le_sup_left, le_sup_right⟩

/-- Helper for Lemma 15.21.6: a literal source-enlargement stage remembers an actual finite-type
source subalgebra of `R` together with a finite target subalgebra of `S` over that source stage.
-/
structure SourceEnlargementStage
    (R₀ : Type*) (R' : Type*) (S' : Type*)
    [CommRing R₀] [CommRing R'] [CommRing S']
    [Algebra R₀ R'] [Algebra R' S'] [Algebra R₀ S'] [IsScalarTower R₀ R' S'] where
  source : Subalgebra R₀ R'
  source_finiteType : Algebra.FiniteType R₀ source
  target : Subalgebra source S'
  target_finite : Module.Finite source target

/-- Helper for Lemma 15.21.6: the source ring of a source-enlargement stage is Noetherian once
the base ring `R₀` is Noetherian. -/
lemma SourceEnlargementStage.source_isNoetherian
    {R₀ : Type*} {R' : Type*} {S' : Type*}
    [CommRing R₀] [CommRing R'] [CommRing S']
    [Algebra R₀ R'] [Algebra R' S'] [Algebra R₀ S'] [IsScalarTower R₀ R' S']
    [IsNoetherianRing R₀]
    (i : SourceEnlargementStage R₀ R' S') :
    IsNoetherianRing i.source := by
  -- Proof comment: finite type over a Noetherian ring is the exact source-side hypothesis needed
  -- later for the finite-stage descent theorem.
  let _ : Algebra.FiniteType R₀ i.source := i.source_finiteType
  exact Algebra.FiniteType.isNoetherianRing R₀ i.source

/-- Helper for Lemma 15.21.6: above any two source-enlargement stages there is a common
finite-type source subalgebra of `R`. -/
lemma exists_common_source_subalgebra_of_source_enlargement
    {R₀ : Type*} {R' : Type*} {S' : Type*}
    [CommRing R₀] [CommRing R'] [CommRing S']
    [Algebra R₀ R'] [Algebra R' S'] [Algebra R₀ S'] [IsScalarTower R₀ R' S']
    (i j : SourceEnlargementStage R₀ R' S') :
    ∃ C : Subalgebra R₀ R', Algebra.FiniteType R₀ C ∧ i.source ≤ C ∧ j.source ≤ C := by
  -- Proof comment: the source side is directed by taking joins of finite-type subalgebras.
  let _ : Algebra.FiniteType R₀ i.source := i.source_finiteType
  let _ : Algebra.FiniteType R₀ j.source := j.source_finiteType
  exact
    exists_common_finiteType_subalgebra
      (R₀ := R₀) (R' := R') i.source j.source

/-- Helper for Lemma 15.21.6: once the source stage is fixed, any finite set of target elements
integral over that source stage is contained in a finite target subalgebra. -/
lemma SourceEnlargementStage.exists_target_subalgebra_containing_finset
    {R₀ : Type*} {R' : Type*} {S' : Type*}
    [CommRing R₀] [CommRing R'] [CommRing S']
    [Algebra R₀ R'] [Algebra R' S'] [Algebra R₀ S'] [IsScalarTower R₀ R' S']
    (i : SourceEnlargementStage R₀ R' S') (t : Finset S')
    (hInt : ∀ x ∈ (t : Set S'), IsIntegral i.source x) :
    ∃ T : Subalgebra i.source S', Module.Finite i.source T ∧ (↑t : Set S') ⊆ T := by
  -- Proof comment: this is the target-side finite capture step that will be used to enlarge a
  -- stage so that finitely many chosen target elements already live in one finite subalgebra.
  simpa using
    (forall_isIntegral_iff_exists_subalgebra_finite_containing
      (R := i.source) (S := S') (s := (↑t : Set S')) t.finite_toSet).1 hInt

/-- Helper for Lemma 15.21.6: base change flatness from a descended stage and then transport it
across a comparison linear equivalence. -/
lemma flat_target_of_flat_stage_baseChange
    {R₀ : Type*} {R' : Type*} [CommRing R₀] [CommRing R'] [Algebra R₀ R']
    {M₀ : Type*} [AddCommGroup M₀] [Module R₀ M₀]
    {N : Type*} [AddCommGroup N] [Module R' N]
    (hflat : Module.Flat R₀ M₀)
    (e : R' ⊗[R₀] M₀ ≃ₗ[R'] N) :
    Module.Flat R' N := by
  -- First base change the flat stage module from `R₀` to `R'`.
  letI : Module.Flat R₀ M₀ := hflat
  letI : Module.Flat R' (R' ⊗[R₀] M₀) := by
    simpa using (Module.Flat.baseChange (R := R₀) (S := R') (M := M₀))
  -- Then transport flatness across the comparison equivalence.
  exact Module.Flat.of_linearEquiv e.symm

/-- Helper for Lemma 15.21.6: once a descended source model base-changes back to `M`, the given
`S`-flatness transports to flatness of the descended tensor module over `S`. -/
lemma flat_tensorProduct_of_descended_base_model
    {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
    {M₀ : Type*} [AddCommGroup M₀] [Module R₀ M₀]
    (e : R ⊗[R₀] M₀ ≃ₗ[R] RestrictScalars R P M)
    (hflat : Module.Flat S (S ⊗[R] RestrictScalars R P M)) :
    Module.Flat S (S ⊗[R₀] M₀) := by
  let eTensor :
      S ⊗[R] (R ⊗[R₀] M₀) ≃ₗ[S] S ⊗[R] RestrictScalars R P M :=
    LinearEquiv.baseChange R S (R ⊗[R₀] M₀) (RestrictScalars R P M) e
  let eCancel :
      S ⊗[R] (R ⊗[R₀] M₀) ≃ₗ[S] S ⊗[R₀] M₀ :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R₀ R S S M₀
  let _ : Module.Flat S (S ⊗[R] RestrictScalars R P M) := by
    exact hflat
  -- Proof comment: rewrite the given tensor module through the descended comparison, then cancel
  -- the intermediate base change `R₀ → R → S`.
  exact Module.Flat.of_linearEquiv (eCancel.symm.trans eTensor)

/-- Helper for Lemma 15.21.6: once a descended `R₀`-module model is fixed and its tensor product
with `S` is flat, the remaining missing step is the textbook source enlargement producing one
finite injective stage inside `S`. -/
lemma exists_source_enlargement_finite_integral_flat_stage
    {R₀ : Type u} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
    [IsNoetherianRing R₀]
    {M₀ : Type w} [AddCommGroup M₀] [Module R₀ M₀]
    (e : R ⊗[R₀] M₀ ≃ₗ[R] RestrictScalars R P M)
    (hflatDesc : Module.Flat S (S ⊗[R₀] M₀))
    (hinj : Function.Injective (algebraMap R S)) :
    ∃ (R₁ : Type u) (_ : CommRing R₁) (_ : Algebra R₁ R) (_ : IsNoetherianRing R₁)
      (S₁ : Type v) (_ : CommRing S₁) (_ : Algebra R₁ S₁) (_ : Module.Finite R₁ S₁)
      (hinj₁ : Function.Injective (algebraMap R₁ S₁))
      (M₁ : Type w) (_ : AddCommGroup M₁) (_ : Module R₁ M₁),
      Module.Flat S₁ (S₁ ⊗[R₁] M₁) ∧
        Nonempty (R ⊗[R₁] M₁ ≃ₗ[R] RestrictScalars R P M) := by
  let _ : Module.Flat S (S ⊗[R₀] M₀) := hflatDesc
  let _ := e
  let _ := hinj
  -- Route correction: the missing step is no longer hidden inside the outer wrapper. We now need
  -- exactly the source-faithful enlargement promised by the plan: enlarge `R₀` inside `R` so that
  -- finitely many integral equations for one flat finite target stage of `S` already live over the
  -- enlarged source ring, then apply `15.21.5` at that finite injective stage.
  -- TODO: the remaining missing object is the concrete approximation from the plan: build the
  -- directed family of actual source enlargements `R₁ ⊆ R` and finite target stages `S₁ ⊆ S`,
  -- use `exists_common_finite_subalgebra_of_isIntegral` for directed upper bounds, package the
  -- frozen descended model `(R₀, M₀)` as stage modules `S₁ ⊗[R₁] (R₁ ⊗[R₀] M₀)`, and then apply
  -- `eventually_flat_stageModules_of_flat_limit` to extract one flat finite injective stage.
  sorry

/-- Helper for Lemma 15.21.6: the canonical map from a finite adjoin stage into the ambient ring
is injective because the stage is a subalgebra of the target. -/
lemma finite_adjoin_stage_to_target_injective
    {R₀ : Type*} {S' : Type*} [CommRing R₀] [CommRing S'] [Algebra R₀ S']
    (t : Finset S') :
    Function.Injective (algebraMap ↥(Algebra.adjoin R₀ (t : Set S')) S') := by
  -- Proof comment: the stage-to-target map is the subtype inclusion on underlying elements.
  intro x y hxy
  exact Subtype.ext hxy

/-- Helper for Lemma 15.21.6: injectivity of the ambient algebra map descends to any finite
adjoin stage inside the target ring. -/
lemma finite_adjoin_stage_injective_of_injective_algebraMap
    {R₀ : Type*} {S' : Type*} [CommRing R₀] [CommRing S'] [Algebra R₀ S']
    (hinj : Function.Injective (algebraMap R₀ S')) (t : Finset S') :
    Function.Injective (algebraMap R₀ ↥(Algebra.adjoin R₀ (t : Set S'))) := by
  intro x y hxy
  apply hinj
  have hxy' := congrArg (fun z : ↥(Algebra.adjoin R₀ (t : Set S')) ↦ (z : S')) hxy
  -- Proof comment: composing with the stage inclusion identifies both composites with the ambient
  -- map `R₀ → S'`.
  exact hxy'

/-- Helper for Lemma 15.21.6: a finite set of integral target elements already lies in a finite
source subalgebra. -/
lemma exists_finite_subalgebra_containing_finset_of_isIntegral
    {R₀ : Type*} {S' : Type*} [CommRing R₀] [CommRing S'] [Algebra R₀ S']
    (t : Finset S') (hInt : ∀ x ∈ (t : Set S'), IsIntegral R₀ x) :
    ∃ T : Subalgebra R₀ S', Module.Finite R₀ T ∧ (↑t : Set S') ⊆ T := by
  -- Proof comment: this is the finite-set form of Lemma `10.36.4`, matching the source proof's
  -- step where finitely many integral coefficients are captured inside one finite stage.
  simpa using
    (forall_isIntegral_iff_exists_subalgebra_finite_containing
      (R := R₀) (S := S') (s := (↑t : Set S')) t.finite_toSet).1 hInt

/-- Helper for Lemma 15.21.6: two finite source stages inside a common ambient algebra are
contained in a common finite source stage. -/
lemma exists_common_finite_subalgebra_of_isIntegral
    {R₀ : Type*} {S' : Type*} [CommRing R₀] [CommRing S'] [Algebra R₀ S']
    (T₁ T₂ : Subalgebra R₀ S') [Module.Finite R₀ T₁] [Module.Finite R₀ T₂] :
    ∃ T₃ : Subalgebra R₀ S', Module.Finite R₀ T₃ ∧ T₁ ≤ T₃ ∧ T₂ ≤ T₃ := by
  classical
  let _ : Algebra.FiniteType R₀ T₁ := inferInstance
  let _ : Algebra.FiniteType R₀ T₂ := inferInstance
  have hfg₁ : T₁.FG := (Subalgebra.fg_iff_finiteType T₁).2 inferInstance
  have hfg₂ : T₂.FG := (Subalgebra.fg_iff_finiteType T₂).2 inferInstance
  rcases (Subalgebra.fg_def.mp hfg₁) with ⟨s₁, hs₁finite, hs₁top⟩
  rcases (Subalgebra.fg_def.mp hfg₂) with ⟨s₂, hs₂finite, hs₂top⟩
  let t : Finset S' := hs₁finite.toFinset ∪ hs₂finite.toFinset
  have hInt : ∀ x ∈ (↑t : Set S'), IsIntegral R₀ x := by
    intro x hx
    have hxFin : x ∈ t := by
      simpa [t] using hx
    rcases Finset.mem_union.mp hxFin with hx₁ | hx₂
    · have hxSet : x ∈ s₁ := hs₁finite.mem_toFinset.mp hx₁
      have hxT₁ : x ∈ T₁ := by
        rw [← hs₁top]
        exact Algebra.subset_adjoin hxSet
      let _ : Algebra.IsIntegral R₀ T₁ := inferInstance
      exact T₁.isIntegral_iff.mp inferInstance x hxT₁
    · have hxSet : x ∈ s₂ := hs₂finite.mem_toFinset.mp hx₂
      have hxT₂ : x ∈ T₂ := by
        rw [← hs₂top]
        exact Algebra.subset_adjoin hxSet
      let _ : Algebra.IsIntegral R₀ T₂ := inferInstance
      exact T₂.isIntegral_iff.mp inferInstance x hxT₂
  obtain ⟨T₃, hT₃finite, ht⟩ :=
    exists_finite_subalgebra_containing_finset_of_isIntegral
      (R₀ := R₀) (S' := S') t hInt
  refine ⟨T₃, hT₃finite, ?_, ?_⟩
  · -- Proof comment: every generator of `T₁` lies in the enlarged finite stage, so the whole
    -- generated subalgebra `T₁` maps into that stage.
    rw [← hs₁top]
    refine Algebra.adjoin_le ?_
    intro x hx
    exact ht <| by
      have hxFin : x ∈ hs₁finite.toFinset := hs₁finite.mem_toFinset.mpr hx
      exact show x ∈ (↑t : Set S') from by
        simpa [t] using Finset.mem_union.mpr (Or.inl hxFin)
  · -- Proof comment: the same generator argument gives the inclusion for `T₂`.
    rw [← hs₂top]
    refine Algebra.adjoin_le ?_
    intro x hx
    exact ht <| by
      have hxFin : x ∈ hs₂finite.toFinset := hs₂finite.mem_toFinset.mpr hx
      exact show x ∈ (↑t : Set S') from by
        simpa [t] using Finset.mem_union.mpr (Or.inr hxFin)

/-- Helper for Lemma 15.21.6: enlarge the source ring of a source-enlargement stage and capture
the old finite target stage inside one finite target subalgebra over the larger source ring. -/
lemma SourceEnlargementStage.exists_target_over_source_superalgebra
    {R₀ : Type*} {R' : Type*} {S' : Type*}
    [CommRing R₀] [CommRing R'] [CommRing S']
    [Algebra R₀ R'] [Algebra R' S'] [Algebra R₀ S'] [IsScalarTower R₀ R' S']
    (i : SourceEnlargementStage R₀ R' S') {C : Subalgebra R₀ R'} (hC : i.source ≤ C) :
    ∃ T : Subalgebra C S', Module.Finite C T ∧ (i.target : Set S') ⊆ T := by
  let _ := hC
  -- TODO: realize `i.target` as generated by finitely many elements integral over the larger
  -- source `C`, then apply `exists_finite_subalgebra_containing_finset_of_isIntegral` over `C`
  -- and compare the resulting `C`-subalgebra with `i.target` via restriction of scalars.
  sorry

/-- Helper for Lemma 15.21.6: source-enlargement stages are ordered by inclusion of their source
subalgebras and inclusion of their target carriers inside `S`. -/
instance SourceEnlargementStage.instLE
    {R₀ : Type*} {R' : Type*} {S' : Type*}
    [CommRing R₀] [CommRing R'] [CommRing S']
    [Algebra R₀ R'] [Algebra R' S'] [Algebra R₀ S'] [IsScalarTower R₀ R' S'] :
    LE (SourceEnlargementStage R₀ R' S') where
  le i j := i.source ≤ j.source ∧ (i.target : Set S') ⊆ j.target

/-- Helper for Lemma 15.21.6: the inclusion order on source-enlargement stages is a preorder. -/
instance SourceEnlargementStage.instPreorder
    {R₀ : Type*} {R' : Type*} {S' : Type*}
    [CommRing R₀] [CommRing R'] [CommRing S']
    [Algebra R₀ R'] [Algebra R' S'] [Algebra R₀ S'] [IsScalarTower R₀ R' S'] :
    Preorder (SourceEnlargementStage R₀ R' S') where
  le_refl := by
    intro i
    exact ⟨le_rfl, Set.Subset.rfl⟩
  le_trans := by
    intro i j k hij hjk
    exact ⟨hij.1.trans hjk.1, Set.Subset.trans hij.2 hjk.2⟩

/-- Helper for Lemma 15.21.6: two source-enlargement stages admit a common upper bound obtained
by first enlarging the source ring and then joining the two finite target stages over that larger
source. -/
lemma source_enlargement_stage_upper_bound
    {R₀ : Type*} {R' : Type*} {S' : Type*}
    [CommRing R₀] [CommRing R'] [CommRing S']
    [Algebra R₀ R'] [Algebra R' S'] [Algebra R₀ S'] [IsScalarTower R₀ R' S']
    (i j : SourceEnlargementStage R₀ R' S') :
    ∃ k : SourceEnlargementStage R₀ R' S', i ≤ k ∧ j ≤ k := by
  -- TODO: first join the two source subalgebras, then apply the previous enlargement lemma to
  -- move both finite target stages over that common source ring, and finally join those finite
  -- target stages over the enlarged source.
  let _ := i
  let _ := j
  sorry

/-- Helper for Lemma 15.21.6: source-enlargement stages form a directed preorder under literal
inclusion. -/
instance SourceEnlargementStage.instDirectedOrder
    {R₀ : Type*} {R' : Type*} {S' : Type*}
    [CommRing R₀] [CommRing R'] [CommRing S']
    [Algebra R₀ R'] [Algebra R' S'] [Algebra R₀ S'] [IsScalarTower R₀ R' S'] :
    IsDirectedOrder (SourceEnlargementStage R₀ R' S') where
  directed i j := source_enlargement_stage_upper_bound i j

/-- Helper for Lemma 15.21.6: the source proof spreads the finitely presented polynomial module to
one finite integral stage whose stage tensor module is already flat and whose base change back to
`R` recovers the original restricted-scalar module. -/
lemma exists_finite_integral_flat_stage_model
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] RestrictScalars R P M)) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R₀ R) (_ : IsNoetherianRing R₀)
      (S₀ : Type v) (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : Module.Finite R₀ S₀)
      (hinj₀ : Function.Injective (algebraMap R₀ S₀))
      (M₀ : Type w) (_ : AddCommGroup M₀) (_ : Module R₀ M₀),
      Module.Flat S₀ (S₀ ⊗[R₀] M₀) ∧
        Nonempty (R ⊗[R₀] M₀ ≃ₗ[R] RestrictScalars R P M) := by
  obtain ⟨R₀, _, r, hR₀finiteType, P₀, _, _, stageMap, _, targetMap, M₀, _, _, _,
    htargetMap, _, hsource⟩ :=
    exists_descended_mvPolynomial_stage_model_finiteType (R := R) (n := n) (M := M)
  let _ : Algebra ℤ R₀ := (Int.castRingHom R₀).toAlgebra
  let _ : Algebra.FiniteType ℤ R₀ := hR₀finiteType
  let _ : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  let _ : Algebra R₀ R := r.toAlgebra
  let _ : Algebra P₀ P := targetMap.toAlgebra
  let _ : Module R₀ M₀ := Module.compHom M₀ stageMap
  obtain ⟨e⟩ := hsource
  let _ := htargetMap
  let _ : Algebra R₀ S := (RingHom.comp (algebraMap R S) (algebraMap R₀ R)).toAlgebra
  let _ : IsScalarTower R₀ R S := IsScalarTower.of_algebraMap_eq' rfl
  have hflatDesc : Module.Flat S (S ⊗[R₀] M₀) :=
    flat_tensorProduct_of_descended_base_model
      (R := R) (S := S) (n := n) (M := M) (R₀ := R₀) (M₀ := M₀) e hflat
  -- Proof comment: the descended base-module model and tensor-flatness transport are now closed,
  -- so the outer existential packaging reduces to the single source-enlargement lemma above.
  exact
    exists_source_enlargement_finite_integral_flat_stage
      (R := R) (S := S) (n := n) (M := M) (R₀ := R₀) (M₀ := M₀) e hflatDesc hinj

/-- Lemma 15.21.6: let `R → S` be an injective integral ring map, and let `M` be a finitely
presented `P`-module, where `P = R[x₁, …, xₙ]` is formalized by `MvPolynomial (Fin n) R`.
If the base change `S ⊗[R] (RestrictScalars R P M)` is flat over `S`, then the restricted
`R`-module `RestrictScalars R P M` is flat over `R`. -/
@[stacks 0534]
theorem flat_of_injective_algebraMap_of_isIntegral_of_flat_tensorProduct_of_finitePresentation_mvPolynomial
    (hinj : Function.Injective (algebraMap R S))
    (hflat : Module.Flat S (S ⊗[R] RestrictScalars R P M)) :
    Module.Flat R (RestrictScalars R P M) := by
  -- Route correction: the source-faithful proof is now isolated to two structural inputs:
  -- one finite injective stage carrying the descended flat model, and the comparison identifying
  -- its base change with the original module over `R`. The actual closing steps after that stage
  -- are already packaged in `flat_of_flat_finite_integral_stage` and
  -- `flat_target_of_flat_stage_baseChange`.
  obtain ⟨R₀, _, _, _, S₀, _, _, _, hinj₀, M₀, _, _, hflat₀, hcomp⟩ :=
    exists_finite_integral_flat_stage_model (R := R) (S := S) (n := n) (M := M) hinj hflat
  obtain ⟨e⟩ := hcomp
  -- First descend flatness from the finite injective stage back to its source ring, and then
  -- base change that flat stage to `R` and transport along the comparison with the restricted
  -- `R`-module.
  let _ : Module R M := Module.compHom M (algebraMap R P)
  exact
    flat_target_of_flat_stage_baseChange
      (R₀ := R₀) (R' := R) (M₀ := M₀) (N := M)
      (flat_of_flat_finite_integral_stage (R₀ := R₀) (S₀ := S₀) (M₀ := M₀) hinj₀ hflat₀) e

end
