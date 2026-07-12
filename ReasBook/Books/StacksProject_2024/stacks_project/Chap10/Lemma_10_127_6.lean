import StacksProject_2024.Chap10.Lemma_10_127_5

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x y

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (R : I → Type v) [∀ i, CommRing (R i)]
variable (f : ∀ i j, i ≤ j → R i →+* R j)
variable [DirectedSystem R (fun i j hij ↦ (f i j hij : R i →+* R j))]

local notation "ρ" => (fun i j hij ↦ (f i j hij : R i →+* R j))
local notation "R∞" => Ring.DirectLimit R ρ

/-!
Domain sampling:
* Primary domain: module descent along directed colimits of commutative rings.
* Sampled owner declarations:
  - `baseChangeLinearMap_descends_of_finitePresentation`
  - `baseChange_eventually_eq_of_finite`
  - the mathlib instance `[Module.FinitePresentation R M] : Module.Finite R M`
* Best owner abstraction: the module-colimit descent API from `Lemma_10_127_5`.
* Layer triage:
  - `source-facing`: the three numbered statements below
  - `core/canonical`: the owner descent theorems from `Lemma_10_127_5`
  - `bridge/view`: the internal tail restriction `j ≥ i`, together with the canonical stage maps
    into `R∞`
* Primitive vs. derived:
  - primitive data here are only the original directed system and its modules over a chosen stage
  - the stage-to-`R∞` scalar-tower compatibility and any tail-system comparison are derived bridge
    data, so they stay local
-/

private noncomputable instance stageDirectLimitAlgebra (i : I) : Algebra (R i) R∞ :=
  (Ring.DirectLimit.of R ρ i).toAlgebra

private theorem directLimitStage_isScalarTower {i j : I} (hij : i ≤ j) :
    let _ : Algebra (R i) (R j) := (f i j hij).toAlgebra
    let _ : Algebra (R j) R∞ := stageDirectLimitAlgebra R f j
    IsScalarTower (R i) (R j) R∞ := sorry

/-- Lemma 10.127.6 (1): every finitely presented module over the directed colimit ring descends to
some stage. -/
-- Proof sketch: choose a finite presentation of `M` over the colimit ring; only finitely many
-- coefficients appear in the presentation matrix, so they all come from one stage `R i`, and the
-- corresponding presentation over `R i` yields a finitely presented module whose base change to
-- the colimit ring is linearly equivalent to `M`.
theorem finitelyPresented_module_descends_to_stage
    {M : Type x} [AddCommGroup M] [Module R∞ M] [Module.FinitePresentation R∞ M] :
    ∃ (i : I) (M_i : Type y) (_ : AddCommGroup M_i) (_ : Module (R i) M_i)
      (_ : Module.FinitePresentation (R i) M_i),
      Nonempty (R∞ ⊗[R i] M_i ≃ₗ[R∞] M) := sorry

/-- Lemma 10.127.6 (2): for a fixed stage `i`, a morphism between the base changes of finitely
presented `R_i`-modules to the colimit ring `R∞` descends after base change from some later stage
`R_j`. -/
-- Proof sketch: specialize `baseChangeLinearMap_descends_of_finitePresentation` from
-- `Lemma_10_127_5` to the restricted tail system `j ≥ i`, then transport the result across the
-- canonical identification of that tail colimit with `R∞`. The owner theorem already packages the
-- descended map using the canonical `cancelBaseChange` comparison. It only needs finite
-- presentation of the source module `M_i`.
theorem finitelyPresented_baseChange_map_descends
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
      [Module.FinitePresentation (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (φ : R∞ ⊗[R i] M_i →ₗ[R∞] R∞ ⊗[R i] N_i) :
    ∃ (j : I) (hij : i ≤ j)
      (φ_j : let _ : Algebra (R i) (R j) := (f i j hij).toAlgebra
        R j ⊗[R i] M_i →ₗ[R j] R j ⊗[R i] N_i),
      let _ : Algebra (R i) (R j) := (f i j hij).toAlgebra
      let _ : Algebra (R j) R∞ := stageDirectLimitAlgebra R f j
      let _ : IsScalarTower (R i) (R j) R∞ := directLimitStage_isScalarTower R f hij
      (cancelBaseChange (R i) (R j) R∞ R∞ N_i).toLinearMap ∘ₗ
          φ_j.baseChange R∞ ∘ₗ
            (cancelBaseChange (R i) (R j) R∞ R∞ M_i).symm.toLinearMap =
        φ := sorry

/-- Lemma 10.127.6 (3): for a fixed stage `i`, if two maps between finitely presented
`R_i`-modules become equal after base change to the colimit ring `R∞`, then they already become
equal after base change to some later stage. -/
-- Proof sketch: `Module.FinitePresentation` on `M_i` gives `Module.Finite`, so apply
-- `baseChange_eventually_eq_of_finite` from `Lemma_10_127_5` to the restricted tail system
-- `j ≥ i` and transport the resulting stage equality back along the canonical comparison with
-- `R∞`. No finite-presentation hypothesis on the target `N_i` is needed.
theorem finitelyPresented_baseChange_map_eventually_eq
    (i : I)
    {M_i : Type x} [AddCommGroup M_i] [Module (R i) M_i]
      [Module.FinitePresentation (R i) M_i]
    {N_i : Type y} [AddCommGroup N_i] [Module (R i) N_i]
    (φ_i ψ_i : M_i →ₗ[R i] N_i)
    (h : φ_i.baseChange R∞ = ψ_i.baseChange R∞) :
    ∃ (j : I) (hij : i ≤ j),
      let _ : Algebra (R i) (R j) := (f i j hij).toAlgebra
      φ_i.baseChange (R j) = ψ_i.baseChange (R j) := sorry

end
