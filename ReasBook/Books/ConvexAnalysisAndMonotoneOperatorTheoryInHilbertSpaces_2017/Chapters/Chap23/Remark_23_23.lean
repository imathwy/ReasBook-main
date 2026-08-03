import Mathlib.Analysis.InnerProductSpace.ProdL2
import BauschkeLean.Chap09.Proposition_9_18
import BauschkeLean.Chap23.Corollary_23_11
import BauschkeLean.Chap23.Proposition_23_20
import BauschkeLean.Chap23.Proposition_23_22

-- Semantic recall note: `lean_leansearch` surfaced no monotone-operator Minty parameterization
-- API, so this item follows the verified local Chapter 23 owners `resolventMap`,
-- `yosidaApproximationMap`, `J[...]`, and `gra A`. The product metric is the textbook Hilbert
-- direct-sum `ℓ²` metric, so the Lipschitz clauses reuse the Chapter 9 raw-product `ℓ²` bridge
-- rather than Lean's default product max metric.

open scoped Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem resolventYosidaPair_mem_graph_and_reconstruct
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) (x : H) :
    (resolventMap A hA γ x, yosidaApproximationMap A hA γ x) ∈ gra A ∧
      x = resolventMap A hA γ x + (γ : ℝ) • yosidaApproximationMap A hA γ x :=
  (resolvent_yosida_eq_singletons_iff hA.1 γ x
      (resolventMap A hA γ x) (yosidaApproximationMap A hA γ x)).1
    ⟨resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ x,
      yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal A hA γ x⟩

/-- Remark 23.23 (1): for a maximally monotone operator `A`, the pair
`x ↦ (resolventMap A γ x, yosidaApproximationMap A γ x)` defines a graph parameterization
`H ≃ gra A`. -/
noncomputable def resolventYosidaGraphParameterization
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) : H ≃ gra A where
  toFun x :=
    ⟨(resolventMap A hA γ x, yosidaApproximationMap A hA γ x),
      (resolventYosidaPair_mem_graph_and_reconstruct hA γ x).1⟩
  invFun p := p.1.1 + (γ : ℝ) • p.1.2
  left_inv := by
    intro x
    simpa using (resolventYosidaPair_mem_graph_and_reconstruct hA γ x).2.symm
  right_inv := by
    intro p
    let x := p.1.1 + (γ : ℝ) • p.1.2
    apply Subtype.ext
    change
      (resolventMap A hA γ x, yosidaApproximationMap A hA γ x) = p.1
    have hp :
        J[((γ : ℝ) • A)] x = ({p.1.1} : Set H) ∧ ({}^[γ] A) x = ({p.1.2} : Set H) :=
      (resolvent_yosida_eq_singletons_iff hA.1 γ x p.1.1 p.1.2).2 ⟨p.2, rfl⟩
    have hy :
        resolventMap A hA γ x = p.1.1 := by
      apply Set.singleton_injective
      calc
        ({resolventMap A hA γ x} : Set H) = J[((γ : ℝ) • A)] x := by
                symm
                exact resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ x
        _ = ({p.1.1} : Set H) := hp.1
    have hv :
        yosidaApproximationMap A hA γ x = p.1.2 := by
      apply Set.singleton_injective
      calc
        ({yosidaApproximationMap A hA γ x} : Set H) = ({}^[γ] A) x := by
                symm
                exact yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal A hA γ x
        _ = ({p.1.2} : Set H) := hp.2
    exact Prod.ext hy hv

/-- The graph parameterization evaluates to the resolvent/Yosida pair. -/
@[simp] theorem resolventYosidaGraphParameterization_apply
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) (x : H) :
    (resolventYosidaGraphParameterization hA γ x).1 =
      (resolventMap A hA γ x, yosidaApproximationMap A hA γ x) :=
  rfl

/-- The inverse graph map is the explicit affine reconstruction `(y, v) ↦ y + γ • v`. -/
@[simp] theorem resolventYosidaGraphParameterization_symm_apply
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) (p : gra A) :
    (resolventYosidaGraphParameterization hA γ).symm p = p.1.1 + (γ : ℝ) • p.1.2 :=
  rfl

section ProductGraphL2

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_completeSpace_l2 prod_innerProductSpace_l2

/-- The resolvent/Yosida graph parameterization is
`sqrt (1 + ((γ : ℝ)⁻¹)^2)`-Lipschitz for the Chapter 9 raw-product `ℓ²` graph metric on
`gra A ⊆ H × H`. -/
theorem resolventYosidaGraphParameterization_lipschitzWith
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) :
    LipschitzWith (Real.toNNReal (Real.sqrt (1 + ((γ : ℝ)⁻¹)^2)))
      (resolventYosidaGraphParameterization hA γ) := sorry

/-- The inverse graph map `(y, v) ↦ y + γ • v` is
`sqrt (1 + (γ : ℝ)^2)`-Lipschitz for the Chapter 9 raw-product `ℓ²` graph metric on
`gra A ⊆ H × H`. -/
theorem resolventYosidaGraphParameterization_symm_lipschitzWith
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (γ : PosReal) :
    LipschitzWith (Real.toNNReal (Real.sqrt (1 + (γ : ℝ)^2)))
      ((resolventYosidaGraphParameterization hA γ).symm : gra A → H) := sorry

end ProductGraphL2

/-- Remark 23.23 (2): setting `γ = 1` yields the Minty parameterization
`x ↦ (resolventMap A (1 : PosReal) x, resolventMap A⁻¹ (1 : PosReal) x)` of `gra A`. -/
theorem resolventYosidaGraphParameterization_one_apply_eq_minty
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) (x : H) :
    (resolventYosidaGraphParameterization hA (1 : PosReal) x).1 =
      (resolventMap A hA (1 : PosReal) x,
        resolventMap A⁻¹ (Maximal.inverse hA) (1 : PosReal) x) := by
  have hyosida :
      yosidaApproximationMap A hA (1 : PosReal) x =
        resolventMap A⁻¹ (Maximal.inverse hA) (1 : PosReal) x := by
    apply Set.singleton_injective
    calc
      ({yosidaApproximationMap A hA (1 : PosReal) x} : Set H)
          = ({}^[(1 : PosReal)] A) x := by
              symm
              exact
                yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal
                  A hA (1 : PosReal) x
      _ = J[A⁻¹] x := by
            rw [yosidaApproximation_one_eq_resolvent_inverse]
      _ = J[((1 : ℝ) • A⁻¹)] x := by
            simp
      _ = ({resolventMap A⁻¹ (Maximal.inverse hA) (1 : PosReal) x} : Set H) := by
            exact
              resolvent_smul_eq_singleton_resolventMap_of_maximal A⁻¹
                (Maximal.inverse hA) (1 : PosReal) x
  exact Prod.ext rfl hyosida

end SetValuedOperator
