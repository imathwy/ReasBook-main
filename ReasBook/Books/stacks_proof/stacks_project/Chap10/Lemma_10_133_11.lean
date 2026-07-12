import Mathlib
import StacksProject_2024.Chap10.Definition_10_133_1
import StacksProject_2024.Chap10.Lemma_10_133_2
import StacksProject_2024.Chap10.Lemma_10_133_3

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain triage:
* primary domain: relative differential operators on modules over a generated algebra, controlled
  by the scalar-commutator owner predicate;
* sampled owner API:
  `LinearMap.IsDifferentialOperatorOfOrder`,
  `LinearMap.isDifferentialOperatorOfOrder_succ_iff`,
  `LinearMap.isDifferentialOperatorOfOrder_comp`,
  `differential_operators_order_le_submodule`;
* best owner abstraction: the order-`k` differential-operator submodule together with the induced
  subalgebra of scalars whose commutator with `D` has order `k`;
* primitive data: an `A`-linear map `D` and the recursive scalar-commutator condition;
* derived API: the generator criterion below, obtained by proving the good scalars form an
  `A`-subalgebra and then applying `Algebra.adjoin_le`.

Source/core/bridge triage:
* source-facing: the Stacks-project generator criterion for checking order `k + 1`;
* core/canonical: `LinearMap.IsDifferentialOperatorOfOrder` and
  `differential_operators_order_le_submodule`;
* bridge/view: none beyond the internal use of the order-bounded submodule packaging.
-/

universe u

section

variable {A : Type u} {B : Type u} {I : Type u} {M : Type u} {N : Type u}
variable [CommSemiring A] [CommSemiring B] [Algebra A B]
variable [AddCommGroup M] [AddCommGroup N]
variable [Module B M] [Module B N] [Module A M] [Module A N]
variable [IsScalarTower A B M] [IsScalarTower A B N]

namespace LinearMap

-- Proof sketch: let `S` be the set of `g : B` such that `D.scalarCommutator g` has order `k`.
-- Using the commutator formulas for `g + g'` and `g * g'`, together with stability under sums
-- and composition from the differential-operator calculus, `S` is an `A`-subalgebra of `B`.
-- Since `S` contains every generator `g i`, the hypothesis `Algebra.adjoin A (Set.range g) = ⊤`
-- implies `S = ⊤`, so the recursive characterization of order `k + 1` holds for all `g : B`.
/-- Lemma 10.133.11: if `g : I → B` generates `B` as an `A`-algebra, then an `A`-linear map
`D : M → N` is a differential operator of order `k + 1` as soon as each scalar commutator with a
generator `g i` is a differential operator of order `k`. -/
@[stacks 0G35]
theorem isDifferentialOperatorOfOrder_succ_of_generator_scalarCommutator
    (g : I → B) (hgen : Algebra.adjoin A (Set.range g) = ⊤) {D : M →ₗ[A] N} {k : ℕ}
    (hD : ∀ i : I,
      (D.scalarCommutator (g i)).IsDifferentialOperatorOfOrder B k) :
    D.IsDifferentialOperatorOfOrder B (k + 1) := by
  rw [isDifferentialOperatorOfOrder_succ_iff D k]
  let orderLe : Submodule B (M →ₗ[A] N) := differential_operators_order_le_submodule A B M k N
  have lsmul_isDifferentialOperatorOfOrder_zero {P : Type u}
      [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P] (b : B) :
      (Algebra.lsmul A A P b : Module.End A P).IsDifferentialOperatorOfOrder B 0 := by
    rw [isDifferentialOperatorOfOrder_zero_iff]
    intro c m
    simp [smul_smul, mul_comm]
  let good : Subalgebra A B :=
    { carrier := { b | D.scalarCommutator b ∈ orderLe }
      algebraMap_mem' := by
        intro a
        have hcomm : D.scalarCommutator (algebraMap A B a) = 0 := by
          ext m
          simp
        change D.scalarCommutator (algebraMap A B a) ∈ orderLe
        rw [hcomm]
        exact orderLe.zero_mem
      add_mem' := by
        intro x y hx hy
        have hxy : D.scalarCommutator (x + y) = D.scalarCommutator x + D.scalarCommutator y := by
          ext m
          simp [sub_eq_add_neg, add_smul, map_add]
          ac_rfl
        simpa [hxy] using orderLe.add_mem hx hy
      mul_mem' := by
        intro x y hx hy
        have hx' : (D.scalarCommutator x).IsDifferentialOperatorOfOrder B k := hx
        have hy' : (D.scalarCommutator y).IsDifferentialOperatorOfOrder B k := hy
        let Ly : Module.End A M := Algebra.lsmul A A M y
        let Lx : Module.End A N := Algebra.lsmul A A N x
        have hy0 : Ly.IsDifferentialOperatorOfOrder B 0 := by
          simpa [Ly] using lsmul_isDifferentialOperatorOfOrder_zero y
        have hx0 : Lx.IsDifferentialOperatorOfOrder B 0 := by
          simpa [Lx] using lsmul_isDifferentialOperatorOfOrder_zero x
        have hleft : (D.scalarCommutator x).comp (Algebra.lsmul A A M y : Module.End A M) ∈ orderLe := by
          let commx : M →ₗ[A] N := D.scalarCommutator x
          have hcommx : commx.IsDifferentialOperatorOfOrder B k := by
            simpa [commx] using hx'
          have hleft' :
              (commx.comp Ly).IsDifferentialOperatorOfOrder B (0 + k) :=
            isDifferentialOperatorOfOrder_comp hy0 hcommx
          simpa [commx, Ly, zero_add] using
            hleft'
        have hright : (Algebra.lsmul A A N x : Module.End A N).comp (D.scalarCommutator y) ∈ orderLe := by
          let commy : M →ₗ[A] N := D.scalarCommutator y
          have hcommy : commy.IsDifferentialOperatorOfOrder B k := by
            simpa [commy] using hy'
          have hright' :
              (Lx.comp commy).IsDifferentialOperatorOfOrder B (k + 0) :=
            isDifferentialOperatorOfOrder_comp hcommy hx0
          simpa [commy, Lx, Nat.add_zero] using
            hright'
        have hxy :
            D.scalarCommutator (x * y) =
              (D.scalarCommutator x).comp (Algebra.lsmul A A M y : Module.End A M) +
                (Algebra.lsmul A A N x : Module.End A N).comp (D.scalarCommutator y) := by
          ext m
          simp [sub_eq_add_neg, mul_smul]
        simpa [hxy] using orderLe.add_mem hleft hright }
  have hgood : Algebra.adjoin A (Set.range g) ≤ good := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    exact hD i
  have htop : (⊤ : Subalgebra A B) ≤ good := by
    rw [← hgen]
    exact hgood
  intro b
  simpa [good] using htop (show b ∈ (⊤ : Subalgebra A B) from by simp)

end LinearMap

end
