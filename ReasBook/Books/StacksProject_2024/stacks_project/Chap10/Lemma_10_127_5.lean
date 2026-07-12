import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w x y

section

variable {A : Type u} [CommRing A]
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (R : I → Type w) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
variable (f : ∀ i j, i ≤ j → R i →ₐ[A] R j)
variable [DirectedSystem R (fun i j h ↦ (f i j h : R i →+* R j))]

local notation "ρ" => (fun i j h ↦ (f i j h : R i →+* R j))
local notation "R∞" => Ring.DirectLimit R ρ

/-- The directed colimit ring carries its canonical `A`-algebra structure induced from the stage
algebras. -/
noncomputable local instance directLimitAlgebra : Algebra A R∞ :=
  ((Ring.DirectLimit.of R ρ (Classical.arbitrary I)).comp
    (algebraMap A (R (Classical.arbitrary I)))).toAlgebra

-- Proof sketch: compare the auxiliary stage used to define the local `A`-algebra structure with
-- any fixed stage `i` inside a common upper bound of the directed system, then use
-- `Ring.DirectLimit.of_f` together with the fact that the transition maps are `A`-algebra maps.
/-- The canonical `A`-algebra map to the directed colimit agrees with the map induced from any
stage. -/
private theorem algebraMap_directLimit_eq_of (i : I) (a : A) :
    algebraMap A R∞ a = Ring.DirectLimit.of R ρ i (algebraMap A (R i) a) := by
  classical
  let i₀ : I := Classical.arbitrary I
  rcases exists_ge_ge i₀ i with ⟨j, hi₀j, hij⟩
  change Ring.DirectLimit.of R ρ i₀ (algebraMap A (R i₀) a) =
    Ring.DirectLimit.of R ρ i (algebraMap A (R i) a)
  calc
    Ring.DirectLimit.of R ρ i₀ (algebraMap A (R i₀) a) =
        Ring.DirectLimit.of R ρ j ((f i₀ j hi₀j) (algebraMap A (R i₀) a)) := by
          symm
          exact Ring.DirectLimit.of_f hi₀j (algebraMap A (R i₀) a)
    _ = Ring.DirectLimit.of R ρ j (algebraMap A (R j) a) := by
          rw [(f i₀ j hi₀j).commutes]
    _ = Ring.DirectLimit.of R ρ j ((f i j hij) (algebraMap A (R i) a)) := by
          rw [← (f i j hij).commutes]
    _ = Ring.DirectLimit.of R ρ i (algebraMap A (R i) a) := by
          exact Ring.DirectLimit.of_f hij (algebraMap A (R i) a)

/-- The canonical algebra map from a stage to the directed colimit ring. -/
noncomputable local instance stageToDirectLimitAlgebra (i : I) : Algebra (R i) R∞ :=
  (Ring.DirectLimit.of R ρ i).toAlgebra

/-- The canonical stage-to-colimit algebra map is compatible with the ambient `A`-algebra
structures. -/
local instance stageToDirectLimit_isScalarTower (i : I) : IsScalarTower A (R i) R∞ :=
  IsScalarTower.of_algebraMap_eq' <| by
    ext a
    exact algebraMap_directLimit_eq_of R f i a

variable {M : Type x} [AddCommGroup M] [Module A M]
variable {N : Type y} [AddCommGroup N] [Module A N]

-- Proof sketch: choose finitely many generators of `M`; equality after tensoring to the direct
-- limit means the images of those generators agree in a direct limit module, hence already agree in
-- some stage, which forces equality of the whole base-changed maps there.
/-- Lemma 10.127.5 (1): if two maps from a finite `A`-module become equal after base change to
the directed colimit, then they already become equal after base change to some stage. -/
theorem baseChange_eventually_eq_of_finite [Module.Finite A M] (u u' : M →ₗ[A] N)
    (h : u.baseChange R∞ = u'.baseChange R∞) :
    ∃ i : I, u.baseChange (R i) = u'.baseChange (R i) := sorry

-- Proof sketch: choose finitely many generators of `N`; surjectivity after tensoring to the direct
-- limit gives preimages for these generators in the direct limit, and finitely many such preimages
-- all come from one stage, where they already witness surjectivity.
/-- Lemma 10.127.5 (2): if the base change of `u` to the directed colimit is surjective and `N`
is finite, then the base change of `u` is already surjective at some stage. -/
theorem baseChange_eventually_surjective_of_finite [Module.Finite A N] (u : M →ₗ[A] N)
    (h : Function.Surjective (u.baseChange R∞)) :
    ∃ i : I, Function.Surjective (u.baseChange (R i)) := sorry

-- Proof sketch: identify an `R∞`-linear map `R∞ ⊗[A] N → R∞ ⊗[A] M` with the corresponding
-- `A`-linear map `N → R∞ ⊗[A] M`; finite presentation of `N` implies that such an `A`-linear map
-- factors through one stage of the directed system, and the stage factor then reassembles into the
-- desired base-changed linear map.
/-- Lemma 10.127.5 (3): if `N` is finitely presented, then any `R∞`-linear map
`R∞ ⊗[A] N → R∞ ⊗[A] M` descends from some stage of the directed system. -/
theorem baseChangeLinearMap_descends_of_finitePresentation [Module.FinitePresentation A N]
    (v : R∞ ⊗[A] N →ₗ[R∞] R∞ ⊗[A] M) :
    ∃ i : I,
      ∃ v_i : R i ⊗[A] N →ₗ[R i] R i ⊗[A] M,
        (cancelBaseChange A (R i) R∞ R∞ M).toLinearMap ∘ₗ
            v_i.baseChange R∞ ∘ₗ
            (cancelBaseChange A (R i) R∞ R∞ N).symm.toLinearMap =
          v := sorry

-- Proof sketch: take an inverse to the base-changed map over the direct colimit, descend that
-- inverse to a stage using part (3), and then use part (1) on the two composites with the identity
-- maps to enlarge once more until both inverse identities already hold at a finite stage.
/-- Lemma 10.127.5 (4): if `M` is finite, `N` is finitely presented, and the base change of `u`
to the directed colimit is bijective, then the base change of `u` is already bijective at some
stage. -/
theorem baseChange_eventually_bijective_of_finite_of_finitePresentation
    [Module.Finite A M] [Module.FinitePresentation A N] (u : M →ₗ[A] N)
    (h : Function.Bijective (u.baseChange R∞)) :
    ∃ i : I, Function.Bijective (u.baseChange (R i)) := sorry

end
