import StacksProject_2024.Chap10.Proposition_10_89_3
import StacksProject_2024.Chap10.Proposition_10_89_5
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Module

section

variable {R : Type u} [CommRing R]

/-- Helper for Chap10 Lemma 10 89 8: in an exact pair `K ⟶ F ⟶ C`, surjectivity of the
left product-tensor comparison and injectivity of the middle comparison imply injectivity of the
right comparison. -/
lemma piRightHom_injective_of_exact_of_left_surjective_of_middle_injective
    {K F C : Type v} [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
    [AddCommGroup C] [Module R C] (κ : K →ₗ[R] F) (π : F →ₗ[R] C)
    (hExact : Function.Exact κ π) (hπ : Function.Surjective π) {A : Type v}
    {Q : A → Type v} [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)]
    (hK : Function.Surjective (TensorProduct.piRightHom R R K Q))
    (hF : Function.Injective (TensorProduct.piRightHom R R F Q)) :
    Function.Injective (TensorProduct.piRightHom R R C Q) := by
  intro t₁ t₂ hEq
  -- Lift the difference in the right tensor to the middle tensor using surjectivity of `π`.
  obtain ⟨u, hu⟩ := LinearMap.rTensor_surjective (∀ a, Q a) hπ (t₁ - t₂)
  have hcoord_zero :
      ∀ a,
        π.rTensor (Q a) ((TensorProduct.piRightHom R R F Q u) a) = 0 := by
    intro a
    calc
      π.rTensor (Q a) ((TensorProduct.piRightHom R R F Q u) a)
          = TensorProduct.piRightHom R R C Q (π.rTensor (∀ a, Q a) u) a := by
              symm
              simpa using congr_fun
                (piRightHom_rTensor_apply_linear (R := R) (Q := Q) π u) a
      _ = TensorProduct.piRightHom R R C Q (t₁ - t₂) a := by rw [hu]
      _ = (TensorProduct.piRightHom R R C Q t₁) a -
            (TensorProduct.piRightHom R R C Q t₂) a := by
              simp
      _ = 0 := by
            simpa using sub_eq_zero.mpr (congr_fun hEq a)
  have hcoord_range :
      ∀ a, (TensorProduct.piRightHom R R F Q u) a ∈
        LinearMap.range (κ.rTensor (Q a)) := by
    intro a
    -- Exactness after tensoring identifies the coordinate kernel with the coordinate range.
    rw [← Function.Exact.linearMap_ker_eq (rTensor_exact (Q a) hExact hπ)]
    simpa [LinearMap.mem_ker] using hcoord_zero a
  classical
  choose z hz using hcoord_range
  obtain ⟨s, hs⟩ := hK z
  have hu_eq : u = κ.rTensor (∀ a, Q a) s := by
    -- The middle comparison map is injective, so coordinatewise equality determines `u`.
    apply hF
    ext a
    calc
      TensorProduct.piRightHom R R F Q u a = κ.rTensor (Q a) (z a) := (hz a).symm
      _ = κ.rTensor (Q a) ((TensorProduct.piRightHom R R K Q s) a) := by rw [hs]
      _ = TensorProduct.piRightHom R R F Q (κ.rTensor (∀ a, Q a) s) a := by
            symm
            simpa using congr_fun
              (piRightHom_rTensor_apply_linear (R := R) (Q := Q) κ s) a
  have hsub : t₁ - t₂ = 0 := by
    -- The lifted difference lies in the image of `κ`, hence maps to zero by exactness.
    calc
      t₁ - t₂ = π.rTensor (∀ a, Q a) u := hu.symm
      _ = π.rTensor (∀ a, Q a) (κ.rTensor (∀ a, Q a) s) := by rw [hu_eq]
      _ = ((π.rTensor (∀ a, Q a)).comp (κ.rTensor (∀ a, Q a))) s := rfl
      _ = ((π.comp κ).rTensor (∀ a, Q a)) s := by
            rw [← LinearMap.rTensor_comp]
      _ = 0 := by
            rw [hExact.linearMap_comp_eq_zero, LinearMap.rTensor_zero, LinearMap.zero_apply]
  exact sub_eq_zero.mp hsub

end

end Module

namespace CategoryTheory.ShortComplex

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

-- Proof sketch: for any family `(Q a)`, tensor the exact sequence `S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` with
-- `∀ a, Q a` and compare it to the product of the exact sequences obtained by tensoring with each
-- `Q a`. Proposition `10.89.2` makes the left vertical map surjective because `S.X₁` is finite,
-- and Proposition `10.89.5` makes the middle vertical map injective because `S.X₂` is
-- Mittag-Leffler. A diagram chase gives injectivity on the right vertical map, and Proposition
-- `10.89.5` then shows that `S.X₃` is Mittag-Leffler.
/-- Chap10 Lemma 10 89 8: if `S : ShortComplex (ModuleCat R)` is exact, `S.g` is surjective,
`S.X₁` is finite, and `S.X₂` is Mittag-Leffler, then `S.X₃` is Mittag-Leffler. -/
@[stacks 0EGI]
theorem mittagLeffler_X₃_of_exact_of_finite_of_mittagLeffler
    (hS : S.Exact) (hSurj : Function.Surjective S.g) [Module.Finite R S.X₁]
    [Module.MittagLeffler R S.X₂] :
    Module.MittagLeffler R S.X₃ := by
  -- Convert categorical exactness to the linear-map exactness used in the tensor chase.
  have hExact : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS
  have hSurjHom : Function.Surjective S.g.hom := by
    simpa using hSurj
  -- Use the Mittag-Leffler product-tensor injectivity criterion for the right term.
  refine (Module.mittagLeffler_iff_tensorProduct_piRight_injective.{u, v, v, v}
    (R := R) (M := S.X₃)).2 ?_
  intro A Q _ _ x y hxy
  have hLeft :
      Function.Surjective (TensorProduct.piRightHom R R S.X₁ Q) :=
    piRightHom_surjective_of_finite_universe_lift (R := R) (N := S.X₁) (A := A) (Q := Q)
  have hMiddle :
      Function.Injective (TensorProduct.piRightHom R R S.X₂ Q) :=
    (Module.mittagLeffler_iff_tensorProduct_piRight_injective.{u, v, v, v}
      (R := R) (M := S.X₂)).1
      (inferInstance : Module.MittagLeffler R S.X₂) A Q
  -- The diagram chase transfers injectivity across the exact, surjective short complex.
  exact Module.piRightHom_injective_of_exact_of_left_surjective_of_middle_injective
    S.f.hom S.g.hom hExact hSurjHom hLeft hMiddle hxy

end

end CategoryTheory.ShortComplex
