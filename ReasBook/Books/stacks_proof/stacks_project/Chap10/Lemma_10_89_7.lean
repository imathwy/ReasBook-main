import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_82_1
import stacks_proof.stacks_project.Chap10.Proposition_10_89_3
import stacks_proof.stacks_project.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w x

namespace Module

section

variable {R : Type u} [CommRing R]
variable {K M C : Type v}
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup C] [Module R C]

/-- Helper for Chap10 Lemma 10 89 7: tensoring a linear map on the left preserves zero after
`TensorProduct.piRightHom`. -/
lemma piRightHom_rTensor_eq_zero (f : K →ₗ[R] M) {A : Type v} {Q : A → Type v}
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] (t : K ⊗[R] (∀ a, Q a))
    (ht : TensorProduct.piRightHom R R K Q t = 0) :
    TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) t) = 0 := by
  -- Compare coordinates after commuting `piRightHom` with `rTensor`.
  ext a
  calc
    TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) t) a
        = f.rTensor (Q a) ((TensorProduct.piRightHom R R K Q t) a) := by
            simpa using congr_fun (piRightHom_rTensor_apply_linear (R := R) (Q := Q) f t) a
    _ = 0 := by
          rw [congr_fun ht a]
          simp

/-- Helper for Chap10 Lemma 10 89 7: universal injectivity reflects zero through
`TensorProduct.piRightHom`. -/
lemma piRightHom_eq_zero_of_rTensor_eq_zero_of_universallyInjective (f : K →ₗ[R] M)
    (hf : LinearMap.UniversallyInjective.{u, v, v, v} f) {A : Type v} {Q : A → Type v}
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] (s : K ⊗[R] (∀ a, Q a))
    (hs : TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) s) = 0) :
    TensorProduct.piRightHom R R K Q s = 0 := by
  -- Prove each coordinate by injecting through the tensor of `f` with that coordinate module.
  ext a
  suffices hvanish : (TensorProduct.piRightHom R R K Q s) a = 0 by
    simpa using hvanish
  apply hf (Q a) inferInstance inferInstance
  have hcoordZero :
      f.rTensor (Q a) ((TensorProduct.piRightHom R R K Q s) a) = 0 := by
    calc
      f.rTensor (Q a) ((TensorProduct.piRightHom R R K Q s) a)
          = TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) s) a := by
              simpa using
                (congr_fun (piRightHom_rTensor_apply_linear (R := R) (Q := Q) f s) a).symm
      _ = 0 := by simpa using congr_fun hs a
  simpa using hcoordZero

/-- Helper for Chap10 Lemma 10 89 7: a universally injective submodule of a Mittag-Leffler module
is Mittag-Leffler. -/
lemma mittagLeffler_of_universallyInjective_of_mittagLeffler [MittagLeffler R M]
    (f : K →ₗ[R] M) (hf : LinearMap.UniversallyInjective.{u, v, v, v} f) :
    MittagLeffler R K := by
  -- Use the product-tensor injectivity criterion and compare after tensoring with `f`.
  refine (Module.mittagLeffler_iff_tensorProduct_piRight_injective.{u, v, v, v}
    (R := R) (M := K)).2 ?_
  intro A Q _ _ x y hxy
  apply hf (∀ a, Q a) inferInstance inferInstance
  have hM : Function.Injective (TensorProduct.piRightHom R R M Q) :=
    (Module.mittagLeffler_iff_tensorProduct_piRight_injective.{u, v, v, v}
      (R := R) (M := M)).1 (inferInstance : MittagLeffler R M) A Q
  apply hM
  ext a
  calc
    TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) x) a
        = f.rTensor (Q a) ((TensorProduct.piRightHom R R K Q x) a) := by
            simpa using congr_fun (piRightHom_rTensor_apply_linear (R := R) (Q := Q) f x) a
    _ = f.rTensor (Q a) ((TensorProduct.piRightHom R R K Q y) a) := by
          rw [congr_fun hxy a]
    _ = TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) y) a := by
          simpa using
            (congr_fun (piRightHom_rTensor_apply_linear (R := R) (Q := Q) f y) a).symm

/-- Helper for Chap10 Lemma 10 89 7: an exact middle term is Mittag-Leffler when its endpoints are
Mittag-Leffler and the first map is universally injective. -/
lemma mittagLeffler_of_exact_of_universallyInjective [MittagLeffler R K] [MittagLeffler R C]
    (f : K →ₗ[R] M) (g : M →ₗ[R] C) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) (hf : LinearMap.UniversallyInjective.{u, v, v, v} f) :
    MittagLeffler R M := by
  -- Work with the injectivity criterion for every product family.
  refine (Module.mittagLeffler_iff_tensorProduct_piRight_injective.{u, v, v, v}
    (R := R) (M := M)).2 ?_
  intro A Q _ _ x y hxy
  suffices hsub : x - y = 0 by
    exact sub_eq_zero.mp hsub
  have hPi : TensorProduct.piRightHom R R M Q (x - y) = 0 := by
    ext a
    simp [map_sub, congr_fun hxy a]
  have hCinj : Function.Injective (TensorProduct.piRightHom R R C Q) :=
    (Module.mittagLeffler_iff_tensorProduct_piRight_injective.{u, v, v, v}
      (R := R) (M := C)).1 (inferInstance : MittagLeffler R C) A Q
  have hgz : g.rTensor (∀ a, Q a) (x - y) = 0 := by
    apply hCinj
    simpa using piRightHom_rTensor_eq_zero (R := R) g (x - y) hPi
  have hTensorExact : Function.Exact (f.rTensor (∀ a, Q a)) (g.rTensor (∀ a, Q a)) :=
    rTensor_exact (∀ a, Q a) hfg hg
  have hzRange : x - y ∈ LinearMap.range (f.rTensor (∀ a, Q a)) := by
    rw [← Function.Exact.linearMap_ker_eq hTensorExact]
    simpa [LinearMap.mem_ker] using hgz
  obtain ⟨s, hs⟩ := hzRange
  have hPiLift : TensorProduct.piRightHom R R M Q (f.rTensor (∀ a, Q a) s) = 0 := by
    rw [hs]
    exact hPi
  have hKPi : TensorProduct.piRightHom R R K Q s = 0 :=
    piRightHom_eq_zero_of_rTensor_eq_zero_of_universallyInjective (R := R) f hf s hPiLift
  have hKinj : Function.Injective (TensorProduct.piRightHom R R K Q) :=
    (Module.mittagLeffler_iff_tensorProduct_piRight_injective.{u, v, v, v}
      (R := R) (M := K)).1 (inferInstance : MittagLeffler R K) A Q
  have hsZero : s = 0 := by
    apply hKinj
    simpa using hKPi
  calc
    x - y = f.rTensor (∀ a, Q a) s := hs.symm
    _ = f.rTensor (∀ a, Q a) 0 := by rw [hsZero]
    _ = 0 := by simp

end

end Module

namespace CategoryTheory.ShortComplex

/- Domain triage:
- primary domain: universally exact short complexes of modules and the owner property
  `Module.MittagLeffler`;
- sampled owner declarations: `CategoryTheory.ShortComplex.UniversallyExact`,
  `Module.mittagLeffler_iff_tensorProduct_piRight_injective`,
  `CategoryTheory.ShortComplex.UniversallyExact.flat_X₁`;
- primitive data vs. derived API: `UniversallyExact S` is the primitive short-complex datum, and
  propagation of the owner property `Module.MittagLeffler` along it is derived API belonging in
  the `UniversallyExact` namespace.
-/

namespace UniversallyExact

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/- Chap10 Lemma 10 89 7: the two public declarations below record the left-term and middle-term
Mittag-Leffler consequences of a universally exact short exact sequence. -/
-- recall CategoryTheory.ShortComplex.UniversallyExact.mittagLeffler_X₁ / CategoryTheory.ShortComplex.UniversallyExact.mittagLeffler_X₂

/-
/-- Validator bridge for Chap10 Lemma 10 89 7: records the two public declarations that
together form the planned main result for this item. -/
theorem CategoryTheory.ShortComplex.UniversallyExact.mittagLeffler_X₁ / CategoryTheory.ShortComplex.UniversallyExact.mittagLeffler_X₂
-/

-- Proof sketch: for every family `(Q α)` of `R`-modules, tensor the universally exact short exact
-- sequence `S` with `∏ α, Q α` and compare it with the product of the tensor sequences. The top
-- horizontal map is injective by universal exactness, and the right vertical map is injective by
-- Proposition `10.89.5` for `S.X₂`, so the left vertical map is injective as well.
/-- First clause for Chap10 Lemma 10 89 7: in a universally exact short exact sequence of
`R`-modules, if the
middle term is Mittag-Leffler, then the left term is Mittag-Leffler. -/
@[stacks 059N]
theorem mittagLeffler_X₁ [Module.MittagLeffler R S.X₂] (hS : UniversallyExact S) :
    Module.MittagLeffler R S.X₁ := by
  -- Descend the product-tensor injectivity criterion along the universally injective first map.
  exact Module.mittagLeffler_of_universallyInjective_of_mittagLeffler S.f.hom
    hS.universallyInjective_f

-- Proof sketch: for every family `(Q α)`, compare the tensor sequence with `∏ α, Q α` to the
-- product of the tensor sequences with each `Q α`. If an element of the middle tensor maps to zero
-- in the product, its image in the right tensor also maps to zero, hence vanishes by
-- Mittag-Leffler for `S.X₃`. Exactness of the tensor sequence lifts it from the left tensor, and
-- injectivity on the left term from universal exactness plus Mittag-Leffler for `S.X₁` forces the
-- original element to vanish.
/-- Second clause for Chap10 Lemma 10 89 7: in a universally exact short exact sequence of
`R`-modules, if the left and right terms are Mittag-Leffler, then the middle term is
Mittag-Leffler. -/
@[stacks 059N]
theorem mittagLeffler_X₂ [Module.MittagLeffler R S.X₁] [Module.MittagLeffler R S.X₃]
    (hS : UniversallyExact S) : Module.MittagLeffler R S.X₂ := by
  -- Convert universal exactness to a function-exact, surjective pair and apply the tensor chase.
  have hExact : Function.Exact S.f.hom S.g.hom :=
    (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.shortExact.exact
  have hSurj : Function.Surjective S.g.hom := hS.shortExact.moduleCat_surjective_g
  exact Module.mittagLeffler_of_exact_of_universallyInjective S.f.hom S.g.hom hExact hSurj
    hS.universallyInjective_f

end

end UniversallyExact
end CategoryTheory.ShortComplex
