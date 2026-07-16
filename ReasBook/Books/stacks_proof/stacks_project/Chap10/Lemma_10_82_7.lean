import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.ShortComplex
open LinearMap

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{max u v} R)}

/-- Helper for Lemma 10.82.7: universal exactness makes every right tensor map by `S.f`
injective. -/
lemma rTensor_f_injective_of_universallyExact (hS : UniversallyExact S)
    (Q : Type (max u v)) [AddCommGroup Q] [Module R Q] :
    Function.Injective (S.f.hom.rTensor Q) := by
  -- This is exactly the universal injectivity built into `UniversallyExact`.
  exact hS.universallyInjective_f Q inferInstance inferInstance

/-- Helper for Lemma 10.82.7: if the middle term of a universally exact short complex is flat, then
the left term is flat. -/
lemma flat_left_term_of_universallyExact [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₁ := by
  -- Use the left-tensor flatness criterion so the source square matches the universally exact rows.
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ i hi
  have hNInj : Function.Injective (S.f.hom.rTensor N) :=
    rTensor_f_injective_of_universallyExact hS N
  have hMidInj : Function.Injective (i.lTensor S.X₂) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  -- Apply `S.f ⊗ P` to the proposed equality, then use injectivity in the middle and on the left.
  intro x y hxy
  have hxComm :
      (i.lTensor S.X₂) ((S.f.hom.rTensor N) x) =
        (S.f.hom.rTensor P) ((i.lTensor S.X₁) x) := by
    calc
      (i.lTensor S.X₂) ((S.f.hom.rTensor N) x)
          = TensorProduct.map S.f.hom i x := by
              simpa only [LinearMap.comp_apply] using
                DFunLike.congr_fun
                  (LinearMap.lTensor_comp_rTensor (f := S.f.hom) (g := i)) x
      _ = (S.f.hom.rTensor P) ((i.lTensor S.X₁) x) := by
            simpa only [LinearMap.comp_apply] using
              (DFunLike.congr_fun
                (LinearMap.rTensor_comp_lTensor (f := S.f.hom) (g := i)) x).symm
  have hyComm :
      (i.lTensor S.X₂) ((S.f.hom.rTensor N) y) =
        (S.f.hom.rTensor P) ((i.lTensor S.X₁) y) := by
    calc
      (i.lTensor S.X₂) ((S.f.hom.rTensor N) y)
          = TensorProduct.map S.f.hom i y := by
              simpa only [LinearMap.comp_apply] using
                DFunLike.congr_fun
                  (LinearMap.lTensor_comp_rTensor (f := S.f.hom) (g := i)) y
      _ = (S.f.hom.rTensor P) ((i.lTensor S.X₁) y) := by
            simpa only [LinearMap.comp_apply] using
              (DFunLike.congr_fun
                (LinearMap.rTensor_comp_lTensor (f := S.f.hom) (g := i)) y).symm
  exact hNInj <| hMidInj <| by
    calc
      (i.lTensor S.X₂) ((S.f.hom.rTensor N) x)
          = (S.f.hom.rTensor P) ((i.lTensor S.X₁) x) := hxComm
      _ = (S.f.hom.rTensor P) ((i.lTensor S.X₁) y) := by
            rw [hxy]
      _ = (i.lTensor S.X₂) ((S.f.hom.rTensor N) y) := by
            exact hyComm.symm

/-- Helper for Lemma 10.82.7: if the middle term of a universally exact short complex is flat, then
the right term is flat. -/
lemma flat_right_term_of_universallyExact [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₃ := by
  -- Use the tensor-left flatness criterion and chase the quotient diagram attached to an injective
  -- map `i : N → P`, exactly as in the textbook proof.
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ i hi
  let Q : Type (max u v) := P ⧸ LinearMap.range i
  let π : P →ₗ[R] Q := Submodule.mkQ (LinearMap.range i)
  have hExactCol : Function.Exact i π := LinearMap.exact_map_mkQ_range i
  have hSurjCol : Function.Surjective π := Submodule.mkQ_surjective _
  have hExactRow : Function.Exact S.f.hom S.g.hom := by
    simpa using (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.shortExact.exact
  have hSurjRow : Function.Surjective S.g.hom := hS.shortExact.moduleCat_surjective_g
  have hRightInj : Function.Injective (S.f.hom.rTensor Q) :=
    rTensor_f_injective_of_universallyExact hS Q
  have hMiddleInj : Function.Injective (i.lTensor S.X₂) :=
    Module.Flat.lTensor_preserves_injective_linearMap i hi
  -- The standard three-row diagram chase upgrades injectivity from `X₂` to `X₃`.
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    hExactRow hSurjRow hExactCol hSurjCol hRightInj hMiddleInj

-- Proof sketch: apply the owner abstraction `UniversallyExact S`. Its short exactness gives the
-- exact sequence, and its universal injectivity for `S.f` supplies the tensor-injectivity input.
-- Then use the tensor criterion for flatness together with exactness preservation for the flat
-- middle term `S.X₂` to deduce flatness of `S.X₁` and `S.X₃`.
/-- Lemma 10.82.7: if `S : ShortComplex (ModuleCat R)` is universally exact and the middle module
`S.X₂` is flat, then the first and third modules are flat. -/
@[stacks 058P]
theorem flat_X₁_and_X₃_of_universallyExact [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₁ ∧ Module.Flat R S.X₃ := by
  -- First recover flatness of the left term from the universally injective tensor square.
  have hFlatX₁ : Module.Flat R S.X₁ := flat_left_term_of_universallyExact hS
  -- Then tensor the quotient diagram of an injective map and chase exactness to reach the right.
  have hFlatX₃ : Module.Flat R S.X₃ := flat_right_term_of_universallyExact hS
  exact ⟨hFlatX₁, hFlatX₃⟩

/-- In a universally exact short complex of `R`-modules, flatness of the middle term implies
flatness of the first term. -/
theorem UniversallyExact.flat_X₁ [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₁ :=
  (flat_X₁_and_X₃_of_universallyExact hS).1

/-- In a universally exact short complex of `R`-modules, flatness of the middle term implies
flatness of the third term. -/
theorem UniversallyExact.flat_X₃ [Module.Flat R S.X₂] (hS : UniversallyExact S) :
    Module.Flat R S.X₃ :=
  (flat_X₁_and_X₃_of_universallyExact hS).2

end
