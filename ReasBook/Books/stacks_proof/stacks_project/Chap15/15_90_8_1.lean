import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_24_1
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

universe u v

local notation "Away" => LocalizedModule.Away

section

variable {R : Type u} [CommRing R]
variable {ι : Type v}

/- Domain-style sampling for the formal glueing complex:
- primary domain: degree-zero formal glueing for modules, combining tensor base change with the
  canonical away-localization compatibility sequence on a principal-open family;
- sampled owner declarations:
  `awayLocalizationFamilyMap`,
  `awayLocalizationCompatibilityMap`,
  `ShortComplex.moduleCatMk`;
- best owner abstraction: the chapter-local away-localization family and compatibility maps from
  `Lemma_10_24_1`; the formal glueing complex here is the source-facing bridge obtained by adjoining
  the tensor-product term;
- primitive data: the canonical tensor map `M → S ⊗[R] M` and the canonical away-localization
  family map `M → ∀ i, M_(fᵢ)`;
- derived API: the formal glueing map `β`, its vanishing composite with `α`, and the resulting
  short complex.
-/

private noncomputable def overlapFamilyProdIndexLinearEquiv
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ((i : ι) → (j : ι) → Away (f i * f j) M) ≃ₗ[R]
      ((ij : ι × ι) → Away (f ij.1 * f ij.2) M) where
  toFun g ij := g ij.1 ij.2
  invFun g i j := g (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The map `α` in the formal glueing complex, written in the library-facing order
`S ⊗[R] M` for the base-change term. -/
noncomputable def formalGlueingModuleComplexAlpha
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    M →ₗ[R] (S ⊗[R] M) × ((i : ι) → Away (f i) M) :=
  (TensorProduct.mk R S M 1).prod <|
    awayLocalizationFamilyMap M f

/-- The tensor-product part of `β` in the formal glueing complex. -/
private noncomputable def formalGlueingModuleComplexBetaTensorMap
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ((S ⊗[R] M) × ((i : ι) → Away (f i) M)) →ₗ[R]
      ((i : ι) → Away (f i) (S ⊗[R] M)) :=
  LinearMap.pi fun i ↦
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) (S ⊗[R] M)).comp
        (LinearMap.fst R (S ⊗[R] M) ((i : ι) → Away (f i) M))
      -
      ((LocalizedModule.map (Submonoid.powers (f i)) (TensorProduct.mk R S M 1)).restrictScalars R).comp
        ((LinearMap.proj i).comp
          (LinearMap.snd R (S ⊗[R] M) ((i : ι) → Away (f i) M)))

/-- The overlap part of `β` in the formal glueing complex, written through the canonical
away-localization compatibility map from `Lemma_10_24_1`. -/
private noncomputable def formalGlueingModuleComplexBetaOverlapMap
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ((S ⊗[R] M) × ((i : ι) → Away (f i) M)) →ₗ[R]
      ((ij : ι × ι) → Away (f ij.1 * f ij.2) M) :=
  (overlapFamilyProdIndexLinearEquiv f M).toLinearMap.comp <|
    (awayLocalizationCompatibilityMap M f).comp
      (LinearMap.snd R (S ⊗[R] M) ((i : ι) → Away (f i) M))

/-- The map `β` in the formal glueing complex, written with its tensor and overlap components. -/
noncomputable def formalGlueingModuleComplexBeta
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    ((S ⊗[R] M) × ((i : ι) → Away (f i) M)) →ₗ[R]
      (((i : ι) → Away (f i) (S ⊗[R] M)) ×
        ((ij : ι × ι) → Away (f ij.1 * f ij.2) M)) :=
  LinearMap.prod
    (formalGlueingModuleComplexBetaTensorMap S f M)
    (formalGlueingModuleComplexBetaOverlapMap S f M)

-- Proof sketch: on the tensor-product side, localizing `1 ⊗ m` agrees with localizing the image
-- of `m` under base change, so each `i`-component cancels. On the overlap side, both canonical
-- restrictions of `m` to `M_{f_i f_j}` agree, so each difference also vanishes.
/-- Helper for 15.90.8.1: the tensor-localization component of `β (α x)` is zero. -/
private theorem formal_glueing_tensor_component_eq_zero
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) (x : M) (i : ι) :
    (formalGlueingModuleComplexBetaTensorMap S f M
      (formalGlueingModuleComplexAlpha S f M x)) i = 0 := by
  -- Both tensor-side terms are the same canonical localization of `1 ⊗ x`.
  simp [formalGlueingModuleComplexBetaTensorMap, formalGlueingModuleComplexAlpha,
    awayLocalizationFamilyMap]

/-- Helper for 15.90.8.1: the overlap-localization component of `β (α x)` is zero. -/
private theorem formal_glueing_overlap_component_eq_zero
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) (x : M) (ij : ι × ι) :
    (formalGlueingModuleComplexBetaOverlapMap S f M
      (formalGlueingModuleComplexAlpha S f M x)) ij = 0 := by
  rcases ij with ⟨i, j⟩
  -- Both overlap-side restrictions send the canonical section `x / 1` to the same localization.
  simp [formalGlueingModuleComplexBetaOverlapMap, formalGlueingModuleComplexAlpha,
    awayLocalizationFamilyMap, awayLocalizationCompatibilityMap, overlapFamilyProdIndexLinearEquiv]

/-- 15.90.8.1: in the formal glueing module sequence
`0 → M ⟶ S ⊗[R] M × ∏ i, M_{fᵢ} ⟶ ∏ i, (S ⊗[R] M)_{fᵢ} × ∏ (i, j), M_{fᵢ fⱼ}`,
the two nonzero arrows `α` and `β` compose to zero. -/
@[stacks 05EJ]
theorem formalGlueingModuleComplex_comp_eq_zero
    (S : Type u) [CommRing S] [Algebra R S]
    (f : ι → R) (M : ModuleCat.{max u v} R) :
    formalGlueingModuleComplexBeta S f M ∘ₗ formalGlueingModuleComplexAlpha S f M = 0 := by
  apply LinearMap.ext
  intro x
  -- Split the product target into its tensor branch and overlap branch.
  refine Prod.ext ?_ ?_
  · -- Each tensor component is a difference of two identical localizations of `1 ⊗ x`.
    ext i
    exact formal_glueing_tensor_component_eq_zero S f M x i
  · -- Each overlap component compares two identical restrictions of `x`.
    ext ij
    exact formal_glueing_overlap_component_eq_zero S f M x ij

end

section

variable {R : Type u} [CommRing R]
variable {J : Type v}

/-- The formal glueing short complex attached to `M`. -/
noncomputable def formalGlueingModuleComplex
    (S : Type u) [CommRing S] [Algebra R S]
    (f : J → R) (M : ModuleCat.{max u v} R) :
    ShortComplex (ModuleCat.{max u v} R) :=
  let X₂ := (S ⊗[R] M) × ((i : J) → Away (f i) M)
  let X₃ :=
    (((i : J) → Away (f i) (S ⊗[R] M)) ×
      ((ij : J × J) → Away (f ij.1 * f ij.2) M))
  let α : M →ₗ[R] X₂ := formalGlueingModuleComplexAlpha S f M
  let β : X₂ →ₗ[R] X₃ := formalGlueingModuleComplexBeta S f M
  ShortComplex.moduleCatMk α β <| by
    simpa [α, β] using formalGlueingModuleComplex_comp_eq_zero S f M

end
