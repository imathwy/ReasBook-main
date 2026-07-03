import Mathlib
import Serre.Chap06.Proposition_6_6_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra

universe u

section

variable (k : Type*) [CommSemiring k]
variable {G : Type u} [Group G] [Finite G]

/-- The class sum in `k[G]` attached to a conjugacy class, obtained from its indicator function. -/
noncomputable def conjugacyClassSum (c : ConjClasses G) : k[G] :=
  Finsupp.equivFunOnFinite.symm c.indicator

@[simp] theorem conjugacyClassSum_apply (c : ConjClasses G) (g : G) :
    conjugacyClassSum k c g = (c.indicator : G → k) g := by
  rfl

/-- A class function defines a central element of `k[G]`. -/
theorem mem_center_of_classFunction (f : classFunctionSubmodule k G) :
    Finsupp.equivFunOnFinite.symm (f : G → k) ∈ Subalgebra.center k (k[G]) := by
  have hf : IsClassFunction (f : G → k) := by
    exact (mem_classFunctionSubmodule_iff k _).1 f.2
  set z : k[G] := Finsupp.equivFunOnFinite.symm (f : G → k)
  change z ∈ Subsemiring.center k[G]
  rw [Subsemiring.mem_center_iff]
  intro y
  ext h
  rw [MonoidAlgebra.mul_apply_left, MonoidAlgebra.mul_apply_right]
  rw [Finsupp.sum, Finsupp.sum]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have hcomm : (f : G → k) (a⁻¹ * h) = (f : G → k) (h * a⁻¹) :=
    hf.map_mul_comm a⁻¹ h
  simpa [z, mul_comm] using congrArg (fun t : k ↦ y a * t) hcomm

/-- Each conjugacy-class sum lies in the center of `k[G]`. -/
theorem conjugacyClassSum_mem_center (c : ConjClasses G) :
    conjugacyClassSum k c ∈ Subalgebra.center k (k[G]) :=
  mem_center_of_classFunction k
    ⟨c.indicator, (mem_classFunctionSubmodule_iff k _).2 inferInstance⟩

/-- The conjugacy-class sum attached to `c`, regarded as an element of the center of `k[G]`. -/
noncomputable abbrev conjugacyClassSumInCenter (c : ConjClasses G) :
    Subalgebra.center k (k[G]) :=
  ⟨conjugacyClassSum k c, conjugacyClassSum_mem_center k c⟩

@[simp] theorem coe_conjugacyClassSumInCenter (c : ConjClasses G) :
    (conjugacyClassSumInCenter k c : k[G]) = conjugacyClassSum k c :=
  rfl

/-- The coefficient-function map identifies the center of `k[G]` with the `k`-module of
class functions on `G`. -/
noncomputable def centerClassFunctionEquiv :
    Subalgebra.center k (k[G]) ≃ₗ[k] classFunctionSubmodule k G where
  toFun u :=
    ⟨fun g ↦ (u : k[G]) g, Representation.coeff_isClassFunction_of_mem_center u⟩
  invFun f :=
    ⟨Finsupp.equivFunOnFinite.symm (f : G → k), mem_center_of_classFunction k f⟩
  left_inv u := by
    ext g
    simp
  right_inv f := by
    ext g
    simp
  map_add' u v := by
    ext g
    rfl
  map_smul' n u := by
    ext g
    rfl

/-- The center of `k[G]` is canonically identified with `k`-valued functions on the conjugacy
classes of `G`. -/
noncomputable def centerCoeffEquivFun :
    Subalgebra.center k (k[G]) ≃ₗ[k] (ConjClasses G → k) :=
  (centerClassFunctionEquiv k).trans (classFunctionSubmodule.equivFun k G)

@[simp] theorem centerCoeffEquivFun_apply_mk
    (u : Subalgebra.center k (k[G])) (g : G) :
    centerCoeffEquivFun k u (ConjClasses.mk g) = (u : k[G]) g := by
  rfl

@[simp] theorem centerCoeffEquivFun_conjugacyClassSumInCenter_apply_mk
    (c : ConjClasses G) (g : G) :
    centerCoeffEquivFun k (conjugacyClassSumInCenter k c) (ConjClasses.mk g) =
      (c.indicator : G → k) g := by
  simp [centerCoeffEquivFun_apply_mk, conjugacyClassSum_apply]

/-- The conjugacy-class sums form the canonical `k`-basis of the center of `k[G]`, indexed by the
conjugacy classes of `G`. -/
noncomputable def conjugacyClassSumBasis :
    Module.Basis (ConjClasses G) k (Subalgebra.center k (k[G])) :=
  Module.Basis.ofEquivFun (centerCoeffEquivFun k)

@[simp] theorem centerCoeffEquivFun_conjugacyClassSumInCenter_self (c : ConjClasses G) :
    centerCoeffEquivFun k (conjugacyClassSumInCenter k c) c = 1 := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  have h1 : ((ConjClasses.mk g).indicator : G → k) g = 1 := by
    simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq]
  simpa [centerCoeffEquivFun_apply_mk, conjugacyClassSum_apply] using h1

@[simp] theorem centerCoeffEquivFun_conjugacyClassSumInCenter_of_ne
    {c c' : ConjClasses G} (h : c' ≠ c) :
    centerCoeffEquivFun k (conjugacyClassSumInCenter k c) c' = 0 := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c'
  have h0 : (c.indicator : G → k) g = 0 := by
    simp [ConjClasses.indicator, ConjClasses.mem_carrier_iff_mk_eq, h]
  simpa [centerCoeffEquivFun_apply_mk, conjugacyClassSum_apply] using h0

@[simp] theorem conjugacyClassSumBasis_apply (c : ConjClasses G) :
    conjugacyClassSumBasis k c = conjugacyClassSumInCenter k c := by
  classical
  apply (centerCoeffEquivFun k).injective
  funext c'
  by_cases h : c' = c
  · subst h
    simp [conjugacyClassSumBasis]
  · simp [conjugacyClassSumBasis, h]

end

section

variable {G : Type u} [Group G] [Finite G]

/-- Companion reformulation of Exercise 6-6.5-6 in span form. -/
theorem center_intGroupRing_eq_span_conjugacyClassSum :
    Submodule.span ℤ (Set.range (conjugacyClassSum ℤ : ConjClasses G → ℤ[G])) =
      (Subalgebra.center ℤ (ℤ[G])).toSubmodule := by
  let Z : Subalgebra ℤ (ℤ[G]) := Subalgebra.center ℤ (ℤ[G])
  let i : Z →ₗ[ℤ] ℤ[G] := Z.toSubmodule.subtype
  -- The conjugacy-class sums already form a basis of the center, so they span all of it there.
  have hbasisRange :
      Set.range (conjugacyClassSumInCenter ℤ : ConjClasses G → Z) =
        Set.range (conjugacyClassSumBasis (G := G) (k := ℤ) : ConjClasses G → Z) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, conjugacyClassSumBasis_apply (G := G) (k := ℤ) c⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, (conjugacyClassSumBasis_apply (G := G) (k := ℤ) c).symm⟩
  have hspan :
      Submodule.span ℤ
          (Set.range
            (conjugacyClassSumInCenter ℤ :
              ConjClasses G → Z)) = ⊤ := by
    rw [hbasisRange]
    exact (conjugacyClassSumBasis (G := G) (k := ℤ)).span_eq
  -- Mapping those generators through the center subtype gives exactly the ambient class sums.
  have himage :
      i '' Set.range (conjugacyClassSumInCenter ℤ : ConjClasses G → Z) =
        Set.range (conjugacyClassSum ℤ : ConjClasses G → ℤ[G]) := by
    ext x
    constructor
    · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
      refine ⟨c, ?_⟩
      show conjugacyClassSum ℤ c = i (conjugacyClassSumInCenter ℤ c)
      change conjugacyClassSum ℤ c = ((conjugacyClassSumInCenter ℤ c : Z) : ℤ[G])
      exact (coe_conjugacyClassSumInCenter (k := ℤ) c).symm
    · rintro ⟨c, rfl⟩
      exact ⟨conjugacyClassSumInCenter ℤ c, ⟨c, rfl⟩, by
        show i (conjugacyClassSumInCenter ℤ c) = conjugacyClassSum ℤ c
        change ((conjugacyClassSumInCenter ℤ c : Z) : ℤ[G]) = conjugacyClassSum ℤ c
        exact coe_conjugacyClassSumInCenter (k := ℤ) c⟩
  -- Transport the spanning statement from the center to the ambient group ring.
  calc
    Submodule.span ℤ (Set.range (conjugacyClassSum ℤ : ConjClasses G → ℤ[G]))
        = Submodule.map i
            (Submodule.span ℤ
              (Set.range
                (conjugacyClassSumInCenter ℤ :
                  ConjClasses G → Z))) := by
            rw [Submodule.map_span, himage]
    _ = Submodule.map i ⊤ := by
      rw [hspan]
    _ = Z.toSubmodule := by
      rw [Submodule.map_top]
      simpa only [i] using (Submodule.range_subtype Z.toSubmodule)
    _ = (Subalgebra.center ℤ (ℤ[G])).toSubmodule := by
      rfl

end
