import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {G : Type u} {R : Type v} [Monoid G]

/-- Remark 2-2.1-2: a class function on a group factors through the canonical map to conjugacy
classes, equivalently it is constant on conjugacy classes. -/
@[mk_iff]
class IsClassFunction (f : G → R) : Prop where
  factorsThrough : f.FactorsThrough ConjClasses.mk

theorem IsClassFunction.eq_of_isConj {f : G → R} (hf : IsClassFunction f) {u v : G}
    (h : IsConj u v) : f u = f v :=
  hf.factorsThrough <| ConjClasses.mk_eq_mk_iff_isConj.mpr h

/-- A class function descends canonically to conjugacy classes. -/
def IsClassFunction.lift {f : G → R} (hf : IsClassFunction f) : ConjClasses G → R :=
  Quotient.lift f fun _ _ h ↦ hf.eq_of_isConj h

@[simp] theorem IsClassFunction.lift_mk {f : G → R} (hf : IsClassFunction f) (g : G) :
    hf.lift (ConjClasses.mk g) = f g :=
  rfl

@[simp] theorem IsClassFunction.lift_comp_mk {f : G → R} (hf : IsClassFunction f) :
    hf.lift ∘ ConjClasses.mk = f := by
  ext g
  rfl

theorem isClassFunction_iff_exists {f : G → R} :
    IsClassFunction f ↔ ∃ φ : ConjClasses G → R, f = φ ∘ ConjClasses.mk := by
  constructor
  · intro hf
    exact ⟨hf.lift, hf.lift_comp_mk.symm⟩
  · rintro ⟨φ, rfl⟩
    exact ⟨fun _ _ h ↦ congrArg φ h⟩

theorem IsClassFunction.eq_of_mk_eq {f : G → R} (hf : IsClassFunction f) {u v : G}
    (h : ConjClasses.mk u = ConjClasses.mk v) : f u = f v :=
  hf.factorsThrough h

/-- Postcomposing a class function with any function preserves conjugacy invariance. -/
theorem IsClassFunction.comp {f : G → R} (hf : IsClassFunction f) {S : Type*} (φ : R → S) :
    IsClassFunction (φ ∘ f) := by
  refine ⟨?_⟩
  intro u v huv
  simpa using congrArg φ (hf.eq_of_mk_eq huv)

/-- Precomposing a function on conjugacy classes with `ConjClasses.mk` produces a class function
on `G`. -/
instance (f : ConjClasses G → R) :
    IsClassFunction (f ∘ ConjClasses.mk) :=
  ⟨fun _ _ h ↦ congrArg f h⟩

/-- Constant functions on a group are class functions. -/
instance (c : R) : IsClassFunction (fun _ : G ↦ c) :=
  ⟨fun _ _ _ ↦ rfl⟩

/-- The pointwise sum of two class functions is a class function. -/
instance [Add R] {f g : G → R} [IsClassFunction f] [IsClassFunction g] :
    IsClassFunction (f + g) :=
by
  refine ⟨?_⟩
  intro u v h
  change f u + g u = f v + g v
  simpa using congrArg₂ (· + ·)
    ((inferInstance : IsClassFunction f).factorsThrough h)
    ((inferInstance : IsClassFunction g).factorsThrough h)

/-- Scalar multiples of class functions are class functions. -/
instance {S : Type*} [SMul S R] (c : S) {f : G → R} [IsClassFunction f] :
    IsClassFunction (c • f) :=
by
  refine ⟨?_⟩
  intro u v h
  change c • f u = c • f v
  simpa using congrArg (c • ·) ((inferInstance : IsClassFunction f).factorsThrough h)

section Submodule

variable (R) [Semiring R]

/-- The `R`-submodule of `R`-valued functions on `G` that are constant on conjugacy classes. -/
def classFunctionSubmodule (G : Type u) [Monoid G] : Submodule R (G → R) where
  carrier := { f | IsClassFunction f }
  zero_mem' := by
    simpa using (inferInstance : IsClassFunction (fun _ : G ↦ (0 : R)))
  add_mem' := by
    intro f g hf hg
    letI : IsClassFunction f := hf
    letI : IsClassFunction g := hg
    simpa using (inferInstance : IsClassFunction (f + g))
  smul_mem' := by
    intro c f hf
    letI : IsClassFunction f := hf
    simpa using (inferInstance : IsClassFunction (c • f))

/-- A function lies in `classFunctionSubmodule R G` exactly when it is a class function. -/
@[simp] theorem mem_classFunctionSubmodule_iff (f : G → R) :
    f ∈ classFunctionSubmodule R G ↔ IsClassFunction f := by
  rfl

namespace classFunctionSubmodule

/-- Elements of `classFunctionSubmodule R G` are canonically viewed as `R`-valued functions on
`G`. -/
instance : CoeFun (classFunctionSubmodule R G) (fun _ ↦ G → R) where
  coe f := f.1

/-- The class-function submodule is canonically linearly equivalent to functions on the conjugacy
classes. -/
def equivFun (G : Type u) [Monoid G] : classFunctionSubmodule R G ≃ₗ[R] (ConjClasses G → R) :=
  { toFun := fun χ ↦
      let hf : IsClassFunction (χ : G → R) :=
        χ.2
      hf.lift
    invFun := fun χ ↦
      ⟨χ ∘ ConjClasses.mk, (mem_classFunctionSubmodule_iff R _).2 inferInstance⟩
    left_inv := fun χ ↦ by
      ext g
      rfl
    right_inv := fun χ ↦ by
      ext c
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      rfl
    map_add' := by
      intro χ ψ
      ext c
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      rfl
    map_smul' := by
      intro a χ
      ext c
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      rfl }

end classFunctionSubmodule

end Submodule

/-- The complex vector subspace of functions on `G` that are constant on conjugacy classes. -/
abbrev classFunctionSubspace (G : Type u) [Monoid G] : Submodule ℂ (G → ℂ) :=
  classFunctionSubmodule ℂ G

/-- A function lies in `classFunctionSubspace G` exactly when it is a class function. -/
@[simp] theorem mem_classFunctionSubspace_iff (f : G → ℂ) :
    f ∈ classFunctionSubspace G ↔ IsClassFunction f := by
  rfl

end

section

variable {G : Type u} {R : Type v} [Monoid G]

variable [Zero R] [One R]

namespace ConjClasses

/-- The `R`-valued indicator of a conjugacy class, viewed as a class function on `G`. -/
noncomputable def indicator (c : ConjClasses G) : G → R := by
  classical
  exact c.carrier.indicator 1

@[simp] theorem indicator_apply_eq_one (c : ConjClasses G) {g : G}
    (h : ConjClasses.mk g = c) : c.indicator g = 1 := by
  classical
  simp [indicator, ConjClasses.mem_carrier_iff_mk_eq, h]

@[simp] theorem indicator_apply_eq_zero (c : ConjClasses G) {g : G}
    (h : ConjClasses.mk g ≠ c) : c.indicator g = 0 := by
  classical
  simp [indicator, ConjClasses.mem_carrier_iff_mk_eq, h]

/-- The indicator of a conjugacy class is a class function. -/
instance (c : ConjClasses G) : IsClassFunction (c.indicator : G → R) :=
by
  refine ⟨?_⟩
  intro x y hxy
  by_cases hx : ConjClasses.mk x = c
  · have hy : ConjClasses.mk y = c :=
      hxy.symm.trans hx
    simp [indicator, ConjClasses.mem_carrier_iff_mk_eq, hx, hy]
  · have hy : ConjClasses.mk y ≠ c := fun hy ↦
      hx <| hxy.trans hy
    simp [indicator, ConjClasses.mem_carrier_iff_mk_eq, hx, hy]

section Submodule

variable [Semiring R]

/-- The `R`-valued indicator of a conjugacy class, regarded as an element of the canonical
class-function submodule. -/
noncomputable def indicatorClassFunctionSubmodule (c : ConjClasses G) :
    classFunctionSubmodule R G :=
  ⟨c.indicator, (mem_classFunctionSubmodule_iff R _).2 inferInstance⟩

@[simp] theorem coe_indicatorClassFunctionSubmodule (c : ConjClasses G) :
    (c.indicatorClassFunctionSubmodule : G → R) = c.indicator :=
  rfl

end Submodule

/-- The complex-valued indicator of a conjugacy class, regarded as an element of the canonical
class-function subspace. -/
noncomputable abbrev indicatorClassFunction (c : ConjClasses G) : classFunctionSubspace G :=
  c.indicatorClassFunctionSubmodule (R := ℂ)

@[simp] theorem coe_indicatorClassFunction (c : ConjClasses G) :
    (c.indicatorClassFunction : G → ℂ) = c.indicator :=
  rfl

end ConjClasses

end

section

variable {G : Type u} {R : Type v} [Group G]

/-- A class function satisfies the source-facing identity `f (u * v) = f (v * u)`. -/
-- Proof sketch: the elements `u * v` and `v * u` are conjugate, with witness `v`,
-- so the defining conjugacy-invariance property applies.
theorem IsClassFunction.map_mul_comm {f : G → R} (hf : IsClassFunction f) (u v : G) :
    f (u * v) = f (v * u) :=
  hf.eq_of_isConj <| isConj_iff.2 ⟨v, by simp [mul_assoc]⟩

end
