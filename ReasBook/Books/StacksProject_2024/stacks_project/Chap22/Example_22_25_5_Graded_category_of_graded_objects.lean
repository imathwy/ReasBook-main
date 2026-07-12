import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.CategoryTheory.Shift.ShiftedHom
import StacksProject_2024.Chap12.Definition_12_16_1
import StacksProject_2024.Chap22.Definition_22_25_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum

universe v u

namespace CategoryTheory

namespace GradedObject

noncomputable section

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Preadditive 𝒜]

/- Source/core/bridge triage for Example 22.25.5:
- source-facing: the graded category whose objects are graded objects of `𝒜` and whose degree-`n`
  homogeneous morphisms are maps `A ⟶ B⟦n⟧`;
- core/canonical: the same-objects owner `GradedHomCategory 𝒜` below, whose ordinary morphisms are
  finite sums of shifted homogeneous morphisms;
- bridge/view: the degree-`0` homogeneous piece recovers the ordinary category `Gr(𝒜)`. -/

/-- The same-objects owner used in Example 22.25.5 (Graded category of graded objects). Its
objects are the ordinary graded objects of `𝒜`, while its total Hom from `A` to `B` is the direct
sum of the shifted homogeneous pieces `A ⟶ B⟦n⟧`. -/
structure GradedHomCategory where
  obj : Gr(𝒜)

namespace GradedHomCategory

open scoped GradedCategory

instance : CoeTC (GradedHomCategory 𝒜) (Gr(𝒜)) where
  coe A := A.obj

omit [Category.{v} 𝒜] [Preadditive 𝒜] in
@[simp] theorem coe_mk (A : Gr(𝒜)) : ((⟨A⟩ : GradedHomCategory 𝒜) : Gr(𝒜)) = A :=
  rfl

/-- The degree-`n` homogeneous morphisms in the graded Hom category. -/
private abbrev shiftedHom (A B : GradedHomCategory 𝒜) (n : ℤ) : Type v :=
  ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n

/-- Example 22.25.5 (1): for graded objects `A` and `B`, the total graded Hom is the direct sum
of the homogeneous degree pieces `ShiftedHom A B n`. -/
@[stacks 09MM]
abbrev homSpace (A B : GradedHomCategory 𝒜) :=
  ⨁ n : ℤ, ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n

/-- `homSpace` is the direct sum of the homogeneous degree pieces. -/
theorem homSpace_def (A B : GradedHomCategory 𝒜) :
    homSpace 𝒜 A B = ⨁ n : ℤ, ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n :=
  rfl

/-- The degree-`0` homogeneous identity map of a graded object. -/
def idHom (A : GradedHomCategory 𝒜) : ShiftedHom (A : Gr(𝒜)) (A : Gr(𝒜)) (0 : ℤ) :=
  ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (A : Gr(𝒜)))

/-- The identity morphism in the graded Hom category is concentrated in degree `0`. -/
def idSpace (A : GradedHomCategory 𝒜) : homSpace 𝒜 A A :=
  DirectSum.of (fun n ↦ shiftedHom 𝒜 A A n) 0 (idHom 𝒜 A)

/-- Example 22.25.5 (2): composing a degree-`m` homogeneous map `g : B ⟶ C⟦m⟧` with a degree-`n`
homogeneous map `f : A ⟶ B⟦n⟧` produces a degree-`n + m` homogeneous map `A ⟶ C⟦n + m⟧`. -/
@[stacks 09MM]
abbrev compHomDegree
    {A B C : GradedHomCategory 𝒜} {m n : ℤ}
    (g : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    ShiftedHom (A : Gr(𝒜)) (C : Gr(𝒜)) (n + m) :=
  ShiftedHom.comp f g (add_comm m n)

/- `compHomDegree` is composition in the shifted-hom category of graded objects. -/
omit [Preadditive 𝒜] in
theorem compHomDegree_def
    {A B C : GradedHomCategory 𝒜} {m n : ℤ}
    (g : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    compHomDegree 𝒜 g f =
      ShiftedHom.comp f g (by simpa [add_comm]) :=
  rfl

@[simp] theorem compHomDegree_add_left
    {A B C : GradedHomCategory 𝒜} {m n : ℤ}
    (g₁ g₂ : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    compHomDegree 𝒜 (g₁ + g₂) f =
      compHomDegree 𝒜 g₁ f + compHomDegree 𝒜 g₂ f := by
  simpa [compHomDegree] using ShiftedHom.comp_add f g₁ g₂ (add_comm m n)

@[simp] theorem compHomDegree_add_right
    {A B C : GradedHomCategory 𝒜} {m n : ℤ}
    (g : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (f₁ f₂ : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    compHomDegree 𝒜 g (f₁ + f₂) =
      compHomDegree 𝒜 g f₁ + compHomDegree 𝒜 g f₂ := by
  simpa [compHomDegree] using ShiftedHom.add_comp f₁ f₂ g (add_comm m n)

@[simp] theorem compHomDegree_smul_left
    {A B C : GradedHomCategory 𝒜} {m n : ℤ}
    (r : ℤ) (g : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    compHomDegree 𝒜 (r • g) f = r • compHomDegree 𝒜 g f := by
  simpa [compHomDegree] using ShiftedHom.comp_smul r f g (add_comm m n)

@[simp] theorem compHomDegree_smul_right
    {A B C : GradedHomCategory 𝒜} {m n : ℤ}
    (r : ℤ) (g : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    compHomDegree 𝒜 g (r • f) = r • compHomDegree 𝒜 g f := by
  simpa [compHomDegree] using ShiftedHom.smul_comp r f g (add_comm m n)

private def compHomLinear
    {A B C : GradedHomCategory 𝒜} {m n : ℤ}
    (g : shiftedHom 𝒜 B C m) :
    shiftedHom 𝒜 A B n →ₗ[ℤ] shiftedHom 𝒜 A C (n + m) where
  toFun := compHomDegree 𝒜 g
  map_add' := by
    intro f₁ f₂
    simpa using compHomDegree_add_right g f₁ f₂
  map_smul' := by
    intro r f
    simpa using compHomDegree_smul_right r g f

private def postcomposeHom
    {A B C : GradedHomCategory 𝒜} {m : ℤ}
    (g : shiftedHom 𝒜 B C m) :
    homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C :=
  DirectSum.toModule ℤ ℤ (homSpace 𝒜 A C)
    (fun n ↦
      (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (n + m)).comp (compHomLinear 𝒜 g))

private def composeByDegree
    {A B C : GradedHomCategory 𝒜} (m : ℤ) :
    shiftedHom 𝒜 B C m →ₗ[ℤ] homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C :=
  { toFun := fun g ↦ postcomposeHom 𝒜 g
    map_add' := by
      intro g₁ g₂
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro f
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change
        postcomposeHom 𝒜 (g₁ + g₂) ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f) =
          postcomposeHom 𝒜 g₁ ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f) +
            postcomposeHom 𝒜 g₂ ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f)
      change
        DirectSum.toModule ℤ ℤ (homSpace 𝒜 A C)
            (fun k ↦
              (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (k + m)).comp
                (compHomLinear 𝒜 (g₁ + g₂)))
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f) =
          DirectSum.toModule ℤ ℤ (homSpace 𝒜 A C)
              (fun k ↦
                (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (k + m)).comp
                  (compHomLinear 𝒜 g₁))
              ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f) +
            DirectSum.toModule ℤ ℤ (homSpace 𝒜 A C)
              (fun k ↦
                (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (k + m)).comp
                  (compHomLinear 𝒜 g₂))
              ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f)
      repeat rw [DirectSum.toModule_lof]
      change
        (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (n + m))
            (compHomDegree 𝒜 (g₁ + g₂) f) =
          (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (n + m))
            (compHomDegree 𝒜 g₁ f) +
              (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (n + m))
                (compHomDegree 𝒜 g₂ f)
      simpa using
        congrArg
          (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (n + m))
          (compHomDegree_add_left g₁ g₂ f)
    map_smul' := by
      intro r g
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro f
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change
        postcomposeHom 𝒜 (r • g) ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f) =
          (((RingHom.id ℤ) r) • postcomposeHom 𝒜 g)
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f)
      change
        DirectSum.toModule ℤ ℤ (homSpace 𝒜 A C)
            (fun k ↦
              (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (k + m)).comp
                (compHomLinear 𝒜 (r • g)))
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f) =
          (((RingHom.id ℤ) r) •
              DirectSum.toModule ℤ ℤ (homSpace 𝒜 A C)
                (fun k ↦
                  (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (k + m)).comp
                    (compHomLinear 𝒜 g)))
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f)
      change
        DirectSum.toModule ℤ ℤ (homSpace 𝒜 A C)
            (fun k ↦
              (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (k + m)).comp
                (compHomLinear 𝒜 (r • g)))
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f) =
          r •
            DirectSum.toModule ℤ ℤ (homSpace 𝒜 A C)
              (fun k ↦
                (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (k + m)).comp
                  (compHomLinear 𝒜 g))
              ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f)
      repeat rw [DirectSum.toModule_lof]
      change
        (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (n + m))
            (compHomDegree 𝒜 (r • g) f) =
          r •
            (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (n + m))
              (compHomDegree 𝒜 g f)
      simpa using
        congrArg
          (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (n + m))
          (compHomDegree_smul_left r g f) }

private def compLinear
    {A B C : GradedHomCategory 𝒜} :
    homSpace 𝒜 B C →ₗ[ℤ] homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C :=
  DirectSum.toModule ℤ ℤ (homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C)
    (composeByDegree 𝒜)

/-- Composition in the graded category is induced by homogeneous composition on shifted-Hom
pieces. -/
def compSpace
    {A B C : GradedHomCategory 𝒜}
    (g : homSpace 𝒜 B C) (f : homSpace 𝒜 A B) :
    homSpace 𝒜 A C :=
  compLinear 𝒜 g f

@[simp] private theorem compSpace_lof_lof'
    {A B C : GradedHomCategory 𝒜} {m n : ℤ}
    (g : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    compSpace 𝒜
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) i) m) g)
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) n) f) =
      (DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (A : Gr(𝒜)) (C : Gr(𝒜)) i) (n + m))
        (compHomDegree 𝒜 g f) := by
  rw [compSpace, compLinear]
  have hcompose :
      ((DirectSum.toModule ℤ ℤ (homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C) (composeByDegree 𝒜))
          ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) i) m) g)) =
        composeByDegree 𝒜 m g := by
    simpa using
      (@DirectSum.toModule_lof ℤ _ ℤ (shiftedHom 𝒜 B C) _ _ _
        (homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C) _ _ (composeByDegree 𝒜) m g)
  have happ :
      ((DirectSum.toModule ℤ ℤ (homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C) (composeByDegree 𝒜))
          ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) i) m) g))
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) n) f) =
      (composeByDegree 𝒜 m g)
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) n) f) := by
    exact
      congrArg
        (fun T : homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C ↦
          T ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) n) f))
        hcompose
  calc
    ((DirectSum.toModule ℤ ℤ (homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C) (composeByDegree 𝒜))
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) i) m) g))
      ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) n) f) =
        (composeByDegree 𝒜 m g)
          ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) n) f) := happ
    _ = (DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (A : Gr(𝒜)) (C : Gr(𝒜)) i) (n + m))
          (compHomDegree 𝒜 g f) := by
      exact
        (@DirectSum.toModule_lof ℤ _ ℤ (shiftedHom 𝒜 A B) _ _ _ (homSpace 𝒜 A C) _ _
          (fun n ↦
            (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A C i) (n + m)).comp
              (compHomLinear 𝒜 g))
          n f)

@[simp] private theorem compSpace_of_of
    {A B C : GradedHomCategory 𝒜} {m n : ℤ}
    (g : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    compSpace 𝒜
        (DirectSum.of (fun i ↦ ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) i) m g)
        (DirectSum.of (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) n f) =
      (DirectSum.of (fun i ↦ ShiftedHom (A : Gr(𝒜)) (C : Gr(𝒜)) i) (n + m))
        (compHomDegree 𝒜 g f) := by
  simpa [DirectSum.lof_eq_of] using compSpace_lof_lof' 𝒜 g f

@[simp] theorem compSpace_lof_lof
    {A B C : GradedHomCategory 𝒜} {m n : ℤ}
    (g : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    compSpace 𝒜
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) i) m) g)
        ((DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) n) f) =
      (DirectSum.lof ℤ ℤ (fun i ↦ ShiftedHom (A : Gr(𝒜)) (C : Gr(𝒜)) i) (n + m))
        (compHomDegree 𝒜 g f) := by
  exact compSpace_lof_lof' 𝒜 g f

@[simp] theorem compSpace_zero_left
    {A B C : GradedHomCategory 𝒜} (f : homSpace 𝒜 A B) :
    compSpace 𝒜 (0 : homSpace 𝒜 B C) f = 0 := by
  simpa [compSpace] using
    ((compLinear 𝒜 : homSpace 𝒜 B C →ₗ[ℤ] homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C).map_zero f)

@[simp] theorem compSpace_zero_right
    {A B C : GradedHomCategory 𝒜} (g : homSpace 𝒜 B C) :
    compSpace 𝒜 g (0 : homSpace 𝒜 A B) = 0 := by
  simpa [compSpace] using
    ((compLinear 𝒜 : homSpace 𝒜 B C →ₗ[ℤ] homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C) g).map_zero

@[simp] theorem compSpace_add_left
    {A B C : GradedHomCategory 𝒜} (g₁ g₂ : homSpace 𝒜 B C) (f : homSpace 𝒜 A B) :
    compSpace 𝒜 (g₁ + g₂) f = compSpace 𝒜 g₁ f + compSpace 𝒜 g₂ f := by
  simpa [compSpace] using
    ((compLinear 𝒜 : homSpace 𝒜 B C →ₗ[ℤ] homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C).map_add g₁ g₂ f)

@[simp] theorem compSpace_add_right
    {A B C : GradedHomCategory 𝒜} (g : homSpace 𝒜 B C) (f₁ f₂ : homSpace 𝒜 A B) :
    compSpace 𝒜 g (f₁ + f₂) = compSpace 𝒜 g f₁ + compSpace 𝒜 g f₂ := by
  simpa [compSpace] using
    ((compLinear 𝒜 : homSpace 𝒜 B C →ₗ[ℤ] homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C) g).map_add f₁ f₂

@[simp] theorem compSpace_smul_left
    {A B C : GradedHomCategory 𝒜} (r : ℤ) (g : homSpace 𝒜 B C) (f : homSpace 𝒜 A B) :
    compSpace 𝒜 (r • g) f = r • compSpace 𝒜 g f := by
  simpa [compSpace] using
    ((compLinear 𝒜 : homSpace 𝒜 B C →ₗ[ℤ] homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C).map_smul r g f)

@[simp] theorem compSpace_smul_right
    {A B C : GradedHomCategory 𝒜} (r : ℤ) (g : homSpace 𝒜 B C) (f : homSpace 𝒜 A B) :
    compSpace 𝒜 g (r • f) = r • compSpace 𝒜 g f := by
  simpa [compSpace] using
    ((compLinear 𝒜 : homSpace 𝒜 B C →ₗ[ℤ] homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C) g).map_smul r f

/-- Helper for Example 22.25.5 (Graded category of graded objects): if a homogeneous element
transports along an index equality to another homogeneous element, then their direct-sum
generators agree. -/
private theorem directSumOf_eq_of_transport
    {β : ℤ → Type v} [∀ i, AddCommMonoid (β i)]
    {i j : ℤ} (hij : i = j) (x : β i) (y : β j)
    (hxy : hij ▸ x = y) :
    DirectSum.of β i x = DirectSum.of β j y := by
  -- Proof comment: eliminating the index equality reduces the dependent statement to ordinary
  -- congruence for a fixed direct-sum summand.
  cases hij
  simpa using congrArg (DirectSum.of β i) hxy

omit [Preadditive 𝒜] in
/-- Helper for Example 22.25.5: transporting a homogeneous composite along an equality of output
degrees agrees with recomputing the same composite in the transported degree. -/
private theorem shiftedHomComp_transport
    {A B C : Gr(𝒜)} {a b c c' : ℤ}
    (f : ShiftedHom A B a) (g : ShiftedHom B C b)
    (h : b + a = c) (hc : c = c') :
    hc ▸ ShiftedHom.comp f g h = ShiftedHom.comp f g (h.trans hc) := by
  -- Proof comment: the only dependence on `hc` is through the target degree, so abstract
  -- elimination on that equality computes the transport exactly.
  cases hc
  rfl

omit [Preadditive 𝒜] in
/-- Helper for Example 22.25.5: the witness of the output-degree equality does not affect a fixed
homogeneous composite. -/
private theorem shiftedHomComp_eq
    {A B C : Gr(𝒜)} {a b c : ℤ}
    (f : ShiftedHom A B a) (g : ShiftedHom B C b)
    (h₁ h₂ : b + a = c) :
    ShiftedHom.comp f g h₁ = ShiftedHom.comp f g h₂ := by
  -- Proof comment: after the codomain degree is fixed, the remaining proof argument is a mere
  -- proposition, so proof irrelevance identifies the two composites.
  cases Subsingleton.elim h₁ h₂
  rfl

omit [Preadditive 𝒜] in
/-- Helper for Example 22.25.5: composing with the degree-`0` source identity agrees with the
original homogeneous map after normalizing the output degree. -/
private theorem compHomDegree_idSource_cast
    {A B : GradedHomCategory 𝒜} {n : ℤ}
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    (zero_add n) ▸ compHomDegree 𝒜 f (idHom 𝒜 A) = f := by
  -- Route correction: use the `ShiftedHom` degree-`0` identity API directly and normalize only
  -- the resulting degree cast.
  calc
    (zero_add n) ▸ compHomDegree 𝒜 f (idHom 𝒜 A) =
        ShiftedHom.comp (idHom 𝒜 A) f ((add_comm n 0).trans (zero_add n)) := by
          -- Proof comment: first move the transport from the ambient type to the output-degree
          -- witness of the homogeneous composite.
          simpa only [compHomDegree] using
            shiftedHomComp_transport (f := idHom 𝒜 A) (g := f)
              (h := add_comm n 0) (hc := zero_add n)
    _ = f := by
      -- Proof comment: after the degree witness is normalized to `n + 0 = n`, the standard
      -- shifted-Hom identity lemma applies directly.
      simpa only [idHom] using
        (ShiftedHom.mk₀_id_comp (f := f) (m₀ := (0 : ℤ)) (hm₀ := rfl))

/-- Helper for Example 22.25.5 (Graded category of graded objects): the direct-sum generator
obtained by composing with the degree-`0` identity on the source agrees with the original
generator. -/
@[simp] private theorem compHomDegree_idSource_of
    {A B : GradedHomCategory 𝒜} {n : ℤ}
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    DirectSum.of (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) (0 + n)
        (compHomDegree 𝒜 f (idHom 𝒜 A)) =
      DirectSum.of (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) n f := by
  -- Proof comment: package the cast-normalized homogeneous identity as an equality of
  -- direct-sum generators.
  exact directSumOf_eq_of_transport (β := fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i)
    (hij := zero_add n) _ _ (compHomDegree_idSource_cast (𝒜 := 𝒜) (A := A) (B := B) f)

omit [Preadditive 𝒜] in
/-- Helper for Example 22.25.5: composing with the degree-`0` target identity agrees with the
original homogeneous map after normalizing the output degree. -/
private theorem compHomDegree_idTarget_cast
    {A B : GradedHomCategory 𝒜} {n : ℤ}
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    (add_zero n) ▸ compHomDegree 𝒜 (idHom 𝒜 B) f = f := by
  -- Route correction: use the `ShiftedHom` right-identity API and keep the only transport at the
  -- level of the degree index.
  calc
    (add_zero n) ▸ compHomDegree 𝒜 (idHom 𝒜 B) f =
        ShiftedHom.comp f (idHom 𝒜 B) ((add_comm 0 n).trans (add_zero n)) := by
          -- Proof comment: as on the left identity side, transport is absorbed into the witness
          -- of the composite degree.
          simpa only [compHomDegree] using
            shiftedHomComp_transport (f := f) (g := idHom 𝒜 B)
              (h := add_comm 0 n) (hc := add_zero n)
    _ = f := by
      -- Proof comment: with the degree witness normalized to `0 + n = n`, the right-identity
      -- lemma for shifted morphisms closes the goal.
      simpa only [idHom] using
        (ShiftedHom.comp_mk₀_id (f := f) (m₀ := (0 : ℤ)) (hm₀ := rfl))

/-- Helper for Example 22.25.5 (Graded category of graded objects): the direct-sum generator
obtained by composing with the degree-`0` identity on the target agrees with the original
generator. -/
@[simp] private theorem compHomDegree_idTarget_of
    {A B : GradedHomCategory 𝒜} {n : ℤ}
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    DirectSum.of (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) (n + 0)
        (compHomDegree 𝒜 (idHom 𝒜 B) f) =
      DirectSum.of (fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i) n f := by
  -- Proof comment: compare the two direct-sum generators by transporting along `add_zero n`.
  exact directSumOf_eq_of_transport (β := fun i ↦ ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) i)
    (hij := add_zero n) _ _ (compHomDegree_idTarget_cast (𝒜 := 𝒜) (A := A) (B := B) f)

omit [Preadditive 𝒜] in
/-- Helper for Example 22.25.5: homogeneous composition is associative after reassociating the
total degree. -/
private theorem compHomDegree_assoc_cast
    {A B C D : GradedHomCategory 𝒜} {l m n : ℤ}
    (χ : ShiftedHom (C : Gr(𝒜)) (D : Gr(𝒜)) l)
    (ψ : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (φ : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    (add_assoc n m l) ▸ compHomDegree 𝒜 χ (compHomDegree 𝒜 ψ φ) =
      compHomDegree 𝒜 (compHomDegree 𝒜 χ ψ) φ := by
  -- Route correction: stay in the `ShiftedHom.comp_assoc` spelling and normalize only the degree
  -- arithmetic, rather than trying to force definally equal composite proofs.
  calc
    (add_assoc n m l) ▸ compHomDegree 𝒜 χ (compHomDegree 𝒜 ψ φ) =
        ShiftedHom.comp (compHomDegree 𝒜 ψ φ) χ
          ((add_comm l (n + m)).trans (add_assoc n m l)) := by
            -- Proof comment: transport the outer composite to the final degree
            -- `n + (m + l)` before invoking associativity.
            simpa only [compHomDegree] using
              shiftedHomComp_transport (f := compHomDegree 𝒜 ψ φ) (g := χ)
                (h := add_comm l (n + m)) (hc := add_assoc n m l)
    _ = ShiftedHom.comp (compHomDegree 𝒜 ψ φ) χ
          (show l + (n + m) = n + (m + l) by
            simpa [add_assoc, add_comm, add_left_comm]) := by
              -- Proof comment: once the target degree is fixed, the witness proof is irrelevant.
              apply shiftedHomComp_eq
    _ = compHomDegree 𝒜 (compHomDegree 𝒜 χ ψ) φ := by
      -- Proof comment: the canonical `ShiftedHom.comp_assoc` lemma now matches the normalized
      -- degree bookkeeping exactly.
      simpa only [compHomDegree, add_assoc, add_comm, add_left_comm] using
        (ShiftedHom.comp_assoc (a := n + (m + l)) φ ψ χ (add_comm m n) (add_comm l m)
          (by simpa [add_assoc, add_comm, add_left_comm]))

/-- Helper for Example 22.25.5 (Graded category of graded objects): on homogeneous generators,
graded composition is associative after normalizing the total degree. -/
private theorem compHomDegree_assoc_of
    {A B C D : GradedHomCategory 𝒜} {l m n : ℤ}
    (χ : ShiftedHom (C : Gr(𝒜)) (D : Gr(𝒜)) l)
    (ψ : ShiftedHom (B : Gr(𝒜)) (C : Gr(𝒜)) m)
    (φ : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    DirectSum.of (fun i ↦ ShiftedHom (A : Gr(𝒜)) (D : Gr(𝒜)) i) ((n + m) + l)
        (compHomDegree 𝒜 χ (compHomDegree 𝒜 ψ φ)) =
      DirectSum.of (fun i ↦ ShiftedHom (A : Gr(𝒜)) (D : Gr(𝒜)) i) (n + (m + l))
        (compHomDegree 𝒜 (compHomDegree 𝒜 χ ψ) φ) := by
  -- Proof comment: package the cast-normalized associativity bridge into the direct-sum owner.
  exact directSumOf_eq_of_transport (β := fun i ↦ ShiftedHom (A : Gr(𝒜)) (D : Gr(𝒜)) i)
    (hij := add_assoc n m l) _ _
    (compHomDegree_assoc_cast (𝒜 := 𝒜) (χ := χ) (ψ := ψ) (φ := φ))

instance instCategory : Category (GradedHomCategory 𝒜) where
  Hom A B := homSpace 𝒜 A B
  id := idSpace 𝒜
  comp f g := compSpace 𝒜 g f
  id_comp := by
    intro A B f
    -- Reduce the left identity law to homogeneous generators of the direct sum.
    refine DirectSum.induction_on f ?_ ?_ ?_
    · simp
    · intro n φ
      -- On a generator, the direct-sum composition bridge reduces to the homogeneous identity.
      rw [idSpace, compSpace_of_of]
      simpa using compHomDegree_idSource_of (𝒜 := 𝒜) (A := A) (B := B) (n := n) φ
    · intro x y hx hy
      -- Extend from generators using additivity in the first argument of `compSpace`.
      simpa [compSpace_add_left, hx, hy]
  comp_id := by
    intro A B f
    -- Reduce the right identity law to homogeneous generators of the direct sum.
    refine DirectSum.induction_on f ?_ ?_ ?_
    · simp
    · intro n φ
      -- On a generator, the direct-sum composition bridge reduces to the homogeneous identity.
      rw [idSpace, compSpace_of_of]
      simpa using compHomDegree_idTarget_of (𝒜 := 𝒜) (A := A) (B := B) (n := n) φ
    · intro x y hx hy
      -- Extend from generators using additivity in the second argument of `compSpace`.
      simpa [compSpace_add_right, hx, hy]
  assoc := by
    intro A B C D f g h
    -- Reduce associativity successively to homogeneous generators in each direct sum.
    refine DirectSum.induction_on h ?_ ?_ ?_
    · simp
    · intro l χ
      refine DirectSum.induction_on g ?_ ?_ ?_
      · simp
      · intro m ψ
        refine DirectSum.induction_on f ?_ ?_ ?_
        · simp
        · intro n φ
          -- On triple generators, associativity is deferred to the homogeneous bridge lemma.
          rw [compSpace_of_of, compSpace_of_of, compSpace_of_of, compSpace_of_of]
          simpa using compHomDegree_assoc_of (𝒜 := 𝒜) (χ := χ) (ψ := ψ) (φ := φ)
        · intro x y hx hy
          -- Additivity in the innermost variable propagates the induction step.
          simpa [compSpace_add_right, hx, hy]
      · intro x y hx hy
        -- Additivity in the middle variable uses bilinearity in both slots.
        simpa [compSpace_add_left, compSpace_add_right, hx, hy]
    · intro x y hx hy
      -- Additivity in the outermost variable propagates the induction step.
      simpa [compSpace_add_left, hx, hy]

instance instPreadditive : Preadditive (GradedHomCategory 𝒜) where
  homGroup A B := by
    change AddCommGroup (homSpace 𝒜 A B)
    infer_instance
  add_comp := by
    intro A B C f g h
    let f' : homSpace 𝒜 A B := f
    let g' : homSpace 𝒜 A B := g
    let h' : homSpace 𝒜 B C := h
    change compSpace 𝒜 h' (f' + g') = compSpace 𝒜 h' f' + compSpace 𝒜 h' g'
    simpa [compSpace] using
      ((compLinear 𝒜 : homSpace 𝒜 B C →ₗ[ℤ] homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C) h').map_add f' g'
  comp_add := by
    intro A B C f g h
    let f' : homSpace 𝒜 A B := f
    let g' : homSpace 𝒜 B C := g
    let h' : homSpace 𝒜 B C := h
    change compSpace 𝒜 (g' + h') f' = compSpace 𝒜 g' f' + compSpace 𝒜 h' f'
    simpa [compSpace] using
      ((compLinear 𝒜 : homSpace 𝒜 B C →ₗ[ℤ] homSpace 𝒜 A B →ₗ[ℤ] homSpace 𝒜 A C).map_add g' h' f')

/-- The degree-`n` homogeneous summand inside the total graded Hom module. -/
private abbrev gradedHomDegree (A B : GradedHomCategory 𝒜) (n : ℤ) : Submodule ℤ (A ⟶ B) :=
  (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n).range

private def gradedHomDegreeOf (A B : GradedHomCategory 𝒜) (n : ℤ) :
    shiftedHom 𝒜 A B n →ₗ[ℤ] gradedHomDegree 𝒜 A B n where
  toFun f := ⟨DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n f, ⟨f, rfl⟩⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    exact (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n).map_add f g
  map_smul' := by
    intro r f
    apply Subtype.ext
    exact (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n).map_smul r f

/-- The degree-`n` shifted-Hom group identifies with the degree-`n` graded summand in the total
Hom module. -/
private def gradedHomDegreeEquiv (A B : GradedHomCategory 𝒜) (n : ℤ) :
    shiftedHom 𝒜 A B n ≃ₗ[ℤ] gradedHomDegree 𝒜 A B n where
  toFun := gradedHomDegreeOf 𝒜 A B n
  invFun x := DirectSum.component ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n x.1
  left_inv := by
    intro f
    simp [gradedHomDegreeOf]
  right_inv := by
    intro x
    rcases x.2 with ⟨f, hf⟩
    have hx : x = gradedHomDegreeOf 𝒜 A B n f := by
      apply Subtype.ext
      exact hf.symm
    rw [hx]
    ext
    simp [gradedHomDegreeOf]
  map_add' := by
    intro x y
    exact (gradedHomDegreeOf 𝒜 A B n).map_add x y
  map_smul' := by
    intro r x
    exact (gradedHomDegreeOf 𝒜 A B n).map_smul r x

@[simp] private theorem gradedHomDegreeEquiv_apply
    (A B : GradedHomCategory 𝒜) (n : ℤ) (f : shiftedHom 𝒜 A B n) :
    ((gradedHomDegreeEquiv 𝒜 A B n f : gradedHomDegree 𝒜 A B n) : A ⟶ B) =
      DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n f :=
  rfl

private def homSpaceDecompose (A B : GradedHomCategory 𝒜) :
    homSpace 𝒜 A B →ₗ[ℤ] ⨁ n : ℤ, gradedHomDegree 𝒜 A B n :=
  DirectSum.toModule ℤ ℤ (⨁ n : ℤ, gradedHomDegree 𝒜 A B n)
    (fun n ↦
      (DirectSum.lof ℤ ℤ (fun i ↦ gradedHomDegree 𝒜 A B i) n).comp
        (gradedHomDegreeEquiv 𝒜 A B n).toLinearMap)

private instance instHomSpaceDecomposition (A B : GradedHomCategory 𝒜) :
    DirectSum.Decomposition (gradedHomDegree 𝒜 A B) :=
  DirectSum.Decomposition.ofLinearMap (gradedHomDegree 𝒜 A B) (homSpaceDecompose 𝒜 A B)
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro f
      change
        DirectSum.coeLinearMap (gradedHomDegree 𝒜 A B)
            (DirectSum.toModule ℤ ℤ (⨁ k : ℤ, gradedHomDegree 𝒜 A B k)
              (fun k ↦
                (DirectSum.lof ℤ ℤ (fun i ↦ gradedHomDegree 𝒜 A B i) k).comp
                  (gradedHomDegreeEquiv 𝒜 A B k).toLinearMap)
              ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f)) =
          (DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f
      rw [DirectSum.toModule_lof]
      simpa [gradedHomDegreeEquiv_apply])
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro x
      rcases x.2 with ⟨f, hf⟩
      have hx : x = gradedHomDegreeOf 𝒜 A B n f := by
        apply Subtype.ext
        exact hf.symm
      rw [hx]
      change
        homSpaceDecompose 𝒜 A B
            (DirectSum.coeLinearMap (gradedHomDegree 𝒜 A B)
              ((DirectSum.lof ℤ ℤ (fun i ↦ gradedHomDegree 𝒜 A B i) n)
                (gradedHomDegreeOf 𝒜 A B n f))) =
          (DirectSum.lof ℤ ℤ (fun i ↦ gradedHomDegree 𝒜 A B i) n)
            (gradedHomDegreeOf 𝒜 A B n f)
      rw [DirectSum.coeLinearMap_lof]
      change
        DirectSum.toModule ℤ ℤ (⨁ k : ℤ, gradedHomDegree 𝒜 A B k)
            (fun k ↦
              (DirectSum.lof ℤ ℤ (fun i ↦ gradedHomDegree 𝒜 A B i) k).comp
                (gradedHomDegreeEquiv 𝒜 A B k).toLinearMap)
            ((DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n) f) =
          (DirectSum.lof ℤ ℤ (fun i ↦ gradedHomDegree 𝒜 A B i) n)
            (gradedHomDegreeOf 𝒜 A B n f)
      rw [DirectSum.toModule_lof]
      rfl)

/-- Example 22.25.5 (Graded category of graded objects): graded objects form a graded category
whose degree-`n` piece is the `n`-th shifted-Hom summand. -/
instance instGradedCategory : GradedCategory ℤ (GradedHomCategory 𝒜) where
  homDegree := gradedHomDegree 𝒜
  homDecomposition := instHomSpaceDecomposition 𝒜
  id_mem_homDegree_zero := by
    intro A
    exact ⟨idHom 𝒜 A, rfl⟩
  comp_mem := by
    intro A B C i j f g hf hg
    rcases hf with ⟨f', rfl⟩
    rcases hg with ⟨g', rfl⟩
    exact ⟨compHomDegree 𝒜 g' f', (compSpace_lof_lof 𝒜 g' f').symm⟩

variable (A B : GradedHomCategory 𝒜)
variable (n : ℤ)

omit [Preadditive 𝒜] in
/-- The degree-`n` piece `Hom^n(A, B)` of `GradedHomCategory 𝒜` is canonically the shifted-Hom
group `A ⟶ B⟦n⟧`. -/
def homDegreeEquivShiftedHom :
    (Hom^n(A, B) : Submodule ℤ (A ⟶ B)) ≃ₗ[ℤ] ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n :=
  (gradedHomDegreeEquiv 𝒜 A B n).symm

@[simp] theorem homDegreeEquivShiftedHom_apply_lof
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    homDegreeEquivShiftedHom 𝒜 A B n
        ⟨DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n f, ⟨f, rfl⟩⟩ = f := by
  change (gradedHomDegreeEquiv 𝒜 A B n).symm ((gradedHomDegreeEquiv 𝒜 A B n) f) = f
  exact (gradedHomDegreeEquiv 𝒜 A B n).symm_apply_apply f

@[simp] theorem homDegreeEquivShiftedHom_symm_apply
    (f : ShiftedHom (A : Gr(𝒜)) (B : Gr(𝒜)) n) :
    (((homDegreeEquivShiftedHom 𝒜 A B n).symm f : Hom^n(A, B)) : A ⟶ B) =
      DirectSum.lof ℤ ℤ (fun i ↦ shiftedHom 𝒜 A B i) n f := by
  rfl

/- Example 22.25.5 (3): the degree-`0` homogeneous maps are canonically the ordinary morphisms of
graded objects, so the degree-`0` part recovers `Gr(𝒜)`. -/
recall ShiftedHom.homEquiv

/-- The canonical degree-`0` piece `Hom^0(A, B)` identifies with the ordinary morphisms of graded
objects. -/
noncomputable def degreeZeroHomEquiv :
    (Hom^0(A, B) : Submodule ℤ (A ⟶ B)) ≃ ((A : Gr(𝒜)) ⟶ B) :=
  (homDegreeEquivShiftedHom 𝒜 A B 0).toEquiv.trans (ShiftedHom.homEquiv (0 : ℤ) rfl).symm

@[simp] theorem degreeZeroHomEquiv_apply_mk₀
    (f : (A : Gr(𝒜)) ⟶ B) :
    degreeZeroHomEquiv 𝒜 A B
        ⟨DirectSum.lof ℤ ℤ (fun n ↦ shiftedHom 𝒜 A B n) 0 (ShiftedHom.mk₀ (0 : ℤ) rfl f),
          ⟨ShiftedHom.mk₀ (0 : ℤ) rfl f, rfl⟩⟩ = f := by
  change
    (ShiftedHom.homEquiv (0 : ℤ) rfl).symm
        ((homDegreeEquivShiftedHom 𝒜 A B 0)
          ⟨DirectSum.lof ℤ ℤ (fun n ↦ shiftedHom 𝒜 A B n) 0 (ShiftedHom.mk₀ (0 : ℤ) rfl f),
            ⟨ShiftedHom.mk₀ (0 : ℤ) rfl f, rfl⟩⟩) =
      f
  rw [homDegreeEquivShiftedHom_apply_lof]
  simpa using Equiv.symm_apply_apply (ShiftedHom.homEquiv (0 : ℤ) rfl) f

@[simp] theorem degreeZeroHomEquiv_symm_apply
    (f : (A : Gr(𝒜)) ⟶ B) :
    (((degreeZeroHomEquiv 𝒜 A B).symm f : Hom^0(A, B)) : A ⟶ B) =
      DirectSum.lof ℤ ℤ (fun n ↦ shiftedHom 𝒜 A B n) 0 (ShiftedHom.mk₀ (0 : ℤ) rfl f) := by
  simpa [degreeZeroHomEquiv] using
    homDegreeEquivShiftedHom_symm_apply (ShiftedHom.homEquiv (0 : ℤ) rfl f)

/-- A morphism in `(GradedHomCategory 𝒜)^0` is canonically the same thing as an ordinary
morphism of graded objects. -/
noncomputable def degreeZeroSubcategoryHomEquiv
    (A B : (GradedHomCategory 𝒜)^0) :
    (A ⟶ B) ≃ ((A.obj : Gr(𝒜)) ⟶ B.obj) where
  toFun f :=
    degreeZeroHomEquiv 𝒜 A.obj B.obj
      ⟨f.hom, GradedCategory.DegreeZero.hom_mem_homDegree_zero f⟩
  invFun f :=
    let hf := (degreeZeroHomEquiv 𝒜 A.obj B.obj).symm f
    ⟨hf.1, hf.2⟩
  left_inv f := by
    apply WideSubcategory.hom_ext
    change
      (((degreeZeroHomEquiv 𝒜 A.obj B.obj).symm
        (degreeZeroHomEquiv 𝒜 A.obj B.obj
          ⟨f.hom, GradedCategory.DegreeZero.hom_mem_homDegree_zero f⟩)).1) = f.hom
    simpa using congrArg Subtype.val
      ((degreeZeroHomEquiv 𝒜 A.obj B.obj).symm_apply_apply
        ⟨f.hom, GradedCategory.DegreeZero.hom_mem_homDegree_zero f⟩)
  right_inv f := by
    simpa using (degreeZeroHomEquiv 𝒜 A.obj B.obj).apply_symm_apply f

@[simp] theorem degreeZeroSubcategoryHomEquiv_apply
    {A B : (GradedHomCategory 𝒜)^0} (f : A ⟶ B) :
    degreeZeroSubcategoryHomEquiv 𝒜 A B f =
      degreeZeroHomEquiv 𝒜 A.obj B.obj
        ⟨f.hom, GradedCategory.DegreeZero.hom_mem_homDegree_zero f⟩ :=
  rfl

@[simp] theorem degreeZeroSubcategoryHomEquiv_symm_hom
    {A B : (GradedHomCategory 𝒜)^0} (f : (A.obj : Gr(𝒜)) ⟶ B.obj) :
    ((degreeZeroSubcategoryHomEquiv 𝒜 A B).symm f).hom =
      (((degreeZeroHomEquiv 𝒜 A.obj B.obj).symm f : Hom^0(A.obj, B.obj)) : A.obj ⟶ B.obj) :=
  rfl

@[simp] theorem degreeZeroSubcategoryHomEquiv_id
    (A : (GradedHomCategory 𝒜)^0) :
    degreeZeroSubcategoryHomEquiv 𝒜 A A (𝟙 A) = 𝟙 (A.obj : Gr(𝒜)) := by
  change
    degreeZeroHomEquiv 𝒜 A.obj A.obj
      ⟨DirectSum.lof ℤ ℤ (fun n ↦ shiftedHom 𝒜 A.obj A.obj n) 0
          (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (A.obj : Gr(𝒜)))),
        ⟨ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (A.obj : Gr(𝒜))), rfl⟩⟩ =
      𝟙 (A.obj : Gr(𝒜))
  exact
    degreeZeroHomEquiv_apply_mk₀ 𝒜 A.obj A.obj (𝟙 (A.obj : Gr(𝒜)))

end GradedHomCategory

end

end

end GradedObject

end CategoryTheory
