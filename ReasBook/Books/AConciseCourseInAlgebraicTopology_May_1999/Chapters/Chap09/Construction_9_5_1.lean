import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2

open scoped TopCat Topology Topology.Homotopy

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: mathlib provides the compact-open mapping-space surface
-- `C(A, X)` and the loop-space notation `Ω^ (Fin n) X x` for iterated based cubes. This item
-- uses evaluation at the Chapter 9 sphere basepoint together with a source-facing identification
-- of its fiber with that canonical iterated loop-space owner.

/-- The evaluation map `C(𝕊 n, X) → X` at the chosen sphere basepoint `s : 𝕊 n`. -/
def sphereMapEvalAtBasepoint (n : ℕ) (s : 𝕊 n) : C(C(𝕊 n, X), X) where
  toFun f := f s
  continuous_toFun := continuous_eval_const s

/-- Construction 9.5.1 (1): evaluation at the chosen basepoint of `𝕊 n` gives a fibration
`C(𝕊 n, X) → X`. -/
theorem sphereMapEvalAtBasepoint_isFibration (n : ℕ) :
    IsFibration ((sphereMapEvalAtBasepoint n (sphereBasepoint n)) : C(C(𝕊 n, X), X)) := sorry

/-- The evaluation map at `sphereBasepoint n` carries the canonical `IsFibration` instance from
`Construction 9.5.1 (1)`. -/
instance sphereMapEvalAtBasepointInstIsFibration (n : ℕ) :
    IsFibration ((sphereMapEvalAtBasepoint n (sphereBasepoint n)) : C(C(𝕊 n, X), X)) :=
  sphereMapEvalAtBasepoint_isFibration n

/-- The fiber over `x` of evaluation at the chosen sphere basepoint `sphereBasepoint n`. -/
def sphereBasepointFiber (n : ℕ) (x : X) : Set (C(𝕊 n, X)) :=
  (sphereMapEvalAtBasepoint n (sphereBasepoint n)) ⁻¹' ({x} : Set X)

/-- The concrete space of maps `𝕊 n ⟶ X` sending the chosen sphere basepoint to `x`. -/
abbrev sphereBasepointBasedMapSpace (n : ℕ) (x : X) :=
  { f : C(𝕊 n, X) // f (sphereBasepoint n) = x }

/-- A map `f : C(𝕊 n, X)` lies in the chosen-basepoint fiber over `x` exactly when it sends
`sphereBasepoint n` to `x`. -/
theorem mem_sphereBasepointFiber_iff (n : ℕ) (x : X) (f : C(𝕊 n, X)) :
    f ∈ sphereBasepointFiber n x ↔ f (sphereBasepoint n) = x :=
  Iff.rfl

/-- The fiber over `x` of evaluation at the chosen sphere basepoint is homeomorphic to the
concrete space of based maps `𝕊 n ⟶ X` sending `sphereBasepoint n` to `x`. -/
def sphereBasepointFiberBasedMapSpaceHomeomorph (n : ℕ) (x : X) :
    sphereBasepointFiber n x ≃ₜ sphereBasepointBasedMapSpace n x where
  toEquiv :=
    { toFun := fun f ↦ ⟨f.1, (mem_sphereBasepointFiber_iff n x f.1).1 f.2⟩
      invFun := fun f ↦ ⟨f.1, (mem_sphereBasepointFiber_iff n x f.1).2 f.2⟩
      left_inv := fun f ↦ by ext; rfl
      right_inv := fun f ↦ by ext; rfl }
  continuous_toFun :=
    Continuous.subtype_mk continuous_subtype_val fun f ↦
      (mem_sphereBasepointFiber_iff n x f.1).1 f.2
  continuous_invFun :=
    Continuous.subtype_mk continuous_subtype_val fun f ↦
      (mem_sphereBasepointFiber_iff n x f.1).2 f.2

/-- As a function, `sphereBasepointFiberBasedMapSpaceHomeomorph n x` keeps the same continuous
map and re-reads the fiber equation as the based-map condition. -/
@[simp] theorem sphereBasepointFiberBasedMapSpaceHomeomorph_coe
    (n : ℕ) (x : X) :
    ⇑(sphereBasepointFiberBasedMapSpaceHomeomorph n x) =
      fun f ↦ ⟨f.1, (mem_sphereBasepointFiber_iff n x f.1).1 f.2⟩ :=
  rfl

/-- The comparison `sphereBasepointFiberBasedMapSpaceHomeomorph n x` sends a fiber element to the
same continuous map together with its basepoint condition. -/
@[simp] theorem sphereBasepointFiberBasedMapSpaceHomeomorph_apply
    (n : ℕ) (x : X) (f : sphereBasepointFiber n x) :
    sphereBasepointFiberBasedMapSpaceHomeomorph n x f =
      ⟨f.1, (mem_sphereBasepointFiber_iff n x f.1).1 f.2⟩ :=
  rfl

/-- As a function, the inverse of `sphereBasepointFiberBasedMapSpaceHomeomorph n x` keeps the same
continuous map and re-reads the based-map condition as the fiber equation. -/
@[simp] theorem sphereBasepointFiberBasedMapSpaceHomeomorph_symm_coe
    (n : ℕ) (x : X) :
    ⇑(sphereBasepointFiberBasedMapSpaceHomeomorph n x).symm =
      fun f ↦ ⟨f.1, (mem_sphereBasepointFiber_iff n x f.1).2 f.2⟩ :=
  rfl

/-- The inverse comparison `sphereBasepointFiberBasedMapSpaceHomeomorph n x` sends a based map to
the same continuous map together with its basepoint condition viewed as a fiber equation. -/
@[simp] theorem sphereBasepointFiberBasedMapSpaceHomeomorph_symm_apply
    (n : ℕ) (x : X) (f : sphereBasepointBasedMapSpace n x) :
    (sphereBasepointFiberBasedMapSpaceHomeomorph n x).symm f =
      ⟨f.1, (mem_sphereBasepointFiber_iff n x f.1).2 f.2⟩ :=
  rfl

/-- Construction 9.5.1 (2): the fiber over `x` of evaluation at `sphereBasepoint n` is
homeomorphic to the iterated loop space `Ω^ (Fin n) X x`. -/
theorem sphereBasepointFiber_homeomorphic_iteratedLoopSpace (n : ℕ) (x : X) :
    Nonempty (sphereBasepointFiber n x ≃ₜ Ω^ (Fin n) X x) := sorry

/-- Given a comparison from the concrete space of based maps `𝕊 n ⟶ X` sending
`sphereBasepoint n` to `x` to the iterated loop-space owner `Ω^ (Fin n) X x`, the fiber over `x`
of evaluation at `sphereBasepoint n` identifies with `Ω^ (Fin n) X x` by explicit composition. -/
noncomputable def sphereBasepointFiberHomeomorphOf (n : ℕ) (x : X)
    (e : sphereBasepointBasedMapSpace n x ≃ₜ Ω^ (Fin n) X x) :
    sphereBasepointFiber n x ≃ₜ Ω^ (Fin n) X x :=
  (sphereBasepointFiberBasedMapSpaceHomeomorph n x).trans e

/-- The comparison `sphereBasepointFiberHomeomorphOf n x e` is the explicit composite of
`sphereBasepointFiberBasedMapSpaceHomeomorph n x` with the chosen based-map-to-loop-space
comparison `e`. -/
@[simp] theorem sphereBasepointFiberHomeomorphOf_def
    (n : ℕ) (x : X) (e : sphereBasepointBasedMapSpace n x ≃ₜ Ω^ (Fin n) X x) :
    sphereBasepointFiberHomeomorphOf n x e =
      (sphereBasepointFiberBasedMapSpaceHomeomorph n x).trans e :=
  rfl

/-- As a function, `sphereBasepointFiberHomeomorphOf n x e` first forgets that a point of the
fiber is presented as a fiber element and then applies the chosen based-map-to-loop-space
comparison `e`. -/
@[simp] theorem sphereBasepointFiberHomeomorphOf_coe
    (n : ℕ) (x : X) (e : sphereBasepointBasedMapSpace n x ≃ₜ Ω^ (Fin n) X x) :
    ⇑(sphereBasepointFiberHomeomorphOf n x e) =
      fun f ↦ e ⟨f.1, (mem_sphereBasepointFiber_iff n x f.1).1 f.2⟩ :=
  rfl

/-- Applying `sphereBasepointFiberHomeomorphOf n x e` first forgets that a fiber element is a
fiber element and then applies the supplied based-map-to-loop-space comparison `e`. -/
@[simp] theorem sphereBasepointFiberHomeomorphOf_apply
    (n : ℕ) (x : X) (e : sphereBasepointBasedMapSpace n x ≃ₜ Ω^ (Fin n) X x)
    (f : sphereBasepointFiber n x) :
    sphereBasepointFiberHomeomorphOf n x e f =
      e ⟨f.1, (mem_sphereBasepointFiber_iff n x f.1).1 f.2⟩ :=
  rfl

/-- The inverse of `sphereBasepointFiberHomeomorphOf n x e` is obtained by first applying `e.symm`
and then viewing the resulting based map as a point of the evaluation fiber over `x`. -/
@[simp] theorem sphereBasepointFiberHomeomorphOf_symm_apply
    (n : ℕ) (x : X) (e : sphereBasepointBasedMapSpace n x ≃ₜ Ω^ (Fin n) X x)
    (γ : Ω^ (Fin n) X x) :
    (sphereBasepointFiberHomeomorphOf n x e).symm γ =
      ⟨(e.symm γ).1, (mem_sphereBasepointFiber_iff n x (e.symm γ).1).2 (e.symm γ).2⟩ :=
  rfl
