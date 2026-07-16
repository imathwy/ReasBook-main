import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Basic

noncomputable section

universe u v w

namespace Rockafellar
end Rockafellar

open scoped Rockafellar

namespace Bifunction

/-- Canonical pointwise lift of a finite-valued bifunction into `WithTopBot`. -/
abbrev toWithTopBot {U V α : Type*} (K : U → V → α) : U → V → WithTopBot α :=
  fun u v ↦ (K u v : WithTopBot α)

section

variable {U : Type u} {V : Type v} {β : Type w}
variable {C : Set U} {D : Set V}
variable [Bot β] [Top β]

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage:

- `source-facing`: Definition33.0.2 introduces two ambient bifunctions obtained from a
  bifunction defined only on `C × D`: the lower and upper simple extensions.
- `core/canonical`: there is no earlier project bifunction owner for this two-sided extension
  pattern. The closest unary analogue is `Function.toWithTopBotOn`, while the canonical codomain
  lift for the bridge-to-ambient finite kernels is `Bifunction.toWithTopBot`.
- `bridge/view`: the restricted bridge is expressed directly as
  `lowerSimpleExtension (toWithTopBot K)` / `upperSimpleExtension (toWithTopBot K)` for
  `K : C → D → α`; the ambient total-kernel forms `saddleExtension` and
  `upperBoundaryExtension` are thin restriction views.

Domain-style sampling used here:
- `Bifunction.toWithTopBot` from `Chap01.EOrder.Basic`;
- `Function.toWithTopBotOn` from `Chap01.Remark_4_4_5`;
- `Bifunction.feasibleSet` from `Chap06.Definition_6_29_16`;
- `Bifunction.closure` from `Chap06.Definition_6_29_24`.

Primitive data vs derived API:
- primitive source data: a bifunction `K : C → D → β` on a codomain carrying `⊥` and `⊤`;
- primitive owners: `lowerSimpleExtension K` and `upperSimpleExtension K`;
- derived API: agreement with `K` on `C × D` and the ambient total-kernel bridge abbreviations
  `saddleExtension`/`upperBoundaryExtension`, obtained by restriction plus the canonical codomain
  lift `toWithTopBot`.

Ambient-assumption minimization:
- only the extremal values `⊥` and `⊤` are used, so the owner is stated at the minimal codomain
  layer `[Bot β] [Top β]` instead of specializing to a concrete `WithTopBot` model;
- no algebraic, order, topological, or scalar assumptions are needed.
-/

/-- Definition33.0.2 (1): the lower simple extension of a bifunction `K` on `C × D` agrees with
`K` on `C × D`, takes the value `⊤` when `u ∈ C` and `v ∉ D`, and takes the value `⊥` when
`u ∉ C`. -/
def lowerSimpleExtension (K : C → D → β) (u : U) (v : V) :
    β :=
  if hu : u ∈ C then
    if hv : v ∈ D then K ⟨u, hu⟩ ⟨v, hv⟩ else ⊤
  else
    ⊥

-- Proof sketch: this is the definitional unfolding of `lowerSimpleExtension`; the theorem keeps
-- the public API at a reusable `_def`/`_spec` level for later rewriting without exposing the
-- raw definition body directly at every call site.
/-- Defining equation for the lower simple extension. -/
theorem lowerSimpleExtension_def (K : C → D → β) (u : U) (v : V) :
    lowerSimpleExtension K u v =
      if hu : u ∈ C then
        if hv : v ∈ D then K ⟨u, hu⟩ ⟨v, hv⟩ else ⊤
      else
        ⊥ := rfl

/-- The upper simple extension of a bifunction `K` on `C × D` agrees with `K` on `C × D`, takes
the value `⊥` when `u ∉ C` and `v ∈ D`, and takes the value `⊤` when `v ∉ D`. -/
def upperSimpleExtension (K : C → D → β) (u : U) (v : V) :
    β :=
  if hv : v ∈ D then
    if hu : u ∈ C then K ⟨u, hu⟩ ⟨v, hv⟩ else ⊥
  else
    ⊤

-- Proof sketch: unfold `lowerSimpleExtension`; under `hu : u ∈ C` and `hv : v ∈ D`, both
-- conditionals take their finite branch and return the original value `K ⟨u, hu⟩ ⟨v, hv⟩`.
/-- On `C × D`, the lower simple extension evaluates to the original bifunction. -/
@[simp] theorem lowerSimpleExtension_of_mem_of_mem
    (K : C → D → β) {u : U} {v : V} (hu : u ∈ C) (hv : v ∈ D) :
    lowerSimpleExtension K u v = K ⟨u, hu⟩ ⟨v, hv⟩ := by
  simp [lowerSimpleExtension, hu, hv]

-- Proof sketch: unfold `lowerSimpleExtension`; with `hu : u ∈ C` and `hv : v ∉ D`, the outer
-- conditional takes the `u ∈ C` branch and the inner conditional returns `⊤`.
/-- On points with `u ∈ C` and `v ∉ D`, the lower simple extension takes the value `⊤`. -/
@[simp] theorem lowerSimpleExtension_of_mem_of_notMem
    (K : C → D → β) {u : U} {v : V} (hu : u ∈ C) (hv : v ∉ D) :
    lowerSimpleExtension K u v = ⊤ := by
  simp [lowerSimpleExtension, hu, hv]

-- Proof sketch: unfold `lowerSimpleExtension`; if `u ∉ C`, the outer conditional immediately
-- returns `⊥`, independently of `v`.
/-- Outside the first-coordinate domain `C`, the lower simple extension is identically `⊥`. -/
@[simp] theorem lowerSimpleExtension_of_notMem
    (K : C → D → β) {u : U} {v : V} (hu : u ∉ C) :
    lowerSimpleExtension K u v = ⊥ := by
  simp [lowerSimpleExtension, hu]

-- Proof sketch: unfold `upperSimpleExtension`; under `hu : u ∈ C` and `hv : v ∈ D`, both
-- conditionals take their finite branch and return the original value `K ⟨u, hu⟩ ⟨v, hv⟩`.
/-- On `C × D`, the upper simple extension evaluates to the original bifunction. -/
@[simp] theorem upperSimpleExtension_of_mem_of_mem
    (K : C → D → β) {u : U} {v : V} (hu : u ∈ C) (hv : v ∈ D) :
    upperSimpleExtension K u v = K ⟨u, hu⟩ ⟨v, hv⟩ := by
  simp [upperSimpleExtension, hu, hv]

-- Proof sketch: unfold `upperSimpleExtension`; with `hv : v ∈ D` and `hu : u ∉ C`, the outer
-- conditional keeps the `v ∈ D` branch and the inner conditional returns `⊥`.
/-- On points with `u ∉ C` and `v ∈ D`, the upper simple extension takes the value `⊥`. -/
@[simp] theorem upperSimpleExtension_of_notMem_of_mem
    (K : C → D → β) {u : U} {v : V} (hu : u ∉ C) (hv : v ∈ D) :
    upperSimpleExtension K u v = ⊥ := by
  simp [upperSimpleExtension, hu, hv]

-- Proof sketch: unfold `upperSimpleExtension`; if `v ∉ D`, the outer conditional immediately
-- returns `⊤`, independently of `u`.
/-- Outside the second-coordinate domain `D`, the upper simple extension is identically `⊤`. -/
@[simp] theorem upperSimpleExtension_of_notMem
    (K : C → D → β) {u : U} {v : V} (hv : v ∉ D) :
    upperSimpleExtension K u v = ⊤ := by
  simp [upperSimpleExtension, hv]

-- Proof sketch: unfold `lowerSimpleExtension`; for subtype inputs `u : C` and `v : D`, both
-- membership tests reduce to the true branch, so the value is definitionally `K u v`.
/-- On `C × D`, the lower simple extension agrees with the original bifunction. -/
@[simp] theorem lowerSimpleExtension_apply (K : C → D → β) (u : C) (v : D) :
    lowerSimpleExtension K u v = K u v := by
  simp [lowerSimpleExtension]

-- Proof sketch: unfold `upperSimpleExtension`; for subtype inputs `u : C` and `v : D`, both
-- membership tests reduce to the true branch, so the value is definitionally `K u v`.
/-- On `C × D`, the upper simple extension agrees with the original bifunction. -/
@[simp] theorem upperSimpleExtension_apply (K : C → D → β) (u : C) (v : D) :
    upperSimpleExtension K u v = K u v := by
  simp [upperSimpleExtension]

section Bridge

section Intrinsic

variable {γ : Type w}
variable [Bot γ] [Top γ]

/-- The intrinsic ambient lower extension obtained by restricting an already extended-valued kernel
to `C × D` and applying `lowerSimpleExtension`. -/
abbrev saddleExtensionOn (K : U → V → γ) (C : Set U) (D : Set V) : U → V → γ :=
  lowerSimpleExtension (fun u : C ↦ fun v : D ↦ K u v)

/-- The intrinsic ambient upper extension obtained by restricting an already extended-valued kernel
to `C × D` and applying `upperSimpleExtension`. -/
abbrev upperBoundaryExtensionOn (K : U → V → γ) (C : Set U) (D : Set V) : U → V → γ :=
  upperSimpleExtension (fun u : C ↦ fun v : D ↦ K u v)

@[simp] theorem saddleExtensionOn_apply_of_mem
    {K : U → V → γ} {u : U} {v : V} (hu : u ∈ C) (hv : v ∈ D) :
    saddleExtensionOn K C D u v = K u v := by
  simpa [saddleExtensionOn] using
    (lowerSimpleExtension_of_mem_of_mem
      (K := fun u : C ↦ fun v : D ↦ K u v) hu hv)

@[simp] theorem saddleExtensionOn_apply_of_not_mem_left
    {K : U → V → γ} {u : U} {v : V} (hu : u ∉ C) :
    saddleExtensionOn K C D u v = ⊥ := by
  simpa [saddleExtensionOn] using
    (lowerSimpleExtension_of_notMem
      (K := fun u : C ↦ fun v : D ↦ K u v) hu)

@[simp] theorem saddleExtensionOn_apply_of_mem_left_of_not_mem_right
    {K : U → V → γ} {u : U} {v : V} (hu : u ∈ C) (hv : v ∉ D) :
    saddleExtensionOn K C D u v = ⊤ := by
  simpa [saddleExtensionOn] using
    (lowerSimpleExtension_of_mem_of_notMem
      (K := fun u : C ↦ fun v : D ↦ K u v) hu hv)

@[simp] theorem upperBoundaryExtensionOn_apply_of_mem
    {K : U → V → γ} {u : U} {v : V} (hu : u ∈ C) (hv : v ∈ D) :
    upperBoundaryExtensionOn K C D u v = K u v := by
  simpa [upperBoundaryExtensionOn] using
    (upperSimpleExtension_of_mem_of_mem
      (K := fun u : C ↦ fun v : D ↦ K u v) hu hv)

@[simp] theorem upperBoundaryExtensionOn_apply_of_not_mem_left_of_mem_right
    {K : U → V → γ} {u : U} {v : V} (hu : u ∉ C) (hv : v ∈ D) :
    upperBoundaryExtensionOn K C D u v = ⊥ := by
  simpa [upperBoundaryExtensionOn] using
    (upperSimpleExtension_of_notMem_of_mem
      (K := fun u : C ↦ fun v : D ↦ K u v) hu hv)

@[simp] theorem upperBoundaryExtensionOn_apply_of_not_mem_right
    {K : U → V → γ} {u : U} {v : V} (hv : v ∉ D) :
    upperBoundaryExtensionOn K C D u v = ⊤ := by
  simpa [upperBoundaryExtensionOn] using
    (upperSimpleExtension_of_notMem
      (K := fun u : C ↦ fun v : D ↦ K u v) hv)

end Intrinsic

section Finite

variable {α : Type w}

/-- The ambient finite-kernel view of `lowerSimpleExtension`, obtained by restricting `K` to
`C × D` and applying the canonical codomain lift `toWithTopBot`. -/
abbrev saddleExtension (K : U → V → α) (C : Set U) (D : Set V) : U → V → WithTopBot α :=
  saddleExtensionOn (toWithTopBot K) C D

/-- The ambient finite-kernel view of `upperSimpleExtension`, obtained by restricting `K` to
`C × D` and applying the canonical codomain lift `toWithTopBot`. -/
abbrev upperBoundaryExtension (K : U → V → α) (C : Set U) (D : Set V) :
    U → V → WithTopBot α :=
  upperBoundaryExtensionOn (toWithTopBot K) C D

/-- Textbook surface notation for the lower ambient extension `K₁` on `C × D`. -/
scoped[Rockafellar] notation "K₁[" K " | " C ", " D "]" =>
  Bifunction.saddleExtension K C D

/-- Textbook surface notation for the upper ambient extension `K₂` on `C × D`. -/
scoped[Rockafellar] notation "K₂[" K " | " C ", " D "]" =>
  Bifunction.upperBoundaryExtension K C D

@[simp] theorem lowerSimpleExtension_toWithTopBot_of_mem_of_mem
    {K : C → D → α} {u : U} {v : V} (hu : u ∈ C) (hv : v ∈ D) :
    lowerSimpleExtension (toWithTopBot K) u v = toWithTopBot K ⟨u, hu⟩ ⟨v, hv⟩ := by
  simpa using
    (lowerSimpleExtension_of_mem_of_mem (K := toWithTopBot K) hu hv)

@[simp] theorem lowerSimpleExtension_toWithTopBot_of_not_mem
    {K : C → D → α} {u : U} {v : V} (hu : u ∉ C) :
    lowerSimpleExtension (toWithTopBot K) u v = ⊥ := by
  simpa using
    (lowerSimpleExtension_of_notMem (K := toWithTopBot K) hu)

@[simp] theorem lowerSimpleExtension_toWithTopBot_of_mem_of_not_mem
    {K : C → D → α} {u : U} {v : V} (hu : u ∈ C) (hv : v ∉ D) :
    lowerSimpleExtension (toWithTopBot K) u v = ⊤ := by
  simpa using
    (lowerSimpleExtension_of_mem_of_notMem (K := toWithTopBot K) hu hv)

@[simp] theorem upperSimpleExtension_toWithTopBot_of_mem_of_mem
    {K : C → D → α} {u : U} {v : V} (hu : u ∈ C) (hv : v ∈ D) :
    upperSimpleExtension (toWithTopBot K) u v = toWithTopBot K ⟨u, hu⟩ ⟨v, hv⟩ := by
  simpa using
    (upperSimpleExtension_of_mem_of_mem (K := toWithTopBot K) hu hv)

@[simp] theorem upperSimpleExtension_toWithTopBot_of_not_mem_of_mem
    {K : C → D → α} {u : U} {v : V} (hu : u ∉ C) (hv : v ∈ D) :
    upperSimpleExtension (toWithTopBot K) u v = ⊥ := by
  simpa using
    (upperSimpleExtension_of_notMem_of_mem (K := toWithTopBot K) hu hv)

@[simp] theorem upperSimpleExtension_toWithTopBot_of_not_mem
    {K : C → D → α} {u : U} {v : V} (hv : v ∉ D) :
    upperSimpleExtension (toWithTopBot K) u v = ⊤ := by
  simpa using
    (upperSimpleExtension_of_notMem (K := toWithTopBot K) hv)

@[simp] theorem saddleExtension_apply_of_mem
    {K : U → V → α} {u : U} {v : V} (hu : u ∈ C) (hv : v ∈ D) :
    K₁[K | C, D] u v = toWithTopBot K u v := by
  simpa [saddleExtension] using
    (saddleExtensionOn_apply_of_mem (K := toWithTopBot K) (C := C) (D := D) hu hv)

@[simp] theorem saddleExtension_apply_of_not_mem_left
    {K : U → V → α} {u : U} {v : V} (hu : u ∉ C) :
    K₁[K | C, D] u v = ⊥ := by
  simpa [saddleExtension] using
    (saddleExtensionOn_apply_of_not_mem_left (K := toWithTopBot K) (C := C) (D := D) hu)

@[simp] theorem saddleExtension_apply_of_mem_left_of_not_mem_right
    {K : U → V → α} {u : U} {v : V} (hu : u ∈ C) (hv : v ∉ D) :
    K₁[K | C, D] u v = ⊤ := by
  simpa [saddleExtension] using
    (saddleExtensionOn_apply_of_mem_left_of_not_mem_right
      (K := toWithTopBot K) (C := C) (D := D) hu hv)

@[simp] theorem upperBoundaryExtension_apply_of_mem
    {K : U → V → α} {u : U} {v : V} (hu : u ∈ C) (hv : v ∈ D) :
    K₂[K | C, D] u v = toWithTopBot K u v := by
  simpa [upperBoundaryExtension] using
    (upperBoundaryExtensionOn_apply_of_mem (K := toWithTopBot K) (C := C) (D := D) hu hv)

@[simp] theorem upperBoundaryExtension_apply_of_not_mem_left_of_mem_right
    {K : U → V → α} {u : U} {v : V} (hu : u ∉ C) (hv : v ∈ D) :
    K₂[K | C, D] u v = ⊥ := by
  simpa [upperBoundaryExtension] using
    (upperBoundaryExtensionOn_apply_of_not_mem_left_of_mem_right
      (K := toWithTopBot K) (C := C) (D := D) hu hv)

@[simp] theorem upperBoundaryExtension_apply_of_not_mem_right
    {K : U → V → α} {u : U} {v : V} (hv : v ∉ D) :
    K₂[K | C, D] u v = ⊤ := by
  simpa [upperBoundaryExtension] using
    (upperBoundaryExtensionOn_apply_of_not_mem_right
      (K := toWithTopBot K) (C := C) (D := D) hv)

end Finite

end Bridge

end

end Bifunction
