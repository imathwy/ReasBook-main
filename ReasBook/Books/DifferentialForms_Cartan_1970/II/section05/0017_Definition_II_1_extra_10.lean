import Mathlib

open scoped unitInterval

universe u

/- Definition II.1-extra-10: homotopy of paths with fixed endpoints is the existing mathlib
relation `Path.Homotopic`, i.e. existence of a `Path.Homotopy` between two paths with the same
initial point and endpoint. -/
#check Path.Homotopic

variable {X : Type u} [TopologicalSpace X]

/-- A closed path in `X` is a continuous map `I → X` whose endpoints agree. -/
def IsClosedPath (γ : C(I, X)) : Prop :=
  γ 0 = γ 1

/-- The loop based at `γ 0` canonically attached to a closed path `γ`. -/
def IsClosedPath.toPath {γ : C(I, X)} (hγ : IsClosedPath γ) : Path (γ 0) (γ 0) :=
  Path.mk γ rfl hγ.symm

@[simp]
theorem IsClosedPath.toPath_toContinuousMap {γ : C(I, X)} (hγ : IsClosedPath γ) :
    hγ.toPath.toContinuousMap = γ :=
  rfl

/-- Constant maps on `I` are closed paths. -/
theorem isClosedPath_const (x : X) : IsClosedPath (ContinuousMap.const I x) := by
  simp [IsClosedPath]

/-- The subtype of closed paths in `X`, packaged from the canonical owner `IsClosedPath`. -/
abbrev ClosedPath (X : Type u) [TopologicalSpace X] :=
  {γ : C(I, X) // IsClosedPath γ}

namespace ClosedPath

/-- The loop canonically attached to a packaged closed path. -/
def toPath (γ : ClosedPath X) : Path ((γ : C(I, X)) 0) ((γ : C(I, X)) 0) :=
  γ.2.toPath

@[simp]
theorem toPath_toContinuousMap (γ : ClosedPath X) :
    (ClosedPath.toPath γ).toContinuousMap = (γ : C(I, X)) :=
  rfl

@[simp]
theorem toPath_apply (γ : ClosedPath X) (t : I) : γ.toPath t = (γ : C(I, X)) t :=
  rfl

@[simp]
theorem range_toPath (γ : ClosedPath X) : Set.range γ.toPath = Set.range (γ : C(I, X)) :=
  rfl

end ClosedPath

namespace Path

/-- Every loop in the path sense is a closed path in the chapter's sense. -/
theorem isClosedPath {x : X} (γ : Path x x) : IsClosedPath (γ : C(I, X)) := by
  simp [IsClosedPath]

/-- Every loop canonically determines a packaged closed path. -/
def toClosedPath {x : X} (γ : Path x x) : ClosedPath X :=
  ⟨γ, γ.isClosedPath⟩

end Path

/-- A closed path in `D` is a closed path whose image is contained in `D`. -/
def IsClosedPathIn (D : Set X) (γ : C(I, X)) : Prop :=
  IsClosedPath γ ∧ Set.range γ ⊆ D

/-- A closed path in `D` is exactly a closed path whose every point lies in `D`. -/
theorem isClosedPathIn_iff_forall {D : Set X} {γ : C(I, X)} :
    IsClosedPathIn D γ ↔ IsClosedPath γ ∧ ∀ t : I, γ t ∈ D := by
  constructor
  · rintro ⟨hγ, hD⟩
    exact ⟨hγ, fun t ↦ hD ⟨t, rfl⟩⟩
  · rintro ⟨hγ, hD⟩
    refine ⟨hγ, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hD t

/-- A closed path in the complement of `D` is exactly a closed path avoiding `D` pointwise. -/
theorem isClosedPathIn_compl_iff {D : Set X} {γ : C(I, X)} :
    IsClosedPathIn Dᶜ γ ↔ IsClosedPath γ ∧ ∀ t : I, γ t ∉ D := by
  rw [isClosedPathIn_iff_forall]
  simp

/-- Two maps `I → X` are homotopic through closed paths contained in `D`. -/
abbrev ClosedPathHomotopicIn (D : Set X) (γ₀ γ₁ : C(I, X)) : Prop :=
  ContinuousMap.HomotopicWith γ₀ γ₁ (IsClosedPathIn D)

/-- Every closed path is homotopic to itself as a closed path. -/
theorem closedPathHomotopic_refl {γ : C(I, X)} (hγ : IsClosedPath γ) :
    ContinuousMap.HomotopicWith γ γ IsClosedPath :=
  ContinuousMap.HomotopicWith.refl γ hγ

/-- Constant maps on `I` with value in `D` are closed paths in `D`. -/
theorem isClosedPathIn_const {D : Set X} {x : X} (hx : x ∈ D) :
    IsClosedPathIn D (ContinuousMap.const I x) := by
  refine ⟨isClosedPath_const x, ?_⟩
  rintro _ ⟨t, rfl⟩
  simpa using hx

/-- Every closed path in `D` is homotopic to itself through closed paths in `D`. -/
theorem closedPathHomotopicIn_refl {D : Set X} {γ : C(I, X)} (hγ : IsClosedPathIn D γ) :
    ClosedPathHomotopicIn D γ γ :=
  ContinuousMap.HomotopicWith.refl γ hγ

/-- A closed path is homotopic to a point if it is homotopic through closed paths to a constant
path. -/
def IsNullHomotopicClosedPath (γ : C(I, X)) : Prop :=
  ∃ x : X, ContinuousMap.HomotopicWith γ (ContinuousMap.const I x) IsClosedPath

/-- A closed path in `D` is null-homotopic in `D` if it is homotopic through closed paths in `D`
to a constant path with value in `D`. -/
def IsNullHomotopicClosedPathIn (D : Set X) (γ : C(I, X)) : Prop :=
  ∃ x ∈ D, ClosedPathHomotopicIn D γ (ContinuousMap.const I x)

/-- Every constant path is homotopic to a point as a closed path. -/
theorem isNullHomotopicClosedPath_const (x : X) :
    IsNullHomotopicClosedPath (ContinuousMap.const I x) :=
  ⟨x, closedPathHomotopic_refl (isClosedPath_const x)⟩

/-- Every constant path with value in `D` is null-homotopic in `D`. -/
theorem isNullHomotopicClosedPathIn_const {D : Set X} {x : X} (hx : x ∈ D) :
    IsNullHomotopicClosedPathIn D (ContinuousMap.const I x) :=
  ⟨x, hx, closedPathHomotopicIn_refl (isClosedPathIn_const hx)⟩
