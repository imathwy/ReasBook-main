import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Bundle
open scoped LinearAlgebra.Projectivization

-- Semantic recall via `lean_leansearch`: mathlib provides projectivization `ℙ 𝕜 V`, and
-- `Bundle.TotalSpace` is the canonical owner for the total space of a fiberwise construction.
-- The companion API here keeps the source-facing projective bundle while publicizing the ambient
-- topological surface and the tautological line family used throughout the rest of Chapter 24.

section

variable {X : Type u}
variable [TopologicalSpace X]
variable {n : ℕ} (E : ComplexPlaneBundle.{u, v} n X)

/-- The fiberwise projectivization of the complex `n`-plane bundle `E`. -/
abbrev projectiveBundleFiber : X → Type v :=
  fun x ↦ ℙ ℂ (E.fiber x)

/-- Each fiber `ℙ ℂ (E x)` carries the quotient topology inherited from the fiber `E x`. -/
noncomputable instance projectiveBundleFiber_topologicalSpace (x : X) :
    TopologicalSpace (projectiveBundleFiber E x) :=
  by
    change TopologicalSpace (Projectivization ℂ (E.fiber x))
    delta Projectivization
    infer_instance

/-- Definition 24.3.1: for a complex `n`-plane bundle `E` over `X`, the projective bundle
`P(E) → X` is the total space whose fiber over `x : X` is the projective space
`ℙ ℂ (E x)` of complex lines in the fiber `E x`. -/
abbrev ProjectiveBundle :=
  Bundle.TotalSpace (ℙ ℂ (Fin n → ℂ)) (projectiveBundleFiber E)

namespace ProjectiveBundleNotation

scoped notation "P(" E ")" => ProjectiveBundle E

end ProjectiveBundleNotation

open scoped ProjectiveBundleNotation

/-- The total space of `P(E)` identifies with the sigma-type of its fiberwise projective
spaces. -/
abbrev projectiveBundleToSigma :
    P(E) → Σ x : X, projectiveBundleFiber E x :=
  fun p ↦ ⟨p.proj, p.2⟩

/-- `P(E)` carries the canonical total-space topology induced from the base and the
fiberwise quotient topologies on `ℙ ℂ (E x)`. -/
noncomputable instance projectiveBundle_topologicalSpace :
    TopologicalSpace (P(E)) :=
  TopologicalSpace.induced (projectiveBundleToSigma E) inferInstance

/-- `P(E)` is the total space of the fiberwise projectivization
`x ↦ ℙ ℂ (E x)`. -/
theorem projectiveBundle_def :
    P(E) = Bundle.TotalSpace (ℙ ℂ (Fin n → ℂ)) (projectiveBundleFiber E) := rfl

/-- The canonical projection `P(E) → X` from the projective bundle to its base. -/
abbrev projectiveBundleProj : P(E) → X :=
  Bundle.TotalSpace.proj

/-- The projective-bundle projection `P(E) → X` is continuous for the canonical total-space
topology on `P(E)`. -/
theorem projectiveBundleProj_continuous :
    Continuous (projectiveBundleProj E) := by
  have hfst : Continuous (Sigma.fst : (Σ x : X, projectiveBundleFiber E x) → X) := by
    refine continuous_def.2 fun s hs ↦ ?_
    simpa using isOpen_sigma_fst_preimage s
  simpa [projectiveBundleProj, projectiveBundleToSigma] using
    hfst.comp (continuous_induced_dom : Continuous (projectiveBundleToSigma E))

/-- The projective-bundle projection sends the point represented by a complex line in `E x` back
to `x`. -/
@[simp] theorem projectiveBundleProj_mk (x : X) (L : projectiveBundleFiber E x) :
    projectiveBundleProj E (⟨x, L⟩ : P(E)) = x := rfl

/-- The tautological complex line over `P(E)`, whose fiber over `p` is the complex
line represented by `p`. -/
abbrev projectiveBundleTautologicalLine :
    P(E) → Type v :=
  fun p ↦ p.2.submodule

/-- Each fiber of the tautological line inherits its subspace topology. -/
instance projectiveBundleTautologicalLine_topologicalSpace (p : P(E)) :
    TopologicalSpace (projectiveBundleTautologicalLine E p) :=
  inferInstance

/-- The total space of the tautological line identifies with the sigma-type of its fibers. -/
abbrev projectiveBundleTautologicalLineToSigma :
    Bundle.TotalSpace (Fin 1 → ℂ) (projectiveBundleTautologicalLine E) →
      Σ p : P(E), projectiveBundleTautologicalLine E p :=
  fun q ↦ ⟨q.proj, q.2⟩

/-- The total space of the tautological line carries the canonical sigma-type topology induced
from `P(E)` and its fiberwise subspace topologies. -/
noncomputable instance projectiveBundleTautologicalLine_totalSpaceTopologicalSpace :
    TopologicalSpace (Bundle.TotalSpace (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)) := by
  exact TopologicalSpace.induced (projectiveBundleTautologicalLineToSigma E) inferInstance

/-- Each fiber of the tautological line is an additive commutative group. -/
noncomputable instance projectiveBundleTautologicalLine_addCommGroup (p : P(E)) :
    AddCommGroup (projectiveBundleTautologicalLine E p) :=
  inferInstance

/-- Each fiber of the tautological line is a complex vector space. -/
noncomputable instance projectiveBundleTautologicalLine_module (p : P(E)) :
    Module ℂ (projectiveBundleTautologicalLine E p) :=
  inferInstance

/-- The tautological complex line bundle on `P(E)`, viewed as a rank-`1` complex
plane bundle once the ambient bundle structure on the tautological family is fixed. -/
noncomputable abbrev projectiveBundleTautologicalLineBundle
    [FiberBundle (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
    [VectorBundle ℂ (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)] :
    ComplexPlaneBundle 1 (P(E)) where
  fiber := projectiveBundleTautologicalLine E
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := inferInstance
  fiber_module := inferInstance
  vectorBundle := inferInstance

/-- The isomorphism class of the tautological complex line bundle on `P(E)`. -/
noncomputable abbrev projectiveBundleTautologicalLineBundleClass
    [FiberBundle (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)]
    [VectorBundle ℂ (Fin 1 → ℂ) (projectiveBundleTautologicalLine E)] :
    ComplexPlaneBundle.classes 1 (P(E)) :=
  ComplexPlaneBundle.classOf (projectiveBundleTautologicalLineBundle E)

/-- The fiber of `projectiveBundleProj E` over `x` is canonically the projective space
`ℙ ℂ (E x)`. -/
def projectiveBundleFiberEquiv (x : X) :
    {p : P(E) // projectiveBundleProj E p = x} ≃ projectiveBundleFiber E x where
  toFun p := by
    rcases p with ⟨⟨x', L⟩, hx⟩
    cases hx
    exact L
  invFun L := ⟨(⟨x, L⟩ : P(E)), rfl⟩
  left_inv p := by
    rcases p with ⟨⟨x', L⟩, hx⟩
    cases hx
    rfl
  right_inv L := rfl

end
