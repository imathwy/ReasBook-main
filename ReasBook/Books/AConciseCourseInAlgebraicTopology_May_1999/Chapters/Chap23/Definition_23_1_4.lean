import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.VectorBundle.Constructions
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_1_1

noncomputable section

open Bundle
open scoped Topology

universe u v w

-- Semantic recall via `lean_leansearch`: `VectorBundle.pullback` is the canonical pullback API,
-- and Definition 23.1.1 uses the ambient owner `VectorBundle ℝ (Fin n → ℝ) E` for real
-- `n`-plane bundles rather than a separate wrapper.

/-- Pullback along a map inherits the additive commutative group structure fiberwise. -/
instance continuousMapPullbackAddCommGroup
    {B : Type u} {B' : Type v} (f : B' → B) (E : B → Type w)
    [∀ b, AddCommGroup (E b)] (x : B') :
    AddCommGroup ((f *ᵖ E) x) :=
  show AddCommGroup (E (f x)) from inferInstance

/-- Pullback along a map inherits the module structure fiberwise. -/
instance continuousMapPullbackModule
    {R : Type u} [Semiring R] {B : Type v} {B' : Type w} (f : B' → B) (E : B → Type _)
    [∀ b, AddCommGroup (E b)] [∀ b, Module R (E b)] (x : B') :
    Module R ((f *ᵖ E) x) :=
  show Module R (E (f x)) from inferInstance

/-- Pullback along a continuous map inherits the module structure fiberwise in the coercion shape
used by `ContinuousMap` pullbacks. -/
instance continuousMapCoePullbackModule
    {R : Type u} [Semiring R] {B : Type v} [TopologicalSpace B]
    {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) (E : B → Type _)
    [∀ b, AddCommGroup (E b)] [∀ b, Module R (E b)] (x : B') :
    Module R ((⇑f *ᵖ E) x) :=
  continuousMapPullbackModule f E x

/-- Pullback along a continuous map inherits the family of module structures needed by
`RealPlaneBundleIso` and related bundle APIs. -/
instance continuousMapCoePullbackModules
    {R : Type u} [Semiring R] {B : Type v} [TopologicalSpace B]
    {B' : Type w} [TopologicalSpace B'] (f : C(B', B)) (E : B → Type _)
    [∀ b, AddCommGroup (E b)] [∀ b, Module R (E b)] :
    ∀ x : B', Module R ((⇑f *ᵖ E) x) :=
  fun x ↦ continuousMapCoePullbackModule f E x

/-- A fiberwise continuous linear equivalence between two real `n`-plane bundles over the same
base. -/
structure RealPlaneBundleIso
    (n : ℕ) (B : Type u) [TopologicalSpace B]
    (E E' : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E')]
    [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (E b)] [∀ b, AddCommGroup (E' b)]
    [∀ b, Module ℝ (E b)] [∀ b, Module ℝ (E' b)] where
  /-- The fiberwise linear equivalence. -/
  toContinuousLinearEquiv (b : B) : E b ≃L[ℝ] E' b
  /-- Continuity of the induced map on total spaces. -/
  continuous_toFun : Continuous fun z : Bundle.TotalSpace (Fin n → ℝ) E ↦
    @Bundle.TotalSpace.mk B (Fin n → ℝ) E' z.1 (toContinuousLinearEquiv z.1 z.2)
  /-- Continuity of the inverse induced map on total spaces. -/
  continuous_invFun : Continuous fun z : Bundle.TotalSpace (Fin n → ℝ) E' ↦
    @Bundle.TotalSpace.mk B (Fin n → ℝ) E z.1 ((toContinuousLinearEquiv z.1).symm z.2)

/-- A bundle isomorphism acts on total spaces by its fiberwise continuous linear equivalences. -/
instance realPlaneBundleIsoCoeFun
    {n : ℕ} {B : Type u} [TopologicalSpace B] {E E' : B → Type v}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E')]
    [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (E b)] [∀ b, AddCommGroup (E' b)]
    [∀ b, Module ℝ (E b)] [∀ b, Module ℝ (E' b)] :
    CoeFun (RealPlaneBundleIso n B E E') fun _ ↦
      Bundle.TotalSpace (Fin n → ℝ) E → Bundle.TotalSpace (Fin n → ℝ) E' where
  coe η z :=
    @Bundle.TotalSpace.mk B (Fin n → ℝ) E' z.1 (η.toContinuousLinearEquiv z.1 z.2)

/-- A pullback of the universal bundle carries the fiberwise structures needed to speak about a
bundle isomorphism with a real `n`-plane bundle over the source. -/
abbrev pullbackRealPlaneBundleIso
    (n : ℕ) {X : Type u} [TopologicalSpace X] (E : X → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ x, TopologicalSpace (E x)] [FiberBundle (Fin n → ℝ) E]
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    {BO : Type w} [TopologicalSpace BO] (f : ContinuousMap X BO) (γ : BO → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)] :
    Type _ :=
  @RealPlaneBundleIso n X _ E (f *ᵖ γ)
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    (fun x ↦ continuousMapPullbackAddCommGroup f γ x)
    inferInstance
    (fun x ↦ show Module ℝ (γ (f x)) from inferInstance)

/-- The type of bundle isomorphisms between the pullbacks of a fixed real `n`-plane bundle along
two maps with common source and target. -/
abbrev PullbackRealPlaneBundleIso
    (n : ℕ) {X : Type u} [TopologicalSpace X] {B : Type v} [TopologicalSpace B]
    (E : B → Type w) [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    (f₀ f₁ : ContinuousMap X B) : Type _ :=
  @RealPlaneBundleIso n X _ (f₀ *ᵖ E) (f₁ *ᵖ E) _ _ _ _
    (fun x ↦ continuousMapPullbackAddCommGroup f₀ E x)
    (fun x ↦ continuousMapPullbackAddCommGroup f₁ E x)
    (continuousMapCoePullbackModules f₀ E)
    (continuousMapCoePullbackModules f₁ E)

/-- Definition 23.1.4. A classifying space `BO(n)` for real `n`-plane bundles is represented by a
base space together with a universal real `n`-plane bundle `γ`, such that every real `n`-plane
bundle is isomorphic to a pullback `f *ᵖ γ` along some continuous map `f`. The chapter API also
records the corresponding uniqueness-up-to-homotopy property used in Theorem 23.1.5. -/
class RealPlaneBundleClassifyingSpace
    (n : ℕ) (BO : Type u) [TopologicalSpace BO] (γ : BO → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
    extends VectorBundle ℝ (Fin n → ℝ) γ where
  /-- Every real `n`-plane bundle is isomorphic to a pullback of the universal bundle. -/
  classifies {X : Type w} [TopologicalSpace X] (E : X → Type v)
      [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
      [∀ x, TopologicalSpace (E x)] [FiberBundle (Fin n → ℝ) E]
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
      [VectorBundle ℝ (Fin n → ℝ) E] :
      ∃ f : C(X, BO), Nonempty (pullbackRealPlaneBundleIso n E f γ)
  /-- Pullbacks of the universal bundle determine the classifying map uniquely up to homotopy. -/
  unique {X : Type u} [TopologicalSpace X] {f₀ f₁ : C(X, BO)}
      (hIso : Nonempty (PullbackRealPlaneBundleIso n γ f₀ f₁)) :
      ContinuousMap.Homotopic f₀ f₁

/-- A real `n`-plane bundle classifying space carries the canonical vector-bundle structure on its
universal bundle. -/
instance realPlaneBundleClassifyingSpaceToVectorBundle
    {n : ℕ} {BO : Type u} [TopologicalSpace BO] {γ : BO → Type v}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℝ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
    [h : RealPlaneBundleClassifyingSpace n BO γ] :
    VectorBundle ℝ (Fin n → ℝ) γ :=
  h.toVectorBundle
