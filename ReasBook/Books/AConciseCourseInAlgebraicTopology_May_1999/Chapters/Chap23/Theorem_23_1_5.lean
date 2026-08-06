import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Lemma_22_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Proposition_23_1_3

noncomputable section

open Bundle
open scoped Topology

universe u v w

-- Semantic recall via `lean_leansearch` did not surface a chapter-level vector-bundle
-- classification theorem; local precedent shows that `homotopyClasses X BO` is the canonical
-- owner for `[X, BO]`, and pullback along continuous maps is the right contravariant action on
-- bundle classes.

section

variable {n : ℕ}
variable {B : Type u} [TopologicalSpace B]
variable {B' : Type u} [TopologicalSpace B']

/-- A bundled compatibility view of a real `n`-plane bundle over `B`. The classification API in
this file is carried by `RealPlaneBundle.classes` and `RealPlaneBundle.classOf` on raw
`Fin n → ℝ`-modeled vector-bundle families, while this structure is the reusable owner for later
constructions that genuinely need a bundled family. -/
structure RealPlaneBundle (n : ℕ) (B : Type u) [TopologicalSpace B] where
  /-- The fiber family over `B`. -/
  fiber : B → Type v
  /-- The topology on the total space. -/
  totalSpace_topology : TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) fiber)
  /-- The fiberwise topologies. -/
  fiber_topology (b : B) : TopologicalSpace (fiber b)
  /-- The local triviality data. -/
  fiberBundle : FiberBundle (Fin n → ℝ) fiber
  /-- The fiberwise additive commutative group structure. -/
  fiber_addCommGroup (b : B) : AddCommGroup (fiber b)
  /-- The fiberwise real vector-space structure. -/
  fiber_module (b : B) : Module ℝ (fiber b)
  /-- The vector-bundle structure with model fiber `Fin n → ℝ`. -/
  vectorBundle : VectorBundle ℝ (Fin n → ℝ) fiber

attribute [instance] RealPlaneBundle.totalSpace_topology
attribute [instance] RealPlaneBundle.fiber_topology
attribute [instance] RealPlaneBundle.fiberBundle
attribute [instance] RealPlaneBundle.fiber_addCommGroup
attribute [instance] RealPlaneBundle.fiber_module
attribute [instance] RealPlaneBundle.vectorBundle

namespace RealPlaneBundle

/-- A bundled real `n`-plane bundle may be used as its underlying fiber family. -/
instance : CoeFun (RealPlaneBundle n B) fun _ ↦ B → Type v where
  coe E := E.fiber

/-- Bundle a raw `Fin n → ℝ`-modeled vector-bundle family into the Chapter 23 owner
`RealPlaneBundle n B`. -/
def ofFamily (n : ℕ) {B : Type u} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    RealPlaneBundle n B where
  fiber := E
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := inferInstance
  fiber_module := inferInstance
  vectorBundle := inferInstance

/-- A chosen `Fin (n + m) → ℝ`-modeled Whitney sum of two bundled real plane bundles over the
same base. -/
def whitneySum
    {n m : ℕ} {B : Type u} [TopologicalSpace B]
    (E₁ : RealPlaneBundle.{u, v} n B) (E₂ : RealPlaneBundle.{u, v} m B)
    [TopologicalSpace (Bundle.TotalSpace (Fin (n + m) → ℝ) (E₁.fiber ×ᵇ E₂.fiber))]
    [FiberBundle (Fin (n + m) → ℝ) (E₁.fiber ×ᵇ E₂.fiber)]
    [VectorBundle ℝ (Fin (n + m) → ℝ) (E₁.fiber ×ᵇ E₂.fiber)] :
    RealPlaneBundle (n + m) B where
  fiber := E₁.fiber ×ᵇ E₂.fiber
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := inferInstance
  fiber_module := inferInstance
  vectorBundle := inferInstance

/-- Internal representatives for the quotient `E_n(B)` of real `n`-plane bundles over `B`. The
public API stays on raw fiber families with ambient `VectorBundle ℝ (Fin n → ℝ) E` structure. -/
private structure Model (n : ℕ) (B : Type u) [TopologicalSpace B] where
  fiber : B → Type v
  totalSpace_topology : TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) fiber)
  fiber_topology : ∀ b, TopologicalSpace (fiber b)
  fiberBundle : FiberBundle (Fin n → ℝ) fiber
  fiber_addCommGroup : ∀ b, AddCommGroup (fiber b)
  fiber_module : ∀ b, Module ℝ (fiber b)
  vectorBundle : VectorBundle ℝ (Fin n → ℝ) fiber

attribute [instance] Model.totalSpace_topology
attribute [instance] Model.fiber_topology
attribute [instance] Model.fiberBundle
attribute [instance] Model.fiber_addCommGroup
attribute [instance] Model.fiber_module
attribute [instance] Model.vectorBundle

/-- Internal constructor from a raw family carrying the canonical vector-bundle owner. -/
private def Model.ofFamily (n : ℕ) {B : Type u} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    Model n B where
  fiber := E
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := inferInstance
  fiber_module := inferInstance
  vectorBundle := inferInstance

/-- Internal pullback representative for bundle classes. -/
private def Model.pullback (n : ℕ) {B : Type u} [TopologicalSpace B] {B' : Type u}
    [TopologicalSpace B'] (E : Model n B) (f : C(B', B)) :
    Model n B' where
  fiber := f *ᵖ E.fiber
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := fun x ↦ continuousMapPullbackAddCommGroup f E.fiber x
  fiber_module := continuousMapCoePullbackModules f E.fiber
  vectorBundle := (VectorBundle.pullback ℝ f :
    VectorBundle ℝ (Fin n → ℝ) (f *ᵖ E.fiber))

/-- Bundle isomorphism is an equivalence relation on real `n`-plane bundle representatives. -/
private theorem iso_equivalence (n : ℕ) (B : Type u) [TopologicalSpace B] :
    Equivalence
      (fun E E' : Model.{u, v} n B ↦ Nonempty (RealPlaneBundleIso n B E.fiber E'.fiber)) := sorry

/-- The setoid of internal representatives of real `n`-plane bundles modulo bundle isomorphism. -/
private def setoid (n : ℕ) (B : Type u) [TopologicalSpace B] : Setoid (Model.{u, v} n B) where
  r E E' := Nonempty (RealPlaneBundleIso n B E.fiber E'.fiber)
  iseqv := iso_equivalence n B

/-- The type `E_n(B)` of real `n`-plane bundles over `B` modulo bundle isomorphism. -/
abbrev classes (n : ℕ) (B : Type u) [TopologicalSpace B] :=
  Quotient (setoid n B)

/-- The isomorphism class of a real `n`-plane bundle family `E : B → Type*`. -/
def classOf (n : ℕ) {B : Type u} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    classes n B :=
  Quotient.mk (setoid n B) (Model.ofFamily n E)

/-- The class of the pullback of `E` along `f`. The pullback family itself remains the canonical
owner; this declaration only packages the induced class in `E_n(B')`. -/
def pullbackClass (n : ℕ) {B : Type u} [TopologicalSpace B] {B' : Type u} [TopologicalSpace B']
    (f : C(B', B)) (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    classes n B' :=
  Quotient.mk (setoid n B') (Model.pullback n (Model.ofFamily n E) f)

/-- A family-level construction descends to `E_n(B)` once it is invariant under real bundle
isomorphism. -/
noncomputable def liftClasses (n : ℕ) {B : Type u} [TopologicalSpace B] {β : Sort*}
    (f :
      ∀ (E : B → Type v), [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [∀ b, TopologicalSpace (E b)] → [FiberBundle (Fin n → ℝ) E] →
        [∀ b, AddCommGroup (E b)] → [∀ b, Module ℝ (E b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] → β)
    (h :
      ∀ {E E' : B → Type v}, [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E')] →
        [∀ b, TopologicalSpace (E b)] → [∀ b, TopologicalSpace (E' b)] →
        [FiberBundle (Fin n → ℝ) E] → [FiberBundle (Fin n → ℝ) E'] →
        [∀ b, AddCommGroup (E b)] → [∀ b, AddCommGroup (E' b)] →
        [∀ b, Module ℝ (E b)] → [∀ b, Module ℝ (E' b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] → [VectorBundle ℝ (Fin n → ℝ) E'] →
        RealPlaneBundleIso n B E E' → f E = f E') :
    classes n B → β :=
  Quotient.lift
    (fun E : Model n B ↦ f E.fiber)
    (fun E E' hEE' ↦ by
      rcases hEE' with ⟨e⟩
      exact h e)

/-- Evaluating `liftClasses` on the class of a bundle family recovers the original family-level
construction. -/
@[simp] theorem liftClasses_classOf (n : ℕ) {B : Type u} [TopologicalSpace B] {β : Sort*}
    (f :
      ∀ (E : B → Type v), [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [∀ b, TopologicalSpace (E b)] → [FiberBundle (Fin n → ℝ) E] →
        [∀ b, AddCommGroup (E b)] → [∀ b, Module ℝ (E b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] → β)
    (h :
      ∀ {E E' : B → Type v}, [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E')] →
        [∀ b, TopologicalSpace (E b)] → [∀ b, TopologicalSpace (E' b)] →
        [FiberBundle (Fin n → ℝ) E] → [FiberBundle (Fin n → ℝ) E'] →
        [∀ b, AddCommGroup (E b)] → [∀ b, AddCommGroup (E' b)] →
        [∀ b, Module ℝ (E b)] → [∀ b, Module ℝ (E' b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] → [VectorBundle ℝ (Fin n → ℝ) E'] →
        RealPlaneBundleIso n B E E' → f E = f E')
    (E : B → Type v) [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    liftClasses n f h (classOf n E) = f E :=
  rfl

/-- Proposition-valued statements about `E_n(B)` may be proved by choosing a representative
bundle family. -/
@[elab_as_elim] theorem inductionOnClasses (n : ℕ) {B : Type u} [TopologicalSpace B]
    {motive : classes n B → Prop} (ξ : classes n B)
    (h :
      ∀ (E : B → Type v), [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] →
        [∀ b, TopologicalSpace (E b)] → [FiberBundle (Fin n → ℝ) E] →
        [∀ b, AddCommGroup (E b)] → [∀ b, Module ℝ (E b)] →
        [VectorBundle ℝ (Fin n → ℝ) E] → motive (classOf n E)) :
    motive ξ :=
  Quotient.inductionOn ξ (fun E : Model n B ↦ h E.fiber)

/-- Isomorphic real `n`-plane bundles determine the same class in `E_n(B)`. -/
theorem classOf_eq_of_iso (n : ℕ) {B : Type u} [TopologicalSpace B] {E E' : B → Type v}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E')]
    [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle (Fin n → ℝ) E]
    [FiberBundle (Fin n → ℝ) E'] [∀ b, AddCommGroup (E b)] [∀ b, AddCommGroup (E' b)]
    [∀ b, Module ℝ (E b)] [∀ b, Module ℝ (E' b)] [VectorBundle ℝ (Fin n → ℝ) E]
    [VectorBundle ℝ (Fin n → ℝ) E'] (e : RealPlaneBundleIso n B E E') :
    classOf n E = classOf n E' :=
  Quotient.sound ⟨e⟩

/-- Pulling back real `n`-plane bundles descends from maps to homotopy classes of maps. -/
def pullbackOnHomotopyClasses (n : ℕ) {B : Type u} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] {B' : Type u} [TopologicalSpace B'] :
    homotopyClasses B' B → classes n B' :=
  Quotient.lift
    (fun f : C(B', B) ↦ pullbackClass n f E)
    (fun f₀ f₁ h ↦ by
      letI : ∀ x : B', AddCommGroup ((f₀ *ᵖ E) x) :=
        fun x ↦ continuousMapPullbackAddCommGroup f₀ E x
      letI : ∀ x : B', Module ℝ ((f₀ *ᵖ E) x) :=
        continuousMapCoePullbackModules f₀ E
      letI : ∀ x : B', AddCommGroup ((f₁ *ᵖ E) x) :=
        fun x ↦ continuousMapPullbackAddCommGroup f₁ E x
      letI : ∀ x : B', Module ℝ ((f₁ *ᵖ E) x) :=
        continuousMapCoePullbackModules f₁ E
      have hIso : Nonempty (PullbackRealPlaneBundleIso n E f₀ f₁) :=
        pullbackRealPlaneBundleIsoOfHomotopic h
      rcases hIso with ⟨e⟩
      exact Quotient.sound ⟨e⟩)

/-- Evaluating pullback on a representative map gives the class of the actual pullback bundle. -/
@[simp] theorem pullbackOnHomotopyClasses_mk (n : ℕ) {B : Type u} [TopologicalSpace B]
    (E : B → Type v) [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)]
    [∀ b, Module ℝ (E b)] [VectorBundle ℝ (Fin n → ℝ) E] {B' : Type u}
    [TopologicalSpace B'] (f : C(B', B)) :
    pullbackOnHomotopyClasses n E ⟦f⟧ = pullbackClass n f E :=
  rfl

/-- Pulling back a real bundle isomorphism along a map again yields a bundle isomorphism. -/
private theorem pullbackIsoOfIso (n : ℕ) {B : Type u} [TopologicalSpace B]
    {B' : Type u} [TopologicalSpace B'] {E E' : Model n B}
    (h : Nonempty (RealPlaneBundleIso n B E.fiber E'.fiber)) (f : C(B', B)) :
    Nonempty
      (RealPlaneBundleIso n B' (Model.pullback n E f).fiber (Model.pullback n E' f).fiber) := sorry

/-- Pullback along `g : C(B', B)` induces the map `E_n(B) → E_n(B')` on real plane bundle
classes. -/
def pullbackOnClasses (n : ℕ) {B : Type u} [TopologicalSpace B] {B' : Type u}
    [TopologicalSpace B'] (g : C(B', B)) :
    classes n B → classes n B' :=
  Quotient.map
    (fun E : Model n B ↦ Model.pullback n E g)
    (fun _ _ h ↦ by
      simpa [Model.pullback] using pullbackIsoOfIso n h g)

/-- Pullback on real `n`-plane bundle classes sends the class of a bundle to the class of its
pullback. -/
@[simp] theorem pullbackOnClasses_classOf (n : ℕ) {B : Type u} [TopologicalSpace B]
    {B' : Type u} [TopologicalSpace B'] (g : C(B', B)) (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℝ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
    [VectorBundle ℝ (Fin n → ℝ) E] :
    pullbackOnClasses n g (classOf n E) = pullbackClass n g E :=
  rfl

end RealPlaneBundle

/-- Precomposition respects ordinary homotopy classes of maps into `Z`. -/
theorem homotopyClassesPrecompose_wellDefined {X : Type u} [TopologicalSpace X]
    {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] (g : C(X, Y)) {f₀ f₁ : C(Y, Z)}
    (h : ContinuousMap.Homotopic f₀ f₁) :
    ContinuousMap.Homotopic (f₀.comp g) (f₁.comp g) := sorry

/-- Precomposition by `g : C(X, Y)` induces the contravariant map `[Y, Z] → [X, Z]`. -/
def homotopyClassesPrecompose {X : Type u} [TopologicalSpace X] {Y Z : Type u}
    [TopologicalSpace Y] [TopologicalSpace Z] (g : C(X, Y)) :
    homotopyClasses Y Z → homotopyClasses X Z :=
  Quotient.map
    (fun f : C(Y, Z) ↦ f.comp g)
    (fun _ _ h ↦ homotopyClassesPrecompose_wellDefined g h)

section Classifying

variable (n : ℕ)
variable {BO : Type u} [TopologicalSpace BO]
variable (γ : BO → Type v)
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) γ)]
variable [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℝ) γ]
variable [∀ b, AddCommGroup (γ b)] [∀ b, Module ℝ (γ b)]
variable {X : Type u} [TopologicalSpace X]
variable {X' : Type u} [TopologicalSpace X']

/-- The universal real `n`-plane bundle over `BO(n)` determines its canonical class in
`E_n(BO(n))`. -/
def universalRealPlaneBundleClass [RealPlaneBundleClassifyingSpace n BO γ] :
    RealPlaneBundle.classes n BO :=
  RealPlaneBundle.classOf n γ

/-- The natural transformation `[X, BO(n)] → E_n(X)` sending a map to the class of the pullback
bundle `f *ᵖ γ`. -/
def realPlaneBundleClassifyingMap [RealPlaneBundleClassifyingSpace n BO γ] (X : Type u)
    [TopologicalSpace X] :
    homotopyClasses X BO → RealPlaneBundle.classes n X :=
  RealPlaneBundle.pullbackOnHomotopyClasses n γ

/-- Evaluating the classifying map on a representative `f : X ⟶ BO(n)` yields the class of the
pullback bundle `f *ᵖ γ`. -/
@[simp] theorem realPlaneBundleClassifyingMap_mk [RealPlaneBundleClassifyingSpace n BO γ]
    (f : C(X, BO)) :
    realPlaneBundleClassifyingMap n γ X ⟦f⟧ = RealPlaneBundle.pullbackClass n f γ :=
  rfl

/-- The classifying-space owner supplies the surjective/existence half of the classifying
assignment `[X, BO(n)] → E_n(X)`. -/
theorem realPlaneBundleClassifyingMap_surjective [RealPlaneBundleClassifyingSpace n BO γ] :
    Function.Surjective (realPlaneBundleClassifyingMap n γ X) := by
  sorry

/-- Theorem 23.1.5 (1): the classifying assignment `[X, BO(n)] → E_n(X)`,
`f ↦ f *ᵖ γ`, is bijective. -/
theorem realPlaneBundleClassifyingMap_bijective [RealPlaneBundleClassifyingSpace n BO γ] :
    Function.Bijective (realPlaneBundleClassifyingMap n γ X) := by
  sorry

/-- Under a classifying universal bundle, two maps `X ⟶ BO(n)` are homotopic whenever they
define the same classifying bundle class. -/
theorem homotopic_of_realPlaneBundleClassifyingMap_eq [RealPlaneBundleClassifyingSpace n BO γ]
    {f₀ f₁ : C(X, BO)}
    (h : realPlaneBundleClassifyingMap n γ X ⟦f₀⟧ =
      realPlaneBundleClassifyingMap n γ X ⟦f₁⟧) :
    ContinuousMap.Homotopic f₀ f₁ := by
  sorry

/-- Under a classifying universal bundle, isomorphic pullbacks of `γ` come from homotopic
classifying maps. -/
theorem homotopic_of_isomorphic_classifyingPullbacks
    [hγ : RealPlaneBundleClassifyingSpace n BO γ] {f₀ f₁ : C(X, BO)}
    (h : Nonempty (PullbackRealPlaneBundleIso n γ f₀ f₁)) :
    ContinuousMap.Homotopic f₀ f₁ :=
  RealPlaneBundleClassifyingSpace.unique h

/-- Theorem 23.1.5 (2): the classifying assignment `[X, BO(n)] → E_n(X)`, `f ↦ f *ᵖ γ`, is
natural with respect to pullback along maps of base spaces. -/
theorem realPlaneBundleClassifyingMap_natural [RealPlaneBundleClassifyingSpace n BO γ]
    (g : C(X', X)) :
    RealPlaneBundle.pullbackOnClasses n g ∘ realPlaneBundleClassifyingMap n γ X =
      realPlaneBundleClassifyingMap n γ X' ∘ homotopyClassesPrecompose g := by
  sorry

end Classifying

end
