import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Homotopy.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.VectorBundle.Constructions
import Mathlib.Topology.Instances.Matrix
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.HomotopyClasses
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_8_1

noncomputable section

open Bundle
open scoped Topology

universe u v w x

-- The canonical owner for unbased homotopy classes `[X,Y]` is
-- `continuousMapHomotopyClasses X Y`; this file builds the Chapter 23 principal- and
-- complex-bundle classification constructions directly on that quotient.

/-- A bundled compatibility view of a principal `G`-bundle over `B`. The source-facing
classification API in this file is carried by `PrincipalGBundle.classes` and
`PrincipalGBundle.classOf` on raw principal bundle maps, while this structure remains available for
later constructions that genuinely need a bundled total space. -/
structure PrincipalGBundle (G : Type u) [Group G] [TopologicalSpace G]
    (B : Type v) [TopologicalSpace B] where
  /-- The total space of the bundle. -/
  totalSpace : Type w
  /-- The topology on the total space. -/
  topologicalSpace_totalSpace : TopologicalSpace totalSpace
  /-- The structure-group action on the total space. -/
  mulAction_totalSpace : MulAction G totalSpace
  /-- Continuity of the structure-group action. -/
  continuousSMul_totalSpace : ContinuousSMul G totalSpace
  /-- The bundle projection to the base. -/
  proj : totalSpace → B
  /-- The projection exhibits a principal `G`-bundle. -/
  isPrincipal : IsPrincipalBundleMap G proj

attribute [instance] PrincipalGBundle.topologicalSpace_totalSpace
attribute [instance] PrincipalGBundle.mulAction_totalSpace
attribute [instance] PrincipalGBundle.continuousSMul_totalSpace
attribute [instance] PrincipalGBundle.isPrincipal
/-- A bundled principal `G`-bundle may be used as its projection map. -/
instance {G : Type u} [Group G] [TopologicalSpace G] {B : Type v} [TopologicalSpace B] :
    CoeFun (PrincipalGBundle G B) fun P ↦ P.totalSpace → B where
  coe P := P.proj

namespace PrincipalGBundle

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {B : Type v} [TopologicalSpace B]
variable {B' : Type w} [TopologicalSpace B']

private def ofMap {Z : Type w} [TopologicalSpace Z] [MulAction G Z] [ContinuousSMul G Z]
    (p : Z → B) [IsPrincipalBundleMap G p] : PrincipalGBundle G B where
  totalSpace := Z
  topologicalSpace_totalSpace := inferInstance
  mulAction_totalSpace := inferInstance
  continuousSMul_totalSpace := inferInstance
  proj := p
  isPrincipal := inferInstance

/-- A principal bundle isomorphism is a `G`-equivariant homeomorphism over the common base. -/
structure Iso (P Q : PrincipalGBundle G B) where
  /-- The underlying homeomorphism of total spaces. -/
  toHomeomorph : P.totalSpace ≃ₜ Q.totalSpace
  /-- The homeomorphism respects the bundle projections. -/
  comm_proj : Q.proj ∘ toHomeomorph = P.proj
  /-- The homeomorphism is `G`-equivariant. -/
  map_smul (g : G) (z : P.totalSpace) : toHomeomorph (g • z) = g • toHomeomorph z

/-- Principal `G`-bundle isomorphism is an equivalence relation on principal bundles over a fixed
base. -/
theorem iso_equivalence (G : Type u) [Group G] [TopologicalSpace G]
    (B : Type v) [TopologicalSpace B] :
    Equivalence (fun P Q : PrincipalGBundle G B ↦ Nonempty (PrincipalGBundle.Iso P Q)) := sorry

/-- The setoid whose classes are principal `G`-bundles over `B` modulo `G`-equivariant
homeomorphism over `B`. -/
def setoid (G : Type u) [Group G] [TopologicalSpace G]
    (B : Type v) [TopologicalSpace B] : Setoid (PrincipalGBundle G B) where
  r P Q := Nonempty (PrincipalGBundle.Iso P Q)
  iseqv := iso_equivalence G B

/-- The type `PG(B)` of principal `G`-bundles over `B` modulo principal bundle isomorphism. -/
abbrev classes (G : Type u) [Group G] [TopologicalSpace G]
    (B : Type v) [TopologicalSpace B] :=
  Quotient (setoid G B)

/-- The isomorphism class of a principal `G`-bundle map `p : Z → B`. -/
def classOf {Z : Type w} [TopologicalSpace Z] [MulAction G Z] [ContinuousSMul G Z]
    (p : Z → B) [IsPrincipalBundleMap G p] : classes G B :=
  Quotient.mk (setoid G B) (ofMap p)

/-- Isomorphic bundled representatives determine the same class in `PG(B)`. -/
theorem classOf_eq_of_iso {P Q : PrincipalGBundle G B} (e : PrincipalGBundle.Iso P Q) :
    (classOf P : classes G B) = classOf Q :=
  Quotient.sound ⟨e⟩

/-- The explicit pullback total space of `P` along `f : C(B', B)`. -/
def pullbackTotalSpace (P : PrincipalGBundle G B) (f : C(B', B)) :=
  { z : B' × P.totalSpace // f z.1 = P.proj z.2 }

/-- The pullback total space inherits the subtype topology from `B' × P.totalSpace`. -/
instance pullbackTopologicalSpace (P : PrincipalGBundle G B) (f : C(B', B)) :
    TopologicalSpace (pullbackTotalSpace P f) :=
  inferInstanceAs (TopologicalSpace { z : B' × P.totalSpace // f z.1 = P.proj z.2 })

/-- The diagonal action preserves the pullback condition because the original projection is
constant on `G`-orbits. -/
theorem pullbackTotalSpace_smul_mem (P : PrincipalGBundle G B) (f : C(B', B))
    (g : G) (z : pullbackTotalSpace P f) :
    f z.1.1 = P.proj (g • z.1.2) := by
  rw [IsPrincipalBundleMap.proj_smul P.isPrincipal g z.1.2, z.2]

/-- The pullback total space carries the diagonal `G`-action. -/
instance pullbackMulAction (P : PrincipalGBundle G B) (f : C(B', B)) :
    MulAction G (pullbackTotalSpace P f) where
  smul g z := ⟨(z.1.1, g • z.1.2), pullbackTotalSpace_smul_mem P f g z⟩
  one_smul z := sorry
  mul_smul g h z := sorry

/-- The diagonal `G`-action on the pullback total space is continuous. -/
theorem pullbackContinuousSMul (P : PrincipalGBundle G B) (f : C(B', B)) :
    ContinuousSMul G (pullbackTotalSpace P f) := sorry

attribute [instance] pullbackContinuousSMul

/-- Pulling back a principal `G`-bundle along a continuous map again yields a principal
`G`-bundle. -/
theorem pullbackIsPrincipal (P : PrincipalGBundle G B) (f : C(B', B)) :
    IsPrincipalBundleMap G (fun z : pullbackTotalSpace P f ↦ z.1.1) := sorry

/-- The raw pullback projection of a principal `G`-bundle carries the induced principal-bundle
structure. -/
instance pullbackProjIsPrincipalBundleMap (P : PrincipalGBundle G B) (f : C(B', B)) :
    IsPrincipalBundleMap G (fun z : pullbackTotalSpace P f ↦ z.1.1) :=
  pullbackIsPrincipal P f

/-- The pullback principal `G`-bundle along `f : C(B', B)`. -/
def pullback (P : PrincipalGBundle G B) (f : C(B', B)) : PrincipalGBundle G B' where
  totalSpace := pullbackTotalSpace P f
  topologicalSpace_totalSpace := inferInstance
  mulAction_totalSpace := inferInstance
  continuousSMul_totalSpace := inferInstance
  proj z := z.1.1
  isPrincipal := inferInstance

/-- The class of the pullback of a raw principal `G`-bundle map along `f`. -/
def pullbackClass {B' : Type x} [TopologicalSpace B'] {Z : Type w} [TopologicalSpace Z]
    [MulAction G Z] [ContinuousSMul G Z] (f : C(B', B)) (p : Z → B)
    [IsPrincipalBundleMap G p] :
    classes.{u, x, max x w} G B' :=
  Quotient.mk (setoid.{u, x, max x w} G B') ((ofMap p).pullback f)

/-- Homotopic maps give isomorphic pullbacks of the same principal bundle. -/
theorem pullbackIsoOfHomotopic (P : PrincipalGBundle G B)
    {f₀ f₁ : C(B', B)} (h : ContinuousMap.Homotopic f₀ f₁) :
    Nonempty (PrincipalGBundle.Iso (P.pullback f₀) (P.pullback f₁)) := sorry

/-- Pulling back along a map of bases preserves principal bundle isomorphism classes. -/
theorem pullbackIsoOfIso {P Q : PrincipalGBundle G B}
    (h : Nonempty (PrincipalGBundle.Iso P Q)) (f : C(B', B)) :
    Nonempty (PrincipalGBundle.Iso (P.pullback f) (Q.pullback f)) := sorry

/-- Pulling back a raw principal `G`-bundle map descends from maps to homotopy classes of maps. -/
def pullbackOnHomotopyClasses {Z : Type w} [TopologicalSpace Z] [MulAction G Z]
    [ContinuousSMul G Z] (p : Z → B) [IsPrincipalBundleMap G p]
    {B' : Type v} [TopologicalSpace B'] :
    continuousMapHomotopyClasses B' B → classes.{u, v, max v w} G B' :=
  Quotient.map
    (fun f : C(B', B) ↦ (ofMap p).pullback f)
    (fun _ _ h ↦ by
      simpa [PrincipalGBundle.setoid] using pullbackIsoOfHomotopic (ofMap p) h)

/-- Evaluating pullback on a representative map gives the class of the actual pullback bundle. -/
@[simp] theorem pullbackOnHomotopyClasses_mk
    {Z : Type w} [TopologicalSpace Z] [MulAction G Z] [ContinuousSMul G Z]
    (p : Z → B) [IsPrincipalBundleMap G p] {B' : Type v} [TopologicalSpace B']
    (f : C(B', B)) :
    (pullbackOnHomotopyClasses p :
      continuousMapHomotopyClasses B' B → classes.{u, v, max v w} G B') ⟦f⟧ =
        pullbackClass f p :=
  rfl

/-- Pullback along `g : C(B', B)` induces the map `PG(B) → PG(B')` on principal bundle classes. -/
def pullbackOnClasses (g : C(B', B)) : classes G B → classes G B' :=
  Quotient.map
    (fun P : PrincipalGBundle G B ↦ P.pullback g)
    (fun _ _ h ↦ pullbackIsoOfIso h g)

/-- Pullback on principal-bundle classes sends the class of a bundle to the class of its
pullback. -/
@[simp] theorem pullbackOnClasses_classOf
    {Z : Type w} [TopologicalSpace Z] [MulAction G Z] [ContinuousSMul G Z]
    (g : C(B', B)) (p : Z → B) [IsPrincipalBundleMap G p] :
    pullbackOnClasses g (classOf p : classes G B) = pullbackClass g p :=
  rfl

/-- Pullback along a composite agrees, up to principal bundle isomorphism, with iterated pullback.
-/
theorem pullbackIso_comp {B'' : Type x} [TopologicalSpace B'']
    (P : PrincipalGBundle G B) (f : C(B', B)) (g : C(B'', B')) :
    Nonempty (PrincipalGBundle.Iso ((P.pullback f).pullback g) (P.pullback (f.comp g))) := sorry

end PrincipalGBundle

section UniversalPrincipalBundle

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {Y : Type v} [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

/-- The orbit-space principal bundle attached to the quotient map
`Y → MulAction.orbitRel.Quotient G Y`. -/
def orbitPrincipalGBundle
    (hY : IsPrincipalBundleMap G (Quotient.mk'' : Y → MulAction.orbitRel.Quotient G Y)) :
    PrincipalGBundle G (MulAction.orbitRel.Quotient G Y) where
  totalSpace := Y
  topologicalSpace_totalSpace := inferInstance
  mulAction_totalSpace := inferInstance
  continuousSMul_totalSpace := inferInstance
  proj := Quotient.mk''
  isPrincipal := hY

end UniversalPrincipalBundle

section

variable {n : ℕ}
variable {B : Type u} [TopologicalSpace B]
variable {B' : Type w} [TopologicalSpace B']

/-- A bundled compatibility view of a complex `n`-plane bundle over `B`. The source-facing
classification API in this file is carried by `ComplexPlaneBundle.classes` and
`ComplexPlaneBundle.classOf` on raw `Fin n → ℂ`-modeled vector-bundle families, while this
structure remains available for later constructions that genuinely need a bundled family. -/
structure ComplexPlaneBundle (n : ℕ) (B : Type u) [TopologicalSpace B] where
  /-- The fiber family over `B`. -/
  fiber : B → Type v
  /-- The topology on the total space. -/
  totalSpace_topology : TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) fiber)
  /-- The fiberwise topologies. -/
  fiber_topology (b : B) : TopologicalSpace (fiber b)
  /-- The local triviality data. -/
  fiberBundle : FiberBundle (Fin n → ℂ) fiber
  /-- The fiberwise additive commutative group structure. -/
  fiber_addCommGroup (b : B) : AddCommGroup (fiber b)
  /-- The fiberwise complex vector-space structure. -/
  fiber_module (b : B) : Module ℂ (fiber b)
  /-- The vector-bundle structure with model fiber `Fin n → ℂ`. -/
  vectorBundle : VectorBundle ℂ (Fin n → ℂ) fiber

/-- A fiberwise continuous complex-linear equivalence between two complex `n`-plane bundles over
the same base. -/
structure ComplexPlaneBundleIso
    (n : ℕ) (B : Type u) [TopologicalSpace B]
    (E E' : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E')]
    [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (E b)] [∀ b, AddCommGroup (E' b)]
    [∀ b, Module ℂ (E b)] [∀ b, Module ℂ (E' b)] where
  /-- The fiberwise continuous complex-linear equivalence. -/
  toContinuousLinearEquiv (b : B) : E b ≃L[ℂ] E' b
  /-- Continuity of the induced map on total spaces. -/
  continuous_toFun : Continuous fun z : Bundle.TotalSpace (Fin n → ℂ) E ↦
    @Bundle.TotalSpace.mk B (Fin n → ℂ) E' z.1 (toContinuousLinearEquiv z.1 z.2)
  /-- Continuity of the inverse induced map on total spaces. -/
  continuous_invFun : Continuous fun z : Bundle.TotalSpace (Fin n → ℂ) E' ↦
    @Bundle.TotalSpace.mk B (Fin n → ℂ) E z.1 ((toContinuousLinearEquiv z.1).symm z.2)

/-- A bundle isomorphism acts on total spaces by its fiberwise continuous linear equivalences. -/
instance complexPlaneBundleIsoCoeFun
    {n : ℕ} {B : Type u} [TopologicalSpace B] {E E' : B → Type v}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E')]
    [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (E b)] [∀ b, AddCommGroup (E' b)]
    [∀ b, Module ℂ (E b)] [∀ b, Module ℂ (E' b)] :
    CoeFun (ComplexPlaneBundleIso n B E E') fun _ ↦
      Bundle.TotalSpace (Fin n → ℂ) E → Bundle.TotalSpace (Fin n → ℂ) E' where
  coe η z :=
    @Bundle.TotalSpace.mk B (Fin n → ℂ) E' z.1 (η.toContinuousLinearEquiv z.1 z.2)

attribute [instance] ComplexPlaneBundle.totalSpace_topology
attribute [instance] ComplexPlaneBundle.fiber_topology
attribute [instance] ComplexPlaneBundle.fiberBundle
attribute [instance] ComplexPlaneBundle.fiber_addCommGroup
attribute [instance] ComplexPlaneBundle.fiber_module
attribute [instance] ComplexPlaneBundle.vectorBundle

/-- A bundled complex `n`-plane bundle may be used as its underlying fiber family. -/
instance {n : ℕ} {B : Type u} [TopologicalSpace B] :
    CoeFun (ComplexPlaneBundle n B) fun _ ↦ B → Type v where
  coe E := E.fiber

namespace ComplexPlaneBundle

/-- Bundle a raw `Fin n → ℂ`-modeled vector-bundle family into the Chapter 23 owner
`ComplexPlaneBundle n B`. -/
def ofFamily (n : ℕ) {B : Type u} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    ComplexPlaneBundle n B where
  fiber := E
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := inferInstance
  fiber_module := inferInstance
  vectorBundle := inferInstance

private abbrev pullbackIsoType
    (n : ℕ) {X : Type u} [TopologicalSpace X] (E : X → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
    [∀ x, TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    {BU : Type w} [TopologicalSpace BU] (f : C(X, BU)) (γ : BU → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℂ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℂ (γ b)] :
    Type _ :=
  @ComplexPlaneBundleIso n X _ E (⇑f *ᵖ γ)
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    (fun x ↦ continuousMapPullbackAddCommGroup f γ x)
    inferInstance
    (continuousMapCoePullbackModules f γ)

/-- The type of raw fiberwise complex-linear bundle isomorphisms from a complex `n`-plane bundle
family `E` to a pullback `f *ᵖ γ`. This source-facing owner keeps the classifying-space field
inferable without exposing pullback instance plumbing in the public surface. -/
abbrev pullbackComplexPlaneBundleIso
    (n : ℕ) {X : Type u} [TopologicalSpace X] (E : X → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
    [∀ x, TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    {BU : Type w} [TopologicalSpace BU] (f : C(X, BU)) (γ : BU → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℂ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℂ (γ b)] :
    Type _ :=
  pullbackIsoType n E f γ

/-- The type of bundle isomorphisms between the pullbacks of a fixed complex `n`-plane bundle
along two maps with common source and target. -/
abbrev PullbackComplexPlaneBundleIso
    (n : ℕ) {X : Type u} [TopologicalSpace X] {B : Type w} [TopologicalSpace B]
    (E : B → Type v) [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℂ) E]
    [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    (f₀ f₁ : C(X, B)) : Type _ :=
  @ComplexPlaneBundleIso n X _ (f₀ *ᵖ E) (f₁ *ᵖ E) _ _ _ _
    (fun x ↦ continuousMapPullbackAddCommGroup f₀ E x)
    (fun x ↦ continuousMapPullbackAddCommGroup f₁ E x)
    (continuousMapCoePullbackModules f₀ E)
    (continuousMapCoePullbackModules f₁ E)

private structure Model (n : ℕ) (B : Type u) [TopologicalSpace B] where
  fiber : B → Type v
  totalSpace_topology : TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) fiber)
  fiber_topology : ∀ b, TopologicalSpace (fiber b)
  fiberBundle : FiberBundle (Fin n → ℂ) fiber
  fiber_addCommGroup : ∀ b, AddCommGroup (fiber b)
  fiber_module : ∀ b, Module ℂ (fiber b)
  vectorBundle : VectorBundle ℂ (Fin n → ℂ) fiber

attribute [instance] Model.totalSpace_topology
attribute [instance] Model.fiber_topology
attribute [instance] Model.fiberBundle
attribute [instance] Model.fiber_addCommGroup
attribute [instance] Model.fiber_module
attribute [instance] Model.vectorBundle

private def Model.ofFamily (n : ℕ) {B : Type u} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    Model n B where
  fiber := E
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := inferInstance
  fiber_module := inferInstance
  vectorBundle := inferInstance

private def Model.pullback (n : ℕ) {B : Type u} [TopologicalSpace B] {B' : Type w}
    [TopologicalSpace B'] (E : Model n B) (f : C(B', B)) :
    Model n B' where
  fiber := f *ᵖ E.fiber
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := fun x ↦ continuousMapPullbackAddCommGroup f E.fiber x
  fiber_module := continuousMapCoePullbackModules f E.fiber
  vectorBundle := (VectorBundle.pullback ℂ f :
    VectorBundle ℂ (Fin n → ℂ) (f *ᵖ E.fiber))

private def pullbackBundleOfFamily (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] (f : C(B', B)) :
    ComplexPlaneBundle n B' where
  fiber := f *ᵖ E
  totalSpace_topology := inferInstance
  fiber_topology := inferInstance
  fiberBundle := inferInstance
  fiber_addCommGroup := fun x ↦ continuousMapPullbackAddCommGroup f E x
  fiber_module := continuousMapCoePullbackModules f E
  vectorBundle := (VectorBundle.pullback ℂ f :
    VectorBundle ℂ (Fin n → ℂ) (f *ᵖ E))

/-- A complex plane bundle isomorphism is a fiberwise continuous complex-linear equivalence over
the common base. -/
abbrev Iso (E E' : ComplexPlaneBundle n B) : Type _ :=
  ComplexPlaneBundleIso n B E.fiber E'.fiber

/-- Bundle isomorphism is an equivalence relation on internal representatives of complex
`n`-plane bundles. -/
private theorem iso_equivalence (n : ℕ) (B : Type u) [TopologicalSpace B] :
    Equivalence
      (fun E E' : Model.{u, v} n B ↦ Nonempty (ComplexPlaneBundleIso n B E.fiber E'.fiber)) := sorry

private def setoid (n : ℕ) (B : Type u) [TopologicalSpace B] : Setoid (Model.{u, v} n B) where
  r E E' := Nonempty (ComplexPlaneBundleIso n B E.fiber E'.fiber)
  iseqv := iso_equivalence n B

/-- The type of complex `n`-plane bundles over `B` modulo bundle isomorphism. -/
abbrev classes (n : ℕ) (B : Type u) [TopologicalSpace B] :=
  Quotient (setoid n B)

/-- The isomorphism class of a complex `n`-plane bundle family `E : B → Type*`. -/
def classOf {n : ℕ} {B : Type u} [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    classes n B :=
  Quotient.mk (setoid n B) (Model.ofFamily n E)

/-- Pulling back a complex `n`-plane bundle along a continuous map again yields a complex
`n`-plane bundle. -/
def pullback (E : ComplexPlaneBundle n B) (f : C(B', B)) : ComplexPlaneBundle n B' :=
  pullbackBundleOfFamily E.fiber f

/-- The class of the pullback of a raw family `E` along `f`, packaged in
`ComplexPlaneBundle.classes n B'`. -/
def pullbackClass (f : C(B', B)) (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    classes n B' :=
  Quotient.mk (setoid n B') (Model.pullback n (Model.ofFamily n E) f)

/-- Homotopic maps give isomorphic pullbacks of the same raw complex `n`-plane bundle family. -/
private theorem pullbackIsoOfHomotopic (n : ℕ) (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] {f₀ f₁ : C(B', B)}
    (h : ContinuousMap.Homotopic f₀ f₁) :
    Nonempty (PullbackComplexPlaneBundleIso n E f₀ f₁) := sorry

/-- Isomorphic raw `Fin n → ℂ`-modeled vector-bundle families determine the same class in
`ComplexPlaneBundle.classes n B`. -/
theorem classOf_eq_of_iso {E E' : B → Type v}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E')]
    [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
    [FiberBundle (Fin n → ℂ) E] [FiberBundle (Fin n → ℂ) E']
    [∀ b, AddCommGroup (E b)] [∀ b, AddCommGroup (E' b)]
    [∀ b, Module ℂ (E b)] [∀ b, Module ℂ (E' b)]
    [VectorBundle ℂ (Fin n → ℂ) E] [VectorBundle ℂ (Fin n → ℂ) E']
    (e : ComplexPlaneBundleIso n B E E') :
    (classOf E : classes n B) = classOf E' :=
  Quotient.sound ⟨e⟩

/-- Pulling back a raw complex `n`-plane-bundle family descends from maps to homotopy classes of
maps. -/
def pullbackOnHomotopyClasses (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] {B' : Type u} [TopologicalSpace B'] :
    continuousMapHomotopyClasses B' B → classes n B' :=
  Quotient.lift
    (fun f : C(B', B) ↦ pullbackClass f E)
    (fun f₀ f₁ h ↦ by
      letI : ∀ x : B', AddCommGroup ((f₀ *ᵖ E) x) :=
        fun x ↦ continuousMapPullbackAddCommGroup f₀ E x
      letI : ∀ x : B', Module ℂ ((f₀ *ᵖ E) x) :=
        continuousMapCoePullbackModules f₀ E
      letI : ∀ x : B', AddCommGroup ((f₁ *ᵖ E) x) :=
        fun x ↦ continuousMapPullbackAddCommGroup f₁ E x
      letI : ∀ x : B', Module ℂ ((f₁ *ᵖ E) x) :=
        continuousMapCoePullbackModules f₁ E
      have hIso :
          Nonempty
            (ComplexPlaneBundleIso n B'
              (Model.pullback n (Model.ofFamily n E) f₀).fiber
              (Model.pullback n (Model.ofFamily n E) f₁).fiber) := by
        simpa [Model.pullback] using pullbackIsoOfHomotopic n E h
      exact Quotient.sound hIso)

/-- Evaluating pullback on a representative map gives the class of the actual pullback bundle. -/
@[simp] theorem pullbackOnHomotopyClasses_mk (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] {B' : Type u} [TopologicalSpace B']
    (f : C(B', B)) :
    (ComplexPlaneBundle.pullbackOnHomotopyClasses E :
      continuousMapHomotopyClasses B' B → classes n B') ⟦f⟧ = pullbackClass f E :=
  rfl

/-- Pulling back a complex-bundle isomorphism along a map again yields a complex-bundle
isomorphism on internal representatives. -/
private theorem pullbackIsoOfIso {E E' : Model n B}
    (h : Nonempty (ComplexPlaneBundleIso n B E.fiber E'.fiber)) (f : C(B', B)) :
    Nonempty
      (ComplexPlaneBundleIso n B'
        (Model.pullback n E f).fiber
        (Model.pullback n E' f).fiber) := sorry

/-- Pullback along `g : C(B', B)` induces the map `ComplexPlaneBundle.classes n B →
ComplexPlaneBundle.classes n B'`. -/
def pullbackOnClasses (g : C(B', B)) : classes n B → classes n B' :=
  Quotient.map
    (fun E : Model n B ↦ Model.pullback n E g)
    (fun _ _ h ↦ by
      simpa [Model.pullback] using pullbackIsoOfIso h g)

/-- Pullback on complex-bundle classes sends the class of a family to the class of its pullback. -/
@[simp] theorem pullbackOnClasses_classOf (g : C(B', B)) (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)] [∀ b, TopologicalSpace (E b)]
    [FiberBundle (Fin n → ℂ) E] [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)]
    [VectorBundle ℂ (Fin n → ℂ) E] :
    pullbackOnClasses g (classOf E : classes n B) = pullbackClass g E :=
  rfl

/-- Iterated pullback of a complex `n`-plane bundle is isomorphic to pullback along the composite
map. -/
theorem pullbackIso_comp {B'' : Type x} [TopologicalSpace B'']
    (E : ComplexPlaneBundle n B) (f : C(B', B)) (g : C(B'', B')) :
    Nonempty (Iso ((E.pullback f).pullback g) (E.pullback (f.comp g))) := sorry

end ComplexPlaneBundle

/-- The unitary group `U(n)` of complex `n × n` matrices. -/
abbrev U (n : ℕ) :=
  Matrix.unitaryGroup (Fin n) ℂ

section Classifying

variable {n : ℕ}
variable {BU : Type u} [TopologicalSpace BU]
variable {γ : BU → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γ)]
variable [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℂ) γ]
variable [∀ b, AddCommGroup (γ b)] [∀ b, Module ℂ (γ b)]
variable {X : Type u} [TopologicalSpace X]
variable {X' : Type u} [TopologicalSpace X']

/-- The quotient `EU / U(n)` presenting a chosen model of the classifying space `BU(n)` attached
to a universal `U(n)`-space `EU`. -/
abbrev complexPlaneBundleClassifyingSpace (n : ℕ) (EU : Type u) [TopologicalSpace EU]
    [MulAction (U n) EU] [ContinuousSMul (U n) EU] : Type u :=
  MulAction.orbitRel.Quotient (U n) EU

/-- Source-facing notation for the quotient-model classifying space `BU(n)`. -/
notation "BU[" n ", " EU "]" => complexPlaneBundleClassifyingSpace n EU

/-- A classifying space `BU` for complex `n`-plane bundles is represented by a universal complex
`n`-plane bundle `γ` such that every complex `n`-plane bundle is isomorphic to some pullback
`f *ᵖ γ`. The chapter API also records the corresponding uniqueness-up-to-homotopy property used
to derive injectivity of the classifying assignment. -/
class ComplexPlaneBundleClassifyingSpace
    (n : ℕ) (BU : Type u) [TopologicalSpace BU] (γ : BU → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℂ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℂ (γ b)]
    extends VectorBundle ℂ (Fin n → ℂ) γ where
  /-- Every complex `n`-plane bundle is isomorphic to a pullback of the universal bundle. -/
  classifies {X : Type w} [TopologicalSpace X] (E : X → Type v)
      [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) E)]
      [∀ x, TopologicalSpace (E x)] [FiberBundle (Fin n → ℂ) E]
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [VectorBundle ℂ (Fin n → ℂ) E] :
      ∃ f : C(X, BU), Nonempty (ComplexPlaneBundle.pullbackComplexPlaneBundleIso n E f γ)
  /-- Pullbacks of the universal bundle determine the classifying map uniquely up to homotopy. -/
  unique {X : Type u} [TopologicalSpace X] {f₀ f₁ : C(X, BU)}
      (hIso : Nonempty (ComplexPlaneBundle.PullbackComplexPlaneBundleIso n γ f₀ f₁)) :
      ContinuousMap.Homotopic f₀ f₁

/-- A complex `n`-plane-bundle classifying space carries the canonical vector-bundle structure on
its universal bundle. -/
instance complexPlaneBundleClassifyingSpaceToVectorBundle
    {n : ℕ} {BU : Type u} [TopologicalSpace BU] {γ : BU → Type v}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℂ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℂ (γ b)]
    [h : ComplexPlaneBundleClassifyingSpace n BU γ] :
    VectorBundle ℂ (Fin n → ℂ) γ :=
  h.toVectorBundle

/-- The universal complex `n`-plane bundle over `BU`, repackaged in bundled form for later
constructions that need an explicit object. -/
def universalComplexPlaneBundle [ComplexPlaneBundleClassifyingSpace n BU γ] :
    ComplexPlaneBundle n BU :=
  ComplexPlaneBundle.ofFamily n γ

/-- The canonical class of the universal complex `n`-plane bundle in
`ComplexPlaneBundle.classes n BU`. -/
def universalComplexPlaneBundleClass [ComplexPlaneBundleClassifyingSpace n BU γ] :
    ComplexPlaneBundle.classes n BU :=
  ComplexPlaneBundle.classOf γ

/-- The classifying assignment `[X, BU] → ComplexPlaneBundle.classes n X` sending a map to the
pullback class of the chosen complex `n`-plane bundle `γ`. -/
def complexPlaneBundleClassifyingMap
    (n : ℕ) (BU : Type u) [TopologicalSpace BU] (γ : BU → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γ)]
    [∀ b, TopologicalSpace (γ b)] [FiberBundle (Fin n → ℂ) γ]
    [∀ b, AddCommGroup (γ b)] [∀ b, Module ℂ (γ b)]
    [VectorBundle ℂ (Fin n → ℂ) γ]
    (X : Type u) [TopologicalSpace X] :
    continuousMapHomotopyClasses X BU → ComplexPlaneBundle.classes n X :=
  (ComplexPlaneBundle.pullbackOnHomotopyClasses γ :
    continuousMapHomotopyClasses X BU → ComplexPlaneBundle.classes n X)

/-- Evaluating the complex classifying map on a representative `f : C(X, BU)` yields the class of
the pullback bundle `f *ᵖ γ`. -/
@[simp] theorem complexPlaneBundleClassifyingMap_mk
    [VectorBundle ℂ (Fin n → ℂ) γ]
    (f : C(X, BU)) :
    complexPlaneBundleClassifyingMap n BU γ X ⟦f⟧ =
      ComplexPlaneBundle.pullbackClass f γ :=
  rfl

/-- The classifying-space owner supplies the surjective half of the classifying assignment
`[X, BU] → ComplexPlaneBundle.classes n X`. -/
theorem complexPlaneBundleClassifyingMap_surjective [ComplexPlaneBundleClassifyingSpace n BU γ] :
    Function.Surjective (complexPlaneBundleClassifyingMap n BU γ X) := sorry

/-- Under a classifying universal bundle, two maps `X ⟶ BU` are homotopic whenever they define
the same complex bundle class. -/
theorem homotopic_of_complexPlaneBundleClassifyingMap_eq
    [ComplexPlaneBundleClassifyingSpace n BU γ] {f₀ f₁ : C(X, BU)}
    (h : complexPlaneBundleClassifyingMap n BU γ X ⟦f₀⟧ =
      complexPlaneBundleClassifyingMap n BU γ X ⟦f₁⟧) :
    ContinuousMap.Homotopic f₀ f₁ := by
  sorry

/-- The classifying-space uniqueness field makes the classifying assignment injective on
homotopy classes. -/
theorem complexPlaneBundleClassifyingMap_injective
    [ComplexPlaneBundleClassifyingSpace n BU γ] :
    Function.Injective (complexPlaneBundleClassifyingMap n BU γ X) := by
  sorry

/-- A classifying universal complex `n`-plane bundle makes its classifying assignment bijective. -/
theorem complexPlaneBundleClassifyingMap_bijective_of_classifyingSpace
    [ComplexPlaneBundleClassifyingSpace n BU γ] :
    Function.Bijective (complexPlaneBundleClassifyingMap n BU γ X) := sorry

/-- Under a classifying universal bundle, isomorphic pullbacks of `γ` come from homotopic
classifying maps. -/
theorem homotopic_of_isomorphic_complexPlaneBundleClassifyingPullbacks
    [ComplexPlaneBundleClassifyingSpace n BU γ] {f₀ f₁ : C(X, BU)}
    (hIso : Nonempty (ComplexPlaneBundle.PullbackComplexPlaneBundleIso n γ f₀ f₁)) :
    ContinuousMap.Homotopic f₀ f₁ := by
  exact ComplexPlaneBundleClassifyingSpace.unique hIso

/-- The complex classifying assignment is natural with respect to pullback along maps of base
spaces. -/
theorem complexPlaneBundleClassifyingMap_natural
    [VectorBundle ℂ (Fin n → ℂ) γ] (g : C(X', X)) :
    ComplexPlaneBundle.pullbackOnClasses g ∘ complexPlaneBundleClassifyingMap n BU γ X =
      complexPlaneBundleClassifyingMap n BU γ X' ∘
        continuousMapHomotopyClassesPrecompose g := by
  funext c
  refine Quotient.inductionOn c ?_
  intro f
  rcases ComplexPlaneBundle.pullbackIso_comp (ComplexPlaneBundle.ofFamily n γ) f g with ⟨e⟩
  simp only [Function.comp_apply, complexPlaneBundleClassifyingMap_mk]
  exact Quotient.sound ⟨e⟩

variable {EU : Type u} [TopologicalSpace EU]
variable [MulAction (U n) EU] [ContinuousSMul (U n) EU]
variable {γBU : BU[n, EU] → Type v}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γBU)]
variable [∀ b, TopologicalSpace (γBU b)] [FiberBundle (Fin n → ℂ) γBU]
variable [∀ b, AddCommGroup (γBU b)] [∀ b, Module ℂ (γBU b)]
variable [VectorBundle ℂ (Fin n → ℂ) γBU]

/-- The quotient-model classifying assignment `[X, BU(n)] → ComplexPlaneBundle.classes n X`
attached to the chosen universal bundle `γBU` over `BU(n)`. -/
def quotientModelComplexPlaneBundleClassifyingMap
    (n : ℕ) (EU : Type u) [TopologicalSpace EU]
    [MulAction (U n) EU] [ContinuousSMul (U n) EU]
    (γBU : BU[n, EU] → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γBU)]
    [∀ b, TopologicalSpace (γBU b)] [FiberBundle (Fin n → ℂ) γBU]
    [∀ b, AddCommGroup (γBU b)] [∀ b, Module ℂ (γBU b)]
    [VectorBundle ℂ (Fin n → ℂ) γBU]
    (X : Type u) [TopologicalSpace X] :
    continuousMapHomotopyClasses X BU[n, EU] →
      ComplexPlaneBundle.classes n X :=
  complexPlaneBundleClassifyingMap n BU[n, EU] γBU X

/-- The quotient-model principal-bundle classification map `[X, BU(n)] → PU(n)(X)` induced by the
universal principal `U(n)`-bundle `EU → BU(n)`. -/
def quotientModelUnitaryPrincipalBundleClassifyingMap
    [IsPrincipalBundleMap (U n)
      (Quotient.mk'' : EU → BU[n, EU])] :
    continuousMapHomotopyClasses X BU[n, EU] →
      PrincipalGBundle.classes (U n) X :=
  PrincipalGBundle.pullbackOnHomotopyClasses
    (Quotient.mk'' : EU → BU[n, EU])

/-- A quotient-model universal complex bundle identifies complex `n`-plane bundle classes with the
principal `U(n)`-bundle classes classified by the universal principal bundle `EU → BU(n)`. -/
class ComplexPlaneBundleQuotientModel
    (n : ℕ) (EU : Type u) [TopologicalSpace EU]
    [MulAction (U n) EU] [ContinuousSMul (U n) EU]
    (γBU : BU[n, EU] → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℂ) γBU)]
    [∀ b, TopologicalSpace (γBU b)] [FiberBundle (Fin n → ℂ) γBU]
    [∀ b, AddCommGroup (γBU b)] [∀ b, Module ℂ (γBU b)]
    [VectorBundle ℂ (Fin n → ℂ) γBU]
    [IsPrincipalBundleMap (U n)
      (Quotient.mk'' : EU → BU[n, EU])] where
  /-- The bridge from principal `U(n)`-bundle classes to complex `n`-plane bundle classes. -/
  principalToComplexClasses (X : Type u) [TopologicalSpace X] :
    PrincipalGBundle.classes (U n) X ≃ ComplexPlaneBundle.classes n X
  /-- The chosen quotient-model complex-bundle classification map agrees with the principal-bundle
  classification map followed by the bridge to complex bundle classes. -/
  classifyingMap_eq (X : Type u) [TopologicalSpace X] :
    quotientModelComplexPlaneBundleClassifyingMap n EU γBU X =
      fun c : continuousMapHomotopyClasses X BU[n, EU] ↦
        principalToComplexClasses X (quotientModelUnitaryPrincipalBundleClassifyingMap c)

/-- Over a contractible quotient model `BU(n) = EU / U(n)`, a quotient-model universal complex
`n`-plane bundle supplies the canonical classifying-space instance for complex
`n`-plane bundles. This is the bridge from the source-facing quotient-model
packaging to the reusable Chapter 23 classifying-space API. -/
instance complexPlaneBundleQuotientModelToClassifyingSpace [ContractibleSpace EU]
    [IsPrincipalBundleMap (U n)
      (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU] :
    ComplexPlaneBundleClassifyingSpace n BU[n, EU] γBU where
  toVectorBundle := inferInstance
  classifies := by
    intro X _ E _ _ _ _ _ _
    sorry
  unique := by
    intro X _ f₀ f₁ hIso
    sorry

/-- Theorem 23.7.1: if `EU` is contractible, `EU → BU(n)` is a principal
`U(n)`-bundle for the quotient model `BU(n) := EU /[U(n)]`, and `γBU` is a chosen universal complex
`n`-plane bundle over this quotient model whose classes are identified with the principal
`U(n)`-bundle classes coming from `EU → BU(n)`, then the quotient-model classifying assignment
`[X, BU(n)] → ComplexPlaneBundle.classes n X` is bijective. -/
theorem complexPlaneBundleClassifyingMap_bijective
    [ContractibleSpace EU]
    [IsPrincipalBundleMap (U n)
      (Quotient.mk'' : EU → BU[n, EU])]
    [ComplexPlaneBundleQuotientModel n EU γBU] :
    Function.Bijective (quotientModelComplexPlaneBundleClassifyingMap n EU γBU X) := by
  constructor <;> sorry

end Classifying

end
