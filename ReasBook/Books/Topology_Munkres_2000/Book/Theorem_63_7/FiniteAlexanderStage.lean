module

public import Topology_Munkres_2000.Book.Theorem_62_1.CechDiagram
public import Topology_Munkres_2000.Book.Theorem_62_1.FiniteRelativeDuality
public import Topology_Munkres_2000.Book.Theorem_62_1.ReducedHomologyZero
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

public section

namespace InvarianceOfDomainSupport

open CategoryTheory

/-- Helper for Theorem 63.7: the universe-lifted ordinary face-nerve
cohomology used by positive-degree finite Alexander stages. -/
noncomputable abbrev liftedFaceNerveCohomology
    {X : Type} [TopologicalSpace X]
    (U : CechFiniteOpenCover.{0, 0} X) (q : ℕ) :
    ModuleCat.{1} (ZMod 2) :=
  (ModuleCat.uliftFunctor.{1, 0} (ZMod 2)).obj
    (ModuleCat.of (ZMod 2) (CechFiniteOpenCover.faceNerveCohomology U q))

/-- Helper for Theorem 63.7: an adapted finite Alexander stage combines a
finite Čech cover with verified dual-cell and ambient complement data. -/
structure FiniteAlexanderStage (K X : TopCat.{0}) (q : ℕ) where
  /-- The cohomological degree is positive. -/
  positiveDegree : 0 < q
  /-- The finite cover supplying the Čech stage. -/
  cover : CechFiniteOpenCover.{0, 0} K
  /-- Vertices of the finite dual graph. -/
  vertex : Type
  /-- The dual graph has finitely many vertices. -/
  [vertexFintype : Fintype vertex]
  /-- The finite dual graph. -/
  graph : SimpleGraph vertex
  /-- Equality of graph vertices is decidable. -/
  [vertexDecidableEq : DecidableEq vertex]
  /-- Graph adjacency is decidable. -/
  [adjDecidable : DecidableRel graph.Adj]
  /-- A model space for the finite-stage complement. -/
  modelSpace : Type
  /-- The model complement carries its geometric topology. -/
  [modelTopology : TopologicalSpace modelSpace]
  /-- Path components of the model complement are the graph components. -/
  componentEquiv : ZerothHomotopy modelSpace ≃ graph.ConnectedComponent
  /-- The model complement includes into the actual complement. -/
  inclusion : modelSpace → X
  /-- The model-complement inclusion is continuous. -/
  inclusionContinuous : Continuous inclusion
  /-- The finite Čech cohomology stage is the lifted reduced homology of the
  verified dual graph. -/
  finiteDuality :
    liftedFaceNerveCohomology cover q ≅
      (ModuleCat.uliftFunctor.{1, 0} (ZMod 2)).obj
        (ModuleCat.of (ZMod 2) (graphReducedHomologyZeroModTwo graph))

namespace FiniteAlexanderStage

/-- Helper for Theorem 63.7: recover the stored finite vertex structure of an
Alexander stage through typeclass inference. -/
instance vertexFintypeInstance
    {K X : TopCat.{0}} {q : ℕ} (A : FiniteAlexanderStage K X q) :
    Fintype A.vertex := A.vertexFintype

/-- Helper for Theorem 63.7: recover decidable equality on the vertices of an
Alexander stage through typeclass inference. -/
instance vertexDecidableEqInstance
    {K X : TopCat.{0}} {q : ℕ} (A : FiniteAlexanderStage K X q) :
    DecidableEq A.vertex := A.vertexDecidableEq

/-- Helper for Theorem 63.7: recover decidable graph adjacency from an
Alexander stage through typeclass inference. -/
instance adjacencyDecidableInstance
    {K X : TopCat.{0}} {q : ℕ} (A : FiniteAlexanderStage K X q) :
    DecidableRel A.graph.Adj := A.adjDecidable

/-- Helper for Theorem 63.7: recover the model-space topology stored in an
Alexander stage through typeclass inference. -/
instance modelTopologyInstance
    {K X : TopCat.{0}} {q : ℕ} (A : FiniteAlexanderStage K X q) :
    TopologicalSpace A.modelSpace := A.modelTopology

/-- Helper for Theorem 63.7: reduced graph homology is identified with the
augmentation kernel on components of the stage graph. -/
noncomputable def graphComponentKernelIso
    {K X : TopCat.{0}} {q : ℕ} (A : FiniteAlexanderStage K X q) :
    ModuleCat.of (ZMod 2) (graphReducedHomologyZeroModTwo A.graph) ≅
      ModuleCat.of (ZMod 2)
        (LinearMap.ker
          (componentAugmentationModTwo A.graph.ConnectedComponent)) :=
  (Classical.choice
    (graphReducedHomologyZeroModTwo_linearEquiv_componentKernel A.graph)).toModuleIso

/-- Helper for Theorem 63.7: the component equivalence transports graph
component chains to model-complement component chains. -/
noncomputable def graphToModelComponentKernelIso
    {K X : TopCat.{0}} {q : ℕ} (A : FiniteAlexanderStage K X q) :
    ModuleCat.of (ZMod 2)
        (LinearMap.ker
          (componentAugmentationModTwo A.graph.ConnectedComponent)) ≅
      ModuleCat.of (ZMod 2)
        (LinearMap.ker
          (componentAugmentationModTwo (ZerothHomotopy A.modelSpace))) :=
  (componentAugmentationKernelLinearEquiv A.componentEquiv.symm).toModuleIso

/-- Helper for Theorem 63.7: the model inclusion pushes component chains into
the actual complement's component chains. -/
noncomputable def modelToTargetComponentKernel
    {K X : TopCat.{0}} {q : ℕ} (A : FiniteAlexanderStage K X q) :
    ModuleCat.of (ZMod 2)
        (LinearMap.ker
          (componentAugmentationModTwo (ZerothHomotopy A.modelSpace))) ⟶
      ModuleCat.of (ZMod 2)
        (LinearMap.ker (componentAugmentationModTwo (ZerothHomotopy X))) :=
  ModuleCat.ofHom
    (componentAugmentationKernelMapOfFunction
      (zerothHomotopyMap A.inclusion A.inclusionContinuous))

/-- Helper for Theorem 63.7: canonical reduced mod-two `H₀` is identified with
the augmentation kernel on components of the target complement. -/
noncomputable def targetHomologyComponentKernelIso
    {K X : TopCat.{0}} {q : ℕ} (_A : FiniteAlexanderStage K X q) :
    reducedHomologyZeroModTwo X ≅
      ModuleCat.of (ZMod 2)
        (LinearMap.ker (componentAugmentationModTwo (ZerothHomotopy X))) :=
  (Classical.choice
    (nonempty_reducedHomologyZeroModTwo_linearEquiv_componentKernel X)).toModuleIso

/-- Helper for Theorem 63.7: the verified finite graph homology maps to
reduced mod-two `H₀` of the actual complement. -/
noncomputable def unliftedAlexanderMap
    {K X : TopCat.{0}} {q : ℕ} (A : FiniteAlexanderStage K X q) :
    ModuleCat.of (ZMod 2) (graphReducedHomologyZeroModTwo A.graph) ⟶
      reducedHomologyZeroModTwo X :=
  A.graphComponentKernelIso.hom ≫ A.graphToModelComponentKernelIso.hom ≫
      A.modelToTargetComponentKernel ≫ A.targetHomologyComponentKernelIso.inv

/-- Helper for Theorem 63.7: an adapted finite stage supplies a concrete
Alexander morphism into lifted reduced mod-two `H₀` of the actual complement. -/
noncomputable def alexanderMap
    {K X : TopCat.{0}} {q : ℕ} (A : FiniteAlexanderStage K X q) :
    liftedFaceNerveCohomology A.cover q ⟶
      (ModuleCat.uliftFunctor.{1, 0} (ZMod 2)).obj
        (reducedHomologyZeroModTwo X) :=
  A.finiteDuality.hom ≫
    (ModuleCat.uliftFunctor.{1, 0} (ZMod 2)).map A.unliftedAlexanderMap

end FiniteAlexanderStage

end InvarianceOfDomainSupport

end
