module

public import Topology_Munkres_2000.Book.Remark_60_1.AntipodalCover
public import Topology_Munkres_2000.Book.Remark_60_1.SimplexCochains
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory
open unitInterval

/-- Helper for Remark 60.1: the additive fiber equivalence returns `g`
exactly when the second fiber point is the translate of the first by `g`. -/
lemma _root_.IsAddQuotientCoveringMap.fiberEquivAddGroup_eq_iff
    {E X G : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [AddGroup G] [AddAction G E] {p : E → X}
    (hp : IsAddQuotientCoveringMap p G) {x : X}
    (e e' : p ⁻¹' {x}) (g : G) :
    hp.fiberEquivAddGroup e e' = g ↔ (e' : E) = g +ᵥ (e : E) := by
  -- This is the additive computation rule for the inverse orbit equivalence.
  rw [IsAddQuotientCoveringMap.fiberEquivAddGroup, Equiv.symm_apply_eq,
    Equiv.ofBijective_apply, Subtype.mk.injEq]

/-- Helper for Remark 60.1: identify the additive Boolean group with the
additive group of integers modulo two. -/
def boolToZModTwo (b : Bool) : ZMod 2 :=
  if b then 1 else 0

/-- Helper for Remark 60.1: the Boolean-to-mod-two identification preserves
addition. -/
lemma boolToZModTwo_add (b c : Bool) :
    boolToZModTwo (b + c) = boolToZModTwo b + boolToZModTwo c := by
  -- Both groups have two elements, so the homomorphism law is a finite check.
  cases b <;> cases c <;> decide

/-- Helper for Remark 60.1: the Boolean identity maps to zero modulo two. -/
lemma boolToZModTwo_zero : boolToZModTwo 0 = 0 := by
  -- This is the identity case of the explicit two-element identification.
  rfl

/-- Helper for Remark 60.1: the nonidentity Boolean deck transformation maps
to one modulo two. -/
lemma boolToZModTwo_true : boolToZModTwo true = 1 := by
  -- This is the nonidentity case of the explicit two-element identification.
  rfl

/-- Helper for Remark 60.1: a chosen point in the fiber over `x` projects back
to `x`. -/
lemma chosenFiberPoint_projects
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : E → X) (s : ∀ x : X, p ⁻¹' {x}) (x : X) :
    p (s x : E) = x := by
  -- Unpack membership in the singleton fiber.
  exact Set.mem_singleton_iff.mp (s x).property

/-- Helper for Remark 60.1: the endpoint of the lift begun at the chosen
source point lies over the endpoint of the base path. -/
lemma liftedPathEndpoint_mem_fiber
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    (p : E → X) (hp : IsCoveringMap p)
    (s : ∀ x : X, p ⁻¹' {x}) (γ : C(I, X)) :
    hp.liftPath γ (s (γ 0) : E)
        (chosenFiberPoint_projects p s (γ 0)).symm 1 ∈ p ⁻¹' {γ 1} := by
  -- Evaluate the defining lift equation at the terminal endpoint.
  exact congrFun
    (hp.liftPath_lifts γ (s (γ 0) : E)
      (chosenFiberPoint_projects p s (γ 0)).symm) 1

/-- Helper for Remark 60.1: a morphism from the universe-lifted interval used
by `TopCat` determines an ordinary path by the canonical interval homeomorphism. -/
def topCatIntervalMorphismToPath
    {X : Type} [TopologicalSpace X]
    (γ : TopCat.I ⟶ TopCat.of X) : C(I, X) :=
  γ.hom.comp
    ⟨TopCat.I.homeomorph.symm, TopCat.I.homeomorph.symm.continuous⟩

/-- Helper for Remark 60.1: evaluate the ordinary path underlying a `TopCat`
interval morphism through the interval homeomorphism. -/
lemma topCatIntervalMorphismToPath_apply
    {X : Type} [TopologicalSpace X]
    (γ : TopCat.I ⟶ TopCat.of X) (t : I) :
    topCatIntervalMorphismToPath γ t = γ (TopCat.I.homeomorph.symm t) := by
  -- This is the pointwise computation rule of the defining composition.
  rfl

/-- Helper for Remark 60.1: the path of a singular edge evaluates its
representing simplex map on the canonical standard one-simplex point. -/
lemma topCatIntervalMorphismToPath_toSSetObj₁Equiv_apply
    {X : Type} [TopologicalSpace X]
    (edge : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) (t : I) :
    topCatIntervalMorphismToPath (TopCat.toSSetObj₁Equiv edge) t =
      (TopCat.of X).toSSetObjEquiv _ edge
        (TopCat.stdSimplexHomeomorphI.symm
          (TopCat.I.homeomorph.symm t)) := by
  -- Expand the two canonical interval changes once at their common owner.
  rfl

/-- Helper for Remark 60.1: the transition of a path in a Boolean quotient
cover compares its lifted endpoint with the chosen point in the terminal fiber. -/
noncomputable def boolCoverPathTransition
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x}) (γ : C(I, X)) : Bool :=
  hp.fiberEquivAddGroup (s (γ 1))
    ⟨hp.isCoveringMap.liftPath γ (s (γ 0) : E)
        (chosenFiberPoint_projects p s (γ 0)).symm 1,
      liftedPathEndpoint_mem_fiber p hp.isCoveringMap s γ⟩

/-- Helper for Remark 60.1: an endpoint computation for the canonical lifted
path determines its Boolean deck transition. -/
lemma boolCoverPathTransition_eq_of_endpoint
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x}) (γ : C(I, X)) (b : Bool)
    (hendpoint :
      hp.isCoveringMap.liftPath γ (s (γ 0) : E)
          (chosenFiberPoint_projects p s (γ 0)).symm 1 =
        b +ᵥ (s (γ 1) : E)) :
    boolCoverPathTransition p hp s γ = b := by
  -- The quotient-cover fiber equivalence is characterized by the deck action
  -- on its chosen base point.
  exact (hp.fiberEquivAddGroup_eq_iff (s (γ 1))
    ⟨hp.isCoveringMap.liftPath γ (s (γ 0) : E)
        (chosenFiberPoint_projects p s (γ 0)).symm 1,
      liftedPathEndpoint_mem_fiber p hp.isCoveringMap s γ⟩ b).2 hendpoint

/-- Helper for Remark 60.1: any explicitly exhibited lift computes the Boolean
transition once its terminal deck translate is known. -/
lemma boolCoverPathTransition_eq_of_explicitLift
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x}) (γ : C(I, X)) (Γ : C(I, E)) (b : Bool)
    (hprojection : p ∘ Γ = γ)
    (hsource : Γ 0 = (s (γ 0) : E))
    (htarget : Γ 1 = b +ᵥ (s (γ 1) : E)) :
    boolCoverPathTransition p hp s γ = b := by
  -- Uniqueness of path lifting identifies `Γ` with the canonical lift, after
  -- which the terminal-point computation gives the transition.
  have hlift : Γ = hp.isCoveringMap.liftPath γ (s (γ 0) : E)
      (chosenFiberPoint_projects p s (γ 0)).symm :=
    (hp.isCoveringMap.eq_liftPath_iff' _).2 ⟨hprojection, hsource⟩
  apply boolCoverPathTransition_eq_of_endpoint p hp s γ b
  calc
    hp.isCoveringMap.liftPath γ (s (γ 0) : E)
        (chosenFiberPoint_projects p s (γ 0)).symm 1 = Γ 1 :=
      congrArg (fun path : C(I, E) ↦ path 1) hlift.symm
    _ = b +ᵥ (s (γ 1) : E) := htarget

/-- Helper for Remark 60.1: a singular edge has the transition of its path
lift in the fixed Boolean quotient cover. -/
noncomputable def boolCoverEdgeTransition
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x})
    (edge : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) : Bool :=
  boolCoverPathTransition p hp s
    (topCatIntervalMorphismToPath (TopCat.toSSetObj₁Equiv edge))

/-- Helper for Remark 60.1: the transition of a singular edge is computed by
the interval path underlying that edge. -/
lemma boolCoverEdgeTransition_eq_pathTransition
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x})
    (edge : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    boolCoverEdgeTransition p hp s edge =
      boolCoverPathTransition p hp s
        (topCatIntervalMorphismToPath (TopCat.toSSetObj₁Equiv edge)) := by
  -- Expose only the stable path computation rule of the edge transition.
  rfl

/-- Helper for Remark 60.1: the transition values of a Boolean quotient cover
extend linearly to a mod-two singular one-cochain. -/
noncomputable def boolCoverParityCochain
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x}) :
    singularCochainGroupWithCoefficients
      (TopCat.of X) (ModuleCat.of ℤ (ZMod 2)) 1 :=
  singularCochainOfSimplexValues (TopCat.of X) (ModuleCat.of ℤ (ZMod 2)) 1
    (fun edge ↦ boolToZModTwo (boolCoverEdgeTransition p hp s edge))

/-- Helper for Remark 60.1: the Boolean-cover parity cochain evaluates on an
edge generator as its deck transition modulo two. -/
lemma boolCoverParityCochain_generator
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x})
    (edge : (TopCat.toSSet.obj (TopCat.of X)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    boolCoverParityCochain p hp s
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) edge |>.hom 1) =
      boolToZModTwo (boolCoverEdgeTransition p hp s edge) := by
  -- Apply the generator computation rule of the coproduct-defined cochain.
  exact singularCochainOfSimplexValues_generator
    (TopCat.of X) (ModuleCat.of ℤ (ZMod 2)) 1 _ edge

/-- Helper for Remark 60.1: if transitions compose around every singular
two-simplex, then the Boolean-cover parity cochain is a cocycle. -/
lemma boolCoverParityCochain_isCocycle_of_triangle
    {E X : Type} [TopologicalSpace E] [TopologicalSpace X]
    [AddAction Bool E]
    (p : E → X) (hp : IsAddQuotientCoveringMap p Bool)
    (s : ∀ x : X, p ⁻¹' {x})
    (htriangle : ∀ simplex :
        (TopCat.toSSet.obj (TopCat.of X)).obj
          (Opposite.op (SimplexCategory.mk 2)),
      boolCoverEdgeTransition p hp s
          ((TopCat.toSSet.obj (TopCat.of X)).δ 1 simplex) =
        boolCoverEdgeTransition p hp s
            ((TopCat.toSSet.obj (TopCat.of X)).δ 0 simplex) +
          boolCoverEdgeTransition p hp s
            ((TopCat.toSSet.obj (TopCat.of X)).δ 2 simplex)) :
    ((singularCochainComplexWithCoefficients
      (TopCat.of X) (ModuleCat.of ℤ (ZMod 2))).d 1 2).hom
        (boolCoverParityCochain p hp s) = 0 := by
  -- The generic coproduct lemma reduces the coboundary to the alternating
  -- sum of the three edge-transition values.
  apply singularCochainOfSimplexValues_isCocycle
  intro simplex
  have htransition := congrArg boolToZModTwo (htriangle simplex)
  rw [boolToZModTwo_add] at htransition
  rw [Fin.sum_univ_three]
  norm_num
  rw [htransition]
  abel

end AlgebraicTopology

namespace RealProjectivePlane

open AlgebraicTopology

/-- Helper for Remark 60.1: every fiber of the antipodal quotient contains a
sphere point. -/
lemma quotientMapFiber_nonempty (x : RealProjectivePlane) :
    Nonempty (quotientMap ⁻¹' {x}) := by
  -- Surjectivity supplies a representative of the projective point.
  obtain ⟨e, he⟩ := quotientMap_isQuotientMap.surjective x
  exact ⟨⟨e, Set.mem_singleton_iff.mpr he⟩⟩

/-- Helper for Remark 60.1: fix one sphere representative in every projective
fiber for the transition-cochain construction. -/
noncomputable def antipodalFiberChoice
    (x : RealProjectivePlane) : quotientMap ⁻¹' {x} :=
  Classical.choice (quotientMapFiber_nonempty x)

/-- Helper for Remark 60.1: the fixed sphere representative projects to its
projective point. -/
lemma quotientMap_antipodalFiberChoice (x : RealProjectivePlane) :
    quotientMap (antipodalFiberChoice x : UnitSphereThree) = x := by
  -- This is the membership property of the chosen fiber point.
  exact chosenFiberPoint_projects quotientMap antipodalFiberChoice x

/-- Helper for Remark 60.1: the antipodal double cover's transition cochain
with respect to the fixed fiber representatives. -/
noncomputable def antipodalParityCochain :
    singularCochainGroupWithCoefficients
      (TopCat.of RealProjectivePlane) (ModuleCat.of ℤ (ZMod 2)) 1 :=
  boolCoverParityCochain quotientMap quotientMap_isAddQuotientCoveringMap
    antipodalFiberChoice

/-- Helper for Remark 60.1: the antipodal parity cochain is the generic
Boolean-cover cochain specialized to the antipodal quotient. -/
lemma antipodalParityCochain_eq_boolCoverParityCochain :
    antipodalParityCochain =
      boolCoverParityCochain quotientMap quotientMap_isAddQuotientCoveringMap
        antipodalFiberChoice := by
  -- Expose the specialization without unfolding it at downstream call sites.
  rfl

/-- Helper for Remark 60.1: the antipodal parity cochain evaluates on a
singular edge generator as that edge's lifted deck transition. -/
lemma antipodalParityCochain_generator
    (edge : (TopCat.toSSet.obj (TopCat.of RealProjectivePlane)).obj
      (Opposite.op (SimplexCategory.mk 1))) :
    antipodalParityCochain
        ((TopCat.toSSet.obj (TopCat.of RealProjectivePlane)).ιChainComplex
          (R := ModuleCat.of ℤ ℤ) edge |>.hom 1) =
      boolToZModTwo
        (boolCoverEdgeTransition quotientMap
          quotientMap_isAddQuotientCoveringMap antipodalFiberChoice edge) := by
  -- Specialize the generic Boolean-cover generator computation.
  exact boolCoverParityCochain_generator quotientMap
    quotientMap_isAddQuotientCoveringMap antipodalFiberChoice edge

end RealProjectivePlane
