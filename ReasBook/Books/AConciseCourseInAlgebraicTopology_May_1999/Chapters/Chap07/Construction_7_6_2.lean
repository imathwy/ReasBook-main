import Mathlib.Topology.Homotopy.Path
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} E]
variable [CompactlyGeneratedWeakHausdorffSpace.{v, v} B]

-- Semantic recall via `lean_leansearch`: `Path.toHomotopyConst` is the canonical homotopy
-- between constant maps determined by a path, so the source-faithful statement lifts that base
-- homotopy over the fiber `fiber p b`.

/-- Construction 7.6.2: if `p : C(E, B)` is a fibration and `β : Path b b'`, then the covering
homotopy property lifts the constant-map homotopy `β.toHomotopyConst` on `fiber p b` to a
homotopy in `E` beginning with the inclusion `fiberInclusion p b`. -/
theorem exists_fiberInclusionHomotopyLift (p : C(E, B)) [hp : IsFibration.{u, v, u} p]
    {b b' : B}
    (β : Path b b') :
    ∃ g₁ : C(fiber p b, E), ∃ G : (fiberInclusion p b).Homotopy g₁,
      p.comp G.toContinuousMap = β.toHomotopyConst.toContinuousMap := by
  -- Apply the covering homotopy property to the constant homotopy induced by `β`.
  simpa using IsFibration.exists_homotopyLift.{u, v, u}
    (p := p) (hp := hp) (A := ↥(fiber p b)) (g₀ := fiberInclusion p b)
    β.toHomotopyConst (comp_fiberInclusion p b)

/-- Any lifted homotopy from Construction 7.6.2 ends at a map into the fiber over `b'`. -/
theorem comp_endpoint_eq_const_of_fiberInclusionHomotopyLift (p : C(E, B)) {b b' : B}
    {β : Path b b'} {g₁ : C(fiber p b, E)}
    (G : (fiberInclusion p b).Homotopy g₁)
    (hG : p.comp G.toContinuousMap = β.toHomotopyConst.toContinuousMap) :
    p.comp g₁ = ContinuousMap.const (fiber p b) b' := by
  -- Evaluate the lifted homotopy identity at time `1` to read off the endpoint map.
  ext x
  change p (g₁ x) = b'
  rw [← G.apply_one x]
  have h := ContinuousMap.congr_fun hG (1, x)
  simpa using h

/-- Helper for Construction 7.6.2: the endpoint map of a lifted homotopy lands in the fiber over
`b'` once its composition with `p` is the constant map at `b'`. -/
theorem fiberInclusionHomotopyLiftEndpointMap_memFiber (p : C(E, B)) {b b' : B}
    (g₁ : C(fiber p b, E)) (hg₁ : p.comp g₁ = ContinuousMap.const (fiber p b) b')
    (x : fiber p b) :
    g₁ x ∈ fiber p b' := by
  -- Rewrite the continuous-map equality at `x` to obtain the fiber membership condition.
  rw [mem_fiber_iff]
  have h := ContinuousMap.congr_fun hg₁ x
  simpa using h

/-- Helper for Construction 7.6.2: the subtype-valued endpoint map is continuous because the
underlying endpoint map is continuous and every value lies in the target fiber. -/
theorem fiberInclusionHomotopyLiftEndpointMap_continuous (p : C(E, B)) {b b' : B}
    (g₁ : C(fiber p b, E)) (hg₁ : p.comp g₁ = ContinuousMap.const (fiber p b) b') :
    Continuous fun x : fiber p b ↦
      (⟨g₁ x, fiberInclusionHomotopyLiftEndpointMap_memFiber p g₁ hg₁ x⟩ : fiber p b') := by
  -- Promote the continuous endpoint map to a map into the subtype using the membership lemma.
  exact g₁.continuous.subtype_mk fun x ↦
    fiberInclusionHomotopyLiftEndpointMap_memFiber p g₁ hg₁ x

/-- An endpoint map `g₁ : fiber p b ⟶ E` whose image lies in the fiber over `b'` can be regarded
as a map `fiber p b ⟶ fiber p b'`. -/
def fiberInclusionHomotopyLiftEndpointMap (p : C(E, B)) {b b' : B} (g₁ : C(fiber p b, E))
    (hg₁ : p.comp g₁ = ContinuousMap.const (fiber p b) b') : C(fiber p b, fiber p b') :=
  ⟨fun x ↦ ⟨g₁ x, fiberInclusionHomotopyLiftEndpointMap_memFiber p g₁ hg₁ x⟩,
    fiberInclusionHomotopyLiftEndpointMap_continuous p g₁ hg₁⟩

/-- Forgetting the target-fiber subtype of `fiberInclusionHomotopyLiftEndpointMap` recovers the
original endpoint map `g₁`. -/
@[simp] theorem fiberInclusionHomotopyLiftEndpointMap_apply (p : C(E, B)) {b b' : B}
    (g₁ : C(fiber p b, E)) (hg₁ : p.comp g₁ = ContinuousMap.const (fiber p b) b')
    (x : fiber p b) :
    ((fiberInclusionHomotopyLiftEndpointMap p g₁ hg₁ x : fiber p b') : E) = g₁ x :=
  rfl

/-- Composing the endpoint map into `fiber p b'` with the fiber inclusion recovers its
`E`-valued endpoint map. -/
@[simp] theorem comp_fiberInclusionHomotopyLiftEndpointMap (p : C(E, B)) {b b' : B}
    (g₁ : C(fiber p b, E)) (hg₁ : p.comp g₁ = ContinuousMap.const (fiber p b) b') :
    (fiberInclusion p b').comp (fiberInclusionHomotopyLiftEndpointMap p g₁ hg₁) = g₁ := by
  ext x
  rfl

/-- Construction 7.6.2 also yields a time-one endpoint map from `fiber p b` into the fiber over
`b'`. -/
theorem exists_fiberInclusionHomotopyLiftEndpoint (p : C(E, B)) [hp : IsFibration.{u, v, u} p]
    {b b' : B} (β : Path b b') :
    ∃ g₁ : C(fiber p b, fiber p b'),
      ∃ G : (fiberInclusion p b).Homotopy ((fiberInclusion p b').comp g₁),
        p.comp G.toContinuousMap = β.toHomotopyConst.toContinuousMap := by
  -- First choose a lifted homotopy in `E`, then package its endpoint into the target fiber.
  rcases exists_fiberInclusionHomotopyLift p β with ⟨g₁, G, hG⟩
  let hg₁ := comp_endpoint_eq_const_of_fiberInclusionHomotopyLift p G hG
  refine ⟨fiberInclusionHomotopyLiftEndpointMap p g₁ hg₁, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa using G
  · simpa using hG
