module

public import Topology_Munkres_2000.Book.Definition_35_4.AdjunctionSpace
public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction
public import Topology_Munkres_2000.Book.Definition_58_3.HomotopyType
public import Topology_Munkres_2000.Book.Proposition_58_1
public import Topology_Munkres_2000.Book.Theorem_58_1.HomotopyExtension

public section

universe u v

open scoped ContinuousMap
open unitInterval

section MappingCylinder

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Helper for Theorem 58.1: the attaching end of the cylinder `X × I`. -/
private def mappingCylinderBase (X : Type u) [TopologicalSpace X] : Set (X × I) :=
  {p | p.2 = 0}

/-- Helper for Theorem 58.1: the mapping-cylinder attaching map is continuous. -/
private lemma continuous_mappingCylinderAttachment (f : C(X, Y)) :
    Continuous (fun p : mappingCylinderBase X ↦ f p.1.1) := by
  -- The attaching map is the first projection followed by `f`.
  fun_prop

/-- Helper for Theorem 58.1: the map attaching `(x, 0)` to `f x`. -/
private def mappingCylinderAttachment (f : C(X, Y)) : C(mappingCylinderBase X, Y) :=
  ⟨fun p ↦ f p.1.1, continuous_mappingCylinderAttachment f⟩

/-- Helper for Theorem 58.1: evaluation of the attaching map forgets the zero-height
coordinate and applies `f`. -/
private lemma mappingCylinderAttachment_apply (f : C(X, Y))
    (a : mappingCylinderBase X) : mappingCylinderAttachment f a = f a.1.1 := by
  -- Unpack only the local continuous-map wrapper.
  rfl

/-- Helper for Theorem 58.1: the mapping cylinder of a continuous map. -/
private abbrev MappingCylinder (f : C(X, Y)) : Type (max u v) :=
  AdjunctionSpace (mappingCylinderBase X) (mappingCylinderAttachment f)

/-- Helper for Theorem 58.1: the top inclusion into a mapping cylinder is continuous. -/
private lemma continuous_mappingCylinderTop (f : C(X, Y)) :
    Continuous (fun x ↦ AdjunctionSpace.includeX (mappingCylinderBase X)
      (mappingCylinderAttachment f) (x, 1)) := by
  -- Insert the top endpoint continuously into the cylinder summand.
  exact (AdjunctionSpace.continuous_includeX _ _).comp (continuous_id.prodMk continuous_const)

/-- Helper for Theorem 58.1: the canonical top copy of `X` in a mapping cylinder. -/
private def mappingCylinderTop (f : C(X, Y)) : C(X, MappingCylinder f) :=
  ⟨fun x ↦ AdjunctionSpace.includeX (mappingCylinderBase X)
    (mappingCylinderAttachment f) (x, 1), continuous_mappingCylinderTop f⟩

/-- Helper for Theorem 58.1: the bottom inclusion into a mapping cylinder is continuous. -/
private lemma continuous_mappingCylinderBottom (f : C(X, Y)) :
    Continuous (AdjunctionSpace.includeY (mappingCylinderBase X)
      (mappingCylinderAttachment f)) := by
  -- The bottom copy is the canonical inclusion of the adjunction-space target.
  exact AdjunctionSpace.continuous_includeY _ _

/-- Helper for Theorem 58.1: the canonical bottom copy of `Y` in a mapping cylinder. -/
private def mappingCylinderBottom (f : C(X, Y)) : C(Y, MappingCylinder f) :=
  ⟨AdjunctionSpace.includeY (mappingCylinderBase X) (mappingCylinderAttachment f),
    continuous_mappingCylinderBottom f⟩

/-- Helper for Theorem 58.1: evaluation of the bundled bottom inclusion is the canonical
adjunction-space inclusion. -/
private lemma mappingCylinderBottom_apply (f : C(X, Y)) (y : Y) :
    mappingCylinderBottom f y =
      AdjunctionSpace.includeY (mappingCylinderBase X) (mappingCylinderAttachment f) y := by
  -- Unpack only the local continuous-map wrapper.
  rfl

/-- Helper for Theorem 58.1: the subset occupied by the top copy of `X`. -/
private def mappingCylinderTopRange (f : C(X, Y)) : Set (MappingCylinder f) :=
  Set.range (mappingCylinderTop f)

/-- Helper for Theorem 58.1: the subset occupied by the bottom copy of `Y`. -/
private def mappingCylinderBottomRange (f : C(X, Y)) : Set (MappingCylinder f) :=
  Set.range (mappingCylinderBottom f)

/-- Helper for Theorem 58.1: the cylinder projection agrees with the identity on the
attaching end. -/
private lemma mappingCylinderProjection_agrees (f : C(X, Y)) (a : mappingCylinderBase X) :
    f a.1.1 = ContinuousMap.id Y (mappingCylinderAttachment f a) := by
  -- Both sides are definitionally `f a.1.1`.
  rfl

/-- Helper for Theorem 58.1: projection of the mapping cylinder onto its bottom copy. -/
private def mappingCylinderProjection (f : C(X, Y)) : C(MappingCylinder f, Y) :=
  ⟨AdjunctionSpace.lift (mappingCylinderBase X) (mappingCylinderAttachment f)
      (f.comp ContinuousMap.fst) (ContinuousMap.id Y) (mappingCylinderProjection_agrees f),
    AdjunctionSpace.continuous_lift _ _ _ _ (mappingCylinderProjection_agrees f)⟩

/-- Helper for Theorem 58.1: the bottom projection is a left inverse to the bottom inclusion. -/
private lemma mappingCylinderProjection_leftInverse (f : C(X, Y)) :
    Function.LeftInverse (mappingCylinderProjection f) (mappingCylinderBottom f) := by
  -- The quotient lift computes as the identity on the bottom summand.
  intro y
  exact AdjunctionSpace.lift_includeY _ _ _ _ _ y

/-- Helper for Theorem 58.1: projection computes as `f` on the cylinder summand. -/
private lemma mappingCylinderProjection_includeX (f : C(X, Y)) (p : X × I) :
    mappingCylinderProjection f
      (AdjunctionSpace.includeX (mappingCylinderBase X) (mappingCylinderAttachment f) p) =
        f p.1 := by
  -- This is the left-summand computation rule for the quotient lift.
  exact AdjunctionSpace.lift_includeX _ _ _ _ _ p

/-- Helper for Theorem 58.1: the bottom inclusion is a topological embedding. -/
private lemma mappingCylinderBottom_isEmbedding (f : C(X, Y)) :
    Topology.IsEmbedding (mappingCylinderBottom f) := by
  -- A continuous map with a continuous left inverse is an embedding.
  exact (mappingCylinderProjection_leftInverse f).isEmbedding
    (mappingCylinderProjection f).continuous (mappingCylinderBottom f).continuous

/-- Helper for Theorem 58.1: `Y` is homeomorphic to the bottom range in its mapping cylinder. -/
private noncomputable def mappingCylinderBottomHomeomorph (f : C(X, Y)) :
    Y ≃ₜ mappingCylinderBottomRange f :=
  (mappingCylinderBottom_isEmbedding f).toHomeomorph

/-- Helper for Theorem 58.1: continuity of the path that shrinks one cylinder segment
toward its attaching endpoint. -/
private lemma continuous_mappingCylinderShrinkPath (f : C(X, Y)) (p : X × I) :
    Continuous (fun s : I ↦ AdjunctionSpace.includeX (mappingCylinderBase X)
      (mappingCylinderAttachment f) (p.1, σ s * p.2)) := by
  -- Multiplication by `1 - s` varies continuously in the interval coordinate.
  apply (AdjunctionSpace.continuous_includeX _ _).comp
  apply continuous_const.prodMk
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp unitInterval.continuous_symm).mul continuous_const

/-- Helper for Theorem 58.1: the shrinking path of a point in the cylinder summand. -/
private def mappingCylinderShrinkPath (f : C(X, Y)) (p : X × I) :
    C(I, MappingCylinder f) :=
  ⟨fun s ↦ AdjunctionSpace.includeX (mappingCylinderBase X)
    (mappingCylinderAttachment f) (p.1, σ s * p.2),
    continuous_mappingCylinderShrinkPath f p⟩

/-- Helper for Theorem 58.1: shrinking an attaching point gives the constant path at its
bottom image. -/
private lemma mappingCylinderShrinkPath_agrees (f : C(X, Y))
    (a : mappingCylinderBase X) :
    mappingCylinderShrinkPath f a =
      ContinuousMap.const I (mappingCylinderBottom f (mappingCylinderAttachment f a)) := by
  -- At height zero every shrunken representative is identified with its attached image.
  ext s
  have hCoordinate : σ s * a.1.2 = 0 := by
    rw [a.2, mul_zero]
  have hPair : (a.1.1, 0) = a.1 := by
    apply Prod.ext
    · rfl
    · exact a.2.symm
  calc
    mappingCylinderShrinkPath f a s =
        AdjunctionSpace.includeX (mappingCylinderBase X) (mappingCylinderAttachment f)
          (a.1.1, 0) := by
            change AdjunctionSpace.includeX (mappingCylinderBase X)
              (mappingCylinderAttachment f) (a.1.1, σ s * a.1.2) = _
            rw [hCoordinate]
    _ = AdjunctionSpace.includeX (mappingCylinderBase X) (mappingCylinderAttachment f) a := by
      exact congrArg (AdjunctionSpace.includeX (mappingCylinderBase X)
        (mappingCylinderAttachment f)) hPair
    _ = mappingCylinderBottom f (mappingCylinderAttachment f a) :=
      AdjunctionSpace.glue _ _ a
    _ = ContinuousMap.const I
        (mappingCylinderBottom f (mappingCylinderAttachment f a)) s := rfl

/-- Helper for Theorem 58.1: the shrinking paths form a continuous family over the cylinder. -/
private lemma continuous_mappingCylinderShrinkPathFamily (f : C(X, Y)) :
    Continuous (fun p : X × I ↦ mappingCylinderShrinkPath f p) := by
  -- Uncurry the family and verify continuity of its two product coordinates.
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply (AdjunctionSpace.continuous_includeX _ _).comp
  apply (continuous_fst.comp continuous_fst).prodMk
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.comp
    (unitInterval.continuous_symm.comp continuous_snd)).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))

/-- Helper for Theorem 58.1: the continuous family of paths shrinking cylinder points. -/
private def mappingCylinderShrinkPathFamily (f : C(X, Y)) :
    C(X × I, C(I, MappingCylinder f)) :=
  ⟨fun p ↦ mappingCylinderShrinkPath f p, continuous_mappingCylinderShrinkPathFamily f⟩

/-- Helper for Theorem 58.1: bottom points determine a continuous family of constant paths. -/
private def mappingCylinderBottomConstantPathFamily (f : C(X, Y)) :
    C(Y, C(I, MappingCylinder f)) :=
  ContinuousMap.const'.comp (mappingCylinderBottom f)

/-- Helper for Theorem 58.1: the adjoint of the bottom-shrinking homotopy is continuous. -/
private lemma continuous_mappingCylinderBottomHomotopyAdjoint (f : C(X, Y)) :
    Continuous (AdjunctionSpace.lift (mappingCylinderBase X) (mappingCylinderAttachment f)
      (mappingCylinderShrinkPathFamily f)
      (mappingCylinderBottomConstantPathFamily f)
      (mappingCylinderShrinkPath_agrees f)) := by
  -- Continuity follows from the quotient-lift companion after currying the interval variable.
  exact AdjunctionSpace.continuous_lift _ _ _ _ (mappingCylinderShrinkPath_agrees f)

/-- Helper for Theorem 58.1: the curried bottom-shrinking homotopy. -/
private def mappingCylinderBottomHomotopyAdjoint (f : C(X, Y)) :
    C(MappingCylinder f, C(I, MappingCylinder f)) :=
  ⟨AdjunctionSpace.lift (mappingCylinderBase X) (mappingCylinderAttachment f)
      (mappingCylinderShrinkPathFamily f)
      (mappingCylinderBottomConstantPathFamily f)
      (mappingCylinderShrinkPath_agrees f),
    continuous_mappingCylinderBottomHomotopyAdjoint f⟩

/-- Helper for Theorem 58.1: the continuous bottom-shrinking map on `I × MappingCylinder f`. -/
private def mappingCylinderBottomHomotopyMap (f : C(X, Y)) :
    C(I × MappingCylinder f, MappingCylinder f) :=
  (mappingCylinderBottomHomotopyAdjoint f).uncurry.comp ContinuousMap.prodSwap

/-- Helper for Theorem 58.1: computation of the bottom homotopy on a cylinder representative. -/
private lemma mappingCylinderBottomHomotopy_includeX (f : C(X, Y)) (s : I) (p : X × I) :
    mappingCylinderBottomHomotopyMap f
      (s, AdjunctionSpace.includeX (mappingCylinderBase X) (mappingCylinderAttachment f) p) =
        mappingCylinderShrinkPath f p s := by
  -- Evaluate the quotient lift before evaluating the resulting path at `s`.
  have hPath := AdjunctionSpace.lift_includeX (mappingCylinderBase X)
    (mappingCylinderAttachment f) (mappingCylinderShrinkPathFamily f)
    (mappingCylinderBottomConstantPathFamily f) (mappingCylinderShrinkPath_agrees f) p
  exact congrArg (fun k : C(I, MappingCylinder f) ↦ k s) hPath

/-- Helper for Theorem 58.1: computation of the bottom homotopy on a bottom representative. -/
private lemma mappingCylinderBottomHomotopy_includeY (f : C(X, Y)) (s : I) (y : Y) :
    mappingCylinderBottomHomotopyMap f (s, mappingCylinderBottom f y) =
      mappingCylinderBottom f y := by
  -- The quotient lift assigns the constant path to every bottom representative.
  have hPath := AdjunctionSpace.lift_includeY (mappingCylinderBase X)
    (mappingCylinderAttachment f) (mappingCylinderShrinkPathFamily f)
    (mappingCylinderBottomConstantPathFamily f) (mappingCylinderShrinkPath_agrees f) y
  exact congrArg (fun k : C(I, MappingCylinder f) ↦ k s) hPath

/-- Helper for Theorem 58.1: the bottom-shrinking homotopy starts at the identity. -/
private lemma mappingCylinderBottomHomotopy_zero (f : C(X, Y))
    (q : MappingCylinder f) : mappingCylinderBottomHomotopyMap f (0, q) = q := by
  -- Check the endpoint on the two canonical families of quotient representatives.
  rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
    (mappingCylinderBase X) (mappingCylinderAttachment f) q with ⟨p, rfl⟩ | ⟨y, rfl⟩
  · rw [mappingCylinderBottomHomotopy_includeX]
    change AdjunctionSpace.includeX (mappingCylinderBase X)
      (mappingCylinderAttachment f) (p.1, σ 0 * p.2) = _
    rw [unitInterval.symm_zero, one_mul]
  · exact mappingCylinderBottomHomotopy_includeY f 0 y

/-- Helper for Theorem 58.1: the bottom-shrinking homotopy ends at the ambient bottom
projection. -/
private lemma mappingCylinderBottomHomotopy_one (f : C(X, Y))
    (q : MappingCylinder f) :
    mappingCylinderBottomHomotopyMap f (1, q) =
      mappingCylinderBottom f (mappingCylinderProjection f q) := by
  -- Check the endpoint on cylinder and bottom representatives separately.
  rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
    (mappingCylinderBase X) (mappingCylinderAttachment f) q with ⟨p, rfl⟩ | ⟨y, rfl⟩
  · rw [mappingCylinderProjection_includeX, mappingCylinderBottomHomotopy_includeX]
    change AdjunctionSpace.includeX (mappingCylinderBase X)
        (mappingCylinderAttachment f) (p.1, σ 1 * p.2) =
      mappingCylinderBottom f (f p.1)
    rw [unitInterval.symm_one, zero_mul]
    exact AdjunctionSpace.glue _ _
      (⟨(p.1, 0), rfl⟩ : mappingCylinderBase X)
  · rw [← mappingCylinderBottom_apply,
      mappingCylinderBottomHomotopy_includeY,
      mappingCylinderProjection_leftInverse]

/-- Helper for Theorem 58.1: the bottom endpoint map lands in the bottom range. -/
private lemma mappingCylinderBottom_mem_range (f : C(X, Y)) (q : MappingCylinder f) :
    mappingCylinderBottom f (mappingCylinderProjection f q) ∈
      mappingCylinderBottomRange f := by
  -- The projection value itself is a range witness.
  exact ⟨mappingCylinderProjection f q, rfl⟩

/-- Helper for Theorem 58.1: the mapping-cylinder projection bundled into the bottom range. -/
private def mappingCylinderBottomRetractionMap (f : C(X, Y)) :
    C(MappingCylinder f, mappingCylinderBottomRange f) :=
  ⟨fun q ↦ ⟨mappingCylinderBottom f (mappingCylinderProjection f q),
      mappingCylinderBottom_mem_range f q⟩,
    (mappingCylinderBottom f).continuous.comp
      (mappingCylinderProjection f).continuous |>.subtype_mk _⟩

/-- Helper for Theorem 58.1: the bottom range map is a left inverse to subtype inclusion. -/
private lemma mappingCylinderBottomRetractionMap_leftInverse (f : C(X, Y)) :
    Function.LeftInverse (mappingCylinderBottomRetractionMap f) Subtype.val := by
  -- A point in the range has a bottom representative, on which projection is the identity.
  rintro ⟨q, y, rfl⟩
  apply Subtype.ext
  exact congrArg (mappingCylinderBottom f) (mappingCylinderProjection_leftInverse f y)

/-- Helper for Theorem 58.1: the canonical retraction onto the bottom range. -/
private def mappingCylinderBottomRetraction (f : C(X, Y)) :
    Set.Retraction (mappingCylinderBottomRange f) :=
  Set.Retraction.ofContinuousMap (mappingCylinderBottomRetractionMap f)
    (mappingCylinderBottomRetractionMap_leftInverse f)

/-- Helper for Theorem 58.1: the bottom-shrinking homotopy fixes its bottom range. -/
private lemma mappingCylinderBottomHomotopy_fixed (f : C(X, Y)) (s : I)
    (q : MappingCylinder f) (hq : q ∈ mappingCylinderBottomRange f) :
    mappingCylinderBottomHomotopyMap f (s, q) = ContinuousMap.id (MappingCylinder f) q := by
  -- Replace the range point by a bottom representative, where the adjoint is constant.
  obtain ⟨y, rfl⟩ := hq
  exact mappingCylinderBottomHomotopy_includeY f s y

/-- Helper for Theorem 58.1: the bottom-shrinking map is a homotopy relative to the
bottom range. -/
private def mappingCylinderBottomHomotopyRel (f : C(X, Y)) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (MappingCylinder f))
      (mappingCylinderBottomRetraction f).toAmbient (mappingCylinderBottomRange f) :=
  { toFun := mappingCylinderBottomHomotopyMap f
    map_zero_left := mappingCylinderBottomHomotopy_zero f
    map_one_left := mappingCylinderBottomHomotopy_one f
    prop' := mappingCylinderBottomHomotopy_fixed f }

/-- Helper for Theorem 58.1: the bottom copy of every mapping cylinder is a deformation
retract and is homeomorphic to `Y`. -/
private lemma mappingCylinderBottomDeformationData (f : C(X, Y)) :
    Set.IsDeformationRetract (mappingCylinderBottomRange f) ∧
      Nonempty (Y ≃ₜ mappingCylinderBottomRange f) := by
  -- Package the explicit retraction and relative shrinking homotopy, then the range homeomorphism.
  constructor
  · apply (Set.isDeformationRetract_iff _).2
    exact ⟨mappingCylinderBottomRetraction f,
      ⟨mappingCylinderBottomHomotopyRel f⟩⟩
  · exact ⟨mappingCylinderBottomHomeomorph f⟩

/-- Helper for Theorem 58.1: the chosen left-inverse homotopy, read along a cylinder
from the attaching end to the top. -/
private noncomputable def mappingCylinderTopCylinderMap (e : X ≃ₕ Y) : C(X × I, X) :=
  e.left_inv.some.toContinuousMap.comp ContinuousMap.prodSwap

/-- Helper for Theorem 58.1: the top cylinder map evaluates the chosen homotopy at the
cylinder height. -/
private lemma mappingCylinderTopCylinderMap_apply (e : X ≃ₕ Y) (p : X × I) :
    mappingCylinderTopCylinderMap e p = e.left_inv.some (p.2, p.1) := by
  -- Unpack composition with the product swap.
  rfl

/-- Helper for Theorem 58.1: the top projection agrees with the inverse map at the
attaching end. -/
private lemma mappingCylinderTopProjection_agrees (e : X ≃ₕ Y)
    (a : mappingCylinderBase X) :
    mappingCylinderTopCylinderMap e a = e.invFun (mappingCylinderAttachment e.toFun a) := by
  -- At cylinder height zero the chosen homotopy is `e.symm ∘ e`.
  have hStart := e.left_inv.some.apply_zero a.1.1
  rw [mappingCylinderTopCylinderMap_apply, mappingCylinderAttachment_apply, a.2]
  exact hStart

/-- Helper for Theorem 58.1: projection of a homotopy-equivalence mapping cylinder
onto its top copy. -/
private noncomputable def mappingCylinderTopProjection (e : X ≃ₕ Y) :
    C(MappingCylinder e.toFun, X) :=
  ⟨AdjunctionSpace.lift (mappingCylinderBase X) (mappingCylinderAttachment e.toFun)
      (mappingCylinderTopCylinderMap e) e.invFun
      (mappingCylinderTopProjection_agrees e),
    AdjunctionSpace.continuous_lift _ _ _ _ (mappingCylinderTopProjection_agrees e)⟩

/-- Helper for Theorem 58.1: evaluation of the bundled top inclusion is the canonical
adjunction-space inclusion. -/
private lemma mappingCylinderTop_apply (f : C(X, Y)) (x : X) :
    mappingCylinderTop f x = AdjunctionSpace.includeX (mappingCylinderBase X)
      (mappingCylinderAttachment f) (x, 1) := by
  -- Unpack only the local continuous-map wrapper.
  rfl

/-- Helper for Theorem 58.1: the top projection is a left inverse to the top inclusion. -/
private lemma mappingCylinderTopProjection_leftInverse (e : X ≃ₕ Y) :
    Function.LeftInverse (mappingCylinderTopProjection e) (mappingCylinderTop e.toFun) := by
  -- Compute the quotient lift on the top representative and then use the homotopy endpoint.
  intro x
  calc
    mappingCylinderTopProjection e (mappingCylinderTop e.toFun x) =
        mappingCylinderTopCylinderMap e (x, 1) :=
      AdjunctionSpace.lift_includeX _ _ _ _ _ (x, 1)
    _ = x := e.left_inv.some.apply_one x

/-- Helper for Theorem 58.1: the top inclusion of a homotopy-equivalence mapping cylinder
is a topological embedding. -/
private lemma mappingCylinderTop_isEmbedding (e : X ≃ₕ Y) :
    Topology.IsEmbedding (mappingCylinderTop e.toFun) := by
  -- The continuous top projection supplies a continuous left inverse.
  exact (mappingCylinderTopProjection_leftInverse e).isEmbedding
    (mappingCylinderTopProjection e).continuous (mappingCylinderTop e.toFun).continuous

/-- Helper for Theorem 58.1: `X` is homeomorphic to the top range of the mapping cylinder. -/
private noncomputable def mappingCylinderTopHomeomorph (e : X ≃ₕ Y) :
    X ≃ₜ mappingCylinderTopRange e.toFun :=
  (mappingCylinderTop_isEmbedding e).toHomeomorph

/-- Helper for Theorem 58.1: the ambient endpoint map obtained by projecting to `X`
and including the result at the top of the mapping cylinder. -/
private noncomputable def mappingCylinderTopAmbient (e : X ≃ₕ Y) :
    C(MappingCylinder e.toFun, MappingCylinder e.toFun) :=
  (mappingCylinderTop e.toFun).comp (mappingCylinderTopProjection e)

/-- Helper for Theorem 58.1: evaluation of the ambient top endpoint is top inclusion
after the chosen top projection. -/
private lemma mappingCylinderTopAmbient_apply (e : X ≃ₕ Y)
    (q : MappingCylinder e.toFun) :
    mappingCylinderTopAmbient e q =
      mappingCylinderTop e.toFun (mappingCylinderTopProjection e q) := by
  -- Unpack the local continuous-map composition.
  rfl

/-- Helper for Theorem 58.1: the canonical top endpoint lies in the top range. -/
private lemma mappingCylinderTop_mem_range (e : X ≃ₕ Y)
    (q : MappingCylinder e.toFun) :
    mappingCylinderTopAmbient e q ∈ mappingCylinderTopRange e.toFun := by
  -- The projected point itself supplies the range witness.
  exact ⟨mappingCylinderTopProjection e q, rfl⟩

/-- Helper for Theorem 58.1: the top endpoint bundled as a map into the top range. -/
private noncomputable def mappingCylinderTopRetractionMap (e : X ≃ₕ Y) :
    C(MappingCylinder e.toFun, mappingCylinderTopRange e.toFun) :=
  ⟨fun q ↦ ⟨mappingCylinderTopAmbient e q, mappingCylinderTop_mem_range e q⟩,
    (mappingCylinderTopAmbient e).continuous.subtype_mk _⟩

/-- Helper for Theorem 58.1: the top-range map is a left inverse to subtype inclusion. -/
private lemma mappingCylinderTopRetractionMap_leftInverse (e : X ≃ₕ Y) :
    Function.LeftInverse (mappingCylinderTopRetractionMap e) Subtype.val := by
  -- Replace a range point by a top representative and use the projection's left inverse.
  rintro ⟨q, x, rfl⟩
  apply Subtype.ext
  exact congrArg (mappingCylinderTop e.toFun)
    (mappingCylinderTopProjection_leftInverse e x)

/-- Helper for Theorem 58.1: the canonical retraction onto the top range. -/
private noncomputable def mappingCylinderTopRetraction (e : X ≃ₕ Y) :
    Set.Retraction (mappingCylinderTopRange e.toFun) :=
  Set.Retraction.ofContinuousMap (mappingCylinderTopRetractionMap e)
    (mappingCylinderTopRetractionMap_leftInverse e)

/-- Helper for Theorem 58.1: the ambient map of the top retraction is the explicit
top projection followed by top inclusion. -/
private lemma mappingCylinderTopRetraction_toAmbient (e : X ≃ₕ Y) :
    (mappingCylinderTopRetraction e).toAmbient = mappingCylinderTopAmbient e := by
  -- Both bundled maps have the same value at every mapping-cylinder point.
  ext q
  rfl

/-- Helper for Theorem 58.1: the ambient endpoint of the bottom deformation is bottom
inclusion after the mapping-cylinder projection. -/
private def mappingCylinderBottomAmbient (f : C(X, Y)) : C(MappingCylinder f, MappingCylinder f) :=
  (mappingCylinderBottom f).comp (mappingCylinderProjection f)

/-- Helper for Theorem 58.1: the stored bottom retraction has the explicit ambient endpoint. -/
private lemma mappingCylinderBottomRetraction_toAmbient (f : C(X, Y)) :
    (mappingCylinderBottomRetraction f).toAmbient = mappingCylinderBottomAmbient f := by
  -- Evaluate both maps; the subtype inclusion only forgets the range certificate.
  ext q
  rfl

/-- Helper for Theorem 58.1: the bottom shrink gives an ordinary homotopy to the
explicit bottom endpoint. -/
private lemma mappingCylinderBottomAmbient_homotopic (f : C(X, Y)) :
    (ContinuousMap.id (MappingCylinder f)).Homotopic (mappingCylinderBottomAmbient f) := by
  -- Forget relativity in the bottom deformation and identify its endpoint map.
  rw [← mappingCylinderBottomRetraction_toAmbient f]
  change Nonempty ((ContinuousMap.id (MappingCylinder f)).Homotopy
    (mappingCylinderBottomRetraction f).toAmbient)
  exact ⟨(mappingCylinderBottomHomotopyRel f).toHomotopy⟩

/-- Helper for Theorem 58.1: the bottom endpoint after reversing the chosen
right-inverse homotopy on `Y`. -/
private noncomputable def mappingCylinderRightCorrected (e : X ≃ₕ Y) :
    C(MappingCylinder e.toFun, MappingCylinder e.toFun) :=
  (mappingCylinderBottom e.toFun).comp
    (e.toFun.comp (e.invFun.comp (mappingCylinderProjection e.toFun)))

/-- Helper for Theorem 58.1: reversing the right-inverse homotopy moves the bottom
endpoint to the corrected bottom endpoint. -/
private lemma mappingCylinderBottom_to_rightCorrected (e : X ≃ₕ Y) :
    (mappingCylinderBottomAmbient e.toFun).Homotopic
      (mappingCylinderRightCorrected e) := by
  -- Postcompose the reversed right-inverse homotopy by the bottom inclusion and
  -- precompose it by the mapping-cylinder projection.
  have hPost := (ContinuousMap.Homotopic.refl (mappingCylinderBottom e.toFun)).comp
    e.right_inv.symm
  have hWhiskered := hPost.comp
    (ContinuousMap.Homotopic.refl (mappingCylinderProjection e.toFun))
  simpa only [mappingCylinderBottomAmbient, mappingCylinderRightCorrected,
    ContinuousMap.comp_id, ContinuousMap.comp_assoc] using hWhiskered

/-- Helper for Theorem 58.1: the endpoint just before the left-inverse correction is
the top copy of the inverse of the bottom projection. -/
private noncomputable def mappingCylinderPreTop (e : X ≃ₕ Y) :
    C(MappingCylinder e.toFun, MappingCylinder e.toFun) :=
  (mappingCylinderTop e.toFun).comp
    (e.invFun.comp (mappingCylinderProjection e.toFun))

/-- Helper for Theorem 58.1: evaluation of the pre-top endpoint applies the inverse
map to the bottom projection and then includes at the top. -/
private lemma mappingCylinderPreTop_apply (e : X ≃ₕ Y)
    (q : MappingCylinder e.toFun) :
    mappingCylinderPreTop e q = mappingCylinderTop e.toFun
      (e.invFun (mappingCylinderProjection e.toFun q)) := by
  -- Unpack the two local continuous-map compositions.
  rfl

/-- Helper for Theorem 58.1: the vertical cylinder motion is continuous. -/
private lemma continuous_mappingCylinderVerticalMap (e : X ≃ₕ Y) :
    Continuous (fun q : I × MappingCylinder e.toFun ↦
        AdjunctionSpace.includeX (mappingCylinderBase X)
        (mappingCylinderAttachment e.toFun)
        (e.invFun (mappingCylinderProjection e.toFun q.2), q.1)) := by
  -- The inverse of the bottom projection and the interval parameter form a continuous pair.
  apply (AdjunctionSpace.continuous_includeX _ _).comp
  exact (e.invFun.continuous.comp
    ((mappingCylinderProjection e.toFun).continuous.comp continuous_snd)).prodMk continuous_fst

/-- Helper for Theorem 58.1: vertical motion from the corrected bottom point to its
corresponding top point. -/
private noncomputable def mappingCylinderVerticalMap (e : X ≃ₕ Y) :
    C(I × MappingCylinder e.toFun, MappingCylinder e.toFun) :=
  ⟨fun q ↦ AdjunctionSpace.includeX (mappingCylinderBase X)
      (mappingCylinderAttachment e.toFun)
      (e.invFun (mappingCylinderProjection e.toFun q.2), q.1),
    continuous_mappingCylinderVerticalMap e⟩

/-- Helper for Theorem 58.1: vertical motion starts at the corrected bottom endpoint. -/
private lemma mappingCylinderVerticalMap_zero (e : X ≃ₕ Y)
    (q : MappingCylinder e.toFun) :
    mappingCylinderVerticalMap e (0, q) = mappingCylinderRightCorrected e q := by
  -- At height zero, the adjunction relation identifies the cylinder point with its image in `Y`.
  have hGlue := AdjunctionSpace.glue (mappingCylinderBase X)
    (mappingCylinderAttachment e.toFun)
    (⟨(e.invFun (mappingCylinderProjection e.toFun q), 0), rfl⟩ : mappingCylinderBase X)
  calc
    mappingCylinderVerticalMap e (0, q) =
        AdjunctionSpace.includeX (mappingCylinderBase X)
          (mappingCylinderAttachment e.toFun)
          (e.invFun (mappingCylinderProjection e.toFun q), 0) := rfl
    _ = AdjunctionSpace.includeY (mappingCylinderBase X)
        (mappingCylinderAttachment e.toFun)
        (e.toFun (e.invFun (mappingCylinderProjection e.toFun q))) := by
      simpa only [mappingCylinderAttachment_apply] using hGlue
    _ = mappingCylinderBottom e.toFun
        (e.toFun (e.invFun (mappingCylinderProjection e.toFun q))) := by
      exact (mappingCylinderBottom_apply e.toFun _).symm
    _ = mappingCylinderRightCorrected e q := rfl

/-- Helper for Theorem 58.1: vertical motion ends at the pre-top endpoint. -/
private lemma mappingCylinderVerticalMap_one (e : X ≃ₕ Y)
    (q : MappingCylinder e.toFun) :
    mappingCylinderVerticalMap e (1, q) = mappingCylinderPreTop e q := by
  -- At height one the cylinder representative is exactly the bundled top inclusion.
  rfl

/-- Helper for Theorem 58.1: the vertical cylinder motion as an ordinary homotopy. -/
private noncomputable def mappingCylinderVerticalHomotopy (e : X ≃ₕ Y) :
    ContinuousMap.Homotopy (mappingCylinderRightCorrected e) (mappingCylinderPreTop e) :=
  { toFun := mappingCylinderVerticalMap e
    map_zero_left := mappingCylinderVerticalMap_zero e
    map_one_left := mappingCylinderVerticalMap_one e }

/-- Helper for Theorem 58.1: the corrected bottom endpoint is homotopic to the pre-top endpoint. -/
private lemma mappingCylinderRightCorrected_to_preTop (e : X ≃ₕ Y) :
    (mappingCylinderRightCorrected e).Homotopic (mappingCylinderPreTop e) := by
  -- Package the explicit vertical motion.
  exact ⟨mappingCylinderVerticalHomotopy e⟩

/-- Helper for Theorem 58.1: the chosen top projection computes on a cylinder representative. -/
private lemma mappingCylinderTopProjection_includeX (e : X ≃ₕ Y) (p : X × I) :
    mappingCylinderTopProjection e
      (AdjunctionSpace.includeX (mappingCylinderBase X)
        (mappingCylinderAttachment e.toFun) p) =
      e.left_inv.some (p.2, p.1) := by
  -- First compute the quotient lift and then unfold the local cylinder-map wrapper.
  calc
    mappingCylinderTopProjection e
        (AdjunctionSpace.includeX (mappingCylinderBase X)
          (mappingCylinderAttachment e.toFun) p) =
        mappingCylinderTopCylinderMap e p :=
      AdjunctionSpace.lift_includeX _ _ _ _ _ p
    _ = e.left_inv.some (p.2, p.1) := mappingCylinderTopCylinderMap_apply e p

/-- Helper for Theorem 58.1: the chosen top projection computes as the inverse map on
a bottom representative. -/
private lemma mappingCylinderTopProjection_includeY (e : X ≃ₕ Y) (y : Y) :
    mappingCylinderTopProjection e (mappingCylinderBottom e.toFun y) = e.invFun y := by
  -- Compute the quotient lift on the bottom summand.
  exact AdjunctionSpace.lift_includeY _ _ _ _ _ y

/-- Helper for Theorem 58.1: the left-inverse correction path on a cylinder representative
is continuous. -/
private lemma continuous_mappingCylinderTopCorrectionPath (e : X ≃ₕ Y) (p : X × I) :
    Continuous (fun t : I ↦ mappingCylinderTop e.toFun
      (e.left_inv.some (t * p.2, p.1))) := by
  -- Follow the continuous scaled-time path in the chosen left-inverse homotopy by top inclusion.
  have hScaledTime : Continuous (fun t : I ↦ t * p.2) := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.mul continuous_const
  exact (mappingCylinderTop e.toFun).continuous.comp
    (e.left_inv.some.toContinuousMap.continuous.comp
      (hScaledTime.prodMk continuous_const))

/-- Helper for Theorem 58.1: the left-inverse correction path attached to a cylinder point. -/
private noncomputable def mappingCylinderTopCorrectionPath (e : X ≃ₕ Y) (p : X × I) :
    C(I, MappingCylinder e.toFun) :=
  ⟨fun t ↦ mappingCylinderTop e.toFun (e.left_inv.some (t * p.2, p.1)),
    continuous_mappingCylinderTopCorrectionPath e p⟩

/-- Helper for Theorem 58.1: evaluation of the left-inverse correction path has the
scaled cylinder height as homotopy time. -/
private lemma mappingCylinderTopCorrectionPath_apply (e : X ≃ₕ Y)
    (p : X × I) (t : I) :
    mappingCylinderTopCorrectionPath e p t =
      mappingCylinderTop e.toFun (e.left_inv.some (t * p.2, p.1)) := by
  -- Unpack only the local continuous-map wrapper.
  rfl

/-- Helper for Theorem 58.1: at the attaching end, the correction path is the constant
top path determined by the inverse map. -/
private lemma mappingCylinderTopCorrectionPath_agrees (e : X ≃ₕ Y)
    (a : mappingCylinderBase X) :
    mappingCylinderTopCorrectionPath e a =
      ContinuousMap.const I (mappingCylinderTop e.toFun
        (e.invFun (mappingCylinderAttachment e.toFun a))) := by
  -- The scaled time is zero at the attaching end, where the left-inverse homotopy
  -- starts at `g ∘ f`.
  ext t
  rw [mappingCylinderTopCorrectionPath_apply]
  have hTime : t * a.1.2 = 0 := by
    rw [a.2, mul_zero]
  rw [hTime, e.left_inv.some.apply_zero, mappingCylinderAttachment_apply]
  rfl

/-- Helper for Theorem 58.1: the correction paths vary continuously with the cylinder point. -/
private lemma continuous_mappingCylinderTopCorrectionPathFamily (e : X ≃ₕ Y) :
    Continuous (fun p : X × I ↦ mappingCylinderTopCorrectionPath e p) := by
  -- Uncurry the family; multiplication supplies the scaled homotopy time continuously.
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hScaledTime : Continuous
      (fun q : (X × I) × I ↦ q.2 * q.1.2) := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
  exact (mappingCylinderTop e.toFun).continuous.comp
    (e.left_inv.some.toContinuousMap.continuous.comp
      (hScaledTime.prodMk (continuous_fst.comp continuous_fst)))

/-- Helper for Theorem 58.1: the continuous family of left-inverse correction paths. -/
private noncomputable def mappingCylinderTopCorrectionPathFamily (e : X ≃ₕ Y) :
    C(X × I, C(I, MappingCylinder e.toFun)) :=
  ⟨fun p ↦ mappingCylinderTopCorrectionPath e p,
    continuous_mappingCylinderTopCorrectionPathFamily e⟩

/-- Helper for Theorem 58.1: bottom representatives receive constant top paths under
the left-inverse correction. -/
private noncomputable def mappingCylinderTopConstantPathFamily (e : X ≃ₕ Y) :
    C(Y, C(I, MappingCylinder e.toFun)) :=
  ContinuousMap.const'.comp ((mappingCylinderTop e.toFun).comp e.invFun)

/-- Helper for Theorem 58.1: the adjoint correction map is continuous on the quotient. -/
private lemma continuous_mappingCylinderTopCorrectionAdjoint (e : X ≃ₕ Y) :
    Continuous (AdjunctionSpace.lift (mappingCylinderBase X)
      (mappingCylinderAttachment e.toFun)
      (mappingCylinderTopCorrectionPathFamily e)
      (mappingCylinderTopConstantPathFamily e)
      (mappingCylinderTopCorrectionPath_agrees e)) := by
  -- Descend the two compatible continuous path families through the adjunction quotient.
  exact AdjunctionSpace.continuous_lift _ _ _ _
    (mappingCylinderTopCorrectionPath_agrees e)

/-- Helper for Theorem 58.1: the curried left-inverse correction on the mapping cylinder. -/
private noncomputable def mappingCylinderTopCorrectionAdjoint (e : X ≃ₕ Y) :
    C(MappingCylinder e.toFun, C(I, MappingCylinder e.toFun)) :=
  ⟨AdjunctionSpace.lift (mappingCylinderBase X)
      (mappingCylinderAttachment e.toFun)
      (mappingCylinderTopCorrectionPathFamily e)
      (mappingCylinderTopConstantPathFamily e)
      (mappingCylinderTopCorrectionPath_agrees e),
    continuous_mappingCylinderTopCorrectionAdjoint e⟩

/-- Helper for Theorem 58.1: the uncurried left-inverse correction map. -/
private noncomputable def mappingCylinderTopCorrectionMap (e : X ≃ₕ Y) :
    C(I × MappingCylinder e.toFun, MappingCylinder e.toFun) :=
  (mappingCylinderTopCorrectionAdjoint e).uncurry.comp ContinuousMap.prodSwap

/-- Helper for Theorem 58.1: the correction map computes by the scaled path on a
cylinder representative. -/
private lemma mappingCylinderTopCorrectionMap_includeX (e : X ≃ₕ Y)
    (t : I) (p : X × I) :
    mappingCylinderTopCorrectionMap e
      (t, AdjunctionSpace.includeX (mappingCylinderBase X)
        (mappingCylinderAttachment e.toFun) p) =
      mappingCylinderTopCorrectionPath e p t := by
  -- Evaluate the quotient lift before evaluating the resulting path at `t`.
  have hPath := AdjunctionSpace.lift_includeX (mappingCylinderBase X)
    (mappingCylinderAttachment e.toFun)
    (mappingCylinderTopCorrectionPathFamily e)
    (mappingCylinderTopConstantPathFamily e)
    (mappingCylinderTopCorrectionPath_agrees e) p
  exact congrArg (fun k : C(I, MappingCylinder e.toFun) ↦ k t) hPath

/-- Helper for Theorem 58.1: the correction map is constant on a bottom representative. -/
private lemma mappingCylinderTopCorrectionMap_includeY (e : X ≃ₕ Y)
    (t : I) (y : Y) :
    mappingCylinderTopCorrectionMap e (t, mappingCylinderBottom e.toFun y) =
      mappingCylinderTop e.toFun (e.invFun y) := by
  -- The quotient lift assigns the chosen constant path to the bottom summand.
  have hPath := AdjunctionSpace.lift_includeY (mappingCylinderBase X)
    (mappingCylinderAttachment e.toFun)
    (mappingCylinderTopCorrectionPathFamily e)
    (mappingCylinderTopConstantPathFamily e)
    (mappingCylinderTopCorrectionPath_agrees e) y
  exact congrArg (fun k : C(I, MappingCylinder e.toFun) ↦ k t) hPath

/-- Helper for Theorem 58.1: the left-inverse correction begins at the pre-top endpoint. -/
private lemma mappingCylinderTopCorrectionMap_zero (e : X ≃ₕ Y)
    (q : MappingCylinder e.toFun) :
    mappingCylinderTopCorrectionMap e (0, q) = mappingCylinderPreTop e q := by
  -- Check the endpoint on the two canonical quotient families.
  rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
    (mappingCylinderBase X) (mappingCylinderAttachment e.toFun) q with ⟨p, rfl⟩ | ⟨y, rfl⟩
  · rw [mappingCylinderTopCorrectionMap_includeX,
      mappingCylinderTopCorrectionPath_apply, zero_mul,
      e.left_inv.some.apply_zero, mappingCylinderPreTop_apply,
      mappingCylinderProjection_includeX, ContinuousMap.comp_apply]
  · rw [← mappingCylinderBottom_apply e.toFun y,
      mappingCylinderTopCorrectionMap_includeY,
      mappingCylinderPreTop_apply, mappingCylinderProjection_leftInverse]

/-- Helper for Theorem 58.1: the left-inverse correction ends at the ambient top retraction. -/
private lemma mappingCylinderTopCorrectionMap_one (e : X ≃ₕ Y)
    (q : MappingCylinder e.toFun) :
    mappingCylinderTopCorrectionMap e (1, q) = mappingCylinderTopAmbient e q := by
  -- On a cylinder point the chosen homotopy reaches its height parameter; on a bottom
  -- point both sides are the same constant top point.
  rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
    (mappingCylinderBase X) (mappingCylinderAttachment e.toFun) q with ⟨p, rfl⟩ | ⟨y, rfl⟩
  · rw [mappingCylinderTopCorrectionMap_includeX,
      mappingCylinderTopCorrectionPath_apply, one_mul,
      mappingCylinderTopAmbient_apply, mappingCylinderTopProjection_includeX]
  · rw [← mappingCylinderBottom_apply e.toFun y,
      mappingCylinderTopCorrectionMap_includeY,
      mappingCylinderTopAmbient_apply, mappingCylinderTopProjection_includeY]

/-- Helper for Theorem 58.1: the scaled left-inverse correction as an ordinary homotopy. -/
private noncomputable def mappingCylinderTopCorrectionHomotopy (e : X ≃ₕ Y) :
    ContinuousMap.Homotopy (mappingCylinderPreTop e) (mappingCylinderTopAmbient e) :=
  { toFun := mappingCylinderTopCorrectionMap e
    map_zero_left := mappingCylinderTopCorrectionMap_zero e
    map_one_left := mappingCylinderTopCorrectionMap_one e }

/-- Helper for Theorem 58.1: the pre-top endpoint is homotopic to the ambient top retraction. -/
private lemma mappingCylinderPreTop_to_topAmbient (e : X ≃ₕ Y) :
    (mappingCylinderPreTop e).Homotopic (mappingCylinderTopAmbient e) := by
  -- Package the quotient-descended correction homotopy.
  exact ⟨mappingCylinderTopCorrectionHomotopy e⟩

/-- Helper for Theorem 58.1: the mapping cylinder of a homotopy equivalence has an
ordinary retraction homotopy onto its top range. -/
private lemma mappingCylinderTopOrdinaryDeformation (e : X ≃ₕ Y) :
    ∃ r : Set.Retraction (mappingCylinderTopRange e.toFun),
      (ContinuousMap.id (MappingCylinder e.toFun)).Homotopic r.toAmbient := by
  -- Concatenate bottom shrink, reversed right-inverse correction, vertical motion,
  -- and the scaled left-inverse correction, then identify the canonical retraction.
  refine ⟨mappingCylinderTopRetraction e, ?_⟩
  rw [mappingCylinderTopRetraction_toAmbient]
  exact (mappingCylinderBottomAmbient_homotopic e.toFun).trans <|
    (mappingCylinderBottom_to_rightCorrected e).trans <|
      (mappingCylinderRightCorrected_to_preTop e).trans
        (mappingCylinderPreTop_to_topAmbient e)

/-- Helper for Theorem 58.1: the cylinder height agrees with zero on the attaching end. -/
private lemma mappingCylinderHeight_agrees (f : C(X, Y)) (a : mappingCylinderBase X) :
    a.1.2 = (ContinuousMap.const Y 0) (mappingCylinderAttachment f a) := by
  -- The defining property of the attaching subtype is precisely that its height is zero.
  exact a.2

/-- Helper for Theorem 58.1: the continuous height coordinate on a mapping cylinder. -/
private def mappingCylinderHeight (f : C(X, Y)) : C(MappingCylinder f, I) :=
  ⟨AdjunctionSpace.lift (mappingCylinderBase X) (mappingCylinderAttachment f)
      (ContinuousMap.snd : C(X × I, I)) (ContinuousMap.const Y 0)
      (mappingCylinderHeight_agrees f),
    AdjunctionSpace.continuous_lift _ _ _ _ (mappingCylinderHeight_agrees f)⟩

/-- Helper for Theorem 58.1: the height coordinate computes on a cylinder representative. -/
private lemma mappingCylinderHeight_includeX (f : C(X, Y)) (p : X × I) :
    mappingCylinderHeight f
      (AdjunctionSpace.includeX (mappingCylinderBase X) (mappingCylinderAttachment f) p) =
      p.2 := by
  -- Apply the left-summand computation rule for the quotient lift.
  exact AdjunctionSpace.lift_includeX _ _ _ _ _ p

/-- Helper for Theorem 58.1: every bottom representative has height zero. -/
private lemma mappingCylinderHeight_includeY (f : C(X, Y)) (y : Y) :
    mappingCylinderHeight f (mappingCylinderBottom f y) = 0 := by
  -- Apply the right-summand computation rule for the quotient lift.
  exact AdjunctionSpace.lift_includeY _ _ _ _ _ y

/-- Helper for Theorem 58.1: the top range is exactly the height-one level set. -/
private lemma mappingCylinderTopRange_eq_height_preimage (f : C(X, Y)) :
    mappingCylinderTopRange f = mappingCylinderHeight f ⁻¹' ({1} : Set I) := by
  -- Compare membership on top representatives, then exhaust the quotient in the converse direction.
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change mappingCylinderHeight f (mappingCylinderTop f x) = 1
    rw [mappingCylinderTop_apply, mappingCylinderHeight_includeX]
  · intro hq
    have hHeight : mappingCylinderHeight f q = 1 := hq
    rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
      (mappingCylinderBase X) (mappingCylinderAttachment f) q with ⟨p, rfl⟩ | ⟨y, rfl⟩
    · rw [mappingCylinderHeight_includeX] at hHeight
      refine ⟨p.1, ?_⟩
      rw [mappingCylinderTop_apply]
      exact congrArg (AdjunctionSpace.includeX (mappingCylinderBase X)
        (mappingCylinderAttachment f)) (Prod.ext rfl hHeight.symm)
    · rw [← mappingCylinderBottom_apply f y,
        mappingCylinderHeight_includeY] at hHeight
      norm_num at hHeight

/-- Helper for Theorem 58.1: the top range of every mapping cylinder is closed. -/
private lemma mappingCylinderTopRange_isClosed (f : C(X, Y)) :
    IsClosed (mappingCylinderTopRange f) := by
  -- Express the range as the inverse image of the closed singleton `{1}` under height.
  rw [mappingCylinderTopRange_eq_height_preimage]
  exact isClosed_singleton.preimage (mappingCylinderHeight f).continuous

/-- Helper for Theorem 58.1: the clipped cylinder height used by the homotopy-extension
retraction. -/
private noncomputable def mappingCylinderExtensionHeight (s u : I) : I :=
  Set.projIcc 0 1 (zero_le_one' ℝ) ((s : ℝ) * (1 + (u : ℝ)))

/-- Helper for Theorem 58.1: the clipped outer coordinate used by the
homotopy-extension retraction. -/
private noncomputable def mappingCylinderExtensionOuter (s u : I) : I :=
  Set.projIcc 0 1 (zero_le_one' ℝ) ((s : ℝ) * (1 + (u : ℝ)) - 1)

/-- Helper for Theorem 58.1: the clipped cylinder height varies continuously. -/
private lemma continuous_mappingCylinderExtensionHeight :
    Continuous (fun q : I × I ↦ mappingCylinderExtensionHeight q.1 q.2) := by
  -- Project the continuous real-valued product back to the unit interval.
  exact continuous_projIcc.comp
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.add (continuous_subtype_val.comp continuous_snd)))

/-- Helper for Theorem 58.1: the clipped outer coordinate varies continuously. -/
private lemma continuous_mappingCylinderExtensionOuter :
    Continuous (fun q : I × I ↦ mappingCylinderExtensionOuter q.1 q.2) := by
  -- Subtracting one before projecting preserves continuity.
  exact continuous_projIcc.comp
    (((continuous_subtype_val.comp continuous_fst).mul
      (continuous_const.add (continuous_subtype_val.comp continuous_snd))).sub continuous_const)

/-- Helper for Theorem 58.1: zero cylinder height remains zero after clipping. -/
private lemma mappingCylinderExtensionHeight_zero (u : I) :
    mappingCylinderExtensionHeight 0 u = 0 := by
  -- The unclipped product is zero.
  norm_num [mappingCylinderExtensionHeight, Set.projIcc_of_le_left]

/-- Helper for Theorem 58.1: zero cylinder height forces zero outer coordinate. -/
private lemma mappingCylinderExtensionOuter_zero (u : I) :
    mappingCylinderExtensionOuter 0 u = 0 := by
  -- The unclipped outer coordinate is `-1`.
  norm_num [mappingCylinderExtensionOuter, Set.projIcc_of_le_left]

/-- Helper for Theorem 58.1: on the zero outer face the clipped height is unchanged. -/
private lemma mappingCylinderExtensionHeight_outer_zero (s : I) :
    mappingCylinderExtensionHeight s 0 = s := by
  -- The unclipped height is already in the unit interval.
  simp [mappingCylinderExtensionHeight]

/-- Helper for Theorem 58.1: the zero outer face remains at outer coordinate zero. -/
private lemma mappingCylinderExtensionOuter_outer_zero (s : I) :
    mappingCylinderExtensionOuter s 0 = 0 := by
  -- Since `s ≤ 1`, the unclipped outer coordinate `s - 1` is nonpositive.
  apply Set.projIcc_of_le_left
  simpa using sub_nonpos.mpr s.2.2

/-- Helper for Theorem 58.1: top cylinder height remains one after clipping. -/
private lemma mappingCylinderExtensionHeight_one (u : I) :
    mappingCylinderExtensionHeight 1 u = 1 := by
  -- The unclipped height `1 + u` is at least one.
  apply Set.projIcc_of_right_le
  simpa using u.2.1

/-- Helper for Theorem 58.1: at top cylinder height the clipped outer coordinate is unchanged. -/
private lemma mappingCylinderExtensionOuter_one (u : I) :
    mappingCylinderExtensionOuter 1 u = u := by
  -- The unclipped outer coordinate simplifies to `u`, already in the unit interval.
  simp [mappingCylinderExtensionOuter]

/-- Helper for Theorem 58.1: the two clipped coordinates always land on the zero outer
face or the top cylinder face. -/
private lemma mappingCylinderExtensionOuter_eq_zero_or_height_eq_one (s u : I) :
    mappingCylinderExtensionOuter s u = 0 ∨ mappingCylinderExtensionHeight s u = 1 := by
  -- Split according to whether the unclipped product has crossed height one.
  by_cases hCrossed : 1 ≤ (s : ℝ) * (1 + (u : ℝ))
  · apply Or.inr
    unfold mappingCylinderExtensionHeight
    apply Set.projIcc_of_right_le
    exact hCrossed
  · apply Or.inl
    unfold mappingCylinderExtensionOuter
    apply Set.projIcc_of_le_left
    linarith

/-- Helper for Theorem 58.1: the cylinder-representative formula for the
homotopy-extension retraction. -/
private noncomputable def mappingCylinderExtensionCylinder (f : C(X, Y))
    (q : (X × I) × (I × I)) : (MappingCylinder f × I) × I :=
  ((AdjunctionSpace.includeX (mappingCylinderBase X) (mappingCylinderAttachment f)
      (q.1.1, mappingCylinderExtensionHeight q.1.2 q.2.2), q.2.1),
    mappingCylinderExtensionOuter q.1.2 q.2.2)

/-- Helper for Theorem 58.1: the bottom-representative formula for the
homotopy-extension retraction. -/
private def mappingCylinderExtensionBottom (f : C(X, Y))
    (q : Y × (I × I)) : (MappingCylinder f × I) × I :=
  ((mappingCylinderBottom f q.1, q.2.1), 0)

/-- Helper for Theorem 58.1: the cylinder-representative extension formula is continuous. -/
private lemma continuous_mappingCylinderExtensionCylinder (f : C(X, Y)) :
    Continuous (mappingCylinderExtensionCylinder f) := by
  -- Assemble the modified cylinder point, unchanged inner parameter, and clipped outer parameter.
  have hHeight : Continuous (fun q : (X × I) × (I × I) ↦
      mappingCylinderExtensionHeight q.1.2 q.2.2) :=
    continuous_mappingCylinderExtensionHeight.comp
      ((continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))
  have hOuter : Continuous (fun q : (X × I) × (I × I) ↦
      mappingCylinderExtensionOuter q.1.2 q.2.2) :=
    continuous_mappingCylinderExtensionOuter.comp
      ((continuous_snd.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))
  have hCylinder : Continuous (fun q : (X × I) × (I × I) ↦
      AdjunctionSpace.includeX (mappingCylinderBase X) (mappingCylinderAttachment f)
        (q.1.1, mappingCylinderExtensionHeight q.1.2 q.2.2)) :=
    (AdjunctionSpace.continuous_includeX _ _).comp
      ((continuous_fst.comp continuous_fst).prodMk hHeight)
  exact (hCylinder.prodMk (continuous_fst.comp continuous_snd)).prodMk hOuter

/-- Helper for Theorem 58.1: the bottom-representative extension formula is continuous. -/
private lemma continuous_mappingCylinderExtensionBottom (f : C(X, Y)) :
    Continuous (mappingCylinderExtensionBottom f) := by
  -- Keep the bottom point and inner parameter fixed while setting the outer parameter to zero.
  exact (((mappingCylinderBottom f).continuous.comp continuous_fst).prodMk
    (continuous_fst.comp continuous_snd)).prodMk continuous_const

/-- Helper for Theorem 58.1: the cylinder and bottom extension formulas agree on the
attaching subset. -/
private lemma mappingCylinderExtension_agrees (f : C(X, Y))
    (a : mappingCylinderBase X) (w : I × I) :
    mappingCylinderExtensionCylinder f (a.1, w) =
      mappingCylinderExtensionBottom f (mappingCylinderAttachment f a, w) := by
  -- At attaching height zero both clipped coordinates are zero, and the quotient glues
  -- the cylinder representative to its bottom image.
  have hHeight : mappingCylinderExtensionHeight a.1.2 w.2 = 0 := by
    rw [a.2]
    exact mappingCylinderExtensionHeight_zero w.2
  have hOuter : mappingCylinderExtensionOuter a.1.2 w.2 = 0 := by
    rw [a.2]
    exact mappingCylinderExtensionOuter_zero w.2
  apply Prod.ext
  · apply Prod.ext
    · calc
        AdjunctionSpace.includeX (mappingCylinderBase X) (mappingCylinderAttachment f)
            (a.1.1, mappingCylinderExtensionHeight a.1.2 w.2) =
            AdjunctionSpace.includeX (mappingCylinderBase X)
              (mappingCylinderAttachment f) a := by
          exact congrArg (AdjunctionSpace.includeX (mappingCylinderBase X)
            (mappingCylinderAttachment f))
            (Prod.ext rfl (hHeight.trans a.2.symm))
        _ = mappingCylinderBottom f (mappingCylinderAttachment f a) :=
          AdjunctionSpace.glue _ _ a
    · rfl
  · exact hOuter

/-- Helper for Theorem 58.1: the extension formula on coproduct representatives. -/
private noncomputable def mappingCylinderExtensionRepresentative (f : C(X, Y))
    (q : ((X × I) ⊕ Y) × (I × I)) : (MappingCylinder f × I) × I :=
  Sum.elim (fun p ↦ mappingCylinderExtensionCylinder f (p, q.2))
    (fun y ↦ mappingCylinderExtensionBottom f (y, q.2)) q.1

/-- Helper for Theorem 58.1: the representative-level extension formula is continuous. -/
private lemma continuous_mappingCylinderExtensionRepresentative (f : C(X, Y)) :
    Continuous (mappingCylinderExtensionRepresentative f) := by
  -- Distribute the parameter product over the coproduct and check the two summands.
  rw [← Homeomorph.comp_continuous_iff'
      (Homeomorph.sumProdDistrib (X := X × I) (Y := Y) (Z := I × I)).symm,
    continuous_sum_dom]
  constructor
  · simpa [mappingCylinderExtensionRepresentative, Function.comp_def] using
      continuous_mappingCylinderExtensionCylinder f
  · simpa [mappingCylinderExtensionRepresentative, Function.comp_def] using
      continuous_mappingCylinderExtensionBottom f

/-- Helper for Theorem 58.1: the extension formula descended to a mapping-cylinder point
with two interval parameters. -/
private noncomputable def mappingCylinderExtensionCore (f : C(X, Y))
    (q : MappingCylinder f × (I × I)) : (MappingCylinder f × I) × I :=
  AdjunctionSpace.lift (mappingCylinderBase X) (mappingCylinderAttachment f)
    (fun p ↦ mappingCylinderExtensionCylinder f (p, q.2))
    (fun y ↦ mappingCylinderExtensionBottom f (y, q.2))
    (fun a ↦ mappingCylinderExtension_agrees f a q.2) q.1

/-- Helper for Theorem 58.1: the descended extension core computes on quotient representatives. -/
private lemma mappingCylinderExtensionCore_quotientMap (f : C(X, Y))
    (r : (X × I) ⊕ Y) (w : I × I) :
    mappingCylinderExtensionCore f
      (AdjunctionSpace.quotientMap (mappingCylinderBase X)
        (mappingCylinderAttachment f) r, w) =
      mappingCylinderExtensionRepresentative f (r, w) := by
  -- Use the public computation rule for a quotient lift.
  exact AdjunctionSpace.lift_quotientMap _ _ _ _ _ r

/-- Helper for Theorem 58.1: the extension core is jointly continuous in the mapping-cylinder
point and both interval parameters. -/
private lemma continuous_mappingCylinderExtensionCore (f : C(X, Y)) :
    Continuous (mappingCylinderExtensionCore f) := by
  -- Test joint continuity after the quotient map in the first coordinate.
  apply (AdjunctionSpace.quotientMap_isQuotientMap
    (mappingCylinderBase X) (mappingCylinderAttachment f)).continuous_lift_prod_left
  have hComposition :
      (fun q : ((X × I) ⊕ Y) × (I × I) ↦
        mappingCylinderExtensionCore f
          (AdjunctionSpace.quotientMap (mappingCylinderBase X)
            (mappingCylinderAttachment f) q.1, q.2)) =
        mappingCylinderExtensionRepresentative f := by
    funext q
    exact mappingCylinderExtensionCore_quotientMap f q.1 q.2
  rw [hComposition]
  exact continuous_mappingCylinderExtensionRepresentative f

/-- Helper for Theorem 58.1: the extension core computes by the cylinder formula on a
cylinder representative. -/
private lemma mappingCylinderExtensionCore_includeX (f : C(X, Y))
    (p : X × I) (w : I × I) :
    mappingCylinderExtensionCore f
      (AdjunctionSpace.includeX (mappingCylinderBase X) (mappingCylinderAttachment f) p, w) =
      mappingCylinderExtensionCylinder f (p, w) := by
  -- Apply the left-summand computation rule for the quotient lift.
  exact AdjunctionSpace.lift_includeX _ _ _ _ _ p

/-- Helper for Theorem 58.1: the extension core computes by the bottom formula on a
bottom representative. -/
private lemma mappingCylinderExtensionCore_includeY (f : C(X, Y))
    (y : Y) (w : I × I) :
    mappingCylinderExtensionCore f (mappingCylinderBottom f y, w) =
      mappingCylinderExtensionBottom f (y, w) := by
  -- Apply the right-summand computation rule for the quotient lift.
  exact AdjunctionSpace.lift_includeY _ _ _ _ _ y

/-- Helper for Theorem 58.1: the union of the zero outer face and the top-range face
used in homotopy extension. -/
private def mappingCylinderExtensionSet (f : C(X, Y)) :
    Set ((MappingCylinder f × I) × I) :=
  {q | q.2 = 0 ∨ q.1.1 ∈ mappingCylinderTopRange f}

/-- Helper for Theorem 58.1: the descended extension core in the original product order. -/
private noncomputable def mappingCylinderExtensionMap (f : C(X, Y)) :
    C((MappingCylinder f × I) × I, (MappingCylinder f × I) × I) :=
  ⟨fun q ↦ mappingCylinderExtensionCore f (q.1.1, (q.1.2, q.2)),
    (continuous_mappingCylinderExtensionCore f).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))⟩

/-- Helper for Theorem 58.1: the reordered extension map computes on a cylinder representative. -/
private lemma mappingCylinderExtensionMap_includeX (f : C(X, Y))
    (p : X × I) (t u : I) :
    mappingCylinderExtensionMap f
      ((AdjunctionSpace.includeX (mappingCylinderBase X) (mappingCylinderAttachment f) p, t), u) =
      mappingCylinderExtensionCylinder f (p, (t, u)) := by
  -- Reduce to the corresponding computation rule for the descended core.
  exact mappingCylinderExtensionCore_includeX f p (t, u)

/-- Helper for Theorem 58.1: the reordered extension map computes on a bottom representative. -/
private lemma mappingCylinderExtensionMap_includeY (f : C(X, Y))
    (y : Y) (t u : I) :
    mappingCylinderExtensionMap f ((mappingCylinderBottom f y, t), u) =
      mappingCylinderExtensionBottom f (y, (t, u)) := by
  -- Reduce to the corresponding computation rule for the descended core.
  exact mappingCylinderExtensionCore_includeY f y (t, u)

/-- Helper for Theorem 58.1: the extension map lands in the zero-or-top face union. -/
private lemma mappingCylinderExtensionMap_mem (f : C(X, Y))
    (q : (MappingCylinder f × I) × I) :
    mappingCylinderExtensionMap f q ∈ mappingCylinderExtensionSet f := by
  -- Exhaust the mapping-cylinder coordinate; the clipping dichotomy handles cylinder points,
  -- while bottom points are sent directly to outer coordinate zero.
  rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
    (mappingCylinderBase X) (mappingCylinderAttachment f) q.1.1 with ⟨p, hp⟩ | ⟨y, hy⟩
  · rcases q with ⟨⟨m, t⟩, u⟩
    change m = AdjunctionSpace.includeX (mappingCylinderBase X)
      (mappingCylinderAttachment f) p at hp
    subst m
    rw [mappingCylinderExtensionMap_includeX]
    rcases mappingCylinderExtensionOuter_eq_zero_or_height_eq_one p.2 u with
      hOuter | hHeight
    · exact Or.inl hOuter
    · apply Or.inr
      refine ⟨p.1, ?_⟩
      rw [mappingCylinderTop_apply]
      exact congrArg (AdjunctionSpace.includeX (mappingCylinderBase X)
        (mappingCylinderAttachment f)) (Prod.ext rfl hHeight.symm)
  · rcases q with ⟨⟨m, t⟩, u⟩
    change m = AdjunctionSpace.includeY (mappingCylinderBase X)
      (mappingCylinderAttachment f) y at hy
    subst m
    rw [← mappingCylinderBottom_apply f y, mappingCylinderExtensionMap_includeY]
    exact Or.inl rfl

/-- Helper for Theorem 58.1: the extension map fixes the zero outer face and the top-range face. -/
private lemma mappingCylinderExtensionMap_fixed (f : C(X, Y))
    (q : (MappingCylinder f × I) × I) (hq : q ∈ mappingCylinderExtensionSet f) :
    mappingCylinderExtensionMap f q = q := by
  -- On the zero face use the `u = 0` clipping equations; on the top face use the
  -- `s = 1` clipping equations.
  rcases q with ⟨⟨m, t⟩, u⟩
  rcases hq with hu | hm
  · change u = 0 at hu
    subst u
    rcases AdjunctionSpace.exists_eq_includeX_or_eq_includeY
      (mappingCylinderBase X) (mappingCylinderAttachment f) m with ⟨p, rfl⟩ | ⟨y, rfl⟩
    · rw [mappingCylinderExtensionMap_includeX]
      unfold mappingCylinderExtensionCylinder
      rw [
        mappingCylinderExtensionHeight_outer_zero,
        mappingCylinderExtensionOuter_outer_zero]
    · rw [← mappingCylinderBottom_apply f y,
        mappingCylinderExtensionMap_includeY]
      rfl
  · obtain ⟨x, rfl⟩ := hm
    rw [mappingCylinderTop_apply, mappingCylinderExtensionMap_includeX]
    unfold mappingCylinderExtensionCylinder
    rw [
      mappingCylinderExtensionHeight_one, mappingCylinderExtensionOuter_one]

/-- Helper for Theorem 58.1: the extension map bundled into the zero-or-top face union. -/
private noncomputable def mappingCylinderExtensionRetractionMap (f : C(X, Y)) :
    C((MappingCylinder f × I) × I, mappingCylinderExtensionSet f) :=
  ⟨fun q ↦ ⟨mappingCylinderExtensionMap f q, mappingCylinderExtensionMap_mem f q⟩,
    (mappingCylinderExtensionMap f).continuous.subtype_mk _⟩

/-- Helper for Theorem 58.1: the bundled extension map is a left inverse to subtype inclusion. -/
private lemma mappingCylinderExtensionRetractionMap_leftInverse (f : C(X, Y)) :
    Function.LeftInverse (mappingCylinderExtensionRetractionMap f) Subtype.val := by
  -- The unbundled extension map fixes every point of the target union.
  intro q
  apply Subtype.ext
  exact mappingCylinderExtensionMap_fixed f q.1 q.2

/-- Helper for Theorem 58.1: the canonical retraction onto the zero-or-top face union. -/
private noncomputable def mappingCylinderExtensionRetraction (f : C(X, Y)) :
    Set.Retraction (mappingCylinderExtensionSet f) :=
  Set.Retraction.ofContinuousMap (mappingCylinderExtensionRetractionMap f)
    (mappingCylinderExtensionRetractionMap_leftInverse f)

/-- Helper for Theorem 58.1: the mapping-cylinder top range is closed and its
zero-or-top face union is a retract. -/
private lemma mappingCylinderTopHomotopyExtensionData (f : C(X, Y)) :
    IsClosed (mappingCylinderTopRange f) ∧ Set.IsRetract (mappingCylinderExtensionSet f) := by
  -- Package the height-level-set proof and the explicit clipped-coordinate retraction.
  constructor
  · exact mappingCylinderTopRange_isClosed f
  · apply (Set.isRetract_iff _).2
    exact ⟨(mappingCylinderExtensionRetraction f).toContinuousMap,
      (mappingCylinderExtensionRetraction f).leftInverse⟩

/-- Helper for Theorem 58.1: an ordinary retraction homotopy can be corrected to a
deformation retraction when the zero-or-subspace cylinder union is a retract. -/
private lemma isDeformationRetract_of_retraction_homotopy_extension
    {Z : Type*} [TopologicalSpace Z] (A : Set Z) (hA : IsClosed A)
    (r : Set.Retraction A)
    (hH : (ContinuousMap.id Z).Homotopic r.toAmbient)
    (hExtension : Set.IsRetract {q : (Z × I) × I | q.2 = 0 ∨ q.1.1 ∈ A}) :
    Set.IsDeformationRetract A := by
  -- Route correction: replace the monolithic four-edge boundary by a canonical
  -- two-segment backtrack, extend its tent contraction, and read off three square edges.
  obtain ⟨H⟩ := hH
  obtain ⟨K, N, hAgree⟩ := HomotopyExtension.existsRetractionBacktrack r H
  obtain ⟨F, hFzero, hFA⟩ :=
    HomotopyExtension.existsExtensionOfRestrictionContraction
      A hA K N hAgree hExtension
  obtain ⟨Hrel⟩ :=
    HomotopyExtension.homotopyRel_of_extensionSquare
      A K N hAgree F hFzero hFA
  -- Package the corrected relative homotopy with the original endpoint retraction.
  apply (Set.isDeformationRetract_iff A).2
  exact ⟨r, ⟨Hrel⟩⟩

/-- Helper for Theorem 58.1: the top copy in the mapping cylinder of a homotopy
equivalence is a deformation retract. -/
private lemma mappingCylinderTop_isDeformationRetract (e : X ≃ₕ Y) :
    Set.IsDeformationRetract (mappingCylinderTopRange e.toFun) := by
  -- Route correction: the ordinary four-stage homotopy is now isolated above; what remains
  -- is delegated to the generic Fuchs correction using the verified extension retraction.
  obtain ⟨r, hOrdinary⟩ := mappingCylinderTopOrdinaryDeformation e
  obtain ⟨hClosed, hExtension⟩ := mappingCylinderTopHomotopyExtensionData e.toFun
  apply isDeformationRetract_of_retraction_homotopy_extension
    (mappingCylinderTopRange e.toFun) hClosed r hOrdinary
  simpa only [mappingCylinderExtensionSet] using hExtension

end MappingCylinder

section DeformationRetractHomotopyEquiv

variable {Z : Type*} [TopologicalSpace Z] {A : Set Z}

/-- Helper for Theorem 58.1: a retraction followed by subtype inclusion is homotopic
to the identity on the retract. -/
private lemma retractionCompInclusionHomotopicId (r : Set.Retraction A) :
    (r.toContinuousMap.comp
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, Z))).Homotopic
        (ContinuousMap.id A) := by
  -- The composite is strictly the identity by the retraction's left-inverse law.
  have hComposite :
      r.toContinuousMap.comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, Z)) = ContinuousMap.id A := by
    ext a
    exact congrArg Subtype.val (r.leftInverse a)
  rw [hComposite]

/-- Helper for Theorem 58.1: inclusion after the endpoint retraction is homotopic
to the ambient identity. -/
private lemma inclusionCompRetractionHomotopicId (H : Set.DeformationRetraction A) :
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, Z)).comp
      H.toRetraction.toContinuousMap).Homotopic (ContinuousMap.id Z) := by
  -- Reverse the stored deformation homotopy and forget its relative condition.
  have hAmbient : H.toRetraction.toAmbient.Homotopic (ContinuousMap.id Z) :=
    ⟨H.toHomotopyRel.symm.toHomotopy⟩
  simpa only [Set.Retraction.toAmbient] using hAmbient

/-- Helper for Theorem 58.1: deformation-retraction data gives a homotopy equivalence
from the retract to its ambient space. -/
private def deformationRetractionHomotopyEquiv (H : Set.DeformationRetraction A) : A ≃ₕ Z :=
  { toFun := ⟨Subtype.val, continuous_subtype_val⟩
    invFun := H.toRetraction.toContinuousMap
    left_inv := retractionCompInclusionHomotopicId H.toRetraction
    right_inv := inclusionCompRetractionHomotopicId H }

/-- Helper for Theorem 58.1: every deformation retract is homotopy equivalent to its
ambient space. -/
private lemma deformationRetractHomotopyEquivExists (hA : Set.IsDeformationRetract A) :
    Nonempty (A ≃ₕ Z) := by
  -- Recover concrete deformation data and apply the canonical inclusion/retraction equivalence.
  obtain ⟨r, ⟨H⟩⟩ := (Set.isDeformationRetract_iff A).mp hA
  exact ⟨deformationRetractionHomotopyEquiv
    (Set.DeformationRetraction.ofHomotopyRel r H)⟩

end DeformationRetractHomotopyEquiv

/-- Theorem 58.1: Two spaces have the same homotopy type if and only if they are
homeomorphic to deformation retracts of a single space. -/
theorem sameHomotopyType_iff_commonDeformationRetracts (X : TopCat.{u}) (Y : TopCat.{v}) :
    SameHomotopyType X Y ↔
      ∃ (Z : TopCat.{max u v}) (A B : Set Z),
        Set.IsDeformationRetract A ∧ Set.IsDeformationRetract B ∧
          Nonempty (X ≃ₜ A) ∧ Nonempty (Y ≃ₜ B) := by
  rw [SameHomotopyType.iff_nonempty_homotopyEquiv]
  constructor
  · rintro ⟨e⟩
    -- Use the mapping cylinder of the supplied homotopy equivalence as the common space.
    obtain ⟨hBottom, eBottom⟩ := mappingCylinderBottomDeformationData e.toFun
    exact ⟨TopCat.of (MappingCylinder e.toFun), mappingCylinderTopRange e.toFun,
      mappingCylinderBottomRange e.toFun, mappingCylinderTop_isDeformationRetract e,
      hBottom, ⟨mappingCylinderTopHomeomorph e⟩, eBottom⟩
  · rintro ⟨Z, A, B, hA, hB, ⟨eXA⟩, ⟨eYB⟩⟩
    -- Pass from both deformation retracts to the ambient space and compose four equivalences.
    obtain ⟨eAZ⟩ := deformationRetractHomotopyEquivExists hA
    obtain ⟨eBZ⟩ := deformationRetractHomotopyEquivExists hB
    exact ⟨eXA.toHomotopyEquiv.trans <|
      eAZ.trans <| eBZ.symm.trans eYB.symm.toHomotopyEquiv⟩
