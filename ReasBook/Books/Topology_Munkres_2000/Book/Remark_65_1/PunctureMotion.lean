module

public import Topology_Munkres_2000.Book.Corollary_58_5
public import Topology_Munkres_2000.Book.Definition_9_0_2
public import Topology_Munkres_2000.Book.Exercise_35_4.RadialRetraction
public import Mathlib.Topology.Connected.LocallyPathConnected

public section

open Set

namespace PuncturedPlaneMap

/-- Helper for Remark 65.1: subtracting a point outside a set never sends a
point of the set to the origin. -/
private lemma sub_puncture_mem
    (C : Set (EuclideanSpace ℝ (Fin 2)))
    (p : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2)))) (x : C) :
    (x : EuclideanSpace ℝ (Fin 2)) - p ∈ EuclideanPlane.punctured := by
  -- Equality to zero would identify the curve point with the chosen puncture.
  rw [EuclideanPlane.mem_punctured_iff, sub_ne_zero]
  intro hxp
  exact p.property (hxp ▸ x.property)

/-- Helper for Remark 65.1: translate a set inclusion so that a chosen
complement point becomes the puncture at the origin. -/
def translatedPunctureInclusion
    (C : Set (EuclideanSpace ℝ (Fin 2)))
    (p : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
    C(C, EuclideanPlane.punctured) :=
  ⟨fun x ↦ ⟨(x : EuclideanSpace ℝ (Fin 2)) - p, sub_puncture_mem C p x⟩,
    (continuous_subtype_val.sub continuous_const).subtype_mk (sub_puncture_mem C p)⟩

/-- Helper for Remark 65.1: the translated inclusion has the expected ambient
value. -/
lemma translatedPunctureInclusion_apply
    (C : Set (EuclideanSpace ℝ (Fin 2)))
    (p : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2)))) (x : C) :
    ((translatedPunctureInclusion C p x : EuclideanPlane.punctured) :
      EuclideanSpace ℝ (Fin 2)) = (x : EuclideanSpace ℝ (Fin 2)) - p := by
  -- Record the defining formula inside the construction's owner module.
  rfl

/-- Helper for Remark 65.1: moving the puncture along a path in the complement
gives a homotopy between the corresponding translated inclusions. -/
lemma translatedPunctureInclusion_homotopic_of_joinedIn
    (C : Set (EuclideanSpace ℝ (Fin 2)))
    (p q : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2))))
    (hjoined : JoinedIn Cᶜ (p : EuclideanSpace ℝ (Fin 2)) q) :
    (translatedPunctureInclusion C p).Homotopic
      (translatedPunctureInclusion C q) := by
  let puncturePath : Path (p : EuclideanSpace ℝ (Fin 2)) q := hjoined.somePath
  have homotopy_mem (z : unitInterval × C) :
      (z.2 : EuclideanSpace ℝ (Fin 2)) - puncturePath z.1 ∈
        EuclideanPlane.punctured := by
    -- Every intermediate puncture remains outside `C` by the path hypothesis.
    rw [EuclideanPlane.mem_punctured_iff, sub_ne_zero]
    intro hz
    exact (hjoined.somePath_mem z.1) (hz ▸ z.2.property)
  have homotopy_continuous : Continuous (fun z : unitInterval × C ↦
      (⟨(z.2 : EuclideanSpace ℝ (Fin 2)) - puncturePath z.1,
        homotopy_mem z⟩ : EuclideanPlane.punctured)) := by
    -- Subtraction is continuous in the curve point and path parameter.
    exact ((continuous_subtype_val.comp continuous_snd).sub
      (puncturePath.continuous.comp continuous_fst)).subtype_mk homotopy_mem
  let homotopyMap : C(unitInterval × C, EuclideanPlane.punctured) :=
    ⟨fun z ↦ ⟨(z.2 : EuclideanSpace ℝ (Fin 2)) - puncturePath z.1,
      homotopy_mem z⟩, homotopy_continuous⟩
  have map_zero (x : C) :
      homotopyMap (0, x) = translatedPunctureInclusion C p x := by
    -- At time zero the moving puncture is `p`.
    apply Subtype.ext
    simp only [homotopyMap, puncturePath, hjoined.somePath.source,
      translatedPunctureInclusion, ContinuousMap.coe_mk]
  have map_one (x : C) :
      homotopyMap (1, x) = translatedPunctureInclusion C q x := by
    -- At time one the moving puncture is `q`.
    apply Subtype.ext
    simp only [homotopyMap, puncturePath, hjoined.somePath.target,
      translatedPunctureInclusion, ContinuousMap.coe_mk]
  exact ⟨
    { homotopyMap with
      map_zero_left := map_zero
      map_one_left := map_one }⟩

/-- Helper for Remark 65.1: homotopy invariance of injectivity in mathlib's
canonical fundamental-group convention. -/
lemma fundamentalGroupMap_injective_of_homotopic_canonical
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h k : C(X, Y)) (x : X) (homotopic : h.Homotopic k)
    (h_injective : Function.Injective (FundamentalGroup.map h x)) :
    Function.Injective (FundamentalGroup.map k x) := by
  -- Pass to opposite groups, where Corollary 58.5 is stated.
  have hLeftInjective : Function.Injective
      (FundamentalGroup.LeftToRight.map h x) :=
    MulOpposite.op_bijective.1.comp
      (h_injective.comp MulOpposite.unop_bijective.1)
  have kLeftInjective := fundamentalGroupMap_injective_of_homotopic
    h k x homotopic hLeftInjective
  -- Injectivity of `op` transports the resulting equality back.
  intro a b hab
  have hopEq : (.op a : (FundamentalGroup X x)ᵐᵒᵖ) = .op b := by
    apply kLeftInjective
    exact congrArg MulOpposite.op hab
  exact MulOpposite.op_bijective.1 hopEq

/-- Helper for Remark 65.1: homotopy invariance of surjectivity in mathlib's
canonical fundamental-group convention. -/
lemma fundamentalGroupMap_surjective_of_homotopic_canonical
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (h k : C(X, Y)) (x : X) (homotopic : h.Homotopic k)
    (h_surjective : Function.Surjective (FundamentalGroup.map h x)) :
    Function.Surjective (FundamentalGroup.map k x) := by
  -- Pass to opposite groups, where Corollary 58.5 is stated.
  have hLeftSurjective : Function.Surjective
      (FundamentalGroup.LeftToRight.map h x) :=
    MulOpposite.op_bijective.2.comp
      (h_surjective.comp MulOpposite.unop_bijective.2)
  have kLeftSurjective := fundamentalGroupMap_surjective_of_homotopic
    h k x homotopic hLeftSurjective
  -- Lift the opposite target and remove `op` from the resulting equality.
  intro target
  obtain ⟨source, hsource⟩ := kLeftSurjective (.op target)
  refine ⟨source.unop, ?_⟩
  exact MulOpposite.op_bijective.1 hsource

/-- Helper for Remark 65.1: a bijective induced map in the left-to-right
convention is bijective in mathlib's canonical convention. -/
lemma fundamentalGroupMap_bijective_of_leftToRight
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X)
    (h_bijective : Function.Bijective (FundamentalGroup.LeftToRight.map f x)) :
    Function.Bijective (FundamentalGroup.map f x) := by
  -- Transport injectivity and surjectivity through the `op` equivalence.
  constructor
  · intro a b hab
    have hopEq : (.op a : (FundamentalGroup X x)ᵐᵒᵖ) = .op b :=
      h_bijective.1 (congrArg MulOpposite.op hab)
    exact MulOpposite.op_bijective.1 hopEq
  · intro target
    obtain ⟨source, hsource⟩ := h_bijective.2 (.op target)
    exact ⟨source.unop, MulOpposite.op_bijective.1 hsource⟩

/-- Helper for Remark 65.1: equal complementary components of a closed planar
set provide a path along which the puncture may move. -/
lemma joinedIn_compl_of_connectedComponentIn_eq
    (C : Set (EuclideanSpace ℝ (Fin 2))) (hCclosed : IsClosed C)
    (p q : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2))))
    (hcomponents : connectedComponentIn Cᶜ p = connectedComponentIn Cᶜ q) :
    JoinedIn Cᶜ (p : EuclideanSpace ℝ (Fin 2)) q := by
  have hpComponent : (p : EuclideanSpace ℝ (Fin 2)) ∈
      connectedComponentIn Cᶜ p := mem_connectedComponentIn p.property
  have hqComponent : (q : EuclideanSpace ℝ (Fin 2)) ∈
      connectedComponentIn Cᶜ p := by
    rw [hcomponents]
    exact mem_connectedComponentIn q.property
  have componentPathConnected :
      IsPathConnected (connectedComponentIn Cᶜ (p : EuclideanSpace ℝ (Fin 2))) := by
    -- An open connected subset of the plane is path connected.
    apply (hCclosed.isOpen_compl.connectedComponentIn.isConnected_iff_isPathConnected).mp
    exact isConnected_connectedComponentIn_iff.mpr p.property
  exact (componentPathConnected.joinedIn p hpComponent q hqComponent).mono
    (connectedComponentIn_subset Cᶜ p)

/-- Helper for Remark 65.1: surjectivity of the translated inclusion is
unchanged when the puncture moves within one complementary component. -/
lemma translatedPunctureInclusionMap_surjective_iff_of_sameComponent
    (C : Set (EuclideanSpace ℝ (Fin 2))) (hCclosed : IsClosed C)
    (p q : (Cᶜ : Set (EuclideanSpace ℝ (Fin 2))))
    (hcomponents : connectedComponentIn Cᶜ p = connectedComponentIn Cᶜ q)
    (c : C) :
    Function.Surjective (FundamentalGroup.map (translatedPunctureInclusion C p) c) ↔
      Function.Surjective (FundamentalGroup.map (translatedPunctureInclusion C q) c) := by
  have homotopic := translatedPunctureInclusion_homotopic_of_joinedIn C p q
    (joinedIn_compl_of_connectedComponentIn_eq C hCclosed p q hcomponents)
  have homotopicSymm := translatedPunctureInclusion_homotopic_of_joinedIn C q p
    (joinedIn_compl_of_connectedComponentIn_eq C hCclosed q p hcomponents.symm)
  -- Corollary 58.5 transfers surjectivity in both directions.
  constructor
  · exact fundamentalGroupMap_surjective_of_homotopic_canonical
      (translatedPunctureInclusion C p) (translatedPunctureInclusion C q) c homotopic
  · exact fundamentalGroupMap_surjective_of_homotopic_canonical
      (translatedPunctureInclusion C q) (translatedPunctureInclusion C p) c homotopicSymm

end PuncturedPlaneMap

end
