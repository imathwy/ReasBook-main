module

public import Topology_Munkres_2000.Book.Definition_58_1.DeformationRetraction

public section

universe u

namespace Set.DeformationRetraction

variable {X : Type u} [TopologicalSpace X] {A B : Set X}

/-- Helper for Exercise 58.1: the composite endpoint map is continuous. -/
lemma continuous_compositeRetractionMap (H_A : Set.DeformationRetraction A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A)) :
    Continuous (fun x ↦ (⟨H_B.toRetraction.toContinuousMap
      (H_A.toRetraction.toContinuousMap x),
        (H_B.toRetraction.toContinuousMap (H_A.toRetraction.toContinuousMap x)).2⟩ : B)) := by
  fun_prop

/-- Helper for Exercise 58.1: the endpoint map obtained by composing the two retractions. -/
noncomputable def compositeRetractionMap (H_A : Set.DeformationRetraction A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A)) : C(X, B) :=
  { toFun := fun x ↦ ⟨H_B.toRetraction.toContinuousMap
        (H_A.toRetraction.toContinuousMap x),
      (H_B.toRetraction.toContinuousMap (H_A.toRetraction.toContinuousMap x)).2⟩
    continuous_toFun := continuous_compositeRetractionMap H_A H_B }

/-- Helper for Exercise 58.1: the composite endpoint map retracts onto `B`. -/
lemma compositeRetractionMap_leftInverse (H_A : Set.DeformationRetraction A) (hBA : B ⊆ A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A)) :
    Function.LeftInverse
      (fun x ↦ (⟨H_B.toRetraction.toContinuousMap (H_A.toRetraction.toContinuousMap x),
        (H_B.toRetraction.toContinuousMap (H_A.toRetraction.toContinuousMap x)).2⟩ : B))
      Subtype.val := by
  intro b
  let a : A := ⟨b, hBA b.2⟩
  let bA : Subtype.val ⁻¹' B := ⟨a, b.2⟩
  have hA : H_A.toRetraction.toContinuousMap b = a := H_A.toRetraction.leftInverse a
  have hB : H_B.toRetraction.toContinuousMap a = bA := H_B.toRetraction.leftInverse bA
  apply Subtype.ext
  calc
    ((H_B.toRetraction.toContinuousMap (H_A.toRetraction.toContinuousMap b)).1 : X) =
        ((H_B.toRetraction.toContinuousMap a).1 : X) := by rw [hA]
    _ = (bA.1 : X) := congrArg (fun z : Subtype.val ⁻¹' B ↦ (z.1 : X)) hB
    _ = b := rfl

/-- Helper for Exercise 58.1: the second-stage homotopy is continuous on `I × X`. -/
lemma continuous_secondStageHomotopy (H_A : Set.DeformationRetraction A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A)) :
    Continuous (fun tx : unitInterval × X ↦
      ((H_B.toHomotopyRel (tx.1, H_A.toRetraction.toContinuousMap tx.2) : A) : X)) := by
  fun_prop

/-- Helper for Exercise 58.1: the second-stage homotopy starts at the first retraction. -/
lemma secondStageHomotopy_zero (H_A : Set.DeformationRetraction A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A)) (x : X) :
    ((H_B.toHomotopyRel (0, H_A.toRetraction.toContinuousMap x) : A) : X) =
      H_A.toRetraction.toAmbient x := by
  simp

/-- Helper for Exercise 58.1: the second-stage homotopy ends at the composite retraction. -/
lemma secondStageHomotopy_one (H_A : Set.DeformationRetraction A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A)) (x : X) :
    ((H_B.toHomotopyRel (1, H_A.toRetraction.toContinuousMap x) : A) : X) =
      (H_B.toRetraction.toContinuousMap (H_A.toRetraction.toContinuousMap x) : A) := by
  simp

/-- Helper for Exercise 58.1: the second-stage homotopy fixes `B` pointwise. -/
lemma secondStageHomotopy_fixed (H_A : Set.DeformationRetraction A) (hBA : B ⊆ A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A))
    (t : unitInterval) (x : X) (hx : x ∈ B) :
    ((H_B.toHomotopyRel (t, H_A.toRetraction.toContinuousMap x) : A) : X) =
      (H_A.toRetraction.toContinuousMap x : X) := by
  have hA : H_A.toRetraction.toContinuousMap x = (⟨x, hBA hx⟩ : A) :=
    H_A.toRetraction.leftInverse ⟨x, hBA hx⟩
  have hmem : H_A.toRetraction.toContinuousMap x ∈ Subtype.val ⁻¹' B := by
    simpa [hA] using hx
  exact congrArg (fun a : A ↦ (a : X)) (H_B.toHomotopyRel.prop t _ hmem)

/-- Helper for Exercise 58.1: the composite endpoint map is continuous as an ambient self-map. -/
lemma continuous_compositeAmbientMap (H_A : Set.DeformationRetraction A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A)) :
    Continuous (fun x ↦
      ((H_B.toRetraction.toContinuousMap (H_A.toRetraction.toContinuousMap x) : A) : X)) := by
  fun_prop

/-- Helper for Exercise 58.1: the ambient composite endpoint map equals its `B`-valued map. -/
lemma compositeRetraction_ambient_eq (H_A : Set.DeformationRetraction A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A)) :
    ({ toFun := fun x ↦
          ((H_B.toRetraction.toContinuousMap (H_A.toRetraction.toContinuousMap x) : A) : X)
       continuous_toFun := continuous_compositeAmbientMap H_A H_B }
      : C(X, X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X)).comp
        (compositeRetractionMap H_A H_B) := by
  ext x
  rfl

/-- Compose deformation retractions of `X` onto `A` and of `A` onto the preimage of `B`. -/
noncomputable def trans (H_A : Set.DeformationRetraction A) (hBA : B ⊆ A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A)) :
    Set.DeformationRetraction B where
  toRetraction :=
    { toContinuousMap := compositeRetractionMap H_A H_B
      leftInverse := compositeRetractionMap_leftInverse H_A hBA H_B }
  toHomotopyRel :=
    let first : ContinuousMap.HomotopyRel
        (ContinuousMap.id X) H_A.toRetraction.toAmbient B :=
      { toHomotopy := H_A.toHomotopyRel.toHomotopy
        prop' := fun t x hx ↦ H_A.toHomotopyRel.prop t x (hBA hx) }
    let second : ContinuousMap.HomotopyRel H_A.toRetraction.toAmbient
        ({ toFun := fun x ↦ H_B.toRetraction.toContinuousMap
              (H_A.toRetraction.toContinuousMap x)
           continuous_toFun := continuous_compositeAmbientMap H_A H_B } : C(X, X)) B :=
      { toHomotopy :=
          { toFun := fun tx ↦ H_B.toHomotopyRel
              (tx.1, H_A.toRetraction.toContinuousMap tx.2)
            continuous_toFun := continuous_secondStageHomotopy H_A H_B
            map_zero_left := secondStageHomotopy_zero H_A H_B
            map_one_left := secondStageHomotopy_one H_A H_B }
        prop' := secondStageHomotopy_fixed H_A hBA H_B }
    first.trans <| second.cast rfl (compositeRetraction_ambient_eq H_A H_B)

/-- The endpoint retraction of a composite deformation retraction is the composite retraction. -/
theorem trans_toRetraction_apply (H_A : Set.DeformationRetraction A) (hBA : B ⊆ A)
    (H_B : Set.DeformationRetraction (Subtype.val ⁻¹' B : Set A)) (x : X) :
    ((H_A.trans hBA H_B).toRetraction.apply x : X) =
      H_B.toRetraction.apply (H_A.toRetraction.apply x) := by
  rfl

end Set.DeformationRetraction
