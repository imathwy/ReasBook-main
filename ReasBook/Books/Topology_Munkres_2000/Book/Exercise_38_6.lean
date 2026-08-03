module

public import Topology_Munkres_2000.Book.Proposition_38_1
public import Topology_Munkres_2000.Book.Exercise_38_6.Connected

public section

universe u

/-- Helper for Exercise 38.6: connectedness of `StoneCech X` forces `X` to be nonempty. -/
private lemma nonempty_of_connectedSpace_stoneCech {X : Type u} [TopologicalSpace X]
    [ConnectedSpace (StoneCech X)] : Nonempty X := by
  -- Pull nonemptiness back along the dense Stone–Čech unit map.
  exact denseRange_stoneCechUnit.nonempty

/-- Helper for Exercise 38.6: every continuous Boolean-valued map on `X` is constant when
`StoneCech X` is connected. -/
private lemma continuous_bool_eq_of_connectedSpace_stoneCech {X : Type u} [TopologicalSpace X]
    [ConnectedSpace (StoneCech X)] {f : X → Bool} (hf : Continuous f) (x y : X) :
    f x = f y := by
  -- Extend the map to `StoneCech X`, use connectedness there, and restrict back to `X`.
  calc
    f x = stoneCechExtend hf (stoneCechUnit x) := by
      rw [stoneCechExtend_stoneCechUnit]
    _ = stoneCechExtend hf (stoneCechUnit y) :=
      PreconnectedSpace.constant inferInstance (continuous_stoneCechExtend hf)
    _ = f y := by
      rw [stoneCechExtend_stoneCechUnit]

/-- Helper for Exercise 38.6: connectedness of `StoneCech X` implies preconnectedness of `X`. -/
private lemma preconnectedSpace_of_connectedSpace_stoneCech {X : Type u} [TopologicalSpace X]
    [ConnectedSpace (StoneCech X)] : PreconnectedSpace X := by
  -- Apply the Boolean-valued characterization of preconnected spaces.
  refine preconnectedSpace_of_forall_constant fun f hf x y ↦ ?_
  exact continuous_bool_eq_of_connectedSpace_stoneCech hf x y

/-- Exercise 38.6: A completely regular space `X` is connected if and only if its
Stone–Čech compactification `StoneCech X` is connected. -/
theorem connectedSpace_iff_stoneCech {X : Type u} [TopologicalSpace X]
    [T35Space X] : ConnectedSpace X ↔ ConnectedSpace (StoneCech X) := by
  constructor
  · intro hX
    -- The dense continuous unit map carries connectedness to the compactification.
    letI : ConnectedSpace X := hX
    infer_instance
  · intro hStoneCech
    -- Recover preconnectedness and nonemptiness separately, then assemble connectedness of `X`.
    letI : ConnectedSpace (StoneCech X) := hStoneCech
    exact
      { toPreconnectedSpace := preconnectedSpace_of_connectedSpace_stoneCech
        toNonempty := nonempty_of_connectedSpace_stoneCech }
