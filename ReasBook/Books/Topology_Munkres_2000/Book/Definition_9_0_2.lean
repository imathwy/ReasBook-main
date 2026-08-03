module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

public section

/- Definition 9.0.2 (1). The fundamental group of a pointed topological space. -/
#check FundamentalGroup

universe u v

/-- Helper for Definition 9.0.2: the map induced by a homeomorphism followed by
the map induced by its inverse is the identity on the source fundamental group. -/
lemma Homeomorph.fundamentalGroupMap_leftInverse
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (p : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq (e.symm : C(Y, X)) (e.symm_apply_apply x)
      (FundamentalGroup.map (e : C(X, Y)) x p) = p := by
  -- Expand the endpoint-adjusted map, then combine the two quotient maps.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply]
  -- On a representative loop, the composite path is pointwise the original loop.
  induction p using Quotient.ind
  case _ γ =>
    apply Quotient.sound
    suffices hpath : (fun path ↦ path.cast (e.symm_apply_apply x).symm
        (e.symm_apply_apply x).symm)
        ((fun path ↦ path.map e.symm.continuous)
          ((fun path ↦ path.map e.continuous) γ)) = γ by
      rw [hpath]
    ext t
    change e.symm (e (γ t)) = γ t
    exact e.symm_apply_apply (γ t)

/-- Helper for Definition 9.0.2: the map induced by the inverse homeomorphism
followed by the original induced map is the identity on the target fundamental group. -/
lemma Homeomorph.fundamentalGroupMap_rightInverse
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (p : FundamentalGroup Y (e x)) :
    FundamentalGroup.map (e : C(X, Y)) x
      (FundamentalGroup.mapOfEq (e.symm : C(Y, X)) (e.symm_apply_apply x) p) = p := by
  -- Move the forward map through the endpoint cast and combine the quotient maps.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
    Path.Homotopic.Quotient.map_cast]
  -- On a representative loop, the inverse-first composite is pointwise unchanged.
  induction p using Quotient.ind
  case _ γ =>
    apply Quotient.sound
    suffices hpath : (fun path ↦ path.cast
        (congrArg e (e.symm_apply_apply x).symm)
        (congrArg e (e.symm_apply_apply x).symm))
        ((fun path ↦ path.map e.continuous)
          ((fun path ↦ path.map e.symm.continuous) γ)) = γ by
      rw [hpath]
    ext t
    change e (e.symm (γ t)) = γ t
    exact e.apply_symm_apply (γ t)

/-- Definition 9.0.2. The multiplicative equivalence of fundamental groups induced by a
homeomorphism. -/
@[expose] noncomputable def Homeomorph.fundamentalGroupMulEquiv
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  let forward : FundamentalGroup X x →* FundamentalGroup Y (e x) :=
    FundamentalGroup.map (e : C(X, Y)) x
  let inverse : FundamentalGroup Y (e x) →* FundamentalGroup X x :=
    FundamentalGroup.mapOfEq (e.symm : C(Y, X)) (e.symm_apply_apply x)
  MulEquiv.mk'
    { toFun := forward
      invFun := inverse
      left_inv := e.fundamentalGroupMap_leftInverse x
      right_inv := e.fundamentalGroupMap_rightInverse x }
    forward.map_mul

/-- The forward homomorphism of `Homeomorph.fundamentalGroupMulEquiv` is the
homomorphism induced by the homeomorphism. -/
@[simp] theorem Homeomorph.fundamentalGroupMulEquiv_toMonoidHom
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    (e.fundamentalGroupMulEquiv x).toMonoidHom = FundamentalGroup.map (e : C(X, Y)) x := rfl

/-- The homeomorphism-induced equivalence acts by the usual induced map on
fundamental groups. -/
@[simp] theorem Homeomorph.fundamentalGroupMulEquiv_apply
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (p : FundamentalGroup X x) :
    e.fundamentalGroupMulEquiv x p = FundamentalGroup.map (e : C(X, Y)) x p := rfl

/- Definition 9.0.2 (2). Homeomorphic spaces have isomorphic fundamental groups at
corresponding basepoints. -/
#check Homeomorph.fundamentalGroupMulEquiv

/-- For a path-connected space, simple connectedness is equivalent to the fundamental group at a
chosen basepoint being trivial. -/
theorem simplyConnectedSpace_iff_subsingleton_fundamentalGroup
    (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    SimplyConnectedSpace X ↔ Subsingleton (FundamentalGroup X x) := by
  constructor
  · intro h
    -- A simply connected space has a subsingleton fundamental group at every basepoint.
    letI : SimplyConnectedSpace X := h
    infer_instance
  · intro h
    -- Reduce simple connectedness to null-homotopy of every based loop.
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨inferInstance, ?_⟩
    intro y γ
    letI : Subsingleton (FundamentalGroup X x) := h
    -- Path connectedness transports triviality from `x` to the arbitrary basepoint `y`.
    have hy : Subsingleton (FundamentalGroup X y) :=
      (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x y).toEquiv.symm.subsingleton
    -- Equality of the two loop classes is exactly the required path homotopy.
    exact Quotient.eq.mp (@Subsingleton.elim (FundamentalGroup X y) hy ⟦γ⟧ ⟦Path.refl y⟧)

end
