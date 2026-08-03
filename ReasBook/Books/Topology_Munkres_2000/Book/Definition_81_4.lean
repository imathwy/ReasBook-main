module

public import Topology_Munkres_2000.Book.Definition_81_4.Regular
import Topology_Munkres_2000.Book.Exercise_72_1

public section

universe u v

namespace IsCoveringMap

/-- Helper for Definition 81.4: reflexive target-basepoint transport leaves the induced
fundamental-group homomorphism unchanged. -/
private lemma fundamentalGroupMapOfEq_refl
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) = FundamentalGroup.map f x := by
  -- Evaluate on a loop class, where reflexive endpoint transport is trivial.
  ext γ
  simp [FundamentalGroup.mapOfEq_apply]

/-- Helper for Definition 81.4: basepoint change along a path maps the induced subgroup at
the path's source onto the induced subgroup at its target. -/
private lemma fundamentalGroupMapRange_map_basepointChange
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) {e₀ e₁ : E} (γ : Path e₀ e₁) :
    (hp.fundamentalGroupMapRange (rfl : p e₀ = p e₀)).map
        (FundamentalGroup.fundamentalGroupMulEquivOfPath
          (γ.map hp.continuous)).toMonoidHom =
      hp.fundamentalGroupMapRange (rfl : p e₁ = p e₁) := by
  -- Normalize both transported maps before passing the naturality square to their ranges.
  unfold fundamentalGroupMapRange
  rw [fundamentalGroupMapOfEq_refl, fundamentalGroupMapOfEq_refl]
  have hcomm :
      (FundamentalGroup.fundamentalGroupMulEquivOfPath
          (γ.map hp.continuous)).toMonoidHom.comp
          (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀) =
        (FundamentalGroup.map ⟨p, hp.continuous⟩ e₁).comp
          (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom :=
    FundamentalGroup.map_comp_basepointChange ⟨p, hp.continuous⟩ γ
  -- Equality of the naturality-square homomorphisms gives equality of their ranges.
  calc
    (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀).range.map
        (FundamentalGroup.fundamentalGroupMulEquivOfPath
          (γ.map hp.continuous)).toMonoidHom =
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath
          (γ.map hp.continuous)).toMonoidHom.comp
        (FundamentalGroup.map ⟨p, hp.continuous⟩ e₀)).range :=
          MonoidHom.map_range _ _
    _ = ((FundamentalGroup.map ⟨p, hp.continuous⟩ e₁).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom).range :=
      congrArg (fun f ↦ f.range) hcomm
    _ = (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).toMonoidHom.range.map
        (FundamentalGroup.map ⟨p, hp.continuous⟩ e₁) :=
      MonoidHom.range_comp _ _
    _ = (⊤ : Subgroup (FundamentalGroup E e₁)).map
        (FundamentalGroup.map ⟨p, hp.continuous⟩ e₁) :=
      congrArg
        (fun H ↦ H.map (FundamentalGroup.map ⟨p, hp.continuous⟩ e₁))
        (FundamentalGroup.fundamentalGroupMulEquivOfPath γ).range_eq_top
    _ = (FundamentalGroup.map ⟨p, hp.continuous⟩ e₁).range :=
      (MonoidHom.range_eq_map _).symm

/-- Helper for Definition 81.4: normality of the induced subgroup is transported along a
path between choices of total-space basepoint. -/
private lemma fundamentalGroupMapRange_normal_of_path
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) {e₀ e₁ : E} (γ : Path e₀ e₁)
    (hnormal : (hp.fundamentalGroupMapRange (rfl : p e₀ = p e₀)).Normal) :
    (hp.fundamentalGroupMapRange (rfl : p e₁ = p e₁)).Normal := by
  -- Surjective basepoint change preserves normality, and the range bridge identifies its image.
  have hmapped := hnormal.map
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (γ.map hp.continuous)).toMonoidHom
    (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (γ.map hp.continuous)).surjective
  rwa [fundamentalGroupMapRange_map_basepointChange hp γ] at hmapped

end IsCoveringMap

namespace ConnectedCovering

variable {B : Type v} [TopologicalSpace B]

/-- Definition 81.4: for a chosen `b₀ : B` and `e₀` over it, the covering `C` is regular
exactly when the induced subgroup `C.isCoveringMap.fundamentalGroupMapRange h₀` (the source's
`H₀`) is normal in `π₁(B, b₀)`. -/
theorem isRegular_iff_fundamentalGroupMapRange_normal (C : ConnectedCovering.{u} B)
    (b₀ : B) (e₀ : C.Total) (h₀ : C.proj e₀ = b₀) :
    C.IsRegular ↔ (C.isCoveringMap.fundamentalGroupMapRange h₀).Normal := by
  constructor
  · intro hregular
    -- The forward implication is the chosen component of basepoint-independent regularity.
    exact hregular.normal b₀ e₀ h₀
  · intro hnormal
    -- Put the given subgroup at its literal projected basepoint before transporting it.
    subst b₀
    letI : PathConnectedSpace C.Total := C.pathConnectedSpace
    refine ⟨?_⟩
    intro b e he
    subst b
    -- Path-connectedness joins the chosen point to the arbitrary point required by `IsRegular`.
    exact C.isCoveringMap.fundamentalGroupMapRange_normal_of_path
      (PathConnectedSpace.somePath e₀ e) hnormal

end ConnectedCovering
