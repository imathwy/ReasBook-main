import Mathlib.AlgebraicGeometry.AffineScheme

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `Scheme.isAffine_of_isLimit` and the
-- affine-transition-limit API around `Scheme.Γ.mapCocone`; the source-facing owner below keeps the
-- explicit candidate `Spec (colimit (D.op ⋙ Scheme.Γ))` and its comparison cone.

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ i, IsAffine (D.obj i)]

/-- The explicit affine candidate for the directed limit of affine schemes. -/
noncomputable abbrev directedAffineLimitScheme : Scheme.{u} :=
  Spec (colimit (D.op ⋙ Scheme.Γ))

/-- The cone on the explicit affine candidate for the directed limit of affine schemes. -/
noncomputable abbrev directedAffineLimitCone : Cone D :=
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : OrderDual I) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  (Cone.postcompose (asIso α).inv).obj <|
    Scheme.Spec.mapCone (coneOfCoconeLeftOp (colimit.cocone (D.op ⋙ Scheme.Γ)))

/-- The cone on the explicit affine candidate has the expected stagewise comparison morphisms. -/
@[simp]
theorem directedAffineLimitCone_π_app (i : OrderDual I) :
    (directedAffineLimitCone D).π.app i =
      Spec.map (colimit.ι (D.op ⋙ Scheme.Γ) (Opposite.op i)) ≫ (D.obj i).isoSpec.inv := by
  simp [directedAffineLimitCone]

/-- Naturality of the comparison morphisms from the explicit affine limit candidate. -/
theorem directedAffineLimitCone_π_naturality {i j : OrderDual I} (f : i ⟶ j) :
    (directedAffineLimitCone D).π.app j = (directedAffineLimitCone D).π.app i ≫ D.map f := by
  simpa using ((directedAffineLimitCone D).w f).symm

/-- Lemma 32.2.1 (1): for a directed inverse system of affine schemes, the explicit cone on
`Spec (colimit_i Γ(S_i, \mathcal O))` is a limit cone in `Scheme`. -/
@[stacks 01YW]
theorem directedAffineLimitCone_isLimit :
    IsLimit (directedAffineLimitCone D) := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : OrderDual I) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let c : Cone ((D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec) :=
    Scheme.Spec.mapCone (coneOfCoconeLeftOp (colimit.cocone (D.op ⋙ Scheme.Γ)))
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec <|
    isLimitConeOfCoconeLeftOp (D ⋙ Scheme.Γ.rightOp) (colimit.isColimit (D.op ⋙ Scheme.Γ))
  simpa [directedAffineLimitCone, α, c] using
    (IsLimit.postcomposeHomEquiv (asIso α).symm c).symm hc

/-- Lemma 32.2.1 (2): the limit scheme `Spec (colimit_i Γ(S_i, \mathcal O))` is affine. -/
@[stacks 01YW]
theorem directedAffineLimitScheme_isAffine :
    IsAffine (directedAffineLimitScheme D) := by
  let α : D ⟶ (D ⋙ Scheme.Γ.rightOp) ⋙ Scheme.Spec := D.whiskerLeft ΓSpec.adjunction.unit
  have (i : OrderDual I) : IsIso (α.app i) := IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let hc := directedAffineLimitCone_isLimit D
  let e : directedAffineLimitScheme D ≅ Spec Γ(directedAffineLimitScheme D, ⊤) :=
    hc.conePointUniqueUpToIso <|
      ((IsLimit.postcomposeHomEquiv (asIso α).symm _).symm <|
        isLimitOfPreserves (Scheme.Γ.rightOp ⋙ Scheme.Spec) hc)
  exact .of_isIso e.hom

end

end AlgebraicGeometry
