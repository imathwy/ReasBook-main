import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_4_1

open CategoryTheory Limits
open scoped unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: the visible hits were for homological-algebra mapping
-- cones rather than the based-space cofiber construction. The verified local owners for this item
-- are `basedCone`, `homotopyCofiber`, `constantBasedMap`, and the pushout descent
-- `pushout.desc`.

section

variable {X Y Z : BasedSpace} (f : X ⟶ Y) (g : Y ⟶ Z)
variable
  (H : ((f ≫ g).right.hom).HomotopyRel ((constantBasedMap X Z).right.hom)
    ({underTopBasepoint X} : Set X.right))

/-- The raw cone-side formula attached to a nullhomotopy of `g ∘ f`. -/
def nullHomotopyToBasedConePoint :
    X.right × I → Z.right
  | (x, t) => H.toHomotopy (t, x)

/-- On the wedge segment `{x₀} × I`, the cone-side formula takes the constant basepoint value. -/
theorem nullHomotopyToBasedConePoint_basepoint (t : I) :
    nullHomotopyToBasedConePoint f g H (underTopBasepoint X, t) = underTopBasepoint Z := sorry

/-- At the cone vertex `t = 1`, the cone-side formula takes the constant basepoint value. -/
theorem nullHomotopyToBasedConePoint_top (x : X.right) :
    nullHomotopyToBasedConePoint f g H (x, 1) = underTopBasepoint Z := sorry

/-- The cone-side formula respects the smash-product relation defining `CX = X ∧ I`. -/
theorem nullHomotopyToBasedConePoint_respects {p q : X.right × I}
    (hpq : smashProductRel X basedUnitInterval p q) :
    nullHomotopyToBasedConePoint f g H p = nullHomotopyToBasedConePoint f g H q := sorry

/-- The quotient-lifted cone-side formula defines a continuous map `CX → Z`. -/
theorem nullHomotopyToBasedConeContinuous :
    Continuous
      ((Quotient.lift
          (nullHomotopyToBasedConePoint f g H)
          (fun _ _ hpq ↦ nullHomotopyToBasedConePoint_respects f g H hpq)) :
        (basedCone X).right → Z.right) := sorry

/-- The continuous map `CX → Z` obtained by descending the nullhomotopy along the cone quotient. -/
def nullHomotopyToBasedConeContinuousMap :
    C((basedCone X).right, Z.right) :=
  ⟨
    ((Quotient.lift
        (nullHomotopyToBasedConePoint f g H)
        (fun _ _ hpq ↦ nullHomotopyToBasedConePoint_respects f g H hpq)) :
      (basedCone X).right → Z.right),
    nullHomotopyToBasedConeContinuous f g H
  ⟩

/-- The descended cone-side map preserves the chosen basepoints. -/
theorem nullHomotopyToBasedCone_w :
    (basedCone X).hom ≫ TopCat.ofHom (nullHomotopyToBasedConeContinuousMap f g H) = Z.hom := sorry

/-- ProofStep 8.4.7 (1). If `g : Y ⟶ Z` has `g ∘ f`, formalized as `f ≫ g`,
nullhomotopic rel the basepoint of `X`, then the nullhomotopy descends to a based map `CX ⟶ Z`. -/
def nullHomotopyToBasedCone :
    basedCone X ⟶ Z :=
  Under.homMk
    (TopCat.ofHom (nullHomotopyToBasedConeContinuousMap f g H))
    (nullHomotopyToBasedCone_w f g H)

/-- Restricting the descended cone-side map along `X ⟶ CX` recovers `g ∘ f`. -/
theorem nullHomotopyToBasedCone_baseInclusion :
    f ≫ g = basedConeBaseInclusion X ≫ nullHomotopyToBasedCone f g H := sorry

/-- ProofStep 8.4.7 (2). The map `g : Y ⟶ Z`, together with the cone-side map
defined by the nullhomotopy of `g ∘ f`, induces a map `C_f ⟶ Z`. -/
def homotopyCofiberDescOfNullHomotopy :
    homotopyCofiber f ⟶ Z :=
  pushout.desc g (nullHomotopyToBasedCone f g H)
    (nullHomotopyToBasedCone_baseInclusion f g H)

/-- The induced map `C_f ⟶ Z` restricts to `g` on the target summand `Y ⟶ C_f`. -/
@[simp] theorem homotopyCofiberDescOfNullHomotopy_targetInclusion :
    homotopyCofiberTargetInclusion f ≫ homotopyCofiberDescOfNullHomotopy f g H =
      g := by
  simpa [homotopyCofiberDescOfNullHomotopy] using
    (pushout.inl_desc g (nullHomotopyToBasedCone f g H)
      (nullHomotopyToBasedCone_baseInclusion f g H))

/-- The induced map `C_f ⟶ Z` restricts to the descended cone-side map on the cone summand
`CX ⟶ C_f`. -/
@[simp] theorem homotopyCofiberDescOfNullHomotopy_coneInclusion :
    homotopyCofiberConeInclusion f ≫ homotopyCofiberDescOfNullHomotopy f g H =
      nullHomotopyToBasedCone f g H := by
  simpa [homotopyCofiberDescOfNullHomotopy] using
    (pushout.inr_desc g (nullHomotopyToBasedCone f g H)
      (nullHomotopyToBasedCone_baseInclusion f g H))

end
