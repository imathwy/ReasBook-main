import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Problem_15_3_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped Topology Topology.Homotopy HomotopyClasses

noncomputable section

universe u v

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall: Chapter 9 already exports the canonical induced-map owners
-- `homotopyGroupMap`, `ContinuousMap.eStar`, and `ContinuousMap.eStarMulHomOverEq` for maps on
-- homotopy groups, and Chapter 15 packages `K(π,n)` via `IsEilenbergMacLaneSpace` in
-- `Problem_15_3_6`.

-- The representative-level homotopy lemma is already public in Problem 15.3.6; this file reuses
-- that owner instead of introducing a duplicate private declaration with the same generated name.

/-- The representative-level comparison map sending a based map to its induced homomorphism on the
distinguished nontrivial homotopy groups of Eilenberg-MacLane models. -/
private noncomputable def basedMapToHom
    {π : Type u} [Group π] {ρ : Type v} [Group ρ] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* ρ) :
    (X ⟶ Y) → (π →* ρ) :=
  fun f ↦
    let g : C(X.right, Y.right) := f.right.hom
    eY.toMonoidHom.comp
      ((g.eStarMulHomOverEq n (fundamentalGroupFunctorMap_basepoint f)).comp
        eX.symm.toMonoidHom)

/-- A based homotopy step induces the same representative-level comparison homomorphism. -/
private theorem basedMapToHom_eq_of_basedHomotopyRel
    {π : Type u} [Group π] {ρ : Type v} [Group ρ] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* ρ)
    {f g : X ⟶ Y}
    (hfg : basedHomotopyRel f g) :
    basedMapToHom n eX eY f = basedMapToHom n eX eY g := sorry

/-- Based-homotopic representatives induce the same homomorphism on the distinguished homotopy
group. -/
private theorem basedMapToHom_eq_of_basedHomotopy
    {π : Type u} [Group π] {ρ : Type v} [Group ρ] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* ρ)
    {f g : X ⟶ Y}
    (hfg : (basedHomotopySetoid X Y).r f g) :
    basedMapToHom n eX eY f = basedMapToHom n eX eY g := by
  induction hfg with
  | rel _ _ h => exact basedMapToHom_eq_of_basedHomotopyRel n eX eY h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The comparison map from based homotopy classes of maps to group homomorphisms, computed using
chosen identifications of the distinguished homotopy groups with `π` and `ρ`. -/
noncomputable def basedHomotopyClassesToHom
    {π : Type u} [Group π] {ρ : Type v} [Group ρ] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* ρ) :
    Ho*[X, Y] → (π →* ρ) :=
  Quotient.lift (basedMapToHom n eX eY)
    (fun _ _ hfg ↦ basedMapToHom_eq_of_basedHomotopy n eX eY hfg)

/-- The representative-level comparison homomorphism attached to a based map, obtained by applying
`basedHomotopyClassesToHom` to its based homotopy class. -/
noncomputable abbrev basedMapClassToHom
    {π : Type u} [Group π] {ρ : Type v} [Group ρ] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* ρ)
    (f : X ⟶ Y) :
    π →* ρ :=
  basedHomotopyClassesToHom n eX eY ((Quotient.mk (basedHomotopySetoid X Y) f : Ho*[X, Y]))

/-- Applying `basedHomotopyClassesToHom` to the class of a representative based map returns
`basedMapClassToHom`. -/
theorem basedHomotopyClassesToHom_apply
    {π : Type u} [Group π] {ρ : Type v} [Group ρ] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* ρ)
    (f : X ⟶ Y) :
    basedHomotopyClassesToHom n eX eY ((Quotient.mk (basedHomotopySetoid X Y) f : Ho*[X, Y])) =
      basedMapClassToHom n eX eY f :=
  rfl

/-- Based-homotopic representatives define the same representative-level comparison homomorphism. -/
theorem basedMapClassToHom_eq_of_basedHomotopy
    {π : Type u} [Group π] {ρ : Type v} [Group ρ] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* ρ)
    {f g : X ⟶ Y}
    (hfg : (basedHomotopySetoid X Y).r f g) :
    basedMapClassToHom n eX eY f = basedMapClassToHom n eX eY g := by
  change basedHomotopyClassesToHom n eX eY ((Quotient.mk (basedHomotopySetoid X Y) f : Ho*[X, Y])) =
    basedHomotopyClassesToHom n eX eY ((Quotient.mk (basedHomotopySetoid X Y) g : Ho*[X, Y]))
  simpa using congrArg (basedHomotopyClassesToHom n eX eY) (Quotient.sound hfg)

/-- Problem 15.3.7. Writing the source degree `n ≥ 1` as `n + 1`, if `X` and `Y` are based
spaces realizing `K(π, n + 1)` and `K(ρ, n + 1)`, then for any chosen identifications of their
distinguished homotopy groups with `π` and `ρ`, the based homotopy classes `[X,Y]` are classified
by the resulting explicit comparison map to the group homomorphisms `π →* ρ`. -/
theorem basedHomotopyClasses_eilenbergMacLane_equiv_hom
    {π : Type u} [Group π] {ρ : Type v} [Group ρ] (n : ℕ)
    {X Y : BasedSpace}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* ρ)
    (hX : IsEilenbergMacLaneSpace π n.succPNat X.right (underTopBasepoint X))
    (hY : IsEilenbergMacLaneSpace ρ n.succPNat Y.right (underTopBasepoint Y)) :
    Function.Bijective (basedHomotopyClassesToHom n eX eY) := sorry
