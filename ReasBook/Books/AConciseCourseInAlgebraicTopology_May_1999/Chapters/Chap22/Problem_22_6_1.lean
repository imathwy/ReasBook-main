import Mathlib.Algebra.Group.TypeTags.Hom
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap15.Problem_15_3_7

open CategoryTheory
open scoped Topology Topology.Homotopy HomotopyClasses

noncomputable section

universe u v

-- Semantic recall: `lean_leansearch` confirms `AddMonoidHom.toMultiplicative` as the canonical
-- additive/multiplicative hom transport, and Chapter 15 already formalizes the multiplicative
-- classification of based maps between `K(π, n + 1)` models.

/-- An additive-group restatement of the Chapter 15 `K(π, n + 1)` condition, hiding the
canonical `Multiplicative` tags used by the positive-degree homotopy-group API. -/
abbrev IsAdditiveEilenbergMacLaneSpace
    (π : Type u) [AddCommGroup π] (n : ℕ) (X : Under (⊤_ TopCat)) : Prop :=
  IsEilenbergMacLaneSpace (Multiplicative π) n.succPNat X.right (underTopBasepoint X)

/-- The Chapter 15 comparison map, transported across `Multiplicative`, with codomain rewritten
as additive homomorphisms `π →+ ρ`. -/
def basedHomotopyClassesToAddMonoidHom
    {π : Type u} [AddCommGroup π] {ρ : Type v} [AddCommGroup ρ] (n : ℕ)
    {X Y : Under (⊤_ TopCat)}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* Multiplicative π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* Multiplicative ρ) :
    Ho*[X, Y] → (π →+ ρ) :=
  fun f ↦
    (basedHomotopyClassesToHom n eX eY f).toAdditive

/-- The representative-level additive comparison homomorphism attached to a based map, obtained
by applying `basedHomotopyClassesToAddMonoidHom` to its based homotopy class. -/
abbrev basedMapClassToAddMonoidHom
    {π : Type u} [AddCommGroup π] {ρ : Type v} [AddCommGroup ρ] (n : ℕ)
    {X Y : Under (⊤_ TopCat)}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* Multiplicative π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* Multiplicative ρ)
    (f : X ⟶ Y) :
    π →+ ρ :=
  basedHomotopyClassesToAddMonoidHom n eX eY
    ((Quotient.mk (basedHomotopySetoid X Y) f : Ho*[X, Y]))

/-- Applying `basedHomotopyClassesToAddMonoidHom` to the class of a representative based map
returns `basedMapClassToAddMonoidHom`. -/
theorem basedHomotopyClassesToAddMonoidHom_apply
    {π : Type u} [AddCommGroup π] {ρ : Type v} [AddCommGroup ρ] (n : ℕ)
    {X Y : Under (⊤_ TopCat)}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* Multiplicative π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* Multiplicative ρ)
    (f : X ⟶ Y) :
    basedHomotopyClassesToAddMonoidHom n eX eY
        ((Quotient.mk (basedHomotopySetoid X Y) f : Ho*[X, Y])) =
      basedMapClassToAddMonoidHom n eX eY f :=
  rfl

/-- Based-homotopic representatives define the same representative-level additive comparison
homomorphism. -/
theorem basedMapClassToAddMonoidHom_eq_of_basedHomotopy
    {π : Type u} [AddCommGroup π] {ρ : Type v} [AddCommGroup ρ] (n : ℕ)
    {X Y : Under (⊤_ TopCat)}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* Multiplicative π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* Multiplicative ρ)
    {f g : X ⟶ Y}
    (hfg : (basedHomotopySetoid X Y).r f g) :
    basedMapClassToAddMonoidHom n eX eY f = basedMapClassToAddMonoidHom n eX eY g := by
  change basedHomotopyClassesToAddMonoidHom n eX eY
      ((Quotient.mk (basedHomotopySetoid X Y) f : Ho*[X, Y])) =
    basedHomotopyClassesToAddMonoidHom n eX eY
      ((Quotient.mk (basedHomotopySetoid X Y) g : Ho*[X, Y]))
  simpa using congrArg (basedHomotopyClassesToAddMonoidHom n eX eY) (Quotient.sound hfg)

/-- If `X` and `Y` realize `K(π, n + 1)` and `K(ρ, n + 1)`, then the transported Chapter 15
comparison map is bijective onto additive homomorphisms `π →+ ρ`. -/
theorem basedHomotopyClassesToAddMonoidHom_bijective
    {π : Type u} [AddCommGroup π] {ρ : Type v} [AddCommGroup ρ] (n : ℕ)
    {X Y : Under (⊤_ TopCat)}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* Multiplicative π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* Multiplicative ρ)
    (hX : IsAdditiveEilenbergMacLaneSpace π n X)
    (hY : IsAdditiveEilenbergMacLaneSpace ρ n Y) :
    Function.Bijective (basedHomotopyClassesToAddMonoidHom n eX eY) :=
  (((MonoidHom.toAdditive :
      (Multiplicative π →* Multiplicative ρ) ≃ (π →+ ρ))).bijective).comp
    (basedHomotopyClasses_eilenbergMacLane_equiv_hom n eX eY hX hY)

/-- Problem 22.6.1. Writing the positive source degree as `n + 1`, if `X` and `Y` are based
spaces realizing `K(π, n + 1)` and `K(ρ, n + 1)` for abelian groups `π` and `ρ`, then the based
homotopy classes `[X,Y]` are in bijection with the additive homomorphisms `π →+ ρ`. The explicit
comparison map is `basedHomotopyClassesToAddMonoidHom`. -/
theorem basedHomotopyClasses_eilenbergMacLane_equiv_addMonoidHom
    {π : Type u} [AddCommGroup π] {ρ : Type v} [AddCommGroup ρ] (n : ℕ)
    {X Y : Under (⊤_ TopCat)}
    (eX : π_ (n + 1) X.right (underTopBasepoint X) ≃* Multiplicative π)
    (eY : π_ (n + 1) Y.right (underTopBasepoint Y) ≃* Multiplicative ρ)
    (hX : IsAdditiveEilenbergMacLaneSpace π n X)
    (hY : IsAdditiveEilenbergMacLaneSpace ρ n Y) :
    Nonempty (Ho*[X, Y] ≃ (π →+ ρ)) :=
  ⟨Equiv.ofBijective
    (basedHomotopyClassesToAddMonoidHom n eX eY)
    (basedHomotopyClassesToAddMonoidHom_bijective n eX eY hX hY)⟩
