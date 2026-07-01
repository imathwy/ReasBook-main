import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v uC uA uSheaf uComplex

section

/-- A commutative square
`E ⟶ Y`, `E ⟶ Z`, `Y ⟶ X`, `Z ⟶ X`
used as a Mayer-Vietoris test square. -/
structure MayerVietorisTestSquare (C : Type uC) [Category.{v} C] where
  /-- The terminal object of the square. -/
  X : C
  /-- The upper-right object of the square. -/
  Y : C
  /-- The lower-left object of the square. -/
  Z : C
  /-- The upper-left object of the square. -/
  E : C
  /-- The map `E ⟶ Y`. -/
  e_to_y : E ⟶ Y
  /-- The map `E ⟶ Z`. -/
  e_to_z : E ⟶ Z
  /-- The map `Y ⟶ X`. -/
  y_to_x : Y ⟶ X
  /-- The map `Z ⟶ X`. -/
  z_to_x : Z ⟶ X
  /-- The square commutes. -/
  comm : e_to_y ≫ y_to_x = e_to_z ≫ z_to_x

variable {C : Type uC} [Category.{v} C]

-- Proof sketch: the forward implication is exactly the hypothesis that objects in the essential
-- image of `R ε_*` have isomorphic comparison maps. For the reverse implication, use the
-- adjunction triangle `K' ⟶ R ε_* ε⁻¹ K' ⟶ M' ⟶ K'[1]`, apply the two-out-of-three result for
-- the comparison maps to show that `M'` satisfies the same comparison condition, and then prove
-- by induction on the lowest nonvanishing cohomology sheaf that any bounded-below `M'` with
-- vanishing `ε⁻¹ M'` and satisfying the comparison condition must be zero.
/-- Lemma 21.29.2: for a family of commutative squares
`E_α ⟶ Y_α`, `E_α ⟶ Z_α`, `Y_α ⟶ X_α`, `Z_α ⟶ X_α`, assume that every `τ'`-sheaf whose sections
on each square satisfy the pullback condition
`F'(X_α) = F'(Z_α) ×_{F'(E_α)} F'(Y_α)` is already a `τ`-sheaf, and assume that every object in
the essential image of `R ε_*` has all comparison maps
`c^{K'}_{X_α,Z_α,Y_α,E_α}` isomorphisms. Then a bounded-below object `K'` lies in the essential
image of `R ε_*` if and only if all of these comparison maps are isomorphisms. -/
lemma essentialImage_iff_comparison_maps_areIso_of_mayerVietoris_family
    {A : Type uA} (squares : A → MayerVietorisTestSquare C)
    {Sheaf : Type uSheaf} {Complex : Type uComplex}
    (isTauSheaf : Sheaf → Prop)
    (hasPullbackSections : MayerVietorisTestSquare C → Sheaf → Prop)
    (comparisonMapIsIso : MayerVietorisTestSquare C → Complex → Prop)
    (inEssentialImage : Complex → Prop)
    (isBoundedBelow : Complex → Prop)
    (hSheaf :
      ∀ F' : Sheaf, (∀ α : A, hasPullbackSections (squares α) F') → isTauSheaf F')
    (hEssentialImage :
      ∀ ⦃K' : Complex⦄, inEssentialImage K' → ∀ α : A, comparisonMapIsIso (squares α) K')
    {K' : Complex} (hK' : isBoundedBelow K') :
    inEssentialImage K' ↔ ∀ α : A, comparisonMapIsIso (squares α) K' := sorry

end
