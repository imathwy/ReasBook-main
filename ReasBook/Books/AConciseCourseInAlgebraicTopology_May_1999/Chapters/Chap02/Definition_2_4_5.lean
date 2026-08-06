import Mathlib.CategoryTheory.Quotient

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

namespace CategoryTheory.HomRel

variable {C : Type u} [Category.{v} C] (r : HomRel C)

/-- Definition 2.4.5: a morphism is a homotopy equivalence if it admits a two-sided inverse up to
the homotopy relation `r`. This always becomes an isomorphism after passing to the quotient
category `CategoryTheory.Quotient r`, and the converse holds when `r` is a congruence. -/
class IsHomotopyEquivalence {X Y : C} (f : X ⟶ Y) : Prop where
  /-- A homotopy equivalence admits a two-sided inverse up to the relation `r`. -/
  exists_inverse :
    ∃ g : Y ⟶ X, r (g ≫ f) (𝟙 Y) ∧ r (f ≫ g) (𝟙 X)

namespace IsHomotopyEquivalence

/-- A morphism is a homotopy equivalence exactly when it admits a two-sided inverse up to `r`. -/
theorem iff_exists_inverse {X Y : C} {f : X ⟶ Y} :
    IsHomotopyEquivalence r f ↔
      ∃ g : Y ⟶ X, r (g ≫ f) (𝟙 Y) ∧ r (f ≫ g) (𝟙 X) :=
  ⟨fun h ↦ h.exists_inverse, fun h ↦ ⟨h⟩⟩

/-- A homotopy equivalence becomes an isomorphism after passing to the quotient category. -/
instance isIso_map {X Y : C} {f : X ⟶ Y} [IsHomotopyEquivalence r f] :
    IsIso ((Quotient.functor r).map f) := by
  rcases (inferInstance : IsHomotopyEquivalence r f).exists_inverse with ⟨g, hgf, hfg⟩
  refine IsIso.mk' ⟨(Quotient.functor r).map g, ?_, ?_⟩
  · simpa using CategoryTheory.Quotient.sound r hgf
  · simpa using CategoryTheory.Quotient.sound r hfg

/-- If `r` is a congruence, invertibility in the quotient category canonically induces a homotopy
equivalence. The low priority keeps this reverse bridge from firing eagerly when a more specific
source of `IsHomotopyEquivalence r f` is already available. -/
@[instance low]
instance isHomotopyEquivalence_of_isIso_map [Congruence r] {X Y : C}
    {f : X ⟶ Y} [IsIso ((Quotient.functor r).map f)] :
    IsHomotopyEquivalence r f := by
  obtain ⟨g, hg : (Quotient.functor r).map g = inv ((Quotient.functor r).map f)⟩ :=
    (Quotient.functor r).map_surjective (inv ((Quotient.functor r).map f))
  refine ⟨⟨g, ?_, ?_⟩⟩
  · exact (Quotient.functor_map_eq_iff r (g ≫ f) (𝟙 Y)).mp <| by
      simp [hg]
  · exact (Quotient.functor_map_eq_iff r (f ≫ g) (𝟙 X)).mp <| by
      simp [hg]

/-- If `r` is a congruence, any morphism whose image in the quotient is invertible is already a
homotopy equivalence for `r`. -/
theorem of_isIso_map [Congruence r] {X Y : C} {f : X ⟶ Y}
    [IsIso ((Quotient.functor r).map f)] :
    IsHomotopyEquivalence r f :=
  inferInstance

/-- For a congruence relation, homotopy equivalences are exactly the morphisms that become
isomorphisms in the quotient category. -/
theorem isIso_map_iff [Congruence r] {X Y : C} {f : X ⟶ Y} :
    IsIso ((Quotient.functor r).map f) ↔ IsHomotopyEquivalence r f := by
  constructor
  · intro hf
    let _ : IsIso ((Quotient.functor r).map f) := hf
    exact inferInstance
  · intro hf
    let _ : IsHomotopyEquivalence r f := hf
    exact inferInstance

end IsHomotopyEquivalence

end CategoryTheory.HomRel
