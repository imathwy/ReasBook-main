/-- Exactness for pointed fragments means that the fiber of the chosen distinguished point under
the second map is exactly the image of the first map. -/
def pointedExact {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) (c₀ : C) : Prop :=
  ∀ b : B, g b = c₀ ↔ ∃ a : A, f a = b
