module

public import Mathlib.Data.Set.Basic

public section

universe u

namespace StrictOrder

/-- Definition 11.4 (1). An upper bound of `B` for the strict partial order `r`. -/
def IsUpperBound {A : Type u} (r : A → A → Prop) (B : Set A) (c : A) : Prop :=
  ∀ b ∈ B, b = c ∨ r b c

/-- Definition 11.4 (2). A maximal element for the strict partial order `r`. -/
def IsMaximal {A : Type u} (r : A → A → Prop) (m : A) : Prop :=
  ∀ a, ¬r m a

end StrictOrder
