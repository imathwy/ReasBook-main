module

public import Mathlib.Order.Interval.Set.InitialSeg

public section

universe u v

/-- The canonical initial-segment embedding obtained by filling the gaps in a strictly
order-preserving map between well-orders. -/
noncomputable def initialSegOfStrictMono
    {J : Type u} {E : Type v} [LinearOrder J] [LinearOrder E]
    [IsWellOrder J (· < ·)] [IsWellOrder E (· < ·)]
    (k : J → E) (hk : StrictMono k) : J ≤i E :=
  (RelEmbedding.ofMonotone k hk).collapse

/-- Exercise 1.99.3: If there is a strictly order-preserving map from the
well-order `J` to the well-order `E`, then `J` has the order type of `E` or of
a strict section `Set.Iio e` of `E`. -/
theorem orderIso_or_section_of_strictMono
    {J : Type u} {E : Type v} [LinearOrder J] [LinearOrder E]
    [IsWellOrder J (· < ·)] [IsWellOrder E (· < ·)]
    (k : J → E) (hk : StrictMono k) :
    Nonempty (J ≃o E) ∨ ∃ e : E, Nonempty (J ≃o Set.Iio e) := by
  match (initialSegOfStrictMono k hk).principalSumRelIso with
  | .inl f => exact .inr ⟨f.top, ⟨f.orderIsoIio⟩⟩
  | .inr f => exact .inl ⟨OrderIso.ofRelIsoLT f⟩
