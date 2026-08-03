module

public import Topology_Munkres_2000.Book.Exercise_10_10.InitialSeg

public section

open scoped InitialSeg

universe u v

/-- The initial-segment embedding obtained by sending each element to the least unused value. -/
noncomputable def initialSegOfNoSectionSurjection
    {J : Type u} {C : Type v} [LinearOrder J] [LinearOrder C]
    [IsWellOrder J (· < ·)] [IsWellOrder C (· < ·)]
    (hsection : ∀ x : J, ∀ f : Set.Iio x → C, ¬ Function.Surjective f) :
    J ≤i C :=
  match InitialSeg.total (· < · : J → J → Prop) (· < · : C → C → Prop) with
  | .inl f => f
  | .inr g =>
      match g.principalSumRelIso with
      | .inl g' => False.elim (hsection g'.top g'.subrelIso g'.subrelIso.surjective)
      | .inr g' => g'.symm.toInitialSeg

/-- The canonical initial-segment embedding satisfies the least-unused recursion. -/
theorem initialSegOfNoSectionSurjection_isLeastUnused
    {J : Type u} {C : Type v} [LinearOrder J] [LinearOrder C]
    [IsWellOrder J (· < ·)] [IsWellOrder C (· < ·)]
    (hsection : ∀ x : J, ∀ f : Set.Iio x → C, ¬ Function.Surjective f) :
    Function.IsLeastUnused (initialSegOfNoSectionSurjection hsection) :=
  (initialSegOfNoSectionSurjection hsection).isLeastUnused

/-- Helper for Exercise 10.10: functions agreeing below an index have the same
set of values used below that index. -/
private lemma image_Iio_eq_of_eqOn_lt
    {ι : Type u} {α : Type v} [Preorder ι] {f g : ι → α} {x : ι}
    (hfg : ∀ y, y < x → f y = g y) :
    f '' Set.Iio x = g '' Set.Iio x := by
  -- Transport each image witness using pointwise agreement below `x`.
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (hfg y hy).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, hfg y hy⟩

/-- Helper for Exercise 10.10: a least-unused function on a well-founded linear
order is uniquely determined. -/
private lemma Function.IsLeastUnused.eq
    {ι : Type u} {α : Type v} [LinearOrder ι] [WellFoundedLT ι] [PartialOrder α]
    {f g : ι → α} (hf : f.IsLeastUnused) (hg : g.IsLeastUnused) :
    f = g := by
  -- Well-founded induction reduces equality at `x` to equality at all predecessors.
  funext x
  exact wellFounded_lt.induction x fun y hy ↦ by
    have hRange : f '' Set.Iio y = g '' Set.Iio y :=
      image_Iio_eq_of_eqOn_lt fun z hzy ↦ hy z hzy
    -- Equal earlier ranges make both recursion clauses choose the same least element.
    exact IsLeast.unique (hf.at y) (hRange.symm ▸ hg.at y)

/-- Exercise 10.10: If no strict section of the well-order `J` surjects onto the
well-order `C`, there is a unique function that sends each `x` to the least element
of `C` not used on `Set.Iio x`. -/
theorem existsUniqueLeastUnused
    {J : Type u} {C : Type v} [LinearOrder J] [LinearOrder C]
    [IsWellOrder J (· < ·)] [IsWellOrder C (· < ·)]
    (hsection : ∀ x : J, ∀ f : Set.Iio x → C, ¬ Function.Surjective f) :
    ∃! h : J → C, h.IsLeastUnused := by
  refine ⟨initialSegOfNoSectionSurjection hsection, ?_, ?_⟩
  · exact initialSegOfNoSectionSurjection_isLeastUnused hsection
  · intro h hh
    -- The generic uniqueness lemma compares the canonical function with any competitor.
    exact ((initialSegOfNoSectionSurjection_isLeastUnused hsection).eq hh).symm

end
