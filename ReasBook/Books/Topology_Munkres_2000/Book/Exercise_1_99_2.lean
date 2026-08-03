module

public import Mathlib.Order.Interval.Set.InitialSeg

public section

universe u v

/-- Helper for Exercise 1.99.2: a map is the underlying function of an initial segment exactly
when it is strictly monotone and its range is the whole codomain or a strict section. -/
lemma existsInitialSeg_iff_strictMono_range
    {J : Type u} {E : Type v} [LinearOrder J] [LinearOrder E]
    [IsWellOrder E (· < ·)] (h : J → E) :
    (∃ f : J ≤i E, (f : J → E) = h) ↔
      StrictMono h ∧ (Set.range h = Set.univ ∨ ∃ e : E, Set.range h = Set.Iio e) := by
  constructor
  · rintro ⟨f, rfl⟩
    -- An initial segment is strictly monotone, and its lower range is classified in a well-order.
    exact ⟨f.strictMono, f.isLowerSet_range.eq_univ_or_Iio⟩
  · rintro ⟨hmono, hrange⟩
    -- Build the relation embedding, using the stated range description for downward closure.
    let relEmbedding : (fun x y : J => x < y) ↪r (fun x y : E => x < y) :=
      { toFun := h
        inj' := hmono.injective
        map_rel_iff' := hmono.lt_iff_lt }
    have hinitial : ∀ a b, b < relEmbedding a → b ∈ Set.range relEmbedding := by
      intro a b hba
      rcases hrange with hrange | ⟨e, hrange⟩
      · rw [show Set.range relEmbedding = Set.univ by simpa [relEmbedding] using hrange]
        exact Set.mem_univ b
      · rw [show Set.range relEmbedding = Set.Iio e by simpa [relEmbedding] using hrange]
        have ha : h a ∈ Set.Iio e := by
          rw [← hrange]
          exact ⟨a, rfl⟩
        have ha' : relEmbedding a < e := by
          simpa [relEmbedding] using ha
        exact hba.trans ha'
    refine ⟨⟨relEmbedding, hinitial⟩, ?_⟩
    -- The constructed initial segment has the original underlying function.
    ext x
    rfl

/-- Helper for Exercise 1.99.2: the least-unused recursion makes the image of every predecessor
section exactly the predecessor section of the current value. -/
lemma image_Iio_eq_of_leastUnused
    {J : Type u} {E : Type v} [LinearOrder J] [LinearOrder E] (h : J → E)
    (hleast : ∀ α : J, IsLeast (Set.univ \ h '' Set.Iio α) (h α)) (α : J) :
    h '' Set.Iio α = Set.Iio (h α) := by
  have hmono : StrictMono h := by
    intro β γ hβγ
    have hγunused : h γ ∈ Set.univ \ h '' Set.Iio β := by
      refine ⟨Set.mem_univ _, ?_⟩
      rintro ⟨δ, hδβ, hδγ⟩
      have hδα : δ < γ := hδβ.trans hβγ
      exact (hleast γ).1.2 ⟨δ, hδα, hδγ⟩
    have hle : h β ≤ h γ := (hleast β).2 hγunused
    have hne : h β ≠ h γ := by
      intro heq
      exact (hleast γ).1.2 ⟨β, hβγ, heq⟩
    exact lt_of_le_of_ne hle hne
  ext x
  constructor
  · rintro ⟨β, hβα, rfl⟩
    -- Strict monotonicity sends earlier indices below the current value.
    exact hmono hβα
  · intro hx
    -- Any smaller unused value would contradict leastness of the current value.
    by_contra hnot
    have hxunused : x ∈ Set.univ \ h '' Set.Iio α := ⟨Set.mem_univ _, hnot⟩
    exact (not_le_of_gt hx) ((hleast α).2 hxunused)

/-- Helper for Exercise 1.99.2: an initial segment is characterized by choosing at each index the
least codomain value not used at an earlier index. -/
lemma existsInitialSeg_iff_leastUnused
    {J : Type u} {E : Type v} [LinearOrder J] [LinearOrder E]
    [IsWellOrder E (· < ·)] (h : J → E) :
    (∃ f : J ≤i E, (f : J → E) = h) ↔
      ∀ α : J, IsLeast (Set.univ \ h '' Set.Iio α) (h α) := by
  constructor
  · rintro ⟨f, rfl⟩ α
    -- Initial segments identify earlier images with `Set.Iio (f α)`.
    rw [f.image_Iio]
    simpa only [Set.sdiff_eq, Set.univ_inter, Set.compl_Iio] using
      (isLeast_Ici : IsLeast (Set.Ici (f α)) (f α))
  · intro hleast
    have hmono : StrictMono h := by
      intro β γ hβγ
      have hγunused : h γ ∈ Set.univ \ h '' Set.Iio β := by
        refine ⟨Set.mem_univ _, ?_⟩
        rintro ⟨δ, hδβ, hδγ⟩
        exact (hleast γ).1.2 ⟨δ, hδβ.trans hβγ, hδγ⟩
      have hle : h β ≤ h γ := (hleast β).2 hγunused
      have hne : h β ≠ h γ := by
        intro heq
        exact (hleast γ).1.2 ⟨β, hβγ, heq⟩
      exact lt_of_le_of_ne hle hne
    have hlower : IsLowerSet (Set.range h) := by
      intro x y hyx
      rintro ⟨α, rfl⟩
      rcases hyx.eq_or_lt with rfl | hyx
      · exact ⟨α, rfl⟩
      · have hyxmem : y ∈ Set.Iio (h α) := hyx
        rw [← image_Iio_eq_of_leastUnused h hleast α] at hyxmem
        rcases hyxmem with ⟨β, hβα, rfl⟩
        exact ⟨β, rfl⟩
    -- Classify the lower range and invoke the initial-segment bridge.
    exact (existsInitialSeg_iff_strictMono_range h).2 ⟨hmono, hlower.eq_univ_or_Iio⟩

/-- Exercise 1.99.2 (1): A map from a linear order into a well-order is strictly
order preserving with range the whole codomain or a strict section exactly when
each value is the least element not attained at an earlier index. -/
theorem initialSegmentRange_iff_leastUnused
    {J : Type u} {E : Type v} [LinearOrder J] [LinearOrder E]
    [IsWellOrder E (· < ·)] (h : J → E) :
    (StrictMono h ∧ (Set.range h = Set.univ ∨ ∃ e : E, Set.range h = Set.Iio e)) ↔
      ∀ α : J, IsLeast (Set.univ \ h '' Set.Iio α) (h α) := by
  -- Both textbook conditions are the two canonical interfaces to the same initial segment.
  exact (existsInitialSeg_iff_strictMono_range h).symm.trans
    (existsInitialSeg_iff_leastUnused h)

/-- Exercise 1.99.2 (2): No strict section of a well-order has the same order
type as the whole well-order. -/
theorem sectionNotOrderIso
    {E : Type u} [LinearOrder E] [IsWellOrder E (· < ·)] (e : E) :
    ¬ Nonempty (Set.Iio e ≃o E) := by
  rintro ⟨f⟩
  -- The inverse isomorphism followed by the canonical section gives a principal self-segment.
  exact PrincipalSeg.irrefl
    (PrincipalSeg.relIsoTrans f.symm.toRelIsoLT (Set.principalSegIio e))

/-- Exercise 1.99.2 (3): Two strict sections of a well-order have the same order
type exactly when their endpoints are equal. -/
theorem sectionOrderIso_iff
    {E : Type u} [LinearOrder E] [IsWellOrder E (· < ·)] (e e' : E) :
    Nonempty (Set.Iio e ≃o Set.Iio e') ↔ e = e' := by
  constructor
  · rintro ⟨f⟩
    -- Uniqueness of principal segments into `E` forces their top endpoints to agree.
    simpa only [Set.principalSegIio_top] using
      PrincipalSeg.top_eq f.toRelIsoLT (Set.principalSegIio e) (Set.principalSegIio e')
  · rintro rfl
    -- Equal endpoints give the identity order isomorphism.
    exact ⟨OrderIso.refl _⟩

end
