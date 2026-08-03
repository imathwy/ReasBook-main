module

import Topology_Munkres_2000.Book.Exercise_1_99_3
public import Mathlib.Data.Set.Countable
public import Mathlib.Order.Interval.Set.InitialSeg

public section

universe u v

/-- Helper for Exercise 1.99.4: an order isomorphism and a principal segment
embedding in the same direction cannot coexist between well-orders. -/
lemma orderIso_not_principalSeg
    {A : Type u} {B : Type v} [LinearOrder A] [LinearOrder B]
    [IsWellOrder A (· < ·)] [IsWellOrder B (· < ·)]
    (hIso : Nonempty (A ≃o B)) : ¬ Nonempty (A <i B) := by
  -- Compose the inverse isomorphism with the strict comparison to obtain a
  -- forbidden principal segment from `B` to itself.
  rintro ⟨f⟩
  obtain ⟨e⟩ := hIso
  exact PrincipalSeg.irrefl (PrincipalSeg.relIsoTrans e.symm.toRelIsoLT f)

/-- Helper for Exercise 1.99.4: principal segment embeddings between two
well-orders are asymmetric. -/
lemma principalSeg_asymm
    {A : Type u} {B : Type v} [LinearOrder A] [LinearOrder B]
    [IsWellOrder A (· < ·)] [IsWellOrder B (· < ·)]
    (hAB : Nonempty (A <i B)) : ¬ Nonempty (B <i A) := by
  -- Opposite strict comparisons compose to a principal segment of `A` in itself.
  rintro ⟨g⟩
  obtain ⟨f⟩ := hAB
  exact PrincipalSeg.irrefl (f.trans g)

/-- Helper for Exercise 1.99.4: a type identified with a countable strict
section by a principal segment embedding is countable. -/
lemma countable_of_principalSeg_of_countableSection
    {A : Type u} {B : Type v} [LinearOrder A] [LinearOrder B]
    (f : A <i B) (hSection : (Set.Iio f.top).Countable) : Countable A := by
  -- Transfer the section's countability across the canonical order isomorphism.
  letI : Countable (Set.Iio f.top) := hSection.to_subtype
  exact Countable.of_equiv (Set.Iio f.top) f.orderIsoIio.symm.toEquiv

/-- Exercise 1.99.4 (a): For two well-orders, exactly one comparison holds: they
have the same order type, or one is a strict section of the other. -/
theorem orderTypeTrichotomy
    {A : Type u} {B : Type v} [LinearOrder A] [LinearOrder B]
    [IsWellOrder A (· < ·)] [IsWellOrder B (· < ·)] :
    let sameType := Nonempty (A ≃o B)
    let aSectionOfB := Nonempty (A <i B)
    let bSectionOfA := Nonempty (B <i A)
    (sameType ∨ aSectionOfB ∨ bSectionOfA) ∧
      ¬ (sameType ∧ aSectionOfB) ∧
      ¬ (sameType ∧ bSectionOfA) ∧
      ¬ (aSectionOfB ∧ bSectionOfA) := by
  -- Totality of initial segments supplies a comparison; its canonical split
  -- determines whether that comparison is strict or an isomorphism.
  dsimp only
  classical
  rcases InitialSeg.total (fun x y : A ↦ x < y) (fun x y : B ↦ x < y) with f | g
  · rcases f.principalSumRelIso with fStrict | fIso
    · refine ⟨Or.inr (Or.inl ⟨fStrict⟩), ?_, ?_, ?_⟩
      · rintro ⟨hIso, hStrict⟩
        exact orderIso_not_principalSeg hIso hStrict
      · rintro ⟨hIso, hReverse⟩
        exact orderIso_not_principalSeg (hIso.map fun e ↦ e.symm) hReverse
      · rintro ⟨hStrict, hReverse⟩
        exact principalSeg_asymm hStrict hReverse
    · refine ⟨Or.inl ⟨OrderIso.ofRelIsoLT fIso⟩, ?_, ?_, ?_⟩
      · rintro ⟨hIso, hStrict⟩
        exact orderIso_not_principalSeg hIso hStrict
      · rintro ⟨hIso, hReverse⟩
        exact orderIso_not_principalSeg (hIso.map fun e ↦ e.symm) hReverse
      · rintro ⟨hStrict, hReverse⟩
        exact principalSeg_asymm hStrict hReverse
  · rcases g.principalSumRelIso with gStrict | gIso
    · refine ⟨Or.inr (Or.inr ⟨gStrict⟩), ?_, ?_, ?_⟩
      · rintro ⟨hIso, hStrict⟩
        exact orderIso_not_principalSeg hIso hStrict
      · rintro ⟨hIso, hReverse⟩
        exact orderIso_not_principalSeg (hIso.map fun e ↦ e.symm) hReverse
      · rintro ⟨hStrict, hReverse⟩
        exact principalSeg_asymm hStrict hReverse
    · refine ⟨Or.inl ⟨(OrderIso.ofRelIsoLT gIso).symm⟩, ?_, ?_, ?_⟩
      · rintro ⟨hIso, hStrict⟩
        exact orderIso_not_principalSeg hIso hStrict
      · rintro ⟨hIso, hReverse⟩
        exact orderIso_not_principalSeg (hIso.map fun e ↦ e.symm) hReverse
      · rintro ⟨hStrict, hReverse⟩
        exact principalSeg_asymm hStrict hReverse

/-- Companion to Exercise 1.99.4 (b): Two uncountable well-orders whose strict sections
`Set.Iio a` and `Set.Iio b` are all countable have the same order type. -/
theorem orderIsoOfCountableSections
    {A : Type u} {B : Type v} [LinearOrder A] [LinearOrder B]
    [IsWellOrder A (· < ·)] [IsWellOrder B (· < ·)] [Uncountable A] [Uncountable B]
    (hA : ∀ a : A, (Set.Iio a).Countable) (hB : ∀ b : B, (Set.Iio b).Countable) :
    Nonempty (A ≃o B) := by
  -- The trichotomy is exhaustive, while either strict comparison would make
  -- its uncountable domain countable through the corresponding section.
  rcases orderTypeTrichotomy (A := A) (B := B) |>.1 with hIso | hStrict | hReverse
  · exact hIso
  · obtain ⟨f⟩ := hStrict
    exact ((not_countable (α := A))
      (countable_of_principalSeg_of_countableSection f (hB f.top))).elim
  · obtain ⟨g⟩ := hReverse
    exact ((not_countable (α := B))
      (countable_of_principalSeg_of_countableSection g (hA g.top))).elim

end
