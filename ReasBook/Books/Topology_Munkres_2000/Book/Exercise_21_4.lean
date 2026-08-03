module

public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine
public import Topology_Munkres_2000.Book.Example_16_3.OrderedSquare

public section

open Set Topology

namespace SorgenfreyLine

/-- Helper for Exercise 21.4: a reciprocal half-open interval based at `x` refines any
half-open real interval containing `x`. -/
private lemma exists_reciprocalIco_subset {a b x : ℝ} (hx : x ∈ Set.Ico a b) :
    ∃ n : ℕ, Set.Ico x (x + 1 / (n + 1 : ℝ)) ⊆ Set.Ico a b := by
  -- Choose a reciprocal radius smaller than the distance to the right endpoint.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx.2)
  refine ⟨n, ?_⟩
  have hendpoint : x + 1 / (n + 1 : ℝ) < b := by
    linarith
  intro y hy
  exact ⟨hx.1.trans hy.1, hy.2.trans hendpoint⟩

/-- Helper for Exercise 21.4: every point of the Sorgenfrey line has a countably generated
neighborhood filter. -/
private lemma nhds_isCountablyGenerated (x : SorgenfreyLine) :
    (𝓝 x).IsCountablyGenerated := by
  -- Refine the canonical half-open neighborhood basis to reciprocal intervals indexed by `ℕ`.
  refine (isTopologicalBasis_lowerLimitBasis.nhds_hasBasis.to_hasBasis
    (p' := fun _ : ℕ => True)
    (s' := fun n => Set.Ico (toReal x) (toReal x + 1 / (n + 1 : ℝ))) ?_ ?_).isCountablyGenerated
  · rintro s ⟨hs, hxs⟩
    rcases hs with ⟨a, b, hab, rfl⟩
    obtain ⟨n, hn⟩ := exists_reciprocalIco_subset hxs
    exact ⟨n, trivial, hn⟩
  · intro n _
    have hpositive : 0 < 1 / (n + 1 : ℝ) := by
      positivity
    have hendpoint : toReal x < toReal x + 1 / (n + 1 : ℝ) :=
      lt_add_of_pos_right _ hpositive
    refine ⟨Set.Ico (toReal x) (toReal x + 1 / (n + 1 : ℝ)), ?_, Set.Subset.rfl⟩
    exact ⟨⟨toReal x, toReal x + 1 / (n + 1 : ℝ), hendpoint, rfl⟩,
      Set.left_mem_Ico.mpr hendpoint⟩

/-- The Sorgenfrey line satisfies the first countability axiom. -/
instance instFirstCountableTopology : FirstCountableTopology SorgenfreyLine where
  -- The preceding countable half-open basis supplies the required neighborhood instance.
  nhds_generated_countable := nhds_isCountablyGenerated

end SorgenfreyLine

/-- Helper for Exercise 21.4: two countable sequences cofinal below and coinitial above a point
generate its order-topology neighborhood filter. -/
private lemma isCountablyGenerated_nhds_of_order_sequences
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α]
    (x : α) (lower upper : ℕ → α)
    (hlower : ∀ n, lower n < x) (hupper : ∀ n, x < upper n)
    (hlowerCofinal : ∀ a, a < x → ∃ n, a < lower n)
    (hupperCofinal : ∀ b, x < b → ∃ n, upper n < b) :
    (𝓝 x).IsCountablyGenerated := by
  -- Replace arbitrary open intervals around `x` by intervals with sequential endpoints.
  refine ((nhds_basis_Ioo' ⟨lower 0, hlower 0⟩ ⟨upper 0, hupper 0⟩).to_hasBasis
    (p' := fun _ : ℕ × ℕ => True)
    (s' := fun nm => Set.Ioo (lower nm.1) (upper nm.2)) ?_ ?_).isCountablyGenerated
  · rintro ⟨a, b⟩ ⟨hax, hxb⟩
    obtain ⟨n, han⟩ := hlowerCofinal a hax
    obtain ⟨m, hmb⟩ := hupperCofinal b hxb
    refine ⟨(n, m), trivial, ?_⟩
    exact Set.Ioo_subset_Ioo han.le hmb.le
  · rintro ⟨n, m⟩ _
    exact ⟨(lower n, upper m), ⟨hlower n, hupper m⟩, Set.Subset.rfl⟩

/-- Helper for Exercise 21.4: a countable sequence coinitial above `⊥` generates the
order-topology neighborhood filter at `⊥`. -/
private lemma isCountablyGenerated_nhds_bot_of_order_sequence
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderBot α] [OrderTopology α]
    [Nontrivial α] (upper : ℕ → α) (hupper : ∀ n, ⊥ < upper n)
    (hupperCofinal : ∀ b, (⊥ : α) < b → ∃ n, upper n < b) :
    (𝓝 (⊥ : α)).IsCountablyGenerated := by
  -- Refine the standard right-ray basis at the bottom endpoint to the chosen sequence.
  refine (nhds_bot_basis.to_hasBasis
    (p' := fun _ : ℕ => True) (s' := fun n => Set.Iio (upper n)) ?_ ?_).isCountablyGenerated
  · intro b hb
    obtain ⟨n, hnb⟩ := hupperCofinal b hb
    exact ⟨n, trivial, Set.Iio_subset_Iio hnb.le⟩
  · intro n _
    exact ⟨upper n, hupper n, Set.Subset.rfl⟩

/-- Helper for Exercise 21.4: a countable sequence cofinal below `⊤` generates the
order-topology neighborhood filter at `⊤`. -/
private lemma isCountablyGenerated_nhds_top_of_order_sequence
    {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTop α] [OrderTopology α]
    [Nontrivial α] (lower : ℕ → α) (hlower : ∀ n, lower n < ⊤)
    (hlowerCofinal : ∀ a, a < (⊤ : α) → ∃ n, a < lower n) :
    (𝓝 (⊤ : α)).IsCountablyGenerated := by
  -- Refine the standard left-ray basis at the top endpoint to the chosen sequence.
  refine (nhds_top_basis.to_hasBasis
    (p' := fun _ : ℕ => True) (s' := fun n => Set.Ioi (lower n)) ?_ ?_).isCountablyGenerated
  · intro a ha
    obtain ⟨n, han⟩ := hlowerCofinal a ha
    exact ⟨n, trivial, Set.Ioi_subset_Ioi han.le⟩
  · intro n _
    exact ⟨lower n, hlower n, Set.Subset.rfl⟩

/-- Helper for Exercise 21.4: project a reciprocal perturbation below a unit-interval point. -/
private noncomputable def approachUnitFromBelow (x : unitInterval) (n : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (x - 1 / (n + 1 : ℝ))

/-- Helper for Exercise 21.4: project a reciprocal perturbation above a unit-interval point. -/
private noncomputable def approachUnitFromAbove (x : unitInterval) (n : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (x + 1 / (n + 1 : ℝ))

/-- Helper for Exercise 21.4: the lower reciprocal perturbations are strictly below a positive
unit-interval point. -/
private lemma approachUnitFromBelow_lt {x : unitInterval} (hx : 0 < x) (n : ℕ) :
    approachUnitFromBelow x n < x := by
  -- Both terms selected by the projection's maximum are strictly below `x`.
  change (approachUnitFromBelow x n : ℝ) < (x : ℝ)
  rw [approachUnitFromBelow, Set.coe_projIcc]
  refine max_lt ?_ ?_
  · exact hx
  · exact (min_le_right 1 ((x : ℝ) - 1 / (n + 1 : ℝ))).trans_lt
      (sub_lt_self (x : ℝ) (by positivity))

/-- Helper for Exercise 21.4: the lower reciprocal perturbations are cofinal below every positive
unit-interval point. -/
private lemma exists_lt_approachUnitFromBelow {a x : unitInterval} (hax : a < x) :
    ∃ n, a < approachUnitFromBelow x n := by
  -- Choose the reciprocal smaller than the positive coordinate gap.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hax : 0 < (x : ℝ) - (a : ℝ))
  refine ⟨n, ?_⟩
  change (a : ℝ) < (approachUnitFromBelow x n : ℝ)
  rw [approachUnitFromBelow, Set.coe_projIcc]
  refine lt_max_of_lt_right ?_
  have haxReal : (a : ℝ) < (x : ℝ) := hax
  refine lt_min (haxReal.trans_le x.2.2) ?_
  linarith

/-- Helper for Exercise 21.4: the upper reciprocal perturbations are strictly above a
unit-interval point below one. -/
private lemma lt_approachUnitFromAbove {x : unitInterval} (hx : x < 1) (n : ℕ) :
    x < approachUnitFromAbove x n := by
  -- Both bounds of the projection leave the positive perturbation strictly above `x`.
  change (x : ℝ) < (approachUnitFromAbove x n : ℝ)
  rw [approachUnitFromAbove, Set.coe_projIcc]
  refine lt_max_of_lt_right (lt_min hx ?_)
  exact lt_add_of_pos_right (x : ℝ) (by positivity)

/-- Helper for Exercise 21.4: the upper reciprocal perturbations are coinitial above every
unit-interval point below one. -/
private lemma approachUnitFromAbove_lt_exists {x b : unitInterval} (hxb : x < b) :
    ∃ n, approachUnitFromAbove x n < b := by
  -- Choose the reciprocal smaller than the positive coordinate gap.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hxb : 0 < (b : ℝ) - (x : ℝ))
  refine ⟨n, ?_⟩
  change (approachUnitFromAbove x n : ℝ) < (b : ℝ)
  rw [approachUnitFromAbove, Set.coe_projIcc]
  refine max_lt (x.2.1.trans_lt hxb) ?_
  exact min_lt_of_right_lt (by linarith)

namespace OrderedSquare

/-- Helper for Exercise 21.4: the lexicographic ordered square has the coordinatewise bottom. -/
private noncomputable instance instOrderBot : OrderBot OrderedSquare :=
  inferInstanceAs (OrderBot (Lex (unitInterval × unitInterval)))

/-- Helper for Exercise 21.4: the lexicographic ordered square has the coordinatewise top. -/
private noncomputable instance instOrderTop : OrderTop OrderedSquare :=
  inferInstanceAs (OrderTop (Lex (unitInterval × unitInterval)))

/-- Helper for Exercise 21.4: the first coordinate of the ordered-square bottom is zero. -/
private lemma bot_fst : (⊥ : OrderedSquare).1 = 0 := rfl

/-- Helper for Exercise 21.4: the second coordinate of the ordered-square bottom is zero. -/
private lemma bot_snd : (⊥ : OrderedSquare).2 = 0 := rfl

/-- Helper for Exercise 21.4: the first coordinate of the ordered-square top is one. -/
private lemma top_fst : (⊤ : OrderedSquare).1 = 1 := rfl

/-- Helper for Exercise 21.4: the second coordinate of the ordered-square top is one. -/
private lemma top_snd : (⊤ : OrderedSquare).2 = 1 := rfl

/-- Helper for Exercise 21.4: comparison in the ordered square is lexicographic comparison of
its two coordinates. -/
private lemma lt_iff (p q : OrderedSquare) :
    p < q ↔ p.1 < q.1 ∨ p.1 = q.1 ∧ p.2 < q.2 := by
  -- Unfold only the item-owned carrier wrapper, then use the canonical lexicographic API.
  exact Prod.Lex.lt_iff

/-- Helper for Exercise 21.4: every point of the ordered square has a countably generated
neighborhood filter. -/
private lemma nhds_isCountablyGenerated (p : OrderedSquare) :
    (𝓝 p).IsCountablyGenerated := by
  -- Split at the two fiber endpoints, where lexicographic approach changes coordinates.
  by_cases hy0 : p.2 = 0
  · by_cases hx0 : p.1 = 0
    · have hp : p = ⊥ := by
        exact Prod.ext hx0 hy0
      rw [hp]
      refine isCountablyGenerated_nhds_bot_of_order_sequence
        (fun n => ((0 : unitInterval), approachUnitFromAbove 0 n)) ?_ ?_
      · intro n
        have hbotLt : (⊥ : OrderedSquare).2 < 1 := by
          rw [bot_snd]
          norm_num
        rw [lt_iff]
        exact Or.inr ⟨bot_fst, lt_approachUnitFromAbove hbotLt n⟩
      · intro b hb
        rw [lt_iff] at hb
        rcases hb with hb | ⟨hb₁, hb₂⟩
        · exact ⟨0, (lt_iff _ _).mpr (Or.inl hb)⟩
        · obtain ⟨n, hn⟩ := approachUnitFromAbove_lt_exists hb₂
          exact ⟨n, (lt_iff _ _).mpr (Or.inr ⟨bot_fst.trans hb₁, hn⟩)⟩
    · have hxPos : 0 < p.1 := lt_of_le_of_ne p.1.2.1 (Ne.symm hx0)
      refine isCountablyGenerated_nhds_of_order_sequences p
        (fun n => (approachUnitFromBelow p.1 n, (1 : unitInterval)))
        (fun n => (p.1, approachUnitFromAbove p.2 n)) ?_ ?_ ?_ ?_
      · intro n
        exact (lt_iff _ _).mpr (Or.inl (approachUnitFromBelow_lt hxPos n))
      · intro n
        exact (lt_iff _ _).mpr (Or.inr ⟨rfl,
          lt_approachUnitFromAbove (hy0 ▸ (by norm_num)) n⟩)
      · intro a ha
        rw [lt_iff] at ha
        rcases ha with ha | ⟨ha₁, ha₂⟩
        · obtain ⟨n, hn⟩ := exists_lt_approachUnitFromBelow ha
          exact ⟨n, (lt_iff _ _).mpr (Or.inl hn)⟩
        · exfalso
          rw [hy0] at ha₂
          exact (not_lt_of_ge a.2.2.1) ha₂
      · intro b hb
        rw [lt_iff] at hb
        rcases hb with hb | ⟨hb₁, hb₂⟩
        · exact ⟨0, (lt_iff _ _).mpr (Or.inl hb)⟩
        · obtain ⟨n, hn⟩ := approachUnitFromAbove_lt_exists hb₂
          exact ⟨n, (lt_iff _ _).mpr (Or.inr ⟨hb₁, hn⟩)⟩
  · have hyPos : 0 < p.2 := lt_of_le_of_ne p.2.2.1 (Ne.symm hy0)
    by_cases hy1 : p.2 = 1
    · by_cases hx1 : p.1 = 1
      · have hp : p = ⊤ := by
          exact Prod.ext hx1 hy1
        rw [hp]
        refine isCountablyGenerated_nhds_top_of_order_sequence
          (fun n => ((1 : unitInterval), approachUnitFromBelow 1 n)) ?_ ?_
        · intro n
          have htopPos : 0 < (⊤ : OrderedSquare).2 := by
            rw [top_snd]
            norm_num
          exact (lt_iff _ _).mpr (Or.inr ⟨top_fst.symm,
            approachUnitFromBelow_lt htopPos n⟩)
        · intro a ha
          rw [lt_iff] at ha
          rcases ha with ha | ⟨ha₁, ha₂⟩
          · exact ⟨0, (lt_iff _ _).mpr (Or.inl ha)⟩
          · obtain ⟨n, hn⟩ := exists_lt_approachUnitFromBelow ha₂
            exact ⟨n, (lt_iff _ _).mpr (Or.inr ⟨ha₁.trans top_fst, top_snd ▸ hn⟩)⟩
      · have hxLt : p.1 < 1 := lt_of_le_of_ne p.1.2.2 hx1
        refine isCountablyGenerated_nhds_of_order_sequences p
          (fun n => (p.1, approachUnitFromBelow p.2 n))
          (fun n => (approachUnitFromAbove p.1 n, (0 : unitInterval))) ?_ ?_ ?_ ?_
        · intro n
          exact (lt_iff _ _).mpr (Or.inr ⟨rfl, approachUnitFromBelow_lt hyPos n⟩)
        · intro n
          exact (lt_iff _ _).mpr (Or.inl (lt_approachUnitFromAbove hxLt n))
        · intro a ha
          rw [lt_iff] at ha
          rcases ha with ha | ⟨ha₁, ha₂⟩
          · exact ⟨0, (lt_iff _ _).mpr (Or.inl ha)⟩
          · obtain ⟨n, hn⟩ := exists_lt_approachUnitFromBelow ha₂
            exact ⟨n, (lt_iff _ _).mpr (Or.inr ⟨ha₁, hn⟩)⟩
        · intro b hb
          rw [lt_iff] at hb
          rcases hb with hb | ⟨hb₁, hb₂⟩
          · obtain ⟨n, hn⟩ := approachUnitFromAbove_lt_exists hb
            exact ⟨n, (lt_iff _ _).mpr (Or.inl hn)⟩
          · exfalso
            rw [hy1] at hb₂
            exact (not_lt_of_ge b.2.2.2) hb₂
    · have hyLt : p.2 < 1 := lt_of_le_of_ne p.2.2.2 hy1
      refine isCountablyGenerated_nhds_of_order_sequences p
        (fun n => (p.1, approachUnitFromBelow p.2 n))
        (fun n => (p.1, approachUnitFromAbove p.2 n)) ?_ ?_ ?_ ?_
      · intro n
        exact (lt_iff _ _).mpr (Or.inr ⟨rfl, approachUnitFromBelow_lt hyPos n⟩)
      · intro n
        exact (lt_iff _ _).mpr (Or.inr ⟨rfl, lt_approachUnitFromAbove hyLt n⟩)
      · intro a ha
        rw [lt_iff] at ha
        rcases ha with ha | ⟨ha₁, ha₂⟩
        · exact ⟨0, (lt_iff _ _).mpr (Or.inl ha)⟩
        · obtain ⟨n, hn⟩ := exists_lt_approachUnitFromBelow ha₂
          exact ⟨n, (lt_iff _ _).mpr (Or.inr ⟨ha₁, hn⟩)⟩
      · intro b hb
        rw [lt_iff] at hb
        rcases hb with hb | ⟨hb₁, hb₂⟩
        · exact ⟨0, (lt_iff _ _).mpr (Or.inl hb)⟩
        · obtain ⟨n, hn⟩ := approachUnitFromAbove_lt_exists hb₂
          exact ⟨n, (lt_iff _ _).mpr (Or.inr ⟨hb₁, hn⟩)⟩

/-- The ordered square satisfies the first countability axiom. -/
instance instFirstCountableTopology : FirstCountableTopology OrderedSquare where
  -- The pointwise countable order bases assemble into the first-countability instance.
  nhds_generated_countable := nhds_isCountablyGenerated

end OrderedSquare

/-- Exercise 21.4: The Sorgenfrey line and the ordered square satisfy the first countability
axiom. -/
theorem sorgenfreyLine_and_orderedSquare_firstCountable :
    FirstCountableTopology SorgenfreyLine ∧ FirstCountableTopology OrderedSquare := by
  -- The two explicit neighborhood-basis constructions above provide the required instances.
  constructor
  · exact inferInstance
  · exact inferInstance
