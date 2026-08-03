module

public import Topology_Munkres_2000.Book.Lemma_10_2.OrdinalSpace

public section

open Ordinal

/-- Helper for Lemma 10.2: `ClosedOmegaOne.omega` is the greatest closed countable ordinal. -/
theorem ClosedOmegaOne.omega_isGreatest :
    IsGreatest (Set.univ : Set ClosedOmegaOne) ClosedOmegaOne.omega := by
  -- Membership in the full carrier is immediate, and every point has the stored bound by `ω₁`.
  refine ⟨Set.mem_univ _, fun a _ ↦ ?_⟩
  exact a.property

/-- Helper for Lemma 10.2: the open-to-closed inclusion lands strictly below `omega`. -/
theorem OpenOmegaOne.toClosed_lt_omega (o : OpenOmegaOne) :
    OpenOmegaOne.toClosed o < ClosedOmegaOne.omega := by
  -- Coercing both endpoints to ordinals reduces the comparison to the defining property of `o`.
  exact o.property

/-- Helper for Lemma 10.2: the strict lower section of `ClosedOmegaOne.omega` is uncountable. -/
theorem ClosedOmegaOne.uncountable_Iio_omega :
    Uncountable (Set.Iio ClosedOmegaOne.omega) := by
  -- Embed every countable ordinal into the strict section below the distinguished endpoint.
  let inclusion : OpenOmegaOne → Set.Iio ClosedOmegaOne.omega :=
    fun o ↦ ⟨OpenOmegaOne.toClosed o, OpenOmegaOne.toClosed_lt_omega o⟩
  have inclusion_injective : Function.Injective inclusion := by
    intro o₁ o₂ equality
    apply Subtype.ext
    exact congrArg (fun x : Set.Iio ClosedOmegaOne.omega ↦ (x.1 : Ordinal)) equality
  exact inclusion_injective.uncountable

/-- Helper for Lemma 10.2: every strict section below a nonterminal closed ordinal is countable. -/
theorem ClosedOmegaOne.countable_Iio_of_ne_omega
    (a : ClosedOmegaOne) (ha : a ≠ ClosedOmegaOne.omega) : Countable (Set.Iio a) := by
  -- A nonterminal point is strictly below `ω₁`, hence its ordinal cardinal is at most `ℵ₀`.
  have value_ne_omegaOne : (a : Ordinal) ≠ ω₁ := by
    intro equality
    apply ha
    apply Subtype.ext
    simpa only [ClosedOmegaOne.coe_omega] using equality
  have value_lt_omegaOne : (a : Ordinal) < ω₁ :=
    lt_of_le_of_ne a.property value_ne_omegaOne
  have value_card_le_aleph0 : (a : Ordinal).card ≤ Cardinal.aleph0 :=
    (CountableOrdinal.mem_iff_card_le_aleph0 (a : Ordinal)).mp value_lt_omegaOne
  -- Transfer the cardinal bound first to the canonical type of the ordinal, then to its lower set.
  have toType_countable : Countable (a : Ordinal).ToType := by
    apply Cardinal.mk_le_aleph0_iff.mp
    simpa only [Cardinal.mk_toType] using value_card_le_aleph0
  have ordinalSection_countable : Countable (Set.Iio (a : Ordinal)) :=
    Ordinal.ToType.mk.injective.countable
  -- Forgetting the outer `ClosedOmegaOne` subtype injects the desired section into that lower set.
  let forgetClosed : Set.Iio a → Set.Iio (a : Ordinal) :=
    fun x ↦ ⟨(x.1 : Ordinal), x.2⟩
  have forgetClosed_injective : Function.Injective forgetClosed := by
    intro x y equality
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Set.Iio (a : Ordinal) ↦ z.1) equality
  exact forgetClosed_injective.countable

/-- Lemma 10.2. The canonical closed first-uncountable ordinal has an uncountable
top section and countable sections below every other point. -/
theorem ClosedOmegaOne.section_spec :
    IsGreatest (Set.univ : Set ClosedOmegaOne) ClosedOmegaOne.omega ∧
      Uncountable (Set.Iio ClosedOmegaOne.omega) ∧
        ∀ a : ClosedOmegaOne, a ≠ ClosedOmegaOne.omega → Countable (Set.Iio a) := by
  -- Assemble the endpoint, uncountable top section, and countable proper-section properties.
  exact ⟨ClosedOmegaOne.omega_isGreatest, ClosedOmegaOne.uncountable_Iio_omega,
    ClosedOmegaOne.countable_Iio_of_ne_omega⟩

/-- Helper for Lemma 10.2: the canonical closed ordinal space supplies the
source-facing existential formulation. -/
theorem existsWellOrderedSetWithUncountableTopSection :
    ∃ (A : Set Ordinal) (Ω : A),
      IsGreatest (Set.univ : Set A) Ω ∧
        Uncountable (Set.Iio Ω) ∧
          ∀ a : A, a ≠ Ω → Countable (Set.Iio a) :=
  ⟨Set.Iic (ω₁ : Ordinal), ClosedOmegaOne.omega, ClosedOmegaOne.section_spec⟩
