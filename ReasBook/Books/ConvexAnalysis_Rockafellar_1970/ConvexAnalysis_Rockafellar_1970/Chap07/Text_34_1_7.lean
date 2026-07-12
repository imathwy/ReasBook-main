import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_2
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_3

noncomputable section

universe u v w

open scoped Rockafellar

namespace Bifunction

open SaddleFunction

section

variable {U : Type u} {V : Type v} {α : Type w}
variable [LT α]
variable {C : Set U} {D : Set V}

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage:

- `source-facing`: Text 34.1.7 identifies the Chapter 34 domains and properness of the lower and
  upper simple extensions of a finite kernel on a product set `C × D`.
- `core/canonical`: the natural owner layer is the Chapter 33/34 simple-extension/domain API.
- `bridge/view`: this item is stated directly on those canonical owners, with no local duplicate
  owner namespace.

Primary mathematical domain:
- saddle-function effective domains and properness for simple extensions.

Domain-style sampling used here:
- endpoint-order data `⊥`, `⊤`, and `<` at the primitive codomain layer;
- product sets `×ˢ` and `Set.Nonempty` from the canonical `Set` API;
- the canonical finite-kernel codomain lift `Bifunction.toWithBotTop` for the concrete bridge;
- the Chapter 33 owners `lowerSimpleExtension` and `upperSimpleExtension`;
- the Chapter 34 owners `dom₁`, `dom₂`, `dom`, and `IsProper`.

Primitive data vs derived API:
- primitive source data: a finite-valued kernel on `C × D` at the endpoint-order layer;
- primitive owner data reused here: the simple extensions and the Chapter 34 domain/properness
  owners;
- concrete bridge data: the canonical codomain lift `toWithBotTop` for `J : C → D → α`;
- derived API in this file: coordinate-domain equalities, effective-domain equalities, and the
  resulting properness consequences.

Layer target: `source-facing`.
-/

section FiniteValuedSimpleExtension

variable {β : Type w}
variable [LT β] [Bot β] [Top β]
variable (K : C → D → β)

-- Proof sketch: unfold `SaddleFunction.dom₁` and `Bifunction.lowerSimpleExtension`. If `u ∈ C`,
-- every second-variable value is either finite by `hK` or `⊤`, hence strictly above `⊥`;
-- if `u ∉ C`, the extension is identically `⊥` in the second variable.
/-- Primitive domain-layer form of Text 34.1.7: if `K` is finite-valued on `C × D`, then the
first-coordinate domain of its lower simple extension is exactly `C`, provided `V` is nonempty. -/
theorem dom₁_lowerSimpleExtension_eq_of_finite [Nonempty V]
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom₁ (lowerSimpleExtension K) = C := by
  intro hK
  ext u
  constructor
  · intro hu
    by_contra huc
    let v : V := Classical.choice ‹Nonempty V›
    have hbot : lowerSimpleExtension K u v = ⊥ := by
      simp [lowerSimpleExtension, huc]
    exact hbot_irrefl (by simpa [hbot] using hu v)
  · intro hu v
    by_cases hv : v ∈ D
    · simpa [lowerSimpleExtension, hu, hv] using (hK ⟨u, hu⟩ ⟨v, hv⟩).1
    · simpa [lowerSimpleExtension, hu, hv] using hbot_top

-- Proof sketch: unfold `SaddleFunction.dom₂` and `Bifunction.lowerSimpleExtension`. For `v ∈ D`,
-- every first-variable value is either finite by `hK` or `⊥`, hence strictly below `⊤`.
-- For `v ∉ D`, choose `u ∈ C` from `hC`; the lower simple extension then takes value `⊤`.
/-- Primitive domain-layer form of Text 34.1.7: if `K` is finite-valued on `C × D` and `C` is
nonempty, then the second-coordinate domain of its lower simple extension is exactly `D`. -/
theorem dom₂_lowerSimpleExtension_eq_of_finite (hC : C.Nonempty)
    (htop_irrefl : ¬ ((⊤ : β) < ⊤)) (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom₂ (lowerSimpleExtension K) = D := by
  intro hK
  ext v
  constructor
  · intro hv
    by_contra hvD
    rcases hC with ⟨u, hu⟩
    have htop : lowerSimpleExtension K u v = ⊤ := by
      simp [lowerSimpleExtension, hu, hvD]
    exact htop_irrefl (by simpa [htop] using hv u)
  · intro hv u
    by_cases hu : u ∈ C
    · simpa [lowerSimpleExtension, hu, hv] using (hK ⟨u, hu⟩ ⟨v, hv⟩).2
    · simpa [lowerSimpleExtension, hu] using hbot_top

-- Proof sketch: combine the two preceding coordinate-domain formulas with the definition
-- `SaddleFunction.dom K = SaddleFunction.dom₁ K ×ˢ SaddleFunction.dom₂ K`.
/-- Primitive domain-layer form of Text 34.1.7 for the lower simple extension:
if `K` is finite-valued on `C × D` and `C` is nonempty, then its effective domain is `C ×ˢ D`. -/
theorem dom_lowerSimpleExtension_eq_of_finite (hC : C.Nonempty)
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (htop_irrefl : ¬ ((⊤ : β) < ⊤))
    (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom (lowerSimpleExtension K) = C ×ˢ D := by
  intro hK
  ext p
  constructor
  · intro hp
    rcases mem_dom.mp hp with ⟨hu, hv⟩
    haveI : Nonempty V := ⟨p.2⟩
    refine ⟨?_, ?_⟩
    · simpa [dom₁_lowerSimpleExtension_eq_of_finite (K := K) hbot_irrefl hbot_top hK] using hu
    · simpa [dom₂_lowerSimpleExtension_eq_of_finite (K := K) hC htop_irrefl hbot_top hK] using hv
  · rintro ⟨hu, hv⟩
    refine mem_dom.mpr ?_
    constructor
    · haveI : Nonempty V := ⟨p.2⟩
      have hp₁ : p.1 ∈ dom₁ (lowerSimpleExtension K) := by
        simpa [dom₁_lowerSimpleExtension_eq_of_finite (K := K) hbot_irrefl hbot_top hK] using hu
      exact hp₁
    · simpa [dom₂_lowerSimpleExtension_eq_of_finite (K := K) hC htop_irrefl hbot_top hK] using hv

-- Proof sketch: use the preceding effective-domain identity and the hypotheses that both factors
-- are nonempty to obtain a point of `C ×ˢ D`, hence of the effective domain.
/-- Primitive properness-layer form of Text 34.1.7 for the lower simple extension:
if `K` is finite-valued on `C × D` and both factors are nonempty, then
`lowerSimpleExtension K` is proper. -/
theorem isProper_lowerSimpleExtension_of_finite (hC : C.Nonempty) (hD : D.Nonempty)
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (htop_irrefl : ¬ ((⊤ : β) < ⊤))
    (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    IsProper (lowerSimpleExtension K) := by
  intro hK
  letI : Nonempty V := ⟨Classical.choose hD⟩
  refine (isProper_iff _).2 ?_
  refine ⟨?_, ?_⟩
  · simpa [dom₁_lowerSimpleExtension_eq_of_finite (K := K) hbot_irrefl hbot_top hK] using hC
  · simpa [dom₂_lowerSimpleExtension_eq_of_finite (K := K) hC htop_irrefl hbot_top hK] using hD

-- Proof sketch: unfold `SaddleFunction.dom₁` and `Bifunction.upperSimpleExtension`. If `u ∈ C`,
-- each second-variable value is either finite by `hK` or `⊤`, hence strictly above `⊥`. If
-- `u ∉ C`, choose `v ∈ D` from `hD`; the upper simple extension takes value `⊥` at `(u, v)`.
/-- Primitive domain-layer form of Text 34.1.7: if `K` is finite-valued on `C × D` and `D` is
nonempty, then the first-coordinate domain of its upper simple extension is exactly `C`. -/
theorem dom₁_upperSimpleExtension_eq_of_finite (hD : D.Nonempty)
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom₁ (upperSimpleExtension K) = C := by
  intro hK
  ext u
  constructor
  · intro hu
    by_contra huc
    rcases hD with ⟨v, hv⟩
    have hbot : upperSimpleExtension K u v = ⊥ := by
      simp [upperSimpleExtension, huc, hv]
    exact hbot_irrefl (by simpa [hbot] using hu v)
  · intro hu v
    by_cases hv : v ∈ D
    · simpa [upperSimpleExtension, hu, hv] using (hK ⟨u, hu⟩ ⟨v, hv⟩).1
    · simpa [upperSimpleExtension, hv] using hbot_top

-- Proof sketch: unfold `SaddleFunction.dom₂` and `Bifunction.upperSimpleExtension`. If `v ∈ D`,
-- every first-variable value is either finite by `hK` or `⊥`, so it is strictly below `⊤`;
-- if `v ∉ D`, the extension is identically `⊤` in the first variable.
/-- Primitive domain-layer form of Text 34.1.7: if `K` is finite-valued on `C × D`, then the
second-coordinate domain of its upper simple extension is exactly `D`, provided `U` is nonempty. -/
theorem dom₂_upperSimpleExtension_eq_of_finite [Nonempty U]
    (htop_irrefl : ¬ ((⊤ : β) < ⊤)) (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom₂ (upperSimpleExtension K) = D := by
  intro hK
  ext v
  constructor
  · intro hv
    by_contra hvD
    let u : U := Classical.choice ‹Nonempty U›
    have htop : upperSimpleExtension K u v = ⊤ := by
      simp [upperSimpleExtension, hvD]
    exact htop_irrefl (by simpa [htop] using hv u)
  · intro hv u
    by_cases hu : u ∈ C
    · simpa [upperSimpleExtension, hu, hv] using (hK ⟨u, hu⟩ ⟨v, hv⟩).2
    · simpa [upperSimpleExtension, hu, hv] using hbot_top

-- Proof sketch: combine the two preceding upper-extension coordinate-domain formulas with the
-- product definition of `SaddleFunction.dom`.
/-- Primitive domain-layer form of Text 34.1.7 for the upper simple extension:
if `K` is finite-valued on `C × D` and `D` is nonempty, then its effective domain is `C ×ˢ D`. -/
theorem dom_upperSimpleExtension_eq_of_finite (hD : D.Nonempty)
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (htop_irrefl : ¬ ((⊤ : β) < ⊤))
    (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    dom (upperSimpleExtension K) = C ×ˢ D := by
  intro hK
  ext p
  constructor
  · intro hp
    rcases mem_dom.mp hp with ⟨hu, hv⟩
    haveI : Nonempty U := ⟨p.1⟩
    refine ⟨?_, ?_⟩
    · simpa [dom₁_upperSimpleExtension_eq_of_finite (K := K) hD hbot_irrefl hbot_top hK] using hu
    · simpa [dom₂_upperSimpleExtension_eq_of_finite (K := K) htop_irrefl hbot_top hK] using hv
  · rintro ⟨hu, hv⟩
    refine mem_dom.mpr ?_
    constructor
    · simpa [dom₁_upperSimpleExtension_eq_of_finite (K := K) hD hbot_irrefl hbot_top hK] using hu
    · haveI : Nonempty U := ⟨p.1⟩
      have hp₂ : p.2 ∈ dom₂ (upperSimpleExtension K) := by
        simpa [dom₂_upperSimpleExtension_eq_of_finite (K := K) htop_irrefl hbot_top hK] using hv
      exact hp₂

-- Proof sketch: use the preceding effective-domain identity and the nonemptiness of both factors
-- to produce a point of `C ×ˢ D`, hence a point of the effective domain.
/-- Primitive properness-layer form of Text 34.1.7 for the upper simple extension:
if `K` is finite-valued on `C × D` and both factors are nonempty, then
`upperSimpleExtension K` is proper. -/
theorem isProper_upperSimpleExtension_of_finite (hC : C.Nonempty) (hD : D.Nonempty)
    (hbot_irrefl : ¬ ((⊥ : β) < ⊥)) (htop_irrefl : ¬ ((⊤ : β) < ⊤))
    (hbot_top : (⊥ : β) < ⊤) :
    (hK : ∀ u : C, ∀ v : D, (⊥ : β) < K u v ∧ K u v < ⊤) →
    IsProper (upperSimpleExtension K) := by
  intro hK
  letI : Nonempty U := ⟨Classical.choose hC⟩
  refine (isProper_iff _).2 ?_
  refine ⟨?_, ?_⟩
  · simpa [dom₁_upperSimpleExtension_eq_of_finite (K := K) hD hbot_irrefl hbot_top hK] using hC
  · simpa [dom₂_upperSimpleExtension_eq_of_finite (K := K) htop_irrefl hbot_top hK] using hD

end FiniteValuedSimpleExtension

private theorem withBotTop_not_bot_lt_bot :
    ¬ ((⊥ : WithBotTop α) < ⊥) := by
  intro h
  cases h

private theorem withBotTop_not_top_lt_top :
    ¬ ((⊤ : WithBotTop α) < ⊤) := by
  intro h
  cases h with
  | coe_lt_coe h' =>
      cases h'

private theorem withBotTop_bot_lt_top :
    (⊥ : WithBotTop α) < ⊤ :=
  WithBot.bot_lt_coe (⊤ : WithTop α)

private theorem toWithBotTop_isFinite (J : C → D → α) :
    ∀ u : C, ∀ v : D,
      (⊥ : WithBotTop α) < toWithBotTop J u v ∧ toWithBotTop J u v < ⊤ := by
  intro u v
  constructor
  · change (⊥ : WithBotTop α) < ((J u v : α) : WithBotTop α)
    exact WithBot.bot_lt_coe ((J u v : α) : WithTop α)
  · simpa [toWithBotTop_apply] using
      (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top (J u v)))

section LowerSimpleExtension

variable (J : C → D → α)

/-- Text 34.1.7: the first-coordinate domain of the lower simple extension of a finite kernel
`J : C → D → α` is exactly `C`, provided the second ambient variable type is nonempty. -/
theorem dom₁_lowerSimpleExtension_eq [Nonempty V] :
    dom₁ (lowerSimpleExtension (toWithBotTop J)) = C := by
  simpa using
    (dom₁_lowerSimpleExtension_eq_of_finite
      (K := toWithBotTop J) withBotTop_not_bot_lt_bot withBotTop_bot_lt_top
      (toWithBotTop_isFinite J))

/-- If `C` is nonempty, then the second-coordinate domain of the lower simple extension of `J`
is exactly `D`. -/
theorem dom₂_lowerSimpleExtension_eq (hC : C.Nonempty) :
    dom₂ (lowerSimpleExtension (toWithBotTop J)) = D := by
  simpa using
    (dom₂_lowerSimpleExtension_eq_of_finite
      (K := toWithBotTop J) hC withBotTop_not_top_lt_top withBotTop_bot_lt_top
      (toWithBotTop_isFinite J))

/-- If `C` is nonempty, the effective domain of the lower simple extension of `J` is the product
set `C ×ˢ D`. -/
theorem dom_lowerSimpleExtension_eq (hC : C.Nonempty) :
    dom (lowerSimpleExtension (toWithBotTop J)) = C ×ˢ D := by
  simpa using
    (dom_lowerSimpleExtension_eq_of_finite
      (K := toWithBotTop J) hC withBotTop_not_bot_lt_bot withBotTop_not_top_lt_top
      withBotTop_bot_lt_top (toWithBotTop_isFinite J))

/-- If `C` and `D` are nonempty, the lower simple extension of `J` is proper. -/
theorem isProper_lowerSimpleExtension (hC : C.Nonempty) (hD : D.Nonempty) :
    IsProper (lowerSimpleExtension (toWithBotTop J)) := by
  simpa using
    (isProper_lowerSimpleExtension_of_finite
      (K := toWithBotTop J) hC hD withBotTop_not_bot_lt_bot withBotTop_not_top_lt_top
      withBotTop_bot_lt_top (toWithBotTop_isFinite J))

end LowerSimpleExtension

section UpperSimpleExtension

variable (J : C → D → α)

/-- If `D` is nonempty, then the first-coordinate domain of the upper simple extension of `J` is
exactly `C`. -/
theorem dom₁_upperSimpleExtension_eq (hD : D.Nonempty) :
    dom₁ (upperSimpleExtension (toWithBotTop J)) = C := by
  simpa using
    (dom₁_upperSimpleExtension_eq_of_finite
      (K := toWithBotTop J) hD withBotTop_not_bot_lt_bot withBotTop_bot_lt_top
      (toWithBotTop_isFinite J))

/-- The second-coordinate domain of the upper simple extension of a finite kernel `J : C → D → α`
is exactly `D`, provided the first ambient variable type is nonempty. -/
theorem dom₂_upperSimpleExtension_eq [Nonempty U] :
    dom₂ (upperSimpleExtension (toWithBotTop J)) = D := by
  simpa using
    (dom₂_upperSimpleExtension_eq_of_finite
      (K := toWithBotTop J) withBotTop_not_top_lt_top withBotTop_bot_lt_top
      (toWithBotTop_isFinite J))

/-- If `D` is nonempty, the effective domain of the upper simple extension of `J` is the product
set `C ×ˢ D`. -/
theorem dom_upperSimpleExtension_eq (hD : D.Nonempty) :
    dom (upperSimpleExtension (toWithBotTop J)) = C ×ˢ D := by
  simpa using
    (dom_upperSimpleExtension_eq_of_finite
      (K := toWithBotTop J) hD withBotTop_not_bot_lt_bot withBotTop_not_top_lt_top
      withBotTop_bot_lt_top (toWithBotTop_isFinite J))

/-- If `C` and `D` are nonempty, the upper simple extension of `J` is proper. -/
theorem isProper_upperSimpleExtension (hC : C.Nonempty) (hD : D.Nonempty) :
    IsProper (upperSimpleExtension (toWithBotTop J)) := by
  simpa using
    (isProper_upperSimpleExtension_of_finite
      (K := toWithBotTop J) hC hD withBotTop_not_bot_lt_bot withBotTop_not_top_lt_top
      withBotTop_bot_lt_top (toWithBotTop_isFinite J))

end UpperSimpleExtension

end

end Bifunction
