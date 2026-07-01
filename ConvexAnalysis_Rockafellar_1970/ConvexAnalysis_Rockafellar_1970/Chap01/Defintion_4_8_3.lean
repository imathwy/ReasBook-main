import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {E : Type*} [PseudoEMetricSpace E]

open Metric

/-
Source/core/bridge triage:
- `source-facing`: Definition 4.8.3 introduces the distance from a point to a set, with the
  Chapter 1 extended-real convention `inf ∅ = +∞` already fixed in Definition 4.4.6.
- `core/canonical`: mathlib's exact owner with that empty-set behavior is `Metric.infEDist`.
- `bridge/view`: the chapter codomain view `WithTopBot ℝ` (alias `EReal`) is the canonical
  coercion of `Metric.infEDist x C`, and on nonempty sets it agrees with the real-valued recall
  `Metric.infDist x C`.
- Primitive data vs derived API: the primitive inputs are only the set `C` and the point `x`; the
  `Metric.infEDist` owner is primitive, while the chapter `WithTopBot ℝ` bridge lemmas, the `sInf`
  formulas, the empty-set value, and the `Metric.infDist` comparison are derived API.
- Domain-style sampling used here: `Metric.infEDist`, `Metric.infEDist_empty`,
  `Metric.infDist_eq_iInf`, and the coercion `ENNReal.toEReal`.
- Layer target: the main entry and source notation are direct canonical `Metric.infEDist`; chapter
  `WithTopBot ℝ` statements are kept as bridge/view lemmas.
-/

/- Definition 4.8.3: Rockafellar's point-to-set distance is the canonical extended-edistance owner
`Metric.infEDist`. Chapter 1's `WithTopBot ℝ` reading (alias `EReal`) is a downstream coercion
view, while the primitive owner itself lives in `ℝ≥0∞`.
-/
recall Metric.infEDist

/-- Defintion 4.8.3: the point-to-set distance function attached to a set `C`. -/
def distanceToSet (C : Set E) : E → ENNReal :=
  fun x ↦ Metric.infEDist x C

scoped[Rockafellar] notation "d(" x ", " C ")" => distanceToSet C x

open scoped Rockafellar

@[simp] theorem distanceToSet_eq_infEDist (C : Set E) (x : E) :
    d(x, C) = Metric.infEDist x C := rfl

/-- The point-to-set extended distance is the subtype-indexed infimum of pointwise edist values. -/
theorem distanceToSet_eq_iInf (C : Set E) (x : E) :
    d(x, C) = ⨅ y : C, edist x y := by
  -- Unfold the canonical owner and rewrite the two-binder infimum as a subtype infimum.
  rw [distanceToSet, Metric.infEDist, iInf_subtype']

/-- The point-to-set extended distance is the infimum of the edist image of the set. -/
theorem distanceToSet_def (C : Set E) (x : E) :
    d(x, C) = sInf ((fun y ↦ edist x y) '' C) := by
  simpa [sInf_image'] using (distanceToSet_eq_iInf C x)

/-- The chapter distance notation is the subtype-indexed infimum of pointwise edist values,
viewed in `WithTopBot ℝ` (Chapter 1's extended-real codomain). -/
theorem distanceToSet_eq_iInf_withTopBot (C : Set E) (x : E) :
    (d(x, C) : EReal) = ⨅ y : C, (edist x y : EReal) := by
  -- Map the primitive `ENNReal` infimum formula through the canonical coercion to `EReal`.
  rw [distanceToSet_eq_iInf]
  let f : C → ENNReal := fun y ↦ edist x y
  have hmono : Monotone ((↑) : ENNReal → EReal) := EReal.coe_ennreal_strictMono.monotone
  have hmap :
      ((⨅ y, f y : ENNReal) : EReal) = ⨅ y, ((f y : ENNReal) : EReal) :=
    hmono.map_iInf_of_continuousAt continuous_coe_ennreal_ereal.continuousAt rfl
  change ((⨅ y, f y : ENNReal) : EReal) = ⨅ y : C, (edist x y : EReal)
  simpa [f] using hmap

/-- The chapter distance notation is the infimum of the `WithTopBot ℝ`-coerced edist image of the
set. -/
theorem distanceToSet_def_withTopBot (C : Set E) (x : E) :
    (d(x, C) : EReal) = sInf ((fun y ↦ (edist x y : EReal)) '' C) := by
  simpa [sInf_image'] using (distanceToSet_eq_iInf_withTopBot C x)

@[simp] theorem distanceToSet_empty (x : E) :
    d(x, (∅ : Set E)) = ⊤ := by
  -- Unfold the chapter owner and then use the canonical empty-set formula.
  rw [distanceToSet, Metric.infEDist_empty]

end

section

variable {E : Type*} [PseudoMetricSpace E]

open Metric
open scoped Rockafellar

/-- Canonical pseudo-metric bridge: the point-to-set extended distance can be written as the
infimum of the `ENNReal.ofReal`-lifted `dist` values. -/
theorem distanceToSet_eq_iInf_ofReal_dist (C : Set E) (x : E) :
    d(x, C) = ⨅ y : C, ENNReal.ofReal (dist x y) := by
  -- Replace `edist` by `ENNReal.ofReal ∘ dist` pointwise inside the subtype infimum.
  simpa [edist_dist] using (distanceToSet_eq_iInf C x)

/-- Canonical pseudo-metric bridge: the point-to-set extended distance is the infimum of the
`ENNReal.ofReal`-lifted `dist` image of the set. -/
theorem distanceToSet_def_ofReal_dist (C : Set E) (x : E) :
    d(x, C) = sInf ((fun y ↦ ENNReal.ofReal (dist x y)) '' C) := by
  simpa [sInf_image'] using (distanceToSet_eq_iInf_ofReal_dist C x)

/-- `WithTopBot ℝ` bridge theorem: in a pseudo-metric space, the chapter distance can be written
using `dist`. -/
theorem distanceToSet_eq_iInf_dist (C : Set E) (x : E) :
    (d(x, C) : EReal) = ⨅ y : C, (dist x y : EReal) := by
  -- Rewrite each extended distance term through `dist` before taking the infimum.
  rw [distanceToSet_eq_iInf_withTopBot]
  refine iInf_congr fun y : C ↦ ?_
  change (edist x (y : E) : EReal) = (dist x y : EReal)
  simpa [dist_edist] using (EReal.coe_ennreal_toReal (edist_ne_top x (y : E))).symm

/-- `WithTopBot ℝ` bridge theorem: in a pseudo-metric space, the chapter distance is the infimum
of `dist`. -/
theorem distanceToSet_def_dist (C : Set E) (x : E) :
    (d(x, C) : EReal) = sInf ((fun y ↦ (dist x y : EReal)) '' C) := by
  simpa [sInf_image'] using (distanceToSet_eq_iInf_dist C x)

/-- On a nonempty set, the primitive extended owner matches the `ofReal`-lift of the real-valued
minimal-distance owner `Metric.infDist`. -/
theorem distanceToSet_eq_ofReal_infDist {C : Set E} (hC : C.Nonempty) (x : E) :
    d(x, C) = ENNReal.ofReal (infDist x C) := by
  -- Unfold the real-valued owner and use finiteness of `infEDist` on nonempty sets.
  rw [distanceToSet, infDist]
  simpa using (ENNReal.ofReal_toReal (infEDist_ne_top hC)).symm

/-- On a nonempty set, the chapter `WithTopBot ℝ`-valued distance agrees with mathlib's
real-valued minimal-distance owner `Metric.infDist`. -/
theorem distanceToSet_eq_infDist {C : Set E} (hC : C.Nonempty) (x : E) :
    (d(x, C) : EReal) = (infDist x C : EReal) := by
  -- The same finiteness input identifies the `EReal` coercion of `infEDist` with `infDist`.
  rw [distanceToSet, infDist]
  simpa using (EReal.coe_ennreal_toReal (infEDist_ne_top hC)).symm

/-- The finite real branch of the chapter distance notation is the canonical real-valued owner
`Metric.infDist`. -/
@[simp] theorem distanceToSet_toReal_eq_infDist (C : Set E) (x : E) :
    (d(x, C)).toReal = infDist x C := by
  -- This is definitional after unfolding both chapter and mathlib owners.
  simp [distanceToSet, Metric.infDist]

end
