import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_24
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_15_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_15_1_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ENNReal GaugePolar NNReal RealInnerProductSpace Rockafellar

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "γ" C => fun x : E ↦ (γ(x | C) : EReal)
local notation:max C "ᵒ" => (Cᵒ[ℝ] : Set E)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 15.1.1 states that the polarity map on closed gauges is a symmetric
  one-to-one correspondence, and that mutually polar closed convex sets containing `0` are exactly
  those whose gauge functions are polar to each other.
- `core/canonical`: the owner theorem for clause (1) is
  `gauge_polar_polar_eq_lowerSemicontinuousHull`, specialized through the owner class
  `IsClosedGauge`; the file refines the derived closed-gauge API into the owner namespace
  `IsClosedGauge`. Clause (2) uses mathlib's canonical `Set.BijOn` together with those owner
  lemmas; for clause (3) the owner declarations are `gauge_polar_egauge_eq_egauge_polar`,
  `gauge_polar_egauge_eq_supportFunction_of_isClosedConvexZero`,
  `supportFunction_isClosedGauge_of_zero_mem`, and
  `isClosed_convex_zero_egauge_eq_iff_eq_unit_sublevel`. The set-side owners are `Set.polar`,
  `egauge ℝ≥0`, `supportFunction`, and `gaugeUnitSublevel`.
- `bridge/view`: the set clause is stated directly as an equivalence between the mutual-polar
  relation on `C` and `D` and the corresponding mutual gauge-polar relation, without introducing a
  wrapper around such sets.

Domain-style sampling used here:
- `IsClosedGauge` from `Text_15_0_24`;
- `gauge_polar_polar_eq_lowerSemicontinuousHull` and
  `gauge_polar_egauge_eq_egauge_polar` from `Theorem_15_1`;
- `Set.isClosed_polar`, `Set.convex_polar`, and `Set.zero_mem_polar` from `Theorem_14_5`;
- `gauge_polar_egauge_eq_supportFunction_of_isClosedConvexZero` and
  `supportFunction_isClosedGauge_of_zero_mem` from `Corollary_15_1_2`;
- `isClosed_convex_zero_egauge_eq_iff_eq_unit_sublevel` from `Text_15_0_4`;
- the ambient owners `Set.polar`, `egauge ℝ≥0`, `supportFunction`, and `gaugeUnitSublevel`.

Primitive data vs derived API:
- primitive inputs: a closed gauge `k : E → EReal`, recorded by `IsClosedGauge k`, or sets
  `C D : Set E`;
- derived function-side statement: the bipolar of a closed gauge is the gauge itself, obtained by
  specializing the owner theorem through lower semicontinuity; the polar closed-gauge structure and
  the resulting bijection of the class of closed gauges with itself are then owner-derived API;
- derived set-side statement: `C` and `D` form a mutual polar pair if and only if `γ C` is a
  closed gauge whose polar is `γ D`, and each set is the canonical unit sublevel set of its own
  gauge; the closed-gauge structure of `γ D` and the reverse polar identity are derived from the
  owner involution instead of being kept as primitive public data.

Layer target:
- clause (1) is `source-facing`, exposed as owner-style companion API in the namespace
  `IsClosedGauge` rather than by repeating the predicate fields in the theorem header;
- clause (2) is `source-facing`, expressed by the owner-side `Set.BijOn` correspondence;
- clause (3) is `bridge/view`, stated directly for `Set.polar`, the canonical set gauges, and the
  canonical unit-sublevel realization of a closed convex zero set.

Ambient-space refinement: the sampled owner theorems already live on arbitrary finite-dimensional
real inner-product spaces, and the corollary uses no coordinate arguments. The refined statements
therefore live on that intrinsic ambient layer rather than the concrete display model `R^n`.
-/

namespace IsClosedGauge

-- Proof sketch: Theorem 15.1 already shows that the polar of any gauge is a closed gauge. The
-- `IsClosedGauge` hypothesis packages exactly the required gauge input.
omit [FiniteDimensional ℝ E] in
/-- The polarity map preserves closed gauges. -/
theorem gauge_polar {k : E → EReal} (hk : IsClosedGauge k) :
    IsClosedGauge kᵒ := by
  letI : IsClosedGauge k := hk
  simpa using gauge_polar_isClosedGauge k

-- Proof sketch: for a closed gauge `k`, Theorem 15.1 identifies `kᵒᵒ` with `cl(k)`;
-- lower semicontinuity identifies that closure with `k` itself. Thus polarity is involutive on
-- closed gauges.
/-- Corollary 15.1.1 (1): for a closed gauge `k` on a finite-dimensional real inner-product
space, hence in particular on `R^n`, the bipolar `kᵒᵒ` is `k`. -/
theorem polar_polar_eq {k : E → EReal} (hk : IsClosedGauge k) :
    kᵒᵒ = k := by
  letI : IsClosedGauge k := hk
  simpa [lowerSemicontinuousHull_eq_self hk.lowerSemicontinuous] using
    gauge_polar_polar_eq_lowerSemicontinuousHull k

omit [FiniteDimensional ℝ E] in
/-- A set `C` is the canonical unit sublevel set of a closed gauge `k` exactly when `C` is closed,
convex, contains `0`, and has gauge `k`. -/
theorem eq_unitSublevel_iff {k : E → EReal} (hk : IsClosedGauge k) (C : Set E) :
    (IsClosed C ∧ Convex ℝ C ∧ (0 : E) ∈ C ∧ (γ C) = k) ↔
      C = gaugeUnitSublevel k := by
  letI : IsClosedGauge k := hk
  exact isClosed_convex_zero_egauge_eq_iff_eq_unit_sublevel k hk.lowerSemicontinuous C

end IsClosedGauge

-- Proof sketch: Theorem 15.1 says that `gauge_polar` sends gauges to closed gauges. The
-- involution theorem above gives `kᵒᵒ = k` on closed gauges, so polarity is its own inverse there
-- and hence defines a bijection of the class with itself.
/-- Corollary 15.1.1 (1), correspondence form: the polarity mapping `k ↦ kᵒ` induces a symmetric
one-to-one correspondence on closed gauges, expressed here as a bijection of that class with
itself. -/
theorem gauge_polar_bijOn_closedGauges :
    Set.BijOn
      (fun k : E → EReal ↦ kᵒ)
      {k : E → EReal | IsClosedGauge k}
      {k : E → EReal | IsClosedGauge k} := by
  have hmaps :
      Set.MapsTo
        (fun k : E → EReal ↦ kᵒ)
        {k : E → EReal | IsClosedGauge k}
        {k : E → EReal | IsClosedGauge k} := by
    intro k hk
    exact hk.gauge_polar
  have hinv :
      Set.InvOn
        (fun k : E → EReal ↦ kᵒ)
        (fun k : E → EReal ↦ kᵒ)
        {k : E → EReal | IsClosedGauge k}
        {k : E → EReal | IsClosedGauge k} := by
    constructor <;> intro k hk <;>
      exact hk.polar_polar_eq
  exact hinv.bijOn hmaps hmaps

-- Proof sketch: if `C` and `D` are mutually polar, Theorem 15.1 (3) rewrites the polar of `γ C`
-- as the gauge of `Cᵒ = D`; since every polar set is closed, convex, and contains `0`,
-- Corollary 15.1.2 makes `γ C` a closed gauge, and Text 15.0.4 then identifies `C` and `D` with
-- the canonical unit sublevel sets of their own gauges. Conversely, if `γ C` is a closed gauge
-- with polar `γ D` and `C`, `D` are these canonical unit sublevel sets, then Theorem 15.1 makes
-- `γ D` a closed gauge and Corollary 15.1.1 (1) recovers `(γ D)ᵒ = γ C`. Text 15.0.4 recovers
-- the closed, convex, origin-containing structure of `C` and `D`, after which Corollary 15.1.2
-- identifies the support functions and hence recovers `Cᵒ = D` and `Dᵒ = C`.
/-- Corollary 15.1.1 (3): two sets are polar to each other if and only if their gauge functions
are related by the owner polarity map, with `γ C` closed, and each set is the canonical unit
sublevel set of its own gauge. By Text 15.0.4, those owner-side conditions exactly encode being a
closed convex set containing `0`; the closed-gauge structure of `γ D` and the reverse polar
identity follow from the owner involution and are therefore omitted from the public interface. -/
theorem closed_convex_origin_sets_polar_iff_gauge_functions_polar
    (C D : Set E) :
    (Cᵒ = D ∧ Dᵒ = C) ↔
      IsClosedGauge (γ C) ∧
        ((γ C)ᵒ = γ D) ∧
        (C = gaugeUnitSublevel (γ C)) ∧
        (D = gaugeUnitSublevel (γ D)) := by
  constructor
  · rintro ⟨hCD, hDC⟩
    have hC_closed : IsClosed C := hDC ▸ Set.isClosed_polar D
    have hC_convex : Convex ℝ C := hDC ▸ Set.convex_polar D
    have h0C : (0 : E) ∈ C := hDC ▸ Set.zero_mem_polar D
    have hD_closed : IsClosed D := hCD ▸ Set.isClosed_polar C
    have hD_convex : Convex ℝ D := hCD ▸ Set.convex_polar C
    have h0D : (0 : E) ∈ D := hCD ▸ Set.zero_mem_polar C
    have hγCD : (γ C)ᵒ = γ D := by
      simpa [hCD] using gauge_polar_egauge_eq_egauge_polar C
    have hclosedGaugeC : IsClosedGauge (γ C) :=
      egauge_isClosedGauge_of_isClosedConvex_nonempty hC_closed hC_convex ⟨0, h0C⟩
    have hclosedGaugeD : IsClosedGauge (γ D) :=
      egauge_isClosedGauge_of_isClosedConvex_nonempty hD_closed hD_convex ⟨0, h0D⟩
    have hC_unit : C = gaugeUnitSublevel (γ C) :=
      (hclosedGaugeC.eq_unitSublevel_iff C).mp ⟨hC_closed, hC_convex, h0C, rfl⟩
    have hD_unit : D = gaugeUnitSublevel (γ D) :=
      (hclosedGaugeD.eq_unitSublevel_iff D).mp ⟨hD_closed, hD_convex, h0D, rfl⟩
    exact ⟨hclosedGaugeC, hγCD, hC_unit, hD_unit⟩
  · rintro ⟨hclosedGaugeC, hγCD, hC_unit, hD_unit⟩
    have hclosedGaugeD : IsClosedGauge (γ D) := by
      simpa [hγCD] using hclosedGaugeC.gauge_polar
    have hγDC : (γ D)ᵒ = γ C := by
      calc
        (γ D)ᵒ = ((γ C)ᵒ)ᵒ := by rw [hγCD]
        _ = γ C := hclosedGaugeC.polar_polar_eq
    have hC_data := (hclosedGaugeC.eq_unitSublevel_iff C).mpr hC_unit
    have hD_data := (hclosedGaugeD.eq_unitSublevel_iff D).mpr hD_unit
    rcases hC_data with ⟨hC_closed, hC_convex, h0C, _⟩
    rcases hD_data with ⟨hD_closed, hD_convex, h0D, _⟩
    have hsupportC : supportFunction C = γ D := by
      calc
        supportFunction C = (γ C)ᵒ := by
          symm
          exact
            gauge_polar_egauge_eq_supportFunction_of_isClosedConvexZero
              hC_closed hC_convex h0C
        _ = γ D := hγCD
    have hsupportD : supportFunction D = γ C := by
      calc
        supportFunction D = (γ D)ᵒ := by
          symm
          exact
            gauge_polar_egauge_eq_supportFunction_of_isClosedConvexZero
              hD_closed hD_convex h0D
        _ = γ C := hγDC
    have hsupportClosedGaugeC : IsClosedGauge (supportFunction C) :=
      supportFunction_isClosedGauge_of_zero_mem h0C
    have hsupportClosedGaugeD : IsClosedGauge (supportFunction D) :=
      supportFunction_isClosedGauge_of_zero_mem h0D
    have hD_polar : D = gaugeUnitSublevel (supportFunction C) :=
      (hsupportClosedGaugeC.eq_unitSublevel_iff D).mp
        ⟨hD_closed, hD_convex, h0D, by simp [hsupportC]⟩
    have hC_polar : C = gaugeUnitSublevel (supportFunction D) :=
      (hsupportClosedGaugeD.eq_unitSublevel_iff C).mp
        ⟨hC_closed, hC_convex, h0C, by simp [hsupportD]⟩
    constructor
    · simpa [gaugeUnitSublevel, Set.polar] using hD_polar.symm
    · simpa [gaugeUnitSublevel, Set.polar] using hC_polar.symm

end
