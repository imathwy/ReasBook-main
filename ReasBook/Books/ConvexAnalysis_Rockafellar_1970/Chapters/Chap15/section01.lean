import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_15_1_1 (from Chap03) -/
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

/-! ### Theorem_15_1 (from Chap03) -/
noncomputable section

open scoped ENNReal GaugePolar NNReal RealInnerProductSpace Rockafellar

section

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 15.1 specializes Chapter 15 polarity to gauges: `kᵒ` is a closed
  gauge, `kᵒᵒ = cl(k)`, and for a set gauge `γ(· | C)` the polar is `γ(· | Cᵒ)`.
- `core/canonical`: on the function side, the owner abstraction is
  `convex_function_polar` together with the Chapter 15 owner theorem
  `convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero`;
  on the set side, the owners are `Set.polar`, `egauge ℝ≥0`, and the chapter closure surface
  `cl(·)`.
- `bridge/view`: `gauge_polar` is the positively homogeneous specialization of
  `convex_function_polar` via `convex_function_polar_eq_gauge_polar`, and the set-side gauge is
  rendered through the chapter gauge notation `γ(· | C)` together with only the canonical codomain
  coercion to `EReal`.

Domain-style sampling used here:
- `convex_function_polar_eq_gauge_polar`;
- `isNonnegativeClosedConvexZero_convex_function_polar_of_nonnegative_convex_zero`;
- `convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero`;
- `IsClosedGauge`;
- `Set.polar` and the canonical extended gauge `egauge ℝ≥0`, used through the chapter notation
  `γ(· | C)` and file-local `EReal` coercion bridges `γX`/`γY`;
- the chapter closure notation `cl(·)` from `Text_7_0_4`.

Primitive data vs derived API:
- primitive datum: a gauge `k : E → EReal`, and for the set-side clause a primal set
  `C : Set X` in a paired ambient `(X, Y)`;
- derived function-side API: the closedness package for `gauge_polar k` and the bipolar identity,
  both read through the owner `convex_function_polar`;
- derived set-side API: the identification of `gauge_polar` with the gauge of `Set.polar C`.

Layer target:
- clause (1) stays `source-facing` at the weak inner-product ambient used by the Chapter 15
  function-polar owners;
- clause (3) is raised from a self-dual inner-product model to the pairing layer
  `(X, Y, HasPairingSwap X Y ℝ)`, matching the canonical owner `Set.polar`;
- clause (2) stays `source-facing` in the stronger finite-dimensional normed ambient required by
  the Chapter 15 bipolar owner
  `convex_function_polar_convex_function_polar_eq_lowerSemicontinuousHull_of_nonnegative_convex_zero`;
- all three are refined through the core owner `convex_function_polar` rather than treated as an
  independent second polarity theory.

The source sentence is split into atomic declarations.
-/

-- Proof sketch: first pass to the owner `convex_function_polar k` using positive homogeneity of
-- `k`. The Chapter 15 owner theorem gives the nonnegative/closed/convex/zero package for this
-- polar. Transport those fields back along `convex_function_polar_eq_gauge_polar`; only the
-- positive-homogeneity field remains the genuinely gauge-specific part.
/-- Theorem 15.1 (1): if `k` is a gauge, then its polar `kᵒ` is a closed gauge in the source
terminology. -/
theorem gauge_polar_isClosedGauge
    (k : E → EReal) [IsGauge k] :
    IsClosedGauge kᵒ := by
  sorry

end

section

variable {X : Type*} {Y : Type*}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]
variable [HasPairing X Y ℝ] [HasPairing Y X ℝ] [HasPairingSwap X Y ℝ]

local notation "γX" C => fun x : X ↦ (γ(x | C) : EReal)
local notation "γY" D => fun y : Y ↦ (γ(y | D) : EReal)

-- Proof sketch: specialize the defining majorant inequality for `gauge_polar` to
-- `k = γ C`. For `μ⋆ > 0`, the condition
-- `⟪x, x⋆⟫ ≤ μ⋆ γ(x | C)` for all `x` is equivalent, by positive homogeneity of the gauge, to the
-- condition `μ⋆⁻¹ x⋆ ∈ Cᵒ[ℝ]`. Thus the admissible scalars are exactly the dilates placing
-- `x⋆` in `Cᵒ[ℝ]`, which is the defining infimum formula for `egauge ℝ≥0 (Cᵒ[ℝ])`.
--
-- The convexity hypothesis from the source prose is redundant for this owner-level identity: the
-- comparison uses only the defining majorant inequalities for `gauge_polar`, `egauge ℝ≥0`, and
-- `Set.polar`.
/-- Theorem 15.1 (3): for a set `C` in a paired real ambient `(X, Y)`, the polar of the canonical
extended gauge of `C` is the canonical extended gauge of `Cᵒ[ℝ]`, both viewed in `EReal`. The
source's nonemptiness assumption is redundant for this owner-level identity and is therefore
omitted; specializing to the self-dual inner-product case recovers the textbook `R^n` statement.
-/
theorem gauge_polar_egauge_eq_egauge_polar
    (C : Set X) :
    (γX C)ᵒ = γY (Cᵒ[ℝ]) := sorry

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: use clause (1) to recover that `gauge_polar k` is still a gauge, so
-- `gauge_polar` remains the positively homogeneous specialization of `convex_function_polar` on
-- both the first and second application. The Chapter 15 owner theorem for
-- `convex_function_polar` then gives the bipolar identity directly, specialized to the gauge
-- hypotheses `k ≥ 0`, convexity, and `k 0 = 0`.
/-- Theorem 15.1 (2): in a finite-dimensional real inner-product space, hence in particular on
`R^n`, the bipolar `kᵒᵒ` of a gauge `k` equals the chapter closure `cl(k)`. -/
theorem gauge_polar_polar_eq_lowerSemicontinuousHull
    (k : E → EReal) [IsGauge k] :
    kᵒᵒ = cl(k) := by
  sorry

end

/-! ### Corollary_15_1_2 (from Chap03) -/
noncomputable section

open scoped ENNReal GaugePolar NNReal RealInnerProductSpace Rockafellar

section

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 15.1.2 says that for a closed convex set `C` containing `0`, the
  gauge `γ(· | C)` and the support function `δ^*(· | C)` are closed gauges polar to each other.
- `core/canonical`: the owner abstractions are the set gauge `egauge ℝ≥0`, the support function
  `supportFunction`, the set polar `Set.polar`, the gauge polar `gauge_polar`, and the chapter
  closed-gauge owner class `IsClosedGauge`.
- `bridge/view`: Rockafellar's gauge is rendered by the canonical extended gauge `egauge ℝ≥0`,
  coerced to `EReal`; the corollary is then expressed directly through the existing owner theorems
  for gauge polarity and support functions.

Domain-style sampling used here:
- `egauge_lowerSemicontinuous` from `Corollary_9_7_1`;
- `Function.isConvex_supportFunction` from `Text_5_5_0`;
- `lowerSemicontinuous_supportFunction` from `Text_13_2_3`;
- `IsClosedGauge` from `Text_15_0_24`;
- `gauge_polar_isClosedGauge` and
  `gauge_polar_egauge_eq_egauge_polar` from `Theorem_15_1`;
- `egauge_polar_eq_supportFunction` from `Theorem_14_5`.

Primitive data vs derived API:
- primitive data for the full polar-pair corollary: a set `C : Set E` with `IsClosed C`,
  `Convex ℝ C`, and `(0 : E) ∈ C`;
- primitive data for the support-function closed-gauge clause: only `(0 : E) ∈ C`, since convexity
  and lower semicontinuity of `supportFunction C` are already owner-side facts for arbitrary sets;
- primitive data for the `egauge` closed-gauge clause: `IsClosed C`, `Convex ℝ C`, and
  `C.Nonempty`, since lower semicontinuity is already owner-side and the remaining zero-value gauge
  axiom needs only a witness in `C`;
- owner-side closedness facts already available upstream:
  `egauge_lowerSemicontinuous`, `Function.isConvex_supportFunction`,
  `lowerSemicontinuous_supportFunction`, and the owner class `IsClosedGauge`;
- genuinely new corollary content kept here: the closed-gauge structures on
  `γ C` and `supportFunction C`, together with the two polar identities exchanging them.

Layer target: `bridge/view`, reusing the upstream owner declarations directly and avoiding
parallel local wrappers for closed gauges.

Ambient minimization:
- the support-function clause lives at the same seminormed real inner-product layer as the sampled
  owner declarations `supportFunction`, `Function.isConvex_supportFunction`, and
  `lowerSemicontinuous_supportFunction`;
- the `egauge` closed-gauge clause lives at the weaker real topological-module layer already used
  by `egauge_lowerSemicontinuous` and `egauge_zero_right`;
- only the two polar identities remain in the finite-dimensional real inner-product section,
  because they reuse the Chapter 14–15 polar theorems.
-/

variable {C : Set E}

-- Proof sketch: `Function.isConvex_supportFunction` and `lowerSemicontinuous_supportFunction` are
-- owner facts for every set `C`. If `0 ∈ C`, then `supportFunction C x` is nonnegative because the
-- defining supremum contains the value `⟪x, 0⟫ = 0`, and `supportFunction C 0 = 0` because every
-- inner product with `0` vanishes. These are exactly the remaining gauge clauses.
/-- If a set contains the origin, then its support function is a closed gauge. In the source
corollary the set is also assumed closed and convex, but those two hypotheses are redundant for
this owner-side closed-gauge conclusion. -/
theorem supportFunction_isClosedGauge_of_zero_mem
    (h0C : (0 : E) ∈ C) :
    IsClosedGauge (supportFunction C : E → EReal) := sorry

end

section

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {C : Set E}

local notation "γ" C => fun x ↦ (egauge ℝ≥0 C x : EReal)

-- Proof sketch: lower semicontinuity is exactly the upstream owner theorem
-- `egauge_lowerSemicontinuous`, which uses only closedness and convexity. For the remaining gauge
-- fields, `egauge ℝ≥0 C` is nonnegative by definition, positive homogeneity is built into the
-- owner `egauge`, and `γ C 0 = 0` follows from any witness `x ∈ C` because `0 = 0 • x`.
/-- For a nonempty closed convex set in a real topological module, the canonical extended gauge of
`C`, viewed in `EReal`, is a closed gauge. The source corollary's extra hypothesis `0 ∈ C` is
only needed later for the polar-pair identities, not for this owner-side closed-gauge conclusion.
-/
theorem egauge_isClosedGauge_of_isClosedConvex_nonempty
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty) :
    IsClosedGauge (γ C) := sorry

end

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {C : Set E}

local notation "γ" C => fun x ↦ (egauge ℝ≥0 C x : EReal)

-- Proof sketch: combine Theorem 15.1(3),
-- `gauge_polar_egauge_eq_egauge_polar`, with Theorem 14.5,
-- `egauge_polar_eq_supportFunction`.
/-- Corollary 15.1.2: for a closed convex set `C` containing `0` in a finite-dimensional real
inner-product space, the polar of its gauge `γ(· | C)`, rendered by `γ C`, is the support
function `δ^*(· | C)`, rendered by `supportFunction C`. -/
theorem gauge_polar_egauge_eq_supportFunction_of_isClosedConvexZero
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (h0C : (0 : E) ∈ C)
    :
    (γ C)ᵒ = (supportFunction C : E → EReal) := sorry

-- Proof sketch: apply Theorem 15.1(3) to `Set.polar C`, then rewrite
-- `Set.polar (Set.polar C) = C` and `egauge ℝ≥0 (Set.polar C)` as `supportFunction C` using
-- Theorem 14.5.
/-- Dually, for a closed convex set `C` containing `0` in a finite-dimensional real inner-product
space, the polar of the support function `δ^*(· | C)` is the gauge `γ(· | C)`, rendered by
`γ C`. -/
theorem gauge_polar_supportFunction_eq_egauge_of_isClosedConvexZero
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (h0C : (0 : E) ∈ C)
    :
    (supportFunction C : E → EReal)ᵒ = γ C := sorry

end

end
