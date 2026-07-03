import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_5_4_3 (from Chap01) -/
noncomputable section

section

open scoped Rockafellar
open scoped Pointwise
open Function

variable {E : Type*}
variable {𝕜 : Type*}
variable {α : Type*}

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)
attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.3 computes the right scalar multiple from Text 5.4.2 in the
  positive-scalar case and at zero.
- `core/canonical`: the owner abstraction is the scaled-epigraph vertical-infimum operation
  `rightScalarMul` already introduced in `Text_5_4_2`, together with the chapter indicator owner
  `indicator`, used on the source-facing theorem surface through the notation
  `δ(· | ({0} : Set E))`.
- `bridge/view`: for a positive scalar, the scaled-epigraph vertical infimum simplifies to the
  explicit rescaling formula `x ↦ a * f (a⁻¹ • x)`; at zero, the scaled epigraph collapses to the
  origin indicator `δ(· | ({0} : Set E))` unless `f` is identically `⊤`, in which case it stays
  identically `⊤`.
- Primitive data vs derived API: `rightScalarMul` is primitive; the positive-scalar formula and
  the zero-scalar identification with the canonical origin indicator are derived API, and the
  pointwise evaluation theorem is recorded directly through that same indicator notation.
- Redundant-source-assumption elimination: the source assumes `f` is convex, but these
  identification formulas depend only on the scaled-epigraph construction itself, not on
  convexity.

Domain-style sampling used here:
- `rightScalarMul`;
- `rightScalarMul_eq_sInf`;
- `epi`;
- `Function.verticalInfimum` from `Theorem_5_3`;
- `indicator` and the notation `δ(· | C)` from `Defintion_4_8_1`.
- Ambient minimization: the file is expressed over a general ordered scalar `𝕜`; no theorem
  surface is pinned to `ℝ`.
-/

section

variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [MulAction 𝕜 E]

/-- Text 5.4.3 (1): for a positive scalar `a`, the right scalar multiple is given pointwise by
`x ↦ a * f (a⁻¹ • x)`. -/
theorem rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos
    (f : E → WithBotTop 𝕜) {a : 𝕜} (ha : 0 < a) (x : E) :
    ((⟨a, ha.le⟩ : 𝕜≥0) •ʳ f) x = a * f (a⁻¹ • x) := by
  have hscaled :
      ((a : 𝕜) • epi f : Set (E × 𝕜)) =
        epi (fun y ↦ (a : WithBotTop 𝕜) * f (a⁻¹ • y)) := by
    ext p
    rcases p with ⟨y, μ⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne']
    rw [mem_epi_iff, mem_epi_iff]
    change f (a⁻¹ • y) ≤ a⁻¹ * μ ↔ (a : WithBotTop 𝕜) * f (a⁻¹ • y) ≤ μ
    set z := f (a⁻¹ • y)
    cases z using WithBotTop.rec with
    | bot =>
        rw [WithBotTop.coe_mul_bot_of_pos ha]
        simp
    | top =>
        have hlhs : ¬ ⊤ ≤ (WithBotTop.coe a)⁻¹ * WithBotTop.coe μ := by
          intro h
          have : (WithBotTop.coe a)⁻¹ * WithBotTop.coe μ = (⊤ : WithBotTop 𝕜) :=
            top_le_iff.mp h
          have hEq : (WithBotTop.coe a)⁻¹ * WithBotTop.coe μ =
              (((a⁻¹ * μ : 𝕜)) : WithBotTop 𝕜) := by
            conv_lhs => rw [← WithBotTop.coe_inv a, ← WithBotTop.coe_mul]
          rw [hEq] at this
          exact (WithBotTop.coe_ne_top (a⁻¹ * μ)) this
        constructor
        · intro h
          exact (hlhs h).elim
        · intro h
          rw [WithBotTop.coe_mul_top_of_pos ha] at h
          simp at h
    | coe r =>
        constructor
        · intro h
          rw [← WithBotTop.coe_mul] at h
          have hmulinv : r ≤ a⁻¹ * μ := WithBotTop.coe_le_coe.mp h
          have hdiv : r ≤ μ / a := by
            simpa [div_eq_mul_inv, mul_comm] using hmulinv
          exact WithBotTop.coe_le_coe.mpr <|
            by simpa [mul_comm] using (le_div_iff₀' ha).mp hdiv
        · intro h
          rw [← WithBotTop.coe_mul] at h
          have hmul : a * r ≤ μ := WithBotTop.coe_le_coe.mp h
          have hdiv : r ≤ μ / a := (le_div_iff₀' ha).mpr <|
            by simpa [mul_comm] using hmul
          have hmulinv : r ≤ a⁻¹ * μ := by
            simpa [div_eq_mul_inv, mul_comm] using hdiv
          exact (WithBotTop.coe_le_coe.mpr hmulinv :
            (r : WithBotTop 𝕜) ≤ ((a⁻¹ * μ : 𝕜) : WithBotTop 𝕜))
  calc
    ((⟨a, ha.le⟩ : 𝕜≥0) •ʳ f) x = Function.verticalInfimum (((a : 𝕜) • epi f) : Set (E × 𝕜)) x :=
      rfl
    _ = Function.verticalInfimum (epi (fun y ↦ (a : WithBotTop 𝕜) * f (a⁻¹ • y))) x := by
      rw [hscaled]
    _ = a * f (a⁻¹ • x) := by
      simp

end

section

variable [Monoid 𝕜] [Preorder 𝕜] [Zero 𝕜] [ZeroLEOneClass 𝕜]
variable [ConditionallyCompleteLattice α] [NoBotOrder α]
variable [MulAction 𝕜 E] [MulAction 𝕜 α]

/-- The unit right scalar multiple recovers the original function. -/
@[simp] theorem rightScalarMul_one (f : E → WithBotTop α) :
    ((⟨1, zero_le_one⟩ : 𝕜≥0) •ʳ f) = f := by
  have hs : (1 : 𝕜) • (epi[Set.univ] f : Set (E × α)) = epi[Set.univ] f := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [mem_epi_iff] at hq ⊢
      simpa using hq
    · intro hp
      refine ⟨p, hp, ?_⟩
      ext <;> simp
  change Function.verticalInfimum ((1 : 𝕜) • (epi[Set.univ] f : Set (E × α))) = f
  rw [hs]
  exact Function.verticalInfimum_epi f

end

section

variable [Preorder 𝕜] [Zero 𝕜]
variable [ConditionallyCompleteLattice α]
variable [Zero E] [Zero α]
variable [SMulWithZero 𝕜 E] [SMulWithZero 𝕜 α]

/-- Canonical epigraph-owner form of Text 5.4.3 (2): if `epi f` is nonempty, then `0 •ʳ f`
is the canonical indicator of the origin. -/
theorem rightScalarMul_zero_eq_indicator_zero_of_epi_nonempty
    (f : E → WithBotTop α) (hepi : (epi f).Nonempty) :
    ((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) = (δ(· | ({0} : Set E))) := by
  have hzeroepi : ((0 : 𝕜) • epi f : Set (E × α)) = 0 := Set.zero_smul_set hepi
  ext x
  by_cases hx : x = 0
  · subst hx
    rw [Function.rightScalarMul_eq_sInf]
    simp [Function.verticalHeights, Function.verticalSection, hzeroepi]
  · rw [Function.rightScalarMul_eq_sInf]
    simp [Function.verticalHeights, Function.verticalSection, hzeroepi, hx]

/-- Text 5.4.3 (2): if `f` is not identically `⊤`, then `0 •ʳ f` is the
canonical indicator of the origin. -/
theorem rightScalarMul_zero_eq_indicator_zero_of_ne_top
    (f : E → WithBotTop α) (hf : f ≠ ⊤) :
    ((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) = (δ(· | ({0} : Set E))) := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ ⊤ := by
    by_contra h
    apply hf
    funext y
    exact by simpa using not_exists.mp h y
  have hepi : (epi f).Nonempty := by
    by_cases hbot : f y = ⊥
    · refine ⟨(y, 0), ?_⟩
      simp [hbot]
    · lift f y to α using ⟨hy, hbot⟩ with a ha
      refine ⟨(y, a), ?_⟩
      simp [ha]
  exact rightScalarMul_zero_eq_indicator_zero_of_epi_nonempty f hepi

/-- Pointwise canonical epigraph-owner form of Text 5.4.3 (2). -/
theorem rightScalarMul_zero_apply_eq_origin_indicator_of_epi_nonempty
    (f : E → WithBotTop α) (hepi : (epi f).Nonempty) (x : E) :
    (((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) x) = δ(x | ({0} : Set E)) := by
  simpa using congrFun (rightScalarMul_zero_eq_indicator_zero_of_epi_nonempty f hepi) x

/-- Pointwise form of Text 5.4.3 (2): if `f` is not identically `⊤`, then the zero right scalar
multiple is the canonical origin indicator. -/
theorem rightScalarMul_zero_apply_eq_origin_indicator_of_ne_top
    (f : E → WithBotTop α) (hf : f ≠ ⊤) (x : E) :
    (((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) x) = δ(x | ({0} : Set E)) := by
  simpa using congrFun (rightScalarMul_zero_eq_indicator_zero_of_ne_top f hf) x

end

section

variable [Preorder 𝕜] [Zero 𝕜]
variable [ConditionallyCompleteLattice α]
variable [SMul 𝕜 E] [SMul 𝕜 α]

/-- Canonical epigraph-owner form of Text 5.4.3 (3): if `epi f = ∅`, then `0 •ʳ f = f`. -/
theorem rightScalarMul_zero_eq_self_of_epi_eq_empty
    (f : E → WithBotTop α) (hepi : (epi f : Set (E × α)) = ∅) :
    ((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) = f := by
  ext x
  rw [Function.rightScalarMul_eq_sInf, hepi, Set.smul_set_empty]
  have htop : f x = ⊤ := by
    by_contra hxtop
    by_cases hbot : f x = ⊥
    · let a0 : α := sInf (Set.univ : Set α)
      have hmem : (x, a0) ∈ (epi f : Set (E × α)) := by
        simp [hbot]
      simp [hepi] at hmem
    · lift f x to α using ⟨hxtop, hbot⟩ with a ha
      have hmem : (x, a) ∈ (epi f : Set (E × α)) := by
        simp [ha]
      simp [hepi] at hmem
  rw [htop]
  simp [Function.verticalHeights, Function.verticalSection]

/-- Text 5.4.3 (3): if `f` is identically `⊤`, then `0 •ʳ f = f`. -/
theorem rightScalarMul_zero_eq_self_of_eq_top
    (f : E → WithBotTop α) (hf : f = ⊤) :
    ((⟨0, le_rfl⟩ : 𝕜≥0) •ʳ f) = f := by
  have hepi : (epi f : Set (E × α)) = ∅ := by
    rw [hf]
    ext p
    rcases p with ⟨x, a⟩
    simp
  simpa using rightScalarMul_zero_eq_self_of_epi_eq_empty f hepi

end

end

/-! ### Text_5_4_4 (from Chap01) -/
/-
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.4 recalls the notion of a positively homogeneous function
  as a function-side owner.
- `core/canonical`: the owner abstraction is the generic chapter predicate
  `Function.PositivelyHomogeneous : (E → F) → Prop` from `Definition_4_8`, together with the
  intrinsic positive-scalar owner `Function.PositiveScalars` (notation `𝕜⁺`).
- `bridge/view`: the intrinsic positive-scalar view and the explicit pointwise scaling bridge are
  `Function.PositivelyHomogeneous.iff_forall_pos`,
  `Function.PositivelyHomogeneous.iff_forall_pos_scalar`,
  `Function.PositivelyHomogeneous.map_smul_pos`, and
  `Function.PositivelyHomogeneous.map_smul`.
- Primitive data vs derived API: the owner predicate is primitive; the intrinsic and textbook
  scalar-binder equivalences and the pointwise scaling theorems are the derived API.
- Domain-style sampling used here: `Function.PositivelyHomogeneous`,
  `Function.PositiveScalars`,
  `Function.PositivelyHomogeneous.iff_forall_pos`,
  `Function.PositivelyHomogeneous.iff_forall_pos_scalar`,
  `Function.PositivelyHomogeneous.map_smul_pos`, and
  `Function.PositivelyHomogeneous.map_smul`.
- Layer target: `core/canonical`; this file recalls the codomain-agnostic owner and its intrinsic
  bridge API rather than introducing a codomain-specialized wrapper surface.
-/

namespace Function

/- Text 5.4.4: the notion of a positively homogeneous function is the chapter owner
`PositivelyHomogeneous`. -/
recall PositivelyHomogeneous

/- Intrinsic owner for positive scalars used in positive-homogeneity surfaces. -/
recall PositiveScalars

/- Coercion bridge from the intrinsic positive-scalar action to ambient scalar action. -/
recall positiveScalars_smul_eq_coe_smul

/- Intrinsic positive-scalar view of the owner, using the positive subtype. -/
recall PositivelyHomogeneous.iff_forall_pos

/- Textbook scalar-plus-positivity binder form, as a bridge from the intrinsic owner. -/
recall PositivelyHomogeneous.iff_forall_pos_scalar

/- Pointwise scaling bridges for positive scalars, in subtype and textbook binder forms. -/
recall PositivelyHomogeneous.map_smul_pos
recall PositivelyHomogeneous.map_smul

end Function

/-! ### Theorem_5_4 (from Chap01) -/
noncomputable section

universe u v w

section

variable {E : Type u} {ι : Type v} {𝕜 : Type w}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [DistribMulAction 𝕜 E]

/-!
Source/core/bridge triage for this item.

- Primary domain: finite infimal convolution of extended-real-valued convex functions.
- `source-facing`: Theorem 5.4 states that the infimum of `∑ i, f i (x i)` over all finite
  decompositions `∑ i, x i = x` is convex. In the textbook this is stated for proper convex
  functions, but properness is redundant for the owner-level convexity statement.
- `core/canonical`: the owner abstractions are `finsetInfimalConvolution` /
  `finiteInfimalConvolution` from `Text_5_4_1`, the
  epigraph-based convexity predicate `Function.IsConvex` from `Theorem_4_2`, and the chapter owner
  theorem `Function.isConvex_verticalInfimum` from `Theorem_5_3`.
- `bridge/view`: the proof factors through the support set
  `finsetInfimalConvolutionSupport s f` (or its `Finset.univ` specialization
  `finiteInfimalConvolutionSupport f`) and the owner theorem
  `Function.isConvex_verticalInfimum`.
- Primitive data vs derived API: the family `f` and finite index set `s` are primitive; the owner
  `finsetInfimalConvolution s f` is the primitive finite-operational construction and
  `finiteInfimalConvolution f` is its `Finset.univ` specialization; convexity is derived API.
- Ambient minimization: both the support-set convexity bridge and the owner theorem
  `Function.isConvex_verticalInfimum` live on the ordered-ring layer with only a distributive
  scalar action on `E`, so this file keeps `[Ring 𝕜]` (not a field),
  `[DistribMulAction 𝕜 E]` (not a full `Module`), and does not add a dense-order hypothesis.
- Domain-style sampling used here:
  `finsetInfimalConvolution`,
  `finiteInfimalConvolution`,
  `Function.IsConvex`,
  `Function.isConvex_verticalInfimum`.
- Layer targets:
  - `source-facing`: `Function.isConvex_finsetInfimalConvolution` is the primitive finite
    operational convexity theorem, and `Function.isConvex_finiteInfimalConvolution` is its
    `Finset.univ` specialization;
  - `bridge/view`: the proof factors through the canonical owner theorem
    `Function.isConvex_verticalInfimum` rather than re-exposing a parallel low-level convexity
    construction.
-/

namespace Function

/-- Theorem 5.4 at the primitive finite-operational owner layer: if each summand is convex, then
the infimal convolution over a finite index set `s` is convex. Only convexity of indices in `s`
is required. -/
theorem isConvex_finsetInfimalConvolution (s : Finset ι)
    (f : ι → E → WithTopBot 𝕜)
    (hf_convex : ∀ i ∈ s, (f i).IsConvex 𝕜) :
    (finsetInfimalConvolution s f).IsConvex 𝕜 := by
  rw [finsetInfimalConvolution_eq_verticalInfimum]
  exact Function.isConvex_verticalInfimum
    (convex_finsetInfimalConvolutionSupport (s := s) f
      (fun i hi ↦ by simpa [Function.IsConvex] using hf_convex i hi))

section FintypeFamily

variable [Fintype ι]

/-- Theorem 5.4 in `Fintype` form: if each summand is convex, then the finite-family infimal
convolution is convex. This is the `Finset.univ` specialization of
`Function.isConvex_finsetInfimalConvolution`. -/
theorem isConvex_finiteInfimalConvolution
    (f : ι → E → WithTopBot 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜) :
    (finiteInfimalConvolution f).IsConvex 𝕜 := by
  simpa [finiteInfimalConvolution] using
    (isConvex_finsetInfimalConvolution (s := (Finset.univ : Finset ι)) f
      (fun i _ ↦ hf_convex i))

end FintypeFamily

end Function

namespace Function.IsConvex

/-- The binary infimal convolution of two convex functions is convex. This is the `Fin 2`
specialization of `Function.isConvex_finiteInfimalConvolution`, exposed on the source-facing pair
surface `![f, g]` and then at the owner `f □ g`. -/
theorem infimal_convolution {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hg_convex : g.IsConvex 𝕜) :
    (f □ g).IsConvex 𝕜 := by
  have hEq :
      finiteInfimalConvolution (![f, g] : Fin 2 → E → WithTopBot 𝕜) = f □ g := by
    simpa using finiteInfimalConvolution_pair_eq_infimal_convolution (f := f) (g := g)
  rw [← hEq]
  exact Function.isConvex_finiteInfimalConvolution
    (![f, g] : Fin 2 → E → WithTopBot 𝕜) (Fin.forall_fin_two.2 ⟨hf_convex, hg_convex⟩)

end Function.IsConvex

end

/-! ### Text_5_4_5 (from Chap01) -/
noncomputable section

section

open scoped Pointwise
open scoped Function

variable {E : Type*}
variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [MulAction 𝕜 E]

/-- Helper for Text 5.4.5: extend scalar multiplication to `WithTopBot 𝕜` by multiplying on the
left after coercing the scalar. -/
local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot 𝕜) where
  smul c z := (c : WithTopBot 𝕜) * z

-- Route correction: the canonical `Text_5_4_2`/`Text_5_4_3` owner chain is currently blocked by
-- upstream artifact failures, so this file works directly on the positive-scalar surface that
-- Text 5.4.5 actually quantifies over.
local infixr:73 " •ʳ " => fun a f => fun x ↦ a • f ((a : 𝕜)⁻¹ • x)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.5 characterizes positive homogeneity by invariance under the right
  scalar-multiplication operation `f ↦ f λ`.
- `core/canonical`: the owner abstractions are the previously introduced declarations
  `rightScalarMul` (used on positive scalars via notation), and
  `Function.PositivelyHomogeneous` for functions `E → WithTopBot 𝕜`.
- `bridge/view`: the positive-scalar view of `rightScalarMul` is provided directly by
  `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`, exposing the positive scalar through
  the intrinsic owner `a : 𝕜⁺`; this file exposes that view directly on the
  positive-scalar notation surface and rewrites the epigraph-based definition into the textbook
  pointwise formula
  `x ↦ λ f (x / λ)` for positive scalars.
- Layer target: `source-facing`, expressed directly in terms of the canonical owner predicate
  `Function.PositivelyHomogeneous` from `Definition_4_8`.
- Primitive data vs derived API: the positive scalar `λ` and the function `f` are primitive; the
  fixed-point characterization of positive homogeneity is the derived API.

Domain-style sampling used here:
- `rightScalarMul` and `rightScalarMul_eq_sInf` from `Text_5_4_2`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos` from `Text_5_4_3`;
- the generic owner `Function.PositivelyHomogeneous : (E → WithTopBot 𝕜) → Prop` from
  `Definition_4_8`, recalled in `Text_5_4_4`.
- Ambient minimization: both owners already live canonically over an arbitrary `𝕜`-action, and
  the proof uses only the multiplicative scalar-action identities
  `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos` and `smul_inv_smul₀`, with no additive,
  linear, coordinate, or finite-dimensional structure. The public theorem is therefore
  stated at that intrinsic `MulAction` level rather than through a concrete coordinate model.

The source phrases the statement for convex functions, but once `rightScalarMul` is defined
for arbitrary functions the equivalence itself depends only on that definition, so the convexity
hypothesis is redundant and omitted from the main declaration.
-/

namespace Function

-- Proof sketch: use `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos` from Text 5.4.3.
-- If `f` is positively homogeneous, apply the scaling law to `λ` and `λ⁻¹ • x` to get
-- `λ • f (λ⁻¹ • x) = f x`, hence every positive right scalar multiple `(a •ʳ f)` fixes
-- `f`.
-- Conversely, if every such positive right scalar multiple fixes `f`, evaluate the fixed-point
-- identity at `λ • x` and rewrite with the same explicit formula to recover
-- `f (λ • x) = λ • f x`.

/-- Helper for Text 5.4.5: positive-scalar pointwise formula for right scalar multiplication. -/
theorem rightScalarMulPos_apply_eq_mul_comp_inv_smul
    (f : E → WithTopBot 𝕜) (a : 𝕜⁺) (x : E) :
    (a •ʳ f) x = a • f ((a : 𝕜)⁻¹ • x) := by
  -- The local notation is already the textbook positive-scalar formula.
  rfl

/-- Helper for Text 5.4.5: a positively homogeneous function is fixed by every positive
right scalar multiplication. -/
theorem rightScalarMul_eq_self_of_positivelyHomogeneous
    {f : E → WithTopBot 𝕜} (hf : f.PositivelyHomogeneous 𝕜) :
    ∀ a : 𝕜⁺, a •ʳ f = f := by
  intro a
  -- Rewrite the right scalar multiple pointwise and evaluate homogeneity on the inverse-scaled
  -- argument so the scalar and its inverse cancel.
  ext x
  calc
    (a •ʳ f) x = a • f ((a : 𝕜)⁻¹ • x) := by
      simpa using rightScalarMulPos_apply_eq_mul_comp_inv_smul (f := f) (a := a) (x := x)
    _ = f (a • ((a : 𝕜)⁻¹ • x)) := by
      simpa using (hf.map_smul_pos a ((a : 𝕜)⁻¹ • x)).symm
    _ = f x := by
      -- Collapse the scalar and its inverse before returning to the original argument.
      simpa [smul_smul, one_smul, a.2.ne'] using
        congrArg f (smul_inv_smul₀ a.2.ne' x)

/-- Helper for Text 5.4.5: invariance under every positive right scalar multiplication implies
positive homogeneity. -/
theorem positivelyHomogeneous_of_rightScalarMul_eq_self
    {f : E → WithTopBot 𝕜} (hfix : ∀ a : 𝕜⁺, a •ʳ f = f) :
    f.PositivelyHomogeneous 𝕜 := by
  intro a x
  -- Evaluate the fixed-point identity at the scaled argument and unfold the right scalar
  -- multiplication there to recover the defining scaling law.
  have hfixa : a •ʳ f = f := hfix a
  calc
    f (a • x) = (a •ʳ f) (a • x) := by
      simpa using (congrFun hfixa (a • x)).symm
    _ = a • f ((a : 𝕜)⁻¹ • (a • x)) := by
      simpa using rightScalarMulPos_apply_eq_mul_comp_inv_smul
        (f := f) (a := a) (x := a • x)
    _ = a • f x := by
      -- Collapse the inverse scalar on the argument before applying `f`.
      simpa [smul_smul, one_smul, a.2.ne'] using
        congrArg (fun y ↦ a • f y) (inv_smul_smul₀ a.2.ne' x)

/-- Text 5.4.5: a function is positively homogeneous exactly when every positive right scalar
multiple fixes it. -/
theorem positivelyHomogeneous_iff_rightScalarMul_eq_self (f : E → WithTopBot 𝕜) :
    f.PositivelyHomogeneous 𝕜 ↔
      ∀ a : 𝕜⁺, a •ʳ f = f := by
  constructor
  · intro hf
    exact rightScalarMul_eq_self_of_positivelyHomogeneous hf
  · intro hfix
    exact positivelyHomogeneous_of_rightScalarMul_eq_self hfix

end Function

end

/-! ### Text_5_4_6 (from Chap01) -/
noncomputable section

open scoped Pointwise Rockafellar

universe u v w

/-
Source/core/bridge triage:
- `source-facing`: Text 5.4.6 names the convex cone generated by the epigraph of a global
  extended-valued function `h : E → WithTopBot F`.
- `core/canonical`: the owner abstractions are the chapter epigraph owner `epi h` and the
  pointed-cone hull owner `PointedCone.hull` (notation `cone[R] (epi h)`).
- `bridge/view`: the raw set spelling `{p : E × F | h p.1 ≤ p.2}` stays a bridge view via
  `epi_univ_eq_setOf_le`; the theorem surface itself uses the source-facing nonnegative-ray
  notation `ray[R]` from Corollary 2.6.11.
- Primitive data vs derived API: the primitive datum is `h`; the generated cone owner is
  `cone[R] (epi h)`, and the convex-hull carrier identity on `ray[R] (epi h)` is derived API.
- Redundant-source-assumption elimination: convexity of `h` is not needed for this owner.
-/

namespace PointedCone

/-- Text 5.4.6: source-facing specialization of Corollary 2.6.11 to the epigraph owner `epi h`. -/
theorem cone_epi_eq_convexHull_zero_union_nonnegativeRay
    {R : Type v} [Semifield R] [PartialOrder R] [IsOrderedRing R] [PosMulReflectLT R]
    {E : Type u} [AddCommMonoid E] [Module R E]
    {F : Type w} [LE F] [AddCommMonoid F] [Module R F]
    (h : E → WithTopBot F) :
    (cone[R] (epi h) : Set (E × F)) =
      convexHull R (insert 0 (ray[R] (epi h))) := by
  -- Specialize the generic generated-cone hull formula to the epigraph owner `epi h`.
  simpa using
    (hull_eq_convexHull_zero_union_nonnegativeRay (S := epi h))

end PointedCone

/-! ### Text_5_4_7 (from Chap01) -/
noncomputable section

universe u v

section

variable {E : Type u} {𝕜 : Type v}

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.7 defines the function generated from `h` by applying Theorem 5.3 to
  the cone of the epigraph of `h`.
- `core/canonical`: the owner abstractions already introduced in the chapter are
  `ConvexOn 𝕜 (Set.univ : Set E)` from Definition 4.2, `Function.verticalInfimum` from
  Theorem 5.3, and the generated cone owner `cone[𝕜] (epi h)` from Text 5.4.6.
- `bridge/view`: the source-facing owner is the generated function `sublinearHull h`. The
  raw construction route `verticalInfimum (PointedCone.hull 𝕜 (epi h))` is retained only as a
  secondary bridge/specification. The maximal-minorant interpretation is deferred to `Text_5_4_8`,
  where the extra hypothesis `u 0 ≤ 0` appears explicitly.
- Primitive data vs derived API: `h` and the generated function are primitive; the `sInf`
  description and convexity statement are derived from the owner-side API.
- Ambient minimization: the owner construction and its defining `sInf` formula only need the
  primitive `verticalInfimum` and `PointedCone.hull` layers, so they are kept under the weaker
  ordered-semiring assumptions. The stronger ordered-ring assumptions are isolated to the convexity
  theorem, where `Function.isConvex_verticalInfimum` genuinely requires them.
- Layer target: `source-facing`; this file introduces the generated function itself and records its
  convexity, while the implementation continues to reuse the pointed-cone hull and vertical-infimum
  owners upstream.

Domain-style sampling used here:
- `Function.verticalInfimum`;
- `Function.verticalInfimum_eq_sInf_verticalHeights`;
- `Function.isConvex_verticalInfimum`;

The source assumes `h` is convex, but the cone-of-epigraph construction itself depends only on
`h`, so that hypothesis is not part of the primitive definition.
-/

namespace Function

open PointedCone

section Basic

variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- Text 5.4.7: the sublinear hull of `h`, defined as the vertical infimum of the generated cone
of its epigraph. -/
def sublinearHull (h : E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  verticalInfimum (cone[𝕜] (epi h))

/-- Source-facing owner specification: the sublinear hull of `h` is the vertical infimum of the
generated cone `cone[𝕜] (epi h)`. -/
theorem sublinearHull_eq_verticalInfimum (h : E → WithTopBot 𝕜) :
    sublinearHull h =
      verticalInfimum (cone[𝕜] (epi h)) :=
  rfl

/-- Secondary bridge/view form on the raw owner spelling `PointedCone.hull 𝕜 (epi h)`. -/
theorem sublinearHull_eq_verticalInfimum_hull_epi (h : E → WithTopBot 𝕜) :
    sublinearHull h = verticalInfimum (hull 𝕜 (epi h)) := by
  simpa using sublinearHull_eq_verticalInfimum (h := h)

/-- The value of `sublinearHull h` at `x` is the infimum of the scalar heights in the vertical
fiber of the generated epigraph cone above `x`, stated at the intrinsic owner
`Function.verticalHeights`. -/
theorem sublinearHull_eq_sInf_verticalHeights (h : E → WithTopBot 𝕜) (x : E) :
    sublinearHull h x =
      sInf (verticalHeights (cone[𝕜] (epi h)) x) := by
  simpa [sublinearHull] using
    verticalInfimum_eq_sInf_verticalHeights ((cone[𝕜] (epi h) : Set (E × 𝕜))) x

end Basic

-- Proof sketch: the generated cone of the epigraph of `h` is convex because it is a pointed
-- cone. Apply
-- `Function.isConvex_verticalInfimum` from Theorem 5.3 to its underlying set.
section Convex

variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

local instance : DecidableLT 𝕜 := Classical.decRel (· < ·)

/-- Helper for Text 5.4.7: use the concrete multiplication action of `𝕜` on `WithTopBot 𝕜` in the
owner-side convexity inequality. -/
local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul c z := (c : WithTopBot 𝕜) * z

/-- Helper for Text 5.4.7: left multiplication by a nonnegative finite scalar is monotone on
`WithTopBot 𝕜`. -/
private theorem mul_le_mul_left_coe_withTopBot {a : 𝕜} (ha : 0 ≤ a) {u v : WithTopBot 𝕜}
    (h : u ≤ v) :
    (a : WithTopBot 𝕜) * u ≤ (a : WithTopBot 𝕜) * v := by
  -- Reduce first along the outer `WithTop`; the finite branch then drops to monotonicity on
  -- `WithBot 𝕜`.
  induction v using WithTop.recTopCoe with
  | top =>
      by_cases ha0 : a = 0
      · simp [ha0]
      · have ha0' : (a : WithTopBot 𝕜) ≠ 0 := by
          exact_mod_cast ha0
        rw [WithTop.mul_top ha0']
        exact le_top
  | coe v =>
      induction u using WithTop.recTopCoe with
      | top =>
          exfalso
          simp at h
      | coe u =>
          have huv : u ≤ v := WithTop.coe_le_coe.mp h
          have ha' : (0 : WithBot 𝕜) ≤ ((a : 𝕜) : WithBot 𝕜) := by
            exact WithBot.coe_le_coe.mpr ha
          exact WithTop.coe_le_coe.mpr (mul_le_mul_of_nonneg_left huv ha')

/-- Helper for Text 5.4.7: a nonnegative scalar preserves an upper bound by a finite height in
`WithTopBot 𝕜`. -/
private theorem smul_le_smul_coe_of_le_coe {a μ : 𝕜} (ha : 0 ≤ a) {z : WithTopBot 𝕜}
    (hz : z ≤ (μ : WithTopBot 𝕜)) :
    a • z ≤ a • (μ : WithTopBot 𝕜) := by
  -- Route correction: package the codomain transport through a reusable monotonicity lemma, then
  -- use it as a thin adapter for the local scalar action.
  change ((a : WithTopBot 𝕜) * z ≤ ((a : WithTopBot 𝕜) * (μ : WithTopBot 𝕜)))
  exact mul_le_mul_left_coe_withTopBot ha hz

variable [DenselyOrdered 𝕜]

/-- Theorem 5.3, specialized to Text 5.4.7 on the canonical owner surface: the function
generated from `h` by the cone-of-epigraph construction is convex on the whole space. -/
theorem convexOn_sublinearHull (h : E → WithTopBot 𝕜) :
    ConvexOn 𝕜 (Set.univ : Set E) (sublinearHull h) := by
  -- Rewrite the generated function back to the vertical infimum attached to the convex cone.
  simpa [Function.IsConvex, sublinearHull] using
    Function.isConvex_verticalInfimum ((cone[𝕜] (epi h)).convex)

/-- Bridge form of `convexOn_sublinearHull` on the chapter shorthand owner. -/
theorem isConvex_sublinearHull (h : E → WithTopBot 𝕜) :
    (sublinearHull h).IsConvex 𝕜 := by
  -- Repackage the owner-side convexity inequality into convexity of the finite-height epigraph.
  rw [Function.IsConvex]
  rintro ⟨x, μ⟩ hx ⟨y, ν⟩ hy a b ha hb hab
  rw [mem_epi_iff] at hx hy
  have hconv :
      sublinearHull h (a • x + b • y) ≤
        a • sublinearHull h x + b • sublinearHull h y :=
    (convexOn_sublinearHull (h := h)).2 (by simp) (by simp) ha hb hab
  have hcombo :
      sublinearHull h (a • x + b • y) ≤
        ((a * μ + b * ν : 𝕜) : WithTopBot 𝕜) := by
    -- Push the finite endpoint bounds through the concrete multiplication action on `WithTopBot 𝕜`.
    have hax :
        a • sublinearHull h x ≤ a • (μ : WithTopBot 𝕜) := by
      exact smul_le_smul_coe_of_le_coe ha hx
    have hby :
        b • sublinearHull h y ≤ b • (ν : WithTopBot 𝕜) := by
      exact smul_le_smul_coe_of_le_coe hb hy
    calc
      sublinearHull h (a • x + b • y)
          ≤ a • sublinearHull h x + b • sublinearHull h y := hconv
      _ ≤ a • (μ : WithTopBot 𝕜) + b • (ν : WithTopBot 𝕜) := by
        exact add_le_add hax hby
      _ = ((a : WithTopBot 𝕜) * (μ : WithTopBot 𝕜) +
          (b : WithTopBot 𝕜) * (ν : WithTopBot 𝕜)) := by
        rfl
      _ = ((a * μ + b * ν : 𝕜) : WithTopBot 𝕜) := by
        simp [WithTop.coe_add, WithTop.coe_mul, WithBot.coe_add, WithBot.coe_mul]
  -- Unfolding the pair combination shows exactly the finite-height epigraph condition.
  simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_add, add_comm, add_left_comm,
    add_assoc, mul_comm, mul_left_comm, mul_assoc] using hcombo

end Convex

end Function

end

/-! ### Text_5_4_8 (from Chap01) -/
noncomputable section

universe u v

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.8 states the maximality properties of the positively homogeneous hull
  constructed in Text 5.4.7.
- `core/canonical`: the owner objects already introduced upstream are the function
  `Function.sublinearHull h` from `Text_5_4_7`, the generated cone
  `cone[𝕜] (epi h)` from `Text_5_4_7`, the convexity predicate
  `Function.IsConvex` from `Theorem_4_2`, and the generic positive-homogeneity predicate
  `Function.PositivelyHomogeneous` from `Definition_4_8`,
  on the ordered extended codomain `WithBotTop 𝕜`.
- `bridge/view`: source clause `(1)` is recorded through the owner-side cone statement for the
  epigraph together with the separate origin-membership companion; convexity itself is
  already the upstream owner theorem `Function.isConvex_sublinearHull`, and the cone part of
  clause `(1)` is the generic bridge `Function.isCone_epi_of_positivelyHomogeneous`. The
  canonical generated-cone bridge available without extra closedness hypotheses is the inclusion
  `cone[𝕜] (epi h) ⊆ epi (sublinearHull h)`, coming directly from the owner theorem
  `Function.verticalInfimum_le_of_mem`;
  the maximal-minorant clause is most naturally expressed by a single owner-side set of
  minorants and `IsGreatest`.
- Primitive data vs derived API: the function `h` and the generated hull are primitive; the
  cone statement, origin membership, convexity, the cone-to-epigraph inclusion, and the
  maximal-minorant property are derived statements.

Domain-style sampling used here:
- `Set.IsCone`;
- `Function.IsConvex`;
- `PointedCone.hull`;
- `Function.sublinearHull`;
- `Function.isConvex_sublinearHull`;
- `Function.isCone_epi_of_positivelyHomogeneous`;
- `Function.verticalInfimum_le_of_mem`;
- `Function.PositivelyHomogeneous`.

The source assumes `h` is convex, but every displayed conclusion depends only on the cone
generated by `epi h`, so the convexity hypothesis on `h` is redundant for the maximal-minorant
statements below. The companion bridge retained here is the always-valid inclusion from the
generated cone into the epigraph of `sublinearHull h`; no exact epigraph-cone equality is
claimed without additional attainment/closedness hypotheses.
-/

namespace Function

open PointedCone
open scoped Pointwise

section Basic

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

/-- Text 5.4.8 (5): source clause (2), the generated function satisfies `f(0) ≤ 0`. -/
theorem sublinearHull_apply_zero_le (h : E → WithBotTop 𝕜) :
    sublinearHull h 0 ≤ 0 := by
  rw [sublinearHull_eq_sInf_verticalHeights]
  refine sInf_le ⟨0, ?_, rfl⟩
  change ((0 : E), (0 : 𝕜)) ∈ (cone[𝕜] (epi h) : Set (E × 𝕜))
  exact (cone[𝕜] (epi h)).zero_mem

/-- Text 5.4.8 (1): the epigraph of the generated function contains the origin. -/
theorem zero_mem_epi_sublinearHull (h : E → WithBotTop 𝕜) :
    (0 : E × 𝕜) ∈ epi (sublinearHull h) := by
  rw [mem_epi_restrict_iff]
  simp [sublinearHull_apply_zero_le h]

-- Proof sketch: by definition, `sublinearHull h` is the vertical infimum of the generated cone
-- `cone[𝕜] (epi h)`. Any point `(x, μ)` of that cone therefore satisfies
-- `sublinearHull h x ≤ μ`, so it lies in the epigraph of the generated function.
/-- Companion bridge: the generated cone of the epigraph of `h` is contained in the
epigraph of the generated function `sublinearHull h`. Equality generally fails without additional
attainment or closedness hypotheses on the cone fibers. -/
theorem cone_epi_subset_epi_sublinearHull (h : E → WithBotTop 𝕜) :
    cone[𝕜] (epi h) ⊆ epi (sublinearHull h) := by
  intro p hp
  rcases p with ⟨x, μ⟩
  rw [mem_epi_iff]
  simpa [sublinearHull] using
    (verticalInfimum_le_of_mem hp :
      verticalInfimum (cone[𝕜] (epi h) : Set (E × 𝕜)) x ≤ ((μ : 𝕜) : WithBotTop 𝕜))

end Basic

section NoBotOrder

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜] [IsOrderedRing 𝕜]
variable [NoBotOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

/-- Text 5.4.8 (6): source clause (2), the generated function is a pointwise minorant of `h`. -/
theorem sublinearHull_le (h : E → WithBotTop 𝕜) :
    sublinearHull h ≤ h := by
  have hsubset : epi h ⊆ (cone[𝕜] (epi h) : Set (E × 𝕜)) := by
    exact (subset_hull : epi h ⊆ hull 𝕜 (epi h))
  simpa [sublinearHull] using verticalInfimum_le_of_epi_subset hsubset

end NoBotOrder

section MinorantOwner

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜] [SMul 𝕜 (WithBotTop 𝕜)]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

/-- Canonical owner for the positively homogeneous convex minorants of `h`
with nonpositive value at the origin. -/
def sublinearMinorants (h : E → WithBotTop 𝕜) : Set (E → WithBotTop 𝕜) :=
  {u | u.PositivelyHomogeneous 𝕜 ∧ u.IsConvex 𝕜 ∧ u 0 ≤ 0 ∧ u ≤ h}

end MinorantOwner

section Convex

variable {𝕜 : Type v} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

/- Text 5.4.8 (2): source clause (2), the generated function is convex. This is exactly the owner
theorem already established in `Text_5_4_7`. -/
recall isConvex_sublinearHull

-- Proof sketch: for `a > 0`, every point `(y, μ)` of the generated cone remains in the cone after
-- scaling by `a⁻¹`; this gives
-- `a • sublinearHull h (a⁻¹ • y) ≤ μ` and hence
-- `a • sublinearHull h (a⁻¹ • y) ≤ sublinearHull h y` by
-- `le_verticalInfimum_of_subset_epi`. Applying this once with `a = c` and once with `a = c⁻¹`,
-- then canceling positive scalings on `WithBotTop 𝕜`, yields
-- `sublinearHull h (c • x) = c • sublinearHull h x`.
/-- Text 5.4.8 (4): source clause (2), the generated function is positively homogeneous. -/
theorem positivelyHomogeneous_sublinearHull (h : E → WithBotTop 𝕜) :
    (sublinearHull h).PositivelyHomogeneous 𝕜 := by
  letI : DecidableLT 𝕜 := Classical.decRel (· < ·)
  have hsmul_inv_smul : ∀ (c : 𝕜), 0 < c → ∀ z : WithBotTop 𝕜, c • (c⁻¹ • z) = z := by
    intro c hc z
    cases z using WithBotTop.rec with
    | bot =>
        rw [WithBotTop.smul_def, WithBotTop.smul_def]
        rw [WithBotTop.coe_mul_bot_of_pos (inv_pos.mpr hc)]
        exact WithBotTop.coe_mul_bot_of_pos hc
    | top =>
        rw [WithBotTop.smul_def, WithBotTop.smul_def]
        rw [WithBotTop.coe_mul_top_of_pos (inv_pos.mpr hc)]
        exact WithBotTop.coe_mul_top_of_pos hc
    | coe r =>
        calc
          c • (c⁻¹ • ((r : 𝕜) : WithBotTop 𝕜))
              = (c : WithBotTop 𝕜) * ((((c⁻¹ : 𝕜) : WithBotTop 𝕜) * (r : WithBotTop 𝕜))) := by
                  simp [WithBotTop.smul_def]
          _ = (c : WithBotTop 𝕜) * (((c⁻¹ * r : 𝕜) : WithBotTop 𝕜)) := by
                  rw [← WithBotTop.coe_mul]
          _ = ((c * (c⁻¹ * r) : 𝕜) : WithBotTop 𝕜) := by
                  rw [← WithBotTop.coe_mul]
          _ = (r : WithBotTop 𝕜) := by
                  congr 1
                  field_simp [hc.ne']
  have hscaled_le :
      ∀ {a : 𝕜}, 0 < a →
        (fun y : E ↦ a • sublinearHull h (a⁻¹ • y)) ≤ sublinearHull h := by
    intro a ha
    let g : E → WithBotTop 𝕜 := fun y ↦ a • sublinearHull h (a⁻¹ • y)
    have hsubset : (cone[𝕜] (epi h) : Set (E × 𝕜)) ⊆ epi g := by
      intro p hp
      rcases p with ⟨y, μ⟩
      rw [mem_epi_iff]
      have hscaled : ((a⁻¹ • y, a⁻¹ * μ) : E × 𝕜) ∈ (cone[𝕜] (epi h) : Set (E × 𝕜)) := by
        simpa [smul_eq_mul] using
          (cone[𝕜] (epi h)).smul_mem (inv_nonneg.mpr ha.le) hp
      have hle : sublinearHull h (a⁻¹ • y) ≤ ((a⁻¹ * μ : 𝕜) : WithBotTop 𝕜) := by
        simpa [sublinearHull] using
          (verticalInfimum_le_of_mem hscaled :
            verticalInfimum (cone[𝕜] (epi h) : Set (E × 𝕜)) (a⁻¹ • y) ≤
              ((a⁻¹ * μ : 𝕜) : WithBotTop 𝕜))
      have hmul : a • sublinearHull h (a⁻¹ • y) ≤ a • (((a⁻¹ * μ : 𝕜) : WithBotTop 𝕜)) := by
        have ha_nonneg : (0 : WithBotTop 𝕜) ≤ (a : WithBotTop 𝕜) := by
          exact (WithBotTop.coe_nonneg).2 ha.le
        have hmul' :
            (a : WithBotTop 𝕜) * sublinearHull h (a⁻¹ • y) ≤
              (a : WithBotTop 𝕜) * (((a⁻¹ * μ : 𝕜) : WithBotTop 𝕜)) :=
          (WithBotTop.monotone_mul_left_of_nonneg ha_nonneg) hle
        simpa [WithBotTop.smul_def] using hmul'
      have hright : a • (((a⁻¹ * μ : 𝕜) : WithBotTop 𝕜)) = (μ : WithBotTop 𝕜) := by
        calc
          a • (((a⁻¹ * μ : 𝕜) : WithBotTop 𝕜))
              = ((a * (a⁻¹ * μ) : 𝕜) : WithBotTop 𝕜) := by
                  simp [WithBotTop.smul_def, ← WithBotTop.coe_mul]
          _ = (μ : WithBotTop 𝕜) := by
                  congr 1
                  field_simp [ha.ne']
      exact hmul.trans_eq hright
    simpa [g, sublinearHull] using
      (le_verticalInfimum_of_subset_epi (F := (cone[𝕜] (epi h) : Set (E × 𝕜))) (h := g) hsubset)
  intro c x
  have hc : 0 < (c : 𝕜) := c.2
  have hleft : (c : 𝕜) • sublinearHull h x ≤ sublinearHull h ((c : 𝕜) • x) := by
    have h := (hscaled_le (a := (c : 𝕜)) hc) ((c : 𝕜) • x)
    simpa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using h
  have hinv : ((c : 𝕜)⁻¹) • sublinearHull h ((c : 𝕜) • x) ≤ sublinearHull h x := by
    have h := (hscaled_le (a := (c : 𝕜)⁻¹) (inv_pos.mpr hc)) x
    simpa [inv_inv] using h
  have hright : sublinearHull h ((c : 𝕜) • x) ≤ (c : 𝕜) • sublinearHull h x := by
    have hmul : (c : 𝕜) • (((c : 𝕜)⁻¹) • sublinearHull h ((c : 𝕜) • x)) ≤
        (c : 𝕜) • sublinearHull h x := by
      have hc_nonneg : (0 : WithBotTop 𝕜) ≤ ((c : 𝕜) : WithBotTop 𝕜) := by
        exact (WithBotTop.coe_nonneg).2 hc.le
      have hmul' :
          ((c : 𝕜) : WithBotTop 𝕜) * (((c : 𝕜)⁻¹) • sublinearHull h ((c : 𝕜) • x)) ≤
            ((c : 𝕜) : WithBotTop 𝕜) * sublinearHull h x :=
        (WithBotTop.monotone_mul_left_of_nonneg hc_nonneg) hinv
      simpa [WithBotTop.smul_def] using hmul'
    calc
      sublinearHull h ((c : 𝕜) • x)
          = (c : 𝕜) • (((c : 𝕜)⁻¹) • sublinearHull h ((c : 𝕜) • x)) := by
              symm
              exact hsmul_inv_smul (c : 𝕜) hc _
      _ ≤ (c : 𝕜) • sublinearHull h x := hmul
  exact le_antisymm hright hleft

/-- Helper for Text 5.4.8: a pointwise minorant relation reverses epigraph inclusion. -/
theorem epi_subset_epi_of_le
    {u h : E → WithBotTop 𝕜}
    (hu_le_h : u ≤ h) :
    epi h ⊆ epi u := by
  -- Unpack the epigraph inequality and compose it with the pointwise domination `u ≤ h`.
  intro p hp
  rcases p with ⟨x, μ⟩
  rw [mem_epi_iff] at hp ⊢
  exact (hu_le_h x).trans hp

/-- Helper for Text 5.4.8: a pointwise minorant relation propagates to the generated epigraph
cones. -/
theorem cone_epi_subset_epi_of_le
    {u h : E → WithBotTop 𝕜}
    (hu_le_h : u ≤ h) :
    (cone[𝕜] (epi h) : Set (E × 𝕜)) ⊆ (cone[𝕜] (epi u) : Set (E × 𝕜)) := by
  -- Lift the source-side epigraph containment through the monotonicity of the generated cone.
  exact Submodule.span_mono (epi_subset_epi_of_le hu_le_h)

/-- Helper for Text 5.4.8: a positively homogeneous convex function with `u 0 ≤ 0`
already contains the cone generated by its own epigraph. -/
theorem cone_epi_subset_of_epi
    {u : E → WithBotTop 𝕜}
    (hu_hom : u.PositivelyHomogeneous 𝕜) (hu_convex : u.IsConvex 𝕜)
    (hu_zero : u 0 ≤ 0) :
    (cone[𝕜] (epi u) : Set (E × 𝕜)) ⊆ epi u := by
  have h_cone_u :
      (cone[𝕜] (epi u) : Set (E × 𝕜)) = insert 0 ((Set.Ioi (0 : 𝕜)) • epi u) := by
    -- Rewrite the generated cone of a convex set into its positive ray description.
    simpa using
      (PointedCone.cone_eq_insert_zero_positiveRay_of_convex (C := epi u)
        (by simpa [epi_univ_eq_setOf_le] using hu_convex.convex_epigraph))
  intro p hp
  have hp' : p ∈ insert 0 ((Set.Ioi (0 : 𝕜)) • epi u) := by
    rw [← h_cone_u]
    exact hp
  rcases hp' with rfl | hp'
  · -- The cone origin belongs to the epigraph exactly because `u 0 ≤ 0`.
    rw [mem_epi_iff]
    simpa using hu_zero
  · rcases Set.mem_smul.mp hp' with ⟨a, ha, q, hq, rfl⟩
    rcases q with ⟨x, μ⟩
    rw [mem_epi_iff] at hq ⊢
    have hmul :
        (a : WithBotTop 𝕜) * u x ≤ (a : WithBotTop 𝕜) * (μ : WithBotTop 𝕜) :=
      (WithBotTop.monotone_mul_left_of_nonneg ((WithBotTop.coe_nonneg).2 ha.le)) hq
    -- Positive homogeneity identifies the scaled function value with scalar multiplication
    -- in the extended ordered codomain.
    calc
      u (a • x) = a • u x := hu_hom.map_smul ha x
      _ = (a : WithBotTop 𝕜) * u x := by simp [WithBotTop.smul_def]
      _ ≤ (a : WithBotTop 𝕜) * (μ : WithBotTop 𝕜) := hmul
      _ = ((a * μ : 𝕜) : WithBotTop 𝕜) := by simp [WithBotTop.coe_mul]

/-- Helper for Text 5.4.8: every admissible positively homogeneous convex minorant of `h`
contains the cone generated by `epi h` inside its own epigraph. -/
theorem cone_epi_subset_epi_of_mem_sublinearMinorants
    {u h : E → WithBotTop 𝕜}
    (hu : u ∈ sublinearMinorants h) :
    (cone[𝕜] (epi h) : Set (E × 𝕜)) ⊆ epi u := by
  rcases hu with ⟨hu_hom, hu_convex, hu_zero, hu_le_h⟩
  have h_hull_le : (cone[𝕜] (epi h) : Set (E × 𝕜)) ⊆ (cone[𝕜] (epi u) : Set (E × 𝕜)) :=
    cone_epi_subset_epi_of_le hu_le_h
  -- Route correction: isolate the cone-minimality step once, then reuse the epigraph-collapse
  -- lemma for the source-faithful maximality argument.
  intro p hp
  exact cone_epi_subset_of_epi hu_hom hu_convex hu_zero (h_hull_le hp)

-- Proof sketch: if `u` is positively homogeneous, convex, and satisfies `u 0 ≤ 0`, then its
-- epigraph is a convex cone containing the origin. The assumption `u ≤ h` gives `epi h ⊆ epi u`,
-- so minimality of the generated cone yields `PointedCone.hull 𝕜 (epi h) ⊆ epi u`. Since every
-- point of that generated cone lies in the epigraph of the generated function by construction
-- of the vertical infimum, this inclusion translates back to the pointwise inequality `u ≤ f`.
/-- Text 5.4.8 (3): the generated function is the greatest positively homogeneous convex minorant
of `h` among those satisfying `u 0 ≤ 0`. -/
theorem isGreatest_sublinearHull_minorant
    (h : E → WithBotTop 𝕜) :
    IsGreatest
      (sublinearMinorants h)
      (sublinearHull h) := by
  letI : DecidableLT 𝕜 := Classical.decRel (· < ·)
  refine ⟨?_, ?_⟩
  · exact ⟨positivelyHomogeneous_sublinearHull h, isConvex_sublinearHull h,
      sublinearHull_apply_zero_le h, sublinearHull_le h⟩
  · intro u hu
    -- Route correction: consume the dedicated cone-containment helper so the main proof mirrors
    -- the source argument `epi h ⊆ epi u ⇒ cone(epi h) ⊆ epi u`.
    have h_cone_le : (cone[𝕜] (epi h) : Set (E × 𝕜)) ⊆ epi u :=
      cone_epi_subset_epi_of_mem_sublinearMinorants hu
    have hu_le_vi : u ≤ verticalInfimum (cone[𝕜] (epi h) : Set (E × 𝕜)) :=
      le_verticalInfimum_of_subset_epi h_cone_le
    simpa [sublinearHull] using hu_le_vi

/-- Text 5.4.8 (7): source clause (3), every positively homogeneous convex minorant of `h` lies
below the generated function. -/
theorem le_sublinearHull_of_mem_sublinearMinorants
    {u h : E → WithBotTop 𝕜}
    (hu : u ∈ sublinearMinorants h) :
    u ≤ sublinearHull h :=
  (isGreatest_sublinearHull_minorant h).2 hu

/-- Text 5.4.8 (7), expanded-hypothesis bridge form of
`le_sublinearHull_of_mem_sublinearMinorants`. -/
theorem le_sublinearHull_of_le
    {u h : E → WithBotTop 𝕜}
    (hu_hom : u.PositivelyHomogeneous 𝕜) (hu_convex : u.IsConvex 𝕜)
    (hu_zero : u 0 ≤ 0) (hu_le_h : u ≤ h) :
    u ≤ sublinearHull h :=
  le_sublinearHull_of_mem_sublinearMinorants ⟨hu_hom, hu_convex, hu_zero, hu_le_h⟩

/-- Text 5.4.8 (1): the epigraph of the positively homogeneous convex function generated by
`h` is a cone. Convexity is the separate owner theorem `Function.isConvex_sublinearHull`. -/
theorem epi_sublinearHull_isCone (h : E → WithBotTop 𝕜) :
    Set.IsCone 𝕜 (epi (sublinearHull h)) := by
  exact isCone_epi_of_positivelyHomogeneous (positivelyHomogeneous_sublinearHull h)

end Convex

end Function

end

/-! ### Text_5_4_9 (from Chap01) -/
noncomputable section

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [IsOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)
local notation "𝕜≥0ˣ" => {a : 𝕜≥0 // (0 : 𝕜) < (a : 𝕜)}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.9 identifies the positively homogeneous convex function generated by
  `h` with the pointwise infimum of the nonnegative right scalar multiples `h λ`, and records when
  the zero scalar can be omitted from that infimum.
- `core/canonical`: the owner abstractions are the scaled-epigraph construction
  `rightScalarMul` and the cone-of-epigraph construction
  `Function.sublinearHull`.
- `bridge/view`: the second clause is a pointwise refinement of the first, isolating the `λ = 0`
  term through the zero-scalar behavior of `rightScalarMul`.
- Primitive data vs derived API: the function `h`, its right scalar multiples, and its generated
  positively homogeneous convex hull are primitive; the `iInf` representation and the positive-only
  refinement are derived API. The convexity of `h` is not part of either owner construction, but
  it is an essential theorem-side hypothesis for these `iInf` formulas, because it identifies the
  cone hull of `epi h` with the nonnegative ray through `epi h`.
- Layer target: `bridge/view`; the file gives pointwise `iInf` formulas for the existing owner
  declarations `rightScalarMul` and `Function.sublinearHull`, rather than
  defining a new owner object.

Domain-style sampling used here:
- `rightScalarMul`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`;
- `rightScalarMul_zero_apply_eq_origin_indicator_of_ne_top`;
- `Function.sublinearHull`;
- `Function.IsConvex.convex_epigraph`;
- `PointedCone.hull_eq_convexHull_nonnegativeRay`.
- Ambient minimization: these formulas use only the owner declarations above and pointwise
  evaluation, so they belong over an arbitrary `𝕜`-module `E` instead of the concrete display
  model `EuclideanSpace ℝ (Fin n)`.
-/

namespace Function

-- Proof sketch: use convexity of `h` to identify the cone hull of `epi h` with the nonnegative
-- ray `(Set.Ici (0 : 𝕜)) • epi h`, then isolate the `λ = 0` slice by the zero-scalar behavior of
-- `rightScalarMul`. Computing the attached vertical infimum fiberwise yields the displayed infimum
-- over the family of nonnegative right scalar multiples.

/-- Text 5.4.9: if `h` is convex, then away from the corner case `x = 0` with `h = ⊤`,
the positively homogeneous convex function generated by `h` is the pointwise infimum
of the nonnegative right scalar multiples of `h`. -/
theorem sublinearHull_eq_iInf_rightScalarMul
    (h : E → WithBotTop 𝕜) (h_convex : h.IsConvex 𝕜)
    (x : E) (hx : x ≠ 0 ∨ h ≠ (⊤ : E → WithBotTop 𝕜)) :
    sublinearHull h x =
      ⨅ a : 𝕜≥0, (a •ʳ h) x := sorry

-- Proof sketch: if `x ≠ 0`, the zero right scalar multiple contributes `⊤` at `x`, so it does
-- not change the infimum, even when `h = fun _ ↦ ⊤`. If `h 0 < ⊤`, then in particular `h ≠ ⊤`,
-- so `sublinearHull_eq_iInf_rightScalarMul` applies at `x = 0`; there,
-- the positive right scalar multiples approach `0`, matching the `λ = 0` value, so the same
-- infimum is obtained by restricting to strictly positive scalars.
/-- If `h` is convex and `x ≠ 0` or `h 0 < +∞`, the zero right scalar multiple does not affect the
infimum formula for the positively homogeneous convex function generated by `h`. -/
theorem
    sublinearHull_eq_iInf_pos_rightScalarMul
    [DenselyOrdered 𝕜]
    (h : E → WithBotTop 𝕜) (h_convex : h.IsConvex 𝕜) (x : E)
    (hx : x ≠ 0 ∨ h (0 : E) < ⊤) :
    sublinearHull h x =
      ⨅ a : 𝕜≥0ˣ, ((a : 𝕜≥0) •ʳ h) x := sorry

end Function

end
