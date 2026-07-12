import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Unique
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

-- Analogue note: `MeasureTheory.L2.inner_def` and bundled subspace owners such as
-- `galoisPowerClassFunctionSubmodule` guide the `L²(G)`-level packaging here.

section

variable {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]

local notation "L²G" => (G →₂[(μG : Measure G)] ℂ)

/-- Helper for Definition 4-28: conjugation by a fixed element preserves the normalized Haar
measure on `G`. -/
theorem conjMeasurePreserving (s : G) :
    MeasurePreserving (fun t : G ↦ s * t * s⁻¹) (μG : Measure G) (μG : Measure G) := by
  -- Conjugation is the composition of a right translation by `s⁻¹` and a left translation by `s`.
  simpa [Function.comp, mul_assoc] using
    (measurePreserving_mul_left (μ := (μG : Measure G)) s).comp
      (measurePreserving_mul_right (μ := (μG : Measure G)) s⁻¹)

/-- Helper for Definition 4-28: the zero `L²(G)` class is conjugation-invariant almost
everywhere. -/
theorem zero_ae_conjInvariant :
    ∀ s : G, (fun t ↦ ((0 : L²G) : L²G) (s * t * s⁻¹)) =ᵐ[μG] ((0 : L²G) : L²G) := by
  intro s
  -- Both representatives are the zero function, so the AE statement is immediate.
  have hzero :
      (((0 : L²G) : L²G) : G → ℂ) =ᵐ[μG] 0 :=
    Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal)) (μ := (μG : Measure G))
  have hzeroConj :
      (fun t ↦ (((0 : L²G) : L²G) : G → ℂ) (s * t * s⁻¹)) =ᵐ[μG] 0 := by
    change ((((0 : L²G) : L²G) : G → ℂ) ∘ fun t : G ↦ s * t * s⁻¹) =ᵐ[μG] 0
    exact hzero.comp_tendsto (conjMeasurePreserving s).quasiMeasurePreserving.tendsto_ae
  exact hzeroConj.trans hzero.symm

/-- Helper for Definition 4-28: the sum of two almost-everywhere conjugation-invariant `L²(G)`
classes is again conjugation-invariant almost everywhere. -/
theorem add_ae_conjInvariant
    {f g : L²G}
    (hf : ∀ s : G, (fun t ↦ (f : L²G) (s * t * s⁻¹)) =ᵐ[μG] (f : L²G))
    (hg : ∀ s : G, (fun t ↦ (g : L²G) (s * t * s⁻¹)) =ᵐ[μG] (g : L²G)) :
    ∀ s : G, (fun t ↦ ((f + g : L²G) : L²G) (s * t * s⁻¹)) =ᵐ[μG] ((f + g : L²G) : L²G) := by
  intro s
  -- Add the two AE equalities pointwise and simplify the ambient `L²(G)` addition formula.
  have hadd :
      (((f + g : L²G) : L²G) : G → ℂ) =ᵐ[μG] fun t ↦ (f : L²G) t + (g : L²G) t :=
    Lp.coeFn_add f g
  have haddConj :
      (fun t ↦ (((f + g : L²G) : L²G) : G → ℂ) (s * t * s⁻¹)) =ᵐ[μG]
        fun t ↦ (f : L²G) (s * t * s⁻¹) + (g : L²G) (s * t * s⁻¹) := by
    simpa [Function.comp] using
      hadd.comp_tendsto (conjMeasurePreserving s).quasiMeasurePreserving.tendsto_ae
  have hsum :
      (fun t ↦ (f : L²G) (s * t * s⁻¹) + (g : L²G) (s * t * s⁻¹)) =ᵐ[μG]
        fun t ↦ (f : L²G) t + (g : L²G) t := by
    simpa using (hf s).add (hg s)
  exact haddConj.trans hsum |>.trans hadd.symm

/-- Helper for Definition 4-28: scalar multiples of almost-everywhere conjugation-invariant
`L²(G)` classes stay conjugation-invariant almost everywhere. -/
theorem smul_ae_conjInvariant
    (c : ℂ) {f : L²G}
    (hf : ∀ s : G, (fun t ↦ (f : L²G) (s * t * s⁻¹)) =ᵐ[μG] (f : L²G)) :
    ∀ s : G, (fun t ↦ ((c • f : L²G) : L²G) (s * t * s⁻¹)) =ᵐ[μG] ((c • f : L²G) : L²G) := by
  intro s
  -- Multiply the AE equality by the constant scalar and simplify pointwise.
  have hsmul :
      (((c • f : L²G) : L²G) : G → ℂ) =ᵐ[μG] fun t ↦ c • (f : L²G) t :=
    Lp.coeFn_smul c f
  have hsmulConj :
      (fun t ↦ (((c • f : L²G) : L²G) : G → ℂ) (s * t * s⁻¹)) =ᵐ[μG]
        fun t ↦ c • (f : L²G) (s * t * s⁻¹) := by
    simpa [Function.comp] using
      hsmul.comp_tendsto (conjMeasurePreserving s).quasiMeasurePreserving.tendsto_ae
  exact hsmulConj.trans
    ((Filter.EventuallyEq.smul (Filter.EventuallyEq.rfl) (hf s)).trans hsmul.symm)

/-- `squareIntegrableClassFunctionSubmodule` is the submodule of normalized-Haar `L²(G)` classes
whose representatives are conjugation-invariant almost everywhere. -/
def squareIntegrableClassFunctionSubmodule : Submodule ℂ L²G where
  carrier := {f | ∀ s : G, (fun t ↦ (f : L²G) (s * t * s⁻¹)) =ᵐ[μG] (f : L²G)}
  zero_mem' := zero_ae_conjInvariant
  add_mem' := add_ae_conjInvariant
  smul_mem' := smul_ae_conjInvariant

/-- Membership in `squareIntegrableClassFunctionSubmodule` is exactly conjugation-invariance of the
underlying `L²(G)` class. -/
@[simp]
theorem mem_squareIntegrableClassFunctionSubmodule_iff (f : L²G) :
    f ∈ (squareIntegrableClassFunctionSubmodule : Submodule ℂ L²G) ↔
      ∀ s : G, (fun t ↦ f (s * t * s⁻¹)) =ᵐ[μG] f := by
  -- Unfold the carrier predicate once so the statement becomes tautological.
  simp [squareIntegrableClassFunctionSubmodule]

/-- Helper for Definition 4-28: conjugation acts on normalized-Haar `L²(G)` by pullback along the
measure-preserving conjugation map. -/
def conjTranslateLp (s : G) : L²G →ₗᵢ[ℂ] L²G :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) (p := (2 : ENNReal))
    (fun t : G ↦ s * t * s⁻¹) (conjMeasurePreserving s)

/-- Helper for Definition 4-28: the `L²(G)` conjugation operator is represented almost everywhere
by precomposition with `t ↦ s * t * s⁻¹`. -/
theorem conjTranslateLp_ae_eq (s : G) (f : L²G) :
    conjTranslateLp s f =ᵐ[μG] fun t ↦ f (s * t * s⁻¹) := by
  -- Unpack the `Lp` pullback operator to its representative-level AE equality.
  simpa [conjTranslateLp] using
    (MeasureTheory.Lp.coeFn_compMeasurePreserving
      (f := fun t : G ↦ s * t * s⁻¹) (μ := (μG : Measure G)) (μb := (μG : Measure G))
      (g := f) (hf := conjMeasurePreserving s))

/-- Helper for Definition 4-28: belonging to the class-function submodule is equivalent to being
fixed by every conjugation operator on `L²(G)`. -/
theorem mem_squareIntegrableClassFunctionSubmodule_iff_forall_conjTranslate_eq (f : L²G) :
    f ∈ (squareIntegrableClassFunctionSubmodule : Submodule ℂ L²G) ↔
      ∀ s : G, conjTranslateLp s f = f := by
  constructor
  · intro hf s
    -- Turn the AE representative formula into equality of `L²(G)` classes via extensionality.
    refine Lp.ext ?_
    filter_upwards [conjTranslateLp_ae_eq s f,
      (mem_squareIntegrableClassFunctionSubmodule_iff (f := f)).1 hf s] with t ht₁ ht₂
    exact ht₁.trans ht₂
  · intro hf
    -- Rewrite the fixed-point identity back to the representative-level conjugation formula.
    refine (mem_squareIntegrableClassFunctionSubmodule_iff (f := f)).2 ?_
    intro s
    simpa [hf s] using (conjTranslateLp_ae_eq s f).symm

/-- The submodule of `L²(G)` consisting of square-integrable class functions is closed. -/
theorem squareIntegrableClassFunctionSubmodule_isClosed :
    IsClosed ((squareIntegrableClassFunctionSubmodule : Submodule ℂ L²G) : Set L²G) := by
  -- Identify the submodule with the intersection of the fixed-point kernels of the conjugation
  -- operators, where closedness is immediate from continuity.
  have hset :
      ((squareIntegrableClassFunctionSubmodule : Submodule ℂ L²G) : Set L²G) =
        ⋂ s : G,
          ((((conjTranslateLp s).toContinuousLinearMap - ContinuousLinearMap.id ℂ L²G).ker :
              Submodule ℂ L²G) : Set L²G) := by
    ext f
    simpa [LinearMap.mem_ker, sub_eq_zero] using
      (mem_squareIntegrableClassFunctionSubmodule_iff_forall_conjTranslate_eq (f := f))
  rw [hset]
  exact isClosed_iInter fun s ↦
    ((conjTranslateLp s).toContinuousLinearMap - ContinuousLinearMap.id ℂ L²G).isClosed_ker

/-- The closed-submodule owner for square-integrable class functions on `G`. -/
def squareIntegrableClassFunctionClosedSubmodule : ClosedSubmodule ℂ L²G :=
  ⟨squareIntegrableClassFunctionSubmodule, squareIntegrableClassFunctionSubmodule_isClosed⟩

/-- Definition 4-28 (1): `SquareIntegrableClassFunction` is the Hilbert space `L²_cl(G)` of
square-integrable class functions on `G`. -/
abbrev SquareIntegrableClassFunction
    (H : Type) [Group H] [TopologicalSpace H] [CompactSpace H]
    [MeasurableSpace H] [BorelSpace H] [IsTopologicalGroup H] : Type _ :=
  (squareIntegrableClassFunctionSubmodule :
    Submodule ℂ (H →₂[(μG : Measure H)] ℂ))

scoped[Representation] notation:max "L²_cl(" G ")" =>
  SquareIntegrableClassFunction G

open scoped Representation

/-- Elements of `L²_cl(G)` are canonically viewed as complex-valued functions on `G` through the
ambient normalized-Haar `L²(G)` class. -/
instance : CoeFun (SquareIntegrableClassFunction G) (fun _ ↦ G → ℂ) where
  coe f := (((f : squareIntegrableClassFunctionSubmodule) : L²G) : G → ℂ)

/-- The carrier of `SquareIntegrableClassFunction` is closed in the ambient normalized-Haar
`L²(G)`. -/
instance squareIntegrableClassFunction_isClosed :
    IsClosed ((squareIntegrableClassFunctionSubmodule : Submodule ℂ L²G) : Set L²G) :=
  squareIntegrableClassFunctionSubmodule_isClosed

/-- Coercing the closed owner of `L²_cl(G)` back to a submodule recovers the defining submodule. -/
@[simp] theorem coe_squareIntegrableClassFunctionClosedSubmodule :
    ((squareIntegrableClassFunctionClosedSubmodule : ClosedSubmodule ℂ L²G) :
        Submodule ℂ L²G) =
      squareIntegrableClassFunctionSubmodule :=
  rfl

/-- The Hilbert space `L²_cl(G)` is complete. -/
instance squareIntegrableClassFunctionCompleteSpace :
    CompleteSpace (SquareIntegrableClassFunction G) :=
  inferInstance

/-- `L²_cl(G)` inherits the ambient normalized-Haar `L²(G)` norm. -/
instance squareIntegrableClassFunctionNormedAddCommGroup :
    NormedAddCommGroup (SquareIntegrableClassFunction G) :=
  inferInstance

/-- `L²_cl(G)` inherits the ambient normalized-Haar `L²(G)` inner product. -/
instance squareIntegrableClassFunctionInnerProductSpace :
    InnerProductSpace ℂ (SquareIntegrableClassFunction G) :=
  inferInstance

/-- An element of `SquareIntegrableClassFunction` is conjugation-invariant almost everywhere as an
`L²(G)` class. -/
theorem squareIntegrableClassFunction_ae_conj_invariant
    (f : L²_cl(G)) (s : G) :
    (fun t ↦ f (s * t * s⁻¹)) =ᵐ[μG] f :=
  (mem_squareIntegrableClassFunctionSubmodule_iff (f := (f : L²G))).1 f.2 s

/-- The `L²_cl(G)` inner product is the ambient normalized-Haar `L²(G)` inner product. -/
theorem squareIntegrableClassFunction_inner_eq
    (f h : L²_cl(G)) :
    inner ℂ f h = inner ℂ (f : L²G) (h : L²G) :=
  rfl

/-- Definition 4-28 (2): the textbook scalar product on `L²_cl(G)` is the ambient normalized-Haar
`L²(G)` pairing, written with Serre's conjugate-on-the-second-variable convention. -/
def squareIntegrableClassFunctionScalar
    (f h : L²_cl(G)) : Complex :=
  inner ℂ h f

-- The source formula is stated on representatives of the ambient `L²(G)` classes.
/-- The textbook scalar product on square-integrable class functions is computed by integrating
`f t * conj (h t)` against the normalized Haar measure. -/
theorem squareIntegrableClassFunctionScalar_def
    (f h : L²_cl(G)) :
    squareIntegrableClassFunctionScalar f h =
      ∫ t, f t * conj (h t) ∂μG := by
  -- This is exactly the ambient `L²(G)` inner-product formula with Serre's argument order.
  simpa [squareIntegrableClassFunctionScalar, mul_comm] using
    (L2.inner_def (h : L²G) (f : L²G))

end
