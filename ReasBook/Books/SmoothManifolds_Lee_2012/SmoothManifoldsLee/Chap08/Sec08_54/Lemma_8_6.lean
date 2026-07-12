import Mathlib
import SmoothManifolds_Lee_2012.Chap02.Sec02_11.Proposition_2_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- `lean_leansearch` was unavailable in this session; the statement uses mathlib's canonical
-- smooth-section language `CMDiff[s] n (T% X)` and `Cₛ^∞⟮I; E, TangentSpace I⟯`.

universe uE uH uM

noncomputable section

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  [IsManifold I (∞ : ℕ∞ω) M] [T2Space M] [SigmaCompactSpace M]

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, TangentSpace I⟯

/-- Local smooth extension data for a vector field prescribed on a subset. -/
structure ContMDiffVectorFieldLocalExtension
    {A : Set M} (X : ∀ x : A, TangentSpace I (x : M)) (x : A) where
  V : Set M
  isOpen_V : IsOpen V
  mem_V : (x : M) ∈ V
  Xloc : ∀ y : M, TangentSpace I y
  contMDiffOn : CMDiff[V] (∞ : ℕ∞ω) (T% Xloc)
  eq_source : ∀ y : A, (y : M) ∈ V → Xloc y = X y

/-- A global smooth vector field extends the prescribed field and has support contained in `U`. -/
class IsSupportedContMDiffVectorFieldExtension
    {A : Set M} (X : ∀ x : A, TangentSpace I (x : M)) (U : Set M)
    (Xtilde : ∀ x : M, TangentSpace I x) : Prop where
  contMDiff : CMDiff (∞ : ℕ∞ω) (T% Xtilde)
  eq_source : ∀ x : A, Xtilde x = X x
  support_subset : closure {x : M | Xtilde x ≠ 0} ⊆ U

/-- Lemma 8.6 (Extension Lemma for Vector Fields): encoding a smooth vector field along the closed
subset `A` by a section `X : ∀ x : A, TangentSpace I (x : M)` together with smooth local
extensions near points of `A`, any open neighborhood `U` of `A` admits a global smooth vector
field extending `X` whose support is contained in `U`, written here as
`closure {x | X̃ x ≠ 0} ⊆ U`. -/
theorem exists_supported_contMDiff_vectorField_extension_of_isClosed
    {A U : Set M} (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U)
    (X : ∀ x : A, TangentSpace I (x : M))
    (hX : ∀ x : A, ContMDiffVectorFieldLocalExtension X x) :
    ∃ Xtilde : ∀ x : M, TangentSpace I x,
      IsSupportedContMDiffVectorFieldExtension X U Xtilde := by
  classical
  let t : ∀ x : M, Set (TangentSpace I x) :=
    fun x ↦ if hx : x ∈ A then ({X ⟨x, hx⟩} : Set (TangentSpace I x)) else Set.univ
  -- The prescribed fiber set is convex: a singleton above `A`, and unconstrained away from `A`.
  have htConv : ∀ x : M, Convex ℝ (t x) := by
    intro x
    by_cases hx : x ∈ A
    · simp [t, hx]
    · simpa [t, hx] using (convex_univ : Convex ℝ (Set.univ : Set (TangentSpace I x)))
  -- Near `A`, use the given local extensions; away from `A`, use the zero vector field on `Aᶜ`.
  have hLocal :
      ∀ x₀ : M, ∃ U_x₀ ∈ nhds x₀, ∃ s_loc : (x : M) → TangentSpace I x,
        CMDiff[U_x₀] (∞ : ℕ∞ω) (T% s_loc) ∧ ∀ y ∈ U_x₀, s_loc y ∈ t y := by
    intro x₀
    by_cases hx₀ : x₀ ∈ A
    · let data := hX ⟨x₀, hx₀⟩
      refine ⟨data.V, data.isOpen_V.mem_nhds data.mem_V, data.Xloc, data.contMDiffOn, ?_⟩
      intro y hyV
      by_cases hyA : y ∈ A
      · have hyEq : data.Xloc y = X ⟨y, hyA⟩ := data.eq_source ⟨y, hyA⟩ hyV
        simp [t, hyA, hyEq]
      · simp [t, hyA]
    · refine ⟨Aᶜ, hA.isOpen_compl.mem_nhds hx₀, fun y ↦ 0, ?_, ?_⟩
      · simpa using ((0 : SmoothVectorField).contMDiff.contMDiffOn (s := Aᶜ))
      · intro y hy
        simp [t, show y ∉ A from hy]
  -- Globalize the local constrained sections to a smooth section with the prescribed values on `A`.
  obtain ⟨Y, hYmem⟩ :=
    exists_contMDiffSection_forall_mem_convex_of_local (I := I) (V := TangentSpace I) t htConv
      hLocal
  have hYeq : ∀ x : A, Y x = X x := by
    intro x
    simpa [t, x.property] using hYmem (x : M)
  -- Cut the global section off inside `U` with a smooth bump function equal to `1` on `A`.
  obtain ⟨ψ, _hψrange, hψeq, hψsupport⟩ :=
    exists_smooth_bump_function_for (I := I) hA hU hAU
  let Xtilde : ∀ x : M, TangentSpace I x := fun x ↦ ψ x • Y x
  refine ⟨Xtilde, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Smoothness comes from smooth scalar multiplication of the bump function and the section.
    simpa [Xtilde] using ψ.contMDiff.smul_section Y.contMDiff
  · -- On `A`, the bump function is `1`, so the cutoff field still agrees with the prescribed one.
    intro x
    have hψx : ψ x = 1 := hψeq x.property
    simpa [Xtilde, hψx] using hYeq x
  · -- The support of `ψ • Y` is contained in the support of `ψ`, hence in `U`.
    simpa [Xtilde, tsupport, Function.support] using
      (tsupport_smul_subset_left ψ (fun x ↦ Y x)).trans hψsupport
