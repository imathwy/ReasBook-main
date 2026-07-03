import Mathlib
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing
open scoped Pointwise TensorProduct

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 10.106.5: if one chooses lifts in `M` of a basis of `M / x M`, then the
induced map on the quotients of the free module is a bijection. -/
private theorem quotSMulTop_map_bijective_of_basis_lifts
    {ι : Type*} [Finite ι] {x : R}
    (b : Module.Basis ι (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M))
    (v : ι → M)
    (hv : ∀ i, (Submodule.Quotient.mk (v i) : QuotSMulTop x M) = b i) :
    Function.Bijective (QuotSMulTop.map x (Finsupp.linearCombination R v)) := by
  -- TODO: express `QuotSMulTop x (ι →₀ R)` as `ι →₀ (R ⧸ (x))` through the tensor-model
  -- equivalence and show the induced map is `b.repr.symm`.
  sorry

/-- Helper for Lemma 10.106.5: lifts of a basis of `M / x M` generate `M`. -/
private theorem span_eq_top_of_basis_lifts
    {ι : Type*} [Finite ι] {x : R} (hx : x ∈ maximalIdeal R)
    (b : Module.Basis ι (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M))
    (v : ι → M)
    (hv : ∀ i, (Submodule.Quotient.mk (v i) : QuotSMulTop x M) = b i) :
    Submodule.span R (Set.range v) = ⊤ := by
  -- TODO: lift the quotient-basis coefficients from `R ⧸ (x)` back to `R` and apply
  -- Nakayama clause (8) to the finite set of chosen lifts.
  sorry

/- 
Layering for this item:
- `source-facing`: the Stacks hypothesis that `R` is Noetherian local, `M` is finite, `x` is
  `M`-regular, and the quotient `QuotSMulTop x M` is free over `R ⧸ (x)`;
- `core/canonical`: the owner objects `QuotSMulTop x M`, `IsSMulRegular M x`,
  `Module.FinitePresentation R M`, and the local-ring freeness machinery in
  `Mathlib.RingTheory.LocalRing.Module`;
- `bridge/view`: Noetherianity plus `Module.Finite R M` only serve to supply the canonical finite
  presentation instance `Module.finitePresentation_of_finite R M`.
-/

-- Proof sketch: choose lifts in `M` of a basis of `QuotSMulTop x M` over `R ⧸ (x)`,
-- obtaining a surjection
-- `R^n → M` by Nakayama. Any relation among the lifts has coefficients in `xR`; divide by `x` and
-- use that `x` is a nonzerodivisor on `M` to show the kernel `K` satisfies `xK = K`, hence
-- `K = 0` by Nakayama's lemma.
private theorem free_of_isSMulRegular_of_free_quotSMulTop_of_finitePresentation
    [Module.FinitePresentation R M] {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    [Module.Free (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    Module.Free R M := by
  classical
  let I : Ideal R := Ideal.span ({x} : Set R)
  let b : Module.Basis (Module.Free.ChooseBasisIndex (R ⧸ I) (QuotSMulTop x M)) (R ⧸ I)
      (QuotSMulTop x M) := Module.Free.chooseBasis (R ⧸ I) (QuotSMulTop x M)
  let ι := Module.Free.ChooseBasisIndex (R ⧸ I) (QuotSMulTop x M)
  -- TODO: identify the canonical `(R ⧸ I)`-module structure on `QuotSMulTop x M` with the one
  -- used by `Module.Free`, then derive finiteness of the chosen basis index from
  -- `Module.Finite R (QuotSMulTop x M)`.
  haveI : Finite ι := by
    sorry
  choose v hv using fun i : ι ↦
    Submodule.mkQ_surjective (x • (⊤ : Submodule R M)) (b i)
  let π : (ι →₀ R) →ₗ[R] M := Finsupp.linearCombination R v
  have hquot_bij :
      Function.Bijective (QuotSMulTop.map x π) :=
    quotSMulTop_map_bijective_of_basis_lifts (b := b) (v := v) hv
  have hspan : Submodule.span R (Set.range v) = ⊤ :=
    span_eq_top_of_basis_lifts hx (b := b) (v := v) hv
  have hπ : Function.Surjective π := by
    -- The lifts generate `M`, so the free cover `π` is surjective.
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    simpa [π] using hspan
  let K : Submodule R (ι →₀ R) := LinearMap.ker π
  have hK_le_x_top : K ≤ x • (⊤ : Submodule R (ι →₀ R)) := by
    intro l hl
    have hzero : QuotSMulTop.map x π (Submodule.Quotient.mk l) = 0 := by
      have hπl : π l = 0 := by
        simpa [K, LinearMap.mem_ker] using hl
      simpa [QuotSMulTop.map_apply_mk, hπl]
    have hmk :
        (Submodule.Quotient.mk l : QuotSMulTop x (ι →₀ R)) = 0 :=
      hquot_bij.1 hzero
    exact (Submodule.Quotient.mk_eq_zero _).1 hmk
  have hquot_reg : IsSMulRegular ((ι →₀ R) ⧸ K) x := by
    -- Transport regularity across the quotient isomorphism coming from `π`.
    exact ((LinearMap.quotKerEquivOfSurjective π hπ).isSMulRegular_congr x).2 hreg
  have hK_inf : x • (⊤ : Submodule R (ι →₀ R)) ⊓ K ≤ x • K := by
    -- This is the formal “divide the relation by `x`” step.
    exact smul_top_inf_eq_smul_of_isSMulRegular_on_quot hquot_reg
  have hK_le_xK : K ≤ x • K := by
    intro l hl
    exact hK_inf ⟨hK_le_x_top hl, hl⟩
  have hK_finite : Module.Finite R K :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker π hπ)
  let _ : Module.Finite R K := hK_finite
  have hK_smul_top : I • (⊤ : Submodule R K) = ⊤ := by
    -- Reinterpret `K ≤ xK` as `IK = K` inside the submodule `K`.
    refine top_unique ?_
    intro k hk
    rw [Submodule.mem_smul_top_iff I K]
    simpa [I, Submodule.ideal_span_singleton_smul] using hK_le_xK k.2
  have hIjac : I ≤ Ring.jacobson R := by
    -- In a local ring, `(x)` is contained in the Jacobson radical.
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal R]
    exact (Ideal.span_singleton_le_iff_mem (maximalIdeal R)).2 hx
  have hK_subsingleton : Subsingleton K :=
    subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson (I := I) hK_smul_top hIjac
  have hK_bot : K = ⊥ := (Submodule.subsingleton_iff_eq_bot).1 hK_subsingleton
  have hπ_injective : Function.Injective π := (LinearMap.ker_eq_bot).1 hK_bot
  let e : (ι →₀ R) ≃ₗ[R] M := LinearEquiv.ofBijective π ⟨hπ_injective, hπ⟩
  -- The resulting linear equivalence transports the standard basis of the free module to `M`.
  exact Module.Free.of_basis (Finsupp.basisSingleOne.map e)

/-- Lemma 10.106.5: if `R` is a Noetherian local ring, `x ∈ maximalIdeal R` is a nonzerodivisor on
a finite `R`-module `M`, and `M / xM`, written as `QuotSMulTop x M`, is free over
`R ⧸ Ideal.span {x}`, then `M` is free over `R`. -/
theorem free_of_isSMulRegular_of_free_quotSMulTop
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    [Module.Free (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    Module.Free R M := by
  let _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact free_of_isSMulRegular_of_free_quotSMulTop_of_finitePresentation hx hreg

end
