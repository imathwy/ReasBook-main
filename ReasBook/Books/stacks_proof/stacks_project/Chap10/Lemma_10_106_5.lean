import Mathlib
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_77_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing
open scoped Pointwise TensorProduct

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 10.106.5: the usual `R`-action on `QuotSMulTop x M` is the restriction of
the quotient-ring action through `R → R ⧸ (x)`. -/
private instance quotSMulTop_isScalarTower_quotient (x : R) :
    IsScalarTower R (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M) := by
  -- Proof comment: reduce quotient scalars and quotient-module elements to representatives.
  refine ⟨?_⟩
  intro r c q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (x • (⊤ : Submodule R M)) q
  simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  rw [← map_mul]
  have hleft :
      ((Ideal.Quotient.mk (Ideal.span ({x} : Set R)) (r * s) :
          R ⧸ Ideal.span ({x} : Set R)) •
        ((x • (⊤ : Submodule R M)).mkQ m : QuotSMulTop x M)) =
        (r * s) • ((x • (⊤ : Submodule R M)).mkQ m : QuotSMulTop x M) := rfl
  have hright :
      ((Ideal.Quotient.mk (Ideal.span ({x} : Set R)) s :
          R ⧸ Ideal.span ({x} : Set R)) •
        ((x • (⊤ : Submodule R M)).mkQ m : QuotSMulTop x M)) =
        s • ((x • (⊤ : Submodule R M)).mkQ m : QuotSMulTop x M) := rfl
  rw [hleft, hright, mul_smul]

/-- Helper for Lemma 10.106.5: reducing a finitely supported free module modulo `x` is the same
as reducing every coefficient modulo `(x)`. -/
private noncomputable def quotSMulTopFinsuppEquiv (x : R) (ι : Type*) :
    QuotSMulTop x (ι →₀ R) ≃ₗ[R] ι →₀ (R ⧸ Ideal.span ({x} : Set R)) :=
  (Submodule.quotEquivOfEq
      (x • (⊤ : Submodule R (ι →₀ R)))
      (Ideal.span ({x} : Set R) • (⊤ : Submodule R (ι →₀ R)))
      (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R (ι →₀ R))).symm).trans <|
    (Submodule.quotEquivOfEq
        (Ideal.span ({x} : Set R) • (⊤ : Submodule R (ι →₀ R)))
        (LinearMap.ker
          (finsupp_quotientMapLinear (R := R) (I := Ideal.span ({x} : Set R)) ι))
        (finsupp_quotientMap_ker_eq_ideal_smul_top
          (R := R) (I := Ideal.span ({x} : Set R)) (ι := ι)).symm).trans <|
      LinearMap.quotKerEquivOfSurjective
        (finsupp_quotientMapLinear (R := R) (I := Ideal.span ({x} : Set R)) ι)
          (finsupp_quotientMap_surjective
            (R := R) (I := Ideal.span ({x} : Set R)) ι)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.106.5: the coefficientwise quotient equivalence sends a quotient class to
the coefficientwise reduced finitely supported vector. -/
private lemma quotSMulTopFinsuppEquiv_apply_mk
    {ι : Type*} (x : R) (l : ι →₀ R) :
    quotSMulTopFinsuppEquiv (R := R) x ι (Submodule.Quotient.mk l) =
      finsupp_quotientMapLinear (R := R) (I := Ideal.span ({x} : Set R)) ι l := by
  -- Proof comment: both equivalence steps are built from the same quotient representative.
  simp [quotSMulTopFinsuppEquiv]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 10.106.5: the inverse coefficientwise quotient equivalence sends a reduced
finitely supported vector back to the class of any chosen lift. -/
private lemma quotSMulTopFinsuppEquiv_symm_apply_quotientMap
    {ι : Type*} (x : R) (l : ι →₀ R) :
    (quotSMulTopFinsuppEquiv (R := R) x ι).symm
      (finsupp_quotientMapLinear (R := R) (I := Ideal.span ({x} : Set R)) ι l) =
        Submodule.Quotient.mk l := by
  -- Proof comment: rewrite through the forward representative formula and cancel the equivalence.
  rw [← quotSMulTopFinsuppEquiv_apply_mk (R := R) x l]
  exact (quotSMulTopFinsuppEquiv (R := R) x ι).symm_apply_apply _

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.106.5: after coefficientwise reduction, the free cover determined by
lifts of a quotient basis becomes the basis linear-combination map. -/
private lemma quotSMulTop_linearCombination_comp_finsuppEquiv
    {ι : Type*} {x : R}
    (b : Module.Basis ι (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M))
    (v : ι → M)
    (hv : ∀ i, (Submodule.Quotient.mk (v i) : QuotSMulTop x M) = b i) :
    (QuotSMulTop.map x (Finsupp.linearCombination R v)).comp
        (quotSMulTopFinsuppEquiv (R := R) x ι).symm.toLinearMap =
      (Finsupp.linearCombination (R ⧸ Ideal.span ({x} : Set R)) b).restrictScalars R := by
  -- Proof comment: evaluate on coefficientwise quotient representatives and reduce both sides
  -- to the same finite sum in the quotient module.
  let I : Ideal R := Ideal.span ({x} : Set R)
  let qM : M →ₗ[R] QuotSMulTop x M := Submodule.mkQ (x • (⊤ : Submodule R M))
  let vbar : ι → QuotSMulTop x M := fun i => qM (v i)
  let lcQ : (ι →₀ (R ⧸ I)) →ₗ[R ⧸ I] QuotSMulTop x M :=
    Finsupp.linearCombination (R ⧸ I) vbar
  apply LinearMap.ext
  intro z
  obtain ⟨l, rfl⟩ := finsupp_quotientMap_surjective (R := R) (I := I) ι z
  have hmk :
      (quotSMulTopFinsuppEquiv (R := R) x ι).symm
        (finsupp_quotientMapLinear (R := R) (I := I) ι l) =
          Submodule.Quotient.mk l := by
    simpa [I] using
      quotSMulTopFinsuppEquiv_symm_apply_quotientMap (R := R) x l
  calc
    (QuotSMulTop.map x (Finsupp.linearCombination R v))
        ((quotSMulTopFinsuppEquiv (R := R) x ι).symm
          (finsupp_quotientMapLinear (R := R) (I := I) ι l)) =
        (Submodule.Quotient.mk (Finsupp.linearCombination R v l) :
          QuotSMulTop x M) := by
      rw [hmk]
      simp [QuotSMulTop.map_apply_mk]
    _ = ((Finsupp.linearCombination (R ⧸ Ideal.span ({x} : Set R)) b).restrictScalars R)
          (finsupp_quotientMapLinear (R := R) (I := I) ι l) := by
      have hreduce :
          (Submodule.Quotient.mk (Finsupp.linearCombination R v l) :
            QuotSMulTop x M) =
              (lcQ.restrictScalars R)
                (finsupp_quotientMapLinear (R := R) (I := I) ι l) := by
        calc
          (Submodule.Quotient.mk (Finsupp.linearCombination R v l) :
              QuotSMulTop x M) =
                Finsupp.linearCombination R vbar l := by
            simpa [qM, vbar] using
              (Finsupp.apply_linearCombination
                (R := R)
                (f := qM)
                (v := v) l)
          _ = (lcQ.restrictScalars R)
                (finsupp_quotientMapLinear (R := R) (I := I) ι l) := by
            change _ = (finsupp_quotientMapLinear (R := R) (I := I) ι l).sum
              (fun i a => a • vbar i)
            rw [Finsupp.linearCombination_apply]
            calc
              l.sum (fun i a => a • vbar i) =
                  l.sum (fun i a => ((Ideal.Quotient.mk I) a : R ⧸ I) • vbar i) := by
                refine Finsupp.sum_congr ?_
                intro i hi
                exact ideal_scalar_action_eq_quotient_scalar_action
                  (R := R) (I := I) (N := QuotSMulTop x M) (l i) (vbar i)
              _ = (finsupp_quotientMapLinear (R := R) (I := I) ι l).sum
                    (fun i a => a • vbar i) := by
                have hzero : ∀ i : ι, (0 : R ⧸ I) • vbar i = 0 :=
                  fun i => zero_smul (R ⧸ I) (vbar i)
                simpa [finsupp_quotientMapLinear] using
                  (Finsupp.sum_mapRange_index (g := l) (h := fun i a => a • vbar i)
                    hzero).symm
      simpa [I, qM, vbar, lcQ, hv] using hreduce

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.106.5: if one chooses lifts in `M` of a basis of `M / x M`, then the
induced map on the quotients of the free module is a bijection. -/
private lemma quotSMulTop_map_bijective_of_basis_lifts
    {ι : Type*} [Finite ι] {x : R}
    (b : Module.Basis ι (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M))
    (v : ι → M)
    (hv : ∀ i, (Submodule.Quotient.mk (v i) : QuotSMulTop x M) = b i) :
    Function.Bijective (QuotSMulTop.map x (Finsupp.linearCombination R v)) := by
  -- Proof comment: compose with the coefficientwise quotient equivalence so the map is the
  -- inverse coordinate map of the chosen quotient basis.
  let e := quotSMulTopFinsuppEquiv (R := R) x ι
  have hcover :
      (QuotSMulTop.map x (Finsupp.linearCombination R v)).comp e.symm.toLinearMap =
        (Finsupp.linearCombination (R ⧸ Ideal.span ({x} : Set R)) b).restrictScalars R :=
    quotSMulTop_linearCombination_comp_finsuppEquiv (R := R) (M := M) b v hv
  have hbasis_linear :
      (Finsupp.linearCombination (R ⧸ Ideal.span ({x} : Set R)) b).restrictScalars R =
        (LinearEquiv.restrictScalars R b.repr.symm).toLinearMap := by
    -- Proof comment: a basis linear-combination map is the inverse of the coordinate map.
    ext l
    simp [b.repr_symm_apply]
  have hcover_bij :
      Function.Bijective
        (((QuotSMulTop.map x (Finsupp.linearCombination R v)).comp e.symm.toLinearMap)) := by
    rw [hcover, hbasis_linear]
    exact (LinearEquiv.restrictScalars R b.repr.symm).bijective
  refine ⟨?_, ?_⟩
  · intro a b' hab
    -- Proof comment: compare images after applying the source quotient equivalence.
    apply e.injective
    apply hcover_bij.1
    simpa [e] using hab
  · intro y
    -- Proof comment: lift through the bijective composite and move the lift back across `e`.
    obtain ⟨z, hz⟩ := hcover_bij.2 y
    refine ⟨e.symm z, ?_⟩
    simpa [e] using hz

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.106.5: lifts of a basis of `M / x M` generate `M`. -/
private lemma span_eq_top_of_basis_lifts
    {ι : Type*} [Finite ι] {x : R} (hx : x ∈ maximalIdeal R)
    (b : Module.Basis ι (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M))
    (v : ι → M)
    (hv : ∀ i, (Submodule.Quotient.mk (v i) : QuotSMulTop x M) = b i) :
    Submodule.span R (Set.range v) = ⊤ := by
  classical
  -- Proof comment: first show the quotient images of the chosen lifts span the quotient module.
  let I : Ideal R := Ideal.span ({x} : Set R)
  have hbspanR : Submodule.span R (Set.range b) = ⊤ := by
    calc
      Submodule.span R (Set.range b) =
          (Submodule.span (R ⧸ I) (Set.range b)).restrictScalars R := by
        rw [Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective]
      _ = ⊤ := by
        simp [I, b.span_eq]
  have hquotSet :
      (Submodule.mkQ (x • (⊤ : Submodule R M))) '' Set.range v = Set.range b := by
    ext q
    constructor
    · rintro ⟨m, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hv i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, hv i⟩
  have hquotSpanX :
      Submodule.span R ((Submodule.mkQ (x • (⊤ : Submodule R M))) '' Set.range v) = ⊤ := by
    rw [hquotSet]
    exact hbspanR
  letI : Fintype ι := Fintype.ofFinite ι
  let s : Finset M := Finset.univ.image v
  have hs : (s : Set M) = Set.range v := by
    ext m
    simp [s]
  have hquotSpanI :
      Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' (s : Set M)) = ⊤ := by
    have hI_top : I • (⊤ : Submodule R M) = x • (⊤ : Submodule R M) := by
      simpa [I] using
        (Submodule.ideal_span_singleton_smul x (⊤ : Submodule R M))
    rw [hI_top, hs]
    exact hquotSpanX
  have hIjac : I ≤ Ring.jacobson R := by
    -- Proof comment: in a local ring, the principal ideal generated by `x` lies in the Jacobson
    -- radical because `x` lies in the maximal ideal.
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal R]
    exact (Ideal.span_singleton_le_iff_mem (maximalIdeal R)).2 hx
  have hspan_s : Submodule.span R (s : Set M) = ⊤ :=
    span_eq_top_of_quotient_span_eq_top_of_le_ring_jacobson (I := I) s hquotSpanI hIjac
  -- Proof comment: the finite set `s` has exactly the same carrier as the chosen lift range.
  simpa [hs] using hspan_s

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
omit [IsNoetherianRing R] in
private theorem free_of_isSMulRegular_of_free_quotSMulTop_of_finitePresentation
    [Module.FinitePresentation R M] {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    [Module.Free (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    Module.Free R M := by
  classical
  let I : Ideal R := Ideal.span ({x} : Set R)
  let b : Module.Basis (Module.Free.ChooseBasisIndex (R ⧸ I) (QuotSMulTop x M)) (R ⧸ I)
      (QuotSMulTop x M) := Module.Free.chooseBasis (R ⧸ I) (QuotSMulTop x M)
  let ι := Module.Free.ChooseBasisIndex (R ⧸ I) (QuotSMulTop x M)
  -- Proof comment: the quotient of a finite module is finite over `R`, hence finite over the
  -- quotient ring, so the chosen free basis has finite index.
  letI : Finite ι := by
    have hquotFiniteR : Module.Finite R (QuotSMulTop x M) :=
      Module.Finite.of_surjective
        (Submodule.mkQ (x • (⊤ : Submodule R M)))
        (Submodule.mkQ_surjective _)
    let _ : Module.Finite R (QuotSMulTop x M) := hquotFiniteR
    have hquotFiniteI : Module.Finite (R ⧸ I) (QuotSMulTop x M) :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ I) (QuotSMulTop x M)
    let _ : Module.Finite (R ⧸ I) (QuotSMulTop x M) := hquotFiniteI
    let _ : Fintype ι := Module.Free.ChooseBasisIndex.fintype
      (R ⧸ I) (QuotSMulTop x M)
    infer_instance
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

/-- Chap10 Lemma 10 106 5: if `R` is a Noetherian local ring, `x ∈ maximalIdeal R` is a nonzerodivisor on
a finite `R`-module `M`, and `M / xM`, written as `QuotSMulTop x M`, is free over
`R ⧸ Ideal.span {x}`, then `M` is free over `R`. -/
@[stacks 00NS]
theorem free_of_isSMulRegular_of_free_quotSMulTop
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    [Module.Free (R ⧸ Ideal.span ({x} : Set R)) (QuotSMulTop x M)] :
    Module.Free R M := by
  let _ : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  exact free_of_isSMulRegular_of_free_quotSMulTop_of_finitePresentation hx hreg

end
