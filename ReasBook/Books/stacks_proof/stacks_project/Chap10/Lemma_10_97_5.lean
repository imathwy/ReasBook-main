import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_96_12
import stacks_proof.stacks_project.Chap10.Lemma_10_150_6.AssociatedGradedAPI
import stacks_proof.stacks_project.Chap10.Lemma_10_97_5.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

-- Domain-style sampling:
-- * primary domain: adic completions of commutative rings, with Noetherianity and adic
--   completeness for the extended ideal on the completion.
-- * layer: `source-facing`; the theorem keeps the textbook criterion while reusing the canonical
--   owner ring `AdicCompletion I R` and the owner predicate `IsAdicComplete`.
-- * sampled declarations:
--   `AdicCompletion.isAdicComplete`,
--   `IsAdicComplete.map_algebraMap_iff`,
--   `AdicCompletion.evalOneₐ`,
--   `isNoetherianRing_iff_ideal_fg`.
-- * owner abstraction: `AdicCompletion I R`; the extended ideal
--   `I.map (algebraMap R (AdicCompletion I R))` is derived from that owner, not extra primitive
--   data.
-- * primitive data: the ideal `I`, the quotient hypothesis `[IsNoetherianRing (R ⧸ I)]`, and the
--   finite-generation input `hI`.
-- * derived API: Noetherianity of the completion ring and completeness for the extended ideal.
--
-- Proof sketch: use finite generation of `I` to obtain `I`-adic completeness of
-- `AdicCompletion I R`, then transport it to the extended ideal via
-- `IsAdicComplete.map_algebraMap_iff`. For noetherianity, combine the quotient identification
-- `(AdicCompletion I R) ⧸ I.map (algebraMap R (AdicCompletion I R)) ≃+* R ⧸ I`
-- with finite generation of the extended ideal and the standard criterion that a ring is
-- noetherian when a finitely generated ideal has noetherian quotient.
variable [IsNoetherianRing (R ⧸ I)]

/-- Helper for Lemma 10.97.5: an element of the `n`-th `K`-adic stage gives a degree-`n`
monomial in the quotient-Rees presentation of the associated graded ring. -/
private theorem ideal_associated_graded_stage_monomial_mem
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    Polynomial.monomial n (x : S) ∈ reesAlgebra K := by
  -- The stage condition is exactly the coefficient condition for a Rees monomial.
  apply reesAlgebra.monomial_mem.mpr
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using x.2

/-- Helper for Lemma 10.97.5: the degree-`n` class of a stage element in the quotient-Rees model
of `gr_K(S)`. -/
private noncomputable def idealAssociatedGradedStageClass
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K S n → idealAssociatedGradedRing K :=
  fun x ↦
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
      ⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩

/-- Helper for Lemma 10.97.5: use the canonical quotient-ring structure on the quotient-Rees
model of the associated graded ring, avoiding slower instance search through local wrappers. -/
noncomputable local instance idealAssociatedGradedRing_commRing
    {S : Type u} [CommRing S] (K : Ideal S) :
    CommRing (idealAssociatedGradedRing K) :=
  Ideal.Quotient.commRing (Ideal.map (algebraMap S (reesAlgebra K)) K)

/-- Helper for Lemma 10.97.5: use the canonical quotient algebra structure over `S ⧸ K` on the
quotient-Rees model of the associated graded ring. -/
noncomputable local instance idealAssociatedGradedRing_algebraQuotient
    {S : Type u} [CommRing S] (K : Ideal S) :
    Algebra (S ⧸ K) (idealAssociatedGradedRing K) :=
  Ideal.Quotient.algebraQuotientMapQuotient

/-- Helper for Lemma 10.97.5: the degree-`n` monomial representative of a stage element belongs
to the degree-`n` part of the Rees algebra. -/
private theorem ideal_associated_graded_stage_mem_grade
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    (⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩ :
      reesAlgebra K) ∈ reesAlgebraGrade K n := by
  -- The chosen monomial already has the canonical degree-`n` shape defining `reesAlgebraGrade`.
  refine ⟨⟨(x : S), ?_⟩, rfl⟩
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using x.2

/-- Helper for Lemma 10.97.5: the stage class map lands in the degree-`n` owner piece of the
associated graded ring. -/
private theorem idealAssociatedGradedStageClass_mem_grade
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K n x ∈ idealAssociatedGradedRingGrade K n := by
  -- The owner-grade witness is exactly the degree-`n` monomial representative used to define the
  -- stage class.
  refine ⟨⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩,
    ideal_associated_graded_stage_mem_grade K n x, rfl⟩

/-- Helper for Lemma 10.97.5: the monomial stage construction is linear before passing to the
associated graded quotient. -/
private noncomputable def idealAssociatedGradedStageToReesLinear
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K S n →ₗ[S] reesAlgebra K :=
  LinearMap.codRestrict ((reesAlgebra K).toSubmodule)
    ((Polynomial.monomial n).comp (show
      RingTheory.Sequence.idealAssociatedGradedStage K S n →ₗ[S] S from
        (RingTheory.Sequence.idealAssociatedGradedStage K S n).subtype))
    (fun x ↦ ideal_associated_graded_stage_monomial_mem K n x)

/-- Helper for Lemma 10.97.5: the linear stage map to the owner ring lands in the degree-`n`
owner subtype. -/
private noncomputable def idealAssociatedGradedStageClassLinear
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K S n →ₗ[S] idealAssociatedGradedRingGrade K n :=
  LinearMap.codRestrict (idealAssociatedGradedRingGrade K n)
    (((Ideal.Quotient.mkₐ S (Ideal.map (algebraMap S (reesAlgebra K)) K)).toLinearMap).comp
      (idealAssociatedGradedStageToReesLinear K n))
    (fun x ↦ by
      simpa [idealAssociatedGradedStageToReesLinear, idealAssociatedGradedStageClass,
        LinearMap.comp_apply] using idealAssociatedGradedStageClass_mem_grade K n x)

/-- Helper for Lemma 10.97.5: the linear stage-to-grade map agrees with the stage-class map after
forgetting the grade subtype. -/
private theorem idealAssociatedGradedStageClassLinear_apply
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    ((idealAssociatedGradedStageClassLinear K n x :
      idealAssociatedGradedRingGrade K n) : idealAssociatedGradedRing K) =
      idealAssociatedGradedStageClass K n x := by
  -- Compare both definitions on the common Rees representative before passing to the quotient.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        ((idealAssociatedGradedStageToReesLinear K n) x) =
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        ⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩
  congr 1

/-- Helper for Lemma 10.97.5: every element of the degree-`n` owner piece is represented by a
stage element in `K ^ n`. -/
private theorem idealAssociatedGradedStageClassLinear_surjective
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    Function.Surjective (idealAssociatedGradedStageClassLinear K n) := by
  intro x
  rcases x.2 with ⟨y, hy, hxy⟩
  rcases hy with ⟨a, rfl⟩
  refine ⟨⟨a.1, ?_⟩, ?_⟩
  · -- A homogeneous Rees generator in degree `n` is exactly an element of `K ^ n`.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using a.2
  · -- The representative is already the canonical monomial image of that stage element.
    exact Subtype.ext <| by
      simpa [idealAssociatedGradedStageClassLinear, idealAssociatedGradedStageToReesLinear] using hxy

/-- Helper for Lemma 10.97.5: a finitely generated ideal can be reindexed by a finite `Fin`
family of generators. -/
private theorem exists_fin_generating_family_of_ideal
    {S : Type u} [CommRing S] (K : Ideal S) (hK : K.FG) :
    ∃ t : ℕ, ∃ g : Fin t → K, Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K := by
  classical
  let s : Finset S := (Submodule.FG.finite_generators hK).toFinset
  have hs_generators : (s : Set S) = K.generators := by
    exact (Submodule.FG.finite_generators hK).coe_toFinset
  have hmem_generators : K.generators ⊆ K := Submodule.FG.generators_mem (p := K)
  let g : Fin s.card → K := fun i ↦
    ⟨((Finset.equivFin s).symm i : S), by
      have hi : (((Finset.equivFin s).symm i : s) : S) ∈ (s : Set S) := ((Finset.equivFin s).symm i).2
      rw [hs_generators] at hi
      exact hmem_generators hi⟩
  have hrange : Set.range (fun i ↦ ((g i : K) : S)) = (s : Set S) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Finset.equivFin s).symm i).2
    · intro hx
      refine ⟨(Finset.equivFin s) ⟨x, hx⟩, ?_⟩
      simpa [g] using congrArg Subtype.val ((Finset.equivFin s).symm_apply_apply ⟨x, hx⟩)
  refine ⟨s.card, g, ?_⟩
  calc
    Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = Ideal.span (s : Set S) := by rw [hrange]
    _ = K := by simpa [hs_generators] using K.span_generators

/-- Helper for Lemma 10.97.5: once generators `g` of `K` are fixed, the source proof identifies
`K ^ n` with the span of the degree-`n` monomial weights in those generators. -/
private lemma ideal_pow_eq_span_monomial_weight_of_generators
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K) (n : ℕ) :
    K ^ n =
      Ideal.span ((fun e : Fin t →₀ ℕ =>
        ∏ i : Fin t, ((g i : K) : S) ^ e i) '' {e | e.degree = n}) := by
  -- Rewrite the power of `K` through the chosen generators before invoking the standard
  -- `Finsupp`-product description of powers of a span.
  calc
    K ^ n = (Ideal.span (Set.range fun i ↦ ((g i : K) : S))) ^ n := by rw [hgspan]
    _ = Ideal.span ((fun e : Fin t →₀ ℕ => ∏ i : Fin t, ((g i : K) : S) ^ e i) '' {e | e.degree = n}) := by
      rw [Ideal.span, Submodule.span_pow, ← Set.image_univ,
        Finsupp.image_pow_eq_finsuppProd_image]
      simp

/-- Helper for Lemma 10.97.5: every monomial weight in the chosen generators lies in the matching
power of `K`. -/
private lemma monomial_weight_mem_ideal_pow_of_generators
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K)
    (e : Fin t →₀ ℕ) :
    (∏ i : Fin t, ((g i : K) : S) ^ e i) ∈ K ^ e.degree := by
  -- Place the chosen monomial in the span description of `K ^ e.degree`.
  rw [ideal_pow_eq_span_monomial_weight_of_generators K g hgspan e.degree]
  exact Ideal.subset_span ⟨e, by simp⟩

/-- Helper for Lemma 10.97.5: after choosing generators of `K`, the source polynomial algebra
maps to `gr_K(S)` by sending `X i` to the degree-one class of the `i`-th generator. -/
private noncomputable def associated_graded_presentation
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K) :
    MvPolynomial (Fin t) (S ⧸ K) →ₐ[S ⧸ K] idealAssociatedGradedRing K :=
  MvPolynomial.aeval fun i ↦ idealAssociatedGradedDegreeOne (g i)

/-- Helper for Lemma 10.97.5: the presentation map sends each polynomial variable to the chosen
degree-one generator class in the associated graded ring. -/
private lemma associated_graded_presentation_X
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K) (i : Fin t) :
    associated_graded_presentation K g (MvPolynomial.X i) =
      idealAssociatedGradedDegreeOne (g i) := by
  -- The evaluation map is defined precisely to realize the source presentation on variables.
  simp [associated_graded_presentation]

/-- Helper for Lemma 10.97.5: once the source polynomial presentation
`(S ⧸ K)[T_1, ..., T_t] ↠ gr_K(S)` is constructed, Noetherianity of the associated graded ring
follows formally by surjectivity. -/
private lemma associated_graded_isNoetherian_of_surjective_mvPolynomial
    {S : Type u} [CommRing S] (K : Ideal S) [IsNoetherianRing (S ⧸ K)]
    {t : ℕ}
    (φ : MvPolynomial (Fin t) (S ⧸ K) →ₐ[S ⧸ K] idealAssociatedGradedRing K)
    (hφ : Function.Surjective φ) :
    IsNoetherianRing (idealAssociatedGradedRing K) := by
  -- The source polynomial algebra is Noetherian over the Noetherian coefficient ring `S ⧸ K`.
  letI : IsNoetherianRing (MvPolynomial (Fin t) (S ⧸ K)) := inferInstance
  -- Surjective maps preserve Noetherianity, so the remaining work is exactly the source
  -- presentation by degree-one generators of `K`.
  exact isNoetherianRing_of_surjective _ _ φ.toRingHom hφ

/-- Helper for Lemma 10.97.5: taking the `n`-th coefficient sends the denominator ideal of the
quotient-Rees presentation into `K^(n + 1)`. -/
private theorem rees_algebra_coeff_mem_pow_succ_of_mem_denominator
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    {y : reesAlgebra K}
    (hy : y ∈ Ideal.map (algebraMap S (reesAlgebra K)) K) :
    y.1.coeff n ∈ K ^ (n + 1) := by
  have hy' : y ∈ K • (⊤ : Submodule S (reesAlgebra K)) := by
    -- Rewrite the denominator ideal as the stage-one scalar multiple.
    simpa [Ideal.smul_top_eq_map] using hy
  -- Check the coefficient condition first on generators, then extend by additivity.
  refine Submodule.smul_induction_on hy' ?_ ?_
  · intro r hr z hz
    have hzcoeff : z.1.coeff n ∈ K ^ n := z.2 n
    change (r • z.1).coeff n ∈ K ^ (n + 1)
    simpa [Polynomial.coeff_smul, smul_eq_mul, pow_succ', Ideal.mul_comm] using
      Ideal.mul_mem_mul hr hzcoeff
  · intro x y hx hy
    simpa [Polynomial.coeff_add] using Ideal.add_mem (K ^ (n + 1)) hx hy

/-- Helper for Lemma 10.97.5: if a degree-`n` coefficient already lies in `K^(n + 1)`, then the
corresponding monomial is in the denominator ideal of the quotient-Rees presentation. -/
private theorem monomial_mem_denominator_of_mem_pow_succ
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) {a : S}
    (ha : a ∈ K ^ (n + 1)) :
    (⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr
          ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩ :
      reesAlgebra K) ∈ Ideal.map (algebraMap S (reesAlgebra K)) K := by
  have hsmul :
      (⟨Polynomial.monomial n a,
          reesAlgebra.monomial_mem.mpr
            ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩ :
        reesAlgebra K) ∈ K • (⊤ : Submodule S (reesAlgebra K)) := by
    let x : reesAlgebra K :=
      ⟨Polynomial.monomial n a,
        reesAlgebra.monomial_mem.mpr
          ((Ideal.pow_le_pow_right (Nat.le_succ n)) ha)⟩
    let φ : S →ₗ[S] Polynomial S := Polynomial.monomial n
    have ha' : a ∈ K • (K ^ n : Submodule S S) := by
      -- This is the source identity `K * K^n = K^(n+1)`.
      simpa [Ideal.smul_eq_mul, pow_succ, Ideal.mul_comm] using ha
    let RK : Submodule S (Polynomial S) := Subalgebra.toSubmodule (reesAlgebra K)
    have hmap0 :
        (Submodule.map φ (K ^ n : Submodule S S) : Submodule S (Polynomial S)) ≤ RK := by
      intro p hp
      rcases hp with ⟨b, hb, rfl⟩
      exact reesAlgebra.monomial_mem.mpr hb
    have hmap :
        (Submodule.map φ (K • (K ^ n : Submodule S S)) : Submodule S (Polynomial S)) ≤
          (K • RK : Submodule S (Polynomial S)) := by
      rw [Submodule.map_smul'']
      refine Submodule.smul_le.mpr ?_
      intro r hr p hp
      exact Submodule.smul_mem_smul hr (hmap0 hp)
    have hambient : (x : Polynomial S) ∈ K • RK := by
      have hxmap : φ a ∈ Submodule.map φ (K • (K ^ n : Submodule S S)) := by
        exact Submodule.mem_map_of_mem ha'
      exact hmap <| by simpa [φ, x] using hxmap
    exact (Submodule.mem_smul_top_iff (I := K) (N := RK) (x := x)).2 hambient
  simpa [Ideal.smul_top_eq_map] using hsmul

/-- Helper for Lemma 10.97.5: the degree-`n` class of a stage element is zero exactly when the
coefficient lies one step deeper in the `K`-adic filtration. -/
private theorem associated_graded_stage_class_zero_iff
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K n x = 0 ↔
      (x : S) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1) := by
  constructor
  · intro hx
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
          ⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩ = 0
      at hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx
    -- A vanishing class means the monomial representative falls in the denominator ideal.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using rees_algebra_coeff_mem_pow_succ_of_mem_denominator K n hx
  · intro hx
    change
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
          ⟨Polynomial.monomial n (x : S), ideal_associated_graded_stage_monomial_mem K n x⟩ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hx' : (x : S) ∈ K ^ (n + 1) := by
      -- Re-express the next stage as the pure power ideal `K^(n+1)`.
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using hx
    simpa using monomial_mem_denominator_of_mem_pow_succ K n hx'

/-- Helper for Lemma 10.97.5: the kernel of the stage-to-grade map is the next filtration step. -/
private theorem idealAssociatedGradedStageClassLinear_ker_eq
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    LinearMap.ker (idealAssociatedGradedStageClassLinear K n) =
      (RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage K S n) := by
  ext x
  constructor
  · intro hx
    have hx' :
        (((idealAssociatedGradedStageClassLinear K n x : idealAssociatedGradedRingGrade K n) :
            idealAssociatedGradedRing K)) = 0 := by
      exact congrArg (fun z : idealAssociatedGradedRingGrade K n ↦ (z : idealAssociatedGradedRing K)) hx
    -- Forgetting the grade subtype reduces kernel membership to vanishing of the stage class.
    change idealAssociatedGradedStageClass K n x = 0 at hx'
    exact (associated_graded_stage_class_zero_iff K n x).1 hx'
  · intro hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    -- The previously proved zero criterion identifies the next stage with the kernel.
    change idealAssociatedGradedStageClass K n x = 0
    exact (associated_graded_stage_class_zero_iff K n x).2 hx

/-- Helper for Lemma 10.97.5: the degree-`n` owner piece is canonically equivalent to the
textbook quotient `K^n / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedRingGrade_equiv_piece
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    idealAssociatedGradedRingGrade K n ≃ₗ[S] RingTheory.Sequence.idealAssociatedGradedPiece K S n :=
  ((idealAssociatedGradedStageClassLinear K n).quotKerEquivOfSurjective
      (idealAssociatedGradedStageClassLinear_surjective K n)).symm.trans
    (Submodule.quotEquivOfEq _ _
      (idealAssociatedGradedStageClassLinear_ker_eq K n))

/-- Helper for Lemma 10.97.5: reducing a stage representative modulo `K^(n + 1)` lands in the
image of `K ^ n` in the quotient ring `S / K^(n + 1)`. -/
private theorem idealAssociatedGradedStageToPowQuotient_mem
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    Ideal.Quotient.mk (K ^ (n + 1)) (x : S) ∈
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) := by
  -- Forgetting the stage subtype recovers a literal element of `K ^ n`.
  exact Ideal.mem_map_of_mem _ <|
    by
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using x.2

/-- Helper for Lemma 10.97.5: the `n`-th stage maps linearly into the image of `K ^ n`
inside `S / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedStageToPowQuotientLinear
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedStage K S n →ₗ[S]
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) :=
  { toFun := fun x ↦ ⟨Ideal.Quotient.mk (K ^ (n + 1)) (x : S),
      idealAssociatedGradedStageToPowQuotient_mem K n x⟩
    map_add' := fun x y ↦ by
      apply Subtype.ext
      rfl
    map_smul' := fun r x ↦ by
      apply Subtype.ext
      rfl }

/-- Helper for Lemma 10.97.5: the codomain-restricted stage-to-quotient map evaluates to the
obvious quotient class modulo `K^(n + 1)`. -/
private theorem idealAssociatedGradedStageToPowQuotientLinear_apply
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    ((idealAssociatedGradedStageToPowQuotientLinear K n x :
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n)) : S ⧸ K ^ (n + 1)) =
      Ideal.Quotient.mk (K ^ (n + 1)) (x : S) := by
  -- The codomain restriction keeps the same quotient representative.
  rfl

/-- Helper for Lemma 10.97.5: every class in the image of `K ^ n` inside `S / K^(n + 1)` is
represented by an element of the `n`-th stage. -/
private theorem idealAssociatedGradedStageToPowQuotientLinear_surjective
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    Function.Surjective (idealAssociatedGradedStageToPowQuotientLinear K n) := by
  intro y
  rcases y with ⟨y, hy⟩
  rcases
      (Ideal.mem_map_iff_of_surjective
        (Ideal.Quotient.mk (K ^ (n + 1))) Ideal.Quotient.mk_surjective).mp hy with
    ⟨a, ha, rfl⟩
  refine ⟨⟨a, ?_⟩, ?_⟩
  · -- The witness in `K ^ n` is exactly an element of the `n`-th filtration stage.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using ha
  · -- The codomain representative is built from the same quotient class.
    apply Subtype.ext
    rfl

/-- Helper for Lemma 10.97.5: the kernel of the stage-to-quotient map is the next filtration
stage. -/
private theorem idealAssociatedGradedStageToPowQuotientLinear_ker_eq
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    LinearMap.ker (idealAssociatedGradedStageToPowQuotientLinear K n) =
      (RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1)).submoduleOf
        (RingTheory.Sequence.idealAssociatedGradedStage K S n) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hx' : Ideal.Quotient.mk (K ^ (n + 1)) (x : S) = 0 := by
      exact congrArg Subtype.val hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx'
    -- Vanishing in the quotient means the representative lies one step deeper in the filtration.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using hx'
  · intro hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    -- Membership in the next stage is exactly the quotient-zero criterion.
    exact Ideal.Quotient.eq_zero_iff_mem.mpr <|
      by
        simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
          using hx

/-- Helper for Lemma 10.97.5: the quotient `K^n / K^(n + 1)` identifies with the image of `K ^ n`
inside `S / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedPiece_equiv_map_pow
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    RingTheory.Sequence.idealAssociatedGradedPiece K S n ≃ₗ[S]
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) :=
  (Submodule.quotEquivOfEq _ _
      (idealAssociatedGradedStageToPowQuotientLinear_ker_eq K n).symm).trans
    ((idealAssociatedGradedStageToPowQuotientLinear K n).quotKerEquivOfSurjective
      (idealAssociatedGradedStageToPowQuotientLinear_surjective K n))

/-- Helper for Lemma 10.97.5: the piece-to-quotient identification sends the stage class of `x`
to the quotient class of `x` modulo `K^(n + 1)`. -/
private theorem idealAssociatedGradedPiece_equiv_map_pow_apply_stage
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedPiece_equiv_map_pow K n
      (Submodule.Quotient.mk x) =
        idealAssociatedGradedStageToPowQuotientLinear K n x := by
  -- Both quotient equivalences act trivially on the stage representative `x`.
  simp [idealAssociatedGradedPiece_equiv_map_pow]

/-- Helper for Lemma 10.97.5: the owner degree-`n` piece is canonically equivalent to the image
of `K ^ n` inside `S / K^(n + 1)`. -/
private noncomputable def idealAssociatedGradedRingGrade_equiv_map_pow
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ) :
    idealAssociatedGradedRingGrade K n ≃
      Ideal.map (Ideal.Quotient.mk (K ^ (n + 1))) (K ^ n) :=
  (idealAssociatedGradedRingGrade_equiv_piece K n).toEquiv.trans
    (idealAssociatedGradedPiece_equiv_map_pow K n).toEquiv

/-- Helper for Lemma 10.97.5: on a stage representative, the owner-grade equivalence agrees with
the obvious quotient class modulo `K^(n + 1)`. -/
private theorem idealAssociatedGradedRingGrade_equiv_map_pow_apply_stage
    {S : Type u} [CommRing S] (K : Ideal S) (n : ℕ)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedRingGrade_equiv_map_pow K n
      (idealAssociatedGradedStageClassLinear K n x) =
        idealAssociatedGradedStageToPowQuotientLinear K n x := by
  -- First identify the owner grade with `K^n / K^(n + 1)`, then with the quotient image.
  simpa [idealAssociatedGradedRingGrade_equiv_map_pow, idealAssociatedGradedRingGrade_equiv_piece]
    using idealAssociatedGradedPiece_equiv_map_pow_apply_stage (S := S) K n x

/-- Helper for Lemma 10.97.5: the `n`-th coefficient of a Rees element lies in the `n`-th
associated-graded stage. -/
private theorem coeff_mem_idealAssociatedGradedStage
    {S : Type u} [CommRing S] (K : Ideal S) (y : reesAlgebra K) (n : ℕ) :
    y.1.coeff n ∈ RingTheory.Sequence.idealAssociatedGradedStage K S n := by
  -- The defining coefficient condition for the Rees algebra is exactly stage membership.
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
    using y.2 n

/-- Helper for Lemma 10.97.5: the unit of `S` belongs to the degree-zero stage of the
`K`-adic filtration. -/
private theorem one_mem_idealAssociatedGradedStage_zero
    {S : Type u} [CommRing S] (K : Ideal S) :
    (1 : S) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S 0 := by
  -- Degree zero is the whole ring, so the unit is available as the multiplicative base case.
  simp [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.mul_top]

/-- Helper for Lemma 10.97.5: a chosen generator of `K` raised to the `n`-th power belongs to the
`n`-th stage of the `K`-adic filtration. -/
private theorem generator_pow_mem_idealAssociatedGradedStage
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K) (i : Fin t) (n : ℕ) :
    (((g i : K) : S) ^ n) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S n := by
  -- A generator of `K` contributes one copy of `K` at each multiplication step.
  have hpow : (((g i : K) : S) ^ n) ∈ K ^ n := Ideal.pow_mem_pow (g i).2 n
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using
    hpow

/-- Helper for Lemma 10.97.5: multiplying representatives from stages `m` and `n` lands in the
stage `m + n`. -/
private theorem ideal_associated_graded_stage_mul_mem
    {S : Type u} [CommRing S] (K : Ideal S) {m n : ℕ}
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S m)
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    ((x : S) * (y : S)) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S (m + n) := by
  -- The filtration is multiplicative because `K ^ m * K ^ n = K ^ (m + n)`.
  have hx : (x : S) ∈ K ^ m := by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using x.2
  have hy : (y : S) ∈ K ^ n := by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using y.2
  have hxy : (x : S) * (y : S) ∈ K ^ m * K ^ n := Ideal.mul_mem_mul hx hy
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top,
    pow_add] using hxy

/-- Helper for Lemma 10.97.5: the product in the associated graded ring is induced by
multiplication of stage representatives. -/
private theorem idealAssociatedGradedStageClass_mul
    {S : Type u} [CommRing S] (K : Ideal S) {m n : ℕ}
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S m)
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K (m + n)
        ⟨(x : S) * (y : S), ideal_associated_graded_stage_mul_mem K x y⟩ =
      idealAssociatedGradedStageClass K m x * idealAssociatedGradedStageClass K n y := by
  -- Compare both sides on the canonical quotient-Rees monomial representatives.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        (⟨Polynomial.monomial (m + n) ((x : S) * (y : S)), _⟩ : reesAlgebra K) =
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        ((⟨Polynomial.monomial m (x : S), _⟩ : reesAlgebra K) *
          (⟨Polynomial.monomial n (y : S), _⟩ : reesAlgebra K))
  congr 1
  apply Subtype.ext
  simp [Polynomial.monomial_mul_monomial]

/-- Helper for Lemma 10.97.5: the degree-`n` class of a single generator power is the `n`-th
power of the corresponding degree-one class. -/
private theorem associated_graded_stage_class_generator_pow_eq
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K) (i : Fin t) (n : ℕ) :
    idealAssociatedGradedStageClass K n
        ⟨((g i : K) : S) ^ n, generator_pow_mem_idealAssociatedGradedStage K g i n⟩ =
      idealAssociatedGradedDegreeOne (g i) ^ n := by
  letI : Monoid (idealAssociatedGradedRing K) := inferInstance
  induction n with
  | zero =>
      -- Compare the degree-zero representative with the unit of the quotient-Rees ring.
      change
        (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
          (⟨Polynomial.monomial 0 (((g i : K) : S) ^ 0),
              ideal_associated_graded_stage_monomial_mem K 0
                ⟨((g i : K) : S) ^ 0, generator_pow_mem_idealAssociatedGradedStage K g i 0⟩⟩ :
            reesAlgebra K) : idealAssociatedGradedRing K) =
          Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (1 : reesAlgebra K)
      congr 1
      apply Subtype.ext
      simp
  | succ n ih =>
      -- Multiply the degree-`n` class by the degree-one class of the same generator.
      let xn : RingTheory.Sequence.idealAssociatedGradedStage K S n :=
        ⟨((g i : K) : S) ^ n, generator_pow_mem_idealAssociatedGradedStage K g i n⟩
      let x1 : RingTheory.Sequence.idealAssociatedGradedStage K S 1 :=
        ⟨((g i : K) : S) ^ 1, generator_pow_mem_idealAssociatedGradedStage K g i 1⟩
      have hmul :
          idealAssociatedGradedStageClass K (n + 1)
              ⟨((g i : K) : S) ^ (n + 1), generator_pow_mem_idealAssociatedGradedStage K g i (n + 1)⟩ =
            idealAssociatedGradedStageClass K n xn * idealAssociatedGradedDegreeOne (g i) := by
        -- The source multiplication rule on stages matches multiplication in the quotient.
        simpa [xn, x1, idealAssociatedGradedDegreeOne, pow_succ, pow_one] using
          idealAssociatedGradedStageClass_mul (S := S) K xn x1
      calc
        idealAssociatedGradedStageClass K (n + 1)
            ⟨((g i : K) : S) ^ (n + 1), generator_pow_mem_idealAssociatedGradedStage K g i (n + 1)⟩ =
          idealAssociatedGradedStageClass K n xn * idealAssociatedGradedDegreeOne (g i) := hmul
        _ = idealAssociatedGradedDegreeOne (g i) ^ n * idealAssociatedGradedDegreeOne (g i) := by
            rw [ih]
        _ = idealAssociatedGradedDegreeOne (g i) ^ (n + 1) := by
            rw [pow_succ]

/-- Helper for Lemma 10.97.5: the monomial weight attached to `e` lies in the stage of degree
`e.degree`. -/
private theorem monomial_weight_mem_idealAssociatedGradedStage_of_generators
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K) (e : Fin t →₀ ℕ) :
    (∏ i : Fin t, ((g i : K) : S) ^ e i) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S
      e.degree := by
  -- The monomial-weight description of `K ^ e.degree` gives the required stage membership.
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using
    monomial_weight_mem_ideal_pow_of_generators K g hgspan e

/-- Helper for Lemma 10.97.5: a finite product of ordinary monomials in one variable collapses to
one monomial whose degree and coefficient are the corresponding finite sums and products. -/
private theorem polynomial_finset_prod_monomial_eq_monomial_sum
    {S : Type u} [CommRing S] {ι : Type*}
    (s : Finset ι) (d : ι → ℕ) (a : ι → S) :
    (∏ i ∈ s, Polynomial.monomial (d i) (a i)) =
      Polynomial.monomial (s.sum d) (s.prod a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty product is the degree-zero monomial with coefficient `1`.
      simp
  | @insert i s hi hs =>
      -- One more factor combines with the inductive monomial by `monomial_mul_monomial`.
      simp [hi, hs, Polynomial.monomial_mul_monomial]

/-- Helper for Lemma 10.97.5: the degree-`e.degree` class of the monomial weight attached to `e`
is the product of the degree-one classes of the chosen generators. -/
private theorem associated_graded_stage_class_monomial_weight_eq
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K) (e : Fin t →₀ ℕ) :
    idealAssociatedGradedStageClass K e.degree
        ⟨∏ i : Fin t, ((g i : K) : S) ^ e i,
          monomial_weight_mem_idealAssociatedGradedStage_of_generators K g hgspan e⟩ =
      ∏ i : Fin t, idealAssociatedGradedDegreeOne (g i) ^ e i := by
  classical
  letI : CommRing (idealAssociatedGradedRing K) :=
    Ideal.Quotient.commRing (Ideal.map (algebraMap S (reesAlgebra K)) K)
  let q : reesAlgebra K →+* idealAssociatedGradedRing K :=
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
  let c : Fin t → reesAlgebra K := fun i ↦
    ⟨Polynomial.monomial 1 ((g i : K) : S), idealAssociatedGradedDegreeOne_mem (g i)⟩
  have hprod :
      (∏ i : Fin t, c i ^ e i : reesAlgebra K).1 =
        Polynomial.monomial e.degree (∏ i : Fin t, ((g i : K) : S) ^ e i) := by
    -- Normalize the product of Rees monomials to the single monomial of total weight.
    simpa [Finsupp.degree_eq_sum, c, polynomial_finset_prod_monomial_eq_monomial_sum]
  change q
      (⟨Polynomial.monomial e.degree (∏ i : Fin t, ((g i : K) : S) ^ e i), _⟩ :
        reesAlgebra K) =
    ∏ i : Fin t, q (c i) ^ e i
  -- Push the finite product through the quotient map, then use `map_pow` factor by factor.
  trans q (∏ i : Fin t, c i ^ e i)
  · congr 1
    apply Subtype.ext
    exact hprod.symm
  · calc
      q (∏ i : Fin t, c i ^ e i) = ∏ i : Fin t, q (c i ^ e i) := by
        simpa using (map_prod q (fun i : Fin t ↦ c i ^ e i) Finset.univ)
      _ = ∏ i : Fin t, q (c i) ^ e i := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        exact map_pow q (c i) (e i)

/-- Helper for Chap10 Lemma 10 97 5: the zero stage representative maps to zero in the
quotient-Rees associated graded ring. -/
private theorem idealAssociatedGradedStageClass_zero
    {S : Type u} [CommRing S] (K : Ideal S) {n : ℕ}
    (hzero : (0 : S) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K n ⟨0, hzero⟩ = 0 := by
  -- Compare the zero monomial with the zero Rees element before passing to the quotient.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        (⟨Polynomial.monomial n (0 : S), _⟩ : reesAlgebra K) =
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (0 : reesAlgebra K)
  congr 1
  apply Subtype.ext
  simp

/-- Helper for Chap10 Lemma 10 97 5: addition of representatives in one stage becomes addition
of their associated graded classes. -/
private theorem idealAssociatedGradedStageClass_add
    {S : Type u} [CommRing S] (K : Ideal S) {n : ℕ}
    (x y : RingTheory.Sequence.idealAssociatedGradedStage K S n)
    (hxy : (x : S) + (y : S) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K n ⟨(x : S) + (y : S), hxy⟩ =
      idealAssociatedGradedStageClass K n x + idealAssociatedGradedStageClass K n y := by
  -- Addition is checked on the chosen Rees monomial representatives.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        (⟨Polynomial.monomial n ((x : S) + (y : S)), _⟩ : reesAlgebra K) =
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
          (⟨Polynomial.monomial n (x : S), _⟩ : reesAlgebra K) +
        Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
          (⟨Polynomial.monomial n (y : S), _⟩ : reesAlgebra K)
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        (⟨Polynomial.monomial n ((x : S) + (y : S)), _⟩ : reesAlgebra K) =
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        ((⟨Polynomial.monomial n (x : S), _⟩ : reesAlgebra K) +
          (⟨Polynomial.monomial n (y : S), _⟩ : reesAlgebra K))
  congr 1
  apply Subtype.ext
  simp

/-- Helper for Chap10 Lemma 10 97 5: multiplying a stage representative by an ambient scalar is
the same as multiplying its class by the residue class of that scalar. -/
private theorem idealAssociatedGradedStageClass_algebraMap_mul
    {S : Type u} [CommRing S] (K : Ideal S) {n : ℕ} (r : S)
    (x : RingTheory.Sequence.idealAssociatedGradedStage K S n)
    (hrx : r * (x : S) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K n ⟨r * (x : S), hrx⟩ =
      algebraMap (S ⧸ K) (idealAssociatedGradedRing K) (Ideal.Quotient.mk K r) *
        idealAssociatedGradedStageClass K n x := by
  letI : CommRing (idealAssociatedGradedRing K) :=
    Ideal.Quotient.commRing (Ideal.map (algebraMap S (reesAlgebra K)) K)
  -- The quotient-algebra scalar is represented by the constant Rees polynomial `r`.
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        (⟨Polynomial.monomial n (r * (x : S)), _⟩ : reesAlgebra K) =
      algebraMap (S ⧸ K) (idealAssociatedGradedRing K) (Ideal.Quotient.mk K r) *
        Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
          (⟨Polynomial.monomial n (x : S), _⟩ : reesAlgebra K)
  change
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        (⟨Polynomial.monomial n (r * (x : S)), _⟩ : reesAlgebra K) =
      Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
        ((algebraMap S (reesAlgebra K) r) *
          (⟨Polynomial.monomial n (x : S), _⟩ : reesAlgebra K))
  congr 1
  apply Subtype.ext
  simp

/-- Helper for Lemma 10.97.5: any `S`-linear combination of degree-`n` generator monomials
belongs to the degree-`n` stage. -/
private theorem span_monomial_weight_mem_idealAssociatedGradedStage_of_generators
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K) (n : ℕ) {x : S}
    (hx : x ∈ Ideal.span ((fun e : Fin t →₀ ℕ =>
      ∏ i : Fin t, ((g i : K) : S) ^ e i) '' {e | e.degree = n})) :
    x ∈ RingTheory.Sequence.idealAssociatedGradedStage K S n := by
  -- Reinterpret the span description of `K ^ n` back as stage membership.
  have hxK : x ∈ K ^ n := by
    rw [ideal_pow_eq_span_monomial_weight_of_generators K g hgspan n]
    exact hx
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top] using
    hxK

/-- Helper for Lemma 10.97.5: every stage class lies in the subalgebra generated by the degree-one
classes of a fixed finite generating family of `K`. -/
private theorem associated_graded_stage_class_mem_adjoin_degree_one
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K)
    (n : ℕ) (x : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K n x ∈
      Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne (g i)) := by
  letI : CommRing (idealAssociatedGradedRing K) :=
    Ideal.Quotient.commRing (Ideal.map (algebraMap S (reesAlgebra K)) K)
  let A : Subalgebra (S ⧸ K) (idealAssociatedGradedRing K) :=
    Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne (g i))
  have hxspan :
      (x : S) ∈ Ideal.span ((fun e : Fin t →₀ ℕ =>
        ∏ i : Fin t, ((g i : K) : S) ^ e i) '' {e | e.degree = n}) := by
    -- Move the stage condition to the monomial-span description of `K ^ n`.
    rw [← ideal_pow_eq_span_monomial_weight_of_generators K g hgspan n]
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using x.2
  -- Span induction reduces membership to monomial weights, addition, and residue-field scalars.
  refine Submodule.span_induction (s := (fun e : Fin t →₀ ℕ =>
      ∏ i : Fin t, ((g i : K) : S) ^ e i) '' {e | e.degree = n})
    (p := fun y hy ↦
      idealAssociatedGradedStageClass K n
        ⟨y, span_monomial_weight_mem_idealAssociatedGradedStage_of_generators K g hgspan n hy⟩ ∈
          A) ?_ ?_ ?_ ?_ hxspan
  · rintro y ⟨e, he, rfl⟩
    -- A generator of the span is exactly a monomial in the chosen degree-one generators.
    subst n
    simpa [A] using associated_graded_stage_class_monomial_weight_eq K g hgspan e ▸
      (Subalgebra.prod_mem A fun i _ ↦
        Subalgebra.pow_mem A
          (Algebra.subset_adjoin ⟨i, rfl⟩) (e i))
  · -- The zero linear combination gives the zero class.
    have hzeroClass :
        idealAssociatedGradedStageClass K n
            ⟨0, span_monomial_weight_mem_idealAssociatedGradedStage_of_generators K g hgspan n
              (Submodule.zero_mem _)⟩ = 0 :=
      idealAssociatedGradedStageClass_zero K _
    simpa [hzeroClass] using A.zero_mem
  · intro y z hy hz hyA hzA
    -- Addition of representatives agrees with addition of their classes.
    let yStage : RingTheory.Sequence.idealAssociatedGradedStage K S n :=
      ⟨y, span_monomial_weight_mem_idealAssociatedGradedStage_of_generators K g hgspan n hy⟩
    let zStage : RingTheory.Sequence.idealAssociatedGradedStage K S n :=
      ⟨z, span_monomial_weight_mem_idealAssociatedGradedStage_of_generators K g hgspan n hz⟩
    have hClass :
        idealAssociatedGradedStageClass K n
            ⟨y + z, span_monomial_weight_mem_idealAssociatedGradedStage_of_generators K g
              hgspan n (Submodule.add_mem _ hy hz)⟩ =
          idealAssociatedGradedStageClass K n yStage +
            idealAssociatedGradedStageClass K n zStage :=
      idealAssociatedGradedStageClass_add K yStage zStage _
    simpa [yStage, zStage, hClass] using A.add_mem hyA hzA
  · intro r y hy hyA
    -- Scalar multiplication by `r : S` is multiplication by its image in the residue ring.
    let yStage : RingTheory.Sequence.idealAssociatedGradedStage K S n :=
      ⟨y, span_monomial_weight_mem_idealAssociatedGradedStage_of_generators K g hgspan n hy⟩
    have hClass :
        idealAssociatedGradedStageClass K n
            ⟨r • y, span_monomial_weight_mem_idealAssociatedGradedStage_of_generators K g
              hgspan n (Submodule.smul_mem _ r hy)⟩ =
          algebraMap (S ⧸ K) (idealAssociatedGradedRing K) (Ideal.Quotient.mk K r) *
            idealAssociatedGradedStageClass K n yStage := by
      simpa [yStage, smul_eq_mul] using
        idealAssociatedGradedStageClass_algebraMap_mul K r yStage
          (span_monomial_weight_mem_idealAssociatedGradedStage_of_generators K g hgspan n
            (Submodule.smul_mem _ r hy))
    have hyStageA : idealAssociatedGradedStageClass K n yStage ∈ A := by
      simpa [yStage] using hyA
    exact hClass.symm ▸
      A.mul_mem (Subalgebra.algebraMap_mem A (Ideal.Quotient.mk K r)) hyStageA

/-- Helper for Lemma 10.97.5: every quotient-Rees class is the sum of the stage classes of its
support coefficients. -/
private theorem idealAssociatedGradedClass_eq_sum_stage_classes
    {S : Type u} [CommRing S] (K : Ideal S) (y : reesAlgebra K) :
    (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) y :
      idealAssociatedGradedRing K) =
        ∑ n ∈ y.1.support,
          idealAssociatedGradedStageClass K n
            ⟨y.1.coeff n, coeff_mem_idealAssociatedGradedStage K y n⟩ := by
  classical
  let J : Ideal (reesAlgebra K) := Ideal.map (algebraMap S (reesAlgebra K)) K
  let q : reesAlgebra K →ₐ[S] idealAssociatedGradedRing K := Ideal.Quotient.mkₐ S J
  let c : ℕ → reesAlgebra K :=
    fun n ↦
      ⟨Polynomial.monomial n (y.1.coeff n),
        reesAlgebra.monomial_mem.mpr (y.2 n)⟩
  have hy_sum : y = ∑ n ∈ y.1.support, c n := by
    -- Expand the Rees representative as the finite sum of its coefficient monomials.
    apply Subtype.ext
    simpa [Polynomial.sum, c] using (Polynomial.sum_monomial_eq y.1).symm
  have hq_sum :
      q (∑ n ∈ y.1.support, c n) =
        ∑ n ∈ y.1.support, q (c n) := by
    -- The quotient map preserves finite sums.
    simpa using q.map_sum (fun n ↦ c n) y.1.support
  calc
    (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) y :
      idealAssociatedGradedRing K) =
      q y := by
        rfl
    _ = q (∑ n ∈ y.1.support, c n) := by
      simpa using congrArg q hy_sum
    _ = ∑ n ∈ y.1.support, q (c n) := by
      exact hq_sum
    _ =
        ∑ n ∈ y.1.support,
          idealAssociatedGradedStageClass K n
            ⟨y.1.coeff n, coeff_mem_idealAssociatedGradedStage K y n⟩ := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      rfl

/-- Helper for Lemma 10.97.5: the degree-one classes of a finite generating family of `K`
generate the whole associated graded ring over `S ⧸ K`. -/
private theorem associated_graded_degree_one_adjoin_eq_top
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hgspan : Ideal.span (Set.range fun i ↦ ((g i : K) : S)) = K) :
    Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne (g i)) = ⊤ := by
  let A : Subalgebra (S ⧸ K) (idealAssociatedGradedRing K) :=
    Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne (g i))
  -- Every quotient-Rees class decomposes into homogeneous stage classes, each already in `A`.
  apply le_antisymm
  · exact le_top
  · intro z hz
    rcases Ideal.Quotient.mk_surjective z with ⟨y, rfl⟩
    rw [idealAssociatedGradedClass_eq_sum_stage_classes]
    apply Subalgebra.sum_mem
    intro n hn
    exact associated_graded_stage_class_mem_adjoin_degree_one K g hgspan n
      ⟨y.1.coeff n, coeff_mem_idealAssociatedGradedStage K y n⟩

/-- Helper for Lemma 10.97.5: if the degree-one classes adjoin to all of `gr_K(S)`, then the
source polynomial presentation is surjective. -/
private theorem associated_graded_presentation_surjective
    {S : Type u} [CommRing S] (K : Ideal S) {t : ℕ} (g : Fin t → K)
    (hadjoin :
      Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne (g i)) = ⊤) :
    Function.Surjective (associated_graded_presentation K g) := by
  -- Convert the adjoin statement into the exact range statement for `MvPolynomial.aeval`.
  have hrange :
      (associated_graded_presentation K g).range =
        Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne (g i)) := by
    simpa [associated_graded_presentation] using
      (Algebra.adjoin_range_eq_range_aeval (R := S ⧸ K)
        (f := fun i : Fin t ↦ idealAssociatedGradedDegreeOne (g i))).symm
  -- The range is all of `gr_K(S)`, so the presentation is surjective.
  exact (AlgHom.range_eq_top (associated_graded_presentation K g)).1 <| by
    rw [hrange]
    simpa using hadjoin

/-- Helper for Lemma 10.97.5: once the associated graded ring is generated by finitely many
degree-one classes over `S ⧸ K`, it is Noetherian. -/
private theorem associated_graded_isNoetherian_of_degree_one_adjoin_eq_top
    {S : Type u} [CommRing S] (K : Ideal S) [IsNoetherianRing (S ⧸ K)] {t : ℕ} (g : Fin t → K)
    (hadjoin :
      Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne (g i)) = ⊤) :
    IsNoetherianRing (idealAssociatedGradedRing K) := by
  -- Use the source-faithful polynomial presentation rather than rebuilding a separate finite-type
  -- instance layer.
  exact associated_graded_isNoetherian_of_surjective_mvPolynomial K
    (associated_graded_presentation K g)
    (associated_graded_presentation_surjective K g hadjoin)

/-- Helper for Chap10 Lemma 10 97 5: the initial ideal of `J` in `gr_K(S)` is generated by
the associated-graded classes represented by elements of `J ∩ K^n`. -/
private noncomputable def associatedGradedInitialIdeal
    {S : Type u} [CommRing S] (K J : Ideal S) : Ideal (idealAssociatedGradedRing K) :=
  Ideal.span {z | ∃ (n : ℕ) (x : RingTheory.Sequence.idealAssociatedGradedStage K S n),
    (x : S) ∈ J ∧ z = idealAssociatedGradedStageClass K n x}

/-- Helper for Chap10 Lemma 10 97 5: Noetherianity of `gr_K(S)` makes the initial ideal of any
ideal `J` finitely generated. -/
private theorem associatedGradedInitialIdeal_fg
    {S : Type u} [CommRing S] (K J : Ideal S)
    [IsNoetherianRing (idealAssociatedGradedRing K)] :
    (associatedGradedInitialIdeal K J).FG := by
  -- The initial ideal is an ordinary ideal of the Noetherian associated graded ring.
  exact Ideal.FG.of_isNoetherianRing (associatedGradedInitialIdeal K J)

/-- Helper for Chap10 Lemma 10 97 5: a finitely generated span is generated by a finite subset
of the original spanning set. -/
private theorem exists_finset_subset_span_eq_of_fg_span
    {A M : Type u} [CommSemiring A] [AddCommMonoid M] [Module A M] {s : Set M}
    (hfg : (Submodule.span A s).FG) :
    ∃ t : Finset M, (t : Set M) ⊆ s ∧
      Submodule.span A (t : Set M) = Submodule.span A s := by
  -- Mathlib already packages the finite-subset extraction for spans; we only orient the equality
  -- in the form needed by the associated-graded initial ideal below.
  obtain ⟨t, hts, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := A) (M := M) s).mp hfg
  exact ⟨t, hts, hspan.symm⟩

/-- Helper for Chap10 Lemma 10 97 5: source data for one homogeneous initial form of an ideal
`J` in the associated graded ring of `K`. -/
private abbrev initialFormData
    {S : Type u} [CommRing S] (K J : Ideal S) : Type u :=
  Σ n : ℕ, {x : RingTheory.Sequence.idealAssociatedGradedStage K S n // (x : S) ∈ J}

/-- Helper for Chap10 Lemma 10 97 5: the associated-graded class attached to an
`initialFormData K J` datum. -/
private noncomputable def initialFormDataClass
    {S : Type u} [CommRing S] (K J : Ideal S) :
    initialFormData K J → idealAssociatedGradedRing K :=
  fun p ↦ idealAssociatedGradedStageClass K p.1 p.2.1

/-- Helper for Chap10 Lemma 10 97 5: the initial ideal is the span of the classes attached to
all homogeneous initial-form data. -/
private theorem associatedGradedInitialIdeal_eq_span_initialFormDataClass
    {S : Type u} [CommRing S] (K J : Ideal S) :
    associatedGradedInitialIdeal K J =
      Ideal.span (Set.range (initialFormDataClass K J)) := by
  -- The defining generators and the packaged initial-form data are the same set, just reindexed.
  unfold associatedGradedInitialIdeal
  congr 1
  ext z
  constructor
  · rintro ⟨n, x, hxJ, rfl⟩
    exact ⟨⟨n, ⟨x, hxJ⟩⟩, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2.1, p.2.2, rfl⟩

/-- Helper for Chap10 Lemma 10 97 5: a homogeneous stage representative whose source element
lies in `J` contributes a generator of the initial ideal of `J`. -/
private theorem stageClass_mem_associatedGradedInitialIdeal
    {S : Type u} [CommRing S] (K J : Ideal S) {n : ℕ}
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n) (hyJ : (y : S) ∈ J) :
    idealAssociatedGradedStageClass K n y ∈ associatedGradedInitialIdeal K J := by
  -- The initial ideal was defined as the span of exactly these homogeneous classes.
  unfold associatedGradedInitialIdeal
  exact Ideal.subset_span ⟨n, y, hyJ, rfl⟩

/-- Helper for Chap10 Lemma 10 97 5: a finitely generated initial ideal has finitely many
homogeneous initial-form data whose classes generate it. -/
private theorem exists_initialFormData_finset_span
    {S : Type u} [CommRing S] (K J : Ideal S)
    (hfg : (associatedGradedInitialIdeal K J).FG) :
    ∃ t : Finset (initialFormData K J),
      associatedGradedInitialIdeal K J =
        Ideal.span (initialFormDataClass K J '' (t : Set (initialFormData K J))) := by
  classical
  letI : CommRing (idealAssociatedGradedRing K) :=
    Ideal.Quotient.commRing (Ideal.map (algebraMap S (reesAlgebra K)) K)
  letI : Module (idealAssociatedGradedRing K) (idealAssociatedGradedRing K) := Semiring.toModule
  let f : initialFormData K J → idealAssociatedGradedRing K := initialFormDataClass K J
  have hfgSpan : (Submodule.span (idealAssociatedGradedRing K) (Set.range f)).FG := by
    -- Rewrite finite generation from the named initial ideal to its generating range.
    simpa [f, associatedGradedInitialIdeal_eq_span_initialFormDataClass K J] using hfg
  obtain ⟨v, hv_subset, hv_span⟩ :=
    exists_finset_subset_span_eq_of_fg_span (A := idealAssociatedGradedRing K)
      (M := idealAssociatedGradedRing K) (s := Set.range f) hfgSpan
  have hv_subset_image : (v : Set (idealAssociatedGradedRing K)) ⊆ f '' (Set.univ) := by
    simpa only [Set.image_univ] using hv_subset
  obtain ⟨t, -, ht_image⟩ :=
    (Finset.subset_set_image_iff (s := (Set.univ : Set (initialFormData K J)))
      (t := v) (f := f)).mp hv_subset_image
  refine ⟨t, ?_⟩
  calc
    associatedGradedInitialIdeal K J = Ideal.span (Set.range f) := by
      exact associatedGradedInitialIdeal_eq_span_initialFormDataClass K J
    _ = Ideal.span (v : Set (idealAssociatedGradedRing K)) := hv_span.symm
    _ = Ideal.span (f '' (t : Set (initialFormData K J))) := by
      rw [← Finset.coe_image, ht_image]

/-- Helper for Chap10 Lemma 10 97 5: after finite initial-form extraction, every stage class
coming from `J` lies in the finite span of the chosen initial-form classes. -/
private theorem stageClass_mem_initialFormData_finset_span
    {S : Type u} [CommRing S] (K J : Ideal S) {n : ℕ}
    {t : Finset (initialFormData K J)}
    (ht :
      associatedGradedInitialIdeal K J =
        Ideal.span (initialFormDataClass K J '' (t : Set (initialFormData K J))))
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n) (hyJ : (y : S) ∈ J) :
    idealAssociatedGradedStageClass K n y ∈
      Ideal.span (initialFormDataClass K J '' (t : Set (initialFormData K J))) := by
  -- Rewrite the global initial-ideal membership through the finite spanning set selected above.
  rw [← ht]
  exact stageClass_mem_associatedGradedInitialIdeal K J y hyJ

/-- Helper for Chap10 Lemma 10 97 5: finite initial-form span membership can be written with
quotient-Rees representatives for all coefficients. -/
private theorem initialFormSpan_exists_reesCoefficients
    {S : Type u} [CommRing S] (K J : Ideal S) {n : ℕ}
    {t : Finset (initialFormData K J)}
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n)
    (hy :
      idealAssociatedGradedStageClass K n y ∈
        Ideal.span (initialFormDataClass K J '' (t : Set (initialFormData K J)))) :
    ∃ b : {p // p ∈ t} → reesAlgebra K,
      idealAssociatedGradedStageClass K n y =
        ∑ p : {p // p ∈ t},
          (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (b p) :
              idealAssociatedGradedRing K) *
            initialFormDataClass K J p.1 := by
  classical
  let q : reesAlgebra K →+* idealAssociatedGradedRing K :=
    Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K)
  -- First use the finite-span API to expose the finitely many graded coefficients.
  letI : CommRing (idealAssociatedGradedRing K) :=
    Ideal.Quotient.commRing (Ideal.map (algebraMap S (reesAlgebra K)) K)
  letI : Module (idealAssociatedGradedRing K) (idealAssociatedGradedRing K) := Semiring.toModule
  obtain ⟨c, hc⟩ :=
    (Fintype.mem_span_image_iff_exists_fun
      (R := idealAssociatedGradedRing K)
      (v := initialFormDataClass K J)
      (s := (t : Set (initialFormData K J)))
      (x := idealAssociatedGradedStageClass K n y)).1 hy
  -- Then lift every coefficient from the quotient-Rees ring to an actual Rees representative.
  choose b hb using fun p : {p // p ∈ t} ↦ Ideal.Quotient.mk_surjective (c p)
  refine ⟨b, ?_⟩
  have hc_mul :
      idealAssociatedGradedStageClass K n y =
        ∑ p : {p // p ∈ t}, c p * initialFormDataClass K J p.1 := by
    -- Rewrite the span-linear-combination output from scalar action to ring multiplication once.
    simpa [smul_eq_mul] using hc.symm
  calc
    idealAssociatedGradedStageClass K n y =
        ∑ p : {p // p ∈ t}, c p * initialFormDataClass K J p.1 := hc_mul
    _ =
        ∑ p : {p // p ∈ t},
          (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (b p) :
              idealAssociatedGradedRing K) *
            initialFormDataClass K J p.1 := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      rw [hb p]

/-- Helper for Chap10 Lemma 10 97 5: the coefficient of a product with a monomial is zero
below the monomial degree and otherwise is the shifted coefficient times the monomial
coefficient. -/
private theorem coeff_mul_monomial_at
    {S : Type u} [CommRing S] (P : Polynomial S) (d n : ℕ) (a : S) :
    (P * Polynomial.monomial d a).coeff n =
      if d ≤ n then P.coeff (n - d) * a else 0 := by
  -- Split the arithmetic normal form once, so Rees coefficient extraction can reuse it directly.
  by_cases hd : d ≤ n
  · rw [if_pos hd]
    rw [← Nat.sub_add_cancel hd]
    simpa [add_comm] using Polynomial.coeff_mul_monomial P d (n - d) a
  · rw [if_neg hd]
    rw [Polynomial.coeff_mul]
    refine Finset.sum_eq_zero ?_
    rintro ⟨i, j⟩ hij
    rw [Finset.mem_antidiagonal] at hij
    have hjne : d ≠ j := by
      intro h
      subst j
      have : d ≤ n := by omega
      exact hd this
    simp [Polynomial.coeff_monomial, hjne]

/-- Helper for Chap10 Lemma 10 97 5: a quotient-Rees equality of a stage class with a finite
initial-form combination lifts to one denominator relation before coefficients are taken. -/
private theorem reesInitialFormResidual_mem_denominator
    {S : Type u} [CommRing S] (K J : Ideal S) {n : ℕ}
    {t : Finset (initialFormData K J)}
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n)
    (b : {p // p ∈ t} → reesAlgebra K)
    (h :
      idealAssociatedGradedStageClass K n y =
        ∑ p : {p // p ∈ t},
          (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (b p) :
              idealAssociatedGradedRing K) *
            initialFormDataClass K J p.1) :
    (⟨Polynomial.monomial n (y : S), ideal_associated_graded_stage_monomial_mem K n y⟩ -
      ∑ p : {p // p ∈ t},
        b p *
          (⟨Polynomial.monomial p.1.1 (p.1.2.1 : S),
              ideal_associated_graded_stage_monomial_mem K p.1.1 p.1.2.1⟩ :
            reesAlgebra K)) ∈
      Ideal.map (algebraMap S (reesAlgebra K)) K := by
  let D : Ideal (reesAlgebra K) := Ideal.map (algebraMap S (reesAlgebra K)) K
  let q : reesAlgebra K →+* idealAssociatedGradedRing K := Ideal.Quotient.mk D
  -- Move the quotient equality back to the source Rees algebra as a single kernel statement.
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change
    q
      (⟨Polynomial.monomial n (y : S), ideal_associated_graded_stage_monomial_mem K n y⟩ -
        ∑ p : {p // p ∈ t},
          b p *
            (⟨Polynomial.monomial p.1.1 (p.1.2.1 : S),
                ideal_associated_graded_stage_monomial_mem K p.1.1 p.1.2.1⟩ :
              reesAlgebra K)) = 0
  rw [q.map_sub]
  have hsum :
      q
          (∑ p : {p // p ∈ t},
            b p *
              (⟨Polynomial.monomial p.1.1 (p.1.2.1 : S),
                  ideal_associated_graded_stage_monomial_mem K p.1.1 p.1.2.1⟩ :
                reesAlgebra K)) =
        ∑ p : {p // p ∈ t},
          q
            (b p *
              (⟨Polynomial.monomial p.1.1 (p.1.2.1 : S),
                  ideal_associated_graded_stage_monomial_mem K p.1.1 p.1.2.1⟩ :
                reesAlgebra K)) := by
    -- Cache the finite-sum normalization for the quotient map instead of using a broad rewrite.
    exact map_sum q
      (fun p : {p // p ∈ t} ↦
        b p *
          (⟨Polynomial.monomial p.1.1 (p.1.2.1 : S),
              ideal_associated_graded_stage_monomial_mem K p.1.1 p.1.2.1⟩ :
            reesAlgebra K)) Finset.univ
  rw [hsum]
  calc
    q ⟨Polynomial.monomial n (y : S), ideal_associated_graded_stage_monomial_mem K n y⟩ -
        ∑ x : {p // p ∈ t},
          q
            (b x *
              (⟨Polynomial.monomial x.1.1 (x.1.2.1 : S),
                  ideal_associated_graded_stage_monomial_mem K x.1.1 x.1.2.1⟩ :
                reesAlgebra K)) =
      idealAssociatedGradedStageClass K n y -
        ∑ x : {p // p ∈ t},
          (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (b x) :
              idealAssociatedGradedRing K) *
            initialFormDataClass K J x.1 := by
        refine congrArg₂ HSub.hSub ?_ ?_
        · rfl
        · refine Finset.sum_congr rfl ?_
          intro x hx
          -- Each product normalizes by the quotient map's own multiplication rule.
          simpa [q, D, initialFormDataClass, idealAssociatedGradedStageClass] using
            q.map_mul (b x)
              (⟨Polynomial.monomial x.1.1 (x.1.2.1 : S),
                  ideal_associated_graded_stage_monomial_mem K x.1.1 x.1.2.1⟩ :
                reesAlgebra K)
    _ = 0 := by
      -- The normalized source relation is exactly the supplied quotient equality.
      simpa only [sub_eq_zero] using h

/-- Helper for Chap10 Lemma 10 97 5: the coefficient of the quotient-Rees residual gives the
one-step deeper `K`-adic congruence for the displayed initial-form correction. -/
private theorem reesCoefficients_initialForm_residual_mem_next
    {S : Type u} [CommRing S] (K J : Ideal S) {n : ℕ}
    {t : Finset (initialFormData K J)}
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n)
    (b : {p // p ∈ t} → reesAlgebra K)
    (h :
      idealAssociatedGradedStageClass K n y =
        ∑ p : {p // p ∈ t},
          (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (b p) :
              idealAssociatedGradedRing K) *
            initialFormDataClass K J p.1) :
    (y : S) -
        ∑ p : {p // p ∈ t},
          (if p.1.1 ≤ n then (b p).1.coeff (n - p.1.1) else 0) *
            (p.1.2.1 : S) ∈
      RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1) := by
  have hden :
      (⟨Polynomial.monomial n (y : S), ideal_associated_graded_stage_monomial_mem K n y⟩ -
        ∑ p : {p // p ∈ t},
          b p *
            (⟨Polynomial.monomial p.1.1 (p.1.2.1 : S),
                ideal_associated_graded_stage_monomial_mem K p.1.1 p.1.2.1⟩ :
              reesAlgebra K)) ∈
        Ideal.map (algebraMap S (reesAlgebra K)) K :=
    reesInitialFormResidual_mem_denominator K J y b h
  have hcoeff :
      ((⟨Polynomial.monomial n (y : S), ideal_associated_graded_stage_monomial_mem K n y⟩ -
        ∑ p : {p // p ∈ t},
          b p *
            (⟨Polynomial.monomial p.1.1 (p.1.2.1 : S),
                ideal_associated_graded_stage_monomial_mem K p.1.1 p.1.2.1⟩ :
              reesAlgebra K)) : reesAlgebra K).1.coeff n ∈ K ^ (n + 1) :=
    rees_algebra_coeff_mem_pow_succ_of_mem_denominator K n hden
  -- Coefficient `n` of the denominator residual is exactly the displayed source residual.
  simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top,
    Polynomial.coeff_sub, Polynomial.coeff_sum, coeff_mul_monomial_at] using hcoeff

/-- Helper for Chap10 Lemma 10 97 5: coefficients read from Rees representatives satisfy the
shifted `K`-adic bound needed for a one-step initial-form correction. -/
private theorem reesCoeffInitialCorrection_mem_pow
    {S : Type u} [CommRing S] (K J : Ideal S) {n : ℕ}
    {t : Finset (initialFormData K J)}
    (b : {p // p ∈ t} → reesAlgebra K) (p : {p // p ∈ t}) :
    (if p.1.1 ≤ n then (b p).1.coeff (n - p.1.1) else 0) ∈ K ^ (n - p.1.1) := by
  -- In the active degree branch this is exactly the Rees coefficient condition; the inactive
  -- branch contributes the zero coefficient.
  by_cases hpdeg : p.1.1 ≤ n
  · simpa [hpdeg] using (b p).2 (n - p.1.1)
  · simp [hpdeg]

/-- Helper for Chap10 Lemma 10 97 5: any finite displayed correction from the chosen initial
representatives belongs to the corresponding finite representative span. -/
private theorem initialRepresentative_sum_mem_span
    {S : Type u} [CommRing S] (K J : Ideal S)
    {t : Finset (initialFormData K J)}
    (c : {p // p ∈ t} → S) :
    (∑ p : {p // p ∈ t}, c p * (p.1.2.1 : S)) ∈
      Ideal.span ((fun p : initialFormData K J ↦ (p.2.1 : S)) ''
        (t : Set (initialFormData K J))) := by
  -- Each summand is a scalar multiple of one chosen representative, so the finite sum is in the
  -- ideal generated by those representatives.
  simpa using
    (Ideal.sum_mem
      (Ideal.span ((fun p : initialFormData K J ↦ (p.2.1 : S)) ''
        (t : Set (initialFormData K J))))
      (t := Finset.univ)
      (f := fun p : {p // p ∈ t} ↦ c p * (p.1.2.1 : S))
      (fun p hp ↦
        Ideal.mul_mem_left _ (c p) <| Ideal.subset_span ⟨p.1, p.2, rfl⟩))

/-- Helper for Chap10 Lemma 10 97 5: any finite displayed correction from initial-form data
still lies in the original ideal `J`. -/
private theorem initialRepresentative_sum_mem_ideal
    {S : Type u} [CommRing S] (K J : Ideal S)
    {t : Finset (initialFormData K J)}
    (c : {p // p ∈ t} → S) :
    (∑ p : {p // p ∈ t}, c p * (p.1.2.1 : S)) ∈ J := by
  -- The packaged representatives all lie in `J`, and ideals absorb ambient scalar multiples.
  simpa using
    (Ideal.sum_mem J
      (t := Finset.univ)
      (f := fun p : {p // p ∈ t} ↦ c p * (p.1.2.1 : S))
      (fun p hp ↦ J.mul_mem_left (c p) p.1.2.2))

/-- Helper for Chap10 Lemma 10 97 5: coefficient representatives from a finite initial-form
expression give one correction term in the finite representative span, leaving an error one
filtration step deeper. -/
private theorem initialForm_reesCoeff_oneStepCorrection
    {S : Type u} [CommRing S] (K J : Ideal S) {n : ℕ}
    {t : Finset (initialFormData K J)}
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n) (hyJ : (y : S) ∈ J)
    (b : {p // p ∈ t} → reesAlgebra K)
    (h :
      idealAssociatedGradedStageClass K n y =
        ∑ p : {p // p ∈ t},
          (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (b p) :
              idealAssociatedGradedRing K) *
            initialFormDataClass K J p.1) :
    ∃ c : {p // p ∈ t} → S,
      (∀ p, c p ∈ K ^ (n - p.1.1)) ∧
        (∑ p : {p // p ∈ t}, c p * (p.1.2.1 : S)) ∈
          Ideal.span ((fun p : initialFormData K J ↦ (p.2.1 : S)) ''
            (t : Set (initialFormData K J))) ∧
        (∑ p : {p // p ∈ t}, c p * (p.1.2.1 : S)) ∈ J ∧
        (y : S) - (∑ p : {p // p ∈ t}, c p * (p.1.2.1 : S)) ∈
          J ⊓ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1) := by
  let c : {p // p ∈ t} → S :=
    fun p ↦ if p.1.1 ≤ n then (b p).1.coeff (n - p.1.1) else 0
  refine ⟨c, ?_, ?_, ?_, ?_⟩
  · -- The Rees coefficient condition gives the shifted power bound for every coefficient.
    intro p
    exact reesCoeffInitialCorrection_mem_pow K J b p
  · -- The displayed correction is in the finite span of the chosen representatives.
    exact initialRepresentative_sum_mem_span K J c
  · -- The same correction remains in `J` because all initial representatives were chosen in `J`.
    exact initialRepresentative_sum_mem_ideal K J c
  · -- The residual is in `J` and, by coefficient extraction, in the next filtration stage.
    constructor
    · exact J.sub_mem hyJ (initialRepresentative_sum_mem_ideal K J c)
    · exact reesCoefficients_initialForm_residual_mem_next K J y b h

/-- Helper for Chap10 Lemma 10 97 5: equality of two degree-`n` stage classes is the same as
their difference lying one step deeper in the `K`-adic filtration. -/
private theorem stageClass_eq_iff_sub_mem_next
    {S : Type u} [CommRing S] (K : Ideal S) {n : ℕ}
    (x y : RingTheory.Sequence.idealAssociatedGradedStage K S n) :
    idealAssociatedGradedStageClass K n x = idealAssociatedGradedStageClass K n y ↔
      (x : S) - (y : S) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1) := by
  let xy : RingTheory.Sequence.idealAssociatedGradedStage K S n :=
    ⟨(x : S) - (y : S), Submodule.sub_mem _ x.2 y.2⟩
  have hxy_class :
      idealAssociatedGradedStageClass K n xy =
        idealAssociatedGradedStageClass K n x - idealAssociatedGradedStageClass K n y := by
    -- The linear stage-to-grade map records subtraction before forgetting the grade subtype.
    rw [← idealAssociatedGradedStageClassLinear_apply K n xy,
      ← idealAssociatedGradedStageClassLinear_apply K n x,
      ← idealAssociatedGradedStageClassLinear_apply K n y]
    exact congrArg Subtype.val ((idealAssociatedGradedStageClassLinear K n).map_sub x y)
  constructor
  · intro h
    -- Equal classes make the difference class vanish, hence the representative is in the next
    -- stage by the quotient-Rees zero criterion.
    exact (associated_graded_stage_class_zero_iff K n xy).1 <| by
      rw [hxy_class, h, sub_self]
  · intro hnext
    -- Conversely, next-stage membership kills the difference class and therefore the two classes
    -- are equal.
    have hzero : idealAssociatedGradedStageClass K n xy = 0 :=
      (associated_graded_stage_class_zero_iff K n xy).2 hnext
    rw [hxy_class] at hzero
    exact sub_eq_zero.mp hzero

/-- Helper for Chap10 Lemma 10 97 5: finite generation of `J/(J ∩ K)` gives finitely many
degree-zero lifts that correct every element of `J` modulo `J ∩ K`. -/
private lemma exists_degreeZeroCorrectionIdeal
    {S : Type u} [CommRing S] (K J : Ideal S)
    (h0 : Module.Finite S (J ⧸ (J ⊓ K).submoduleOf J)) :
    ∃ (r : ℕ) (a : Fin r → J),
      let L0 : Ideal S := Ideal.span (Set.range fun i : Fin r ↦ (a i : S))
      L0 ≤ J ∧ ∀ ⦃x : S⦄, x ∈ J → ∃ y ∈ L0, x - y ∈ J ⊓ K := by
  classical
  let N : Submodule S J := (J ⊓ K).submoduleOf J
  have hfgTop : (⊤ : Submodule S (J ⧸ N)).FG :=
    Module.Finite.fg_top (R := S) (M := J ⧸ N)
  obtain ⟨r, q, hqspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfgTop
  choose a ha using fun i : Fin r ↦ Submodule.mkQ_surjective N (q i)
  refine ⟨r, a, ?_⟩
  let L0 : Ideal S := Ideal.span (Set.range fun i : Fin r ↦ (a i : S))
  let Lsub : Submodule S J := Submodule.span S (Set.range a)
  have hL0_le_J : L0 ≤ J := by
    -- The chosen lifts all live in `J`, so their ambient span is contained in `J`.
    refine Ideal.span_le.mpr ?_
    rintro y ⟨i, rfl⟩
    exact (a i).2
  have hmap : Submodule.map (Submodule.mkQ N) Lsub = ⊤ := by
    -- The lifted generators still span after applying the quotient map.
    have himage : (Submodule.mkQ N) '' Set.range a = Set.range q := by
      ext y
      constructor
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (ha i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨a i, ⟨i, rfl⟩, ha i⟩
    change Submodule.map (Submodule.mkQ N) (Submodule.span S (Set.range a)) = ⊤
    rw [Submodule.map_span, himage, hqspan]
  have hLsub_to_L0 : Submodule.map J.subtype Lsub = L0 := by
    -- Passing from the submodule of `J` to the ambient ideal preserves the chosen span.
    change Submodule.map J.subtype (Submodule.span S (Set.range a)) =
      Ideal.span (Set.range fun i : Fin r ↦ (a i : S))
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨a i, ⟨i, rfl⟩, rfl⟩
  refine ⟨hL0_le_J, ?_⟩
  intro x hxJ
  let xJ : J := ⟨x, hxJ⟩
  have hxmap : Submodule.mkQ N xJ ∈ Submodule.map (Submodule.mkQ N) Lsub := by
    rw [hmap]
    exact Submodule.mem_top
  rcases hxmap with ⟨yJ, hyLsub, hqeq⟩
  refine ⟨(yJ : S), ?_, ?_⟩
  · -- The representative chosen in `J` belongs to the ambient correction ideal.
    have hyMap : (yJ : S) ∈ Submodule.map J.subtype Lsub := ⟨yJ, hyLsub, rfl⟩
    simpa [hLsub_to_L0] using hyMap
  · -- Equality in the quotient is exactly congruence modulo `J ∩ K`.
    have hdiffN : xJ - yJ ∈ N := (Submodule.Quotient.eq N).mp hqeq.symm
    simpa [N, xJ] using hdiffN

/-- Helper for Chap10 Lemma 10 97 5: a finite family of homogeneous initial-form data has a
uniform degree bound. -/
private theorem exists_initialFormData_degree_bound
    {S : Type u} [CommRing S] (K J : Ideal S) {t : Finset (initialFormData K J)} :
    ∃ D : ℕ, ∀ p : {p // p ∈ t}, p.1.1 ≤ D := by
  -- Take the supremum of the finitely many packaged degrees.
  refine ⟨t.sup fun p ↦ p.1, ?_⟩
  intro p
  exact Finset.le_sup p.2

/-- Helper for Chap10 Lemma 10 97 5: coefficient corrections with the shifted `K`-power bounds
form compatible partial sums after a common finite degree cutoff. -/
private theorem initialCorrectionPartialSums_compatible
    {S : Type u} [CommRing S] (K J : Ideal S) {t : Finset (initialFormData K J)}
    (D : ℕ) (hD : ∀ p : {p // p ∈ t}, p.1.1 ≤ D)
    (c : ℕ → {p // p ∈ t} → S)
    (hc : ∀ n p, c n p ∈ K ^ ((n + 1) - p.1.1)) :
    ∀ p : {p // p ∈ t}, ∀ {m n : ℕ}, m ≤ n →
      (∑ k ∈ Finset.range (m + D + 1), c k p) ≡
        (∑ k ∈ Finset.range (n + D + 1), c k p)
          [SMOD (K ^ m • (⊤ : Submodule S S))] := by
  intro p m n hmn
  rw [SModEq.sub_mem]
  have hAB : m + D + 1 ≤ n + D + 1 := by omega
  have htail : (∑ k ∈ Finset.Ico (m + D + 1) (n + D + 1), c k p) ∈ K ^ m := by
    -- Each tail coefficient lies in `K^m`, because the common cutoff dominates the degree of
    -- every chosen initial-form representative.
    apply Ideal.sum_mem
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hpow : m ≤ (k + 1) - p.1.1 := by
      apply Nat.le_sub_of_add_le
      have hpD := hD p
      omega
    exact Ideal.pow_le_pow_right (I := K) hpow (hc k p)
  have hdiff :
      (∑ k ∈ Finset.range (m + D + 1), c k p) -
          (∑ k ∈ Finset.range (n + D + 1), c k p) =
        -∑ k ∈ Finset.Ico (m + D + 1) (n + D + 1), c k p := by
    -- Rewrite the difference of partial sums as the negative tail between the two cutoffs.
    rw [Finset.sum_Ico_eq_sub (fun k ↦ c k p) hAB]
    abel
  rw [hdiff]
  simpa [Ideal.smul_eq_mul, Ideal.mul_top] using (K ^ m).neg_mem htail

/-- Helper for Chap10 Lemma 10 97 5: precompleteness gives coefficient limits for compatible
initial-correction partial sums. -/
private theorem exists_initialCorrectionCoefficientLimits
    {S : Type u} [CommRing S] (K J : Ideal S) [IsAdicComplete K S]
    {t : Finset (initialFormData K J)}
    (D : ℕ) (hD : ∀ p : {p // p ∈ t}, p.1.1 ≤ D)
    (c : ℕ → {p // p ∈ t} → S)
    (hc : ∀ n p, c n p ∈ K ^ ((n + 1) - p.1.1)) :
    ∃ b : {p // p ∈ t} → S,
      ∀ p N,
        (∑ k ∈ Finset.range (N + D + 1), c k p) ≡ b p
          [SMOD (K ^ N • (⊤ : Submodule S S))] := by
  classical
  -- Apply the owner precomplete API separately to each coefficient sequence.
  choose b hb using fun p : {p // p ∈ t} ↦
    IsAdicComplete.toIsPrecomplete.prec
      (f := fun N ↦ ∑ k ∈ Finset.range (N + D + 1), c k p)
      (initialCorrectionPartialSums_compatible K J D hD c hc p)
  exact ⟨b, fun p N ↦ hb p N⟩

/-- Helper for Chap10 Lemma 10 97 5: coefficient-wise `K`-adic congruences may be multiplied
by the fixed initial-form representatives and summed. -/
private theorem initialCorrectionRepresentativeSums_smodEq
    {S : Type u} [CommRing S] (K J : Ideal S) {t : Finset (initialFormData K J)}
    (a b : {p // p ∈ t} → S) (N : ℕ)
    (h : ∀ p, a p ≡ b p [SMOD (K ^ N • (⊤ : Submodule S S))]) :
    (∑ p : {p // p ∈ t}, a p * (p.1.2.1 : S)) ≡
      (∑ p : {p // p ∈ t}, b p * (p.1.2.1 : S))
        [SMOD (K ^ N • (⊤ : Submodule S S))] := by
  -- Use `SModEq.sum` after turning right multiplication by a fixed representative into scalar
  -- multiplication in the commutative ring.
  apply SModEq.sum
  intro p hp
  have hp' := SModEq.smul (h p) (p.1.2.1 : S)
  simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hp'

/-- Helper for Chap10 Lemma 10 97 5: the quotient-Rees coefficient normal form supplies one
coefficient-preserving initial-form correction. -/
private theorem initialForm_nextCorrectionData
    {S : Type u} [CommRing S] (K J : Ideal S) {n : ℕ}
    {t : Finset (initialFormData K J)}
    (hstageClass_reesCoefficients :
      ∀ n (y : RingTheory.Sequence.idealAssociatedGradedStage K S n), (y : S) ∈ J →
        ∃ b : {p // p ∈ t} → reesAlgebra K,
          idealAssociatedGradedStageClass K n y =
            ∑ p : {p // p ∈ t},
              (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (b p) :
                  idealAssociatedGradedRing K) *
                initialFormDataClass K J p.1)
    (y : RingTheory.Sequence.idealAssociatedGradedStage K S n) (hyJ : (y : S) ∈ J) :
    ∃ c : {p // p ∈ t} → S,
      (∀ p, c p ∈ K ^ (n - p.1.1)) ∧
        (∑ p : {p // p ∈ t}, c p * (p.1.2.1 : S)) ∈
          Ideal.span ((fun p : initialFormData K J ↦ (p.2.1 : S)) ''
            (t : Set (initialFormData K J))) ∧
        (∑ p : {p // p ∈ t}, c p * (p.1.2.1 : S)) ∈ J ∧
        (y : S) - (∑ p : {p // p ∈ t}, c p * (p.1.2.1 : S)) ∈
          J ⊓ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1) := by
  -- First lift the finite initial-form span relation to Rees representatives, then read off the
  -- coefficient correction and its shifted power bounds.
  obtain ⟨b, hb⟩ := hstageClass_reesCoefficients n y hyJ
  exact initialForm_reesCoeff_oneStepCorrection K J y hyJ b hb

/-- Helper for Chap10 Lemma 10 97 5: one degree-zero correction followed by recursive
initial-form corrections produces residuals one filtration step deeper at each stage. -/
private theorem exists_recursiveInitialCorrectionData
    {S : Type u} [CommRing S] (K J : Ideal S) {t : Finset (initialFormData K J)}
    (L0 : Ideal S)
    (hL0_correction : ∀ ⦃x : S⦄, x ∈ J → ∃ y ∈ L0, x - y ∈ J ⊓ K)
    (hstageClass_reesCoefficients :
      ∀ n (y : RingTheory.Sequence.idealAssociatedGradedStage K S n), (y : S) ∈ J →
        ∃ b : {p // p ∈ t} → reesAlgebra K,
          idealAssociatedGradedStageClass K n y =
            ∑ p : {p // p ∈ t},
              (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (b p) :
                  idealAssociatedGradedRing K) *
                initialFormDataClass K J p.1)
    {x : S} (hxJ : x ∈ J) :
    ∃ y0 ∈ L0, ∃ r : ℕ → S, ∃ c : ℕ → {p // p ∈ t} → S,
      r 0 = x - y0 ∧
        (∀ n, r n ∈ J ⊓ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1)) ∧
        (∀ n p, c n p ∈ K ^ ((n + 1) - p.1.1)) ∧
        (∀ n, r (n + 1) = r n - ∑ p : {p // p ∈ t}, c n p * (p.1.2.1 : S)) := by
  classical
  obtain ⟨y0, hy0L0, hres0⟩ := hL0_correction hxJ
  let Y : ℕ → Type u :=
    fun n ↦ {r : S // r ∈ J ⊓ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1)}
  let yInit : Y 0 :=
    ⟨x - y0, by
      -- The degree-zero correction leaves the initial residual in `J ∩ K = J ∩ K^1`.
      constructor
      · exact hres0.1
      · simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
          Ideal.mul_top] using hres0.2⟩
  let StepOut : (n : ℕ) → Y n → Type u :=
    fun n y ↦
      {out : ({p // p ∈ t} → S) × Y (n + 1) //
        (∀ p, out.1 p ∈ K ^ ((n + 1) - p.1.1)) ∧
          out.2.1 = y.1 - ∑ p : {p // p ∈ t}, out.1 p * (p.1.2.1 : S)}
  let step : (n : ℕ) → (y : Y n) → StepOut n y := fun n y ↦ by
    let yStage : RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1) :=
      ⟨y.1, y.2.2⟩
    let oneStep :=
      initialForm_nextCorrectionData K J hstageClass_reesCoefficients yStage y.2.1
    let c : {p // p ∈ t} → S := Classical.choose oneStep
    have hcPow : ∀ p, c p ∈ K ^ ((n + 1) - p.1.1) :=
      (Classical.choose_spec oneStep).1
    have hcResidual :
        (yStage : S) - (∑ p : {p // p ∈ t}, c p * (p.1.2.1 : S)) ∈
          J ⊓ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1 + 1) :=
      (Classical.choose_spec oneStep).2.2.2
    -- Store the chosen coefficients and the next residual together, so later projections are
    -- definitionally aligned with the recursive sequence.
    refine ⟨(c,
      ⟨y.1 - ∑ p : {p // p ∈ t}, c p * (p.1.2.1 : S), hcResidual⟩), ?_⟩
    exact ⟨hcPow, rfl⟩
  let rData : (n : ℕ) → Y n :=
    fun n ↦ Nat.rec (motive := fun m ↦ Y m) yInit
      (fun m y ↦ (step m y).1.2) n
  let r : ℕ → S := fun n ↦ (rData n).1
  let c : ℕ → {p // p ∈ t} → S := fun n ↦ (step n (rData n)).1.1
  refine ⟨y0, hy0L0, r, c, ?_, ?_, ?_, ?_⟩
  · -- At stage zero the recursive residual is the degree-zero residual.
    rfl
  · -- Every recursive residual carries its stored `J ∩ K^(n+1)` membership.
    intro n
    exact (rData n).2
  · -- Coefficient bounds are exactly the first stored property of each one-step correction.
    intro n p
    exact (step n (rData n)).2.1 p
  · -- The second stored property of the one-step correction is the recursive formula.
    intro n
    exact (step n (rData n)).2.2

/-- Helper for Chap10 Lemma 10 97 5: a sequence of residuals defined by subtracting successive
corrections telescopes to the original element minus the finite correction sum. -/
private theorem recursiveResidual_telescope
    {A : Type u} [AddCommGroup A] (x y0 : A) (r z : ℕ → A)
    (h0 : r 0 = x - y0) (hstep : ∀ n, r (n + 1) = r n - z n) :
    ∀ M, x - (y0 + ∑ k ∈ Finset.range M, z k) = r M := by
  intro M
  -- Inductively peel off the last correction and normalize the additive expression.
  induction M with
  | zero =>
      simpa [h0]
  | succ M ih =>
      rw [Finset.sum_range_succ, hstep M]
      rw [← ih]
      abel

/-- Helper for Chap10 Lemma 10 97 5: finite initial-correction sums may be interchanged so
partial sums are grouped by initial-form representative. -/
private theorem initialCorrection_doubleSum
    {S : Type u} [CommSemiring S] {α : Type u} [Fintype α]
    (M : ℕ) (c : ℕ → α → S) (rep : α → S) :
    (∑ k ∈ Finset.range M, ∑ p : α, c k p * rep p) =
      ∑ p : α, (∑ k ∈ Finset.range M, c k p) * rep p := by
  -- Swap the two finite sums, then factor the fixed representative out of the inner sum.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [Finset.sum_mul]

/-- Helper for Chap10 Lemma 10 97 5: recursive initial corrections and coefficient limits give
the finite representative approximation modulo every power of `K`. -/
private theorem initialCorrectionLimit_smodEq
    {S : Type u} [CommRing S] (K J : Ideal S) {t : Finset (initialFormData K J)}
    (D : ℕ) (x y0 : S) (r : ℕ → S) (c : ℕ → {p // p ∈ t} → S)
    (h0 : r 0 = x - y0)
    (hr : ∀ n, r n ∈ J ⊓ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1))
    (hstep :
      ∀ n, r (n + 1) = r n - ∑ p : {p // p ∈ t}, c n p * (p.1.2.1 : S))
    (b : {p // p ∈ t} → S)
    (hb : ∀ p N,
      (∑ k ∈ Finset.range (N + D + 1), c k p) ≡ b p
        [SMOD (K ^ N • (⊤ : Submodule S S))]) :
    ∀ N, x ≡ y0 + ∑ p : {p // p ∈ t}, b p * (p.1.2.1 : S)
      [SMOD (K ^ N • (⊤ : Submodule S S))] := by
  intro N
  let M : ℕ := N + D + 1
  let z : ℕ → S := fun k ↦ ∑ p : {p // p ∈ t}, c k p * (p.1.2.1 : S)
  have htel :
      x - (y0 + ∑ k ∈ Finset.range M, z k) = r M :=
    recursiveResidual_telescope x y0 r z h0 hstep M
  have hresPow : r M ∈ K ^ N := by
    -- The cutoff residual lies in `K^(M+1)`, which is contained in `K^N`.
    have hstage : r M ∈ RingTheory.Sequence.idealAssociatedGradedStage K S (M + 1) :=
      (hr M).2
    have hpowM : r M ∈ K ^ (M + 1) := by
      simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul,
        Ideal.mul_top] using hstage
    exact Ideal.pow_le_pow_right (I := K) (by omega) hpowM
  have hx_partial :
      x ≡ y0 + ∑ k ∈ Finset.range M, z k
        [SMOD (K ^ N • (⊤ : Submodule S S))] := by
    -- Telescoping reduces this congruence to the smallness of the cutoff residual.
    rw [SModEq.sub_mem]
    simpa [Ideal.smul_eq_mul, Ideal.mul_top, htel] using hresPow
  have hdouble :
      (∑ k ∈ Finset.range M, z k) =
        ∑ p : {p // p ∈ t}, (∑ k ∈ Finset.range M, c k p) * (p.1.2.1 : S) := by
    -- Regroup the finite correction sum by initial-form representative.
    simpa [z] using
      initialCorrection_doubleSum (S := S) (α := {p // p ∈ t}) M c
        (fun p ↦ (p.1.2.1 : S))
  have hx_grouped :
      x ≡
        y0 + ∑ p : {p // p ∈ t}, (∑ k ∈ Finset.range M, c k p) * (p.1.2.1 : S)
        [SMOD (K ^ N • (⊤ : Submodule S S))] := by
    simpa [M, hdouble] using hx_partial
  have hlimitCore :
      (∑ p : {p // p ∈ t}, (∑ k ∈ Finset.range M, c k p) * (p.1.2.1 : S)) ≡
        (∑ p : {p // p ∈ t}, b p * (p.1.2.1 : S))
          [SMOD (K ^ N • (⊤ : Submodule S S))] := by
    -- Coefficient-wise limits remain congruent after multiplication by fixed representatives and
    -- finite summation.
    simpa [M] using
      initialCorrectionRepresentativeSums_smodEq K J
        (fun p : {p // p ∈ t} ↦ ∑ k ∈ Finset.range M, c k p) b N
        (fun p ↦ by simpa [M] using hb p N)
  have hlimit :
      y0 + (∑ p : {p // p ∈ t}, (∑ k ∈ Finset.range M, c k p) * (p.1.2.1 : S)) ≡
        y0 + (∑ p : {p // p ∈ t}, b p * (p.1.2.1 : S))
          [SMOD (K ^ N • (⊤ : Submodule S S))] :=
    SModEq.add (SModEq.refl y0) hlimitCore
  exact hx_grouped.trans hlimit

/-- Helper for Chap10 Lemma 10 97 5: recursive initial-form corrections place every element of
`J` in the finite ideal generated by the degree-zero corrections and chosen initial
representatives. -/
private theorem mem_sup_degreeZero_initialFormSpan_of_recursiveCorrections
    {S : Type u} [CommRing S] (K J : Ideal S) [IsAdicComplete K S]
    {t : Finset (initialFormData K J)} (L0 : Ideal S)
    (hL0_correction : ∀ ⦃x : S⦄, x ∈ J → ∃ y ∈ L0, x - y ∈ J ⊓ K)
    (hstageClass_reesCoefficients :
      ∀ n (y : RingTheory.Sequence.idealAssociatedGradedStage K S n), (y : S) ∈ J →
        ∃ b : {p // p ∈ t} → reesAlgebra K,
          idealAssociatedGradedStageClass K n y =
            ∑ p : {p // p ∈ t},
              (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (b p) :
                  idealAssociatedGradedRing K) *
                initialFormDataClass K J p.1)
    {x : S} (hxJ : x ∈ J) :
    x ∈ L0 ⊔ Ideal.span ((fun p : initialFormData K J ↦ (p.2.1 : S)) ''
      (t : Set (initialFormData K J))) := by
  classical
  obtain ⟨y0, hy0L0, r, c, h0, hr, hc, hstep⟩ :=
    exists_recursiveInitialCorrectionData K J L0 hL0_correction
      hstageClass_reesCoefficients hxJ
  obtain ⟨D, hD⟩ := exists_initialFormData_degree_bound K J
  obtain ⟨b, hb⟩ := exists_initialCorrectionCoefficientLimits K J D hD c hc
  have hx_congr :
      ∀ N, x ≡ y0 + ∑ p : {p // p ∈ t}, b p * (p.1.2.1 : S)
        [SMOD (K ^ N • (⊤ : Submodule S S))] :=
    initialCorrectionLimit_smodEq K J D x y0 r c h0 hr hstep b hb
  have hx_eq :
      x = y0 + ∑ p : {p // p ∈ t}, b p * (p.1.2.1 : S) := by
    -- Hausdorffness upgrades the compatible congruences modulo all powers of `K` to equality.
    rw [IsHausdorff.eq_iff_smodEq (I := K)]
    exact hx_congr
  have hsum :
      (∑ p : {p // p ∈ t}, b p * (p.1.2.1 : S)) ∈
        Ideal.span ((fun p : initialFormData K J ↦ (p.2.1 : S)) ''
          (t : Set (initialFormData K J))) :=
    initialRepresentative_sum_mem_span K J b
  -- The Hausdorff limit is a sum of one element of `L0` and one element of the initial-form span.
  rw [hx_eq]
  exact Submodule.add_mem_sup hy0L0 hsum

/-- Chap10 Lemma 10 97 5: in a complete ring with finitely generated ideal and Noetherian
quotient, every ideal should be finitely generated. -/
private lemma ideal_fg_of_complete_fg_ideal_noetherian_quotient
    {S : Type u} [CommRing S] (K : Ideal S) [IsAdicComplete K S]
    (hKfg : K.FG) (hquot : IsNoetherianRing (S ⧸ K)) (J : Ideal S) :
    J.FG := by
  classical
  -- Route correction: the source proof must run through the associated graded kernel
  -- `⊕ (J ∩ K^n)/(J ∩ K^(n + 1))`, not through the false shortcut `J / KJ`.
  have himagefg : (Ideal.map (Ideal.Quotient.mk K) J).FG :=
    ideal_map_quotient_fg K J
  have hquotInfFinite : Module.Finite S (J ⧸ (J ⊓ K).submoduleOf J) :=
    ideal_quotient_inf_finite_of_noetherian_quotient K J
  have hpullback :
      Ideal.comap (Ideal.Quotient.mk K) (Ideal.map (Ideal.Quotient.mk K) J) = J ⊔ K :=
    comap_ideal_map_quotient_eq_sup K J
  have hzero_bridge :
      ∀ n (x : RingTheory.Sequence.idealAssociatedGradedStage K S n),
        idealAssociatedGradedStageClass K n x = 0 ↔
          (x : S) ∈ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1) := by
    intro n x
    exact associated_graded_stage_class_zero_iff K n x
  have hgr_noeth_of_presentation :
      ∀ {t : ℕ} (φ : MvPolynomial (Fin t) (S ⧸ K) →ₐ[S ⧸ K] idealAssociatedGradedRing K),
        Function.Surjective φ → IsNoetherianRing (idealAssociatedGradedRing K) := by
    intro t φ hφ
    -- This isolates the remaining source-faithful task to constructing the polynomial presentation
    -- from a finite set of generators of `K`.
    exact associated_graded_isNoetherian_of_surjective_mvPolynomial K φ hφ
  obtain ⟨t, g, hgspan⟩ := exists_fin_generating_family_of_ideal K hKfg
  let φ : MvPolynomial (Fin t) (S ⧸ K) →ₐ[S ⧸ K] idealAssociatedGradedRing K :=
    associated_graded_presentation K g
  have hgr_noeth_of_degree_one_adjoin :
      Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne (g i)) = ⊤ →
        IsNoetherianRing (idealAssociatedGradedRing K) := by
    intro hadjoin
    -- The adjoin-to-finite-type bridge isolates the remaining work to proving the source
    -- degree-one generation statement for `gr_K(S)`.
    exact associated_graded_isNoetherian_of_degree_one_adjoin_eq_top K g hadjoin
  have hφX :
      ∀ i : Fin t, φ (MvPolynomial.X i) = idealAssociatedGradedDegreeOne (g i) := by
    intro i
    simpa [φ] using associated_graded_presentation_X K g i
  have hdegreeOne_range :
      ∀ i : Fin t, idealAssociatedGradedDegreeOne (g i) ∈ Set.range φ := by
    intro i
    refine ⟨MvPolynomial.X i, ?_⟩
    simpa using hφX i
  have hpow_span :
      ∀ n,
        K ^ n =
          Ideal.span ((fun e : Fin t →₀ ℕ =>
            ∏ i : Fin t, ((g i : K) : S) ^ e i) '' {e | e.degree = n}) := by
    intro n
    -- This is the source monomial expansion of `K ^ n` attached to the fixed generators `g`.
    exact ideal_pow_eq_span_monomial_weight_of_generators K g hgspan n
  have hmonomial_mem_pow :
      ∀ e : Fin t →₀ ℕ, (∏ i : Fin t, ((g i : K) : S) ^ e i) ∈ K ^ e.degree := by
    intro e
    -- Each source monomial weight really is a degree-`e.degree` element of the `K`-adic
    -- filtration.
    exact monomial_weight_mem_ideal_pow_of_generators K g hgspan e
  have hdegreeOneAdjoin :
      Algebra.adjoin (S ⧸ K) (Set.range fun i : Fin t ↦ idealAssociatedGradedDegreeOne (g i)) =
        ⊤ := by
    -- The fixed degree-one classes generate every homogeneous stage class, hence the whole
    -- associated graded ring.
    exact associated_graded_degree_one_adjoin_eq_top K g hgspan
  have hgrNoeth : IsNoetherianRing (idealAssociatedGradedRing K) :=
    hgr_noeth_of_degree_one_adjoin hdegreeOneAdjoin
  letI : IsNoetherianRing (idealAssociatedGradedRing K) := hgrNoeth
  have hinitialFG : (associatedGradedInitialIdeal K J).FG :=
    associatedGradedInitialIdeal_fg K J
  obtain ⟨tInitial, htInitialSpan⟩ :=
    exists_initialFormData_finset_span K J hinitialFG
  obtain ⟨r0, a0, hdegreeZeroData⟩ :=
    exists_degreeZeroCorrectionIdeal K J hquotInfFinite
  let L0 : Ideal S := Ideal.span (Set.range fun i : Fin r0 ↦ (a0 i : S))
  have hL0_le_J : L0 ≤ J := hdegreeZeroData.1
  have hL0_correction : ∀ ⦃x : S⦄, x ∈ J → ∃ y ∈ L0, x - y ∈ J ⊓ K :=
    hdegreeZeroData.2
  let initialRepresentative : initialFormData K J → S := fun p ↦ (p.2.1 : S)
  let Linitial : Ideal S :=
    Ideal.span (initialRepresentative '' (tInitial : Set (initialFormData K J)))
  let L : Ideal S := L0 ⊔ Linitial
  have hLinitial_le_J : Linitial ≤ J := by
    -- Every homogeneous representative was packaged with its membership in `J`.
    refine Ideal.span_le.mpr ?_
    rintro x ⟨p, hp, rfl⟩
    exact p.2.2
  have hL_le_J : L ≤ J := by
    -- Both degree-zero correction lifts and homogeneous initial-form representatives lie in `J`.
    exact sup_le hL0_le_J hLinitial_le_J
  have hL0_FG : L0.FG := by
    -- The degree-zero correction ideal is spanned by the finite family chosen above.
    refine ⟨Finset.univ.image (fun i : Fin r0 ↦ (a0 i : S)), ?_⟩
    simp [L0]
  have hLinitial_FG : Linitial.FG := by
    -- The homogeneous correction part is spanned by the extracted finite initial-form set.
    refine ⟨tInitial.image initialRepresentative, ?_⟩
    simp [Linitial, initialRepresentative]
  have hL_FG : L.FG := by
    -- The final candidate correction ideal is finite as the sum of two finite ideals.
    exact Submodule.FG.sup hL0_FG hLinitial_FG
  have hstageClass_initialSpan :
      ∀ n (y : RingTheory.Sequence.idealAssociatedGradedStage K S n), (y : S) ∈ J →
        idealAssociatedGradedStageClass K n y ∈
          Ideal.span (initialFormDataClass K J ''
            (tInitial : Set (initialFormData K J))) := by
    intro n y hyJ
    -- The initial ideal has already been replaced by the finite chosen homogeneous generators.
    exact stageClass_mem_initialFormData_finset_span K J htInitialSpan y hyJ
  have hstageClass_reesCoefficients :
      ∀ n (y : RingTheory.Sequence.idealAssociatedGradedStage K S n), (y : S) ∈ J →
        ∃ b : {p // p ∈ tInitial} → reesAlgebra K,
          idealAssociatedGradedStageClass K n y =
            ∑ p : {p // p ∈ tInitial},
              (Ideal.Quotient.mk (Ideal.map (algebraMap S (reesAlgebra K)) K) (b p) :
                  idealAssociatedGradedRing K) *
                initialFormDataClass K J p.1 := by
    intro n y hyJ
    -- Finite initial-form span membership is now in the quotient-Rees coefficient normal form
    -- required for the next coefficient-extraction step.
    exact initialFormSpan_exists_reesCoefficients K J y (hstageClass_initialSpan n y hyJ)
  have hinitial_oneStep :
      ∀ n (y : RingTheory.Sequence.idealAssociatedGradedStage K S n), (y : S) ∈ J →
        ∃ z ∈ Linitial, z ∈ J ∧
          (y : S) - z ∈ J ⊓ RingTheory.Sequence.idealAssociatedGradedStage K S (n + 1) := by
    intro n y hyJ
    obtain ⟨c, hcPow, hcSpan, hcJ, hcResidual⟩ :=
      initialForm_nextCorrectionData K J hstageClass_reesCoefficients y hyJ
    -- Package the coefficient correction as an element of the finite initial-representative span.
    refine ⟨∑ p : {p // p ∈ tInitial}, c p * (p.1.2.1 : S), ?_, hcJ, hcResidual⟩
    simpa [Linitial, initialRepresentative] using hcSpan
  -- These closed facts now match the source setup more closely. The naive quotient-image route
  -- only controls `J / (J ∩ K)`, while `hzero_bridge` supplies the owner/piece zero criterion
  -- needed for the real source route on `⊕ (J ∩ K^n)/(J ∩ K^(n + 1))`. The new bridge
  -- `hgr_noeth_of_presentation` and the new adjoin bridge
  -- `hgr_noeth_of_degree_one_adjoin` now isolate the graded Noetherian step to two equivalent
  -- source-faithful frontiers: either prove the literal surjective presentation
  -- `(S ⧸ K)[T_1, ..., T_t] ↠ gr_K(S)`, or prove directly that the degree-one classes of the
  -- chosen generators adjoin to all of `gr_K(S)`. The closed monomial-span data `hpow_span` and
  -- `hmonomial_mem_pow`, together with `hdegreeOne_range`, prove that generation step. The
  -- initial ideal is now finite (`hinitialFG`) and reindexed by the finite homogeneous data
  -- `tInitial`; the candidate finite correction ideal `L = L0 ⊔ Linitial` is contained in `J`
  -- and is finitely generated by `hL_FG`. The new `hstageClass_reesCoefficients` frontier
  -- has already turned finite initial-form span membership into quotient-Rees coefficient
  -- representatives. The recursive correction helper below now combines those coefficients with
  -- precompleteness and Hausdorffness to show every `x ∈ J` lies in `L = L0 ⊔ Linitial`.
  have hJ_le_L : J ≤ L := by
    intro x hxJ
    -- Apply the recursive correction and Hausdorff closure helper to place `x` in the finite
    -- correction ideal.
    simpa [L, Linitial, initialRepresentative] using
      mem_sup_degreeZero_initialFormSpan_of_recursiveCorrections K J L0 hL0_correction
        hstageClass_reesCoefficients hxJ
  have hJL : J = L := le_antisymm hJ_le_L hL_le_J
  -- Transport finite generation across the equality `J = L`.
  rw [hJL]
  exact hL_FG

/-- Consequence of Chap10 Lemma 10 97 5: if `R ⧸ I` is Noetherian and `I` is finitely generated,
then the `I`-adic completion `AdicCompletion I R` is a Noetherian ring and is complete for the
adic topology defined by the extended ideal `I.map (algebraMap R (AdicCompletion I R))`. -/
@[stacks 05GH]
lemma adicCompletion_isNoetherian_and_isAdicComplete
    (hI : I.FG) :
    IsNoetherianRing (AdicCompletion I R) ∧
      IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) := by
  constructor
  ·
    -- Route correction: the tempting quotient-image route `J / KJ ≃ J.map (Ideal.Quotient.mk K)`
    -- is false in general because the kernel of `J → S ⧸ K` is `J ⊓ K`, not `KJ`.
    refine (isNoetherianRing_iff_ideal_fg (AdicCompletion I R)).2 ?_
    intro J
    let K : Ideal (AdicCompletion I R) := I.map (algebraMap R (AdicCompletion I R))
    have hcompleteK : IsAdicComplete K (AdicCompletion I R) := by
      simpa [K] using completion_ideal_isAdicComplete (I := I) hI
    letI : IsAdicComplete K (AdicCompletion I R) := hcompleteK
    have hquot :
        IsNoetherianRing ((AdicCompletion I R) ⧸ K) := by
      simpa [K] using completion_quotient_isNoetherianRing (I := I) hI
    have hKfg : K.FG := by
      simpa [K] using Ideal.FG.map hI (algebraMap R (AdicCompletion I R))
    -- The theorem-specific work is now reduced to the complete-ring frontier above.
    exact @ideal_fg_of_complete_fg_ideal_noetherian_quotient
      (AdicCompletion I R) _ K hcompleteK hKfg hquot J
  ·
    exact completion_ideal_isAdicComplete (I := I) hI

end
