import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_69_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Ideal

universe u v w

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {S : Type w} [CommRing S] [Algebra R S] [Module.Flat R S]

/- 
Domain triage:
* primary domain: quasi-regular sequences in commutative algebra and their behavior under flat
  base change;
* sampled owner API:
  `RingTheory.Sequence.IsQuasiRegular`,
  `IsBaseChange.linearMap`,
  `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`,
  `RingTheory.Sequence.IsWeaklyRegular.of_flat`;
* source-facing layer: `RingTheory.Sequence.IsQuasiRegular M rs`;
* core/canonical owner abstraction for base change: `IsBaseChange S f`;
* bridge/view split: quasi-regularity is the source-facing graded-comparison predicate, while
  flat-base-change transport is best organized first through the owner abstraction `IsBaseChange`
  and only then specialized to the canonical tensor-product model.
-/

-- Proof sketch: write quasi-regularity via the associated graded map from `10.69.0.1`. Flatness
-- identifies `(Ideal.ofList rs ^ n) • ⊤` after tensoring with the corresponding powers of the
-- extended ideal, and the graded pieces commute with tensor product. Tensoring the defining
-- isomorphism for `rs` with `S` then yields the quasi-regularity criterion for the image sequence
-- on `S ⊗[R] M`, the canonical Lean model for the textbook tensor product `M ⊗[R] S`.
namespace IsQuasiRegular

variable {N : Type v} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Helper for Lemma 10.69.3: every source tensor is a finite sum of monomial simple tensors with
quotient-module coefficients. -/
private theorem tensor_monomial_expansion
    {A : Type*} [CommRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    (rs : List A)
    (z : (P ⧸ ((Ideal.ofList rs) • (⊤ : Submodule A P))) ⊗[A ⧸ Ideal.ofList rs]
      MvPolynomial (Fin rs.length) (A ⧸ Ideal.ofList rs)) :
    ∃ coeffs : (Fin rs.length →₀ ℕ) →₀ (P ⧸ ((Ideal.ofList rs) • (⊤ : Submodule A P))),
      z =
        coeffs.sum fun e q ↦
          (q ⊗ₜ[A ⧸ Ideal.ofList rs]
            MvPolynomial.monomial e (1 : A ⧸ Ideal.ofList rs)) := by
  let comm :=
    TensorProduct.comm (A ⧸ Ideal.ofList rs)
      (P ⧸ ((Ideal.ofList rs) • (⊤ : Submodule A P)))
      (MvPolynomial (Fin rs.length) (A ⧸ Ideal.ofList rs))
  let scalar :=
    MvPolynomial.scalarRTensor
      (R := A ⧸ Ideal.ofList rs)
      (σ := Fin rs.length)
      (N := P ⧸ ((Ideal.ofList rs) • (⊤ : Submodule A P)))
  let coeffs :
      (Fin rs.length →₀ ℕ) →₀ (P ⧸ ((Ideal.ofList rs) • (⊤ : Submodule A P))) :=
    scalar (comm z)
  refine ⟨coeffs, ?_⟩
  -- Pass to the commuted tensor product, where `scalarRTensor` identifies the source with a
  -- finitely supported coefficient family.
  apply comm.injective
  calc
    comm z = scalar.symm coeffs := by
      simp [coeffs]
    _ = scalar.symm (coeffs.sum fun e q ↦ Finsupp.single e q) := by
      simp
    _ = coeffs.sum fun e q ↦ scalar.symm (Finsupp.single e q) := by
      simp [Finsupp.sum]
    _ = coeffs.sum fun e q ↦
          (MvPolynomial.monomial e (1 : A ⧸ Ideal.ofList rs)) ⊗ₜ[A ⧸ Ideal.ofList rs] q := by
      refine Finsupp.sum_congr ?_
      intro e q
      rw [MvPolynomial.scalarRTensor_symm_apply_single]
    _ = comm
          (coeffs.sum fun e q ↦
            (q ⊗ₜ[A ⧸ Ideal.ofList rs]
              MvPolynomial.monomial e (1 : A ⧸ Ideal.ofList rs))) := by
      simp only [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl ?_
      intro e he
      rw [TensorProduct.comm_tmul]

/-- Helper for Lemma 10.69.3: the monomial weight attached to an exponent vector lies in the
matching power of `Ideal.ofList rs`. -/
private theorem ofList_monomial_weight_mem_pow
    {A : Type*} [CommRing A] (rs : List A) (e : Fin rs.length →₀ ℕ) :
    (∏ i : Fin rs.length, rs.get i ^ e i) ∈ (Ideal.ofList rs) ^ e.degree := by
  -- Each factor already lies in the corresponding ideal power, so the full product lands in the
  -- total-degree power after normalizing the product of powers.
  have hprod :
      (∏ i : Fin rs.length, rs.get i ^ e i) ∈
        ∏ i : Fin rs.length, (Ideal.ofList rs) ^ e i := by
    refine Ideal.prod_mem_prod ?_
    intro i hi
    exact Ideal.pow_mem_pow
      (Ideal.subset_span (by simpa using List.getElem_mem rs i))
      (e i)
  simpa [Finsupp.degree_eq_sum, Finset.prod_pow_eq_pow_sum] using hprod

/-- Helper for Lemma 10.69.3: a homogeneous weighted monomial term of total degree `n` lies in the
`n`th filtration stage. -/
private theorem ofList_monomial_weight_smul_mem_of_degree
    {A : Type*} [CommRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    (rs : List A) (n : ℕ) (m : P) (e : Fin rs.length →₀ ℕ) (hdeg : e.degree = n) :
    (∏ i : Fin rs.length, rs.get i ^ e i) • m ∈
      idealAssociatedGradedStage (Ideal.ofList rs) P n := by
  -- Rewrite the stage as `J ^ n • ⊤` and combine monomial-weight membership with the trivial
  -- membership of `m` in the top submodule.
  simpa [idealAssociatedGradedStage, hdeg] using
    (Submodule.smul_mem_smul
      (ofList_monomial_weight_mem_pow rs e)
      (by simp : m ∈ (⊤ : Submodule A P)))

/-- Helper for Lemma 10.69.3: reinserting the degree-`n` component of a monomial image keeps the
same image exactly in degree `n`. -/
private theorem quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_lof
    {A : Type*} [CommRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    {rs : List A} (m : P) (e : Fin rs.length →₀ ℕ) :
    let J : Ideal A := Ideal.ofList rs
    quasiRegularSequenceAssociatedGradedMap P rs
      (((Submodule.Quotient.mk m : P ⧸ (J • (⊤ : Submodule A P))) ⊗ₜ[A ⧸ J]
        MvPolynomial.monomial e (1 : A ⧸ J))) =
      DirectSum.lof (A ⧸ J) ℕ (idealAssociatedGradedPiece J P) e.degree
        (Submodule.Quotient.mk
          (⟨(∏ i : Fin rs.length, rs.get i ^ e i) • m,
            ofList_monomial_weight_smul_mem_of_degree rs e.degree m e rfl⟩ :
            idealAssociatedGradedStage J P e.degree)) := by
  -- Reuse the public owner computations from `10.69.0.1` instead of rebuilding the transport
  -- chain locally.
  dsimp [quasiRegularSequenceAssociatedGradedMap]
  let z := quasiRegularAssociatedGradedInternalMonomialClass rs m e
  have hcomm :=
    quasiRegularSequenceAssociatedGradedSourceComm_tmul P rs m e
  have haux :=
    quasiRegularSequenceAssociatedGradedMapAux_tmul_monomial P rs m e
  have hlof := quasiRegularAssociatedGradedAddEquiv_symm_lof P rs e.degree z
  have hpiece :=
    quasiRegularAssociatedGradedInternalPieceEquiv_monomialClass P rs m e
  -- Each owner-level rewrite now lands exactly on the textbook degree-`e.degree` class.
  rw [hcomm, haux, hlof, hpiece]
  rfl

/-- Helper for Lemma 10.69.3: injectivity transports across a commuting square whose horizontal
maps are equivalences. -/
private theorem injective_iff_of_equiv_conjugate
    {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
    (eSrc : α ≃ β) (eTgt : γ ≃ δ)
    (f : α → γ) (g : β → δ)
    (hcomm : eTgt ∘ f = g ∘ eSrc) :
    Function.Injective f ↔ Function.Injective g := by
  -- Move equalities through the source and target equivalences to compare injectivity on either
  -- side of the conjugation square.
  constructor
  · intro hf x y hxy
    apply eSrc.symm.injective
    apply hf
    apply eTgt.injective
    calc
      eTgt (f (eSrc.symm x)) = g x := by
        simpa [Function.comp] using congrFun hcomm (eSrc.symm x)
      _ = g y := hxy
      _ = eTgt (f (eSrc.symm y)) := by
        simpa [Function.comp] using (congrFun hcomm (eSrc.symm y)).symm
  · intro hg x y hxy
    apply eSrc.injective
    apply hg
    calc
      g (eSrc x) = eTgt (f x) := by
        simpa [Function.comp] using (congrFun hcomm x).symm
      _ = eTgt (f y) := by rw [hxy]
      _ = g (eSrc y) := by
        simpa [Function.comp] using congrFun hcomm y

/-- Helper for Chap10 Lemma 10 69 3: the ambient `R`-action on a quotient by `I • ⊤` factors
through the quotient ring `R ⧸ I`. -/
private theorem quotient_smul_eq_quotient_mk
    (I : Ideal R) (r : R) (x : M ⧸ (I • (⊤ : Submodule R M))) :
    r • x = ((Ideal.Quotient.mk I r : R ⧸ I) • x) := by
  -- Reduce to representatives; both actions are induced by the same scalar action on `M`.
  refine Quotient.inductionOn' x ?_
  intro m
  rfl

/-- Helper for Chap10 Lemma 10 69 3: on the source tensor of the associated-graded comparison,
the `R`-action agrees with scalar multiplication by the corresponding constant polynomial. -/
private theorem sourceScalarAlgebraMap_smul
    (rs : List R) (r : R)
    (x : (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :
    r • x =
      (algebraMap R (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) r) • x := by
  -- Check the scalar comparison on simple tensors; additivity gives the full tensor statement.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro q p
    let J : Ideal R := Ideal.ofList rs
    let A := MvPolynomial (Fin rs.length) (R ⧸ J)
    calc
      r • (q ⊗ₜ[R ⧸ J] p) = (r • q) ⊗ₜ[R ⧸ J] p := by
        rw [TensorProduct.smul_tmul']
      _ = ((Ideal.Quotient.mk J r : R ⧸ J) • q) ⊗ₜ[R ⧸ J] p := by
        rw [quotient_smul_eq_quotient_mk]
      _ = q ⊗ₜ[R ⧸ J] ((algebraMap R A r) * p) := by
        simpa [A, J, Algebra.smul_def] using
          (TensorProduct.tmul_smul (R := R ⧸ J) (R' := R ⧸ J)
            (r := (Ideal.Quotient.mk J r : R ⧸ J)) (x := q) (y := p)).symm
      _ = (algebraMap R A r) • (q ⊗ₜ[R ⧸ J] p) := by
        rfl
  · intro x y hx hy
    simp [smul_add, hx, hy]

/-- Helper for Lemma 10.69.3: an `S`-linear equivalence transports the degree-zero quotient
submodule `Ideal.ofList rs • ⊤` to the corresponding submodule in the target module. -/
private theorem ofList_smul_top_map_eq_linear
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) {rs : List S} :
    ((Ideal.ofList rs) • (⊤ : Submodule S P)).map e.toLinearMap =
      Ideal.ofList rs • (⊤ : Submodule S Q) := by
  -- The source proof first transports the degree-zero quotient submodule, and for a linear
  -- equivalence this is exactly `map_smul''` followed by `map_top`.
  calc
    ((Ideal.ofList rs) • (⊤ : Submodule S P)).map e.toLinearMap
        = Ideal.ofList rs • (⊤ : Submodule S P).map e.toLinearMap := by
          rw [Submodule.map_smul'']
    _ = Ideal.ofList rs • (⊤ : Submodule S Q) := by
          rw [Submodule.map_top, LinearMap.range_eq_top.2 e.surjective]

/-- Helper for Lemma 10.69.3: after restricting scalars along `S → S ⧸ I`, the original
`S`-action agrees with the quotient-ring scalar action. -/
private theorem ideal_scalar_action_eq_quotient_scalar_action
    (I : Ideal S) {P : Type*} [AddCommGroup P] [Module (S ⧸ I) P] [Module S P]
    [IsScalarTower S (S ⧸ I) P]
    (s : S) (x : P) :
    s • x = ((Ideal.Quotient.mk I) s : S ⧸ I) • x := by
  -- Rewrite the restricted scalar action through the quotient-ring unit.
  calc
    s • x = s • ((1 : S ⧸ I) • x) := by simp
    _ = (s • (1 : S ⧸ I)) • x := by rw [smul_assoc]
    _ = ((Ideal.Quotient.mk I) s : S ⧸ I) • x := by
      change ((((Ideal.Quotient.mk I) s : S ⧸ I) * 1) : S ⧸ I) • x =
        ((Ideal.Quotient.mk I) s : S ⧸ I) • x
      simp

/-- Helper for Lemma 10.69.3: an `S`-linear equivalence between modules already defined over
`S ⧸ I` is automatically `(S ⧸ I)`-linear. -/
private theorem linearEquiv_map_smul_over_quotient
    (I : Ideal S)
    {P : Type*} [AddCommGroup P] [Module (S ⧸ I) P] [Module S P]
    [IsScalarTower S (S ⧸ I) P]
    {Q : Type*} [AddCommGroup Q] [Module (S ⧸ I) Q] [Module S Q]
    [IsScalarTower S (S ⧸ I) Q]
    (e : P ≃ₗ[S] Q) (c : S ⧸ I) (x : P) :
    e (c • x) = c • e x := by
  -- Reduce quotient scalars to representatives in `S` and use `S`-linearity of `e`.
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← ideal_scalar_action_eq_quotient_scalar_action (I := I) s x]
  rw [e.map_smul]
  rw [ideal_scalar_action_eq_quotient_scalar_action (I := I) s (e x)]

/-- Helper for Lemma 10.69.3: an `S`-linear equivalence between modules already defined over
`S ⧸ I` can be promoted to an `(S ⧸ I)`-linear equivalence. -/
private def linearEquiv_over_quotient
    (I : Ideal S)
    {P : Type*} [AddCommGroup P] [Module (S ⧸ I) P] [Module S P]
    [IsScalarTower S (S ⧸ I) P]
    {Q : Type*} [AddCommGroup Q] [Module (S ⧸ I) Q] [Module S Q]
    [IsScalarTower S (S ⧸ I) Q]
    (e : P ≃ₗ[S] Q) : P ≃ₗ[S ⧸ I] Q :=
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := linearEquiv_map_smul_over_quotient (I := I) e }

/-- Helper for Lemma 10.69.3: an `S`-linear equivalence descends to the quotient by
`Ideal.ofList rs • ⊤`. -/
private noncomputable def ofList_smul_top_quotientLinearEquiv
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) :
    (P ⧸ (Ideal.ofList rs • (⊤ : Submodule S P))) ≃ₗ[S ⧸ Ideal.ofList rs]
      (Q ⧸ (Ideal.ofList rs • (⊤ : Submodule S Q))) :=
  linearEquiv_over_quotient (I := Ideal.ofList rs) <|
    Submodule.Quotient.equiv
      (Ideal.ofList rs • (⊤ : Submodule S P))
      (Ideal.ofList rs • (⊤ : Submodule S Q))
      e
      (ofList_smul_top_map_eq_linear (e := e) (rs := rs))

/-- Helper for Lemma 10.69.3: the descended quotient equivalence still acts on representatives
through the original linear equivalence. -/
@[simp] private theorem ofList_smul_top_quotientLinearEquiv_apply_mk
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (x : P) :
    ofList_smul_top_quotientLinearEquiv (e := e) rs (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := by
  -- Unfold the descended equivalence once and evaluate the quotient map on the chosen
  -- representative.
  simp [ofList_smul_top_quotientLinearEquiv, linearEquiv_over_quotient]

/-- Helper for Lemma 10.69.3: an `S`-linear equivalence transports the `n`th stage
`(Ideal.ofList rs)^n • ⊤` of the filtration to the corresponding stage in the target module. -/
private theorem ofList_pow_smul_top_map_eq_linear
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (n : ℕ) :
    ((((Ideal.ofList rs) ^ n) • (⊤ : Submodule S P)).map e.toLinearMap) =
      ((Ideal.ofList rs) ^ n) • (⊤ : Submodule S Q) := by
  -- Each stage is again an ideal-smul-top submodule, so the degree-zero transport argument
  -- applies verbatim.
  calc
    ((((Ideal.ofList rs) ^ n) • (⊤ : Submodule S P)).map e.toLinearMap)
        = ((Ideal.ofList rs) ^ n) • (⊤ : Submodule S P).map e.toLinearMap := by
          rw [Submodule.map_smul'']
    _ = ((Ideal.ofList rs) ^ n) • (⊤ : Submodule S Q) := by
          rw [Submodule.map_top, LinearMap.range_eq_top.2 e.surjective]

/-- Helper for Lemma 10.69.3: restrict an ambient linear equivalence to the `n`th filtration
stage. -/
private noncomputable def idealAssociatedGradedStage_linearEquiv
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (n : ℕ) :
    idealAssociatedGradedStage (Ideal.ofList rs) P n ≃ₗ[S]
      idealAssociatedGradedStage (Ideal.ofList rs) Q n := by
  let Pn : Submodule S P := idealAssociatedGradedStage (Ideal.ofList rs) P n
  let Qn : Submodule S Q := idealAssociatedGradedStage (Ideal.ofList rs) Q n
  have hPn : Pn.map (e : P →ₗ[S] Q) = Qn := by
    simpa [Pn, Qn, idealAssociatedGradedStage] using ofList_pow_smul_top_map_eq_linear
      (e := e) rs n
  -- Restrict `e` to the stage `Pn` and rewrite the codomain using the explicit mapped-stage
  -- equality.
  exact (e.submoduleMap Pn).trans (LinearEquiv.ofEq _ _ hPn)

/-- Helper for Lemma 10.69.3: on stage representatives, the restricted equivalence is induced by
the ambient linear equivalence. -/
@[simp] private theorem idealAssociatedGradedStage_linearEquiv_apply
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (n : ℕ)
    (x : idealAssociatedGradedStage (Ideal.ofList rs) P n) :
    ((idealAssociatedGradedStage_linearEquiv (e := e) rs n x :
        idealAssociatedGradedStage (Ideal.ofList rs) Q n) : Q) = e x := by
  -- Unfold the stage transport once; on representatives it is exactly the ambient map `e`.
  simp [idealAssociatedGradedStage_linearEquiv]

/-- Helper for Lemma 10.69.3: on stage representatives, the inverse restricted equivalence is
induced by the inverse ambient linear equivalence. -/
@[simp] private theorem idealAssociatedGradedStage_linearEquiv_symm_apply
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (n : ℕ)
    (x : idealAssociatedGradedStage (Ideal.ofList rs) Q n) :
    (((idealAssociatedGradedStage_linearEquiv (e := e) rs n).symm x :
        idealAssociatedGradedStage (Ideal.ofList rs) P n) : P) = e.symm x := by
  -- Rewrite the inverse through the corresponding stage transport for `e.symm`.
  simp [idealAssociatedGradedStage_linearEquiv]

/-- Helper for Lemma 10.69.3: each graded piece `J^n P / J^(n + 1) P` transports linearly along an
ambient `S`-linear equivalence. -/
private noncomputable def idealAssociatedGradedPiece_linearEquiv
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (n : ℕ) :
    idealAssociatedGradedPiece (Ideal.ofList rs) P n ≃ₗ[S]
      idealAssociatedGradedPiece (Ideal.ofList rs) Q n := by
  let J : Ideal S := Ideal.ofList rs
  let Pn : Submodule S P := idealAssociatedGradedStage J P n
  let Qn : Submodule S Q := idealAssociatedGradedStage J Q n
  let Pn1 : Submodule S Pn := (idealAssociatedGradedStage J P (n + 1)).submoduleOf Pn
  let Qn1 : Submodule S Qn := (idealAssociatedGradedStage J Q (n + 1)).submoduleOf Qn
  let eStage : Pn ≃ₗ[S] Qn := idealAssociatedGradedStage_linearEquiv (e := e) rs n
  have hmap : Pn1.map eStage.toLinearMap = Qn1 := by
    -- Transport the successor stage through the restricted equivalence by checking both
    -- inclusions on explicit stage representatives.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ((eStage x : Qn) : Q) ∈ idealAssociatedGradedStage J Q (n + 1)
      exact
        ((idealAssociatedGradedStage_linearEquiv (e := e) rs (n + 1)
          ⟨(x : P), hx⟩ :
            idealAssociatedGradedStage J Q (n + 1))).property
    · intro hy
      refine ⟨eStage.symm y, ?_, by simp [eStage]⟩
      change ((eStage.symm y : Pn) : P) ∈ idealAssociatedGradedStage J P (n + 1)
      simpa [eStage] using
        ((idealAssociatedGradedStage_linearEquiv (e := e) rs (n + 1)).symm
          ⟨(y : Q), hy⟩).property
  -- Descend the stage equivalence to the quotient by the successor stage.
  exact Submodule.Quotient.equiv Pn1 Qn1 eStage hmap

/-- Helper for Lemma 10.69.3: the piece transport acts on quotient representatives by the stage
transport. -/
@[simp] private theorem idealAssociatedGradedPiece_linearEquiv_apply_mk
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (n : ℕ)
    (x : idealAssociatedGradedStage (Ideal.ofList rs) P n) :
    idealAssociatedGradedPiece_linearEquiv (e := e) rs n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (idealAssociatedGradedStage_linearEquiv (e := e) rs n x) := by
  -- The quotient transport is induced by `Submodule.Quotient.equiv`, so it still evaluates on
  -- representatives by the underlying stage equivalence.
  simp [idealAssociatedGradedPiece_linearEquiv]

/-- Helper for Lemma 10.69.3: the full associated graded module transports degreewise along an
ambient `S`-linear equivalence. -/
private noncomputable def idealAssociatedGradedModule_congr_linearEquiv
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) :
    idealAssociatedGradedModule (Ideal.ofList rs) P ≃ₗ[S]
      idealAssociatedGradedModule (Ideal.ofList rs) Q := by
  -- Package the degreewise quotient equivalences into the direct-sum transport.
  exact DirectSum.congrLinearEquiv fun n ↦ idealAssociatedGradedPiece_linearEquiv (e := e) rs n

/-- Helper for Lemma 10.69.3: the direct-sum transport preserves homogeneous generators degreewise.
-/
@[simp] private theorem idealAssociatedGradedModule_congr_linearEquiv_lof
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (n : ℕ)
    (z : idealAssociatedGradedPiece (Ideal.ofList rs) P n) :
    idealAssociatedGradedModule_congr_linearEquiv (e := e) rs
        (DirectSum.lof S ℕ (idealAssociatedGradedPiece (Ideal.ofList rs) P) n z) =
      DirectSum.lof S ℕ (idealAssociatedGradedPiece (Ideal.ofList rs) Q) n
        (idealAssociatedGradedPiece_linearEquiv (e := e) rs n z) := by
  -- `DirectSum.congrLinearEquiv` is induced by `DirectSum.lmap`, whose effect on `lof` is explicit.
  simpa [idealAssociatedGradedModule_congr_linearEquiv, DirectSum.coe_congrLinearEquiv] using
    (DirectSum.lmap_lof
      (R := S)
      (f := fun n ↦ (idealAssociatedGradedPiece_linearEquiv (e := e) rs n).toLinearMap)
      n z)

/-- Helper for Lemma 10.69.3: the associated-graded transport preserves homogeneous `DirectSum.of`
generators, independently of the scalar ring used to spell `DirectSum.lof`. -/
@[simp] private theorem idealAssociatedGradedModule_congr_linearEquiv_of
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (n : ℕ)
    (z : idealAssociatedGradedPiece (Ideal.ofList rs) P n) :
    idealAssociatedGradedModule_congr_linearEquiv (e := e) rs
        (DirectSum.of (idealAssociatedGradedPiece (Ideal.ofList rs) P) n z) =
      DirectSum.of (idealAssociatedGradedPiece (Ideal.ofList rs) Q) n
        (idealAssociatedGradedPiece_linearEquiv (e := e) rs n z) := by
  -- Convert through the `S`-linear `lof` computation once; subsequent uses can rewrite the
  -- additive direct-sum generator without forcing the scalar-ring parameter to unify.
  simpa [DirectSum.lof_eq_of] using
    idealAssociatedGradedModule_congr_linearEquiv_lof (e := e) rs n z

/-- Helper for Lemma 10.69.3: on monomial simple tensors, the canonical associated-graded map
commutes with the quotient and graded-piece transports induced by an ambient linear equivalence. -/
private theorem quasiRegularSequenceAssociatedGradedMap_linear_naturality_tmul
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (m : P) (d : Fin rs.length →₀ ℕ) :
    let eSrc :
        ((P ⧸ (Ideal.ofList rs • (⊤ : Submodule S P))) ⊗[S ⧸ Ideal.ofList rs]
          MvPolynomial (Fin rs.length) (S ⧸ Ideal.ofList rs)) ≃
          ((Q ⧸ (Ideal.ofList rs • (⊤ : Submodule S Q))) ⊗[S ⧸ Ideal.ofList rs]
            MvPolynomial (Fin rs.length) (S ⧸ Ideal.ofList rs)) :=
      (TensorProduct.congr
        (ofList_smul_top_quotientLinearEquiv (e := e) rs)
        (LinearEquiv.refl (S ⧸ Ideal.ofList rs)
          (MvPolynomial (Fin rs.length) (S ⧸ Ideal.ofList rs)))).toEquiv
    let eTgt :
        idealAssociatedGradedModule (Ideal.ofList rs) P ≃
          idealAssociatedGradedModule (Ideal.ofList rs) Q :=
      (idealAssociatedGradedModule_congr_linearEquiv (e := e) rs).toEquiv
    eTgt
        (quasiRegularSequenceAssociatedGradedMap P rs
          (Submodule.Quotient.mk m ⊗ₜ[S ⧸ Ideal.ofList rs]
            MvPolynomial.monomial d (1 : S ⧸ Ideal.ofList rs))) =
      quasiRegularSequenceAssociatedGradedMap Q rs
        (eSrc
          (Submodule.Quotient.mk m ⊗ₜ[S ⧸ Ideal.ofList rs]
            MvPolynomial.monomial d (1 : S ⧸ Ideal.ofList rs))) := by
  -- Rewrite both sides on the monomial generator and compare the resulting homogeneous stage
  -- classes after transporting the representative by `e`.
  dsimp
  rw [ofList_smul_top_quotientLinearEquiv_apply_mk]
  rw [quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_lof (P := P) (rs := rs) m d]
  rw [quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_lof (P := Q) (rs := rs) (e m) d]
  rw [DirectSum.lof_eq_of, idealAssociatedGradedModule_congr_linearEquiv_of,
    idealAssociatedGradedPiece_linearEquiv_apply_mk]
  rw [DirectSum.lof_eq_of]
  -- The stage representative is transported by the ambient linear equivalence, and the ambient
  -- map preserves scalar multiplication by the monomial weight.
  congr 1
  congr 1
  ext
  simp [idealAssociatedGradedStage_linearEquiv_apply, e.map_smul]

/-- Helper for Lemma 10.69.3: after transporting the quotient source and each graded piece along
an ambient linear equivalence, the canonical associated-graded map is conjugated by those
transports. -/
private theorem quasiRegularSequenceAssociatedGradedMap_linear_naturality
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) :
    let eSrc :
        ((P ⧸ (Ideal.ofList rs • (⊤ : Submodule S P))) ⊗[S ⧸ Ideal.ofList rs]
          MvPolynomial (Fin rs.length) (S ⧸ Ideal.ofList rs)) ≃
          ((Q ⧸ (Ideal.ofList rs • (⊤ : Submodule S Q))) ⊗[S ⧸ Ideal.ofList rs]
            MvPolynomial (Fin rs.length) (S ⧸ Ideal.ofList rs)) :=
      (TensorProduct.congr
        (ofList_smul_top_quotientLinearEquiv (e := e) rs)
        (LinearEquiv.refl (S ⧸ Ideal.ofList rs)
          (MvPolynomial (Fin rs.length) (S ⧸ Ideal.ofList rs)))).toEquiv
    let eTgt :
        idealAssociatedGradedModule (Ideal.ofList rs) P ≃
          idealAssociatedGradedModule (Ideal.ofList rs) Q :=
      (idealAssociatedGradedModule_congr_linearEquiv (e := e) rs).toEquiv
    eTgt ∘ quasiRegularSequenceAssociatedGradedMap P rs =
      quasiRegularSequenceAssociatedGradedMap Q rs ∘ eSrc := by
  -- Expand an arbitrary source tensor into a finite sum of monomial simple tensors, then use the
  -- monomial conjugation formula termwise and reassemble by linearity.
  dsimp
  funext z
  obtain ⟨coeffs, hcoeffs⟩ := tensor_monomial_expansion (P := P) rs z
  rw [hcoeffs]
  rw [Finsupp.sum]
  simp only [Function.comp_apply, map_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  refine Quotient.inductionOn' (coeffs d) ?_
  intro m
  simpa using quasiRegularSequenceAssociatedGradedMap_linear_naturality_tmul
    (e := e) rs m d

/-- Helper for Lemma 10.69.3: quasi-regularity is invariant under `S`-linear equivalence of the
ambient module. -/
private theorem congr_linearEquiv
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) {rs : List S} :
    IsQuasiRegular P rs ↔ IsQuasiRegular Q rs := by
  -- Rewrite quasi-regularity as injectivity of the canonical associated-graded comparison maps.
  rw [isQuasiRegular_iff_injective, isQuasiRegular_iff_injective]
  let eSrc :
      ((P ⧸ (Ideal.ofList rs • (⊤ : Submodule S P))) ⊗[S ⧸ Ideal.ofList rs]
        MvPolynomial (Fin rs.length) (S ⧸ Ideal.ofList rs)) ≃
        ((Q ⧸ (Ideal.ofList rs • (⊤ : Submodule S Q))) ⊗[S ⧸ Ideal.ofList rs]
          MvPolynomial (Fin rs.length) (S ⧸ Ideal.ofList rs)) :=
    (TensorProduct.congr
      (ofList_smul_top_quotientLinearEquiv (e := e) rs)
      (LinearEquiv.refl (S ⧸ Ideal.ofList rs)
        (MvPolynomial (Fin rs.length) (S ⧸ Ideal.ofList rs)))).toEquiv
  let eTgt :
      idealAssociatedGradedModule (Ideal.ofList rs) P ≃
        idealAssociatedGradedModule (Ideal.ofList rs) Q :=
    (idealAssociatedGradedModule_congr_linearEquiv (e := e) rs).toEquiv
  -- Once the conjugation square is isolated, injectivity transports across the source and target
  -- equivalences by the general equivalence-level lemma above.
  exact
    injective_iff_of_equiv_conjugate eSrc eTgt
      (quasiRegularSequenceAssociatedGradedMap P rs)
      (quasiRegularSequenceAssociatedGradedMap Q rs)
      (quasiRegularSequenceAssociatedGradedMap_linear_naturality (e := e) rs)

-- Proof sketch: first normalize scalar extension of `J • ⊤` at the level of submodules, then use
-- the flat `toBaseChange` equivalence to identify each tensor-side filtration stage with the
-- literal stage for the image ideal.
omit [Module.Flat R S] in
/-- Helper for Lemma 10.69.3: flat base change sends the submodule `J M` to the corresponding
submodule for the mapped ideal. -/
private theorem smulTop_baseChange_eq (J : Ideal R) :
    (((J • (⊤ : Submodule R M)).baseChange S : Submodule S (S ⊗[R] M))) =
      (J.map (algebraMap R S)) • (⊤ : Submodule S (S ⊗[R] M)) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.baseChange_eq_span]
    -- Rewrite a base-change generator `1 ⊗ x` with `x ∈ J M` as the image ideal acting on a
    -- denominator-one tensor generator.
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m hm
      have hrewrite :
          (1 ⊗ₜ[R] (r • m) : S ⊗[R] M) = ((algebraMap R S) r) • (1 ⊗ₜ[R] m) := by
        calc
          (1 ⊗ₜ[R] (r • m) : S ⊗[R] M) = (r • (1 : S)) ⊗ₜ[R] m := by
            rw [TensorProduct.smul_tmul]
          _ = ((algebraMap R S) r) • (1 ⊗ₜ[R] m) := by
            simp [Algebra.smul_def, TensorProduct.smul_tmul']
      change (1 ⊗ₜ[R] (r • m) : S ⊗[R] M) ∈
        (J.map (algebraMap R S)) • (⊤ : Submodule S (S ⊗[R] M))
      rw [hrewrite]
      exact Submodule.smul_mem_smul
        (Ideal.mem_map_of_mem (algebraMap R S) hr)
        (by simp : (1 ⊗ₜ[R] m : S ⊗[R] M) ∈ (⊤ : Submodule S (S ⊗[R] M)))
    · intro x y hx hy
      change (1 ⊗ₜ[R] (x + y) : S ⊗[R] M) ∈
        (J.map (algebraMap R S)) • (⊤ : Submodule S (S ⊗[R] M))
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy
  ·
    -- Reduce the target ideal-smul submodule to generators `algebraMap r • z` and prove each
    -- such generator lies in the tensor-span of `J M`.
    intro z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro s hs z hz
      clear hz
      -- The mapped ideal is the `S`-span of the image of `J`, so it is enough to check image
      -- generators and the span closure operations for the fixed tensor `z`.
      rw [Ideal.map] at hs
      refine Submodule.span_induction
        (p := fun s _ ↦ s • z ∈
          ((J • (⊤ : Submodule R M)).baseChange S : Submodule S (S ⊗[R] M)))
        ?_ ?_ ?_ ?_ hs
      · rintro _ ⟨r, hr, rfl⟩
        refine TensorProduct.induction_on z ?_ ?_ ?_
        · simp
        · intro a m
          have hrewrite :
              (((algebraMap R S) r) • (a ⊗ₜ[R] m) : S ⊗[R] M) =
                a ⊗ₜ[R] (r • m) := by
            calc
              (((algebraMap R S) r) • (a ⊗ₜ[R] m) : S ⊗[R] M) =
                  ((algebraMap R S r) • a) ⊗ₜ[R] m := by
                rw [TensorProduct.smul_tmul']
              _ = (r • a) ⊗ₜ[R] m := by
                simp [Algebra.smul_def]
              _ = a ⊗ₜ[R] (r • m) := by
                rw [TensorProduct.smul_tmul]
          rw [hrewrite]
          exact Submodule.tmul_mem_baseChange_of_mem a
            (Submodule.smul_mem_smul hr (by simp))
        · intro x y hx hy
          simpa [smul_add] using Submodule.add_mem _ hx hy
      · simp
      · intro x y _ _ hx hy
        simpa [add_smul] using Submodule.add_mem _ hx hy
      · intro a x _ hx
        simpa [smul_smul] using Submodule.smul_mem _ a hx
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy

/-- Helper for Lemma 10.69.3: after tensoring with `S`, the `n`th stage `J^n M` is canonically
identified with the corresponding stage for the image ideal. -/
private noncomputable def tensorBaseChangeStage_linearEquiv
    (rs : List R) (n : ℕ) :
    S ⊗[R] idealAssociatedGradedStage (Ideal.ofList rs) M n ≃ₗ[S]
      idealAssociatedGradedStage
        (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n := by
  let J : Ideal R := Ideal.ofList rs
  have hstage :
      (idealAssociatedGradedStage J M n).baseChange S =
        idealAssociatedGradedStage
          (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n := by
    -- Expand the stage as `J ^ n • ⊤` and rewrite scalar extension by the mapped ideal power.
    simpa [J, idealAssociatedGradedStage, Ideal.map_pow, Ideal.map_ofList] using
      smulTop_baseChange_eq (R := R) (M := M) (S := S) (J := J ^ n)
  -- First pass from tensors on the subtype `J^n M` to the literal base-changed submodule, then
  -- rewrite that base-changed submodule to the target stage.
  exact
    (Submodule.toBaseChange.toLinearEquiv S (idealAssociatedGradedStage J M n)).trans
      (LinearEquiv.ofEq _ _ hstage)

/-- Helper for Lemma 10.69.3: on denominator-one tensors, the stage base-change equivalence is
the tautological inclusion into the tensor product stage. -/
@[simp] private theorem tensorBaseChangeStage_linearEquiv_apply_one_tmul
    (rs : List R) (n : ℕ) (x : idealAssociatedGradedStage (Ideal.ofList rs) M n) :
    ((tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs n
        (1 ⊗ₜ[R] x) :
          idealAssociatedGradedStage
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n) :
        S ⊗[R] M) =
      (1 ⊗ₜ[R] (x : M)) := by
  -- Unfold the base-change equivalence once; the flat `toBaseChange` inverse is already
  -- normalized on denominator-one tensors.
  simp [tensorBaseChangeStage_linearEquiv, LinearEquiv.trans_apply]

/-- Helper for Lemma 10.69.3: the stage base-change equivalence sends arbitrary simple tensors to
their tautological image in the target tensor-product stage. -/
@[simp] private theorem tensorBaseChangeStage_linearEquiv_apply_tmul
    (rs : List R) (n : ℕ) (s : S)
    (x : idealAssociatedGradedStage (Ideal.ofList rs) M n) :
    ((tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs n
        (s ⊗ₜ[R] x) :
          idealAssociatedGradedStage
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n) :
        S ⊗[R] M) =
      (s ⊗ₜ[R] (x : M)) := by
  -- Reduce an arbitrary simple tensor to an `S`-multiple of the denominator-one tensor and use
  -- the already-normalized computation for `1 ⊗ x`.
  have htensor : (s ⊗ₜ[R] x : S ⊗[R] idealAssociatedGradedStage (Ideal.ofList rs) M n) =
      s • (1 ⊗ₜ[R] x) := by
    rw [TensorProduct.smul_tmul']
    simp
  calc
    ((tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs n
        (s ⊗ₜ[R] x) :
          idealAssociatedGradedStage
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n) :
        S ⊗[R] M)
        = ((tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs n
            (s • (1 ⊗ₜ[R] x)) :
              idealAssociatedGradedStage
                (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n) :
            S ⊗[R] M) := by rw [htensor]
    _ = s •
        ((tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs n
          (1 ⊗ₜ[R] x) :
            idealAssociatedGradedStage
              (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n) :
          S ⊗[R] M) := by simp
    _ = s • (1 ⊗ₜ[R] (x : M) : S ⊗[R] M) := by
      rw [tensorBaseChangeStage_linearEquiv_apply_one_tmul]
    _ = (s ⊗ₜ[R] (x : M) : S ⊗[R] M) := by
      rw [TensorProduct.smul_tmul']
      simp

/-- Helper for Lemma 10.69.3: filtration stages decrease by one step. -/
private theorem idealAssociatedGradedStage_succ_le (I : Ideal R) (n : ℕ) :
    idealAssociatedGradedStage I M (n + 1) ≤ idealAssociatedGradedStage I M n := by
  -- The ideal powers are decreasing, and smul by the top submodule preserves inclusions.
  exact Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) le_rfl

/-- Helper for Lemma 10.69.3: after rewriting the successor stage as a submodule of the previous
stage, tensoring its inclusion and applying the degree-`n` base-change equivalence agrees, on
underlying tensor representatives, with the degree-`n + 1` base-change equivalence. -/
private theorem tensorBaseChangeStage_linearEquiv_lTensor_subtype_apply
    (rs : List R) (n : ℕ)
    (z : S ⊗[R] idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1)) :
    (((tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs n)
        (((TensorProduct.AlgebraTensorModule.lTensor S S)
          (((idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1)).submoduleOf
            (idealAssociatedGradedStage (Ideal.ofList rs) M n)).subtype))
          ((LinearEquiv.lTensor S
            (Submodule.comapSubtypeEquivOfLe
              (idealAssociatedGradedStage_succ_le (M := M) (Ideal.ofList rs) n)).symm) z)) :
          idealAssociatedGradedStage
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n) :
        S ⊗[R] M) =
      (((tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs (n + 1)) z :
          idealAssociatedGradedStage
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) (n + 1)) :
        S ⊗[R] M) := by
  -- Check the compatibility on simple tensors; additivity then gives the statement for all
  -- tensor representatives.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · rw [LinearEquiv.map_zero]
    erw [LinearMap.map_zero]
    simp
  · intro s x
    have htensor :
        ((TensorProduct.AlgebraTensorModule.lTensor S S)
          (((idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1)).submoduleOf
            (idealAssociatedGradedStage (Ideal.ofList rs) M n)).subtype))
            (s ⊗ₜ[R]
              (Submodule.comapSubtypeEquivOfLe
                (idealAssociatedGradedStage_succ_le (M := M) (Ideal.ofList rs) n)).symm x) =
          s ⊗ₜ[R]
            (((idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1)).submoduleOf
              (idealAssociatedGradedStage (Ideal.ofList rs) M n)).subtype
                ((Submodule.comapSubtypeEquivOfLe
                  (idealAssociatedGradedStage_succ_le (M := M) (Ideal.ofList rs) n)).symm x)) := by
      exact TensorProduct.AlgebraTensorModule.lTensor_tmul _ _ _
    rw [LinearEquiv.lTensor_tmul]
    erw [htensor]
    rw [tensorBaseChangeStage_linearEquiv_apply_tmul]
    rw [tensorBaseChangeStage_linearEquiv_apply_tmul]
    rfl
  · intro x y hx hy
    rw [map_add]
    erw [map_add]
    rw [map_add]
    rw [Submodule.coe_add, hx, hy]
    rw [map_add, Submodule.coe_add]

/-- Helper for Lemma 10.69.3: the tensor quotient denominator for the source degree-`n` graded
piece is carried by the stage base-change equivalence to the target successor-stage denominator.
-/
private theorem tensorBaseChangeSuccessorSubmodule_map_eq
    (rs : List R) (n : ℕ) :
    (LinearMap.range
        ((TensorProduct.AlgebraTensorModule.lTensor S S)
          (((idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1)).submoduleOf
            (idealAssociatedGradedStage (Ideal.ofList rs) M n)).subtype))).map
        (tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs n).toLinearMap =
      (idealAssociatedGradedStage
        (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) (n + 1)).submoduleOf
        (idealAssociatedGradedStage
          (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n) := by
  -- Compare membership in the two submodules by moving through the raw successor stage and the
  -- stage-compatibility lemma above.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, rfl⟩
    let hle :=
      idealAssociatedGradedStage_succ_le (M := M) (Ideal.ofList rs) n
    let zRaw :
        S ⊗[R] idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1) :=
      (LinearEquiv.lTensor S (Submodule.comapSubtypeEquivOfLe hle)) z
    have hz :
        (LinearEquiv.lTensor S (Submodule.comapSubtypeEquivOfLe hle).symm) zRaw = z := by
      simpa [zRaw, LinearEquiv.coe_lTensor_symm] using
        (LinearEquiv.lTensor S (Submodule.comapSubtypeEquivOfLe hle)).left_inv z
    have hcompat :=
      tensorBaseChangeStage_linearEquiv_lTensor_subtype_apply
        (R := R) (M := M) (S := S) rs n zRaw
    rw [hz] at hcompat
    change
      (((tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs n)
          (((TensorProduct.AlgebraTensorModule.lTensor S S)
            (((idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1)).submoduleOf
              (idealAssociatedGradedStage (Ideal.ofList rs) M n)).subtype)) z) :
        idealAssociatedGradedStage
          (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n) :
        S ⊗[R] M) ∈
      idealAssociatedGradedStage
        (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) (n + 1)
    rw [hcompat]
    exact
      ((tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs (n + 1))
        zRaw).property
  · intro hy
    let hle :=
      idealAssociatedGradedStage_succ_le (M := M) (Ideal.ofList rs) n
    let yRaw :
        idealAssociatedGradedStage
          (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) (n + 1) :=
      ⟨(y : S ⊗[R] M), hy⟩
    let zRaw :
        S ⊗[R] idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1) :=
      (tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs (n + 1)).symm
        yRaw
    let z :
        S ⊗[R]
          (((idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1)).submoduleOf
            (idealAssociatedGradedStage (Ideal.ofList rs) M n))) :=
      (LinearEquiv.lTensor S (Submodule.comapSubtypeEquivOfLe hle).symm) zRaw
    refine ⟨
      ((TensorProduct.AlgebraTensorModule.lTensor S S)
        (((idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1)).submoduleOf
          (idealAssociatedGradedStage (Ideal.ofList rs) M n)).subtype)) z,
      ⟨z, rfl⟩, ?_⟩
    ext
    simpa [yRaw, zRaw, z] using
      tensorBaseChangeStage_linearEquiv_lTensor_subtype_apply
        (R := R) (M := M) (S := S) rs n zRaw

/-- Helper for Lemma 10.69.3: scalar extension commutes with the degree-`n` associated-graded
piece for the ideal generated by `rs`. -/
private noncomputable def tensorBaseChangeGradedPiece_linearEquiv
    (rs : List R) (n : ℕ) :
    S ⊗[R] idealAssociatedGradedPiece (Ideal.ofList rs) M n ≃ₗ[S]
      idealAssociatedGradedPiece
        (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := R) S R S
    ((idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1)).submoduleOf
      (idealAssociatedGradedStage (Ideal.ofList rs) M n))).trans
    (Submodule.Quotient.equiv
      (LinearMap.range
        ((TensorProduct.AlgebraTensorModule.lTensor S S)
          (((idealAssociatedGradedStage (Ideal.ofList rs) M (n + 1)).submoduleOf
            (idealAssociatedGradedStage (Ideal.ofList rs) M n)).subtype)))
      ((idealAssociatedGradedStage
        (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) (n + 1)).submoduleOf
        (idealAssociatedGradedStage
          (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n))
      (tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs n)
      (tensorBaseChangeSuccessorSubmodule_map_eq (R := R) (M := M) (S := S) rs n))

/-- Helper for Lemma 10.69.3: the degreewise graded-piece base-change equivalence has the
expected formula on quotient representatives of simple tensors. -/
@[simp] private theorem tensorBaseChangeGradedPiece_linearEquiv_apply_tmul_mk
    (rs : List R) (n : ℕ) (s : S)
    (x : idealAssociatedGradedStage (Ideal.ofList rs) M n) :
    tensorBaseChangeGradedPiece_linearEquiv (R := R) (M := M) (S := S) rs n
        (s ⊗ₜ[R] (Submodule.Quotient.mk x :
          idealAssociatedGradedPiece (Ideal.ofList rs) M n)) =
      Submodule.Quotient.mk
        (tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs n
          (s ⊗ₜ[R] x)) := by
  -- The equivalence is a tensor-quotient comparison followed by quotient transport through the
  -- stage equivalence, so both components compute directly on representatives.
  rw [tensorBaseChangeGradedPiece_linearEquiv]
  rw [LinearEquiv.trans_apply]
  rw [TensorProduct.AlgebraTensorModule.tensorQuotientEquiv_apply_tmul]
  erw [Submodule.Quotient.equiv_apply]
  erw [Submodule.mapQ_apply]
  rfl

omit [Module.Flat R S] in
/-- Helper for Lemma 10.69.3: mapped monomial weights act on scalar-extended simple tensors by
tensoring the original monomial-weight action. -/
private theorem mapped_ofList_monomial_weight_smul_tmul
    (rs : List R) (s : S) (m : M) (d : Fin rs.length →₀ ℕ) :
    ((∏ i : Fin rs.length, (algebraMap R S (rs.get i)) ^ d i) •
        (s ⊗ₜ[R] m) : S ⊗[R] M) =
      s ⊗ₜ[R] ((∏ i : Fin rs.length, rs.get i ^ d i) • m) := by
  -- First identify the mapped product with the image of the original product, then move the
  -- original scalar across the tensor product.
  let a : R := ∏ i : Fin rs.length, rs.get i ^ d i
  have hmap :
      (algebraMap R S) a =
        ∏ i : Fin rs.length, (algebraMap R S (rs.get i)) ^ d i := by
    simp [a]
  calc
    ((∏ i : Fin rs.length, (algebraMap R S (rs.get i)) ^ d i) •
        (s ⊗ₜ[R] m) : S ⊗[R] M)
        = ((algebraMap R S) a) • (s ⊗ₜ[R] m) := by rw [hmap]
    _ = (((algebraMap R S) a) • s) ⊗ₜ[R] m := by rw [TensorProduct.smul_tmul']
    _ = (a • s) ⊗ₜ[R] m := by simp [Algebra.smul_def]
    _ = s ⊗ₜ[R] (a • m) := by rw [TensorProduct.smul_tmul]
    _ = s ⊗ₜ[R] ((∏ i : Fin rs.length, rs.get i ^ d i) • m) := by rfl

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: after transporting exponents along `List.length_map`, the
mapped-list monomial weight acts on a simple tensor as the original source weight. -/
private theorem mapped_ofList_monomial_weight_cast_smul_tmul
    (rs : List R) (s : S) (m : M) (d : Fin rs.length →₀ ℕ) :
    ((∏ j : Fin (rs.map (algebraMap R S)).length,
          (rs.map (algebraMap R S)).get j ^
            (d.mapDomain (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm)) j) •
        (s ⊗ₜ[R] m) : S ⊗[R] M) =
      s ⊗ₜ[R] ((∏ i : Fin rs.length, rs.get i ^ d i) • m) := by
  -- Reindex the finite product along the canonical equality of lengths, then use the established
  -- mapped-weight formula without any remaining casts.
  have hprod :
      (∏ j : Fin (rs.map (algebraMap R S)).length,
          (rs.map (algebraMap R S)).get j ^
            (d.mapDomain (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm)) j) =
        ∏ i : Fin rs.length, (algebraMap R S (rs.get i)) ^ d i := by
    let e : Fin rs.length ≃ Fin (rs.map (algebraMap R S)).length :=
      finCongr (List.length_map (as := rs) (algebraMap R S)).symm
    symm
    refine Fintype.prod_equiv e
      (fun i : Fin rs.length ↦ (algebraMap R S (rs.get i)) ^ d i)
      (fun j : Fin (rs.map (algebraMap R S)).length ↦
        (rs.map (algebraMap R S)).get j ^
          (d.mapDomain (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm)) j) ?_
    intro i
    dsimp [e]
    rw [Finsupp.mapDomain_apply]
    · simp
    · exact Fin.cast_injective _
  rw [hprod]
  exact mapped_ofList_monomial_weight_smul_tmul (R := R) (M := M) (S := S) rs s m d

omit [Module.Flat R S] in
/-- Helper for Lemma 10.69.3: the submodule generated by the mapped sequence in the tensor base
change is the same as the extension of the source-list submodule. -/
private theorem ofList_map_smul_top_eq_idealMap_ofList_smul_top
    (rs : List R) :
    (Ideal.ofList (rs.map (algebraMap R S)) •
        (⊤ : Submodule S (S ⊗[R] M))) =
      (Ideal.map (algebraMap R S) (Ideal.ofList rs) •
        (⊤ : Submodule S (S ⊗[R] M))) := by
  -- Normalize the target ideal generated by mapped entries to the mapped source ideal.
  rw [Ideal.map_ofList]

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the mapped ideal annihilates the scalar extension of the
degree-zero source quotient. -/
private theorem tensorQuotientOfListMapEquiv_target_isTorsionBySet
    (rs : List R) :
    Module.IsTorsionBySet S
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))))
      (Ideal.ofList (rs.map (algebraMap R S))) := by
  -- It is enough to check simple tensors and mapped generators of `Ideal.ofList rs`.
  intro x a
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · rw [smul_zero]
  · intro s q
    have ha :
        (a : S) ∈ Ideal.map (algebraMap R S) (Ideal.ofList rs) := by
      simpa [Ideal.map_ofList] using a.property
    refine Submodule.span_induction
      (p := fun b _ ↦
        b • (s ⊗ₜ[R] q :
          S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) = 0)
      ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨r, hr, rfl⟩
      have hrq : r • q = 0 := by
        refine Quotient.inductionOn' q ?_
        intro m
        exact (Submodule.Quotient.mk_eq_zero _).2
          (Submodule.smul_mem_smul hr (by simp : m ∈ (⊤ : Submodule R M)))
      calc
        ((algebraMap R S r) •
            (s ⊗ₜ[R] q :
              S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))))
            = ((algebraMap R S r) • s) ⊗ₜ[R] q := by
              rw [TensorProduct.smul_tmul']
        _ = (r • s) ⊗ₜ[R] q := by
              simp [Algebra.smul_def]
        _ = s ⊗ₜ[R] (r • q) := by
              rw [TensorProduct.smul_tmul]
        _ = 0 := by
              rw [hrq, TensorProduct.tmul_zero]
    · simp
    · intro b c hb hc hpb hpc
      simpa [add_smul, hpb, hpc]
    · intro c b hb hpb
      have hpb' :
          ((b • s) ⊗ₜ[R] q :
            S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) = 0 := by
        simpa [TensorProduct.smul_tmul'] using hpb
      have hc :
          c • ((b • s) ⊗ₜ[R] q :
            S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) = 0 := by
        rw [hpb', smul_zero]
      simpa [TensorProduct.smul_tmul', mul_smul] using hc
  · intro y z hy hz
    rw [smul_add, hy, hz, add_zero]

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the source ideal already annihilates the scalar extension of
the degree-zero source quotient, so this tensor product inherits the source quotient-ring action.
-/
private theorem tensorQuotientOfListMapEquiv_source_isTorsionBySet
    (rs : List R) :
    Module.IsTorsionBySet R
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))))
      (Ideal.ofList rs) := by
  -- It is enough to check simple tensors and use that `Ideal.ofList rs` already kills the source
  -- quotient.
  intro x a
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · rw [smul_zero]
  · intro s q
    have haq : (a : R) ∈ Ideal.ofList rs := a.property
    have hq : (a : R) • q = 0 := by
      refine Quotient.inductionOn' q ?_
      intro m
      exact (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.smul_mem_smul haq (by simp : m ∈ (⊤ : Submodule R M)))
    calc
      ((a : R) •
          (s ⊗ₜ[R] q :
            S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))))) =
        s ⊗ₜ[R] ((a : R) • q) := by
          rw [TensorProduct.tmul_smul]
      _ = 0 := by
          rw [hq, TensorProduct.tmul_zero]
  · intro y z hy hz
    rw [smul_add, hy, hz, add_zero]

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the scalar-extended degree-zero source quotient carries the
natural `R ⧸ Ideal.ofList rs`-module structure induced from the source quotient. -/
noncomputable local instance sourceQuotientTensorModule
    (rs : List R) :
    Module (R ⧸ Ideal.ofList rs)
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
  Module.IsTorsionBySet.module
    (tensorQuotientOfListMapEquiv_source_isTorsionBySet
      (R := R) (M := M) (S := S) rs)

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the scalar-extended degree-zero source quotient also carries
the mapped quotient-ring action used on the target side. -/
noncomputable local instance targetQuotientTensorModule
    (rs : List R) :
    Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
  Module.IsTorsionBySet.module
    (tensorQuotientOfListMapEquiv_target_isTorsionBySet
      (R := R) (M := M) (S := S) rs)

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: on the source quotient module, quotient-ring scalars can be
shifted across the tensor product balancing relation. -/
local instance sourceQuotientCompatibleSmul
    (rs : List R) :
    TensorProduct.CompatibleSMul R (R ⧸ Ideal.ofList rs)
      (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) := by
  -- The quotient action comes from the surjective algebra map `R → R ⧸ J`, so the tensor-product
  -- compatibility is the standard owner lemma specialized to the source quotient module.
  refine TensorProduct.CompatibleSMul.of_algebraMap_surjective
    (M := M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))
    (N := MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ?_
  rw [Ideal.Quotient.algebraMap_eq]
  exact Ideal.Quotient.mk_surjective

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the source quotient-ring action on the scalar-extended
degree-zero source quotient commutes with the ambient `S`-action. -/
local instance sourceQuotientTensorSmulCommClass
    (rs : List R) :
    SMulCommClass (R ⧸ Ideal.ofList rs) S
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) := by
  -- Compare quotient scalars with representatives in `R`, where commutation with the ambient
  -- `S`-action is the usual tensor-product scalar commutativity.
  refine ⟨?_⟩
  intro c s x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← ideal_scalar_action_eq_quotient_scalar_action (I := Ideal.ofList rs) r (s • x)]
  rw [← ideal_scalar_action_eq_quotient_scalar_action (I := Ideal.ofList rs) r x]
  exact smul_comm (r : R) s x

omit [Module.Flat R S] in
/-- Helper for Lemma 10.69.3: `Ideal.qoutMapEquivTensorQout` sends a quotient representative
to the corresponding denominator-one tensor. -/
private theorem qoutMapEquivTensorQout_apply_mk
    (I : Ideal R) (s : S) :
    (Ideal.qoutMapEquivTensorQout (S := S) (I := I))
      (Ideal.Quotient.mk (I.map (algebraMap R S)) s) =
    s ⊗ₜ[R] (1 : R ⧸ I) := by
  -- Evaluate the inverse composite defining the equivalence, where the standard
  -- `tensorQuotEquivQuotSMul` representative formula applies.
  have hsmul :
      I • (⊤ : Submodule R S) =
        Submodule.restrictScalars R (I.map (algebraMap R S) : Ideal S) := by
    simp
  let E : S ⊗[R] (R ⧸ I) ≃ₗ[R] S ⧸ (I.map (algebraMap R S) : Ideal S) :=
    TensorProduct.tensorQuotEquivQuotSMul S I ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hsmul ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv R (I.map (algebraMap R S))
  change E.symm (Ideal.Quotient.mk (I.map (algebraMap R S)) s) =
    s ⊗ₜ[R] (1 : R ⧸ I)
  rw [LinearEquiv.symm_apply_eq]
  have htensor :
      TensorProduct.tensorQuotEquivQuotSMul S I (s ⊗ₜ[R] (1 : R ⧸ I)) =
        Submodule.Quotient.mk s := by
    simpa using TensorProduct.tensorQuotEquivQuotSMul_tmul_mk (M := S) I s (1 : R)
  dsimp [E]
  rw [htensor]
  simp [Submodule.quotEquivOfEq_mk, Submodule.Quotient.restrictScalarsEquiv_mk]

omit [Module.Flat R S] in
/-- Helper for Lemma 10.69.3: the tensor quotient equivalence sends quotient classes of simple
tensors to simple tensors of quotient classes. -/
private theorem tensorQuotMapSMulEquivTensorQuot_apply_mk_tmul
    (I : Ideal R) (s : S) (m : M) :
    TensorProduct.tensorQuotMapSMulEquivTensorQuot (R := R) (S := S) (M := M) I
      (Submodule.Quotient.mk (s ⊗ₜ[R] m)) =
    s ⊗ₜ[R] (Submodule.Quotient.mk m : M ⧸ (I • (⊤ : Submodule R M))) := by
  -- Normalize the scalar quotient representative produced inside the composite equivalence.
  have hsmul_one :
      (s • (1 : S ⧸ I.map (algebraMap R S))) =
        Ideal.Quotient.mk (I.map (algebraMap R S)) s := by
    change Ideal.Quotient.mk (I.map (algebraMap R S)) (s * 1) =
      Ideal.Quotient.mk (I.map (algebraMap R S)) s
    simp
  -- Unfold only this quotient equivalence and then consume the two representative formulas.
  unfold TensorProduct.tensorQuotMapSMulEquivTensorQuot
  simp only [LinearEquiv.trans_apply, TensorProduct.tensorQuotEquivQuotSMul_symm_mk,
    TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    hsmul_one, qoutMapEquivTensorQout_apply_mk,
    TensorProduct.AlgebraTensorModule.assoc_tmul, LinearEquiv.baseChange_tmul]
  have hm :
      (TensorProduct.tensorQuotEquivQuotSMul M I) (m ⊗ₜ[R] (1 : R ⧸ I)) =
        Submodule.Quotient.mk m := by
    simpa using TensorProduct.tensorQuotEquivQuotSMul_tmul_mk (M := M) I m (1 : R)
  rw [hm]

omit [Module.Flat R S] in
/-- Helper for Lemma 10.69.3: the degree-zero quotient after tensor base change is canonically the
tensor product of the source degree-zero quotient. -/
private noncomputable def tensorQuotientOfListMapEquiv
    (rs : List R) :
    ((S ⊗[R] M) ⧸
      (Ideal.ofList (rs.map (algebraMap R S)) •
        (⊤ : Submodule S (S ⊗[R] M)))) ≃ₗ[S]
      S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) :=
  (Submodule.quotEquivOfEq _ _
    (ofList_map_smul_top_eq_idealMap_ofList_smul_top
      (R := R) (M := M) (S := S) rs)).trans
      (TensorProduct.tensorQuotMapSMulEquivTensorQuot
        (R := R) (S := S) (M := M) (Ideal.ofList rs))

omit [Module.Flat R S] in
/-- Helper for Lemma 10.69.3: the list-specialized quotient base-change equivalence has the
expected representative formula on simple tensors. -/
private theorem tensorQuotientOfListMapEquiv_apply_mk_tmul
    (rs : List R) (s : S) (m : M) :
    tensorQuotientOfListMapEquiv (R := R) (M := M) (S := S) rs
      (Submodule.Quotient.mk (s ⊗ₜ[R] m)) =
    s ⊗ₜ[R]
      (Submodule.Quotient.mk m :
        M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) := by
  -- First replace the list-generated target ideal by the mapped source ideal, then apply the
  -- canonical tensor quotient computation.
  unfold tensorQuotientOfListMapEquiv
  rw [LinearEquiv.trans_apply]
  rw [Submodule.quotEquivOfEq_mk]
  exact tensorQuotMapSMulEquivTensorQuot_apply_mk_tmul
    (R := R) (M := M) (S := S) (Ideal.ofList rs) s m

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the inverse quotient base-change equivalence sends a simple
tensor of a quotient representative to the quotient representative of the corresponding tensor.
-/
private theorem tensorQuotientOfListMapEquiv_symm_apply_tmul_mk
    (rs : List R) (s : S) (m : M) :
    (tensorQuotientOfListMapEquiv (R := R) (M := M) (S := S) rs).symm
      (s ⊗ₜ[R]
        (Submodule.Quotient.mk m :
          M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) =
    Submodule.Quotient.mk (s ⊗ₜ[R] m) := by
  -- Apply the forward equivalence and use its representative formula; this avoids unfolding the
  -- quotient comparison a second time.
  apply (tensorQuotientOfListMapEquiv (R := R) (M := M) (S := S) rs).injective
  rw [LinearEquiv.apply_symm_apply]
  rw [tensorQuotientOfListMapEquiv_apply_mk_tmul]

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the degree-zero quotient map induced by denominator-one
tensors is the canonical base-change map for the quotient by `Ideal.ofList rs • ⊤`. -/
private noncomputable def tensorQuotientOfListMap
    (rs : List R) :
    (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) →ₗ[R]
      ((S ⊗[R] M) ⧸
        (Ideal.ofList (rs.map (algebraMap R S)) •
          (⊤ : Submodule S (S ⊗[R] M)))) :=
  ((tensorQuotientOfListMapEquiv (R := R) (M := M) (S := S) rs).symm.restrictScalars R).comp
    (TensorProduct.mk R S (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) 1)

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the denominator-one quotient base-change map sends
representatives to representatives. -/
private theorem tensorQuotientOfListMap_apply_mk
    (rs : List R) (m : M) :
    tensorQuotientOfListMap (R := R) (M := M) (S := S) rs (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (1 ⊗ₜ[R] m) := by
  -- The map is defined through the inverse quotient equivalence, so its representative formula is
  -- exactly the inverse-equivalence computation already isolated above.
  simp [tensorQuotientOfListMap, tensorQuotientOfListMapEquiv_symm_apply_tmul_mk]

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the degree-zero quotient is an `S`-base change of the source
degree-zero quotient. -/
private theorem tensorQuotientOfListMap_isBaseChange
    (rs : List R) :
    IsBaseChange S (tensorQuotientOfListMap (R := R) (M := M) (S := S) rs) := by
  -- Package the quotient equivalence as the owner-level base-change API for this quotient
  -- component.
  refine IsBaseChange.of_equiv
    (S := S)
    (f := tensorQuotientOfListMap (R := R) (M := M) (S := S) rs)
    (tensorQuotientOfListMapEquiv (R := R) (M := M) (S := S) rs).symm ?_
  intro x
  rfl

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the ideal generated by `rs` maps into the comap of the
ideal generated by the mapped sequence. -/
private theorem ofList_le_comap_ofList_map
    (rs : List R) :
    Ideal.ofList rs ≤
      (Ideal.ofList (rs.map (algebraMap R S))).comap (algebraMap R S) := by
  -- Rewrite the mapped-list ideal as the image ideal and use the canonical image membership.
  intro x hx
  change algebraMap R S x ∈ Ideal.ofList (rs.map (algebraMap R S))
  have hmap :
      Ideal.map (algebraMap R S) (Ideal.ofList rs) =
        Ideal.ofList (rs.map (algebraMap R S)) := by
    simpa using Ideal.map_ofList (f := algebraMap R S) rs
  rw [← hmap]
  exact Ideal.mem_map_of_mem (algebraMap R S) hx

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the mapped quotient ring is an algebra over the source
quotient ring. -/
noncomputable local instance quotientAlgebraOfListMap
    (rs : List R) :
    Algebra (R ⧸ Ideal.ofList rs)
      (S ⧸ Ideal.ofList (rs.map (algebraMap R S))) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (A := S) (p := Ideal.ofList rs)
    (P := Ideal.ofList (rs.map (algebraMap R S)))
    (ofList_le_comap_ofList_map (R := R) (S := S) rs)

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: polynomial base change followed by the length-cast variable
rename sends monomial simple tensors to the corresponding mapped monomial. -/
private theorem mvPolynomialQuotientBaseChange_monomial
    (rs : List R)
    (c : S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
    (d : Fin rs.length →₀ ℕ) :
    (MvPolynomial.renameEquiv
      (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (finCongr (List.length_map (as := rs) (algebraMap R S)).symm))
      ((MvPolynomial.algebraTensorAlgEquiv
          (R ⧸ Ideal.ofList rs)
          (S ⧸ Ideal.ofList (rs.map (algebraMap R S))))
        (c ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))) =
    MvPolynomial.monomial
      (d.mapDomain (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm)) c := by
  -- Compute the scalar-extension half on monomials, normalize the scalar coefficient, and then
  -- apply the variable rename computation.
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul]
  rw [MvPolynomial.map_monomial]
  rw [MvPolynomial.smul_monomial]
  change
    (MvPolynomial.renameEquiv
      (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (finCongr (List.length_map (as := rs) (algebraMap R S)).symm))
      (MvPolynomial.monomial d
        (c * algebraMap (R ⧸ Ideal.ofList rs)
          (S ⧸ Ideal.ofList (rs.map (algebraMap R S))) 1)) =
    MvPolynomial.monomial
      (d.mapDomain (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm)) c
  simp only [map_one, mul_one]
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_monomial]
  rfl

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: polynomial base change over the quotient ring, followed by
the canonical variable-length rename, as a single algebra equivalence. -/
private noncomputable def mvPolynomialQuotientBaseChangeAlgEquiv
    (rs : List R) :
    ((S ⧸ Ideal.ofList (rs.map (algebraMap R S))) ⊗[R ⧸ Ideal.ofList rs]
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₐ[
      S ⧸ Ideal.ofList (rs.map (algebraMap R S))]
        MvPolynomial (Fin (rs.map (algebraMap R S)).length)
          (S ⧸ Ideal.ofList (rs.map (algebraMap R S))) :=
  (MvPolynomial.algebraTensorAlgEquiv
    (R ⧸ Ideal.ofList rs)
    (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))).trans
      (MvPolynomial.renameEquiv
        (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
        (finCongr (List.length_map (as := rs) (algebraMap R S)).symm))

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the quotient-ring polynomial base-change equivalence sends
monomial simple tensors to the corresponding mapped monomial. -/
private theorem mvPolynomialQuotientBaseChangeAlgEquiv_tmul_monomial
    (rs : List R)
    (c : S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
    (d : Fin rs.length →₀ ℕ) :
    mvPolynomialQuotientBaseChangeAlgEquiv (R := R) (S := S) rs
      (c ⊗ₜ[R ⧸ Ideal.ofList rs]
        MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs)) =
    MvPolynomial.monomial
      (d.mapDomain (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm)) c := by
  -- Consume the expanded computation through the packaged equivalence so later transport proofs
  -- can rewrite one stable normal form instead of unfolding the two-stage construction.
  simpa [mvPolynomialQuotientBaseChangeAlgEquiv] using
    mvPolynomialQuotientBaseChange_monomial (R := R) (S := S) rs c d

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the inverse quotient-ring polynomial base-change
equivalence sends mapped monomials back to denominator-one monomial tensors. -/
private theorem mvPolynomialQuotientBaseChangeAlgEquiv_symm_monomial
    (rs : List R)
    (c : S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
    (d : Fin rs.length →₀ ℕ) :
    (mvPolynomialQuotientBaseChangeAlgEquiv (R := R) (S := S) rs).symm
      (MvPolynomial.monomial
        (d.mapDomain (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm)) c) =
    c ⊗ₜ[R ⧸ Ideal.ofList rs]
      MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs) := by
  -- Prove the inverse formula by applying the forward equivalence and using the packaged
  -- monomial computation; this keeps the inverse normal form proof independent of internals.
  apply (mvPolynomialQuotientBaseChangeAlgEquiv (R := R) (S := S) rs).injective
  rw [AlgEquiv.apply_symm_apply]
  rw [mvPolynomialQuotientBaseChangeAlgEquiv_tmul_monomial]

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the polynomial base-change equivalence is induced by the
denominator-one tensor map on quotient-coefficient polynomials. -/
private noncomputable def mvPolynomialQuotientBaseChangeLinearMap
    (rs : List R) :
    MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs) →ₗ[R ⧸ Ideal.ofList rs]
      MvPolynomial (Fin (rs.map (algebraMap R S)).length)
        (S ⧸ Ideal.ofList (rs.map (algebraMap R S))) :=
  (((mvPolynomialQuotientBaseChangeAlgEquiv (R := R) (S := S) rs).toLinearMap).restrictScalars
    (R ⧸ Ideal.ofList rs)).comp
      (TensorProduct.mk (R ⧸ Ideal.ofList rs)
        (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
        (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) 1)

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the target quotient-coefficient polynomial ring is the
base change of the source quotient-coefficient polynomial ring. -/
private theorem mvPolynomialQuotientBaseChange_isBaseChange
    (rs : List R) :
    IsBaseChange (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (mvPolynomialQuotientBaseChangeLinearMap (R := R) (S := S) rs) := by
  -- Package the explicit polynomial base-change equivalence as the owner-level base-change API
  -- so tensoring it with the degree-zero quotient can use `IsBaseChange.tensorEquiv`.
  refine IsBaseChange.of_equiv
    (S := S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
    (f := mvPolynomialQuotientBaseChangeLinearMap (R := R) (S := S) rs)
    ((mvPolynomialQuotientBaseChangeAlgEquiv (R := R) (S := S) rs).toLinearEquiv) ?_
  intro p
  rfl

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the degree-zero quotient base-change equivalence is linear
over the mapped quotient ring `S ⧸ Ideal.ofList (rs.map (algebraMap R S))`. -/
private noncomputable def tensorQuotientOfListMapQuotientLinearEquiv
    (rs : List R) :
    letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
        (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
      Module.IsTorsionBySet.module
        (tensorQuotientOfListMapEquiv_target_isTorsionBySet
          (R := R) (M := M) (S := S) rs)
    ((S ⊗[R] M) ⧸
      (Ideal.ofList (rs.map (algebraMap R S)) •
        (⊤ : Submodule S (S ⊗[R] M)))) ≃ₗ[
          S ⧸ Ideal.ofList (rs.map (algebraMap R S))]
      S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) :=
  letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
    Module.IsTorsionBySet.module
      (tensorQuotientOfListMapEquiv_target_isTorsionBySet
        (R := R) (M := M) (S := S) rs)
  -- Promote the quotient comparison without changing its underlying function.
  linearEquiv_over_quotient
    (I := Ideal.ofList (rs.map (algebraMap R S)))
    (tensorQuotientOfListMapEquiv (R := R) (M := M) (S := S) rs)

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the quotient-ring-linear base-change equivalence has the
same representative formula as the underlying `S`-linear equivalence. -/
private theorem tensorQuotientOfListMapQuotientLinearEquiv_apply_mk_tmul
    (rs : List R) (s : S) (m : M) :
    letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
        (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
      Module.IsTorsionBySet.module
        (tensorQuotientOfListMapEquiv_target_isTorsionBySet
          (R := R) (M := M) (S := S) rs)
    tensorQuotientOfListMapQuotientLinearEquiv (R := R) (M := M) (S := S) rs
      (Submodule.Quotient.mk (s ⊗ₜ[R] m)) =
    s ⊗ₜ[R]
      (Submodule.Quotient.mk m :
        M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) := by
  -- The promoted equivalence is definitionally the same function as the `S`-linear quotient
  -- comparison, so the earlier representative computation applies directly.
  exact tensorQuotientOfListMapEquiv_apply_mk_tmul
    (R := R) (M := M) (S := S) rs s m

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: forgetting the quotient-ring balancing on the source
textbook tensor module commutes with scalar extension to `S`. -/
private noncomputable def tensorBaseChangeSourceForgetQuotientLinearEquiv
    (rs : List R) :
    S ⊗[R]
        ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
          MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[S]
      S ⊗[R]
        ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R]
          MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :=
  let _ : TensorProduct.CompatibleSMul R (R ⧸ Ideal.ofList rs)
      (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :=
    sourceQuotientCompatibleSmul (R := R) (M := M) rs
  -- First forget the quotient balancing on the inner tensor, then scalar-extend that fixed
  -- comparison to the outer `S`-tensor factor.
  (TensorProduct.equivOfCompatibleSMul
      R
      (R ⧸ Ideal.ofList rs)
      R
      (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))).baseChange R S

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: after reassociating the plain `R`-tensor product, the
quotient-ring balancing can be restored on the scalar-extended degree-zero quotient. -/
private noncomputable def tensorBaseChangeTargetRestoreQuotientLinearEquiv
    (rs : List R) :
    ((S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) ⊗[R]
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[S]
      ((S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) ⊗[
          R ⧸ Ideal.ofList rs]
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :=
  let _ : TensorProduct.CompatibleSMul R (R ⧸ Ideal.ofList rs)
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))))
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (M := S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))))
      (N := MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (by
        rw [Ideal.Quotient.algebraMap_eq]
        exact Ideal.Quotient.mk_surjective)
  -- After reassociating, restore the quotient balancing on the scalar-extended degree-zero
  -- quotient by reversing the standard compatible-scalar comparison.
  (TensorProduct.equivOfCompatibleSMul
      R
      (R ⧸ Ideal.ofList rs)
      S
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))))
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))).symm

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: once the degree-zero quotient has been scalar-extended, the
polynomial factor can be transported from `R ⧸ Ideal.ofList rs` to the mapped quotient ring. -/
private noncomputable def tensorBaseChangePolynomialFactorLinearEquiv
    (rs : List R) :
    ((S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) ⊗[
        R ⧸ Ideal.ofList rs]
      MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[S]
      ((S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) ⊗[
          S ⧸ Ideal.ofList (rs.map (algebraMap R S))]
        MvPolynomial (Fin (rs.map (algebraMap R S)).length)
          (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))) :=
  let _ : Module (R ⧸ Ideal.ofList rs)
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
    sourceQuotientTensorModule (R := R) (M := M) (S := S) rs
  let _ : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
    targetQuotientTensorModule (R := R) (M := M) (S := S) rs
  let _ : Algebra (R ⧸ Ideal.ofList rs)
      (S ⧸ Ideal.ofList (rs.map (algebraMap R S))) :=
    quotientAlgebraOfListMap (R := R) (S := S) rs
  let _ : IsScalarTower
      (R ⧸ Ideal.ofList rs)
      (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
    IsScalarTower.of_algebraMap_smul fun c x ↦ by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      change
        (((Ideal.Quotient.mk (Ideal.ofList (rs.map (algebraMap R S)))) (algebraMap R S r) :
            S ⧸ Ideal.ofList (rs.map (algebraMap R S))) • x =
          ((Ideal.Quotient.mk (Ideal.ofList rs)) r : R ⧸ Ideal.ofList rs) • x)
      rw [← ideal_scalar_action_eq_quotient_scalar_action
        (I := Ideal.ofList (rs.map (algebraMap R S)))
        (algebraMap R S r) x]
      rw [IsScalarTower.algebraMap_smul (R := R) (A := S) r x]
      rw [ideal_scalar_action_eq_quotient_scalar_action (I := Ideal.ofList rs) r x]
  -- Package the polynomial-factor base change as a tensor equivalence, then restrict scalars
  -- back from the mapped quotient ring to `S`.
  ((mvPolynomialQuotientBaseChange_isBaseChange (R := R) (S := S) rs).tensorEquiv
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))))).symm.restrictScalars S

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: after both factors are transported, replace the scalar-
extended source degree-zero quotient by the mapped target quotient. -/
private noncomputable def tensorBaseChangeTargetQuotientLinearEquiv
    (rs : List R) :
    ((S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) ⊗[
        S ⧸ Ideal.ofList (rs.map (algebraMap R S))]
      MvPolynomial (Fin (rs.map (algebraMap R S)).length)
        (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))) ≃ₗ[S]
      (((S ⊗[R] M) ⧸
          (Ideal.ofList (rs.map (algebraMap R S)) •
            (⊤ : Submodule S (S ⊗[R] M)))) ⊗[
            S ⧸ Ideal.ofList (rs.map (algebraMap R S))]
        MvPolynomial (Fin (rs.map (algebraMap R S)).length)
          (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))) :=
  -- Tensor the quotient comparison with the identity on the polynomial factor, then view the
  -- resulting quotient-ring-linear equivalence as `S`-linear by restriction of scalars.
  (TensorProduct.congr
      (tensorQuotientOfListMapQuotientLinearEquiv (R := R) (M := M) (S := S) rs).symm
      (LinearEquiv.refl
        (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
        (MvPolynomial (Fin (rs.map (algebraMap R S)).length)
          (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))))).restrictScalars S

/-- Helper for Lemma 10.69.3: the forward map from a source graded piece to the target graded
piece is obtained by tensoring with the denominator-one scalar and applying the graded-piece
base-change equivalence. -/
private noncomputable def tensorBaseChangeGradedPieceMap
    (rs : List R) (n : ℕ) :
    idealAssociatedGradedPiece (Ideal.ofList rs) M n →ₗ[R]
      idealAssociatedGradedPiece
        (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n :=
  ((tensorBaseChangeGradedPiece_linearEquiv (R := R) (M := M) (S := S) rs n).toLinearMap.restrictScalars
      R).comp
    (TensorProduct.mk R S (idealAssociatedGradedPiece (Ideal.ofList rs) M n) 1)

/-- Helper for Lemma 10.69.3: each graded piece of the target associated graded module is the
base change of the corresponding source graded piece. -/
private theorem tensorBaseChangeGradedPiece_isBaseChange
    (rs : List R) (n : ℕ) :
    IsBaseChange S (tensorBaseChangeGradedPieceMap (R := R) (M := M) (S := S) rs n) := by
  -- Package the already proved graded-piece tensor equivalence as owner-level base-change API.
  refine IsBaseChange.of_equiv
    (S := S)
    (f := tensorBaseChangeGradedPieceMap (R := R) (M := M) (S := S) rs n)
    (tensorBaseChangeGradedPiece_linearEquiv (R := R) (M := M) (S := S) rs n) ?_
  intro z
  rfl

/-- Helper for Lemma 10.69.3: the forward map from the source associated graded module to the
target associated graded module is assembled degreewise from the graded-piece base-change maps. -/
private noncomputable def tensorBaseChangeGradedModuleMap
    (rs : List R) :
    idealAssociatedGradedModule (Ideal.ofList rs) M →ₗ[R]
      idealAssociatedGradedModule
        (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) :=
  DirectSum.lmap fun n ↦
    tensorBaseChangeGradedPieceMap (R := R) (M := M) (S := S) rs n

/-- Helper for Lemma 10.69.3: the target associated graded module is the direct-sum base change of
the source associated graded module. -/
private theorem tensorBaseChangeGradedModule_isBaseChange
    (rs : List R) :
    IsBaseChange S (tensorBaseChangeGradedModuleMap (R := R) (M := M) (S := S) rs) := by
  -- Use the owner theorem for direct sums, avoiding a hand-built inverse through
  -- `DirectSum.congrLinearEquiv`.
  exact IsBaseChange.directSum fun n ↦
    tensorBaseChangeGradedPiece_isBaseChange (R := R) (M := M) (S := S) rs n

/-- Helper for Lemma 10.69.3: the direct-sum base-change equivalence evaluates on homogeneous
generators through the degreewise graded-piece equivalence. -/
private theorem tensorBaseChangeGradedModule_isBaseChange_equiv_tmul_lof
    (rs : List R) (n : ℕ) (s : S)
    (z : idealAssociatedGradedPiece (Ideal.ofList rs) M n) :
    (tensorBaseChangeGradedModule_isBaseChange (R := R) (M := M) (S := S) rs).equiv
        (s ⊗ₜ[R]
          DirectSum.lof (R ⧸ Ideal.ofList rs) ℕ
            (idealAssociatedGradedPiece (Ideal.ofList rs) M) n z) =
      DirectSum.lof (S ⧸ Ideal.ofList (rs.map (algebraMap R S))) ℕ
        (idealAssociatedGradedPiece
          (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M)) n
        (tensorBaseChangeGradedPiece_linearEquiv (R := R) (M := M) (S := S) rs n
          (s ⊗ₜ[R] z)) := by
  -- First use the base-change computation rule, then read off the effect of `DirectSum.lmap` on
  -- the chosen homogeneous generator.
  rw [IsBaseChange.equiv_tmul]
  simp only [DirectSum.lof_eq_of, tensorBaseChangeGradedModuleMap, DirectSum.lmap_of,
    tensorBaseChangeGradedPieceMap, LinearMap.comp_apply]
  -- After normalizing `lof` to the additive generator `DirectSum.of`, the target is just
  -- componentwise `S`-linearity of the direct sum and of the degreewise base-change equivalence.
  rw [← DirectSum.of_smul S]
  congr 1
  simpa [TensorProduct.smul_tmul'] using
    ((tensorBaseChangeGradedPiece_linearEquiv (R := R) (M := M) (S := S) rs n).map_smul
      s (1 ⊗ₜ[R] z)).symm

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: transporting a monomial exponent across the canonical
length equality for `rs.map (algebraMap R S)` preserves total degree. -/
private theorem mapped_monomial_degree_cast
    (rs : List R) (d : Fin rs.length →₀ ℕ) :
    (d.mapDomain
      (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm)).degree = d.degree := by
  -- The transport is just a relabeling of finitely supported exponent vectors, so total degree is
  -- unchanged.
  simpa using Finsupp.degree_mapDomain_eq_of_subsingletonAddUnits
    (f := Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm) d

/-- Helper for Chap10 Lemma 10 69 3: the monomial computation for
`quasiRegularSequenceAssociatedGradedMap` can be restated at any explicitly chosen degree equal to
the monomial degree. -/
private theorem quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_of_degree
    {A : Type*} [CommRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    {rs : List A} (m : P) (e : Fin rs.length →₀ ℕ) (n : ℕ) (hdeg : e.degree = n) :
    let J : Ideal A := Ideal.ofList rs
    quasiRegularSequenceAssociatedGradedMap P rs
      (((Submodule.Quotient.mk m : P ⧸ (J • (⊤ : Submodule A P))) ⊗ₜ[A ⧸ J]
        MvPolynomial.monomial e (1 : A ⧸ J))) =
      DirectSum.of (idealAssociatedGradedPiece J P) n
        (Submodule.Quotient.mk
          (⟨(∏ i : Fin rs.length, rs.get i ^ e i) • m,
            ofList_monomial_weight_smul_mem_of_degree rs n m e hdeg⟩ :
            idealAssociatedGradedStage J P n)) := by
  -- Choose the homogeneous degree first, then reuse the existing monomial computation without any
  -- later direct-sum index transport.
  subst n
  simpa [DirectSum.lof_eq_of] using
    quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_lof (P := P) (rs := rs) m e

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the scalar extension of the source textbook module is
identified with the source textbook module for the mapped sequence. -/
private noncomputable def tensorBaseChangeSourceLinearEquiv
    (rs : List R) :
    letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
        (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
      Module.IsTorsionBySet.module
        (tensorQuotientOfListMapEquiv_target_isTorsionBySet
          (R := R) (M := M) (S := S) rs)
    S ⊗[R]
        ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
          MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[S]
      (((S ⊗[R] M) ⧸
          (Ideal.ofList (rs.map (algebraMap R S)) •
            (⊤ : Submodule S (S ⊗[R] M)))) ⊗[
            S ⧸ Ideal.ofList (rs.map (algebraMap R S))]
        MvPolynomial (Fin (rs.map (algebraMap R S)).length)
          (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))) :=
  letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
    Module.IsTorsionBySet.module
      (tensorQuotientOfListMapEquiv_target_isTorsionBySet
        (R := R) (M := M) (S := S) rs)
  -- Route correction: keep the source transport as one named composite so later proofs only
  -- rewrite through this boundary, instead of reopening each tensor-balancing step separately.
  tensorBaseChangeSourceForgetQuotientLinearEquiv (R := R) (M := M) (S := S) rs ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.assoc
      R
      R
      S
      S
      (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))).symm ≪≫ₗ
    tensorBaseChangeTargetRestoreQuotientLinearEquiv (R := R) (M := M) (S := S) rs ≪≫ₗ
    tensorBaseChangePolynomialFactorLinearEquiv (R := R) (M := M) (S := S) rs ≪≫ₗ
    tensorBaseChangeTargetQuotientLinearEquiv (R := R) (M := M) (S := S) rs

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the transport-heavy source half of
`tensorBaseChangeSourceLinearEquiv` sends monomial generators to the plain balanced tensor before
the polynomial-factor base change is applied. -/
private theorem tensorBaseChangeSourceTransport_apply_tmul_monomial
    (rs : List R) (s : S) (m : M) (d : Fin rs.length →₀ ℕ) :
    letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
        (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
      Module.IsTorsionBySet.module
        (tensorQuotientOfListMapEquiv_target_isTorsionBySet
          (R := R) (M := M) (S := S) rs)
    (tensorBaseChangeSourceForgetQuotientLinearEquiv (R := R) (M := M) (S := S) rs ≪≫ₗ
        (TensorProduct.AlgebraTensorModule.assoc
          R
          R
          S
          S
          (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))
          (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))).symm ≪≫ₗ
        tensorBaseChangeTargetRestoreQuotientLinearEquiv (R := R) (M := M) (S := S) rs)
      (s ⊗ₜ[R]
        ((Submodule.Quotient.mk m :
            M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))) =
      ((s ⊗ₜ[R]
          (Submodule.Quotient.mk m :
            M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) ⊗ₜ[R ⧸ Ideal.ofList rs]
        MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs)) := by
  letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
    Module.IsTorsionBySet.module
      (tensorQuotientOfListMapEquiv_target_isTorsionBySet
        (R := R) (M := M) (S := S) rs)
  -- Unfold the three source transport legs separately; each leg has a direct simple-tensor
  -- computation rule, so the composite collapses before the later polynomial bridge appears.
  simp [tensorBaseChangeSourceForgetQuotientLinearEquiv,
    tensorBaseChangeTargetRestoreQuotientLinearEquiv, LinearEquiv.trans_apply,
    TensorProduct.equivOfCompatibleSMul, LinearEquiv.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.assoc_symm_tmul]

/-- Helper for Chap10 Lemma 10 69 3: on the associated graded module, the restricted `R`-action
agrees with scalar multiplication by the corresponding constant polynomial. -/
private theorem quasiRegularAssociatedGradedInternal_quotientScalar_smul
    (rs : List R) (r : R)
    (x : quasiRegularAssociatedGradedInternal rs M) :
    r • x =
      ((Ideal.Quotient.mk (Ideal.ofList rs)) r : R ⧸ Ideal.ofList rs) • x := by
  -- Check the scalar comparison on generators of the internal direct-sum model, then extend
  -- additively to arbitrary elements.
  refine DirectSum.induction_on x ?_ ?_ ?_
  · simp
  · intro n z
    refine Quotient.inductionOn' z ?_
    intro t
    calc
      r • DirectSum.of (quasiRegularAssociatedGradedInternalPiece rs M) n
          (Submodule.Quotient.mk t :
            idealAssociatedGradedStage (Ideal.ofList rs) M n ⧸
              (Ideal.ofList rs •
                (⊤ : Submodule R (idealAssociatedGradedStage (Ideal.ofList rs) M n)))) =
        DirectSum.of (quasiRegularAssociatedGradedInternalPiece rs M) n
          (r • (Submodule.Quotient.mk t :
            idealAssociatedGradedStage (Ideal.ofList rs) M n ⧸
              (Ideal.ofList rs •
                (⊤ : Submodule R (idealAssociatedGradedStage (Ideal.ofList rs) M n))))) := by
          exact (DirectSum.of_smul
            (M := quasiRegularAssociatedGradedInternalPiece rs M)
            (i := n) (c := r)
            (x := (Submodule.Quotient.mk t :
              idealAssociatedGradedStage (Ideal.ofList rs) M n ⧸
                (Ideal.ofList rs •
                  (⊤ : Submodule R (idealAssociatedGradedStage (Ideal.ofList rs) M n)))))).symm
      _ =
        DirectSum.of (quasiRegularAssociatedGradedInternalPiece rs M) n
          (((Ideal.Quotient.mk (Ideal.ofList rs)) r : R ⧸ Ideal.ofList rs) •
            (Submodule.Quotient.mk t :
              idealAssociatedGradedStage (Ideal.ofList rs) M n ⧸
                (Ideal.ofList rs •
                  (⊤ : Submodule R (idealAssociatedGradedStage (Ideal.ofList rs) M n))))) := by
          exact congrArg
            (DirectSum.of (quasiRegularAssociatedGradedInternalPiece rs M) n)
            (quotient_smul_eq_quotient_mk
              (M := idealAssociatedGradedStage (Ideal.ofList rs) M n)
              (I := Ideal.ofList rs) r
              (Submodule.Quotient.mk t :
                idealAssociatedGradedStage (Ideal.ofList rs) M n ⧸
                  (Ideal.ofList rs •
                    (⊤ : Submodule R (idealAssociatedGradedStage (Ideal.ofList rs) M n)))))
      _ =
        ((Ideal.Quotient.mk (Ideal.ofList rs)) r : R ⧸ Ideal.ofList rs) •
          DirectSum.of (quasiRegularAssociatedGradedInternalPiece rs M) n
            (Submodule.Quotient.mk t :
              idealAssociatedGradedStage (Ideal.ofList rs) M n ⧸
                (Ideal.ofList rs •
                  (⊤ : Submodule R (idealAssociatedGradedStage (Ideal.ofList rs) M n)))) := by
          exact DirectSum.of_smul
            (M := quasiRegularAssociatedGradedInternalPiece rs M)
            (i := n)
            (c := ((Ideal.Quotient.mk (Ideal.ofList rs)) r : R ⧸ Ideal.ofList rs))
            (x := (Submodule.Quotient.mk t :
              idealAssociatedGradedStage (Ideal.ofList rs) M n ⧸
                (Ideal.ofList rs •
                  (⊤ : Submodule R (idealAssociatedGradedStage (Ideal.ofList rs) M n)))))
  · intro x y hx hy
    simp [smul_add, hx, hy]

/-- Helper for Chap10 Lemma 10 69 3: on the internal associated graded model, the restricted
`R`-action agrees with scalar multiplication by the corresponding constant polynomial. -/
private theorem quasiRegularAssociatedGradedInternal_constantPolynomial_smul
    (rs : List R) (r : R)
    (x : quasiRegularAssociatedGradedInternal rs M) :
    r • x =
      (algebraMap R
        (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) r) • x := by
  let J : Ideal R := Ideal.ofList rs
  letI :
      IsScalarTower (R ⧸ J)
        (MvPolynomial (Fin rs.length) (R ⧸ J))
        (quasiRegularAssociatedGradedInternal rs M) :=
    quasiRegularAssociatedGradedInternal_isScalarTower (M := M) rs
  -- First rewrite the restricted action through the quotient ring, then through the polynomial
  -- algebra structure on the internal associated graded model.
  calc
    r • x = ((Ideal.Quotient.mk J) r : R ⧸ J) • x := by
      simpa [J] using
        quasiRegularAssociatedGradedInternal_quotientScalar_smul (M := M) rs r x
    _ =
        (algebraMap (R ⧸ J)
          (MvPolynomial (Fin rs.length) (R ⧸ J))
          ((Ideal.Quotient.mk J) r)) • x := by
        rw [IsScalarTower.algebraMap_smul]
    _ = (algebraMap R (MvPolynomial (Fin rs.length) (R ⧸ J)) r) • x := by
        rfl

/-- Helper for Chap10 Lemma 10 69 3: on the associated graded module, the restricted `R`-action
agrees with scalar multiplication by the corresponding constant polynomial. -/
private theorem idealAssociatedGradedScalarAlgebraMap_smul
    (rs : List R) (r : R)
    (y : idealAssociatedGradedModule (Ideal.ofList rs) M) :
    r • y =
      (algebraMap R (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) r) • y := by
  let J : Ideal R := Ideal.ofList rs
  let eR :
      idealAssociatedGradedModule J M ≃ₗ[R]
        quasiRegularAssociatedGradedInternal rs M :=
    DirectSum.congrLinearEquiv fun n ↦
      (quasiRegularAssociatedGradedInternalPieceEquiv rs M n).symm
  let ePoly :=
    (quasiRegularAssociatedGradedAddEquiv rs M).linearEquiv
      (MvPolynomial (Fin rs.length) (R ⧸ J))
  -- Compare both actions after transporting the associated graded module to the internal direct-sum
  -- model, where the constant-polynomial action is already packaged by the owner API.
  apply eR.injective
  calc
    eR (r • y) = r • eR y := by
      exact eR.map_smul r y
    _ = (algebraMap R (MvPolynomial (Fin rs.length) (R ⧸ J)) r) • eR y := by
      exact quasiRegularAssociatedGradedInternal_constantPolynomial_smul
        (M := M) rs r (eR y)
    _ = ePoly ((algebraMap R (MvPolynomial (Fin rs.length) (R ⧸ J)) r) • y) := by
      exact (ePoly.map_smul (algebraMap R (MvPolynomial (Fin rs.length) (R ⧸ J)) r) y).symm
    _ = eR ((algebraMap R (MvPolynomial (Fin rs.length) (R ⧸ J)) r) • y) := by
      rfl

omit [Module.Flat R S] in
/-- Helper for Chap10 Lemma 10 69 3: the full source-side base-change equivalence sends monomial
generators to the corresponding mapped monomial generators. -/
private theorem tensorBaseChangeSourceLinearEquiv_apply_tmul_monomial
    (rs : List R) (s : S) (m : M) (d : Fin rs.length →₀ ℕ) :
    letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
        (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
      Module.IsTorsionBySet.module
        (tensorQuotientOfListMapEquiv_target_isTorsionBySet
          (R := R) (M := M) (S := S) rs)
    tensorBaseChangeSourceLinearEquiv (R := R) (M := M) (S := S) rs
      (s ⊗ₜ[R]
        ((Submodule.Quotient.mk m :
            M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))) =
    (Submodule.Quotient.mk (s ⊗ₜ[R] m) :
        ((S ⊗[R] M) ⧸
          (Ideal.ofList (rs.map (algebraMap R S)) •
            (⊤ : Submodule S (S ⊗[R] M))))) ⊗ₜ[
          S ⧸ Ideal.ofList (rs.map (algebraMap R S))]
      MvPolynomial.monomial
        (d.mapDomain (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm))
        (1 : S ⧸ Ideal.ofList (rs.map (algebraMap R S))) := by
  letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
    Module.IsTorsionBySet.module
      (tensorQuotientOfListMapEquiv_target_isTorsionBySet
        (R := R) (M := M) (S := S) rs)
  have hquot :
      (tensorQuotientOfListMapQuotientLinearEquiv (R := R) (M := M) (S := S) rs).symm
        (s ⊗ₜ[R]
          (Submodule.Quotient.mk m :
            M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) =
      (Submodule.Quotient.mk (s ⊗ₜ[R] m) :
        ((S ⊗[R] M) ⧸
          (Ideal.ofList (rs.map (algebraMap R S)) •
            (⊤ : Submodule S (S ⊗[R] M))))) := by
    -- Move through the quotient comparison once, using the already isolated forward
    -- representative formula.
    apply (tensorQuotientOfListMapQuotientLinearEquiv
      (R := R) (M := M) (S := S) rs).injective
    rw [LinearEquiv.apply_symm_apply]
    rw [tensorQuotientOfListMapQuotientLinearEquiv_apply_mk_tmul]
  have hpoly :
      tensorBaseChangePolynomialFactorLinearEquiv (R := R) (M := M) (S := S) rs
        (((s ⊗ₜ[R]
            (Submodule.Quotient.mk m :
              M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) ⊗ₜ[R ⧸ Ideal.ofList rs]
          MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))) =
      ((s ⊗ₜ[R]
          (Submodule.Quotient.mk m :
            M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) ⊗ₜ[
            S ⧸ Ideal.ofList (rs.map (algebraMap R S))]
        MvPolynomial.monomial
          (d.mapDomain (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm))
          (1 : S ⧸ Ideal.ofList (rs.map (algebraMap R S)))) := by
    -- The polynomial-factor base change is exactly the scalar extension of the quotient-ring
    -- polynomial equivalence, so the simple-tensor formula is just the packaged monomial
    -- computation after unfolding the base-change comparison once.
    simp [tensorBaseChangePolynomialFactorLinearEquiv, IsBaseChange.tensorEquiv,
      mvPolynomialQuotientBaseChangeLinearMap,
      mvPolynomialQuotientBaseChangeAlgEquiv_tmul_monomial]
  -- Cross the source transport boundary first, then use the packaged polynomial and quotient
  -- computation lemmas for the remaining two legs of the source equivalence.
  unfold tensorBaseChangeSourceLinearEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  rw [tensorBaseChangeSourceTransport_apply_tmul_monomial (R := R) (M := M) (S := S) rs s m d]
  rw [hpoly]
  have htarget :=
    congrArg
      (tensorBaseChangeTargetQuotientLinearEquiv (R := R) (M := M) (S := S) rs)
      hpoly
  simpa [tensorBaseChangeTargetQuotientLinearEquiv, hquot] using htarget

/-- Helper for Chap10 Lemma 10 69 3: the source quasi-regularity equivalence may be restricted
from polynomial-linearity to `R`-linearity because the source `R`-action is induced by constant
polynomials. -/
private instance sourceQuasiRegularLinearCompatibleSmul
    {rs : List R} :
    LinearMap.CompatibleSMul
      ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
        MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))
      (idealAssociatedGradedModule (Ideal.ofList rs) M)
      R
      (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) := by
  refine LinearMap.CompatibleSMul.mk ?_
  intro f r x
  -- Spell the restricted `R`-action through constant polynomials once; afterwards the original
  -- polynomial-linearity of `f` closes the goal directly.
  rw [sourceScalarAlgebraMap_smul (M := M) rs r x]
  rw [idealAssociatedGradedScalarAlgebraMap_smul (M := M) rs r (f x)]
  simpa [Algebra.smul_def] using
    f.map_smul (algebraMap R (MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) r) x

/-- Helper for Chap10 Lemma 10 69 3: on monomial generators, the target associated-graded map is
the conjugate of the scalar extension of the source quasi-regularity equivalence. -/
private theorem tensorBaseChangeAssociatedGradedMapNaturality_tmul
    {rs : List R} (hqr : IsQuasiRegular M rs)
    (s : S) (m : M) (d : Fin rs.length →₀ ℕ) :
    letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
        (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
      Module.IsTorsionBySet.module
        (tensorQuotientOfListMapEquiv_target_isTorsionBySet
          (R := R) (M := M) (S := S) rs)
    let eMid :=
      (((hqr.linearEquiv).restrictScalars R).baseChange R S :
        S ⊗[R]
            ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
              MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[S]
          S ⊗[R] idealAssociatedGradedModule (Ideal.ofList rs) M)
    (tensorBaseChangeGradedModule_isBaseChange (R := R) (M := M) (S := S) rs).equiv
        (eMid
          (s ⊗ₜ[R]
            ((Submodule.Quotient.mk m :
                M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
              MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs)))) =
      quasiRegularSequenceAssociatedGradedMap
          (S ⊗[R] M) (rs.map (algebraMap R S))
        (tensorBaseChangeSourceLinearEquiv (R := R) (M := M) (S := S) rs
          (s ⊗ₜ[R]
            ((Submodule.Quotient.mk m :
                M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
              MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs)))) := by
  letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
    Module.IsTorsionBySet.module
      (tensorQuotientOfListMapEquiv_target_isTorsionBySet
        (R := R) (M := M) (S := S) rs)
  let eMid :=
    (((hqr.linearEquiv).restrictScalars R).baseChange R S :
      S ⊗[R]
          ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
            MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[S]
        S ⊗[R] idealAssociatedGradedModule (Ideal.ofList rs) M)
  let d' :
      Fin (rs.map (algebraMap R S)).length →₀ ℕ :=
    d.mapDomain (Fin.cast (List.length_map (as := rs) (algebraMap R S)).symm)
  let zSrc : idealAssociatedGradedStage (Ideal.ofList rs) M d.degree :=
    ⟨(∏ i : Fin rs.length, rs.get i ^ d i) • m,
      ofList_monomial_weight_smul_mem_of_degree rs d.degree m d rfl⟩
  let zTgt :
      idealAssociatedGradedStage
        (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) d.degree :=
    ⟨(∏ j : Fin (rs.map (algebraMap R S)).length,
          (rs.map (algebraMap R S)).get j ^ d' j) •
        (s ⊗ₜ[R] m),
      ofList_monomial_weight_smul_mem_of_degree
        (rs.map (algebraMap R S)) d.degree (s ⊗ₜ[R] m) d'
        (mapped_monomial_degree_cast (R := R) (S := S) rs d)⟩
  have hsrc :
      hqr.linearEquiv
          (((Submodule.Quotient.mk m : M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗ₜ[
              R ⧸ Ideal.ofList rs]
            MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))) =
        DirectSum.of (idealAssociatedGradedPiece (Ideal.ofList rs) M) d.degree
          (Submodule.Quotient.mk zSrc) := by
    -- Evaluate the source quasi-regularity equivalence on the chosen monomial generator.
    simpa [linearEquiv, zSrc] using
      quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_of_degree
        (P := M) (rs := rs) (m := m) (e := d) (n := d.degree) rfl
  have hmid :
      eMid
          (s ⊗ₜ[R]
            ((Submodule.Quotient.mk m : M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗ₜ[
                R ⧸ Ideal.ofList rs]
              MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))) =
        s ⊗ₜ[R]
          DirectSum.of (idealAssociatedGradedPiece (Ideal.ofList rs) M) d.degree
            (Submodule.Quotient.mk zSrc) := by
    -- After scalar restriction, base change just tensors the source monomial computation by `s`.
    simpa [eMid] using congrArg (fun y ↦ s ⊗ₜ[R] y) hsrc
  have hzTgt :
      tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs d.degree
          (s ⊗ₜ[R] zSrc) = zTgt := by
    -- Compare the two stage representatives on the ambient tensor product and package the result
    -- back into the subtype.
    apply Subtype.ext
    calc
      ((tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs d.degree
            (s ⊗ₜ[R] zSrc) :
          idealAssociatedGradedStage
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) d.degree) :
          S ⊗[R] M)
          = s ⊗ₜ[R] ((∏ i : Fin rs.length, rs.get i ^ d i) • m) := by
            simpa [zSrc] using
              tensorBaseChangeStage_linearEquiv_apply_tmul
                (R := R) (M := M) (S := S) rs d.degree s zSrc
      _ = ((∏ j : Fin (rs.map (algebraMap R S)).length,
              (rs.map (algebraMap R S)).get j ^ d' j) •
            (s ⊗ₜ[R] m) : S ⊗[R] M) := by
            symm
            simpa [d'] using
              mapped_ofList_monomial_weight_cast_smul_tmul
                (R := R) (M := M) (S := S) rs s m d
  have hleft :
      (tensorBaseChangeGradedModule_isBaseChange (R := R) (M := M) (S := S) rs).equiv
          (eMid
            (s ⊗ₜ[R]
              ((Submodule.Quotient.mk m :
                  M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
                MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs)))) =
        DirectSum.of
          (idealAssociatedGradedPiece
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M))
          d.degree
          (Submodule.Quotient.mk zTgt) := by
    -- First move through the scalar-extended source equivalence, then read the target through the
    -- degreewise graded-piece base-change equivalence.
    calc
      (tensorBaseChangeGradedModule_isBaseChange (R := R) (M := M) (S := S) rs).equiv
          (eMid
            (s ⊗ₜ[R]
              ((Submodule.Quotient.mk m :
                  M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
                MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))))
          =
        (tensorBaseChangeGradedModule_isBaseChange (R := R) (M := M) (S := S) rs).equiv
          (s ⊗ₜ[R]
            DirectSum.of (idealAssociatedGradedPiece (Ideal.ofList rs) M) d.degree
              (Submodule.Quotient.mk zSrc)) := by
        rw [hmid]
      _ =
        DirectSum.of
          (idealAssociatedGradedPiece
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M))
          d.degree
          (tensorBaseChangeGradedPiece_linearEquiv (R := R) (M := M) (S := S) rs d.degree
            (s ⊗ₜ[R] (Submodule.Quotient.mk zSrc))) := by
        simpa [DirectSum.lof_eq_of] using
          tensorBaseChangeGradedModule_isBaseChange_equiv_tmul_lof
            (R := R) (M := M) (S := S) rs d.degree s (Submodule.Quotient.mk zSrc)
      _ =
        DirectSum.of
          (idealAssociatedGradedPiece
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M))
          d.degree
          (Submodule.Quotient.mk
            (tensorBaseChangeStage_linearEquiv (R := R) (M := M) (S := S) rs d.degree
              (s ⊗ₜ[R] zSrc))) := by
        rw [tensorBaseChangeGradedPiece_linearEquiv_apply_tmul_mk]
      _ =
        DirectSum.of
          (idealAssociatedGradedPiece
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M))
          d.degree
          (Submodule.Quotient.mk zTgt) := by
        rw [hzTgt]
  have hright :
      quasiRegularSequenceAssociatedGradedMap
          (S ⊗[R] M) (rs.map (algebraMap R S))
          (tensorBaseChangeSourceLinearEquiv (R := R) (M := M) (S := S) rs
            (s ⊗ₜ[R]
              ((Submodule.Quotient.mk m :
                  M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗ₜ[R ⧸ Ideal.ofList rs]
                MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs)))) =
        DirectSum.of
          (idealAssociatedGradedPiece
            (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M))
          d.degree
          (Submodule.Quotient.mk zTgt) := by
    -- The source transport turns the generator into the mapped target monomial, and the target
    -- monomial computation is already available at the chosen degree.
    rw [tensorBaseChangeSourceLinearEquiv_apply_tmul_monomial
      (R := R) (M := M) (S := S) rs s m d]
    simpa [d', zTgt] using
      quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_of_degree
        (P := S ⊗[R] M) (rs := rs.map (algebraMap R S)) (m := s ⊗ₜ[R] m)
        (e := d') (n := d.degree)
        (mapped_monomial_degree_cast (R := R) (S := S) rs d)
  exact hleft.trans hright.symm

/-- Helper for Chap10 Lemma 10 69 3: after identifying both source modules by scalar extension,
the target associated-graded map is conjugate to the scalar extension of the source
quasi-regularity equivalence. -/
private theorem tensorBaseChangeAssociatedGradedMap_naturality
    {rs : List R} (hqr : IsQuasiRegular M rs) :
    letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
        (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
      Module.IsTorsionBySet.module
        (tensorQuotientOfListMapEquiv_target_isTorsionBySet
          (R := R) (M := M) (S := S) rs)
    let eMid :=
      (((hqr.linearEquiv).restrictScalars R).baseChange R S :
        S ⊗[R]
            ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
              MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[S]
          S ⊗[R] idealAssociatedGradedModule (Ideal.ofList rs) M)
    ((tensorBaseChangeGradedModule_isBaseChange (R := R) (M := M) (S := S) rs).equiv : _ → _) ∘
        eMid =
      quasiRegularSequenceAssociatedGradedMap
          (S ⊗[R] M) (rs.map (algebraMap R S)) ∘
        tensorBaseChangeSourceLinearEquiv (R := R) (M := M) (S := S) rs := by
  letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
    Module.IsTorsionBySet.module
      (tensorQuotientOfListMapEquiv_target_isTorsionBySet
        (R := R) (M := M) (S := S) rs)
  let eMid :=
    (((hqr.linearEquiv).restrictScalars R).baseChange R S :
      S ⊗[R]
          ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
            MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[S]
        S ⊗[R] idealAssociatedGradedModule (Ideal.ofList rs) M)
  let f :
      S ⊗[R] idealAssociatedGradedModule (Ideal.ofList rs) M →+
        idealAssociatedGradedModule
          (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) :=
    ((tensorBaseChangeGradedModule_isBaseChange (R := R) (M := M) (S := S) rs).equiv :
      _ ≃ₗ[S] _).toLinearMap.toAddMonoidHom
  let gSrc :
      S ⊗[R]
          ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
            MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) →ₗ[S]
        (((S ⊗[R] M) ⧸
            (Ideal.ofList (rs.map (algebraMap R S)) •
              (⊤ : Submodule S (S ⊗[R] M)))) ⊗[
              S ⧸ Ideal.ofList (rs.map (algebraMap R S))]
          MvPolynomial (Fin (rs.map (algebraMap R S)).length)
            (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))) :=
    (tensorBaseChangeSourceLinearEquiv (R := R) (M := M) (S := S) rs).toLinearMap
  let g :
      S ⊗[R]
          ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
            MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) →+
        idealAssociatedGradedModule
          (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) :=
    (quasiRegularSequenceAssociatedGradedMap
      (S ⊗[R] M) (rs.map (algebraMap R S))).toAddMonoidHom.comp
      gSrc.toAddMonoidHom
  -- Expand an arbitrary source tensor into monomial simple tensors and compare both composites on
  -- those generators. Route correction: start with literal function extensionality so the outer
  -- tensor induction stays on the intended source tensor variable.
  funext z
  change f (eMid z) = g z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · calc
      f (eMid 0) = f 0 := by
        rw [eMid.map_zero]
      _ = 0 := by
        exact f.map_zero
      _ = g 0 := by
        exact (g.map_zero).symm
  · intro s x
    obtain ⟨coeffs, hcoeffs⟩ := tensor_monomial_expansion (P := M) rs x
    have htmul :
        (s ⊗ₜ[R] x :
          S ⊗[R]
            ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
              MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs))) =
          coeffs.support.sum
            (fun d : Fin rs.length →₀ ℕ ↦
              s ⊗ₜ[R]
                (coeffs d ⊗ₜ[R ⧸ Ideal.ofList rs]
                  MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))) := by
      rw [hcoeffs, Finsupp.sum, TensorProduct.tmul_sum]
    -- Rewrite both composites through the explicit additive maps `f` and `g`, so the monomial
    -- expansion uses owner-level `map_sum` only once on each side.
    have hLeft :
        f (eMid (s ⊗ₜ[R] x)) =
          coeffs.support.sum
            (fun d : Fin rs.length →₀ ℕ ↦
              f (eMid
                (s ⊗ₜ[R]
                  (coeffs d ⊗ₜ[R ⧸ Ideal.ofList rs]
                    MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))))) := by
      calc
        f (eMid (s ⊗ₜ[R] x)) =
            f (eMid
              (coeffs.support.sum
                (fun d : Fin rs.length →₀ ℕ ↦
                  s ⊗ₜ[R]
                    (coeffs d ⊗ₜ[R ⧸ Ideal.ofList rs]
                      MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))))) := by
              rw [htmul]
        _ =
            f (coeffs.support.sum
              (fun d : Fin rs.length →₀ ℕ ↦
                eMid
                  (s ⊗ₜ[R]
                    (coeffs d ⊗ₜ[R ⧸ Ideal.ofList rs]
                      MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))))) := by
              exact congrArg f (_root_.map_sum eMid.toLinearMap _ _)
        _ =
            coeffs.support.sum
              (fun d : Fin rs.length →₀ ℕ ↦
                f (eMid
                  (s ⊗ₜ[R]
                    (coeffs d ⊗ₜ[R ⧸ Ideal.ofList rs]
                      MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))))) := by
              simpa using (_root_.map_sum f _ _)
    have hRight :
        g (s ⊗ₜ[R] x) =
          coeffs.support.sum
            (fun d : Fin rs.length →₀ ℕ ↦
              g
                (s ⊗ₜ[R]
                  (coeffs d ⊗ₜ[R ⧸ Ideal.ofList rs]
                    MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs)))) := by
      calc
        g (s ⊗ₜ[R] x) =
            g (coeffs.support.sum
              (fun d : Fin rs.length →₀ ℕ ↦
                s ⊗ₜ[R]
                  (coeffs d ⊗ₜ[R ⧸ Ideal.ofList rs]
                    MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs)))) := by
              rw [htmul]
        _ =
            coeffs.support.sum
              (fun d : Fin rs.length →₀ ℕ ↦
                g
                  (s ⊗ₜ[R]
                    (coeffs d ⊗ₜ[R ⧸ Ideal.ofList rs]
                      MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs)))) := by
              simpa using (_root_.map_sum g _ _)
    calc
      f (eMid (s ⊗ₜ[R] x)) =
          coeffs.support.sum
            (fun d : Fin rs.length →₀ ℕ ↦
              f (eMid
                (s ⊗ₜ[R]
                  (coeffs d ⊗ₜ[R ⧸ Ideal.ofList rs]
                    MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs))))) := hLeft
      _ =
          coeffs.support.sum
            (fun d : Fin rs.length →₀ ℕ ↦
              g
                (s ⊗ₜ[R]
                  (coeffs d ⊗ₜ[R ⧸ Ideal.ofList rs]
                    MvPolynomial.monomial d (1 : R ⧸ Ideal.ofList rs)))) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          refine Quotient.inductionOn' (coeffs d) ?_
          intro m
          simpa [f, g, eMid] using
            tensorBaseChangeAssociatedGradedMapNaturality_tmul
              (R := R) (M := M) (S := S) hqr s m d
      _ = g (s ⊗ₜ[R] x) := hRight.symm
  · intro x y hx hy
    -- Preserve the commuting-square identity under addition using linearity of the packaged maps.
    calc
      f (eMid (x + y)) = f (eMid x + eMid y) := by
        exact congrArg f (eMid.map_add x y)
      _ = f (eMid x) + f (eMid y) := by
        exact f.map_add (eMid x) (eMid y)
      _ = g x + g y := by
        exact congrArg₂ (· + ·) hx hy
      _ = g (x + y) := by
        exact (g.map_add x y).symm

-- Proof sketch: this is the textbook tensor-product base-change case. One must identify the
-- degree-zero quotient and each associated-graded piece after tensoring with `S`, and then check
-- that `quasiRegularSequenceAssociatedGradedMap` is conjugated by those identifications.
/-- Helper for Lemma 10.69.3: the canonical tensor-product base change preserves quasi-regularity.
This is the source-faithful tensor case from which the owner-level `IsBaseChange` statement is
derived. -/
private theorem tensor_baseChange {rs : List R} (hqr : IsQuasiRegular M rs) :
    IsQuasiRegular (S ⊗[R] M) (rs.map (algebraMap R S)) := by
  letI : Module (S ⧸ Ideal.ofList (rs.map (algebraMap R S)))
      (S ⊗[R] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))) :=
    Module.IsTorsionBySet.module
      (tensorQuotientOfListMapEquiv_target_isTorsionBySet
        (R := R) (M := M) (S := S) rs)
  let eSrc :=
    (tensorBaseChangeSourceLinearEquiv (R := R) (M := M) (S := S) rs).toEquiv
  let eMid :=
    ((((hqr.linearEquiv).restrictScalars R).baseChange R S :
      S ⊗[R]
          ((M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList rs]
            MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs)) ≃ₗ[S]
        S ⊗[R] idealAssociatedGradedModule (Ideal.ofList rs) M)).toEquiv
  let eTgt :=
    ((tensorBaseChangeGradedModule_isBaseChange (R := R) (M := M) (S := S) rs).equiv).toEquiv
  have hcomm :
      eTgt ∘ eMid =
        quasiRegularSequenceAssociatedGradedMap
            (S ⊗[R] M) (rs.map (algebraMap R S)) ∘
          eSrc := by
    -- The previous theorem isolates the commuting square needed to transport injectivity.
    simpa [eSrc, eMid, eTgt] using
      tensorBaseChangeAssociatedGradedMap_naturality
        (R := R) (M := M) (S := S) hqr
  have hmid_injective : Function.Injective eMid := eMid.injective
  have htarget_injective :
      Function.Injective
        (quasiRegularSequenceAssociatedGradedMap
          (S ⊗[R] M) (rs.map (algebraMap R S))) :=
    (injective_iff_of_equiv_conjugate eSrc eTgt eMid
      (quasiRegularSequenceAssociatedGradedMap
        (S ⊗[R] M) (rs.map (algebraMap R S))) hcomm).1 hmid_injective
  -- Route correction: after the square is established, quasi-regularity is just the injective
  -- half of the target associated-graded comparison map.
  exact
    (isQuasiRegular_iff_injective (R := S) (M := S ⊗[R] M)
      (rs := rs.map (algebraMap R S))).2 htarget_injective

-- Proof sketch: reinterpret quasi-regularity through the associated-graded comparison map and use
-- the owner-level base-change equivalence `hf.equiv` to transport the source graded pieces to the
-- target ones. Flatness identifies the graded pieces after scalar extension, so tensoring the
-- defining isomorphism for `M` yields the desired isomorphism for `N`.
/-- Canonical flat-base-change bridge for quasi-regular sequences along an owner-level base-change
map. The textbook tensor-product statement is the specialization `of_flat`. -/
theorem of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {rs : List R}
    (hqr : IsQuasiRegular M rs) :
    IsQuasiRegular N (rs.map (algebraMap R S)) := by
  -- The owner-level statement is now a pure transport problem from the canonical tensor-product
  -- case along the base-change equivalence `hf.equiv`.
  exact
    (congr_linearEquiv (e := hf.equiv) (rs := rs.map (algebraMap R S))).1
      (tensor_baseChange (R := R) (M := M) (S := S) hqr)

-- Proof sketch: specialize `of_flat_of_isBaseChange` to the canonical tensor-product base-change
-- map `TensorProduct.mk R S M 1`, whose base-change property is `TensorProduct.isBaseChange`.
/-- Chap10 Lemma 10 69 3: for a flat ring map `R → S`, an `M`-quasi-regular sequence in `R` remains
quasi-regular after extending scalars to `S`. -/
@[stacks 065L]
theorem of_flat {rs : List R} (hqr : IsQuasiRegular M rs) :
    IsQuasiRegular (S ⊗[R] M) (rs.map (algebraMap R S)) := by
  -- This is exactly the canonical tensor-product case isolated above.
  exact tensor_baseChange (R := R) (M := M) (S := S) hqr

end IsQuasiRegular

end RingTheory.Sequence
