import Mathlib
import stacks_project.Chap10.Lemma_10_69_2

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
  -- TODO for Lemma 10.69.3: build this by descending the explicit stage map
  -- `idealAssociatedGradedStage_linearEquiv` through `Submodule.mapQ`, and then prove the inverse
  -- identities on representatives using the new stage-level computation rules above.
  sorry

/-- Helper for Lemma 10.69.3: the piece transport acts on quotient representatives by the stage
transport. -/
@[simp] private theorem idealAssociatedGradedPiece_linearEquiv_apply_mk
    {P : Type*} [AddCommGroup P] [Module S P]
    {Q : Type*} [AddCommGroup Q] [Module S Q]
    (e : P ≃ₗ[S] Q) (rs : List S) (n : ℕ)
    (x : idealAssociatedGradedStage (Ideal.ofList rs) P n) :
    idealAssociatedGradedPiece_linearEquiv (e := e) rs n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (idealAssociatedGradedStage_linearEquiv (e := e) rs n x) := by
  -- TODO for Lemma 10.69.3: after `idealAssociatedGradedPiece_linearEquiv` is defined through
  -- `Submodule.mapQ`, compute it on quotient representatives by `Submodule.mapQ_apply`.
  sorry

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
  -- TODO for Lemma 10.69.3: now that the graded-piece transport is explicit, compute both sides
  -- on the monomial generator by `quasiRegularSequenceAssociatedGradedMap_tmul_monomial`, rewrite
  -- the target representative with `idealAssociatedGradedPiece_linearEquiv_apply_mk`, and finish
  -- by `idealAssociatedGradedStage_linearEquiv_apply` plus `e.map_smul`.
  sorry

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
  -- TODO for Lemma 10.69.3: after proving the monomial-generator square in
  -- `quasiRegularSequenceAssociatedGradedMap_linear_naturality_tmul`, extend to the full tensor
  -- source by tensor-product extensionality, quotient induction on the first factor, and
  -- `MvPolynomial.induction_on'` on the polynomial factor.
  sorry

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

-- Proof sketch: this is the textbook tensor-product base-change case. One must identify the
-- degree-zero quotient and each associated-graded piece after tensoring with `S`, and then check
-- that `quasiRegularSequenceAssociatedGradedMap` is conjugated by those identifications.
/-- Helper for Lemma 10.69.3: the canonical tensor-product base change preserves quasi-regularity.
This is the source-faithful tensor case from which the owner-level `IsBaseChange` statement is
derived. -/
private theorem tensor_baseChange {rs : List R} (hqr : IsQuasiRegular M rs) :
    IsQuasiRegular (S ⊗[R] M) (rs.map (algebraMap R S)) := by
  -- TODO for Lemma 10.69.3: prove the literal stage equality
  -- `idealAssociatedGradedStage (Ideal.ofList (rs.map (algebraMap R S))) (S ⊗[R] M) n =
  --   (idealAssociatedGradedStage (Ideal.ofList rs) M n).baseChange S`,
  -- build the induced source and graded-piece equivalences using
  -- `TensorProduct.tensorQuotMapSMulEquivTensorQuot`, and then verify the conjugation square on
  -- generators `Submodule.Quotient.mk m ⊗ monomial e 1`.
  sorry

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
/-- Lemma 10.69.3: for a flat ring map `R → S`, an `M`-quasi-regular sequence in `R` remains
quasi-regular after extending scalars to `S`. -/
theorem of_flat {rs : List R} (hqr : IsQuasiRegular M rs) :
    IsQuasiRegular (S ⊗[R] M) (rs.map (algebraMap R S)) := by
  -- This is exactly the canonical tensor-product case isolated above.
  exact tensor_baseChange (R := R) (M := M) (S := S) hqr

end IsQuasiRegular

end RingTheory.Sequence
