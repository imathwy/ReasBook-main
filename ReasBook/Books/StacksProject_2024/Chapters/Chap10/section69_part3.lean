import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_69_3 (from Chap10) -/
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

/-! ### Lemma_10_69_4 (from Chap10) -/
universe u v

open RingTheory
open scoped TensorProduct

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-
Domain triage:
* primary domain: quasi-regular sequences in commutative algebra and their behavior under
  localization;
* sampled owner API:
  `RingTheory.Sequence.IsQuasiRegular`,
  `RingTheory.Sequence.IsQuasiRegular.of_flat_of_isBaseChange`,
  `RingTheory.Sequence.IsRegular.exists_away_of_atPrime`,
  `LocalizedModule.AtPrime`;
* source-facing layer: `RingTheory.Sequence.IsQuasiRegular M xs`;
* core/canonical owner abstractions used by this item: the source-facing predicate
  `IsQuasiRegular` together with the canonical localization owners `Localization.AtPrime`,
  `Localization.Away`, `LocalizedModule.AtPrime`, and `LocalizedModule.Away`;
* primitive vs derived split: the localized rings and modules are primitive owner data, while the
  existence of an element `g ∉ p` spreading quasi-regularity from `M_𝔭` to `M_g` is derived bridge
  API;
* layer: `bridge/view`, since the theorem transports the source-facing quasi-regularity predicate
  along the canonical localization owners without introducing any new owner-level structure.
-/

namespace RingTheory.Sequence

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: a finite product of elements outside a prime ideal remains outside
that prime ideal. -/
lemma finset_prod_notMem_prime (p : Ideal R) [p.IsPrime] {n : ℕ} (g : Fin n → R)
    (hg : ∀ i, g i ∉ p) : (∏ i, g i) ∉ p := by
  -- Use the prime complement multiplicative closure to keep the final denominator away from `p`.
  simpa using p.primeCompl.prod_mem fun i _ ↦ hg i

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: localizing a linear map is injective exactly when the localized
kernel module is trivial. -/
lemma localized_map_injective_iff_subsingleton_kernel {N : Type*}
    [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N) (S : Submonoid R) :
    Function.Injective (LocalizedModule.map S φ) ↔
      Subsingleton (LocalizedModule S (LinearMap.ker φ)) := by
  let κ : LinearMap.ker φ →ₗ[R] LinearMap.ker (LocalizedModule.map S φ) :=
    LinearMap.toKerIsLocalized
      (p := S)
      (f := LocalizedModule.mkLinearMap S M)
      (f' := LocalizedModule.mkLinearMap S N)
      φ
  let _ : IsLocalizedModule S κ :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Localization S)
      (p := S)
      (f := LocalizedModule.mkLinearMap S M)
      (f' := LocalizedModule.mkLinearMap S N)
      φ
  -- Compare the localized kernel module with the actual kernel after localizing the map.
  constructor
  · intro hφ
    have hker :
        LinearMap.ker (LocalizedModule.map S φ) = ⊥ :=
      LinearMap.ker_eq_bot.2 hφ
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map S φ)) :=
      Submodule.subsingleton_iff_eq_bot.2 hker
    exact ((IsLocalizedModule.iso S κ).toEquiv.subsingleton_congr).2 hsub
  · intro hker
    have hsub :
        Subsingleton (LinearMap.ker (LocalizedModule.map S φ)) :=
      ((IsLocalizedModule.iso S κ).toEquiv.subsingleton_congr).1 hker
    exact LinearMap.ker_eq_bot.1 (Submodule.subsingleton_iff_eq_bot.1 hsub)

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: injectivity transports across a commuting square whose horizontal
maps are equivalences. -/
lemma injective_iff_of_equiv_conjugate
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

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: if a module is finite over an `R`-algebra and vanishes at `p`, then
it already vanishes after inverting one element outside `p`. -/
lemma exists_subsingleton_away_of_finite_over_algebra (p : Ideal R) [p.IsPrime]
    {A : Type*} [CommRing A] [Algebra R A] {N : Type*}
    [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]
    [Module.Finite A N] [Subsingleton (LocalizedModule p.primeCompl N)] :
    ∃ g : R, g ∉ p ∧ Subsingleton (LocalizedModule (.powers g) N) := by
  classical
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A N
  let generators : Fin n → N := fun i ↦ f (Pi.single i 1)
  have hkill_one :
      ∀ i : Fin n, ∃ s : R, s ∉ p ∧ s • generators i = 0 := by
    intro i
    -- The prime localization is trivial, so each chosen generator is killed by one denominator.
    obtain ⟨s, hs, hszero⟩ :=
      (LocalizedModule.subsingleton_iff.mp
        (show Subsingleton (LocalizedModule p.primeCompl N) from inferInstance))
        (generators i)
    exact ⟨s, hs, hszero⟩
  choose s hs_notMem hs_zero using hkill_one
  let g : R := ∏ i, s i
  have hg : g ∉ p := finset_prod_notMem_prime p s hs_notMem
  have hg_zero_generators : ∀ i : Fin n, g • generators i = 0 := by
    intro i
    -- Once one factor kills the `i`th generator, the full product does too.
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem s (Finset.mem_univ i)
    calc
      g • generators i = ((s i) * c) • generators i := by simp [g, hc]
      _ = (c * s i) • generators i := by rw [mul_comm]
      _ = c • (s i • generators i) := by
        simp [smul_smul]
      _ = 0 := by simp [hs_zero i]
  have hspan :
      Submodule.span A (Set.range generators) = ⊤ := by
    refine top_le_iff.mp ?_
    intro x hx
    obtain ⟨y, rfl⟩ := hf x
    -- Expand a vector in the finite free source on the standard basis.
    have hy :
        y = ∑ i, y i • ((Pi.single i (1 : A)) : Fin n → A) := by
      ext i
      rw [Finset.sum_apply]
      symm
      simpa [Pi.smul_apply, Pi.single_apply] using
        (Finset.sum_eq_single i
          (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n ↦ y j * Pi.single j (1 : A) i)
          (fun j _ hj ↦ by simp [Pi.single_apply, hj])
          (fun hi ↦ by simp at hi))
    rw [hy, map_sum]
    refine Submodule.sum_mem (Submodule.span A (Set.range generators)) fun i _ ↦ ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hg_zero_all : ∀ x : N, g • x = 0 := by
    intro x
    -- The product denominator kills the spanning family, hence the whole module.
    have hx :
        x ∈ Submodule.span A (Set.range generators) := by
      simpa [hspan]
    refine Submodule.span_induction (p := fun x _ ↦ g • x = 0) ?_ ?_ ?_ ?_ hx
    · intro x hx
      rcases hx with ⟨i, rfl⟩
      exact hg_zero_generators i
    · simp
    · intro x y hx hy hx_zero hy_zero
      simp [smul_add, hx_zero, hy_zero]
    · intro a x hx hx_zero
      calc
        g • (a • x) = a • (g • x) := by
          simpa [smul_assoc] using (smul_comm g a x)
        _ = 0 := by simp [hx_zero]
  refine ⟨g, hg, ?_⟩
  -- Now one power of `g` already annihilates every element, so the away localization is trivial.
  rw [LocalizedModule.subsingleton_iff]
  intro x
  exact ⟨g, ⟨1, by simp⟩, hg_zero_all x⟩

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: the kernel of the associated-graded map carries the ambient
`R`-module structure by restricting scalars from the polynomial ring. -/
noncomputable instance quasiRegularSequenceAssociatedGraded_kernel_module (xs : List R) :
    Module R (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs)) :=
  Module.restrictScalars R
    (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))
    (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: the restricted `R`-action on the kernel is compatible with the
ambient polynomial-ring action. -/
instance quasiRegularSequenceAssociatedGraded_kernel_isScalarTower (xs : List R) :
    IsScalarTower R (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))
      (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs)) := by
  refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
  change ((algebraMap R (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))) r) • x =
    ((algebraMap R (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))) r) • x
  rfl

/-- Helper for Lemma 10.69.4: the kernel of the associated-graded comparison map is finite over
the polynomial ring. -/
lemma quasiRegularSequenceAssociatedGraded_kernel_finite (xs : List R) :
    Module.Finite (MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs))
      (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs)) := by
  let J : Ideal R := Ideal.ofList xs
  let A : Type u := MvPolynomial (Fin xs.length) (R ⧸ J)
  let Q : Type v := M ⧸ (J • ⊤ : Submodule R M)
  -- The quotient `M / JM` is finite over `R / J`, so its polynomial base change is finite over
  -- `A = (R / J)[X₁, ..., X_c]`.
  have hQ : Module.Finite (R ⧸ J) Q := by
    let _ : Module.Finite R Q := inferInstance
    simpa [Q] using (Module.Finite.of_restrictScalars_finite R (R ⧸ J) Q)
  let _ : Module.Finite (R ⧸ J) Q := hQ
  let _ : IsNoetherianRing (R ⧸ J) :=
    isNoetherianRing_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  let _ : IsNoetherianRing A := inferInstance
  let _ : Module A (A ⊗[R ⧸ J] Q) := TensorProduct.leftModule
  let _ : Module A (Q ⊗[R ⧸ J] A) :=
    (TensorProduct.comm (R ⧸ J) Q A).toAddEquiv.module A
  let _ : Module.Finite A (A ⊗[R ⧸ J] Q) :=
    Module.Finite.base_change (R := R ⧸ J) (A := A) (M := Q)
  let eComm : (A ⊗[R ⧸ J] Q) ≃ₗ[A] (Q ⊗[R ⧸ J] A) :=
    (((TensorProduct.comm (R ⧸ J) Q A).toAddEquiv).linearEquiv A).symm
  have hTextbookFinite : Module.Finite A (Q ⊗[R ⧸ J] A) := by
    exact Module.Finite.equiv eComm
  let _ : Module.Finite A (Q ⊗[R ⧸ J] A) := hTextbookFinite
  have hNoetherianTextbook : IsNoetherian A (Q ⊗[R ⧸ J] A) := by
    infer_instance
  let _ : IsNoetherian A (Q ⊗[R ⧸ J] A) := hNoetherianTextbook
  have hfg :
      (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs)).FG := by
    -- Over a Noetherian polynomial ring, every submodule of the finite source is finitely
    -- generated, so in particular the kernel is finite.
    simpa [J, A, Q] using
      (IsNoetherian.noetherian
        (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs)))
  exact Module.Finite.of_fg hfg

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: localizing the quotient `M / (Ideal.ofList xs) M` agrees with
quotienting the localized module by the localized ideal image. -/
noncomputable def localized_ofList_smul_top_quotient_equiv
    (xs : List R) (S : Submonoid R) :
    LocalizedModule S (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)) ≃ₗ[Localization S]
      ((LocalizedModule S M) ⧸
        (Ideal.ofList (xs.map (algebraMap R (Localization S))) • ⊤ :
          Submodule (Localization S) (LocalizedModule S M))) := by
  have hlocalized :
      ((Ideal.ofList xs • ⊤ : Submodule R M)).localized S =
        (Ideal.ofList (xs.map (algebraMap R (Localization S))) • ⊤ :
          Submodule (Localization S) (LocalizedModule S M)) := by
    -- Rewrite the localized submodule through the mapped list ideal before passing to quotients.
    rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top, Ideal.map_ofList]
  -- The quotient-localization owner equivalence becomes the desired textbook quotient after the
  -- explicit ideal rewrite above.
  exact (localizedQuotientEquiv S (Ideal.ofList xs • ⊤ : Submodule R M)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hlocalized

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: the quotient-localization comparison sends the localized class of
`m` to the class of the localized numerator. -/
lemma localized_ofList_smul_top_quotient_equiv_apply_mk
    (xs : List R) (S : Submonoid R) (m : M) :
    localized_ofList_smul_top_quotient_equiv (M := M) xs S
      (LocalizedModule.mkLinearMap S (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))
        (Submodule.Quotient.mk m)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m) := by
  have hlocalized :
      ((Ideal.ofList xs • ⊤ : Submodule R M)).localized S =
        (Ideal.ofList (xs.map (algebraMap R (Localization S))) • ⊤ :
          Submodule (Localization S) (LocalizedModule S M)) := by
    -- Rewrite the localized submodule through the mapped list ideal before touching quotients.
    rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top, Ideal.map_ofList]
  have hmk :
      (localizedQuotientEquiv S (Ideal.ofList xs • ⊤ : Submodule R M)).symm
        (LocalizedModule.mkLinearMap S (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))
          (Submodule.Quotient.mk m)) =
        (Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m) :
          (LocalizedModule S M) ⧸ ((Ideal.ofList xs • ⊤ : Submodule R M)).localized S) := by
    -- First compute the inverse quotient-localization equivalence on the chosen quotient
    -- generator.
    simpa [localizedQuotientEquiv, Submodule.toLocalizedQuotient] using
      (IsLocalizedModule.linearEquiv_symm_apply
        (S := S)
        (f := (Ideal.ofList xs • ⊤ : Submodule R M).toLocalizedQuotient S)
        (g := LocalizedModule.mkLinearMap S (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M)))
        (x := Submodule.Quotient.mk m))
  -- Then rewrite the target quotient by transporting the submodule equality `hlocalized`.
  calc
    localized_ofList_smul_top_quotient_equiv (M := M) xs S
        (LocalizedModule.mkLinearMap S (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))
          (Submodule.Quotient.mk m)) =
      ((Submodule.quotEquivOfEq
          (((Ideal.ofList xs • ⊤ : Submodule R M)).localized S)
          (Ideal.ofList (xs.map (algebraMap R (Localization S))) • ⊤ :
            Submodule (Localization S) (LocalizedModule S M))
          hlocalized)
        ((localizedQuotientEquiv S (Ideal.ofList xs • ⊤ : Submodule R M)).symm
          (LocalizedModule.mkLinearMap S (M ⧸ (Ideal.ofList xs • ⊤ : Submodule R M))
            (Submodule.Quotient.mk m)))) := by
          rfl
    _ = ((Submodule.quotEquivOfEq
          (((Ideal.ofList xs • ⊤ : Submodule R M)).localized S)
          (Ideal.ofList (xs.map (algebraMap R (Localization S))) • ⊤ :
            Submodule (Localization S) (LocalizedModule S M))
          hlocalized)
        (Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m))) := by
          rw [hmk]
    _ = Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m) := by
          rw [Submodule.quotEquivOfEq_mk]

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: localizing the quotient ring `R / Ideal.ofList xs` at the image of
`S` agrees with quotienting `Localization S` by the mapped list ideal. -/
noncomputable def localized_ofList_quotientRing_ringEquiv
    (xs : List R) (S : Submonoid R) :
    Localization (Algebra.algebraMapSubmonoid (R ⧸ Ideal.ofList xs) S) ≃+*
      ((Localization S) ⧸ Ideal.ofList (xs.map (algebraMap R (Localization S)))) := by
  let J : Ideal R := Ideal.ofList xs
  let IS : Ideal (Localization S) := Ideal.map (algebraMap R (Localization S)) J
  let eLoc :
      Localization (Algebra.algebraMapSubmonoid (R ⧸ J) S) ≃ₐ[R ⧸ J]
        ((Localization S) ⧸ IS) :=
    Localization.algEquiv (Algebra.algebraMapSubmonoid (R ⧸ J) S) ((Localization S) ⧸ IS)
  have hIS :
      IS = Ideal.ofList (xs.map (algebraMap R (Localization S))) := by
    -- Rewrite the mapped list ideal into the literal image list ideal once and for all.
    change Ideal.map (algebraMap R (Localization S)) (Ideal.ofList xs) =
      Ideal.ofList (xs.map (algebraMap R (Localization S)))
    simpa using (Ideal.map_ofList (f := algebraMap R (Localization S)) xs)
  -- First identify the localization of `R / J`, then rewrite the target ideal to the literal
  -- localized list ideal.
  exact eLoc.toRingEquiv.trans (Ideal.quotEquivOfEq hIS)

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: each `J`-adic stage localizes to the corresponding stage for the
localized list, where `J = Ideal.ofList xs`. -/
lemma localized_idealAssociatedGradedStage_eq
    (xs : List R) (S : Submonoid R) (n : ℕ) :
    (idealAssociatedGradedStage (Ideal.ofList xs) M n).localized S =
      idealAssociatedGradedStage
        (Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (LocalizedModule S M) n := by
  -- Expand the stage as `J ^ n M`, localize the ideal action, and rewrite the mapped ideal and
  -- its powers in the localized ring.
  rw [Submodule.localized, idealAssociatedGradedStage, idealAssociatedGradedStage,
    Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top,
    Ideal.map_pow, Ideal.map_ofList]

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: the localization of the stage `J^n M` as a module is canonically
identified with the corresponding localized stage inside `M_S`. -/
noncomputable def localized_idealAssociatedGradedStage_linearEquiv
    (xs : List R) (S : Submonoid R) (n : ℕ) :
    LocalizedModule S (idealAssociatedGradedStage (Ideal.ofList xs) M n) ≃ₗ[Localization S]
      idealAssociatedGradedStage
        (Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (LocalizedModule S M) n := by
  let hstage :=
    localized_idealAssociatedGradedStage_eq (M := M) xs S n
  -- First remove the ambient-submodule presentation, then rewrite the localized stage by the
  -- explicit stage equality above.
  exact
    ((idealAssociatedGradedStage (Ideal.ofList xs) M n).localizedEquiv S).symm.trans
      (LinearEquiv.ofEq _ _ hstage)

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: on localized stage generators, the stage localization equivalence is
induced by the ambient localization map. -/
@[simp] lemma localized_idealAssociatedGradedStage_linearEquiv_apply_mk
    (xs : List R) (S : Submonoid R) (n : ℕ)
    (x : idealAssociatedGradedStage (Ideal.ofList xs) M n) :
    ((localized_idealAssociatedGradedStage_linearEquiv (M := M) xs S n
        (LocalizedModule.mkLinearMap S (idealAssociatedGradedStage (Ideal.ofList xs) M n) x) :
          idealAssociatedGradedStage
            (Ideal.ofList (xs.map (algebraMap R (Localization S))))
            (LocalizedModule S M) n) : LocalizedModule S M) =
      LocalizedModule.mkLinearMap S M x := by
  -- Unfold the localization equivalence once; on a stage generator it is exactly the ambient
  -- localization map followed by the explicit stage rewrite.
  -- TODO(Lemma 10.69.4): identify the coercion from the localized stage submodule back into the
  -- ambient localized module, then rewrite `IsLocalizedModule.linearEquiv_symm_apply` for
  -- `Submodule.localizedEquiv` through that coercion.
  sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: the inverse stage localization equivalence sends a localized stage
generator back to the corresponding localized numerator in the source stage. -/
@[simp] lemma localized_idealAssociatedGradedStage_linearEquiv_symm_apply_mk
    (xs : List R) (S : Submonoid R) (n : ℕ)
    (x : idealAssociatedGradedStage (Ideal.ofList xs) M n) :
    ((localized_idealAssociatedGradedStage_linearEquiv (M := M) xs S n).symm
        ⟨LocalizedModule.mkLinearMap S M x, by
          -- Rewrite the ambient localized stage back to the explicit localized stage equality.
          simpa [localized_idealAssociatedGradedStage_eq] using
            (show LocalizedModule.mkLinearMap S M x ∈
              (idealAssociatedGradedStage (Ideal.ofList xs) M n).localized S from
                ⟨x, x.2, 1, by simp⟩)⟩ :
        LocalizedModule S (idealAssociatedGradedStage (Ideal.ofList xs) M n)) =
      LocalizedModule.mkLinearMap S (idealAssociatedGradedStage (Ideal.ofList xs) M n) x := by
  -- Route correction: the inverse is the explicit stage rewrite back to the source stage followed
  -- by the canonical localization equivalence of the stage submodule.
  apply (localized_idealAssociatedGradedStage_linearEquiv (M := M) xs S n).injective
  calc
    localized_idealAssociatedGradedStage_linearEquiv (M := M) xs S n
        ((localized_idealAssociatedGradedStage_linearEquiv (M := M) xs S n).symm
          ⟨LocalizedModule.mkLinearMap S M x, by
            simpa [localized_idealAssociatedGradedStage_eq] using
              (show LocalizedModule.mkLinearMap S M x ∈
                (idealAssociatedGradedStage (Ideal.ofList xs) M n).localized S from
                  ⟨x, x.2, 1, by simp⟩)⟩) =
      ⟨LocalizedModule.mkLinearMap S M x, by
        simpa [localized_idealAssociatedGradedStage_eq] using
          (show LocalizedModule.mkLinearMap S M x ∈
            (idealAssociatedGradedStage (Ideal.ofList xs) M n).localized S from
              ⟨x, x.2, 1, by simp⟩)⟩ := by
          simp
    _ = localized_idealAssociatedGradedStage_linearEquiv (M := M) xs S n
        (LocalizedModule.mkLinearMap S (idealAssociatedGradedStage (Ideal.ofList xs) M n) x) := by
          apply Subtype.ext
          exact (localized_idealAssociatedGradedStage_linearEquiv_apply_mk
            (M := M) xs S n x).symm

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: the localized kernel of the associated-graded map vanishes exactly
when the localized sequence is quasi-regular. -/
lemma localized_quasiRegularSequenceAssociatedGraded_restrictScalars_injective_iff
    (xs : List R) (S : Submonoid R) :
    let A : Type u := MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs)
    let source :=
      RestrictScalars R A
        (((M ⧸ ((Ideal.ofList xs) • ⊤ : Submodule R M)) ⊗[R ⧸ Ideal.ofList xs] A))
    let target :=
      RestrictScalars R A (idealAssociatedGradedModule (Ideal.ofList xs) M)
    letI : Module A source :=
      RestrictScalars.moduleOrig R A
        (((M ⧸ ((Ideal.ofList xs) • ⊤ : Submodule R M)) ⊗[R ⧸ Ideal.ofList xs] A))
    letI : Module A target :=
      RestrictScalars.moduleOrig R A (idealAssociatedGradedModule (Ideal.ofList xs) M)
    letI : Module R source := Module.restrictScalars R A source
    letI : Module R target := Module.restrictScalars R A target
    let φR : source →ₗ[R] target :=
      { toFun := quasiRegularSequenceAssociatedGradedMap M xs
        map_add' := by
          intro x y
          exact (quasiRegularSequenceAssociatedGradedMap M xs).map_add x y
        map_smul' := by
          intro r x
          -- Rewrite the restricted `R`-action back to the polynomial-ring action.
          rw [show r • x = ((algebraMap R A) r) • x by rfl]
          change
            (quasiRegularSequenceAssociatedGradedMap M xs) (((algebraMap R A) r) • x) =
              ((algebraMap R A) r) • (quasiRegularSequenceAssociatedGradedMap M xs x)
          exact
            (quasiRegularSequenceAssociatedGradedMap M xs).map_smul
              ((algebraMap R A) r) x }
    Function.Injective (LocalizedModule.map S φR) ↔
      Function.Injective
        (quasiRegularSequenceAssociatedGradedMap (LocalizedModule S M)
          (xs.map (algebraMap R (Localization S)))) := by
  let A : Type u := MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs)
  let source :=
    RestrictScalars R A
      (((M ⧸ ((Ideal.ofList xs) • ⊤ : Submodule R M)) ⊗[R ⧸ Ideal.ofList xs] A))
  let target :=
    RestrictScalars R A (idealAssociatedGradedModule (Ideal.ofList xs) M)
  letI : Module A source :=
    RestrictScalars.moduleOrig R A
      (((M ⧸ ((Ideal.ofList xs) • ⊤ : Submodule R M)) ⊗[R ⧸ Ideal.ofList xs] A))
  letI : Module A target :=
    RestrictScalars.moduleOrig R A (idealAssociatedGradedModule (Ideal.ofList xs) M)
  letI : Module R source := Module.restrictScalars R A source
  letI : Module R target := Module.restrictScalars R A target
  let φR : source →ₗ[R] target :=
    { toFun := quasiRegularSequenceAssociatedGradedMap M xs
      map_add' := by
        intro x y
        exact (quasiRegularSequenceAssociatedGradedMap M xs).map_add x y
      map_smul' := by
        intro r x
        -- Rewrite the restricted `R`-action back to the polynomial-ring action.
        rw [show r • x = ((algebraMap R A) r) • x by rfl]
        change
          (quasiRegularSequenceAssociatedGradedMap M xs) (((algebraMap R A) r) • x) =
            ((algebraMap R A) r) • (quasiRegularSequenceAssociatedGradedMap M xs x)
        exact
          (quasiRegularSequenceAssociatedGradedMap M xs).map_smul
            ((algebraMap R A) r) x }
  let eQuot := localized_ofList_smul_top_quotient_equiv (M := M) xs S
  let κ := localized_ofList_quotientRing_ringEquiv (R := R) xs S
  have hstage :
      ∀ n : ℕ,
        (idealAssociatedGradedStage (Ideal.ofList xs) M n).localized S =
          idealAssociatedGradedStage
            (Ideal.ofList (xs.map (algebraMap R (Localization S))))
            (LocalizedModule S M) n :=
    localized_idealAssociatedGradedStage_eq (M := M) xs S
  let eStage := localized_idealAssociatedGradedStage_linearEquiv (M := M) xs S
  -- Route correction: the source quotient owner `eQuot` is now normalized on quotient generators
  -- by `localized_ofList_smul_top_quotient_equiv_apply_mk`, so the remaining blocker is the
  -- tensor-source coefficient transport together with the quotient-piece/direct-sum target owner
  -- assembled from the new stage equivalences `eStage`.
  -- TODO(Lemma 10.69.4): descend `hstage` to quotient-piece and direct-sum target owners, combine
  -- them with `eQuot` and `κ` on denominator-1 monomial tensors, prove the resulting naturality
  -- square by `quasiRegularSequenceAssociatedGradedMap_tmul_monomial`, and then apply
  -- `IsLocalizedModule.map_injective_iff_localizedModuleMap_injective`.
  sorry

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.69.4: the localized kernel of the associated-graded map vanishes exactly
when the localized sequence is quasi-regular. -/
lemma localized_quasiRegularSequenceAssociatedGraded_kernel_subsingleton_iff
    (xs : List R) (S : Submonoid R) :
    Subsingleton (LocalizedModule S
      (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs))) ↔
      IsQuasiRegular (LocalizedModule S M)
        (xs.map (algebraMap R (Localization S))) := by
  let A : Type u := MvPolynomial (Fin xs.length) (R ⧸ Ideal.ofList xs)
  let source :=
    RestrictScalars R A
      (((M ⧸ ((Ideal.ofList xs) • ⊤ : Submodule R M)) ⊗[R ⧸ Ideal.ofList xs] A))
  let target :=
    RestrictScalars R A (idealAssociatedGradedModule (Ideal.ofList xs) M)
  letI : Module A source :=
    RestrictScalars.moduleOrig R A
      (((M ⧸ ((Ideal.ofList xs) • ⊤ : Submodule R M)) ⊗[R ⧸ Ideal.ofList xs] A))
  letI : Module A target :=
    RestrictScalars.moduleOrig R A (idealAssociatedGradedModule (Ideal.ofList xs) M)
  letI : Module R source := Module.restrictScalars R A source
  letI : Module R target := Module.restrictScalars R A target
  let φR : source →ₗ[R] target :=
    { toFun := quasiRegularSequenceAssociatedGradedMap M xs
      map_add' := by
        intro x y
        exact (quasiRegularSequenceAssociatedGradedMap M xs).map_add x y
      map_smul' := by
        intro r x
        -- Rewrite the restricted `R`-action back to the polynomial-ring action.
        rw [show r • x = ((algebraMap R A) r) • x by rfl]
        change
          (quasiRegularSequenceAssociatedGradedMap M xs) (((algebraMap R A) r) • x) =
            ((algebraMap R A) r) • (quasiRegularSequenceAssociatedGradedMap M xs x)
        exact
          (quasiRegularSequenceAssociatedGradedMap M xs).map_smul
            ((algebraMap R A) r) x }
  have hlocalized_injective :
      Function.Injective (LocalizedModule.map S φR) ↔
        Function.Injective
          (quasiRegularSequenceAssociatedGradedMap (LocalizedModule S M)
            (xs.map (algebraMap R (Localization S)))) := by
    -- Delegate the remaining transport-heavy injectivity bridge to the dedicated helper above so
    -- the kernel criterion below stays aligned with the textbook finite-kernel argument.
    simpa [A, source, target, φR] using
      localized_quasiRegularSequenceAssociatedGraded_restrictScalars_injective_iff
        (M := M) xs S
  have hkernel_localized :
      Function.Injective (LocalizedModule.map S φR) ↔
        Subsingleton (LocalizedModule S (LinearMap.ker φR)) := by
    let sourceModule : Module R source := Module.restrictScalars R A source
    let targetModule : Module R target := Module.restrictScalars R A target
    -- Reuse the generic localization criterion instead of reproving the kernel comparison here.
    simpa using
      (@localized_map_injective_iff_subsingleton_kernel
        R _ source inferInstance sourceModule target inferInstance targetModule φR S)
  -- Route correction: isolate the remaining localization work in the injectivity comparison for
  -- the associated-graded map, then combine the kernel criterion with the injectivity criterion.
  calc
    Subsingleton (LocalizedModule S
        (LinearMap.ker (quasiRegularSequenceAssociatedGradedMap M xs))) ↔
      Function.Injective
        (LocalizedModule.map S φR) := by
          simpa [φR, source, target] using hkernel_localized.symm
    _ ↔ Function.Injective
        (quasiRegularSequenceAssociatedGradedMap (LocalizedModule S M)
          (xs.map (algebraMap R (Localization S)))) :=
          hlocalized_injective
    _ ↔ IsQuasiRegular (LocalizedModule S M)
        (xs.map (algebraMap R (Localization S))) := by
          simpa using
            (isQuasiRegular_iff_injective
              (M := LocalizedModule S M)
              (rs := xs.map (algebraMap R (Localization S)))).symm

-- Proof sketch: let `K` be the kernel of the quasi-regular associated-graded map for `xs`.
-- Finite generation of `K` over the polynomial ring lets us choose finitely many homogeneous
-- generators. The hypothesis after localizing at `p` makes each generator vanish after inverting
-- some element outside `p`; multiplying those denominators gives `g ∉ p` killing all generators,
-- so the kernel vanishes after localizing away from `g`, which is exactly quasi-regularity there.
/-- Lemma 10.69.4: if the image of a sequence `xs` in `R_𝔭` is quasi-regular on the localized
module `M_𝔭`, then after inverting one element outside `p` the image of `xs` is already
quasi-regular on `M_g`. -/
theorem IsQuasiRegular.exists_away_of_atPrime (p : Ideal R) [p.IsPrime] {xs : List R}
    (hxs : IsQuasiRegular (LocalizedModule.AtPrime p M)
      (xs.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g : R, g ∉ p ∧
      IsQuasiRegular (LocalizedModule.Away g M)
        (xs.map (algebraMap R (Localization.Away g))) := by
  let φ := quasiRegularSequenceAssociatedGradedMap M xs
  let K := LinearMap.ker φ
  -- Route correction: the textbook proof is now reduced to one localization bridge for `φ`; the
  -- finite-kernel and denominator-clearing parts are handled directly below.
  have hK_atPrime : Subsingleton (LocalizedModule p.primeCompl K) := by
    -- Interpret the localized quasi-regularity hypothesis as vanishing of the localized kernel.
    simpa [K, φ, LocalizedModule.AtPrime, Localization.AtPrime] using
      (localized_quasiRegularSequenceAssociatedGraded_kernel_subsingleton_iff
        (M := M) xs p.primeCompl).2 hxs
  obtain ⟨g, hg, hK_away⟩ :
      ∃ g : R, g ∉ p ∧ Subsingleton (LocalizedModule (.powers g) K) := by
    let J : Ideal R := Ideal.ofList xs
    let A : Type u := MvPolynomial (Fin xs.length) (R ⧸ J)
    have hKfinite : Module.Finite A K := by
      simpa [K, φ, J, A] using quasiRegularSequenceAssociatedGraded_kernel_finite (M := M) xs
    let _ : Module.Finite A K := hKfinite
    let _ : Subsingleton (LocalizedModule p.primeCompl K) := hK_atPrime
    exact exists_subsingleton_away_of_finite_over_algebra (p := p) (A := A) (N := K)
  have hxsAway :
      IsQuasiRegular (LocalizedModule.Away g M)
        (xs.map (algebraMap R (Localization.Away g))) := by
    -- Convert the away-localized kernel vanishing back to quasi-regularity.
    simpa [K, φ, LocalizedModule.Away, Localization.Away] using
      (localized_quasiRegularSequenceAssociatedGraded_kernel_subsingleton_iff
        (M := M) xs (.powers g)).1 hK_away
  exact ⟨g, hg, hxsAway⟩

end RingTheory.Sequence

end

/-! ### Lemma_10_69_5 (from Chap10) -/
universe u v

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace IsQuasiRegular

/-- Lemma 10.69.5: if `rs` is an `M`-quasi-regular sequence, then after quotienting `R` by the
ideal generated by the first `i` terms and quotienting `M` by the corresponding submodule, the
remaining tail sequence is quasi-regular on the quotient module. -/
theorem tail_quotient {rs : List R} (hqr : IsQuasiRegular M rs) (i : ℕ) :
    IsQuasiRegular (M ⧸ (Ideal.ofList (rs.take i) • (⊤ : Submodule R M)))
      ((rs.drop i).map (Ideal.Quotient.mk (Ideal.ofList (rs.take i)))) := by
  -- This is the quotient-by-prefix stability statement for quasi-regular sequences.
  admit

end IsQuasiRegular

end RingTheory.Sequence

/-! ### Lemma_10_69_6 (from Chap10) -/
universe u v

open RingTheory
open Lean Elab Term Meta
open scoped BigOperators TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- 
Domain triage:
* primary domain: regular, weakly regular, and quasi-regular sequences in commutative algebra;
* sampled owner API:
  `RingTheory.Sequence.IsWeaklyRegular`,
  `RingTheory.Sequence.isWeaklyRegular_cons_iff'`,
  `RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal`,
  `RingTheory.Sequence.IsQuasiRegular.tail_quotient`;
* core/canonical owner abstraction: mathlib's `IsWeaklyRegular` / `IsRegular` on successive
  quotient modules;
* layer split: `IsQuasiRegular` is the source-facing associated-graded predicate from Definition
  `10.69.1`, while this file is a bridge from that source-facing notion to the owner regular-sequence
  API.
-/

-- Proof sketch: first dispose of the zero module, where weak regularity is automatic. Otherwise
-- argue by induction on the list `rs` using `isWeaklyRegular_cons_iff'`. For the head term, use
-- Krull's intersection theorem for the ideal generated by `rs` to choose the first nonvanishing
-- graded piece of a nonzero `x : M`; quasi-regularity forces multiplication by the head element to
-- stay nonzero in the next graded piece. Then specialize `IsQuasiRegular.tail_quotient` to the
-- first term and continue on the canonical quotient-by-the-head module.
namespace IsQuasiRegular

/-- Helper for Lemma 10.69.6: every sequence is weakly regular on a subsingleton module, because
every scalar-multiplication map is injective and all successive quotients remain subsingleton. -/
private theorem isWeaklyRegular_of_subsingleton
    {S : Type*} [CommRing S] {N : Type*} [AddCommGroup N] [Module S N] [Subsingleton N]
    (rs : List S) :
    IsWeaklyRegular N rs := by
  induction rs generalizing N with
  | nil =>
      -- The empty sequence is weakly regular by definition.
      simpa using (IsWeaklyRegular.nil (R := S) (M := N))
  | cons r rs ih =>
      -- On a subsingleton module every scalar action is injective, and the quotient stays
      -- subsingleton, so we recurse on the tail.
      have hr : IsSMulRegular N r := fun _ _ _ => Subsingleton.elim _ _
      exact IsWeaklyRegular.cons hr ih

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Helper for Lemma 10.69.6: if the head parameter is a unit, then quotienting by its image kills
the whole module. -/
private theorem quotSMulTop_subsingleton_of_isUnit
    {N : Type v} [AddCommGroup N] [Module R N] {r : R} (hr : IsUnit r) :
    Subsingleton (QuotSMulTop r N) := by
  -- A unit acts surjectively on `N`, so the submodule `r • ⊤` is already the whole module.
  rw [Submodule.Quotient.subsingleton_iff]
  refine top_unique ?_
  intro n hn
  rcases hr with ⟨u, rfl⟩
  rw [Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨(↑u⁻¹ : R) • n, by simp, ?_⟩
  simp [smul_smul]

/-- Helper for Lemma 10.69.6: Krull intersection chooses the first nonvanishing stage of a
nonzero element in a proper `J`-adic filtration. -/
private theorem exists_pow_smul_order_of_ne_zero
    {J : Ideal R} (hJ : J ≠ ⊤) {x : M} (hx : x ≠ 0) :
    ∃ n : ℕ, x ∈ J ^ n • (⊤ : Submodule R M) ∧ x ∉ J ^ (n + 1) • (⊤ : Submodule R M) := by
  classical
  have hx_not_mem_iInf : x ∉ ⨅ n : ℕ, J ^ n • (⊤ : Submodule R M) := by
    -- Krull intersection identifies the full intersection with `⊥`, so a nonzero element cannot
    -- lie in every `J`-power stage at once.
    intro hx_iInf
    have hbot :
        (⨅ n : ℕ, J ^ n • (⊤ : Submodule R M) : Submodule R M) = ⊥ :=
      Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := R) (M := M) (I := J) hJ
    have hx_bot : x ∈ (⊥ : Submodule R M) := by
      simpa [hbot] using hx_iInf
    exact hx (by simpa using hx_bot)
  have h_exists : ∃ n : ℕ, x ∉ J ^ (n + 1) • (⊤ : Submodule R M) := by
    -- Otherwise `x` would belong to every stage of the filtration, contradicting the previous
    -- paragraph.
    by_contra h_exists
    push Not at h_exists
    apply hx_not_mem_iInf
    rw [Submodule.mem_iInf]
    intro n
    cases n with
    | zero =>
        simp
    | succ k =>
        simpa using h_exists k
  refine ⟨Nat.find h_exists, ?_, Nat.find_spec h_exists⟩
  by_cases hfind : Nat.find h_exists = 0
  · -- The zeroth stage is the whole module.
    simpa [hfind]
  · -- Minimality of `Nat.find` forces membership in the preceding stage.
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hfind
    have hk_lt : k < Nat.find h_exists := by
      simpa [hk] using Nat.lt_succ_self k
    have hk_mem : ¬ x ∉ J ^ (k + 1) • (⊤ : Submodule R M) := by
      exact Nat.find_min h_exists hk_lt
    simpa [hk] using not_not.mp hk_mem

/-- Canonical strengthening behind Lemma 10.69.6: over a local Noetherian ring, a quasi-regular
sequence whose entries all lie in the maximal ideal is weakly regular on every finite module. -/
theorem isWeaklyRegular {rs : List R} (hqr : IsQuasiRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) :
    IsWeaklyRegular M rs := by
  classical
  by_cases hM : Subsingleton M
  · letI : Subsingleton M := hM
    -- In the zero-module case the regular-sequence conditions are vacuous at every stage.
    exact isWeaklyRegular_of_subsingleton (S := R) (N := M) rs
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    -- Route correction: the theorem is only sound with the maximal-ideal hypothesis carried
    -- through the induction. The remaining blocker is the graded-piece bridge turning injectivity
    -- of the source `X 0`-action into nonvanishing of `r • x` in the next associated-graded
    -- quotient; that bridge depends on private `10.69.0.1` transport lemmas and the induced
    -- polynomial-module structures on the tensor source.
    -- TODO(Lemma 10.69.6): finish the nontrivial case by combining
    -- `exists_pow_smul_order_of_ne_zero`, `IsQuasiRegular.tail_quotient`, the head-variable
    -- injectivity on the source tensor, and the public-to-internal associated-graded transport for
    -- the degree-`n` class of `x`.
    sorry

/-- Lemma 10.69.6: over a local Noetherian ring, a quasi-regular sequence contained in the maximal
ideal is a regular sequence on every nonzero finite module. This is the source-facing local upgrade
obtained by composing `isWeaklyRegular` with the owner theorem
`IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal`. -/
theorem isRegular_of_mem_maximalIdeal [Nontrivial M] {rs : List R} (hqr : IsQuasiRegular M rs)
    (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) :
    IsRegular M rs :=
  IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M hmem (hqr.isWeaklyRegular hmem)

end IsQuasiRegular

end RingTheory.Sequence

/-! ### Remark_10_69_7_Other_types_of_regular_sequences (from Chap10) -/
universe u

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-
Domain triage:
* primary domain: Koszul-, `H_1`-, and quasi-regular refinements of regular sequences in
  commutative algebra;
* sampled owner API:
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.IsKoszulRegularSequence`,
  `RingTheory.Sequence.IsH1RegularSequence`,
  `RingTheory.Sequence.IsH1RegularOn.isQuasiRegular`;
* core/canonical owner: the finite-family predicates
  `IsKoszulRegularSequence` and `IsH1RegularSequence`;
* layer split: this remark is a `bridge/view` file, so the owner predicates stay recalled from
  Chapter 15 and only the source-facing implication theorems remain local.
-/

/- Remark 10.69.7 (1): the canonical owner predicate for Koszul-regularity is
`RingTheory.Sequence.IsKoszulRegularSequence`, with the homology-vanishing formulation exposed by
the companion recall below. -/
recall IsKoszulRegularSequence

/- Companion specification recall for the canonical owner predicate
`RingTheory.Sequence.IsKoszulRegularSequence`. -/
recall isKoszulRegularSequence_iff

/- Remark 10.69.7 (2): the canonical owner predicate for `H_1`-regularity is
`RingTheory.Sequence.IsH1RegularSequence`, with the first-homology formulation exposed by the
companion recall below. -/
recall IsH1RegularSequence

/- Companion specification recall for the canonical owner predicate
`RingTheory.Sequence.IsH1RegularSequence`. -/
recall isH1RegularSequence_iff

/-- Remark 10.69.7 (3): every regular sequence is Koszul-regular. -/
theorem isKoszulRegular_of_isRegular {rs : List R} (hreg : IsRegular R rs) :
    IsKoszulRegularSequence rs.get := sorry

/- Remark 10.69.7 (4): the owner-level bridge from Koszul-regularity to `H_1`-regularity is
`RingTheory.Sequence.isH1RegularSequence_of_isKoszulRegularSequence`. -/
recall isH1RegularSequence_of_isKoszulRegularSequence

/-- Remark 10.69.7 (5): every `H_1`-regular sequence is quasi-regular. -/
theorem isQuasiRegular_of_isH1Regular {rs : List R}
    (hH1 : IsH1RegularSequence rs.get) :
    IsQuasiRegularSequence rs := sorry

end RingTheory.Sequence
