import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import stacks_proof.stacks_project.Chap10.Definition_10_69_1
import stacks_proof.stacks_project.Chap10.Lemma_10_69_4.Index
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory
open scoped TensorProduct

attribute [local instance] MvPolynomial.algebraMvPolynomial

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
  have hmk :
      (Submodule.localizedEquiv (p := S)
          (M' := idealAssociatedGradedStage (Ideal.ofList xs) M n)).symm
        (LocalizedModule.mkLinearMap S
          (idealAssociatedGradedStage (Ideal.ofList xs) M n) x) =
      (idealAssociatedGradedStage (Ideal.ofList xs) M n).toLocalized S x := by
    -- The inverse of the canonical submodule localization equivalence sends the denominator-`1`
    -- generator back to the corresponding numerator in the localized submodule.
    simpa [Submodule.localizedEquiv] using
      (IsLocalizedModule.linearEquiv_symm_apply
        (S := S)
        (f := (idealAssociatedGradedStage (Ideal.ofList xs) M n).toLocalized S)
        (g := LocalizedModule.mkLinearMap S
          (idealAssociatedGradedStage (Ideal.ofList xs) M n))
        x)
  -- After rewriting the stage equality, the resulting localized numerator is literally the
  -- ambient localization of `x`.
  calc
    ((localized_idealAssociatedGradedStage_linearEquiv (M := M) xs S n
        (LocalizedModule.mkLinearMap S (idealAssociatedGradedStage (Ideal.ofList xs) M n) x) :
          idealAssociatedGradedStage
            (Ideal.ofList (xs.map (algebraMap R (Localization S))))
            (LocalizedModule S M) n) : LocalizedModule S M) =
      (((idealAssociatedGradedStage (Ideal.ofList xs) M n).toLocalized S x :
          (idealAssociatedGradedStage (Ideal.ofList xs) M n).localized S) :
        LocalizedModule S M) := by
          rw [localized_idealAssociatedGradedStage_linearEquiv, LinearEquiv.trans_apply, hmk]
          simp only [LinearEquiv.coe_ofEq_apply]
    _ = LocalizedModule.mkLinearMap S M x := by
          rfl

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
/-- Helper for Chap10 Lemma 10 69 4: under the canonical equivalence between a localized
submodule and the localization of the submodule, localized nested submodules are carried to each
other. -/
lemma map_localizedEquiv_submoduleOf_eq
    {N : Submodule R M} {L : Submodule R M} (hLN : L ≤ N) (S : Submonoid R) :
    Submodule.map
        (Submodule.localizedEquiv S N : N.localized S →ₗ[Localization S] LocalizedModule S N)
        ((L.localized S).submoduleOf (N.localized S)) =
      (L.submoduleOf N).localized S := by
  -- Compare both localized submodules by writing their elements as fractions and using the
  -- canonical equivalence between the two localization models of `N`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases
      (Submodule.mem_localized' (Localization S) S (LocalizedModule.mkLinearMap S M) L y).mp hy
      with ⟨l, hl, s, hls⟩
    rw [Submodule.mem_localized']
    refine ⟨⟨l, hLN hl⟩, hl, s, ?_⟩
    rw [IsLocalizedModule.mk'_eq_iff]
    have hy_eq : (Submodule.toLocalized S N) ⟨l, hLN hl⟩ = (s : R) • y := by
      ext
      change (LocalizedModule.mkLinearMap S M) l = (s : R) • (y : LocalizedModule S M)
      exact IsLocalizedModule.mk'_eq_iff.mp hls
    calc
      (LocalizedModule.mkLinearMap S N) ⟨l, hLN hl⟩ =
          (Submodule.localizedEquiv S N) ((Submodule.toLocalized S N) ⟨l, hLN hl⟩) := by
        simpa [Submodule.localizedEquiv] using
          (IsLocalizedModule.linearEquiv_apply S (Submodule.toLocalized S N)
            (LocalizedModule.mkLinearMap S N) ⟨l, hLN hl⟩).symm
      _ = (s : R) • (Submodule.localizedEquiv S N) y := by
        rw [hy_eq]
        simpa [Submonoid.smul_def, algebraMap_smul] using
          map_smul (Submodule.localizedEquiv S N)
            (algebraMap R (Localization S) (s : R)) y
  · intro hx
    rw [Submodule.mem_localized'] at hx
    rcases hx with ⟨l, hl, s, hls⟩
    let y : N.localized S := IsLocalizedModule.mk' (Submodule.toLocalized S N) l s
    refine ⟨y, ?_, ?_⟩
    · change (y : LocalizedModule S M) ∈ L.localized S
      rw [Submodule.mem_localized']
      refine ⟨(l : M), hl, s, ?_⟩
      rw [IsLocalizedModule.mk'_eq_iff]
      have hy_eq : (Submodule.toLocalized S N) l = (s : R) • y := by
        dsimp [y]
        exact IsLocalizedModule.mk'_eq_iff.mp rfl
      simpa [Submodule.toLocalized, Submodule.toLocalized', Submodule.toLocalized₀,
        LocalizedModule.mkLinearMap_apply] using congrArg Subtype.val hy_eq
    · rw [← hls]
      rw [eq_comm, IsLocalizedModule.mk'_eq_iff]
      have hy_eq : (Submodule.toLocalized S N) l = (s : R) • y := by
        dsimp [y]
        exact IsLocalizedModule.mk'_eq_iff.mp rfl
      calc
        (LocalizedModule.mkLinearMap S N) l =
            (Submodule.localizedEquiv S N) ((Submodule.toLocalized S N) l) := by
          simpa [Submodule.localizedEquiv] using
            (IsLocalizedModule.linearEquiv_apply S (Submodule.toLocalized S N)
              (LocalizedModule.mkLinearMap S N) l).symm
        _ = (s : R) • (Submodule.localizedEquiv S N) y := by
          rw [hy_eq]
          simpa [Submonoid.smul_def, algebraMap_smul] using
            map_smul (Submodule.localizedEquiv S N)
              (algebraMap R (Localization S) (s : R)) y

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the quotient of localized nested submodules is the
localization of the original quotient. -/
noncomputable def localized_submoduleQuotientEquiv
    {N : Submodule R M} {L : Submodule R M} (hLN : L ≤ N) (S : Submonoid R) :
    (N.localized S ⧸ (L.localized S).submoduleOf (N.localized S)) ≃ₗ[Localization S]
      LocalizedModule S (N ⧸ L.submoduleOf N) :=
  -- First move the numerator model from a localized submodule to the localization of the
  -- numerator, then apply the canonical quotient-localization equivalence.
  (Submodule.Quotient.equiv ((L.localized S).submoduleOf (N.localized S))
    ((L.submoduleOf N).localized S) (Submodule.localizedEquiv S N)
    (map_localizedEquiv_submoduleOf_eq (M := M) hLN S)).trans
    (localizedQuotientEquiv S (L.submoduleOf N))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the inverse quotient-localization equivalence sends a
denominator-`1` quotient class to the quotient class of the localized numerator. -/
lemma localized_quotientEquiv_symm_apply_mk
    {F : Type*} [AddCommGroup F] [Module R F]
    (K : Submodule R F) (S : Submonoid R) (x : F) :
    (localizedQuotientEquiv S K).symm
        (LocalizedModule.mkLinearMap S (F ⧸ K) (Submodule.Quotient.mk x)) =
      (Submodule.Quotient.mk (LocalizedModule.mkLinearMap S F x) :
        LocalizedModule S F ⧸ K.localized S) := by
  -- Compute the inverse localized quotient map at a generator before any nested-submodule
  -- transports are introduced.
  simpa [localizedQuotientEquiv, Submodule.toLocalizedQuotient] using
    (IsLocalizedModule.linearEquiv_symm_apply
      (S := S)
      (f := K.toLocalizedQuotient S)
      (g := LocalizedModule.mkLinearMap S (F ⧸ K))
      (x := Submodule.Quotient.mk x))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the inverse localized quotient of nested submodules sends
a denominator-`1` quotient class to the quotient class of the localized numerator. -/
lemma localized_submoduleQuotientEquiv_symm_apply_mk
    {N : Submodule R M} {L : Submodule R M} (hLN : L ≤ N) (S : Submonoid R) (x : N) :
    (localized_submoduleQuotientEquiv (M := M) hLN S).symm
        (LocalizedModule.mkLinearMap S (N ⧸ L.submoduleOf N) (Submodule.Quotient.mk x)) =
      (Submodule.Quotient.mk
        ((Submodule.localizedEquiv S N).symm (LocalizedModule.mkLinearMap S N x)) :
        N.localized S ⧸ (L.localized S).submoduleOf (N.localized S)) := by
  -- First compute the quotient localization, then undo the quotient equivalence induced by the
  -- numerator localization equivalence.
  rw [localized_submoduleQuotientEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  rw [localized_quotientEquiv_symm_apply_mk]
  simp [Submodule.Quotient.equiv, Submodule.mapQ_apply]

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: equality transports numerator and denominator submodules to
the corresponding quotient. -/
lemma map_submoduleOf_of_eq
    {R' : Type*} [Ring R'] {X : Type*} [AddCommGroup X] [Module R' X]
    {A B C D : Submodule R' X} (hA : A = C) (hB : B = D) :
    Submodule.map (LinearEquiv.ofEq A C hA : A →ₗ[R'] C) (B.submoduleOf A) =
      D.submoduleOf C := by
  -- After replacing the equal submodules, the equality equivalence is the identity on carriers.
  subst C
  subst D
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    subst x
    simpa [LinearEquiv.ofEq] using hy
  · intro hx
    refine ⟨x, hx, ?_⟩
    exact Subtype.ext rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: each localized graded piece `S⁻¹(J^n M / J^(n + 1) M)` is
canonically identified with the corresponding graded piece of the localized module. -/
noncomputable def localized_idealAssociatedGradedPiece_linearEquiv
    (xs : List R) (S : Submonoid R) (n : ℕ) :
    LocalizedModule S (idealAssociatedGradedPiece (Ideal.ofList xs) M n) ≃ₗ[Localization S]
      idealAssociatedGradedPiece
        (Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (LocalizedModule S M) n := by
  let J : Ideal R := Ideal.ofList xs
  let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
  let N : Submodule R M := idealAssociatedGradedStage J M n
  let L : Submodule R M := idealAssociatedGradedStage J M (n + 1)
  let A : Submodule (Localization S) (LocalizedModule S M) :=
    idealAssociatedGradedStage JS (LocalizedModule S M) n
  let B : Submodule (Localization S) (LocalizedModule S M) :=
    idealAssociatedGradedStage JS (LocalizedModule S M) (n + 1)
  have hLN : L ≤ N := by
    -- Successive filtration stages are nested before localization.
    simpa [J, N, L, idealAssociatedGradedStage] using
      (Submodule.smul_mono_left
        (Ideal.pow_le_pow_right (show n ≤ n + 1 by omega)) :
          (J ^ (n + 1)) • (⊤ : Submodule R M) ≤ (J ^ n) • (⊤ : Submodule R M))
  have hNloc : N.localized S = A := by
    -- Normalize the localized numerator to the explicit stage in the localized module.
    simpa [J, JS, N, A] using localized_idealAssociatedGradedStage_eq (M := M) xs S n
  have hLloc : L.localized S = B := by
    -- Normalize the localized denominator to the next explicit stage in the localized module.
    simpa [J, JS, L, B] using localized_idealAssociatedGradedStage_eq (M := M) xs S (n + 1)
  let eNum : A ≃ₗ[Localization S] N.localized S :=
    LinearEquiv.ofEq A (N.localized S) hNloc.symm
  have hden :
      Submodule.map (eNum : A →ₗ[Localization S] N.localized S) (B.submoduleOf A) =
        (L.localized S).submoduleOf (N.localized S) := by
    -- The equality equivalence carries the localized denominator to the localized successor stage.
    simpa [eNum] using
      map_submoduleOf_of_eq (R' := Localization S) (X := LocalizedModule S M)
        (hA := hNloc.symm) (hB := hLloc.symm)
  let eQuot :
      (A ⧸ B.submoduleOf A) ≃ₗ[Localization S]
        (N.localized S ⧸ (L.localized S).submoduleOf (N.localized S)) :=
    Submodule.Quotient.equiv (B.submoduleOf A)
      ((L.localized S).submoduleOf (N.localized S)) eNum hden
  -- Quotient-localization identifies the localized textbook quotient with the explicit quotient
  -- inside the localized module.
  exact (localized_submoduleQuotientEquiv (M := M) hLN S).symm.trans eQuot.symm

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the localized graded-piece equivalence sends the
denominator-`1` class of a stage element to the corresponding class in the localized stage. -/
@[simp] lemma localized_idealAssociatedGradedPiece_linearEquiv_apply_mk
    (xs : List R) (S : Submonoid R) (n : ℕ)
    (x : idealAssociatedGradedStage (Ideal.ofList xs) M n) :
    localized_idealAssociatedGradedPiece_linearEquiv (M := M) xs S n
        (LocalizedModule.mkLinearMap S (idealAssociatedGradedPiece (Ideal.ofList xs) M n)
          (Submodule.Quotient.mk x)) =
      (Submodule.Quotient.mk
        (localized_idealAssociatedGradedStage_linearEquiv (M := M) xs S n
          (LocalizedModule.mkLinearMap S (idealAssociatedGradedStage (Ideal.ofList xs) M n) x)) :
        idealAssociatedGradedPiece
          (Ideal.ofList (xs.map (algebraMap R (Localization S))))
          (LocalizedModule S M) n) := by
  let J : Ideal R := Ideal.ofList xs
  let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
  let N : Submodule R M := idealAssociatedGradedStage J M n
  let L : Submodule R M := idealAssociatedGradedStage J M (n + 1)
  let A : Submodule (Localization S) (LocalizedModule S M) :=
    idealAssociatedGradedStage JS (LocalizedModule S M) n
  let B : Submodule (Localization S) (LocalizedModule S M) :=
    idealAssociatedGradedStage JS (LocalizedModule S M) (n + 1)
  have hLN : L ≤ N := by
    -- Successive filtration stages are nested, as in the owner definition of the piece
    -- equivalence.
    simpa [J, N, L, idealAssociatedGradedStage] using
      (Submodule.smul_mono_left
        (Ideal.pow_le_pow_right (show n ≤ n + 1 by omega)) :
          (J ^ (n + 1)) • (⊤ : Submodule R M) ≤ (J ^ n) • (⊤ : Submodule R M))
  have hNloc : N.localized S = A := by
    -- Normalize the localized numerator to the explicit localized stage.
    simpa [J, JS, N, A] using localized_idealAssociatedGradedStage_eq (M := M) xs S n
  have hLloc : L.localized S = B := by
    -- Normalize the localized denominator to the next explicit localized stage.
    simpa [J, JS, L, B] using localized_idealAssociatedGradedStage_eq (M := M) xs S (n + 1)
  let eNum : A ≃ₗ[Localization S] N.localized S :=
    LinearEquiv.ofEq A (N.localized S) hNloc.symm
  have hden :
      Submodule.map (eNum : A →ₗ[Localization S] N.localized S) (B.submoduleOf A) =
        (L.localized S).submoduleOf (N.localized S) := by
    -- The equality equivalence carries the localized denominator to the localized successor
    -- stage.
    simpa [eNum] using
      map_submoduleOf_of_eq (R' := Localization S) (X := LocalizedModule S M)
        (hA := hNloc.symm) (hB := hLloc.symm)
  let eQuot :
      (A ⧸ B.submoduleOf A) ≃ₗ[Localization S]
        (N.localized S ⧸ (L.localized S).submoduleOf (N.localized S)) :=
    Submodule.Quotient.equiv (B.submoduleOf A)
      ((L.localized S).submoduleOf (N.localized S)) eNum hden
  have hquot :
      (localized_submoduleQuotientEquiv (M := M) hLN S).symm
        (LocalizedModule.mkLinearMap S (N ⧸ L.submoduleOf N)
          (Submodule.Quotient.mk (x : N))) =
      (Submodule.Quotient.mk
        ((Submodule.localizedEquiv S N).symm (LocalizedModule.mkLinearMap S N (x : N))) :
        N.localized S ⧸ (L.localized S).submoduleOf (N.localized S)) := by
    -- Compute the generic quotient-localization equivalence on a denominator-`1` quotient class.
    exact localized_submoduleQuotientEquiv_symm_apply_mk (M := M) hLN S (x : N)
  -- The piece equivalence is the quotient-localization computation followed by the equality
  -- transport from localized stages to the explicit stages in the localized module.
  calc
    localized_idealAssociatedGradedPiece_linearEquiv (M := M) xs S n
        (LocalizedModule.mkLinearMap S (idealAssociatedGradedPiece (Ideal.ofList xs) M n)
          (Submodule.Quotient.mk x)) =
      eQuot.symm ((localized_submoduleQuotientEquiv (M := M) hLN S).symm
        (LocalizedModule.mkLinearMap S (N ⧸ L.submoduleOf N)
          (Submodule.Quotient.mk (x : N)))) := by
          rfl
    _ = eQuot.symm (Submodule.Quotient.mk
        ((Submodule.localizedEquiv S N).symm (LocalizedModule.mkLinearMap S N (x : N)))) := by
          rw [hquot]
    _ = Submodule.Quotient.mk
        (eNum.symm
          ((Submodule.localizedEquiv S N).symm (LocalizedModule.mkLinearMap S N (x : N)))) := by
          simp [eQuot, Submodule.Quotient.equiv, Submodule.mapQ_apply]
    _ = Submodule.Quotient.mk
        (localized_idealAssociatedGradedStage_linearEquiv (M := M) xs S n
          (LocalizedModule.mkLinearMap S (idealAssociatedGradedStage (Ideal.ofList xs) M n)
            x)) := by
          rfl

set_option maxHeartbeats 800000 in
omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the localized associated graded module transports degreewise
along the piecewise localization equivalences after localizing the direct sum owner. -/
noncomputable def localized_idealAssociatedGradedModule_linearEquiv
    (xs : List R) (S : Submonoid R) :
    LocalizedModule S (idealAssociatedGradedModule (Ideal.ofList xs) M) ≃ₗ[Localization S]
      idealAssociatedGradedModule
        (Ideal.ofList (xs.map (algebraMap R (Localization S))))
        (LocalizedModule S M) := by
  let gPiece :
      (n : ℕ) →
        idealAssociatedGradedPiece (Ideal.ofList xs) M n →ₗ[R]
          idealAssociatedGradedPiece
            (Ideal.ofList (xs.map (algebraMap R (Localization S))))
            (LocalizedModule S M) n :=
    fun n ↦
      (LinearMap.restrictScalars R
        ((localized_idealAssociatedGradedPiece_linearEquiv (M := M) xs S n).toLinearMap)).comp
        (LocalizedModule.mkLinearMap S (idealAssociatedGradedPiece (Ideal.ofList xs) M n))
  let gTgt :
      idealAssociatedGradedModule (Ideal.ofList xs) M →ₗ[R]
        idealAssociatedGradedModule
          (Ideal.ofList (xs.map (algebraMap R (Localization S))))
          (LocalizedModule S M) :=
    DirectSum.lmap gPiece
  have hgTgt : IsLocalizedModule S gTgt := by
    -- Route correction: use the owner-level direct-sum base-change theorem instead of building a
    -- bespoke inverse on the localized direct sum.
    rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
    apply IsBaseChange.directSum
    intro n
    rw [← isLocalizedModule_iff_isBaseChange S (Localization S)]
    let e :
        LocalizedModule S (idealAssociatedGradedPiece (Ideal.ofList xs) M n) ≃ₗ[R]
          idealAssociatedGradedPiece
            (Ideal.ofList (xs.map (algebraMap R (Localization S))))
            (LocalizedModule S M) n :=
      LinearEquiv.restrictScalars R
        (localized_idealAssociatedGradedPiece_linearEquiv (M := M) xs S n)
    change IsLocalizedModule S
      (e.toLinearMap.comp
        (LocalizedModule.mkLinearMap S (idealAssociatedGradedPiece (Ideal.ofList xs) M n)))
    infer_instance
  have hbc : IsBaseChange (Localization S) gTgt := by
    rw [← isLocalizedModule_iff_isBaseChange S (Localization S)]
    exact hgTgt
  -- First identify the localized direct sum with its tensor-product model, then use the direct-sum
  -- base-change equivalence determined by the degreewise localized pieces.
  exact
    (LocalizedModule.equivTensorProduct S
      (idealAssociatedGradedModule (Ideal.ofList xs) M)).trans hbc.equiv

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the localized associated graded transport sends a
denominator-`1` homogeneous generator to the corresponding localized graded piece. -/
@[simp] lemma localized_idealAssociatedGradedModule_linearEquiv_apply_mk_lof
    (xs : List R) (S : Submonoid R) (n : ℕ)
    (z : idealAssociatedGradedPiece (Ideal.ofList xs) M n) :
    localized_idealAssociatedGradedModule_linearEquiv (M := M) xs S
        (LocalizedModule.mkLinearMap S (idealAssociatedGradedModule (Ideal.ofList xs) M)
          (DirectSum.lof R ℕ (idealAssociatedGradedPiece (Ideal.ofList xs) M) n z)) =
      DirectSum.lof (Localization S) ℕ
        (idealAssociatedGradedPiece
          (Ideal.ofList (xs.map (algebraMap R (Localization S))))
          (LocalizedModule S M)) n
        (localized_idealAssociatedGradedPiece_linearEquiv (M := M) xs S n
          (LocalizedModule.mkLinearMap S (idealAssociatedGradedPiece (Ideal.ofList xs) M n) z)) := by
  -- Unfold the owner-level localization transport once so the denominator-`1` generator is
  -- visible inside the tensor-product model.
  rw [localized_idealAssociatedGradedModule_linearEquiv, LinearEquiv.trans_apply]
  -- The localized direct-sum generator becomes `1 ⊗ lof`, and the base-change equivalence then
  -- evaluates by the direct-sum localization map degreewise.
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.equivTensorProduct_apply_mk,
    IsBaseChange.equiv_tmul]
  -- Normalize the denominator-`1` scalar and read off the degreewise image of `DirectSum.lmap`.
  simp only [DirectSum.lmap_lof, LinearMap.comp_apply]
  simp [Localization.mk_one]
  rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: every source tensor is a finite sum of monomial simple
tensors with quotient-module coefficients. -/
lemma tensor_monomial_expansion
    {A : Type*} [CommRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    (xs : List A)
    (z : (P ⧸ ((Ideal.ofList xs) • (⊤ : Submodule A P))) ⊗[A ⧸ Ideal.ofList xs]
      MvPolynomial (Fin xs.length) (A ⧸ Ideal.ofList xs)) :
    ∃ coeffs : (Fin xs.length →₀ ℕ) →₀ (P ⧸ ((Ideal.ofList xs) • (⊤ : Submodule A P))),
      z =
        coeffs.sum fun e q ↦
          (q ⊗ₜ[A ⧸ Ideal.ofList xs]
            MvPolynomial.monomial e (1 : A ⧸ Ideal.ofList xs)) := by
  let comm :=
    TensorProduct.comm (A ⧸ Ideal.ofList xs)
      (P ⧸ ((Ideal.ofList xs) • (⊤ : Submodule A P)))
      (MvPolynomial (Fin xs.length) (A ⧸ Ideal.ofList xs))
  let scalar :=
    MvPolynomial.scalarRTensor
      (R := A ⧸ Ideal.ofList xs)
      (σ := Fin xs.length)
      (N := P ⧸ ((Ideal.ofList xs) • (⊤ : Submodule A P)))
  let coeffs :
      (Fin xs.length →₀ ℕ) →₀ (P ⧸ ((Ideal.ofList xs) • (⊤ : Submodule A P))) :=
    scalar (comm z)
  -- Pass to the commuted tensor product, where `scalarRTensor` identifies the source with a
  -- finitely supported coefficient family.
  refine ⟨coeffs, ?_⟩
  apply comm.injective
  calc
    comm z = scalar.symm coeffs := by
      simp [coeffs]
    _ = scalar.symm (coeffs.sum fun e q ↦ Finsupp.single e q) := by
      simp
    _ = coeffs.sum fun e q ↦ scalar.symm (Finsupp.single e q) := by
      simp [Finsupp.sum]
    _ = coeffs.sum fun e q ↦
          (MvPolynomial.monomial e (1 : A ⧸ Ideal.ofList xs)) ⊗ₜ[A ⧸ Ideal.ofList xs] q := by
      refine Finsupp.sum_congr ?_
      intro e q
      rw [MvPolynomial.scalarRTensor_symm_apply_single]
    _ = comm
          (coeffs.sum fun e q ↦
            (q ⊗ₜ[A ⧸ Ideal.ofList xs]
              MvPolynomial.monomial e (1 : A ⧸ Ideal.ofList xs))) := by
      simp only [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl ?_
      intro e he
      rw [TensorProduct.comm_tmul]

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the monomial weight attached to an exponent vector lies in
the matching power of `Ideal.ofList xs`. -/
lemma ofList_monomial_weight_mem_pow
    {A : Type*} [CommRing A] (xs : List A) (e : Fin xs.length →₀ ℕ) :
    (∏ i : Fin xs.length, xs.get i ^ e i) ∈ (Ideal.ofList xs) ^ e.degree := by
  -- Each factor already lies in the corresponding ideal power, so the full product lands in the
  -- total-degree power after normalizing the product of powers.
  have hprod :
      (∏ i : Fin xs.length, xs.get i ^ e i) ∈
        ∏ i : Fin xs.length, (Ideal.ofList xs) ^ e i := by
    refine Ideal.prod_mem_prod ?_
    intro i hi
    exact Ideal.pow_mem_pow
      (Ideal.subset_span (by simpa using List.getElem_mem xs i))
      (e i)
  simpa [Finsupp.degree_eq_sum, Finset.prod_pow_eq_pow_sum] using hprod

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: a homogeneous weighted monomial term of total degree `n`
lies in the `n`th filtration stage. -/
lemma ofList_monomial_weight_smul_mem_of_degree
    {A : Type*} [CommRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    (xs : List A) (n : ℕ) (m : P) (e : Fin xs.length →₀ ℕ) (hdeg : e.degree = n) :
    (∏ i : Fin xs.length, xs.get i ^ e i) • m ∈
      idealAssociatedGradedStage (Ideal.ofList xs) P n := by
  -- Rewrite the stage as `J ^ n • ⊤` and combine monomial-weight membership with the trivial
  -- membership of `m` in the top submodule.
  simpa [idealAssociatedGradedStage, hdeg] using
    (Submodule.smul_mem_smul
      (ofList_monomial_weight_mem_pow xs e)
      (by simp : m ∈ (⊤ : Submodule A P)))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: reinserting the degree-`n` component of a monomial image
keeps the same image exactly in degree `n`. -/
lemma quasiRegularSequenceAssociatedGradedMap_tmul_monomial_eq_lof
    {A : Type*} [CommRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    {xs : List A} (m : P) (e : Fin xs.length →₀ ℕ) :
    let J : Ideal A := Ideal.ofList xs
    quasiRegularSequenceAssociatedGradedMap P xs
      (((Submodule.Quotient.mk m : P ⧸ (J • (⊤ : Submodule A P))) ⊗ₜ[A ⧸ J]
        MvPolynomial.monomial e (1 : A ⧸ J))) =
      DirectSum.lof (A ⧸ J) ℕ (idealAssociatedGradedPiece J P) e.degree
        (Submodule.Quotient.mk
          (⟨(∏ i : Fin xs.length, xs.get i ^ e i) • m,
            ofList_monomial_weight_smul_mem_of_degree xs e.degree m e rfl⟩ :
            idealAssociatedGradedStage J P e.degree)) := by
  let z := quasiRegularAssociatedGradedInternalMonomialClass xs m e
  -- Reuse the public owner computations from `10.69.0.1` instead of rebuilding the transport
  -- chain locally.
  dsimp [quasiRegularSequenceAssociatedGradedMap]
  have hcomm :=
    quasiRegularSequenceAssociatedGradedSourceComm_tmul P xs m e
  have haux :=
    quasiRegularSequenceAssociatedGradedMapAux_tmul_monomial P xs m e
  have hlof := quasiRegularAssociatedGradedAddEquiv_symm_lof P xs e.degree z
  have hpiece :=
    quasiRegularAssociatedGradedInternalPieceEquiv_monomialClass P xs m e
  -- Each owner-level rewrite now lands exactly on the textbook degree-`e.degree` class.
  rw [hcomm, haux, hlof, hpiece]
  rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: after transporting monomial exponents across
`List.length_map`, the localized monomial weight acts on a denominator-`1` numerator as the
localization of the original source monomial weight. -/
lemma localizedOfListMonomialWeight_smul_mk
    (xs : List R) (S : Submonoid R) (e : Fin xs.length →₀ ℕ) (m : M) :
    ((∏ j : Fin (xs.map (algebraMap R (Localization S))).length,
          (xs.map (algebraMap R (Localization S))).get j ^
            (e.mapDomain
              (Fin.cast (List.length_map (as := xs) (algebraMap R (Localization S))).symm)) j) •
        LocalizedModule.mkLinearMap S M m : LocalizedModule S M) =
      LocalizedModule.mkLinearMap S M ((∏ i : Fin xs.length, xs.get i ^ e i) • m) := by
  have hprod :
      (∏ j : Fin (xs.map (algebraMap R (Localization S))).length,
          (xs.map (algebraMap R (Localization S))).get j ^
            (e.mapDomain
              (Fin.cast (List.length_map (as := xs) (algebraMap R (Localization S))).symm)) j) =
        ∏ i : Fin xs.length, (algebraMap R (Localization S) (xs.get i)) ^ e i := by
    let ee : Fin xs.length ≃ Fin (xs.map (algebraMap R (Localization S))).length :=
      finCongr (List.length_map (as := xs) (algebraMap R (Localization S))).symm
    -- Reindex the localized product along the canonical equality of lengths, removing the only
    -- transport from the monomial weight comparison.
    symm
    refine Fintype.prod_equiv ee
      (fun i : Fin xs.length => (algebraMap R (Localization S) (xs.get i)) ^ e i)
      (fun j : Fin (xs.map (algebraMap R (Localization S))).length =>
        (xs.map (algebraMap R (Localization S))).get j ^
          (e.mapDomain
            (Fin.cast (List.length_map (as := xs) (algebraMap R (Localization S))).symm)) j) ?_
    intro i
    dsimp [ee]
    rw [Finsupp.mapDomain_apply]
    · simp
    · exact Fin.cast_injective _
  let a : R := ∏ i : Fin xs.length, xs.get i ^ e i
  have hmap :
      (algebraMap R (Localization S)) a =
        ∏ i : Fin xs.length, (algebraMap R (Localization S) (xs.get i)) ^ e i := by
    -- The coefficient of the localized monomial is the image of the source coefficient.
    simp [a]
  calc
    ((∏ j : Fin (xs.map (algebraMap R (Localization S))).length,
          (xs.map (algebraMap R (Localization S))).get j ^
            (e.mapDomain
              (Fin.cast (List.length_map (as := xs) (algebraMap R (Localization S))).symm)) j) •
        LocalizedModule.mkLinearMap S M m : LocalizedModule S M) =
      (a • LocalizedModule.mkLinearMap S M m : LocalizedModule S M) := by
        rw [hprod, ← hmap]
        simpa [algebraMap_smul]
    _ = LocalizedModule.mkLinearMap S M (a • m) := by
        exact (map_smul (LocalizedModule.mkLinearMap S M) a m).symm
    _ = LocalizedModule.mkLinearMap S M ((∏ i : Fin xs.length, xs.get i ^ e i) • m) := by
        rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: precomposing a linear map with a linear equivalence does
not change whether the linear map is injective. -/
lemma injective_comp_linearEquiv_iff
    {A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
    [Module R A] [Module R B] [Module R C]
    (e : A ≃ₗ[R] B) (f : B →ₗ[R] C) :
    Function.Injective (f.comp e.toLinearMap) ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    -- Pull the equality back to the source of the equivalence and use injectivity there.
    have hpull :
        f.comp e.toLinearMap (e.symm x) = f.comp e.toLinearMap (e.symm y) := by
      simpa using hxy
    simpa using h hpull
  · intro h x y hxy
    -- Push the equality through `f`, then cancel the equivalence.
    exact e.injective (h hxy)

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the localized quotient target has the scalar tower from
`R ⧸ Ideal.ofList xs` through the localized quotient ring. -/
lemma localizedOfListQuotientTarget_algebraScalarTower
    (xs : List R) (S : Submonoid R) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    let instQs : Module Qs T := localizedOfListQuotientTargetModule (M := M) xs S
    let instQ : Module Q T := localizedOfListQuotientTargetSourceModule (M := M) xs S
    letI : SMul Qs T := instQs.toSMul
    letI : SMul Q T := instQ.toSMul
    IsScalarTower Q Qs T := by
  intro J JS Q Qs T
  letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
  let instQs : Module Qs T := localizedOfListQuotientTargetModule (M := M) xs S
  let instQ : Module Q T := localizedOfListQuotientTargetSourceModule (M := M) xs S
  letI : SMul Qs T := instQs.toSMul
  letI : MulAction Qs T := instQs.toDistribMulAction.toMulAction
  letI : DistribMulAction Qs T := instQs.toDistribMulAction
  letI : Module Qs T := instQs
  letI : SMul Q T := instQ.toSMul
  letI : MulAction Q T := instQ.toDistribMulAction.toMulAction
  letI : DistribMulAction Q T := instQ.toDistribMulAction
  letI : Module Q T := instQ
  -- The restricted `Q`-action was defined by `Module.compHom`, so the scalar tower law is
  -- exactly the defining action of `algebraMap Q Qs`.
  refine IsScalarTower.of_algebraMap_smul fun q x ↦ ?_
  rfl

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the source tensor localization map is the tensor product
of the quotient map and the renamed polynomial map, followed by base change from
`R ⧸ Ideal.ofList xs` to the localized quotient ring. -/
noncomputable def localizedOfListSourceTensorMap
    (xs : List R) (S : Submonoid R) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
    let Pt : Type u :=
      MvPolynomial (Fin (xs.map (algebraMap R (Localization S))).length) Qs
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    let instQs : Module Qs T := localizedOfListQuotientTargetModule (M := M) xs S
    let instQ : Module Q T := localizedOfListQuotientTargetSourceModule (M := M) xs S
    letI : SMul Qs T := instQs.toSMul
    letI : MulAction Qs T := instQs.toDistribMulAction.toMulAction
    letI : DistribMulAction Qs T := instQs.toDistribMulAction
    letI : Module Qs T := instQs
    letI : SMul Q T := instQ.toSMul
    letI : MulAction Q T := instQ.toDistribMulAction.toMulAction
    letI : DistribMulAction Q T := instQ.toDistribMulAction
    letI : Module Q T := instQ
    letI : IsScalarTower Q Qs T :=
      localizedOfListQuotientTarget_algebraScalarTower (M := M) xs S
    (M ⧸ (J • ⊤ : Submodule R M)) ⊗[Q] MvPolynomial (Fin xs.length) Q →ₗ[Q]
      T ⊗[Qs] Pt :=
  let J : Ideal R := Ideal.ofList xs
  let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
  let Q : Type u := R ⧸ J
  let Qs : Type u := (Localization S) ⧸ JS
  let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
  let Pt : Type u :=
    MvPolynomial (Fin (xs.map (algebraMap R (Localization S))).length) Qs
  letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
  let instQs : Module Qs T := localizedOfListQuotientTargetModule (M := M) xs S
  let instQ : Module Q T := localizedOfListQuotientTargetSourceModule (M := M) xs S
  letI : SMul Qs T := instQs.toSMul
  letI : MulAction Qs T := instQs.toDistribMulAction.toMulAction
  letI : DistribMulAction Qs T := instQs.toDistribMulAction
  letI : Module Qs T := instQs
  letI : SMul Q T := instQ.toSMul
  letI : MulAction Q T := instQ.toDistribMulAction.toMulAction
  letI : DistribMulAction Q T := instQ.toDistribMulAction
  letI : Module Q T := instQ
  letI : IsScalarTower Q Qs T :=
    localizedOfListQuotientTarget_algebraScalarTower (M := M) xs S
  letI : Module Qs Pt := Algebra.toModule
  letI : Module Q Pt := Algebra.toModule
  letI : IsScalarTower Q Qs Pt := inferInstance
  (tensorProductBaseChangeMap (R := Q) (A := Qs) (X := T) (Y := Pt)).comp
    (TensorProduct.map (localizedOfListQuotientMap (M := M) xs S)
      (localizedOfListRenamedPolynomialMap (R := R) xs S))

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 69 4: the source tensor map sends a denominator-one quotient
class tensored with a source monomial to the corresponding localized quotient class and
transported monomial. -/
lemma localizedOfListSourceTensorMap_tmul_monomial
    (xs : List R) (S : Submonoid R) (m : M) (e : Fin xs.length →₀ ℕ) :
    let J : Ideal R := Ideal.ofList xs
    let JS : Ideal (Localization S) := Ideal.ofList (xs.map (algebraMap R (Localization S)))
    let Q : Type u := R ⧸ J
    let Qs : Type u := (Localization S) ⧸ JS
    let T : Type (max u v) := localizedOfListQuotientTarget (M := M) xs S
    letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
    let instQs : Module Qs T := localizedOfListQuotientTargetModule (M := M) xs S
    let instQ : Module Q T := localizedOfListQuotientTargetSourceModule (M := M) xs S
    letI : SMul Qs T := instQs.toSMul
    letI : MulAction Qs T := instQs.toDistribMulAction.toMulAction
    letI : DistribMulAction Qs T := instQs.toDistribMulAction
    letI : Module Qs T := instQs
    letI : SMul Q T := instQ.toSMul
    letI : MulAction Q T := instQ.toDistribMulAction.toMulAction
    letI : DistribMulAction Q T := instQ.toDistribMulAction
    letI : Module Q T := instQ
    letI : IsScalarTower Q Qs T :=
      localizedOfListQuotientTarget_algebraScalarTower (M := M) xs S
    localizedOfListSourceTensorMap (M := M) xs S
        ((Submodule.Quotient.mk m :
            M ⧸ (J • ⊤ : Submodule R M)) ⊗ₜ[Q]
          MvPolynomial.monomial e (1 : Q)) =
      (Submodule.Quotient.mk (LocalizedModule.mkLinearMap S M m) : T) ⊗ₜ[Qs]
        MvPolynomial.monomial
          (e.mapDomain
            (Fin.cast (List.length_map (as := xs) (algebraMap R (Localization S))).symm))
          (1 : Qs) := by
  intro J JS Q Qs T
  let Pt : Type u :=
    MvPolynomial (Fin (xs.map (algebraMap R (Localization S))).length) Qs
  letI : Algebra Q Qs := localizedOfListQuotientAlgebra (R := R) xs S
  let instQs : Module Qs T := localizedOfListQuotientTargetModule (M := M) xs S
  let instQ : Module Q T := localizedOfListQuotientTargetSourceModule (M := M) xs S
  letI : SMul Qs T := instQs.toSMul
  letI : MulAction Qs T := instQs.toDistribMulAction.toMulAction
  letI : DistribMulAction Qs T := instQs.toDistribMulAction
  letI : Module Qs T := instQs
  letI : SMul Q T := instQ.toSMul
  letI : MulAction Q T := instQ.toDistribMulAction.toMulAction
  letI : DistribMulAction Q T := instQ.toDistribMulAction
  letI : Module Q T := instQ
  letI : IsScalarTower Q Qs T :=
    localizedOfListQuotientTarget_algebraScalarTower (M := M) xs S
  letI : Module Qs Pt := Algebra.toModule
  letI : Module Q Pt := Algebra.toModule
  letI : IsScalarTower Q Qs Pt := inferInstance
  -- First apply the two factor-localization computations, then the explicit base-change map.
  rw [localizedOfListSourceTensorMap, LinearMap.comp_apply, TensorProduct.map_tmul,
    localizedOfListQuotientMap_mk, localizedOfListRenamedPolynomialMap_monomial,
    tensorProductBaseChangeMap_tmul]

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
  -- Route correction: the target-side associated-graded localization is proved above. The
  -- remaining blocker is the source tensor owner
  -- `S⁻¹((M/JM) ⊗[R/J] (R/J)[X]) ≃
  -- (M_S/J_SM_S) ⊗[(S⁻¹R)/J_S] ((S⁻¹R)/J_S)[X]` with its denominator-`1` monomial formula.
  -- The monomial-weight transport is now isolated in `localizedOfListMonomialWeight_smul_mk`;
  -- what remains is the owner-level `R ⧸ Ideal.ofList xs`-linear source tensor localization
  -- equivalence, including the polynomial variable-length cast across `List.length_map`.
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
@[stacks 061Q]
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
