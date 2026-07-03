import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import StacksProject_2024.Chap10.Definition_10_69_1

-- Declarations for this item will be appended below by the statement pipeline.

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
