import StacksProject_2024.stacks_project.Chap10.Lemma_10_90_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Coherent R R]

omit [Module.Coherent R R] in
private theorem coherent_of_equiv {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) [hM : Module.Coherent R M] :
    Module.Coherent R N where
  toFinite := Module.Finite.of_surjective e.toLinearMap e.surjective
  finitePresentation_submodule P hP := by
    let eP := (P.comap e.toLinearMap).equivMapOfInjective e.toLinearMap e.injective
    have hmap : (P.comap e.toLinearMap).map e.toLinearMap = P :=
      Submodule.map_comap_eq_of_surjective e.surjective P
    letI : Module.Finite R ((P.comap e.toLinearMap).map e.toLinearMap) := by
      rw [hmap]
      exact hP
    letI : Module.Finite R (P.comap e.toLinearMap) := Module.Finite.equiv eP.symm
    letI : Module.FinitePresentation R (P.comap e.toLinearMap) :=
      hM.finitePresentation_submodule (P.comap e.toLinearMap) inferInstance
    exact Module.FinitePresentation.of_equiv
      (eP.trans (LinearEquiv.ofEq _ _ hmap))

private theorem coherent_fin_zero : Module.Coherent R (Fin 0 → R) where
  toFinite := inferInstance
  finitePresentation_submodule P _ := by
    have hP : P = ⊤ := Subsingleton.elim _ _
    subst hP
    exact Module.FinitePresentation.of_equiv
      (Submodule.topEquiv : (⊤ : Submodule R (Fin 0 → R)) ≃ₗ[R] (Fin 0 → R)).symm

private theorem coherent_prod_left {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Coherent R N] :
    Module.Coherent R (R × N) where
  toFinite := inferInstance
  finitePresentation_submodule P hP := by
    let sndP : P →ₗ[R] N := (LinearMap.snd R R N).comp P.subtype
    let fstKer : LinearMap.ker sndP →ₗ[R] R :=
      (LinearMap.fst R R N).comp (P.subtype.comp (LinearMap.ker sndP).subtype)
    letI : Module.Finite R (LinearMap.range sndP) := Module.Finite.of_fg (Submodule.fg_range sndP)
    letI : Module.Coherent R (LinearMap.range sndP) := inferInstance
    have hExact : Function.Exact (LinearMap.ker sndP).subtype sndP.rangeRestrict := by
      rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
    letI : Module.Finite R (LinearMap.ker sndP) :=
      Module.Finite.of_fg <|
        by
          simpa [LinearMap.ker_rangeRestrict] using
            (Module.FinitePresentation.fg_ker sndP.rangeRestrict sndP.surjective_rangeRestrict)
    have hfstKer : Function.Injective fstKer := by
      intro x y hxy
      apply Subtype.ext
      apply P.subtype_injective
      ext
      · simpa [fstKer] using hxy
      ·
        have hx0' : (LinearMap.snd R R N) (P.subtype x.1) = 0 := by
          change sndP x.1 = 0
          exact x.2
        have hy0' : (LinearMap.snd R R N) (P.subtype y.1) = 0 := by
          change sndP y.1 = 0
          exact y.2
        simpa using hx0'.trans hy0'.symm
    let eKer := LinearEquiv.ofInjective fstKer hfstKer
    letI : Module.Finite R (LinearMap.range fstKer) :=
      Module.Finite.of_fg (Submodule.fg_range fstKer)
    letI : Module.Coherent R (LinearMap.range fstKer) := inferInstance
    letI : Module.FinitePresentation R (LinearMap.ker sndP) :=
      by
        letI : Module.FinitePresentation R (LinearMap.range fstKer) := inferInstance
        let eKer' : LinearMap.range fstKer ≃ₗ[R] LinearMap.ker sndP := eKer.symm
        let f : LinearMap.range fstKer →ₗ[R] LinearMap.ker sndP := eKer'.toLinearMap
        have hf : Function.Surjective f := eKer'.surjective
        have hker : LinearMap.ker f = ⊥ := by
          rw [show f = eKer'.toLinearMap by rfl, LinearEquiv.ker]
        show Module.FinitePresentation R (LinearMap.ker sndP)
        exact @Module.finitePresentation_of_surjective R (LinearMap.range fstKer)
          (LinearMap.ker sndP) _ _ _ _ _ inferInstance f hf <| by
          show (LinearMap.ker f).FG
          simpa [hker] using (Submodule.fg_bot : (⊥ : Submodule R (LinearMap.range fstKer)).FG)
    letI : Module.FinitePresentation R (LinearMap.ker sndP.rangeRestrict) := by
      rw [LinearMap.ker_rangeRestrict]
      infer_instance
    exact Module.finitePresentation_of_ker sndP.rangeRestrict sndP.surjective_rangeRestrict

private theorem coherent_fin : ∀ n : ℕ, Module.Coherent R (Fin n → R)
  | 0 => by
      exact coherent_fin_zero
  | n + 1 => by
      letI : Module.Coherent R (Fin n → R) := coherent_fin n
      letI : Module.Coherent R (R × (Fin n → R)) := coherent_prod_left
      let e₁ : (Fin (n + 1) → R) ≃ₗ[R] Option (Fin n) → R :=
        LinearEquiv.piCongrLeft R (fun _ : Option (Fin n) ↦ R) (finSuccEquiv n)
      let e₂ : (Option (Fin n) → R) ≃ₗ[R] R × (Fin n → R) :=
        LinearEquiv.piOptionEquivProd R
      exact coherent_of_equiv (e₁ ≪≫ₗ e₂).symm

private theorem coherent_finite_free {ι : Type*} [Finite ι] :
    Module.Coherent R (ι → R) := by
  classical
  cases nonempty_fintype ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  letI : Module.Coherent R (Fin (Fintype.card ι) → R) := coherent_fin (Fintype.card ι)
  exact coherent_of_equiv
    (LinearEquiv.piCongrLeft R (fun _ : Fin (Fintype.card ι) ↦ R) e).symm

-- Proof sketch: one direction is Lemma `10.90.3`, which makes every coherent module finitely
-- presented. For the converse, choose a finite presentation of `M` as a cokernel of a map
-- `R^m → R^n`; the free modules `R^m` and `R^n` are coherent because `R` is coherent, and then
-- Lemma `10.90.3` shows the cokernel is coherent.
/-- Lemma 10.90.4: over a coherent ring, an `R`-module is coherent if and only if it is finitely
presented. -/
lemma module_coherent_iff_finitePresentation :
    Module.Coherent R M ↔ Module.FinitePresentation R M := by
  constructor
  · intro
    infer_instance
  · intro hM
    letI : Module.FinitePresentation R M := hM
    obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin R M
    letI : Module.Finite R K := Module.Finite.of_fg hK
    letI : Module.Coherent R (Fin n → R) := coherent_finite_free
    letI : Module.Coherent R K := inferInstance
    letI : Module.Coherent R ((Fin n → R) ⧸ K.subtype.range) :=
      cokernel_coherent_of_coherent K.subtype
    letI : Module.Coherent R ((Fin n → R) ⧸ K) :=
      coherent_of_equiv (Submodule.quotEquivOfEq K.subtype.range K (Submodule.range_subtype K))
    exact coherent_of_equiv e.symm

end
