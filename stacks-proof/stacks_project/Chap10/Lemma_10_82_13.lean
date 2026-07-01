import Mathlib
import stacks_project.Chap10.Definition_10_82_1
import stacks_project.Chap10.Theorem_10_82_3
import stacks_project.Chap10.Lemma_10_5_4
import stacks_project.Chap10.Lemma_10_8_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

namespace LinearMap

open CategoryTheory
open CategoryTheory.ShortComplex
open CategoryTheory.MonoidalCategory
open RelSeries

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

/-- The map on quotients modulo `I` induced by an `R`-linear map. -/
abbrev quotientMapByIdeal (f : M →ₗ[R] M') (I : Ideal R) :
    M ⧸ (I • (⊤ : Submodule R M)) →ₗ[R] M' ⧸ (I • (⊤ : Submodule R M')) :=
  (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R M')) f
    (Submodule.smul_top_le_comap_smul_top I f)

end

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

private theorem quotientMapByIdeal_lTensor_naturality {I : Ideal R} (f : M →ₗ[R] M') :
    f.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul M I =
      TensorProduct.quotTensorEquivQuotSMul M' I ∘ₗ f.lTensor (R ⧸ I) := by
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 10.82.13: every element of `I • ⊤` already lies in `J • ⊤` for some
finitely generated subideal `J ≤ I`. -/
private theorem exists_fg_subideal_of_mem_smul_top
    {N : Type*} [AddCommGroup N] [Module R N] {I : Ideal R} {x : N}
    (hx : x ∈ I • (⊤ : Submodule R N)) :
    ∃ J : Ideal R, J ≤ I ∧ J.FG ∧ x ∈ J • (⊤ : Submodule R N) := by
  -- Realize the membership by a finite linear combination and collect the coefficients into one
  -- finitely generated subideal.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y hy
    refine ⟨Ideal.span ({r} : Set R), ?_, ?_, ?_⟩
    · exact Ideal.span_le.2 (by
        intro s hs
        simp at hs
        simpa [hs] using hr)
    · simpa [Ideal.submodule_span_eq] using
        (Submodule.fg_span (R := R) (s := ({r} : Set R)) (by simpa))
    · exact Submodule.smul_mem_smul (Ideal.subset_span (by simp)) (by simpa using hy)
  · intro y z hy hz
    classical
    rcases hy with ⟨Jy, hJyI, hJyfg, hymem⟩
    rcases hz with ⟨Jz, hJzI, hJzfg, hzmem⟩
    rcases hJyfg with ⟨Sy, hSy⟩
    rcases hJzfg with ⟨Sz, hSz⟩
    refine ⟨Jy ⊔ Jz, sup_le hJyI hJzI, ⟨Sy ∪ Sz, ?_⟩, ?_⟩
    · rw [Finset.coe_union, Ideal.span_union, hSy, hSz]
    exact Submodule.add_mem _ ((Submodule.smul_mono_left le_sup_left) hymem)
      ((Submodule.smul_mono_left le_sup_right) hzmem)

private theorem injective_of_ladder_linearEquiv
    {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : A' →ₗ[R] B'} {e₁ : A ≃ₗ[R] A'} {e₂ : B ≃ₗ[R] B'}
    (h : g ∘ₗ e₁ = e₂ ∘ₗ f) (hf : Function.Injective f) :
    Function.Injective g := by
  intro x y hxy
  apply e₁.symm.injective
  apply hf
  apply e₂.injective
  calc
    e₂ (f (e₁.symm x)) = g x := by
      simpa using (LinearMap.congr_fun h (e₁.symm x)).symm
    _ = g y := hxy
    _ = e₂ (f (e₁.symm y)) := by
      simpa using LinearMap.congr_fun h (e₁.symm y)

/-- Helper for Lemma 10.82.13: changing the right tensor factor by a linear equivalence preserves
injectivity of the tensorized map. -/
private theorem injective_rTensor_of_linearEquiv
    {Q P : Type*} [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] M') (e : Q ≃ₗ[R] P) (hP : Function.Injective (f.rTensor P)) :
    Function.Injective (f.rTensor Q) := by
  -- Compare the two tensorized maps through the linear equivalence induced by `e`.
  let eM : TensorProduct R M Q ≃ₗ[R] TensorProduct R M P := e.lTensor M
  let eM' : TensorProduct R M' Q ≃ₗ[R] TensorProduct R M' P := e.lTensor M'
  have hSquare :
      (f.rTensor Q).comp eM.symm.toLinearMap =
        eM'.symm.toLinearMap.comp (f.rTensor P) := by
    apply TensorProduct.ext'
    intro x y
    simp [eM, eM', LinearEquiv.lTensor]
  exact injective_of_ladder_linearEquiv hSquare hP

/-- Helper for Lemma 10.82.13: tensoring with the zero submodule gives an injective map because
the source tensor product is a subsingleton. -/
private theorem injective_rTensor_bot_submodule {Q : Type*} [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] M') :
    Function.Injective (f.rTensor ↥(⊥ : Submodule R Q)) := by
  -- The bottom submodule has only one element, so every map out of its tensor product is injective.
  intro x y _
  exact Subsingleton.elim x y

/-- A universally injective linear map stays injective after reduction modulo any ideal. -/
theorem injective_quotientMapByIdeal_of_universallyInjective (f : M →ₗ[R] M')
    (hf : UniversallyInjective.{u, v, w, max u v w z} f) (I : Ideal R) :
    Function.Injective (f.quotientMapByIdeal I) := by
  -- Specialize universal injectivity to a lifted copy of `R ⧸ I` in the fixed test-module
  -- universe `max u v w z`, then transport injectivity back along `ULift.moduleEquiv`.
  have hRTensorInj :
      Function.Injective (f.rTensor (ULift.{max v w z} (R ⧸ I))) := by
    exact hf (ULift.{max v w z} (R ⧸ I)) inferInstance inferInstance
  have hRTensorBase :
      Function.Injective (f.rTensor (R ⧸ I)) := by
    exact injective_rTensor_of_linearEquiv f ULift.moduleEquiv.symm hRTensorInj
  -- Rewrite the resulting right-tensor injectivity as injectivity of the left-tensor map
  -- appearing in the quotient/tensor comparison square.
  have hTensorInj : Function.Injective (f.lTensor (R ⧸ I)) := by
    simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using
      hRTensorBase
  -- The quotient module is canonically identified with tensoring by `R ⧸ I`, so the comparison
  -- square transports injectivity back to the quotient map.
  exact injective_of_ladder_linearEquiv
    (quotientMapByIdeal_lTensor_naturality (f := f) (I := I)) hTensorInj

/-- Helper for Lemma 10.82.13: injectivity of the quotient map modulo `I` implies injectivity of
the tensorized map with `R ⧸ I`. -/
private theorem injective_rTensor_of_injective_quotientMapByIdeal (f : M →ₗ[R] M')
    (I : Ideal R) (hI : Function.Injective (f.quotientMapByIdeal I)) :
    Function.Injective (f.rTensor (R ⧸ I)) := by
  -- Rewrite the quotient module as `(R ⧸ I) ⊗ M` and transport injectivity back to tensor form.
  let eM := TensorProduct.quotTensorEquivQuotSMul M I
  let eM' := TensorProduct.quotTensorEquivQuotSMul M' I
  have hTensorInj : Function.Injective (f.lTensor (R ⧸ I)) := by
    have hSquare :
      (f.lTensor (R ⧸ I)).comp eM.symm.toLinearMap =
        eM'.symm.toLinearMap.comp (f.quotientMapByIdeal I) := by
      apply DFunLike.ext
      intro z
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) z
      simp [eM, eM', LinearMap.quotientMapByIdeal]
    exact injective_of_ladder_linearEquiv hSquare hI
  simpa [LinearMap.lTensor_inj_iff_rTensor_inj] using hTensorInj

/-- Helper for Lemma 10.82.13: injectivity modulo finitely generated ideals upgrades to arbitrary
ideals because any specific congruence in `I • ⊤` uses only finitely many coefficients from `I`. -/
private theorem injective_quotientMapByIdeal_of_injective_mod_fg (f : M →ₗ[R] M')
    (hfg : ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I))
    (I : Ideal R) :
    Function.Injective (f.quotientMapByIdeal I) := by
  -- Route correction: realize the filtered-colimit sentence pointwise by shrinking one witness in
  -- `I • ⊤` to a finitely generated subideal.
  intro x y hxy
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) x
  obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) y
  have hmem :
      f (m - n) ∈ (I • (⊤ : Submodule R M') : Submodule R M') := by
    have hxy' :
        ((I • (⊤ : Submodule R M')).mkQ (f m)) =
          ((I • (⊤ : Submodule R M')).mkQ (f n)) := by
      simpa [LinearMap.quotientMapByIdeal] using hxy
    exact by
      simpa [map_sub] using
        (Submodule.Quotient.eq (I • (⊤ : Submodule R M') : Submodule R M')).mp hxy'
  obtain ⟨J, hJI, hJfg, hJmem⟩ :=
    exists_fg_subideal_of_mem_smul_top (R := R) hmem
  have hxyJ :
      ((J • (⊤ : Submodule R M)).mkQ m) = ((J • (⊤ : Submodule R M)).mkQ n) := by
    apply hfg J hJfg
    change ((J • (⊤ : Submodule R M')).mkQ (f m)) =
      ((J • (⊤ : Submodule R M')).mkQ (f n))
    exact (Submodule.Quotient.eq (J • (⊤ : Submodule R M') : Submodule R M')).2 <| by
      simpa [map_sub] using hJmem
  exact (Submodule.Quotient.eq (I • (⊤ : Submodule R M) : Submodule R M)).2 <| by
    have hJzero :
        m - n ∈ (J • (⊤ : Submodule R M) : Submodule R M) := by
      exact (Submodule.Quotient.eq (J • (⊤ : Submodule R M) : Submodule R M)).mp hxyJ
    exact (Submodule.smul_mono_left hJI) hJzero

/-- Helper for Lemma 10.82.13: in a short exact sequence of test modules, injectivity of
`f ⊗ -` on the ends forces injectivity in the middle once the target module is flat. -/
private theorem injective_rTensor_of_shortExact_step [Module.Flat R M']
    (f : M →ₗ[R] M')
    {Q₁ Q₂ Q₃ : Type*}
    [AddCommGroup Q₁] [Module R Q₁]
    [AddCommGroup Q₂] [Module R Q₂]
    [AddCommGroup Q₃] [Module R Q₃]
    {i : Q₁ →ₗ[R] Q₂} {π : Q₂ →ₗ[R] Q₃}
    (hi : Function.Injective i) (hex : Function.Exact i π) (hπ : Function.Surjective π)
    (hQ₁ : Function.Injective (f.rTensor Q₁))
    (hQ₃ : Function.Injective (f.rTensor Q₃)) :
    Function.Injective (f.rTensor Q₂) := by
  -- Chase a difference through the tensorized quotient map, then pull it back to the left term and
  -- kill that preimage using flatness of `M'` together with injectivity on `Q₁`.
  intro x y hxy
  let d : TensorProduct R M Q₂ := x - y
  have hdQ₃ : (π.lTensor M) d = 0 := by
    apply hQ₃
    calc
      (f.rTensor Q₃) ((π.lTensor M) d)
          = ((π.lTensor M').comp (f.rTensor Q₂)) d := by
              rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
                LinearMap.lTensor_comp_rTensor]
      _ = 0 := by
            change ((π.lTensor M').comp (f.rTensor Q₂)) (x - y) = 0
            rw [LinearMap.comp_apply, map_sub, hxy, sub_self]
            simp
  obtain ⟨z, hz⟩ := ((lTensor_exact M hex hπ) d).mp hdQ₃
  have hiTensor : Function.Injective (i.lTensor M') := by
    -- Flatness keeps the left map injective after tensoring with `M'`.
    exact Module.Flat.lTensor_preserves_injective_linearMap i hi
  have hfd : (f.rTensor Q₂) d = 0 := by
    change (f.rTensor Q₂) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hzTensor : (f.rTensor Q₁) z = 0 := by
    apply hiTensor
    calc
      (i.lTensor M') ((f.rTensor Q₁) z)
          = ((f.rTensor Q₂).comp (i.lTensor M)) z := by
              change ((i.lTensor M').comp (f.rTensor Q₁)) z =
                ((f.rTensor Q₂).comp (i.lTensor M)) z
              rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
      _ = (f.rTensor Q₂) d := by
            rw [LinearMap.comp_apply, hz]
      _ = 0 := hfd
  have hzZero : z = 0 := hQ₁ hzTensor
  have hdZero : d = 0 := by simpa [hzZero] using hz.symm
  simpa [d, sub_eq_zero] using hdZero

/-- Helper for Lemma 10.82.13: a cyclic filtration propagates injectivity of `f ⊗ -` from the
initial stage to the final stage once every cyclic quotient `R ⧸ I` is controlled. -/
private theorem injective_rTensor_of_cyclic_filtration [Module.Flat R M']
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] M') (s : CyclicFiltration R Q)
    (hquot : ∀ I : Ideal R, Function.Injective (f.quotientMapByIdeal I)) :
    Function.Injective (f.rTensor ↥(s.head)) → Function.Injective (f.rTensor ↥(s.last)) := by
  -- Follow the filtration one snoc step at a time, using the short exact tensor step for each
  -- cyclic quotient.
  induction s using RelSeries.inductionOn' with
  | singleton N =>
      intro hN
      simpa using hN
  | snoc s K hrel ih =>
      rcases hrel with ⟨hle, I, hIquot⟩
      intro hs
      have hprevLast : Function.Injective (f.rTensor ↥(s.last)) := ih hs
      have hprev :
          Function.Injective (f.rTensor ↥(s.last.submoduleOf K)) := by
        -- Rewrite the previous stage through the canonical equivalence `s.last.submoduleOf K ≃ s.last`.
        exact injective_rTensor_of_linearEquiv f (Submodule.submoduleOfEquivOfLe hle) hprevLast
      obtain ⟨e⟩ := hIquot
      have hquotRI : Function.Injective (f.rTensor (R ⧸ I)) :=
        injective_rTensor_of_injective_quotientMapByIdeal f I (hquot I)
      have hquotStep :
          Function.Injective (f.rTensor (↥K ⧸ s.last.submoduleOf K)) := by
        -- Transport the cyclic-quotient injectivity back across the chosen equivalence with `R ⧸ I`.
        exact injective_rTensor_of_linearEquiv f e hquotRI
      rw [RelSeries.last_snoc]
      exact injective_rTensor_of_shortExact_step (f := f)
        (Q₁ := ↥(s.last.submoduleOf K)) (Q₂ := ↥K)
        (Q₃ := ↥K ⧸ s.last.submoduleOf K)
        (i := (s.last.submoduleOf K).subtype) (π := (s.last.submoduleOf K).mkQ)
        (Submodule.injective_subtype (s.last.submoduleOf K))
        (LinearMap.exact_subtype_mkQ (s.last.submoduleOf K))
        (Submodule.mkQ_surjective (s.last.submoduleOf K))
        hprev hquotStep

/-- Helper for Lemma 10.82.13: the cyclic-filtration argument from the source proof shows that
injectivity on every cyclic quotient `R ⧸ I` already implies injectivity after tensoring with an
arbitrary finite module. -/
private theorem injective_rTensor_of_finite_module_of_injective_mod_finite_ideal
    [Module.Flat R M'] {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (f : M →ₗ[R] M') (hquot : ∀ I : Ideal R, Function.Injective (f.quotientMapByIdeal I)) :
    Function.Injective (f.rTensor Q) := by
  obtain ⟨s, hs_head, hs_last⟩ := exists_finite_cyclic_filtration (R := R) (M := Q)
  -- Start at `⊥`, where the tensor source is subsingleton, and propagate injectivity through the
  -- cyclic filtration to the final stage `⊤ = Q`.
  have hhead : Function.Injective (f.rTensor ↥(s.head)) := by
    rw [hs_head]
    exact injective_rTensor_bot_submodule (R := R) (M := M) (M' := M') f
  have hlast : Function.Injective (f.rTensor ↥(s.last)) :=
    injective_rTensor_of_cyclic_filtration (R := R) (M := M) (M' := M')
      (Q := Q) f s hquot hhead
  rw [hs_last] at hlast
  -- Identify the final stage `⊤` with the ambient module `Q`.
  exact injective_rTensor_of_linearEquiv (R := R) (M := M) (M' := M') f
    Submodule.topEquiv.symm hlast

/-- Helper for Lemma 10.82.13: testing the finitely generated ideal criterion at `I = ⊥` already
forces the original map `f` to be injective. -/
private theorem injective_of_injective_mod_finite_ideal
    (f : M →ₗ[R] M')
    (hfg : ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I)) :
    Function.Injective f := by
  -- The quotient modulo the zero ideal is just the original map viewed through the trivial
  -- quotient, so injectivity there descends back to `f`.
  have hquot : Function.Injective (f.quotientMapByIdeal (⊥ : Ideal R)) :=
    hfg ⊥ (by simpa using (Submodule.fg_bot : (⊥ : Ideal R).FG))
  intro x y hxy
  have hxyQ :
      (((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ x) =
        (((⊥ : Ideal R) • (⊤ : Submodule R M)).mkQ y) := by
    apply hquot
    simp [LinearMap.quotientMapByIdeal, hxy]
  have hmem : x - y ∈ ((⊥ : Ideal R) • (⊤ : Submodule R M) : Submodule R M) :=
    (Submodule.Quotient.eq (((⊥ : Ideal R) • (⊤ : Submodule R M) : Submodule R M))).mp hxyQ
  simpa [sub_eq_zero] using hmem

/-- Helper for Lemma 10.82.13: the already-closed finite-module filtration argument applies in
particular to finitely presented test modules. -/
private theorem injective_rTensor_of_finitelyPresented_of_injective_mod_finite_ideal
    [Module.Flat R M'] {Q : Type*} [AddCommGroup Q] [Module R Q]
    [Module.FinitePresentation R Q]
    (f : M →ₗ[R] M')
    (hfg : ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I)) :
    Function.Injective (f.rTensor Q) := by
  -- Route correction: the cyclic-filtration proof is already finished for finite modules, so the
  -- finitely presented case is just the typeclass bridge `FinitePresentation -> Finite`.
  letI : Module.Finite R Q := inferInstance
  exact injective_rTensor_of_finite_module_of_injective_mod_finite_ideal
    (R := R) (M := M) (M' := M') (Q := Q) f
    (fun I ↦ injective_quotientMapByIdeal_of_injective_mod_fg
      (R := R) (M := M) (M' := M') f hfg I)

/-- Helper for Lemma 10.82.13: injectivity of `f ⊗ Q` for every finite module `Q` already implies
universal injectivity, because any tensor equality uses only a finite submodule of the right-hand
tensor factor and flatness of `M'` makes the ambient inclusion detectable after tensoring. -/
private theorem universallyInjective_of_injective_rTensor_finite_modules
    [Module.Flat R M'] (f : M →ₗ[R] M')
    (hfinite :
      ∀ {Q : Type z} [AddCommGroup Q] [Module R Q] [Module.Finite R Q],
        Function.Injective (f.rTensor Q)) :
    UniversallyInjective.{u, v, w, z} f := by
  unfold UniversallyInjective
  intro Q _ _
  intro x y hxy
  let s : Set (TensorProduct R M Q) := {x, y}
  have hs : s.Finite := by
    simp [s]
  obtain ⟨Q', hQ'finite, hsQ'⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite (R := R) (M := M) (N := Q) s hs
  have hx_mem : x ∈ s := by
    simp [s]
  have hy_mem : y ∈ s := by
    simp [s]
  obtain ⟨x', hx'⟩ := hsQ' hx_mem
  obtain ⟨y', hy'⟩ := hsQ' hy_mem
  have hSubtypeInj : Function.Injective (Q'.subtype.lTensor M') := by
    -- Flatness of `M'` keeps the finite-submodule inclusion injective after tensoring.
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := M') Q'.subtype
      (Submodule.injective_subtype Q')
  have hxy' : (f.rTensor Q') x' = (f.rTensor Q') y' := by
    -- Compare `x` and `y` inside the finite submodule through tensor naturality.
    apply hSubtypeInj
    calc
      (Q'.subtype.lTensor M') ((f.rTensor Q') x')
          = (f.rTensor Q) ((Q'.subtype.lTensor M) x') := by
              rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
                LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
      _ = (f.rTensor Q) x := by
            rw [hx']
      _ = (f.rTensor Q) y := hxy
      _ = (f.rTensor Q) ((Q'.subtype.lTensor M) y') := by
            rw [hy']
      _ = (Q'.subtype.lTensor M') ((f.rTensor Q') y') := by
            rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
              LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hQ'inj : Function.Injective (f.rTensor Q') := hfinite (Q := Q')
  have hxy0 : x' = y' := hQ'inj hxy'
  -- Once the equality is proved in the finite tensor factor, transport it back to `M ⊗ Q`.
  calc
    x = (Q'.subtype.lTensor M) x' := hx'.symm
    _ = (Q'.subtype.lTensor M) y' := by
          rw [hxy0]
    _ = y := hy'

/-- Helper for Lemma 10.82.13: universal injectivity proved in the fixed test universe descends to
the public hidden-universe formulation by testing any module through its `ULift`. -/
private theorem universallyInjective_max_test_universe_to_test_universe
    (f : M →ₗ[R] M')
    (hf : UniversallyInjective.{u, v, w, max u v w z} f) :
    UniversallyInjective.{u, v, w, z} f := by
  unfold UniversallyInjective at hf ⊢
  intro Q _ _
  have hLift :
      Function.Injective (f.rTensor (ULift.{max u v w z} Q)) := by
    exact hf (ULift.{max u v w z} Q) inferInstance inferInstance
  -- Transport injectivity back across the canonical equivalence `ULift Q ≃ Q`.
  exact injective_rTensor_of_linearEquiv
    (R := R) (M := M) (M' := M') f ULift.moduleEquiv.symm hLift

/-- Helper for Lemma 10.82.13: the criterion proved at the explicit test-module universe
`max u v w z`, which is the stable universe in which the source-proof filtration argument closes. -/
private theorem universallyInjective_max_test_universe_iff_injective_mod_finite_ideal
    [Module.Flat R M'] (f : M →ₗ[R] M') :
    UniversallyInjective.{u, v, w, max u v w z} f ↔
      ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I) := by
  constructor
  · intro hf I hI
    -- The forward implication is the existing reduction-modulo-`I` specialization of universal
    -- injectivity at the stable test-module universe.
    exact injective_quotientMapByIdeal_of_universallyInjective
      (R := R) (M := M) (M' := M') f hf I
  · intro hfg
    have hfinite :
        ∀ {Q : Type (max u v w z)} [AddCommGroup Q] [Module R Q] [Module.Finite R Q],
          Function.Injective (f.rTensor Q) := by
      intro Q _ _ _
      -- The source-proof cyclic-filtration argument is already closed for every finite module.
      exact injective_rTensor_of_finite_module_of_injective_mod_finite_ideal
        (R := R) (M := M) (M' := M') (Q := Q) f
        (fun I ↦ injective_quotientMapByIdeal_of_injective_mod_fg
          (R := R) (M := M) (M' := M') f hfg I)
    exact universallyInjective_of_injective_rTensor_finite_modules
      (R := R) (M := M) (M' := M') f
      (fun {Q} _ _ _ ↦ hfinite (Q := Q))

/-- Lemma 10.82.13: if `M'` is a flat `R`-module, then an `R`-linear map `M → M'` is universally
injective if and only if the induced map `M / I M → M' / I M'` is injective for every finitely
generated ideal `I` of `R`. -/
theorem universallyInjective_iff_injective_mod_finite_ideal [Module.Flat R M']
    (f : M →ₗ[R] M') :
    UniversallyInjective.{u, v, w, max u v w z} f ↔
      ∀ I : Ideal R, I.FG → Function.Injective (f.quotientMapByIdeal I) := by
  -- Route correction: the theorem statement must expose the fixed test-module universe in which
  -- the source-proof filtration argument closes; this is a meaning-preserving universe repair.
  exact universallyInjective_max_test_universe_iff_injective_mod_finite_ideal
    (R := R) (M := M) (M' := M') f

section

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Flat A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Flat A N]

open IsLocalRing

-- Proof sketch: apply `universallyInjective_iff_injective_mod_finite_ideal`. For a finitely
-- generated ideal `J`, pass to the quotient local ring `A / J`; the induced map on
-- `M / J M → N / J N` has injective reduction modulo its maximal ideal by the hypothesis on
-- `u`, and flatness descends to the quotient modules, so the local criterion over `A / J`
-- upgrades that closed-fiber injectivity to injectivity modulo `J`.
/-- Over a local ring, a linear map between flat modules is universally injective as soon as its
reduction modulo the maximal ideal is injective. -/
theorem universallyInjective_of_injective_mod_maximalIdeal (u : M →ₗ[A] N)
    (hu : Function.Injective (u.quotientMapByIdeal (maximalIdeal A))) :
    UniversallyInjective.{u, v, w, u} u := by
  have hmax :
      UniversallyInjective.{u, v, w, max u v w u} u := by
    refine (universallyInjective_iff_injective_mod_finite_ideal u).2 ?_
    intro J hJ
    sorry
  exact universallyInjective_max_test_universe_to_test_universe
    (R := A) (M := M) (M' := N) u hmax

end

end

end LinearMap
