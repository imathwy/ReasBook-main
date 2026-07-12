import Mathlib
import StacksProject_2024.Chap10.Lemma_10_75_2
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators TensorProduct

universe u v

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {A : Type v}
variable {M : Type u} [AddCommGroup M] [Module R M]

local notation "IM" => I • (⊤ : Submodule R M)
local notation "mkQIM" => Submodule.mkQ IM
set_option quotPrecheck false in
local notation "Tor₁[" R "](" N ", " M ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R N)).obj (ModuleCat.of R M))

/-- Helper for Lemma 10.101.3: a lifted basis of `M / IM` forces the family `x` to span `M`
once `I` is nilpotent. -/
lemma span_eq_top_of_family_of_quotient_basis
    (x : A → M)
    (hI : IsNilpotent I)
    (hbasis : ∃ bbar : Module.Basis A (R ⧸ I) (M ⧸ IM), ∀ a, bbar a = mkQIM (x a)) :
    Submodule.span R (Set.range x) = ⊤ := by
  rcases hbasis with ⟨bbar, hbbar⟩
  have hmkQx : mkQIM ∘ x = bbar := by
    funext a
    exact (hbbar a).symm
  -- Rewrite the quotient basis span in the `R`-linear form required by Nakayama.
  have hgen : Submodule.span R (mkQIM '' Set.range x) = ⊤ := by
    rw [← Set.range_comp, hmkQx, ← Submodule.restrictScalars_span R (R ⧸ I)
      Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff]
    exact bbar.span_eq
  -- Nilpotent Nakayama upgrades generation modulo `I` to generation upstairs.
  exact span_eq_top_of_quotient_span_eq_top_of_isNilpotent (R := R) (M := M) (I := I)
    (Set.range x) hgen hI

/-- Helper for Lemma 10.101.3: tensoring an exact pair with `R / I` is exact after passing to
quotients by `I`. -/
lemma quotientMapByIdeal_exact
    {N P Q : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : N →ₗ[R] P) (g : P →ₗ[R] Q)
    (hExact : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (f.quotientMapByIdeal I) (g.quotientMapByIdeal I) := by
  intro y
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R P)) y
    change ((I • (⊤ : Submodule R Q)).mkQ (g x)) = 0 at hx
    have hx' : g x ∈ I • (⊤ : Submodule R Q) := by
      simpa using (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).mp hx
    have hxLift :
        ∃ y : P, y ∈ I • (⊤ : Submodule R P) ∧ g y = g x :=
      Submodule.smul_induction_on hx'
        (fun r hr z _ ↦ by
          obtain ⟨y, rfl⟩ := hg z
          refine ⟨r • y, ?_, by simp⟩
          exact Submodule.smul_mem_smul hr (by simp))
        (fun y z hy hz ↦ by
          rcases hy with ⟨y', hy', rfl⟩
          rcases hz with ⟨z', hz', rfl⟩
          exact ⟨y' + z', Submodule.add_mem _ hy' hz', by simp⟩)
    rcases hxLift with ⟨y, hyI, hy⟩
    have hxy : g (x - y) = 0 := by
      simp [hy]
    rcases (hExact (x - y)).mp hxy with ⟨n, hn⟩
    refine ⟨(I • (⊤ : Submodule R N)).mkQ n, ?_⟩
    change ((I • (⊤ : Submodule R P)).mkQ (f n)) = (I • (⊤ : Submodule R P)).mkQ x
    rw [hn]
    simpa using hyI
  · rintro ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R N)) x
    change ((I • (⊤ : Submodule R Q)).mkQ (g (f x))) = 0
    exact
      (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R Q))).2 <| by
        have hfx : g (f x) = 0 := by
          simpa [Function.comp] using congr_fun hExact.comp_eq_zero x
        rw [hfx]
        exact Submodule.zero_mem _

/-- Helper for Lemma 10.101.3: the quotient-by-`I` map is the tensor map with `R ⧸ I` under the
standard quotient-tensor comparison. -/
lemma quotientMapByIdeal_lTensor_naturality
    {N P : Type*}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) :
    f.quotientMapByIdeal I ∘ₗ TensorProduct.quotTensorEquivQuotSMul N I =
      TensorProduct.quotTensorEquivQuotSMul P I ∘ₗ f.lTensor (R ⧸ I) := by
  -- Check the commuting square on pure tensors coming from quotient scalars.
  apply TensorProduct.ext'
  intro q x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [LinearMap.quotientMapByIdeal]

/-- Helper for Lemma 10.101.3: injectivity transfers across a commuting square of linear
equivalences. -/
lemma injective_of_ladder_linearEquiv_local
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

/-- Helper for Lemma 10.101.3: the basis of `M / IM` makes the reduced free cover injective. -/
lemma reduced_free_cover_lTensor_comparison
    [DecidableEq A]
    (x : A → M) :
    (Finsupp.linearCombination R x).lTensor (R ⧸ I) ∘ₗ
        (LinearEquiv.restrictScalars R
          (TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) A)).symm.toLinearMap =
      (TensorProduct.quotTensorEquivQuotSMul M I).symm.toLinearMap ∘ₗ
        (Finsupp.linearCombination (R ⧸ I) (mkQIM ∘ x)).restrictScalars R := by
  -- Check the comparison on the `Finsupp.single` generators of the free module over `R ⧸ I`.
  apply Finsupp.lhom_ext
  intro a q
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
  calc
    (Finsupp.linearCombination R x).lTensor (R ⧸ I)
        ((LinearEquiv.restrictScalars R
          (TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) A)).symm
          (Finsupp.single a (Ideal.Quotient.mk I r)))
      = (Ideal.Quotient.mk I r) ⊗ₜ[R] x a := by
          simp [Finsupp.linearCombination_single]
    _ = (r • (1 : R ⧸ I)) ⊗ₜ[R] x a := by
          congr 1
          change Ideal.Quotient.mk I r = (Ideal.Quotient.mk I r) * 1
          simp
    _ = r • ((1 : R ⧸ I) ⊗ₜ[R] x a) := by
          rw [TensorProduct.smul_tmul']
    _ = (TensorProduct.quotTensorEquivQuotSMul M I).symm
          ((Ideal.Quotient.mk I r) • mkQIM (x a)) := by
          apply (TensorProduct.quotTensorEquivQuotSMul M I).injective
          simp only [map_smul, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
            Submodule.mkQ_apply, LinearEquiv.apply_symm_apply]
          exact Module.Quotient.mk_smul_mk (M := M) (I := I) r (x a)
    _ = (TensorProduct.quotTensorEquivQuotSMul M I).symm
          ((Finsupp.linearCombination (R ⧸ I) (mkQIM ∘ x)).restrictScalars R
            (Finsupp.single a (Ideal.Quotient.mk I r))) := by
          simp [Finsupp.linearCombination_single]

/-- Helper for Lemma 10.101.3: the basis of `M / IM` makes the reduced free cover injective. -/
lemma free_cover_mod_ideal_injective_of_quotient_basis
    (x : A → M)
    (hbasis : ∃ bbar : Module.Basis A (R ⧸ I) (M ⧸ IM), ∀ a, bbar a = mkQIM (x a)) :
    Function.Injective ((Finsupp.linearCombination R x).quotientMapByIdeal I) := by
  classical
  rcases hbasis with ⟨bbar, hbbar⟩
  have hmkQx : mkQIM ∘ x = bbar := by
    funext a
    exact (hbbar a).symm
  let e₁ : (A →₀ (R ⧸ I)) ≃ₗ[R] (R ⧸ I) ⊗[R] (A →₀ R) :=
    LinearEquiv.restrictScalars R
      (TensorProduct.finsuppScalarRight R (R ⧸ I) (R ⧸ I) A).symm
  let e₂ : (M ⧸ IM) ≃ₗ[R] (R ⧸ I) ⊗[R] M :=
    (TensorProduct.quotTensorEquivQuotSMul M I).symm
  have hCompare :
      (Finsupp.linearCombination R x).lTensor (R ⧸ I) ∘ₗ e₁.toLinearMap =
        e₂.toLinearMap ∘ₗ (Finsupp.linearCombination (R ⧸ I) bbar).restrictScalars R := by
    -- Rewrite the quotient family `mkQIM ∘ x` as the given basis `bbar`.
    simpa [e₁, e₂, hmkQx] using
      reduced_free_cover_lTensor_comparison (R := R) (I := I) (A := A) (M := M) x
  have hBasisInj :
      Function.Injective ((Finsupp.linearCombination (R ⧸ I) bbar).restrictScalars R) := by
    -- A basis identifies the reduced free cover with its coordinate isomorphism.
    intro c d hcd
    have hrepr := congrArg bbar.repr hcd
    simpa using hrepr
  have hTensorInj : Function.Injective ((Finsupp.linearCombination R x).lTensor (R ⧸ I)) :=
    injective_of_ladder_linearEquiv_local (R := R) hCompare hBasisInj
  -- Transfer the tensor-side injectivity back through the quotient-tensor comparison.
  exact injective_of_ladder_linearEquiv_local (R := R)
    (quotientMapByIdeal_lTensor_naturality (R := R) (I := I) (N := A →₀ R) (P := M)
      (Finsupp.linearCombination R x))
    hTensorInj

/-- Helper for Lemma 10.101.3: if `0 → N → P → M → 0` is exact and `Tor₁^R(R / I, M)` vanishes,
then reduction modulo `I` keeps the left map injective. -/
lemma lTensor_injective_of_exact_of_tor_one_vanishes_local
    {N P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (g : P →ₗ[R] M)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hExact : Function.Exact f g)
    (htor :
      IsZero
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)))) :
    Function.Injective (f.lTensor (R ⧸ I)) := by
  -- Route correction: the intended proof is the six-term Tor/tensor exact sequence for
  -- `0 → N --f→ P --g→ M → 0` with left factor `R ⧸ I`; this helper is kept in the
  -- same universe as `ModuleCat R`, and the public theorem below shrinks larger index types first.
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk f g (Function.Exact.linearMap_comp_eq_zero hExact)
  have hS : S.ShortExact := by
    -- Package the function-level exact presentation as a short exact complex in `ModuleCat R`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      exact hExact
    · exact (ModuleCat.mono_iff_injective _).2 hf
    · exact (ModuleCat.epi_iff_surjective _).2 hg
  let T := ModuleCat.torTensorSixTermSequence (ModuleCat.of R (R ⧸ I)) hS
  have hT : T.Exact :=
    ModuleCat.torTensorSixTermSequence_exact (ModuleCat.of R (R ⧸ I)) hS
  have hExactRaw : Function.Exact (T.map' 2 3).hom (T.map' 3 4).hom := by
    -- Exactness at the tensorized `N` term is the `2 → 3 → 4` window.
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (T.sc hT.toIsComplex 2)).1
        (hT.exact 2)
  have hmap34' :
      T.map' 3 4 =
        MonoidalCategoryStruct.whiskerLeft (ModuleCat.of R (R ⧸ I)) S.f := by
    -- The fourth arrow of the six-term row is tensoring the left map of the short complex.
    dsimp [T]
    unfold ModuleCat.torTensorSixTermSequence ComposableArrows.mk₅ ComposableArrows.mk₄
    rfl
  have hmap34 : (T.map' 3 4).hom = f.lTensor (R ⧸ I) := by
    -- Translate the categorical whiskering map back to the concrete tensor linear map.
    rw [hmap34']
    change ModuleCat.Hom.hom
        (MonoidalCategoryStruct.whiskerLeft
          (ModuleCat.of R (R ⧸ I))
          (ModuleCat.ofHom f)) = f.lTensor (R ⧸ I)
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  have hExactTail : Function.Exact (T.map' 2 3).hom (f.lTensor (R ⧸ I)) := by
    -- Use the concrete description of the tensor-tail map in the exactness window.
    simpa [hmap34] using hExactRaw
  have hSourceSubsingleton :
      Subsingleton
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M))) :=
    (ModuleCat.isZero_iff_subsingleton).1 htor
  -- A vector in the kernel comes from the zero Tor source, hence is zero.
  rw [← LinearMap.ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rcases (hExactTail x).mp hx with ⟨z, hz⟩
  have hz0 : z = 0 := @Subsingleton.elim _ hSourceSubsingleton z 0
  rw [← hz, hz0]
  exact LinearMap.map_zero (T.map' 2 3).hom

/-- Helper for Lemma 10.101.3: if `0 → N → P → M → 0` is exact and `Tor₁^R(R / I, M)` vanishes,
then reduction modulo `I` keeps the left map injective. -/
lemma quotientMapByIdeal_injective_of_exact_of_tor_one_vanishes_local
    {N P : Type u}
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) (g : P →ₗ[R] M)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hExact : Function.Exact f g)
    (htor :
      IsZero
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)))) :
    Function.Injective (f.quotientMapByIdeal I) := by
  have hTensorInj : Function.Injective (f.lTensor (R ⧸ I)) :=
    lTensor_injective_of_exact_of_tor_one_vanishes_local
      (R := R) (I := I) (M := M) f g hf hg hExact htor
  -- The quotient-tensor equivalence transports tensor injectivity to reduction modulo `I`.
  exact injective_of_ladder_linearEquiv_local (R := R)
    (quotientMapByIdeal_lTensor_naturality (R := R) (I := I) f) hTensorInj

/-- Helper for Chap10 Lemma 10 101 3: a nontrivial quotient basis forces a large index type to
be small enough to reindex into the universe of `R`. -/
lemma smallIndexOfNontrivialQuotientBasis
    [Nontrivial (R ⧸ I)]
    (x : A → M)
    (hbasis : ∃ bbar : Module.Basis A (R ⧸ I) (M ⧸ IM), ∀ a, bbar a = mkQIM (x a)) :
    Small.{u} A := by
  rcases hbasis with ⟨bbar, _⟩
  -- A basis over a nontrivial quotient ring is injective into a type already living in universe `u`.
  exact small_of_injective bbar.injective

/-- Helper for Chap10 Lemma 10 101 3: the basis lifting theorem when the index type already
lives in the same universe as the module category used for the Tor exact sequence. -/
theorem basisOfSmallIndexQuotientBasisOfTorOneVanishes
    {A₀ : Type u}
    (x : A₀ → M)
    (hI : IsNilpotent I)
    (hbasis : ∃ bbar : Module.Basis A₀ (R ⧸ I) (M ⧸ IM), ∀ a, bbar a = mkQIM (x a))
    (htor :
      IsZero
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)))) :
    ∃ b : Module.Basis A₀ R M, ∀ a, b a = x a := by
  classical
  let π : (A₀ →₀ R) →ₗ[R] M := Finsupp.linearCombination R x
  let K : Submodule R (A₀ →₀ R) := LinearMap.ker π
  have hspan : Submodule.span R (Set.range x) = ⊤ :=
    span_eq_top_of_family_of_quotient_basis (R := R) (I := I) (A := A₀) (M := M) x hI hbasis
  have hπ_surj : Function.Surjective π := by
    -- Surjectivity is the generation statement coming from Nakayama.
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hspan
  have hExact : Function.Exact K.subtype π := by
    -- The kernel inclusion and the free cover form the presentation exact sequence of `M`.
    exact LinearMap.exact_subtype_ker_map π
  have hπ_inj : Function.Injective π := by
    have hQuotExact :
        Function.Exact (K.subtype.quotientMapByIdeal I) (π.quotientMapByIdeal I) :=
      quotientMapByIdeal_exact (R := R) (I := I) K.subtype π hExact hπ_surj
    have hQuotSubtypeInj : Function.Injective (K.subtype.quotientMapByIdeal I) :=
      quotientMapByIdeal_injective_of_exact_of_tor_one_vanishes_local
        (R := R) (I := I) (M := M) K.subtype π K.injective_subtype hπ_surj hExact htor
    have hQuotInj : Function.Injective (π.quotientMapByIdeal I) :=
      free_cover_mod_ideal_injective_of_quotient_basis (R := R) (I := I) (A := A₀) (M := M) x
        hbasis
    have hRangeBot : LinearMap.range (K.subtype.quotientMapByIdeal I) = ⊥ := by
      -- Exactness modulo `I` and injectivity of the reduced free cover force the reduced kernel to
      -- vanish.
      rw [← LinearMap.exact_iff.mp hQuotExact, LinearMap.ker_eq_bot]
      exact hQuotInj
    have hQuotSubtypeZero : K.subtype.quotientMapByIdeal I = 0 :=
      LinearMap.range_eq_bot.mp hRangeBot
    have hKerQuotSubsingleton :
        Subsingleton (K ⧸ (I • (⊤ : Submodule R K))) := by
      refine ⟨fun x y ↦ hQuotSubtypeInj ?_⟩
      simp [hQuotSubtypeZero]
    have hIKer : I • (⊤ : Submodule R K) = ⊤ := by
      -- A quotient with only one point says exactly that `K = IK`.
      rwa [Submodule.Quotient.subsingleton_iff] at hKerQuotSubsingleton
    have hKSubsingleton : Subsingleton K :=
      subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent I hIKer hI
    -- Nilpotence now kills the whole kernel, so the free cover is injective.
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.subsingleton_iff_eq_bot.mp hKSubsingleton
  -- The final basis is the one induced by the now-bijective free cover.
  refine ⟨Module.Basis.ofRepr (LinearEquiv.ofBijective π ⟨hπ_inj, hπ_surj⟩).symm, ?_⟩
  intro a
  simp [π]

-- Proof sketch: use Nakayama's lemma to show that the family `x` generates `M`. A relation
-- `∑ a, f a • x a = 0` reduces modulo `I` to show each coefficient lies in `I`, while the
-- vanishing of `Tor₁^R(R / I, M)` identifies the first obstruction group controlling relations.
-- Iterating the same argument modulo `I ^ n` forces the coefficients into every power of `I`; the
-- nilpotence of `I` then implies all coefficients vanish, so the family is a basis.
/-- Chap10 Lemma 10 101 3: if `I` is a nilpotent ideal of `R`, the images of a family `x : A → M` form an
`R ⧸ I`-basis of `M / IM`, and `Tor₁^R(R / I, M)` vanishes, then `x` is an `R`-basis of `M`. -/
@[stacks 051H]
theorem exists_basis_of_quotient_basis_of_nilpotent_ideal_of_tor_one_vanishes
    (x : A → M)
    (hI : IsNilpotent I)
    (hbasis : ∃ bbar : Module.Basis A (R ⧸ I) (M ⧸ IM), ∀ a, bbar a = mkQIM (x a))
    (htor :
      IsZero
        ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R (R ⧸ I))).obj
          (ModuleCat.of R M)))) :
    ∃ b : Module.Basis A R M, ∀ a, b a = x a := by
  classical
  by_cases hquot : Nontrivial (R ⧸ I)
  · -- In the nontrivial quotient case, the quotient basis injects the index type into a small type.
    letI : Nontrivial (R ⧸ I) := hquot
    have hsmall : Small.{u} A :=
      smallIndexOfNontrivialQuotientBasis (R := R) (I := I) (A := A) (M := M) x hbasis
    let e : A ≃ Shrink.{u} A := equivShrink A
    let xSmall : Shrink.{u} A → M := x ∘ e.symm
    have hbasisSmall :
        ∃ bbar : Module.Basis (Shrink.{u} A) (R ⧸ I) (M ⧸ IM),
          ∀ a, bbar a = mkQIM (xSmall a) := by
      rcases hbasis with ⟨bbar, hbbar⟩
      refine ⟨bbar.reindex e, ?_⟩
      intro a
      -- Reindex the quotient basis along the chosen small representative of `A`.
      simp [Module.Basis.reindex, xSmall, e, hbbar]
    obtain ⟨bSmall, hbSmall⟩ :=
      basisOfSmallIndexQuotientBasisOfTorOneVanishes
        (R := R) (I := I) (M := M) (A₀ := Shrink.{u} A) xSmall hI hbasisSmall htor
    refine ⟨bSmall.reindex e.symm, ?_⟩
    intro a
    -- Reindex the lifted small basis back to the original index type.
    simpa [Module.Basis.reindex, xSmall, e] using hbSmall (e a)
  · -- If `R / I` is trivial, nilpotence of `I = ⊤` makes `R` and then `M` subsingleton.
    have hquotSubsingleton : Subsingleton (R ⧸ I) :=
      not_nontrivial_iff_subsingleton.mp hquot
    have hItop : I = ⊤ :=
      Ideal.Quotient.subsingleton_iff.mp hquotSubsingleton
    have hRsubsingleton : Subsingleton R := by
      rcases hI with ⟨n, hn⟩
      have hTopNil : (⊤ : Ideal R) = ⊥ := by
        have hpow : (⊤ : Ideal R) ^ n = ⊥ := by
          simpa [hItop] using hn
        simpa [Ideal.top_pow R n] using hpow
      have hzero_one : (0 : R) = 1 := by
        have h1bot : (1 : R) ∈ (⊥ : Ideal R) := by
          rw [← hTopNil]
          simp
        exact (Ideal.mem_bot.mp h1bot).symm
      exact subsingleton_of_zero_eq_one hzero_one
    letI : Subsingleton R := hRsubsingleton
    letI : Subsingleton M := Module.subsingleton R M
    refine ⟨default, ?_⟩
    intro a
    exact Subsingleton.elim _ _

end
