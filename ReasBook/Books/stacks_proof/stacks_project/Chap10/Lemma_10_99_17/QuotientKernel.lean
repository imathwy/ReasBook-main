import StacksProject_2024.Chap10.Lemma_10_99_17.TorDegreeZero

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]
variable {r : ℕ} (f : Fin r → A)

local notation "I" => Ideal.span (Set.range f)
local notation "Ā" => A ⧸ I
local notation "M̄" => M ⧸ (I • (⊤ : Submodule A M))
set_option quotPrecheck false in
local notation "TorQ[" n "]" =>
  (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā))

/-- Helper for Lemma 10.99.17: a commuting square of linear equivalences induces a linear
equivalence on kernels. -/
theorem ker_equiv_of_ladder_linear_equiv_nonempty
    {X₁ X₂ Y₁ Y₂ : Type u}
    [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
    [AddCommGroup Y₁] [Module A Y₁] [AddCommGroup Y₂] [Module A Y₂]
    {u : X₁ →ₗ[A] X₂} {v : Y₁ →ₗ[A] Y₂}
    (e₁ : X₁ ≃ₗ[A] Y₁) (e₂ : X₂ ≃ₗ[A] Y₂)
    (h : v.comp e₁.toLinearMap = e₂.toLinearMap.comp u) :
    Nonempty (LinearMap.ker u ≃ₗ[A] LinearMap.ker v) := by
  let f : LinearMap.ker u →ₗ[A] LinearMap.ker v :=
    { toFun := fun x ↦ ⟨e₁ x, by
        have hx := LinearMap.congr_fun h x.1
        simpa [LinearMap.comp_apply, x.2] using hx⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  refine ⟨LinearEquiv.ofBijective f ?_⟩
  constructor
  · intro x y hxy
    ext
    exact e₁.injective (congrArg Subtype.val hxy)
  · intro y
    refine ⟨⟨e₁.symm y, ?_⟩, ?_⟩
    · have hy := LinearMap.congr_fun h (e₁.symm y)
      apply e₂.injective
      simpa [LinearMap.comp_apply, y.2] using hy.symm
    · ext
      simp [f]

/-- Helper for Lemma 10.99.17: a proof-free extractor for the kernel equivalence from a
commutative square of linear equivalences. -/
noncomputable abbrev ker_equiv_of_ladder_linear_equiv
    {X₁ X₂ Y₁ Y₂ : Type u}
    [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
    [AddCommGroup Y₁] [Module A Y₁] [AddCommGroup Y₂] [Module A Y₂]
    {u : X₁ →ₗ[A] X₂} {v : Y₁ →ₗ[A] Y₂}
    (e₁ : X₁ ≃ₗ[A] Y₁) (e₂ : X₂ ≃ₗ[A] Y₂)
    (h : v.comp e₁.toLinearMap = e₂.toLinearMap.comp u) :
    LinearMap.ker u ≃ₗ[A] LinearMap.ker v :=
  Classical.choice (ker_equiv_of_ladder_linear_equiv_nonempty
    (A := A) (e₁ := e₁) (e₂ := e₂) h)

/-- Helper for Lemma 10.99.17: the fixed-left source owner `Tor'₁^A(M, A / I)` is identified with
the kernel of the canonical map `I ⊗[A] M → M`. -/
theorem source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module_nonempty :
    Nonempty
      ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā)) ≃ₗ[A]
        LinearMap.ker
          (TensorProduct.lift ((LinearMap.lsmul A M).comp ((show Ideal A from I).subtype)))) := by
  let J : Ideal A := I
  let μ : J ⊗[A] M →ₗ[A] M :=
    TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype)
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk J.subtype J.mkQ (by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [J] using (LinearMap.exact_subtype_mkQ J)
    · exact (ModuleCat.mono_iff_injective _).2 J.injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).2 J.mkQ_surjective
  obtain ⟨δ, hFive⟩ :=
    source_owner_tor_one_tensor_exact_of_shortExact (A := A) (M := M) hS
  let β :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₂) ⟶
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₃) :=
    (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
  let u :
      ((tensorLeft (ModuleCat.of A M)).obj S.X₁) ⟶
        ((tensorLeft (ModuleCat.of A M)).obj S.X₂) :=
    ((tensorLeft (ModuleCat.of A M)).map S.f)
  have hβ_zero : β = 0 := by
    -- Proof comment: the middle source-owner term is `Tor'₁(M, A)`, which vanishes.
    simpa [β, S, J] using
      (source_owner_tor_one_unit_isZero (A := A) (M := M)).eq_of_src β 0
  have hExactTor :
      Function.Exact β.hom δ.hom := by
    -- Proof comment: this is the exactness window at `Tor'₁(M, A / I)`.
    simpa [β, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
          δ
          ((tensorLeft (ModuleCat.of A M)).map S.f)
          ((tensorLeft (ModuleCat.of A M)).map S.g)).sc hFive.toIsComplex 1)).1
        (hFive.exact 1)
  have hExactTensor :
      Function.Exact δ.hom u.hom := by
    -- Proof comment: and this is the exactness window identifying the tensor kernel.
    simpa [u, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
          δ
          ((tensorLeft (ModuleCat.of A M)).map S.f)
          ((tensorLeft (ModuleCat.of A M)).map S.g)).sc hFive.toIsComplex 2)).1
        (hFive.exact 2)
  have hδ_injective : Function.Injective δ.hom := by
    have hkerδ : LinearMap.ker δ.hom = ⊥ := by
      calc
        LinearMap.ker δ.hom = LinearMap.range β.hom := LinearMap.exact_iff.mp hExactTor
        _ = ⊥ := by
          have hβhom : β.hom = 0 := congrArg ModuleCat.Hom.hom hβ_zero
          simpa [hβhom] using (LinearMap.range_eq_bot.mpr hβhom)
    exact (LinearMap.ker_eq_bot).1 hkerδ
  have hker :
      IsLimit
        (KernelFork.ofι δ
          (ModuleCat.hom_ext hExactTensor.linearMap_comp_eq_zero)) :=
    ModuleCat.isLimitKernelFork δ u hExactTensor hδ_injective
  have hu : u.hom = J.subtype.lTensor M := by
    -- Proof comment: the endpoint tensor map is just tensoring the ideal inclusion on the left.
    dsimp [u, S]
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  have hμ :
      μ.comp (TensorProduct.comm A M J).toLinearMap =
        (TensorProduct.rid A M).toLinearMap.comp u.hom := by
    have hcommLid :
        (TensorProduct.lid A M).toLinearMap.comp (TensorProduct.comm A M A).toLinearMap =
          (TensorProduct.rid A M).toLinearMap := by
      exact congrArg LinearEquiv.toLinearMap TensorProduct.comm_trans_lid
    rw [hu]
    dsimp [μ]
    rw [← LinearMap.lid_comp_rTensor]
    change
      (TensorProduct.lid A M).toLinearMap.comp
          ((J.subtype.rTensor M).comp (TensorProduct.comm A M J).toLinearMap) =
        (TensorProduct.rid A M).toLinearMap.comp (J.subtype.lTensor M)
    rw [LinearMap.rTensor_comp_comm]
    change
      (TensorProduct.lid A M).toLinearMap.comp
          ((TensorProduct.comm A M A).toLinearMap.comp (J.subtype.lTensor M)) =
        (TensorProduct.rid A M).toLinearMap.comp (J.subtype.lTensor M)
    rw [← LinearMap.comp_assoc, hcommLid]
  let eSource :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā)) ≃ₗ[A]
        LinearMap.ker u.hom :=
    (((limit.isoLimitCone ⟨_, hker⟩).symm ≪≫ ModuleCat.kernelIsoKer u).toLinearEquiv)
  let eKer :
      LinearMap.ker u.hom ≃ₗ[A] LinearMap.ker μ :=
    ker_equiv_of_ladder_linear_equiv (A := A)
      (e₁ := TensorProduct.comm A M J) (e₂ := TensorProduct.rid A M) hμ
  -- Proof comment: the fixed-left source owner and the public quotient owner both compute the
  -- same kernel attached to `0 → I → A → A / I → 0`.
  refine ⟨?_⟩
  simpa [J] using eSource.trans eKer

/-- Helper for Lemma 10.99.17: a proof-free extractor for the fixed-left source-owner quotient
kernel comparison. -/
noncomputable abbrev source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module :
    (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā)) ≃ₗ[A]
      LinearMap.ker
        (TensorProduct.lift ((LinearMap.lsmul A M).comp ((show Ideal A from I).subtype))) :=
  Classical.choice
    (source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module_nonempty
      (A := A) (M := M) (f := f))

/-- Helper for Lemma 10.99.17: at the quotient object `A / I`, the flipped source owner
`Tor'₁^A(A / I, M)` should agree with the fixed-left source owner `Tor'₁^A(M, A / I)`. This is
the only remaining owner swap needed to feed the module-first quotient hypothesis into the
compiled `10.99.8` theorem. -/
noncomputable def tor_one_quotient_flip_to_source_owner_iso :
    ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A Ā))) ≅
      ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A Ā))) := by
  let eFlipPublic :
      ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A Ā))) ≅
        ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A Ā))) :=
    ((tor_one_module_flip_owner_iso (A := A) (M := M)).app (ModuleCat.of A Ā)).symm
  let ePublicKer :
      ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A Ā))) ≅
        ModuleCat.of A
          (LinearMap.ker
            (TensorProduct.lift ((LinearMap.lsmul A M).comp ((show Ideal A from I).subtype)))) :=
    (tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := A) (M := M) I).toModuleIso
  let eSourceKer :
      ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A Ā))) ≅
        ModuleCat.of A
          (LinearMap.ker
            (TensorProduct.lift ((LinearMap.lsmul A M).comp ((show Ideal A from I).subtype)))) :=
    (source_owner_tor_one_quotient_equiv_ker_ideal_tensor_to_module
      (A := A) (M := M) (f := f)).toModuleIso
  -- Proof comment: both quotient-level owners are compared to the same tensor kernel.
  exact eFlipPublic ≪≫ ePublicKer ≪≫ eSourceKer.symm

/-- Helper for Lemma 10.99.17: the degree-`1` quotient hypothesis can be moved from the
module-first public owner to the quotient-first public owner. This closes the only owner swap that
is available uniformly in the current file without new higher-degree source-owner API. -/
lemma tor_one_public_quotient_vanishes
    (htor : ∀ i : Fin (r + 1), IsZero (TorQ[i.1 + 1])) :
    IsZero
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A Ā))) := by
  have hflipped :
      IsZero
        ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A Ā))) := by
    let eModule :
        (((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā)) ≅
          ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A Ā))) :=
      (tor_one_module_flip_owner_iso (A := A) (M := M)).app (ModuleCat.of A Ā)
    -- Proof comment: first move the given module-first quotient vanishing to the flipped source
    -- owner `Tor'₁(Ā, M)`.
    exact IsZero.of_iso (htor 0) eModule.symm
  have hsource :
      IsZero ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A Ā))) := by
    let eSource :
        ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A Ā))) ≅
          ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A Ā))) :=
      tor_one_quotient_flip_to_source_owner_iso (A := A) (M := M) (f := f)
    -- Proof comment: then use the quotient-level degree-`1` owner comparison already proved via
    -- the common kernel model.
    exact IsZero.of_iso hflipped eSource.symm
  let ePublic :
      (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A Ā))) ≅
        ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A Ā))) :=
    (tor_one_left_owner_iso (A := A) (M := M)).app (ModuleCat.of A Ā)
  -- Proof comment: finally return to the quotient-first public owner that the exactness API uses.
  exact IsZero.of_iso hsource ePublic

/-- Helper for Lemma 10.99.17: the fixed-left source owner at an arbitrary quotient `A / J` is
identified with the kernel of the multiplication map `J ⊗[A] M → M`. This is the quotient-only
degree-`1` bridge used in the final flatness criterion. -/
theorem source_owner_tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module_nonempty
    (J : Ideal A) :
    Nonempty
      ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ J))) ≃ₗ[A]
        LinearMap.ker
          (TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype))) := by
  let μ : J ⊗[A] M →ₗ[A] M :=
    TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype)
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk J.subtype J.mkQ (by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem.2 x.2)
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa using (LinearMap.exact_subtype_mkQ J)
    · exact (ModuleCat.mono_iff_injective _).2 J.injective_subtype
    · exact (ModuleCat.epi_iff_surjective _).2 J.mkQ_surjective
  obtain ⟨δ, hFive⟩ :=
    source_owner_tor_one_tensor_exact_of_shortExact (A := A) (M := M) hS
  let β :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₂) ⟶
        (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₃) :=
    (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
  let u :
      ((tensorLeft (ModuleCat.of A M)).obj S.X₁) ⟶
        ((tensorLeft (ModuleCat.of A M)).obj S.X₂) :=
    ((tensorLeft (ModuleCat.of A M)).map S.f)
  have hβ_zero : β = 0 := by
    -- Proof comment: the middle source-owner term is `Tor'₁(M, A)`, which vanishes.
    simpa [β, S] using
      (source_owner_tor_one_unit_isZero (A := A) (M := M)).eq_of_src β 0
  have hExactTor :
      Function.Exact β.hom δ.hom := by
    -- Proof comment: this is the exactness window at `Tor'₁(M, A / J)`.
    simpa [β, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
          δ
          ((tensorLeft (ModuleCat.of A M)).map S.f)
          ((tensorLeft (ModuleCat.of A M)).map S.g)).sc hFive.toIsComplex 1)).1
        (hFive.exact 1)
  have hExactTensor :
      Function.Exact δ.hom u.hom := by
    -- Proof comment: and this is the exactness window identifying the tensor kernel.
    simpa [u, S, ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)
          δ
          ((tensorLeft (ModuleCat.of A M)).map S.f)
          ((tensorLeft (ModuleCat.of A M)).map S.g)).sc hFive.toIsComplex 2)).1
        (hFive.exact 2)
  have hδ_injective : Function.Injective δ.hom := by
    have hkerδ : LinearMap.ker δ.hom = ⊥ := by
      calc
        LinearMap.ker δ.hom = LinearMap.range β.hom := LinearMap.exact_iff.mp hExactTor
        _ = ⊥ := by
          have hβhom : β.hom = 0 := congrArg ModuleCat.Hom.hom hβ_zero
          simpa [hβhom] using (LinearMap.range_eq_bot.mpr hβhom)
    exact (LinearMap.ker_eq_bot).1 hkerδ
  have hker :
      IsLimit
        (KernelFork.ofι δ
          (ModuleCat.hom_ext hExactTensor.linearMap_comp_eq_zero)) :=
    ModuleCat.isLimitKernelFork δ u hExactTensor hδ_injective
  have hu : u.hom = J.subtype.lTensor M := by
    -- Proof comment: the endpoint tensor map is just tensoring the ideal inclusion on the left.
    dsimp [u, S]
    rw [ModuleCat.hom_whiskerLeft]
    rfl
  have hμ :
      μ.comp (TensorProduct.comm A M J).toLinearMap =
        (TensorProduct.rid A M).toLinearMap.comp u.hom := by
    have hcommLid :
        (TensorProduct.lid A M).toLinearMap.comp (TensorProduct.comm A M A).toLinearMap =
          (TensorProduct.rid A M).toLinearMap := by
      exact congrArg LinearEquiv.toLinearMap TensorProduct.comm_trans_lid
    rw [hu]
    dsimp [μ]
    rw [← LinearMap.lid_comp_rTensor]
    change
      (TensorProduct.lid A M).toLinearMap.comp
          ((J.subtype.rTensor M).comp (TensorProduct.comm A M J).toLinearMap) =
        (TensorProduct.rid A M).toLinearMap.comp (J.subtype.lTensor M)
    rw [LinearMap.rTensor_comp_comm]
    change
      (TensorProduct.lid A M).toLinearMap.comp
          ((TensorProduct.comm A M A).toLinearMap.comp (J.subtype.lTensor M)) =
        (TensorProduct.rid A M).toLinearMap.comp (J.subtype.lTensor M)
    rw [← LinearMap.comp_assoc, hcommLid]
  let eSource :
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ J))) ≃ₗ[A]
        LinearMap.ker u.hom :=
    (((limit.isoLimitCone ⟨_, hker⟩).symm ≪≫ ModuleCat.kernelIsoKer u).toLinearEquiv)
  let eKer :
      LinearMap.ker u.hom ≃ₗ[A] LinearMap.ker μ :=
    ker_equiv_of_ladder_linear_equiv (A := A)
      (e₁ := TensorProduct.comm A M J) (e₂ := TensorProduct.rid A M) hμ
  -- Proof comment: the fixed-left source owner and the public module owner both compute the
  -- same kernel attached to `0 → J → A → A / J → 0`.
  refine ⟨?_⟩
  exact eSource.trans eKer

/-- Helper for Lemma 10.99.17: choose the quotient-kernel comparison for the fixed-left source
owner at an arbitrary ideal quotient. -/
noncomputable abbrev source_owner_tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module
    (J : Ideal A) :
    (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj (ModuleCat.of A (A ⧸ J))) ≃ₗ[A]
      LinearMap.ker
        (TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype)) :=
  Classical.choice
    (source_owner_tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module_nonempty
      (A := A) (M := M) J)

/-- Helper for Lemma 10.99.17: at an arbitrary ideal quotient `A / J`, the fixed-left source
owner `Tor'₁^A(M, A / J)` agrees with the public module-first owner `Tor₁^A(M, A / J)`. -/
noncomputable def tor_one_source_owner_to_module_public_iso
    (J : Ideal A) :
    ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A (A ⧸ J)))) ≅
      ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ J)))) := by
  let eSource :
      ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ J)))) ≅
        ModuleCat.of A
          (LinearMap.ker
            (TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype))) :=
    (source_owner_tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module
      (A := A) (M := M) J).toModuleIso
  let ePublic :
      ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ J)))) ≅
        ModuleCat.of A
          (LinearMap.ker
            (TensorProduct.lift ((LinearMap.lsmul A M).comp J.subtype))) :=
    (tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module (R := A) (M := M) J).toModuleIso
  -- Proof comment: both degree-`1` owners are compared to the same tensor kernel.
  exact eSource ≪≫ ePublic.symm

/-- Helper for Lemma 10.99.17: quotient-first degree-`1` vanishing at `A / J` implies the
module-first degree-`1` vanishing at the same quotient. This is the exact quotient-only bridge
needed by the final flatness criterion. -/
lemma tor_one_quotient_public_to_module_public_isZero
    (J : Ideal A)
    (hJ :
      IsZero
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ J))))) :
    IsZero
      ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ J)))) := by
  have hSource :
      IsZero
        ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ J)))) := by
    let eSource :
        (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ J)))) ≅
          ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A (A ⧸ J)))) :=
      (tor_one_left_owner_iso (A := A) (M := M)).app (ModuleCat.of A (A ⧸ J))
    -- Proof comment: first move the quotient-first public owner to the fixed-left source owner.
    exact IsZero.of_iso hJ eSource.symm
  -- Proof comment: then use the common tensor-kernel comparison for the quotient `A / J`.
  exact IsZero.of_iso hSource
    (tor_one_source_owner_to_module_public_iso (A := A) (M := M) J).symm

/-- Helper for Lemma 10.99.17: quotient-first degree-`1` vanishing on all finitely generated
ideal quotients is already enough to conclude flatness of `M`. -/
lemma flat_of_tor_one_public_quotient_vanishing_on_fg_ideals
    (hTor :
      ∀ J : Ideal A, J.FG →
        IsZero
          (((((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A (A ⧸ J))))) :
    Module.Flat A M := by
  let htfae := flat_tfae_tor_vanishing_criteria (R := A) (M := M)
  -- Proof comment: this is exactly item `(5) -> (1)` in the standard flatness/Tor criterion.
  refine (htfae.out 0 4).2 ?_
  intro J hJ
  exact
    tor_one_quotient_public_to_module_public_isZero
      (A := A) (M := M) J (hTor J hJ)

end
