import StacksProject_2024.Chap10.Lemma_10_99_17.QuotientModule

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

/-- Helper for Lemma 10.99.17: finite-support direct sums define an endofunctor on `ModuleCat A`.
This is the exact direct-sum owner used in the free-cover bootstrap. -/
noncomputable def moduleCatFinsupp (ι : Type u) : ModuleCat.{u} A ⥤ ModuleCat.{u} A where
  obj X := ModuleCat.of A (ι →₀ X)
  map f := ModuleCat.ofHom (Finsupp.mapRange.linearMap (α := ι) f.hom)
  map_id := by
    intro X
    ext x i
    rfl
  map_comp := by
    intro X Y Z f g
    ext x i
    rfl

/-- Helper for Chap10 Lemma 10 99 17: finite-support sums of a projective `ModuleCat A`
object are projective. -/
lemma moduleCatFinsupp_projective_obj
    (ι : Type u) (X : ModuleCat.{u} A) [Projective X] :
    Projective ((moduleCatFinsupp (A := A) ι).obj X) := by
  classical
  -- Proof comment: first convert categorical projectivity to ordinary module projectivity.
  let _ : Small.{u} A := small_self A
  let hX : Module.Projective A (X : Type u) := inferInstance
  have hXi : ∀ _ : ι, Module.Projective A (X : Type u) := fun _ ↦ hX
  let hD : Module.Projective A (Π₀ _ : ι, (X : Type u)) :=
    @Module.instProjectiveDFinsupp A _ ι (fun _ : ι ↦ (X : Type u)) _ _ hXi
  letI : Module.Projective A (Π₀ _ : ι, (X : Type u)) := hD
  have hFinsupp : Module.Projective A (ι →₀ (X : Type u)) :=
    Module.Projective.of_equiv
      (finsuppLequivDFinsupp A :
        (ι →₀ (X : Type u)) ≃ₗ[A] Π₀ _ : ι, (X : Type u)).symm
  have hObj : Module.Projective A ↑((moduleCatFinsupp (A := A) ι).obj X) := by
    -- Proof comment: unfold the finite-support functor only to identify its carrier.
    simpa [moduleCatFinsupp] using hFinsupp
  letI : Module.Projective A ↑((moduleCatFinsupp (A := A) ι).obj X) := hObj
  -- Proof comment: return from ordinary module projectivity to categorical projectivity.
  exact ModuleCat.projective_of_categoryTheory_projective ((moduleCatFinsupp (A := A) ι).obj X)

/-- Helper for Lemma 10.99.17: applying `Finsupp.mapRange.linearMap` pointwise preserves
exactness. This is the only exactness input needed for the free-module Tor range step. -/
lemma finsupp_mapRange_exact
    {ι X Y Z : Type*}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z]
    (u : X →ₗ[A] Y) (v : Y →ₗ[A] Z) (hExact : Function.Exact u v) :
    Function.Exact
      (Finsupp.mapRange.linearMap (α := ι) u)
      (Finsupp.mapRange.linearMap (α := ι) v) := by
  classical
  -- Proof comment: rewrite exactness as equality of kernel and range, identify the kernel
  -- pointwise, and build finite-support preimages on the support of the target family.
  rw [LinearMap.exact_iff] at hExact ⊢
  rw [Finsupp.ker_mapRange]
  ext x
  constructor
  · intro hx
    have hpre : ∀ i, ∃ y : X, u y = x i := by
      intro i
      have hx' : x i ∈ LinearMap.range u := by
        simpa [hExact] using hx i
      exact hx'
    let y₀ : ι → X := fun i ↦ if hxi : x i = 0 then 0 else Classical.choose (hpre i)
    have hy₀_mem : ∀ i, y₀ i ≠ 0 → i ∈ x.support := by
      intro i hyi
      rw [Finsupp.mem_support_iff]
      by_contra hxi
      simp [y₀, hxi] at hyi
    refine ⟨Finsupp.onFinset x.support y₀ hy₀_mem, ?_⟩
    ext i
    by_cases hxi : x i = 0
    · simp [Finsupp.onFinset_apply, y₀, hxi]
    · have hyi : u (Classical.choose (hpre i)) = x i := Classical.choose_spec (hpre i)
      simp [Finsupp.onFinset_apply, y₀, hxi, hyi]
  · rintro ⟨y, rfl⟩ i
    rw [hExact]
    refine ⟨y i, ?_⟩
    simp [Finsupp.mapRange.linearMap]

/-- Helper for Lemma 10.99.17: the finite-support functor preserves zero morphisms. This is the
typeclass input required by `mapHomologicalComplex`. -/
instance moduleCatFinsupp_preservesZeroMorphisms (ι : Type u) :
    (moduleCatFinsupp (A := A) ι).PreservesZeroMorphisms where
  map_zero X Y := by
    apply ModuleCat.hom_ext
    ext x
    change ((Finsupp.mapRange.linearMap (α := ι) (0 : X →ₗ[A] Y)) x : ι →₀ Y) = 0
    ext i
    simp

/-- Helper for Chap10 Lemma 10 99 17: the finite-support functor on `ModuleCat A` is additive. -/
instance moduleCatFinsupp_additive (ι : Type u) :
    (moduleCatFinsupp (A := A) ι).Additive where
  map_add {X Y} f g := by
    -- Proof comment: addition of morphisms is checked pointwise on every finite-support
    -- coordinate.
    apply ModuleCat.hom_ext
    ext x
    apply Finsupp.ext
    intro i
    change
      ((Finsupp.mapRange.linearMap (ModuleCat.Hom.hom f + ModuleCat.Hom.hom g)) x) i =
        (((Finsupp.mapRange.linearMap (ModuleCat.Hom.hom f)) x +
          (Finsupp.mapRange.linearMap (ModuleCat.Hom.hom g)) x : ι →₀ Y) i)
    simp [Finsupp.mapRange.linearMap_apply]

/-- Helper for Chap10 Lemma 10 99 17: finite-support families preserve exact short complexes in
`ModuleCat A`. -/
lemma moduleCatFinsupp_map_shortComplex_exact
    (ι : Type u) {S : ShortComplex (ModuleCat A)} (hS : S.Exact) :
    (S.map (moduleCatFinsupp (A := A) ι)).Exact := by
  -- Proof comment: exactness in `ModuleCat` is function-level exactness, and the pointwise
  -- finite-support map preserves exactly that condition.
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  simpa [moduleCatFinsupp] using
    finsupp_mapRange_exact (A := A) (ι := ι) S.f.hom S.g.hom hS

/-- Helper for Chap10 Lemma 10 99 17: the finite-support functor preserves homology. -/
instance moduleCatFinsupp_preservesHomology (ι : Type u) :
    (moduleCatFinsupp (A := A) ι).PreservesHomology := by
  -- Proof comment: preserve homology by preserving exactness of every short complex.
  apply Functor.preservesHomology_of_map_exact
  intro S hS
  exact moduleCatFinsupp_map_shortComplex_exact (A := A) ι hS

/-- Helper for Chap10 Lemma 10 99 17: the finite-support functor preserves projective objects. -/
instance moduleCatFinsupp_preservesProjectiveObjects (ι : Type u) :
    (moduleCatFinsupp (A := A) ι).PreservesProjectiveObjects where
  projective_obj {X} hX := by
    -- Proof comment: reuse the already proved projectivity of finite-support sums of a
    -- projective module object.
    let _ : Projective X := hX
    exact moduleCatFinsupp_projective_obj (A := A) ι X

/-- Helper for Lemma 10.99.17: applying the finite-support functor degreewise to a chain complex
preserves exactness in positive degrees. This packages the pointwise exactness argument needed for
the canonical free-cover bootstrap. -/
lemma moduleCatFinsupp_exactAt_succ
    (ι : Type u) {C : ChainComplex (ModuleCat A) ℕ} (n : ℕ)
    (hC : C.ExactAt (n + 1)) :
    ((((moduleCatFinsupp (A := A) ι).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C)).ExactAt (n + 1) := by
  -- Proof comment: rewrite exactness at degree `n + 1` to the adjacent short complex and then
  -- apply the pointwise `Finsupp` exactness lemma to the two neighboring differentials.
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rw [HomologicalComplex.exactAt_iff' C (n + 2) (n + 1) n (by simp) (by simp)] at hC
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC
  let u₀ : ↑(C.X (n + 2)) →ₗ[A] ↑(C.X (n + 1)) := ((C.sc' (n + 2) (n + 1) n).f).hom
  let v₀ : ↑(C.X (n + 1)) →ₗ[A] ↑(C.X n) := ((C.sc' (n + 2) (n + 1) n).g).hom
  have hC' : Function.Exact u₀ v₀ := hC
  simpa [u₀, v₀, CategoryTheory.Functor.mapHomologicalComplex] using
    finsupp_mapRange_exact (A := A) (ι := ι) u₀ v₀ hC'

/-- Helper for Chap10 Lemma 10 99 17: tensoring on the left by a fixed module commutes
naturally with taking finite-support families. -/
theorem tensorLeft_finsupp_natIso_nonempty
    {M : Type u} [AddCommGroup M] [Module A M] (ι : Type u) :
    Nonempty
      (moduleCatFinsupp (A := A) ι ⋙ tensorLeft (ModuleCat.of A M) ≅
        tensorLeft (ModuleCat.of A M) ⋙ moduleCatFinsupp (A := A) ι) := by
  classical
  -- Proof comment: place the standard finite-support tensor equivalence at each component.
  refine ⟨NatIso.ofComponents (fun X ↦ ?_) ?_⟩
  · exact LinearEquiv.toModuleIso (TensorProduct.finsuppRight A A M X ι)
  · intro X Y g
    -- Proof comment: naturality follows by checking pure tensors and then each support
    -- coordinate.
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m x
    apply Finsupp.ext
    intro i
    change
      ((TensorProduct.finsuppRight A A M Y ι)
        ((LinearMap.lTensor M
          (Finsupp.mapRange.linearMap (α := ι) (ModuleCat.Hom.hom g)))
          (m ⊗ₜ[A] x))) i =
      ((Finsupp.mapRange.linearMap (α := ι)
        (LinearMap.lTensor M (ModuleCat.Hom.hom g)))
        ((TensorProduct.finsuppRight A A M X ι) (m ⊗ₜ[A] x))) i
    simp [TensorProduct.finsuppRight_apply_tmul_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_apply]

/-- Helper for Chap10 Lemma 10 99 17: the natural isomorphism identifying
`M ⊗ (ι →₀ X)` with `ι →₀ (M ⊗ X)` as `X` varies. -/
noncomputable def tensorLeft_finsupp_natIso
    {M : Type u} [AddCommGroup M] [Module A M] (ι : Type u) :
    moduleCatFinsupp (A := A) ι ⋙ tensorLeft (ModuleCat.of A M) ≅
      tensorLeft (ModuleCat.of A M) ⋙ moduleCatFinsupp (A := A) ι :=
  Classical.choice (tensorLeft_finsupp_natIso_nonempty (A := A) (M := M) ι)

/-- Helper for Chap10 Lemma 10 99 17: module-first public Tor vanishing against one copy of
`A / I` propagates to every finite-support free `A / I`-module. -/
lemma tor_module_finsuppQuotient_isZero_of_quotient_isZero
    (n : ℕ) (ι : Type u)
    (h :
      IsZero
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A Ā)))) :
    IsZero
      ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (ι →₀ Ā)))) := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of A Ā) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A Ā)
  let Pfree :
      CategoryTheory.ProjectiveResolution
        ((moduleCatFinsupp (A := A) ι).obj (ModuleCat.of A Ā)) :=
    (moduleCatFinsupp (A := A) ι).mapProjectiveResolution P
  let C : ChainComplex (ModuleCat A) ℕ :=
    (((tensorLeft (ModuleCat.of A M)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex)
  let Cfree : ChainComplex (ModuleCat A) ℕ :=
    (((tensorLeft (ModuleCat.of A M)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj Pfree.complex)
  have hExactC : C.ExactAt (n + 1) := by
    -- Proof comment: compute the module-first public Tor object on the chosen resolution of
    -- `A / I`, then rewrite zero homology as exactness.
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact
      IsZero.of_iso h
        (P.isoLeftDerivedObj (tensorLeft (ModuleCat.of A M)) (n + 1)).symm
  have hExactFinsupp :
      ((((moduleCatFinsupp (A := A) ι).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C)).ExactAt (n + 1) := by
    -- Proof comment: finite-support families preserve the exact tensorized resolution row.
    simpa [C] using moduleCatFinsupp_exactAt_succ (A := A) ι n hExactC
  have hExactFree : Cfree.ExactAt (n + 1) := by
    let e :
        Cfree ≅
          (((moduleCatFinsupp (A := A) ι).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj C) :=
      ((NatIso.mapHomologicalComplex
        (tensorLeft_finsupp_natIso (A := A) (M := M) ι)
        (ComplexShape.down ℕ)).app P.complex)
    -- Proof comment: the tensor comparison identifies the tensorized finite-support resolution
    -- with finite-support families of the original tensorized resolution.
    exact HomologicalComplex.ExactAt.of_iso hExactFinsupp e.symm
  -- Proof comment: exactness of the tensorized finite-support resolution is the desired
  -- module-first public Tor vanishing.
  refine IsZero.of_iso ?_
    (Pfree.isoLeftDerivedObj (tensorLeft (ModuleCat.of A M)) (n + 1))
  simpa [Cfree, Pfree, moduleCatFinsupp] using hExactFree.isZero_homology

end
