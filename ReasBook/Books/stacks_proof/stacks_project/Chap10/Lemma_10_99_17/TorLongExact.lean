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

/-- Helper for Lemma 10.99.17: the source-owner `Tor'` is definitionally the left-derived functor
of tensoring in the second variable and evaluating at the fixed module `M`. -/
theorem source_tor_owner_eq_leftDerived_obj
    (X : ModuleCat A) (n : ℕ) :
    (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj X) =
      ((tensorRight X).leftDerived n).obj (ModuleCat.of A M) := by
  -- This is the definitional expansion of the source-owner orientation.
  rfl

/-- Helper for Lemma 10.99.17: categorical projectivity of `ModuleCat.of A X` implies the usual
module-theoretic projectivity of `X`. This is the flatness bridge needed degreewise on the chosen
projective resolution of `M`. -/
private theorem module_projective_of_categorical_projective
    (X : Type u) [AddCommGroup X] [Module A X]
    (hX : Projective (ModuleCat.of A X)) :
    Module.Projective A X := by
  -- Translate the categorical lifting property against epimorphisms into the standard module
  -- lifting property against surjective linear maps.
  let _ : Small.{u} A := small_self A
  refine Module.Projective.of_lifting_property ?_
  intro P Q _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of A X) := hX
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Lemma 10.99.17: exactness is preserved when the middle term is replaced by a
linearly equivalent module and the adjacent maps are conjugated accordingly. -/
private theorem exact_conj_middle
    {X₁ X₂ X₂' X₃ : Type u}
    [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
    [AddCommGroup X₂'] [Module A X₂'] [AddCommGroup X₃] [Module A X₃]
    {u : X₁ →ₗ[A] X₂} {v : X₂ →ₗ[A] X₃} (e : X₂ ≃ₗ[A] X₂')
    (hExact : Function.Exact u v) :
    Function.Exact (e.toLinearMap.comp u) (v.comp e.symm.toLinearMap) := by
  -- Rewrite exactness via kernel and range, then transport both sides across the equivalence.
  rw [LinearMap.exact_iff] at hExact
  rw [LinearMap.exact_iff]
  rw [LinearMap.ker_comp, LinearMap.range_comp, Submodule.map_equiv_eq_comap_symm]
  simpa [hExact]

/-- Helper for Lemma 10.99.17: tensoring a short exact row on the left by a projective module
preserves short exactness. This is the degreewise exactness input for the source-owner long exact
sequence built from the fixed projective resolution of `M`. -/
theorem tensorLeft_map_shortExact_of_projective
    (P : ModuleCat A) [Projective P] {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    (S.map (tensorLeft P)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Projective modules are flat, so exactness survives after tensoring on the left by `P`.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    let _ : Module.Projective A P :=
      module_projective_of_categorical_projective (A := A) P inferInstance
    let _ : Module.Flat A P := Module.Flat.of_projective
    have hExactBase : Function.Exact S.f.hom S.g.hom := by
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    simpa [ModuleCat.hom_whiskerLeft] using
      (Module.Flat.lTensor_exact P hExactBase)
  · -- The first map stays injective after tensoring on the left by a flat module.
    exact (ModuleCat.mono_iff_injective _).2 <| by
      let _ : Module.Projective A P :=
        module_projective_of_categorical_projective (A := A) P inferInstance
      let _ : Module.Flat A P := Module.Flat.of_projective
      have hu : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective _).1 hS.mono_f
      simpa [ModuleCat.hom_whiskerLeft] using
        (Module.Flat.lTensor_preserves_injective_linearMap (M := P) S.f.hom hu)
  · -- Surjectivity of the quotient map is preserved by left tensoring.
    exact (ModuleCat.epi_iff_surjective _).2 <| by
      have hv : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective _).1 hS.epi_g
      simpa [ModuleCat.hom_whiskerLeft] using
        (LinearMap.lTensor_surjective P hv)

/-- Helper for Lemma 10.99.17: computing `Tor'ₙ(M, X)` on the fixed projective resolution of `M`
identifies it with the `n`th homology of the tensorized resolution. -/
noncomputable def source_owner_tor_projective_resolution_iso
    (X : ModuleCat A) (n : ℕ) :
    (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj X) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.down ℕ) n).obj
        (((tensorRight X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (CategoryTheory.ProjectiveResolution.complex
            (CategoryTheory.projectiveResolution (ModuleCat.of A M)))) := by
  -- The source-owner `Tor'` is computed by the chosen projective resolution of the fixed module.
  erw [source_tor_owner_eq_leftDerived_obj (A := A) (M := M) X n]
  exact
    (CategoryTheory.projectiveResolution (ModuleCat.of A M)).isoLeftDerivedObj
      (tensorRight X) n

/-- Helper for Lemma 10.99.17: a short exact row
`0 → X₁ → X₂ → X₃ → 0` gives the source-owner exact prefix
`Tor'_{n+1}(M, X₃) → Tor'_n(M, X₁) → Tor'_n(M, X₂)`. This is the higher-degree exact row used in
the source proof's dimension-shifting step for modules annihilated by the whole ideal. -/
theorem source_owner_tor_succ_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    ∃ δ :
        (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁),
      Function.Exact δ.hom ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f).hom) := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let φ :
      ((tensorRight (S.X₁ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₂ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} A)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
  let ψ :
      ((tensorRight (S.X₂ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₃ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} A)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
  have hzero : φ ≫ ψ = 0 := by
    -- The tensorized chain maps still compose to zero because `S.f ≫ S.g = 0`.
    refine HomologicalComplex.Hom.ext ?_
    apply funext
    intro k
    apply ModuleCat.hom_ext
    ext x
    dsimp [φ, ψ]
    rw [← ModuleCat.hom_comp]
    rw [← MonoidalCategory.whiskerLeft_comp, S.zero]
    rw [ModuleCat.hom_whiskerLeft]
    change (LinearMap.lTensor (P.complex.X k) (0 : S.X₁ →ₗ[A] S.X₃)) x =
      (0 : P.complex.X k ⊗[A] S.X₁ →ₗ[A] P.complex.X k ⊗[A] S.X₃) x
    simp
  let T : ShortComplex (ChainComplex (ModuleCat.{u} A) ℕ) := ShortComplex.mk φ ψ hzero
  have hT : T.ShortExact := by
    -- Tensoring each degree of the chosen projective resolution with `S` stays short exact.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
    intro k
    simpa [T, φ, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
      ModuleCat.hom_whiskerLeft] using
      tensorLeft_map_shortExact_of_projective (A := A) (P := P.complex.X k) (S := S) hS
  let eLeft :
      (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ≅ T.X₃.homology (n + 1) :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₃ (n + 1)
  let eMid :
      (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁) ≅ T.X₁.homology n :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₁ n
  let eRight :
      (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₂) ≅ T.X₂.homology n :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₂ n
  have hRaw :
      Function.Exact (hT.δ (n + 1) n (by simp)).hom (HomologicalComplex.homologyMap T.f n).hom := by
    -- The homology long exact sequence supplies the `(n + 1, n)` exact window.
    exact
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hT (n + 1) n (by simp)))).1
        (hT.homology_exact₁ (n + 1) n (by simp))
  have hPre :
      Function.Exact
        ((hT.δ (n + 1) n (by simp)).hom.comp eLeft.toLinearEquiv.toLinearMap)
        (HomologicalComplex.homologyMap T.f n).hom := by
    -- Changing only the source of the first map is harmless because `eLeft` is bijective.
    simpa using
      (LinearEquiv.precomp_exact_iff_exact (e := eLeft.toLinearEquiv)).2 hRaw
  have hMid :
      Function.Exact
        (eMid.symm.toLinearEquiv.toLinearMap.comp
          (((hT.δ (n + 1) n (by simp)).hom).comp eLeft.toLinearEquiv.toLinearMap))
        ((HomologicalComplex.homologyMap T.f n).hom.comp eMid.toLinearEquiv.toLinearMap) := by
    -- Conjugate the middle term from raw homology to the source-owner `Tor'_n(M, S.X₁)`.
    exact exact_conj_middle (A := A) (e := eMid.symm.toLinearEquiv) hPre
  have hMapCat :
      (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f) =
        eMid.hom ≫ HomologicalComplex.homologyMap T.f n ≫ eRight.inv := by
    -- The source-owner map is exactly the homology map of the tensorized chain map.
    simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
      (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
        ((tensoringRight (ModuleCat.{u} A)).map S.f) P n)
  have hMap :
      (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f).hom =
        eRight.symm.toLinearEquiv.toLinearMap.comp
          ((HomologicalComplex.homologyMap T.f n).hom.comp eMid.toLinearEquiv.toLinearMap) := by
    exact congrArg ModuleCat.Hom.hom hMapCat
  let δ :
      (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ⟶
        (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁) :=
    ModuleCat.ofHom
      (eMid.symm.toLinearEquiv.toLinearMap.comp
        (((hT.δ (n + 1) n (by simp)).hom).comp eLeft.toLinearEquiv.toLinearMap))
  refine ⟨δ, ?_⟩
  -- Finally transport the target from raw homology to the source-owner endpoint `Tor'_n(M, S.X₂)`.
  rw [hMap]
  have hPost :
      Function.Exact δ.hom
        (eRight.symm.toLinearEquiv.toLinearMap.comp
          ((HomologicalComplex.homologyMap T.f n).hom.comp eMid.toLinearEquiv.toLinearMap)) := by
    simpa [δ] using
      (LinearEquiv.postcomp_exact_iff_exact (e := eRight.symm.toLinearEquiv)).2 hMid
  simpa using hPost

/-- Helper for Lemma 10.99.17: a short exact row
`0 → X₁ → X₂ → X₃ → 0` gives the fixed-left source-owner five-term exact row
`Tor'_{n+1}(M, X₁) → Tor'_{n+1}(M, X₂) → Tor'_{n+1}(M, X₃) → Tor'_n(M, X₁) → Tor'_n(M, X₂) →
Tor'_n(M, X₃)`. This is the full long-exact-sequence fragment used by the source proof's
whole-ideal bootstrap and generator descent. -/
theorem source_owner_tor_five_term_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    ∃ δ :
        (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁),
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g)
        δ
        (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g)).Exact := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let φ :
      ((tensorRight (S.X₁ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₂ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} A)).map S.f)
      (ComplexShape.down ℕ)).app P.complex)
  let ψ :
      ((tensorRight (S.X₂ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex ⟶
        ((tensorRight (S.X₃ : ModuleCat.{u} A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          P.complex :=
    ((NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat.{u} A)).map S.g)
      (ComplexShape.down ℕ)).app P.complex)
  have hzero : φ ≫ ψ = 0 := by
    -- Proof comment: tensoring the short exact row degreewise preserves the relation `S.f ≫ S.g = 0`.
    refine HomologicalComplex.Hom.ext ?_
    apply funext
    intro k
    apply ModuleCat.hom_ext
    ext x
    dsimp [φ, ψ]
    rw [← ModuleCat.hom_comp]
    rw [← MonoidalCategory.whiskerLeft_comp, S.zero]
    rw [ModuleCat.hom_whiskerLeft]
    change (LinearMap.lTensor (P.complex.X k) (0 : S.X₁ →ₗ[A] S.X₃)) x =
      (0 : P.complex.X k ⊗[A] S.X₁ →ₗ[A] P.complex.X k ⊗[A] S.X₃) x
    simp
  let T : ShortComplex (ChainComplex (ModuleCat.{u} A) ℕ) := ShortComplex.mk φ ψ hzero
  have hT : T.ShortExact := by
    -- Proof comment: every projective term in the chosen resolution is flat, so the row remains
    -- short exact after tensoring on the left by that term.
    refine HomologicalComplex.shortExact_of_degreewise_shortExact T ?_
    intro k
    simpa [T, φ, ψ, CategoryTheory.Functor.mapHomologicalComplex_map_f,
      ModuleCat.hom_whiskerLeft] using
      tensorLeft_map_shortExact_of_projective (A := A) (P := P.complex.X k) (S := S) hS
  let eHighX₁ :
      (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₁) ≅ T.X₁.homology (n + 1) :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₁ (n + 1)
  let eHighX₂ :
      (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₂) ≅ T.X₂.homology (n + 1) :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₂ (n + 1)
  let eHighX₃ :
      (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ≅ T.X₃.homology (n + 1) :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₃ (n + 1)
  let eLowX₁ :
      (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁) ≅ T.X₁.homology n :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₁ n
  let eLowX₂ :
      (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₂) ≅ T.X₂.homology n :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₂ n
  let eLowX₃ :
      (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₃) ≅ T.X₃.homology n :=
    source_owner_tor_projective_resolution_iso (A := A) (M := M) S.X₃ n
  have hHighMapF :
      (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f) ≫ eHighX₂.hom =
        eHighX₁.hom ≫ HomologicalComplex.homologyMap T.f (n + 1) := by
    -- Proof comment: the degree-`n + 1` source-owner map is the homology map of the tensorized
    -- projective-resolution chain map.
    have hMap :
        (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f) =
          eHighX₁.hom ≫ HomologicalComplex.homologyMap T.f (n + 1) ≫ eHighX₂.inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.f) P (n + 1))
    rw [hMap]
    simp [Category.assoc]
  have hHighMapG :
      (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g) ≫ eHighX₃.hom =
        eHighX₂.hom ≫ HomologicalComplex.homologyMap T.g (n + 1) := by
    -- Proof comment: the same identification applies to the second degree-`n + 1` arrow.
    have hMap :
        (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g) =
          eHighX₂.hom ≫ HomologicalComplex.homologyMap T.g (n + 1) ≫ eHighX₃.inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.g) P (n + 1))
    rw [hMap]
    simp [Category.assoc]
  have hLowMapF :
      (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f) ≫ eLowX₂.hom =
        eLowX₁.hom ≫ HomologicalComplex.homologyMap T.f n := by
    -- Proof comment: and likewise in degree `n`.
    have hMap :
        (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f) =
          eLowX₁.hom ≫ HomologicalComplex.homologyMap T.f n ≫ eLowX₂.inv := by
      simpa [T, φ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.f) P n)
    rw [hMap]
    simp [Category.assoc]
  have hLowMapG :
      (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g) ≫ eLowX₃.hom =
        eLowX₂.hom ≫ HomologicalComplex.homologyMap T.g n := by
    -- Proof comment: the last degree-`n` source-owner arrow is computed on the same tensorized
    -- projective resolution.
    have hMap :
        (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g) =
          eLowX₂.hom ≫ HomologicalComplex.homologyMap T.g n ≫ eLowX₃.inv := by
      simpa [T, ψ, source_tor_owner_eq_leftDerived_obj, Category.assoc, Tor'] using
        (CategoryTheory.ProjectiveResolution.leftDerived_app_eq
          ((tensoringRight (ModuleCat.{u} A)).map S.g) P n)
    rw [hMap]
    simp [Category.assoc]
  let δ :
      (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ⟶
        (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁) :=
    eHighX₃.hom ≫ hT.δ (n + 1) n (by simp) ≫ eLowX₁.inv
  have hδ :
      δ ≫ eLowX₁.hom =
        eHighX₃.hom ≫ hT.δ (n + 1) n (by simp) := by
    -- Proof comment: the connecting morphism is obtained by conjugating the raw homology
    -- boundary map by the source-owner comparison isomorphisms.
    simp [δ, Category.assoc]
  let eSource :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g)
        δ
        (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g)) ≅
        (ComposableArrows.mk₅
          (HomologicalComplex.homologyMap T.f (n + 1))
          (HomologicalComplex.homologyMap T.g (n + 1))
          (hT.δ (n + 1) n (by simp))
          (HomologicalComplex.homologyMap T.f n)
          (HomologicalComplex.homologyMap T.g n)) :=
    ComposableArrows.isoMk₅
      eHighX₁
      eHighX₂
      eHighX₃
      eLowX₁
      eLowX₂
      eLowX₃
      hHighMapF
      hHighMapG
      hδ
      hLowMapF
      hLowMapG
  refine ⟨δ, ?_⟩
  -- Proof comment: after transporting both degree blocks to the tensorized projective resolution,
  -- exactness is exactly the standard homology-sequence five-term exact row.
  exact (ComposableArrows.exact_iff_of_iso eSource).2 <|
    HomologicalComplex.HomologySequence.composableArrows₅_exact
      (S₁ := T) hT (n + 1) n (by simp)

/-- Helper for Lemma 10.99.17: a short exact row
`0 → X₁ → X₂ → X₃ → 0` gives the quotient-first public exact prefix
`Tor_{n+1}^A(X₃, M) → Tor_n^A(X₁, M) → Tor_n^A(X₂, M)`. This is the public-owner form of the
dimension-shift step needed for the whole-ideal bootstrap. -/
theorem tor_public_succ_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    ∃ δ :
        ((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          ((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj S.X₁),
      Function.Exact δ.hom
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.f).hom) := by
  let eLeft := (tor_left_owner_iso (A := A) (M := M) (n + 1)).app S.X₃
  let eMid := (tor_left_owner_iso (A := A) (M := M) n).app S.X₁
  let eRight := (tor_left_owner_iso (A := A) (M := M) n).app S.X₂
  obtain ⟨δSource, hSource⟩ :=
    source_owner_tor_succ_exact_of_shortExact (A := A) (M := M) hS n
  have hPre :
      Function.Exact
        (δSource.hom.comp eLeft.toLinearEquiv.toLinearMap)
        ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f).hom) := by
    -- Precomposing the connecting morphism by the domain comparison leaves exactness unchanged.
    simpa using
      (LinearEquiv.precomp_exact_iff_exact (e := eLeft.toLinearEquiv)).2 hSource
  have hMid :
      Function.Exact
        (eMid.symm.toLinearEquiv.toLinearMap.comp
          (δSource.hom.comp eLeft.toLinearEquiv.toLinearMap))
        ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f).hom.comp
          eMid.toLinearEquiv.toLinearMap) := by
    -- Conjugate the middle term from the source owner back to the public quotient-first owner.
    exact exact_conj_middle (A := A) (e := eMid.symm.toLinearEquiv) hPre
  have hMap :
      ((((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f).hom.comp
        eMid.toLinearEquiv.toLinearMap) =
        eRight.toLinearEquiv.toLinearMap.comp
          (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.f).hom) := by
    -- Naturality of `tor_left_owner_iso` rewrites the public `Tor` map to the source-owner map.
    simpa using
      (congrArg (fun φ => φ.hom)
        ((tor_left_owner_iso (A := A) (M := M) n).hom.naturality S.f)).symm
  let δ :
      ((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).obj S.X₃) ⟶
        ((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj S.X₁) :=
    ModuleCat.ofHom
      (eMid.symm.toLinearEquiv.toLinearMap.comp
        (δSource.hom.comp eLeft.toLinearEquiv.toLinearMap))
  refine ⟨δ, ?_⟩
  rw [hMap] at hMid
  have hPost :
      Function.Exact δ.hom
        (eRight.toLinearEquiv.toLinearMap.comp
          (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.f).hom)) := by
    simpa [δ] using hMid
  -- Finally remove the target comparison on the right by postcomposing with the inverse equivalence.
  simpa using
    (LinearEquiv.postcomp_exact_iff_exact (e := eRight.toLinearEquiv)).1 hPost

/-- Helper for Lemma 10.99.17: a short exact row
`0 → X₁ → X₂ → X₃ → 0` gives the quotient-first public five-term exact row
`Tor_{n+1}(X₁, M) → Tor_{n+1}(X₂, M) → Tor_{n+1}(X₃, M) → Tor_n(X₁, M) → Tor_n(X₂, M) →
Tor_n(X₃, M)`. This packages exactly the two exactness windows reused later in the source proof. -/
theorem tor_public_five_term_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    ∃ δ :
        ((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          ((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj S.X₁),
      (ComposableArrows.mk₅
        (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.g))
        δ
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.g))).Exact := by
  obtain ⟨δSource, hSource⟩ :=
    source_owner_tor_five_term_exact_of_shortExact (A := A) (M := M) hS n
  let eHighX₁ := (tor_left_owner_iso (A := A) (M := M) (n + 1)).app S.X₁
  let eHighX₂ := (tor_left_owner_iso (A := A) (M := M) (n + 1)).app S.X₂
  let eHighX₃ := (tor_left_owner_iso (A := A) (M := M) (n + 1)).app S.X₃
  let eLowX₁ := (tor_left_owner_iso (A := A) (M := M) n).app S.X₁
  let eLowX₂ := (tor_left_owner_iso (A := A) (M := M) n).app S.X₂
  let eLowX₃ := (tor_left_owner_iso (A := A) (M := M) n).app S.X₃
  have hHighMapF :
      (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.f)) ≫ eHighX₂.hom =
        eHighX₁.hom ≫ (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f) := by
    -- Proof comment: naturality of `tor_left_owner_iso` rewrites the public degree-`n + 1` arrow
    -- into the fixed-left source-owner arrow.
    simpa using (tor_left_owner_iso (A := A) (M := M) (n + 1)).hom.naturality S.f
  have hHighMapG :
      (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.g)) ≫ eHighX₃.hom =
        eHighX₂.hom ≫ (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g) := by
    -- Proof comment: the same owner comparison applies to the second degree-`n + 1` arrow.
    simpa using (tor_left_owner_iso (A := A) (M := M) (n + 1)).hom.naturality S.g
  have hLowMapF :
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.f)) ≫ eLowX₂.hom =
        eLowX₁.hom ≫ (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f) := by
    -- Proof comment: and likewise in degree `n`.
    simpa using (tor_left_owner_iso (A := A) (M := M) n).hom.naturality S.f
  have hLowMapG :
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.g)) ≫ eLowX₃.hom =
        eLowX₂.hom ≫ (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g) := by
    -- Proof comment: this identifies the last public degree-`n` arrow with the source-owner one.
    simpa using (tor_left_owner_iso (A := A) (M := M) n).hom.naturality S.g
  let δ :
      ((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).obj S.X₃) ⟶
        ((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj S.X₁) :=
    eHighX₃.hom ≫ δSource ≫ eLowX₁.inv
  have hδ :
      δ ≫ eLowX₁.hom =
        eHighX₃.hom ≫ δSource := by
    -- Proof comment: the public connecting morphism is obtained by conjugating the source-owner
    -- boundary map by the owner-comparison isomorphisms.
    simp [δ, Category.assoc]
  let ePublic :
      (ComposableArrows.mk₅
        (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.g))
        δ
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.g))) ≅
        (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g)
          δSource
          (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g)) :=
    ComposableArrows.isoMk₅
      eHighX₁
      eHighX₂
      eHighX₃
      eLowX₁
      eLowX₂
      eLowX₃
      hHighMapF
      hHighMapG
      hδ
      hLowMapF
      hLowMapG
  refine ⟨δ, ?_⟩
  -- Proof comment: transporting the public row to the fixed-left source owner reduces the claim
  -- to the source-owner five-term exactness proved on the chosen projective resolution.
  exact (ComposableArrows.exact_iff_of_iso ePublic).2 hSource

/-- Helper for Lemma 10.99.17: from the public five-term row, extract the tail exactness window
`Tor_{n+1}(X₂, M) → Tor_{n+1}(X₃, M) → Tor_n(X₁, M)`. This is the exactness slot used in the
canonical free-cover bootstrap for `I`-annihilated modules. -/
lemma tor_public_tail_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    ∃ δ :
        ((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          ((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).obj S.X₁),
      Function.Exact
        (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.g).hom)
        δ.hom := by
  obtain ⟨δ, hFive⟩ :=
    tor_public_five_term_exact_of_shortExact (A := A) (M := M) hS n
  refine ⟨δ, ?_⟩
  -- Proof comment: exactness at the middle degree-`n + 1` public Tor term is exactly the desired
  -- tail window.
  simpa [ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (ComposableArrows.mk₅
        (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.g))
        δ
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.g))).sc
          hFive.toIsComplex 1)).1
      (hFive.exact 1)

/-- Helper for Lemma 10.99.17: from the public five-term row, extract the same-degree exactness
window `Tor_n(X₁, M) → Tor_n(X₂, M) → Tor_n(X₃, M)`. This is the exactness slot used in the
descending generator step of the source proof. -/
lemma tor_public_middle_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.f).hom)
      (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.g).hom) := by
  obtain ⟨δ, hFive⟩ :=
    tor_public_five_term_exact_of_shortExact (A := A) (M := M) hS n
  -- Proof comment: exactness at the degree-`n` middle term is the last short-complex window of
  -- the public five-term row.
  simpa [ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (ComposableArrows.mk₅
        (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) (n + 1)).flip).obj (ModuleCat.of A M)).map S.g))
        δ
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.f))
        (((((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)).map S.g))).sc
          hFive.toIsComplex 3)).1
      (hFive.exact 3)

end
