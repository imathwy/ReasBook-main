import stacks_proof.stacks_project.Chap10.Lemma_10_99_17.ScalarMultiplication

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A]

/-- Helper for Chap10 Lemma 10 99 17: a projective object of `ModuleCat` gives the usual
module-theoretic projectivity of its underlying module. -/
lemma moduleProjective_of_projective_moduleCat
    (X : Type u) [AddCommGroup X] [Module A X]
    (hX : Projective (ModuleCat.of A X)) :
    Module.Projective A X := by
  -- Proof comment: translate categorical lifting against epimorphisms into the ordinary module
  -- lifting criterion against surjective linear maps.
  let _ : Small.{u} A := small_self A
  refine Module.Projective.of_lifting_property ?_
  intro P Q _ _ _ _ f g hf
  let _ : Projective (ModuleCat.of A X) := hX
  have hf' : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  refine ⟨(Projective.factorThru (ModuleCat.ofHom g) (ModuleCat.ofHom f)).hom, ?_⟩
  exact congrArg ModuleCat.Hom.hom
    (Projective.factorThru_comp (ModuleCat.ofHom g) (ModuleCat.ofHom f))

/-- Helper for Chap10 Lemma 10 99 17: the public quotient-first degree-one exact row may be
written with the literal tensor tail `Y ⊗ -`. -/
lemma torPublicOneTensorExactOfShortExact
    (Y : ModuleCat.{u} A) {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    ∃ δ : ((((Tor (ModuleCat A) 1).flip).obj Y).obj S.X₃) ⟶
        ((tensorLeft Y).obj S.X₁),
      (ComposableArrows.mk₅
        (((((Tor (ModuleCat A) 1).flip).obj Y).map S.f))
        (((((Tor (ModuleCat A) 1).flip).obj Y).map S.g))
        δ
        (((tensorLeft Y).map S.f))
        (((tensorLeft Y).map S.g))).Exact := by
  obtain ⟨δSource, hSource⟩ :=
    source_owner_tor_one_tensor_exact_of_shortExact (A := A) (M := (Y : Type u)) hS
  let eX₁ := (tor_left_owner_iso (A := A) (M := (Y : Type u)) 1).app S.X₁
  let eX₂ := (tor_left_owner_iso (A := A) (M := (Y : Type u)) 1).app S.X₂
  let eX₃ := (tor_left_owner_iso (A := A) (M := (Y : Type u)) 1).app S.X₃
  let δ : ((((Tor (ModuleCat A) 1).flip).obj Y).obj S.X₃) ⟶ ((tensorLeft Y).obj S.X₁) :=
    eX₃.hom ≫ δSource
  have hMapF :
      (((((Tor (ModuleCat A) 1).flip).obj Y).map S.f)) ≫ eX₂.hom =
        eX₁.hom ≫ (((Tor' (ModuleCat A) 1).obj Y).map S.f) := by
    -- Proof comment: degree-one owner transport is natural in the first public variable.
    simpa using (tor_left_owner_iso (A := A) (M := (Y : Type u)) 1).hom.naturality S.f
  have hMapG :
      (((((Tor (ModuleCat A) 1).flip).obj Y).map S.g)) ≫ eX₃.hom =
        eX₂.hom ≫ (((Tor' (ModuleCat A) 1).obj Y).map S.g) := by
    -- Proof comment: apply the same naturality to the second map of the short exact row.
    simpa using (tor_left_owner_iso (A := A) (M := (Y : Type u)) 1).hom.naturality S.g
  have hδ : δ ≫ (Iso.refl ((tensorLeft Y).obj S.X₁)).hom = eX₃.hom ≫ δSource := by
    -- Proof comment: the public connecting morphism is the source connecting morphism after
    -- conjugating the Tor endpoint.
    simp [δ]
  have hTensorF :
      ((tensorLeft Y).map S.f) ≫ (Iso.refl ((tensorLeft Y).obj S.X₂)).hom =
        (Iso.refl ((tensorLeft Y).obj S.X₁)).hom ≫ ((tensorLeft Y).map S.f) := by
    -- Proof comment: the tensor tail is already in the desired public normal form.
    simp
  have hTensorG :
      ((tensorLeft Y).map S.g) ≫ (Iso.refl ((tensorLeft Y).obj S.X₃)).hom =
        (Iso.refl ((tensorLeft Y).obj S.X₂)).hom ≫ ((tensorLeft Y).map S.g) := by
    -- Proof comment: the last tensor map also needs only the identity comparison.
    simp
  let ePublic :
      (ComposableArrows.mk₅
        (((((Tor (ModuleCat A) 1).flip).obj Y).map S.f))
        (((((Tor (ModuleCat A) 1).flip).obj Y).map S.g))
        δ
        (((tensorLeft Y).map S.f))
        (((tensorLeft Y).map S.g))) ≅
        (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) 1).obj Y).map S.f)
          (((Tor' (ModuleCat A) 1).obj Y).map S.g)
          δSource
          (((tensorLeft Y).map S.f))
          (((tensorLeft Y).map S.g))) :=
    ComposableArrows.isoMk₅ eX₁ eX₂ eX₃ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      hMapF hMapG hδ hTensorF hTensorG
  refine ⟨δ, ?_⟩
  -- Proof comment: transport the exact source-owner row across the public/source owner
  -- comparison in degree one.
  exact (ComposableArrows.exact_iff_of_iso ePublic).2 hSource

/-- Helper for Chap10 Lemma 10 99 17: if the right tensor factor is flat, then public
quotient-first `Tor₁` vanishes. -/
lemma torPublicOneIsZeroOfFlatRight
    (X Y : ModuleCat.{u} A) [Module.Flat A (Y : Type u)] :
    IsZero ((((Tor (ModuleCat A) 1).flip).obj Y).obj X) := by
  let P : CategoryTheory.ProjectiveResolution X := CategoryTheory.projectiveResolution X
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk (LinearMap.ker (P.π.f 0).hom).subtype (P.π.f 0).hom
      (by ext x; exact x.2)
  have hS : S.ShortExact := by
    -- Proof comment: use the canonical short exact row `ker(π₀) → P₀ → X` from the projective
    -- resolution.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [S] using LinearMap.exact_subtype_ker_map (P.π.f 0).hom
    · exact (ModuleCat.mono_iff_injective _).2 <| by
        intro x y hxy
        exact Subtype.ext hxy
    · exact (ModuleCat.epi_iff_surjective S.g).2 <| by
        simpa [S] using (ModuleCat.epi_iff_surjective (P.π.f 0)).1 inferInstance
  obtain ⟨δ, hFive⟩ := torPublicOneTensorExactOfShortExact (A := A) Y hS
  have hMiddle : IsZero ((((Tor (ModuleCat A) 1).flip).obj Y).obj S.X₂) := by
    -- Proof comment: the middle term is projective, hence flat in the left public Tor variable.
    let _ : Projective S.X₂ := by
      simpa [S] using (P.projective 0)
    let _ : Module.Projective A (S.X₂ : Type u) :=
      moduleProjective_of_projective_moduleCat (A := A) (S.X₂ : Type u) inferInstance
    let _ : Module.Flat A (S.X₂ : Type u) := Module.Flat.of_projective
    simpa using
      tor_succ_isZero_of_flat_left (A := A) (M := (Y : Type u)) (P := (S.X₂ : Type u)) 0
  have hFirst : (((((Tor (ModuleCat A) 1).flip).obj Y).map S.g)) = 0 :=
    hMiddle.eq_of_src _ _
  have hExactAtTor :
      Function.Exact (((((Tor (ModuleCat A) 1).flip).obj Y).map S.g).hom) δ.hom := by
    -- Proof comment: exactness at `Tor₁(X, Y)` is the second slot of the five-term row.
    simpa [ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((((Tor (ModuleCat A) 1).flip).obj Y).map S.f))
          (((((Tor (ModuleCat A) 1).flip).obj Y).map S.g))
          δ
          (((tensorLeft Y).map S.f))
          (((tensorLeft Y).map S.g))).sc hFive.toIsComplex 1)).1
        (hFive.exact 1)
  have hExactAtTensor : Function.Exact δ.hom (((tensorLeft Y).map S.f).hom) := by
    -- Proof comment: exactness at the tensor term will make the connecting morphism vanish once
    -- the tensor map is known injective.
    simpa [ComposableArrows.sc] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S := (ComposableArrows.mk₅
          (((((Tor (ModuleCat A) 1).flip).obj Y).map S.f))
          (((((Tor (ModuleCat A) 1).flip).obj Y).map S.g))
          δ
          (((tensorLeft Y).map S.f))
          (((tensorLeft Y).map S.g))).sc hFive.toIsComplex 2)).1
        (hFive.exact 2)
  have hTensorInj : Function.Injective (((tensorLeft Y).map S.f).hom) := by
    -- Proof comment: flatness of `Y` preserves injectivity of the kernel inclusion under
    -- tensoring on the left.
    have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).1 hS.mono_f
    simpa [ModuleCat.hom_whiskerLeft] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := (Y : Type u)) S.f.hom hf)
  have hδ : δ = 0 := by
    -- Proof comment: the connecting morphism lands in the kernel of an injective tensor map.
    apply ModuleCat.hom_ext
    ext x
    apply hTensorInj
    exact congrArg (fun φ => φ x) (Function.Exact.linearMap_comp_eq_zero hExactAtTensor)
  have hTarget : IsZero ((((Tor (ModuleCat A) 1).flip).obj Y).obj S.X₃) := by
    -- Proof comment: with both adjacent maps zero, exactness forces the middle `Tor₁` object to
    -- vanish.
    exact isZero_of_exact_zero_zero hExactAtTor hFirst hδ
  simpa [S] using hTarget

/-- Helper for Chap10 Lemma 10 99 17: one dimension-shifting step for public Tor with a flat
right tensor factor. -/
lemma torPublicSuccIsZeroOfFlatRightStep
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) [Projective S.X₂]
    (Y : ModuleCat.{u} A) (n : ℕ)
    (h₁ : IsZero ((((Tor (ModuleCat A) (n + 1)).flip).obj Y).obj S.X₁)) :
    IsZero ((((Tor (ModuleCat A) (n + 2)).flip).obj Y).obj S.X₃) := by
  obtain ⟨δ, hExact⟩ :=
    tor_public_tail_exact_of_shortExact (A := A) (M := (Y : Type u)) (S := S) hS (n + 1)
  have hMiddle : IsZero ((((Tor (ModuleCat A) (n + 2)).flip).obj Y).obj S.X₂) := by
    -- Proof comment: the projective middle object is flat in the left public Tor variable.
    let _ : Module.Projective A (S.X₂ : Type u) :=
      moduleProjective_of_projective_moduleCat (A := A) (S.X₂ : Type u) inferInstance
    let _ : Module.Flat A (S.X₂ : Type u) := Module.Flat.of_projective
    simpa using
      tor_succ_isZero_of_flat_left
        (A := A) (M := (Y : Type u)) (P := (S.X₂ : Type u)) (n + 1)
  have hLeft : (((((Tor (ModuleCat A) (n + 2)).flip).obj Y).map S.g)) = 0 :=
    hMiddle.eq_of_src _ _
  have hRight : δ = 0 := h₁.eq_of_tgt _ _
  -- Proof comment: the tail exactness window with zero adjacent terms kills `Tor_{n+2}(S.X₃,Y)`.
  exact isZero_of_exact_zero_zero hExact hLeft hRight

/-- Helper for Chap10 Lemma 10 99 17: public positive-degree Tor vanishes when the second module
is flat. -/
lemma torPublicSuccIsZeroOfFlatRightObj
    (n : ℕ) (X Y : ModuleCat.{u} A) [Module.Flat A (Y : Type u)] :
    IsZero ((((Tor (ModuleCat A) (n + 1)).flip).obj Y).obj X) := by
  induction n generalizing X with
  | zero =>
      -- Proof comment: degree one is the tensor-injectivity argument on a projective cover.
      exact torPublicOneIsZeroOfFlatRight (A := A) X Y
  | succ n ih =>
      let P : CategoryTheory.ProjectiveResolution X := CategoryTheory.projectiveResolution X
      let S : ShortComplex (ModuleCat A) :=
        ShortComplex.moduleCatMk (LinearMap.ker (P.π.f 0).hom).subtype (P.π.f 0).hom
          (by ext x; exact x.2)
      have hS : S.ShortExact := by
        -- Proof comment: repeat the projective-cover short exact row for the dimension-shift.
        refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
        · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
          simpa [S] using LinearMap.exact_subtype_ker_map (P.π.f 0).hom
        · exact (ModuleCat.mono_iff_injective _).2 <| by
            intro x y hxy
            exact Subtype.ext hxy
        · exact (ModuleCat.epi_iff_surjective S.g).2 <| by
            simpa [S] using (ModuleCat.epi_iff_surjective (P.π.f 0)).1 inferInstance
      let _ : Projective S.X₂ := by
        simpa [S] using (P.projective 0)
      have hKernel : IsZero ((((Tor (ModuleCat A) (n + 1)).flip).obj Y).obj S.X₁) :=
        ih S.X₁
      have hShift :
          IsZero ((((Tor (ModuleCat A) (n + 2)).flip).obj Y).obj S.X₃) :=
        torPublicSuccIsZeroOfFlatRightStep (A := A) hS Y n hKernel
      -- Proof comment: the third object of the projective-cover row is the original module.
      simpa [S] using hShift

/-- Helper for Chap10 Lemma 10 99 17: public positive-degree Tor vanishes when the second module
is flat. -/
lemma tor_public_succ_isZero_of_flat_right
    (n : ℕ) {P Q : Type u} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] [Module.Flat A Q] :
    IsZero ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A P)).obj
      (ModuleCat.of A Q))) := by
  -- Proof comment: convert to quotient-first notation and use the projective-presentation
  -- induction proved above.
  simpa using
    torPublicSuccIsZeroOfFlatRightObj
      (A := A) n (ModuleCat.of A P) (ModuleCat.of A Q)

/-- Helper for Chap10 Lemma 10 99 17: in degree one, vanishing for the module-first quotient
owner transports to the fixed-left source owner through the quotient kernel comparison. -/
lemma sourceOwner_quotient_one_isZero_of_moduleFirstPublic_isZero
    {M : Type u} [AddCommGroup M] [Module A M] {r : ℕ} (f : Fin r → A)
    (h :
      IsZero
        ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))))) :
    IsZero
      ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ Ideal.span (Set.range f))))) := by
  have hflipped :
      IsZero
        ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ Ideal.span (Set.range f))))) := by
    let eModule :
        (((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))) ≅
          ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A (A ⧸ Ideal.span (Set.range f))))) :=
      (tor_one_module_flip_owner_iso (A := A) (M := M)).app
        (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))
    -- Proof comment: `tor_flip_iso` moves the public module-first quotient owner to the flipped
    -- source owner in degree one.
    exact IsZero.of_iso h eModule.symm
  let eSource :
      ((((Functor.flip (Tor' (ModuleCat A) 1)).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ Ideal.span (Set.range f))))) ≅
        ((((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ Ideal.span (Set.range f))))) :=
    tor_one_quotient_flip_to_source_owner_iso (A := A) (M := M) (f := f)
  -- Proof comment: the quotient-specific kernel model identifies the flipped source owner with
  -- the fixed-left source owner.
  exact IsZero.of_iso hflipped eSource.symm

/-- Helper for Chap10 Lemma 10 99 17: public-flipped quotient Tor vanishing in degree `n + 2`
transports to the fixed-left source owner. -/
lemma sourceOwner_quotient_succSucc_isZero_of_publicFlip_isZero
    {M : Type u} [AddCommGroup M] [Module A M] {r : ℕ} (f : Fin r → A)
    (n : ℕ)
    (h :
      IsZero
        (((((Tor (ModuleCat A) (n + 2)).flip).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (A ⧸ Ideal.span (Set.range f)))))) :
    IsZero
      ((((Tor' (ModuleCat A) (n + 2)).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ Ideal.span (Set.range f))))) := by
  -- Proof comment: once the Tor object is in the quotient-first public owner, the existing
  -- `tor_left_owner_iso` comparison gives the fixed-left source owner directly.
  exact
    isZero_sourceOwner_of_isZero_publicFlip
      (A := A) (M := M) (n + 2) h

/-- Helper for Chap10 Lemma 10 99 17: module-first public Tor vanishing transports through
`tor_flip_iso` to the flipped source owner in the same degree. -/
lemma isZero_flippedSource_of_isZero_moduleFirstPublic
    {M K : Type u} [AddCommGroup M] [Module A M] [AddCommGroup K] [Module A K]
    (n : ℕ)
    (h :
      IsZero
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K)))) :
    IsZero
      (((((Functor.flip (Tor' (ModuleCat A) n)).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A K)))) := by
  let e :
      (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj (ModuleCat.of A K)) ≅
        ((((Functor.flip (Tor' (ModuleCat A) n)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K))) :=
    (tor_module_flip_owner_iso (A := A) (M := M) n).app (ModuleCat.of A K)
  -- Proof comment: this is exactly the objectwise component of the already available
  -- public-to-flipped-source owner comparison.
  exact IsZero.of_iso h e.symm

/-- Helper for Chap10 Lemma 10 99 17: flipped source-owner vanishing transports back to
module-first public Tor through `tor_module_flip_owner_iso`. -/
lemma isZero_moduleFirstPublic_of_isZero_flippedSource
    {M K : Type u} [AddCommGroup M] [Module A M] [AddCommGroup K] [Module A K]
    (n : ℕ)
    (h :
      IsZero
        (((((Functor.flip (Tor' (ModuleCat A) n)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K))))) :
    IsZero
      ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A K))) := by
  let e :
      (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj (ModuleCat.of A K)) ≅
        ((((Functor.flip (Tor' (ModuleCat A) n)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K))) :=
    (tor_module_flip_owner_iso (A := A) (M := M) n).app (ModuleCat.of A K)
  -- Proof comment: this is the reverse direction of the same owner comparison, isolating the
  -- remaining gap as public Tor symmetry rather than another source-owner transport.
  exact IsZero.of_iso h e

end
