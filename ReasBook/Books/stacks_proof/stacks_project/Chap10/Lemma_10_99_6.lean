import Mathlib
import StacksProject_2024.Chap10.Remark_10_75_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Helper for Lemma 10.99.6: Tor-vanishing is preserved under linear equivalence in the left
module variable. -/
private lemma isZero_tor_one_of_linearEquiv_left
    {X Y : Type u} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (e : X ≃ₗ[R] Y) (hX : IsZero (Tor₁[R](X, M))) :
    IsZero (Tor₁[R](Y, M)) := by
  -- Functoriality of `Tor₁` in the left variable transports vanishing across the induced module
  -- isomorphism.
  change IsZero ((((Functor.flip (Tor (ModuleCat R) 1)).obj (ModuleCat.of R M)).obj
    (ModuleCat.of R Y)))
  have hX' :
      IsZero ((((Functor.flip (Tor (ModuleCat R) 1)).obj (ModuleCat.of R M)).obj
        (ModuleCat.of R X))) := by
    simpa using hX
  exact IsZero.of_iso hX'
    ((((Functor.flip (Tor (ModuleCat R) 1)).obj (ModuleCat.of R M)).mapIso
      e.toModuleIso).symm)

/-- Helper for Lemma 10.99.6: a subsingleton left module has vanishing degree-`1` Tor. -/
private lemma isZero_tor_one_of_subsingleton_left
    {X : Type u} [AddCommGroup X] [Module R X] [Subsingleton X] :
    IsZero (Tor₁[R](X, M)) := by
  -- A subsingleton left module makes tensoring on the left the zero functor, so the homology
  -- object defining the first derived functor vanishes.
  change IsZero
    (((Functor.leftDerived ((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R X)) 1).obj
      (ModuleCat.of R M)))
  let F : ModuleCat R ⥤ ModuleCat R := (tensoringLeft (ModuleCat R)).obj (ModuleCat.of R X)
  have hZeroX : IsZero (ModuleCat.of R X) :=
    ModuleCat.isZero_of_subsingleton (ModuleCat.of R X)
  have hFobj : ∀ Y, IsZero (F.obj Y) := by
    intro Y
    dsimp [F]
    simpa using (((tensoringRight (ModuleCat R)).obj Y).map_isZero hZeroX)
  refine IsZero.of_iso ?_ ((projectiveResolution (ModuleCat.of R M)).isoLeftDerivedObj F 1)
  erw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_of_isZero_X₂ _ (hFobj _)

/-- Helper for Lemma 10.99.6: every simple module over a local ring is linearly equivalent to the
residue field. -/
private theorem simple_module_equiv_residueField
    {X : Type u} [AddCommGroup X] [Module R X] [IsSimpleModule R X] :
    Nonempty (X ≃ₗ[R] ResidueField R) := by
  obtain ⟨I, hImax, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule R X)
  have hI : I = maximalIdeal R := IsLocalRing.eq_maximalIdeal hImax
  -- Over a local ring the unique maximal ideal is the annihilator ideal of every simple module.
  subst hI
  simpa [IsLocalRing.ResidueField] using ⟨e⟩

/-- Helper for Lemma 10.99.6: `tor_flip_iso` identifies the target owner `X ↦ Tor₁^R(X, M)` with
the fixed-left source owner `X ↦ Tor'₁^R(M, X)`. -/
private noncomputable def tor_one_left_owner_iso
    (M : ModuleCat R) :
    (((Tor (ModuleCat R) 1).flip).obj M) ≅ ((Tor' (ModuleCat R) 1).obj M) where
  hom :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat R) 1).hom.app X).app M)
      naturality := by
        intro X Y f
        -- Naturality of `tor_flip_iso` in the first Tor variable becomes naturality of the fixed
        -- right-variable owner after evaluation at `M`.
        simpa using congrArg (fun α => α.app M) ((tor_flip_iso (ModuleCat R) 1).hom.naturality f) }
  inv :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat R) 1).inv.app X).app M)
      naturality := by
        intro X Y f
        -- The inverse comparison is natural for the same reason.
        simpa using congrArg (fun α => α.app M) ((tor_flip_iso (ModuleCat R) 1).inv.naturality f) }
  hom_inv_id := by
    ext X x
    -- The componentwise inverse law is inherited from `tor_flip_iso` after evaluation at `M`.
    have h := congrArg (fun α => α.app M) ((tor_flip_iso (ModuleCat R) 1).hom_inv_id_app X)
    simpa using congrArg (fun f => f x) (congrArg ModuleCat.Hom.hom h)
  inv_hom_id := by
    ext X x
    -- The same componentwise argument proves the other inverse law.
    have h := congrArg (fun α => α.app M) ((tor_flip_iso (ModuleCat R) 1).inv_hom_id_app X)
    simpa using congrArg (fun f => f x) (congrArg ModuleCat.Hom.hom h)

/-- Helper for Lemma 10.99.6: an exact row with both adjacent maps zero has zero middle term. -/
private theorem isZero_of_exact_zero_zero
    {X₁ X₂ X₃ : ModuleCat R} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}
    (hExact : Function.Exact f.hom g.hom) (hf : f = 0) (hg : g = 0) :
    IsZero X₂ := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk f.hom g.hom (Function.Exact.linearMap_comp_eq_zero hExact)
  have hS : S.Exact := by
    -- Repackage the function-level exactness as exactness of the corresponding short complex.
    simpa [S] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S := S)).2 hExact
  -- Exactness with both adjacent maps zero forces the middle object to vanish.
  simpa [S] using hS.isZero_X₂ hf hg

/-- Helper for Lemma 10.99.6: the fixed-left source owner `X ↦ Tor'₁^R(M, X)` is exact on a short
exact sequence of modules. -/
private theorem source_owner_tor_one_exact_of_shortExact
    (M : ModuleCat R) {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact) :
    Function.Exact ((((Tor' (ModuleCat R) 1).obj M).map S.f).hom)
      ((((Tor' (ModuleCat R) 1).obj M).map S.g).hom) := by
  -- Route correction: the source-faithful fixed-left exactness theorem is now exposed publicly in
  -- Lemma `10.75.2`, so this file only needs the local adapter.
  simpa using ModuleCat.source_owner_tor_one_exact_of_shortExact (R := R) M hS

/-- Helper for Lemma 10.99.6: for a short exact sequence `0 → A → B → C → 0`, vanishing of the
outer degree-`1` Tor terms forces vanishing of the middle term. -/
private theorem isZero_tor_one_of_shortExact_of_outer_vanishing
    {A B C : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf_injective : Function.Injective f) (hg_surjective : Function.Surjective g)
    (hfg_exact : Function.Exact f g)
    (hA : IsZero (Tor₁[R](A, M))) (hC : IsZero (Tor₁[R](C, M))) :
    IsZero (Tor₁[R](B, M)) := by
  -- Route correction: the usable `tor_flip_iso` bridge lands in the fixed-left source owner
  -- `X ↦ Tor'₁^R(M, X)`, so we transport the target row there before using source-owner exactness.
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.moduleCatMk f g (Function.Exact.linearMap_comp_eq_zero hfg_exact)
  have hS : S.ShortExact := by
    -- Package the given injective/surjective/exact row as a short exact sequence in `ModuleCat`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [S] using hfg_exact
    · simpa [S] using (ModuleCat.mono_iff_injective (ModuleCat.ofHom f)).2 hf_injective
    · simpa [S] using (ModuleCat.epi_iff_surjective (ModuleCat.ofHom g)).2 hg_surjective
  let e := tor_one_left_owner_iso (R := R) (ModuleCat.of R M)
  have hA₀ :
      IsZero ((((Tor (ModuleCat R) 1).flip).obj (ModuleCat.of R M)).obj (ModuleCat.of R A)) := by
    -- Rewrite the left outer term in the fixed-right owner shape expected by `e`.
    simpa using hA
  have hA' :
      IsZero ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R A))) := by
    -- Move the left outer vanishing hypothesis into the source owner.
    exact IsZero.of_iso hA₀ (e.app (ModuleCat.of R A)).symm
  have hC₀ :
      IsZero ((((Tor (ModuleCat R) 1).flip).obj (ModuleCat.of R M)).obj (ModuleCat.of R C)) := by
    -- Rewrite the right outer term in the fixed-right owner shape expected by `e`.
    simpa using hC
  have hC' :
      IsZero ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R C))) := by
    -- Move the right outer vanishing hypothesis into the source owner.
    exact IsZero.of_iso hC₀ (e.app (ModuleCat.of R C)).symm
  have hExact :
      Function.Exact ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f).hom)
        ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g).hom) := by
    -- This is the degree-`1` exactness row for the fixed-left source owner.
    simpa [S] using source_owner_tor_one_exact_of_shortExact (R := R) (ModuleCat.of R M) hS
  have hLeft :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.f) = 0 :=
    hA'.eq_of_src _ _
  have hRight :
      (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).map S.g) = 0 :=
    hC'.eq_of_tgt _ _
  have hB' :
      IsZero ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R B))) := by
    -- Exactness with zero outer terms kills the middle source-owner object.
    simpa [S] using isZero_of_exact_zero_zero hExact hLeft hRight
  -- Transport the middle vanishing statement back to the target owner.
  have hB₀ :
      IsZero ((((Tor (ModuleCat R) 1).flip).obj (ModuleCat.of R M)).obj (ModuleCat.of R B)) := by
    exact IsZero.of_iso hB' (e.app (ModuleCat.of R B))
  simpa using hB₀

/- Domain-style sampling:
- primary domain: low-degree `Tor₁` over a local ring, propagated from the residue field to
  finite-length modules in the textbook source-facing argument order;
- sampled owner declarations of the same kind:
  `CategoryTheory.Tor`,
  `CategoryTheory.isZero_Tor_succ_of_projective`,
  `ModuleCat.torTensorSixTermSequence_exact`,
  `CategoryTheory.tor_flip_iso`;
- best owner abstraction: the homological owner is the canonical bifunctor
  `CategoryTheory.Tor (ModuleCat R) 1`, while the induction owner on the finite-length source
  module is `IsFiniteLength R N`;
- primitive data vs derived API: the primitive data are only the fixed right `R`-module `M`, the
  local ring `R`, and the finite-length source module `N`. The vanishing statement below is
  derived API; the proof may pass through the canonical exact-sequence orientation
  `Tor₁^R(M, -)` via `tor_flip_iso`, but that symmetry comparison is bridge data rather than the
  main public statement.

Source/core/bridge triage:
- `source-facing`: Lemma 10.99.6, propagating vanishing of `Tor₁^R(ResidueField R, M)` to
  `Tor₁^R(N, M)` for finite-length `N`;
- `core/canonical`: `CategoryTheory.Tor (ModuleCat R) 1` and `IsFiniteLength R N`;
- `bridge/view`: the composition-series reduction to simple factors and the symmetry comparison
  `tor_flip_iso` used to move to the exact-sequence-friendly orientation belong to the proof, not
  to the public statement.
-/

-- Proof sketch: argue by induction on a finite-length composition series for `N`. Use
-- `tor_flip_iso` only as an internal bridge to pass to the exact-sequence-friendly orientation
-- `Tor₁^R(M, -)`. The base case is the simple-module case, which over a local ring identifies `N`
-- with `ResidueField R`. For the induction step, splice a short exact sequence with smaller
-- finite-length subquotients and apply the six-term exact Tor sequence from Lemma `10.75.2`.
/-- Lemma 10.99.6: if `Tor₁^R(ResidueField R, M)` vanishes for a local ring `R`, then
`Tor₁^R(N, M)` vanishes for every finite-length `R`-module `N`. -/
@[stacks 00MJ]
theorem isZero_tor_one_of_isFiniteLength_of_residueField_vanishing
    (hκ : IsZero (Tor₁[R](ResidueField R, M))) (hN : IsFiniteLength R N) :
    IsZero (Tor₁[R](N, M)) := by
  induction hN with
  | of_subsingleton =>
      -- The zero-length base case is a subsingleton module, whose higher Tor vanishes because it
      -- is projective.
      exact isZero_tor_one_of_subsingleton_left (R := R) (M := M)
  | @of_simple_quotient N _ _ P _ hP ih =>
      have hQuot : IsZero (Tor₁[R](N ⧸ P, M)) := by
        let _ : IsSimpleModule R (N ⧸ P) := inferInstance
        obtain ⟨e⟩ := simple_module_equiv_residueField (R := R) (X := N ⧸ P)
        -- The simple quotient is a copy of the residue field over a local ring.
        exact isZero_tor_one_of_linearEquiv_left (R := R) (M := M) e.symm hκ
      -- The induction step is the short exact sequence `0 → P → N → N ⧸ P → 0`.
      exact isZero_tor_one_of_shortExact_of_outer_vanishing
        (R := R) (M := M) P.subtype P.mkQ Subtype.val_injective (Submodule.mkQ_surjective P)
        (LinearMap.exact_subtype_mkQ P) ih hQuot

end
