import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_39_15
import stacks_proof.stacks_project.Chap10.Lemma_10_75_2
import stacks_proof.stacks_project.Chap10.Lemma_10_75_8
import stacks_proof.stacks_project.Chap10.Lemma_10_76_1
import stacks_proof.stacks_project.Chap10.Lemma_10_77_5
import stacks_proof.stacks_project.Chap10.Lemma_10_99_17.Index

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]
variable {r : ℕ} (f : Fin r → A)

/- Domain-style sampling for the finite-generator local criterion for flatness:
- primary domain: commutative algebra of flat and faithfully flat modules, localized away from a
  finite generating family, together with Tor-vanishing over the quotient by the generated ideal;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Module.flat_of_localized_span`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`;
- best owner abstraction: the owners are `Module.Flat` and `Module.FaithfullyFlat`, while
  Tor-vanishing should use the canonical categorical owner `IsZero`, not the derived witness
  `Subsingleton` on the underlying type;
- primitive data: the generating family `f`, the localized flatness hypotheses, and the quotient
  flatness/faithful-flatness hypothesis over `A / (f₁, …, f_r)`;
- derived API: the vanishing statement for the Tor objects against the quotient by
  `Ideal.span (Set.range f)`.

Source/core/bridge triage:
- `source-facing`: the finite-generator local criterion with quotient and Tor hypotheses;
- `core/canonical`: `Module.Flat`, `Module.FaithfullyFlat`, and `IsZero` for vanishing of Tor
  objects;
- `bridge/view`: the chapter-local quotient-flatness and Tor criteria that reduce the source
  statement to the canonical flatness owners. -/

local notation "I" => Ideal.span (Set.range f)
local notation "Ā" => A ⧸ I
local notation "M̄" => M ⧸ (I • (⊤ : Submodule A M))
set_option quotPrecheck false in
local notation "TorQ[" n "]" =>
  (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj (ModuleCat.of A Ā))

/-- Helper for Chap10 Lemma 10 99 17: tensoring on the left by a fixed module agrees naturally with
tensoring on the right by the same module via tensor commutativity. This is the higher-degree
owner bridge behind the quotient-range vanishing step. -/
noncomputable def tensor_left_right_comm_natIso
    {K : Type u} [AddCommGroup K] [Module A K] :
    tensorLeft (ModuleCat.of A K) ≅ tensorRight (ModuleCat.of A K) :=
  BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of A K)

/-- Helper for Chap10 Lemma 10 99 17: the finite-support tensor comparison exists naturally in the
variable being tensored, using `TensorProduct.finsuppRight` componentwise. -/
theorem tensorRight_finsupp_quotient_natIso_nonempty
    (ι : Type u) :
    Nonempty
      (tensorRight (ModuleCat.of A (ι →₀ Ā)) ≅
        tensorRight (ModuleCat.of A Ā) ⋙ moduleCatFinsupp (A := A) ι) := by
  classical
  -- Proof comment: put the standard finite-support tensor equivalence at every object.
  refine ⟨NatIso.ofComponents (fun X ↦ ?_) ?_⟩
  · exact LinearEquiv.toModuleIso (TensorProduct.finsuppRight A A X Ā ι)
  · intro X Y g
    -- Proof comment: naturality is checked on pure tensors and then pointwise on the finite
    -- support coordinate.
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    apply Finsupp.ext
    intro i
    change
      ((TensorProduct.finsuppRight A A Y Ā ι)
        ((LinearMap.rTensor (ι →₀ Ā) (ModuleCat.Hom.hom g)) (x ⊗ₜ[A] y))) i =
      ((Finsupp.mapRange.linearMap (LinearMap.rTensor Ā (ModuleCat.Hom.hom g)))
        ((TensorProduct.finsuppRight A A X Ā ι) (x ⊗ₜ[A] y))) i
    simp [TensorProduct.finsuppRight_apply_tmul_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange_apply]

/-- Helper for Chap10 Lemma 10 99 17: tensoring on the right with a finitely supported free
quotient module is naturally the same as taking finitely supported families after tensoring on the
right with one copy of `A / I`. -/
noncomputable def tensorRight_finsupp_quotient_natIso
    (ι : Type u) :
    tensorRight (ModuleCat.of A (ι →₀ Ā)) ≅
      tensorRight (ModuleCat.of A Ā) ⋙ moduleCatFinsupp (A := A) ι :=
  Classical.choice (tensorRight_finsupp_quotient_natIso_nonempty (A := A) (f := f) ι)

/-- Helper for Chap10 Lemma 10 99 17: vanishing of the fixed-left source owner against one
copy of `A / I` implies vanishing against any finitely supported free `A / I`-module. -/
lemma sourceOwner_finsuppQuotient_isZero_of_sourceOwner_quotient_isZero
    (n : ℕ) (ι : Type u)
    (h :
      IsZero
        ((((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A Ā)))) :
    IsZero
      ((((Tor' (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (ι →₀ Ā)))) := by
  let P : CategoryTheory.ProjectiveResolution (ModuleCat.of A M) :=
    CategoryTheory.projectiveResolution (ModuleCat.of A M)
  let C : ChainComplex (ModuleCat A) ℕ :=
    (((tensorRight (ModuleCat.of A Ā)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex)
  let Cfree : ChainComplex (ModuleCat A) ℕ :=
    (((tensorRight (ModuleCat.of A (ι →₀ Ā))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex)
  have hExactC : C.ExactAt (n + 1) := by
    -- Proof comment: transport the source-owner vanishing to homology of the fixed projective
    -- resolution, then rewrite zero homology as exactness at the same degree.
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact
      IsZero.of_iso h
        (source_owner_tor_projective_resolution_iso
          (A := A) (M := M) (ModuleCat.of A Ā) (n + 1)).symm
  have hExactFinsupp :
      (((moduleCatFinsupp (A := A) ι).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj C).ExactAt (n + 1) := by
    -- Proof comment: finite-support families preserve the exact tensorized resolution row.
    simpa [C] using moduleCatFinsupp_exactAt_succ (A := A) ι n hExactC
  have hExactFree : Cfree.ExactAt (n + 1) := by
    let e :
        Cfree ≅
          (((moduleCatFinsupp (A := A) ι).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj C) :=
      ((NatIso.mapHomologicalComplex
        (tensorRight_finsupp_quotient_natIso (A := A) (f := f) ι)
        (ComplexShape.down ℕ)).app P.complex)
    -- Proof comment: the tensor comparison identifies the free quotient tensor complex with the
    -- finite-support complex, so exactness transfers back across that isomorphism.
    exact HomologicalComplex.ExactAt.of_iso hExactFinsupp e.symm
  -- Proof comment: exactness of the free quotient tensor complex is the desired vanishing of the
  -- fixed-left source-owner Tor object.
  refine IsZero.of_iso ?_
    (source_owner_tor_projective_resolution_iso
      (A := A) (M := M) (ModuleCat.of A (ι →₀ Ā)) (n + 1))
  simpa [Cfree] using hExactFree.isZero_homology

/-- Helper for Chap10 Lemma 10 99 17: localizing the module-first public Tor owner away from `a`
identifies it with the corresponding Tor object over `A[1 / a]`, which vanishes when the
localized module `M[1 / a]` is flat. -/
lemma tor_module_localizedAway_isZero_of_flat_localization
    (a : A) (n : ℕ) {K : Type u} [AddCommGroup K] [Module A K]
    (hflat : Module.Flat (Localization.Away a) (LocalizedModule.Away a M)) :
    IsZero
      (ModuleCat.of (Localization.Away a)
        (LocalizedModule.Away a
          ↑((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K))))) := by
  let S : Type u := Localization.Away a
  let loc : A →+* S := algebraMap A S
  have hlocFlat : loc.Flat := by
    -- Proof comment: localization is flat as an algebra map, so Tor commutes with this base
    -- change.
    simpa [loc, S] using
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away a) (Submonoid.powers a)))
  have hflatTensor : Module.Flat S (S ⊗[A] M) := by
    -- Proof comment: rewrite the assumed localized-module flatness in the tensor-product model.
    simpa [S] using
      (Module.Flat.of_linearEquiv
        ((LocalizedModule.equivTensorProduct (Submonoid.powers a) M).symm))
  let extTensorIso (T : Type u) [AddCommGroup T] [Module A T] :
      (ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
          (ModuleCat.of A T) ≅
        ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] T) := by
    let U : Type u :=
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away a))).obj
        (ModuleCat.of (Localization.Away a) (Localization.Away a))) : Type u)
    letI : IsScalarTower A (Localization.Away a) U :=
      { smul_assoc := by
          intro r s x
          rw [Algebra.smul_def, mul_smul]
          rfl }
    let eLeft : U ≃ₗ[Localization.Away a] Localization.Away a :=
      LinearEquiv.refl (Localization.Away a) (Localization.Away a)
    let eRight : T ≃ₗ[A] T := LinearEquiv.refl A T
    -- Proof comment: scalar extension is tensoring with the restricted scalar copy of the
    -- localization; this identifies that object with the ordinary tensor product.
    exact (TensorProduct.AlgebraTensorModule.congr eLeft eRight).toModuleIso
  have hTargetTensor :
      IsZero
        ((((Tor (ModuleCat S) (n + 1)).obj
            (ModuleCat.of S (S ⊗[A] M))).obj
          (ModuleCat.of S (S ⊗[A] K)))) := by
    -- Proof comment: over the localized ring, the left Tor variable is flat in the tensor model.
    exact
      tor_succ_isZero_of_flat_left
        (A := S) (M := S ⊗[A] K) (n := n) (P := S ⊗[A] M)
  have hTargetCanonical :
      IsZero
        ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
              (ModuleCat.of A M))).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
            (ModuleCat.of A K)))) := by
    let eM := extTensorIso M
    let eK := extTensorIso K
    let eFirst :
        ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
              (ModuleCat.of A M))).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
            (ModuleCat.of A K)))) ≅
          ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] M))).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
            (ModuleCat.of A K)))) :=
      ((Tor (ModuleCat (Localization.Away a)) (n + 1)).mapIso eM).app
        ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
          (ModuleCat.of A K))
    let eSecond :
        ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] M))).obj
          ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
            (ModuleCat.of A K)))) ≅
          ((((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
            (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] M))).obj
          (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] K)))) := by
      exact
        ((Tor (ModuleCat (Localization.Away a)) (n + 1)).obj
          (ModuleCat.of (Localization.Away a) (Localization.Away a ⊗[A] M))).mapIso eK
    let eTarget := eFirst ≪≫ eSecond
    -- Proof comment: transport the localized flat-Tor vanishing across the two object
    -- normalizations.
    exact IsZero.of_iso hTargetTensor eTarget
  have hTarget :
      IsZero
        ((((Tor (ModuleCat S) (n + 1)).obj
            ((ModuleCat.extendScalars loc).obj (ModuleCat.of A M))).obj
          ((ModuleCat.extendScalars loc).obj (ModuleCat.of A K)))) := by
    -- Proof comment: return from the explicit localization spelling to the local aliases used by
    -- the base-change theorem.
    simpa [S, loc] using hTargetCanonical
  have hIso : IsIso (torBaseChangeHom loc hlocFlat
      (ModuleCat.of A M) (ModuleCat.of A K) (n + 1)) := by
    -- Proof comment: flat base change identifies the localized old Tor object with Tor over
    -- `A[1/a]`.
    simpa [loc, S] using
      (flat_tor_base_change_map_isIso
        (f := loc) (hf := hlocFlat) (M := M) (N := K) (i := n + 1))
  have hSource :
      IsZero
        ((ModuleCat.extendScalars loc).obj
          ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K)))) := by
    -- Proof comment: move the target vanishing back through the base-change isomorphism.
    exact IsZero.of_iso hTarget
      (asIso (torBaseChangeHom loc hlocFlat (ModuleCat.of A M) (ModuleCat.of A K) (n + 1)))
  have hSourceTensorOwner :
      IsZero
        ((ModuleCat.extendScalars (algebraMap A (Localization.Away a))).obj
          ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K)))) := by
    -- Proof comment: align the algebra-map spelling with the tensor-product object comparison.
    simpa [S, loc] using hSource
  let eSourceTensor :=
    extTensorIso
      ↑((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A K)))
  have hTensor :
      IsZero
        (ModuleCat.of (Localization.Away a)
          (Localization.Away a ⊗[A]
            ↑((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
              (ModuleCat.of A K))))) := by
    -- Proof comment: the scalar-extension object is now in the tensor-product normal form.
    exact IsZero.of_iso hSourceTensorOwner eSourceTensor.symm
  -- Proof comment: convert the tensor-product base change back to the literal localized module.
  exact isZero_away_localizedModule_of_isZero_tensorProduct (A := A) a hTensor

/-- Helper for Chap10 Lemma 10 99 17: the source proof's remaining global step is to show that
the public module-first owner `Tor₁^A(M, -)` vanishes on every `A`-module after bootstrapping from
modules killed by `I` and descending on the generators `fᵢ`. -/
lemma tor_one_module_vanishes_of_localized_generators_and_quotient_and_tor_vanishing
    (hlocal : ∀ i : Fin r, Module.Flat (Localization.Away (f i)) (LocalizedModule.Away (f i) M))
    (hquot : Module.Flat Ā M̄)
    (htor : ∀ i : Fin (r + 1), IsZero (TorQ[i.1 + 1])) :
    ∀ (N : Type u) [AddCommGroup N] [Module A N],
      IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A N))) := by
  intro N _ _
  -- Route correction: the old proof passed through quotient-first public Tor and then through the
  -- stuck fixed-quotient source-owner symmetry. The current proof delegates to the new
  -- module-first descent owner, where the quotient hypothesis already has the right orientation.
  exact
    tor_module_one_vanishes_of_generator_descent
      (A := A) (M := M) (f := f) hlocal hquot htor N

-- Proof sketch: argue by induction on the number of generators. The base case `r = 0` is
-- immediate because `I = Ideal.span (Set.range f) = ⊥`, so `Ā = A` and `M̄ = M`. For the step,
-- first use the quotient-flatness and Tor-vanishing hypotheses to propagate vanishing of
-- `Tor_i^A(M, K)` to all modules `K` annihilated by the whole ideal `I = (f₁, ..., f_r)`. Then
-- descend one generator at a time using the exact sequences attached to multiplication by `f_j`
-- and the localization criterion from Lemmas `10.76.1` and `10.75.8`, finally concluding
-- `Tor₁^A(M, K) = 0` for every `A`-module `K`.
/-- Chap10 Lemma 10 99 17 (1): let `I = (f₁, …, f_r)` be an ideal generated by a finite family.
If each localization `M[1 / fᵢ]` is flat over `A[1 / fᵢ]`, the quotient `M / IM` is flat over
`A / I`, and `Tor_i^A(M, A / I)` vanishes for `i = 1, …, r + 1`, then `M` is flat over `A`. -/
@[stacks 0H7P]
theorem flat_of_flat_localizedModule_away_generators_and_flat_quotient_and_tor_vanishing
    (hlocal : ∀ i : Fin r, Module.Flat (Localization.Away (f i)) (LocalizedModule.Away (f i) M))
    (hquot : Module.Flat Ā M̄)
    (htor : ∀ i : Fin (r + 1), IsZero (TorQ[i.1 + 1])) :
    Module.Flat A M := by
  cases r with
  | zero =>
      -- With no generators, the ideal `I` is zero, so the quotient hypothesis is already the
      -- target flatness statement.
      have hrange : Set.range f = (∅ : Set A) := by
        ext x
        constructor
        · rintro ⟨i, _⟩
          exact Fin.elim0 i
        · intro hx
          cases hx
      have hIbot : Ideal.span (Set.range f) = (⊥ : Ideal A) := by
        simp [hrange]
      have hquot_bot :
          Module.Flat (A ⧸ (⊥ : Ideal A))
            (M ⧸ (((⊥ : Ideal A)) • (⊤ : Submodule A M))) := by
        exact hIbot ▸ hquot
      exact flat_of_flat_quotient_bot (A := A) (M := M) hquot_bot
  | succ r =>
      -- Proof comment: after isolating the remaining source-proof descent as a single helper,
      -- the final step is the standard flatness criterion.
      exact flat_of_tor_one_module_vanishing (A := A) (M := M) <|
        tor_one_module_vanishes_of_localized_generators_and_quotient_and_tor_vanishing
          (A := A) (M := M) (f := f) hlocal hquot htor

-- Proof sketch: first apply the previous flatness criterion, since faithful flatness of each
-- localization and of the quotient implies the corresponding flatness statements; when `r = 0`,
-- the quotient hypothesis is already the target conclusion. Then use the standard
-- faithful-flatness criterion together with the same localization-and-quotient descent pattern to
-- show tensoring with `M` is faithful.
/-- Faithfully flat variant of Chap10 Lemma 10 99 17: with the same hypotheses on the generating
family and the same Tor-vanishing assumption, if each `M[1 / fᵢ]` is faithfully flat over
`A[1 / fᵢ]` and `M / IM` is faithfully flat over `A / I`, then `M` is faithfully flat over `A`. -/
@[stacks 0H7P]
theorem faithfullyFlat_of_faithfullyFlat_localizedModule_away_generators_and_faithfullyFlat_quotient_and_tor_vanishing
    (hlocal : ∀ i : Fin r,
      Module.FaithfullyFlat (Localization.Away (f i)) (LocalizedModule.Away (f i) M))
    (hquot : Module.FaithfullyFlat Ā M̄)
    (htor : ∀ i : Fin (r + 1), IsZero (TorQ[i.1 + 1])) :
    Module.FaithfullyFlat A M := by
  cases r with
  | zero =>
      -- With `I = 0`, the quotient module is `M` itself, so the quotient hypothesis is the claim.
      have hrange : Set.range f = (∅ : Set A) := by
        ext x
        constructor
        · rintro ⟨i, _⟩
          exact Fin.elim0 i
        · intro hx
          cases hx
      have hIbot : Ideal.span (Set.range f) = (⊥ : Ideal A) := by
        simp [hrange]
      have hquot_bot :
          Module.FaithfullyFlat (A ⧸ (⊥ : Ideal A))
            (M ⧸ (((⊥ : Ideal A)) • (⊤ : Submodule A M))) := by
        exact hIbot ▸ hquot
      exact faithfullyFlat_of_faithfullyFlat_quotient_bot (A := A) (M := M) hquot_bot
  | succ r =>
      -- First reuse part (1) to obtain the flatness half of faithful flatness.
      have hflat_local :
          ∀ i : Fin (Nat.succ r),
            Module.Flat (Localization.Away (f i)) (LocalizedModule.Away (f i) M) :=
        fun i ↦ by
          let _ :
              Module.FaithfullyFlat (Localization.Away (f i)) (LocalizedModule.Away (f i) M) :=
            hlocal i
          infer_instance
      have hflat_quot :
          Module.Flat (A ⧸ Ideal.span (Set.range f))
            (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule A M))) := by
        let _ :
            Module.FaithfullyFlat (A ⧸ Ideal.span (Set.range f))
              (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule A M))) := hquot
        infer_instance
      have hflat : Module.Flat A M :=
        flat_of_flat_localizedModule_away_generators_and_flat_quotient_and_tor_vanishing
          (f := f) hflat_local hflat_quot htor
      letI : Module.Flat A M := hflat
      -- Route correction: part (2) is cleaner through the proper-ideal criterion than through
      -- residue-field fibers. Use the same localization-versus-quotient dichotomy on a maximal
      -- ideal above any proper `J` with `J • M = M`.
      refine (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top A M).2 ⟨hflat, ?_⟩
      intro J hJ
      by_contra hJ_ne_top
      obtain ⟨m, hm, hJm⟩ := J.exists_le_maximal hJ_ne_top
      by_cases hIm : Ideal.span (Set.range f) ≤ m
      · have hQuotSmul :
            (Ideal.map (algebraMap A (A ⧸ Ideal.span (Set.range f))) J) •
              (⊤ : Submodule (A ⧸ Ideal.span (Set.range f))
                (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule A M)))) = ⊤ := by
          simpa using quotient_span_ideal_smul_top_eq_top
            (A := A) (M := M) (f := f) J hJ
        have hQuotTop :
            Ideal.map (algebraMap A (A ⧸ Ideal.span (Set.range f))) J = ⊤ := by
          exact
            (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top
              (A ⧸ Ideal.span (Set.range f))
              (M ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule A M)))).1 hquot |>.2 _ hQuotSmul
        have hmap_m_ne_top :
            Ideal.map (algebraMap A (A ⧸ Ideal.span (Set.range f))) m ≠ ⊤ := by
          intro hmap_m_top
          have hOneMem :
              (1 : A ⧸ Ideal.span (Set.range f)) ∈
                Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range f))) m := by
            simpa [Ideal.Quotient.algebraMap_eq, Ideal.eq_top_iff_one] using hmap_m_top
          rcases (Ideal.mem_map_iff_of_surjective
            (f := Ideal.Quotient.mk (Ideal.span (Set.range f)))
            (hf := Ideal.Quotient.mk_surjective)).mp hOneMem with ⟨a, ha_m, ha_one⟩
          have hdiff : 1 - a ∈ Ideal.span (Set.range f) := by
            rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ha_one]
            simp
          have hone : (1 : A) ∈ m := by
            simpa using Ideal.add_mem m ha_m (hIm hdiff)
          exact hm.ne_top ((Ideal.eq_top_iff_one m).2 hone)
        have hmap_J_le :
            Ideal.map (algebraMap A (A ⧸ Ideal.span (Set.range f))) J ≤
              Ideal.map (algebraMap A (A ⧸ Ideal.span (Set.range f))) m :=
          Ideal.map_mono hJm
        have hmap_m_top :
            Ideal.map (algebraMap A (A ⧸ Ideal.span (Set.range f))) m = ⊤ := by
          rw [Ideal.eq_top_iff_one]
          exact hmap_J_le <| by
            simpa [Ideal.eq_top_iff_one] using hQuotTop
        exact hmap_m_ne_top hmap_m_top
      · rcases exists_generator_not_mem_of_not_span_le (f := f) hIm with ⟨i, hi⟩
        have hAwaySmul :
            (Ideal.map (algebraMap A (Localization.Away (f i))) J) •
              (⊤ : Submodule (Localization.Away (f i))
                (LocalizedModule.Away (f i) M)) = ⊤ := by
          exact away_localized_ideal_smul_top_eq_top
            (A := A) (M := M) (f i) J hJ
        have hAwayTop :
            Ideal.map (algebraMap A (Localization.Away (f i))) J = ⊤ := by
          exact
            (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top
              (Localization.Away (f i))
              (LocalizedModule.Away (f i) M)).1 (hlocal i) |>.2 _ hAwaySmul
        rcases pow_mem_of_away_localized_ideal_eq_top
          (A := A) (a := f i) (J := J) hAwayTop with ⟨n, hn⟩
        have hpowm : f i ^ n ∈ m := hJm hn
        exact hi (hm.isPrime.mem_of_pow_mem n hpowm)

end
