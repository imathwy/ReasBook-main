import stacks_proof.stacks_project.Chap10.Lemma_10_99_17.FinsuppExact
import stacks_proof.stacks_project.Chap10.Lemma_10_99_17.TorOneExact
import stacks_proof.stacks_project.Chap10.Lemma_10_99_17.ScalarMultiplication
import stacks_proof.stacks_project.Chap10.Lemma_10_99_17.GeneratorAnnihilator

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

/-- Helper for Chap10 Lemma 10 99 17: the canonical free `A / I`-cover of an
`I`-annihilated module is a short exact row after restricting scalars to `A`. -/
lemma quotientCanonicalFreeCover_shortExact
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K) :
    let _ : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
    let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
    (ShortComplex.moduleCatMk
      ((LinearMap.ker πBar).subtype.restrictScalars A)
      (πBar.restrictScalars A)
      (Function.Exact.linearMap_comp_eq_zero
        (quotient_canonical_free_cover_exact (A := A) (f := f) hK))).ShortExact := by
  letI : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
  let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
  have hExactCover : Function.Exact
      (LinearMap.ker πBar).subtype πBar := by
    -- Proof comment: expose the kernel exactness once so the short-complex term stays stable.
    simpa [πBar] using quotient_canonical_free_cover_exact (A := A) (f := f) hK
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk
      ((LinearMap.ker πBar).subtype.restrictScalars A)
      (πBar.restrictScalars A)
      (Function.Exact.linearMap_comp_eq_zero hExactCover)
  -- Proof comment: the row is exact by the kernel-inclusion lemma, monic by subtype inclusion,
  -- and epic because the free cover is surjective.
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    simpa [S, πBar] using quotient_canonical_free_cover_exact (A := A) (f := f) hK
  · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  · exact (ModuleCat.epi_iff_surjective _).2 <| by
      simpa [S, πBar] using quotient_canonical_free_cover_surjective (A := A) (f := f) hK

/-- Helper for Chap10 Lemma 10 99 17: a tail exactness window for module-first Tor kills the
middle term when the adjacent Tor objects vanish. -/
lemma isZero_tor_module_succ_of_tail_exact
    {S : ShortComplex (ModuleCat A)} (n : ℕ)
    (hTail :
      ∃ δ :
          ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ⟶
            (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁)),
        Function.Exact
          ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g).hom)
          δ.hom)
    (hFree :
      IsZero
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₂)))
    (hKer :
      IsZero
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁))) :
    IsZero
      ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃)) := by
  obtain ⟨δ, hExact⟩ := hTail
  have hLeft :
      (((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g) = 0 := by
    -- Proof comment: the free cover term is zero, so the incoming Tor map is the zero map.
    exact hFree.eq_of_src _ _
  have hRight : δ = 0 := by
    -- Proof comment: the kernel term is zero, so the connecting morphism also vanishes.
    exact hKer.eq_of_tgt _ _
  -- Proof comment: exactness between two zero maps forces the middle Tor object to be zero.
  exact isZero_of_exact_zero_zero hExact hLeft hRight

/-- Helper for Chap10 Lemma 10 99 17: a flipped-source five-term row transports to the
module-first public Tor owner through `tor_module_flip_owner_iso`. -/
lemma tor_module_five_term_exact_of_flippedSource
    {S : ShortComplex (ModuleCat A)} (n : ℕ)
    (hFlipped :
      ∃ δ :
          (((Tor' (ModuleCat A) (n + 1)).flip.obj (ModuleCat.of A M)).obj S.X₃) ⟶
            (((Tor' (ModuleCat A) n).flip.obj (ModuleCat.of A M)).obj S.X₁),
        (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) (n + 1)).flip.obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) (n + 1)).flip.obj (ModuleCat.of A M)).map S.g)
          δ
          (((Tor' (ModuleCat A) n).flip.obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) n).flip.obj (ModuleCat.of A M)).map S.g)).Exact) :
    ∃ δ :
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁)),
      (ComposableArrows.mk₅
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g))
        δ
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g))).Exact := by
  obtain ⟨δFlipped, hFlippedExact⟩ := hFlipped
  let eHighX₁ := (tor_module_flip_owner_iso (A := A) (M := M) (n + 1)).app S.X₁
  let eHighX₂ := (tor_module_flip_owner_iso (A := A) (M := M) (n + 1)).app S.X₂
  let eHighX₃ := (tor_module_flip_owner_iso (A := A) (M := M) (n + 1)).app S.X₃
  let eLowX₁ := (tor_module_flip_owner_iso (A := A) (M := M) n).app S.X₁
  let eLowX₂ := (tor_module_flip_owner_iso (A := A) (M := M) n).app S.X₂
  let eLowX₃ := (tor_module_flip_owner_iso (A := A) (M := M) n).app S.X₃
  have hHighMapF :
      ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f)) ≫
          eHighX₂.hom =
        eHighX₁.hom ≫
          (((Tor' (ModuleCat A) (n + 1)).flip.obj (ModuleCat.of A M)).map S.f) := by
    -- Proof comment: naturality of the degree-`n + 1` owner comparison rewrites the first public
    -- Tor arrow as the flipped-source arrow.
    simpa [eHighX₁, eHighX₂] using
      (tor_module_flip_owner_iso (A := A) (M := M) (n + 1)).hom.naturality S.f
  have hHighMapG :
      ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g)) ≫
          eHighX₃.hom =
        eHighX₂.hom ≫
          (((Tor' (ModuleCat A) (n + 1)).flip.obj (ModuleCat.of A M)).map S.g) := by
    -- Proof comment: the same naturality square handles the second high-degree arrow.
    simpa [eHighX₂, eHighX₃] using
      (tor_module_flip_owner_iso (A := A) (M := M) (n + 1)).hom.naturality S.g
  have hLowMapF :
      ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f)) ≫ eLowX₂.hom =
        eLowX₁.hom ≫
          (((Tor' (ModuleCat A) n).flip.obj (ModuleCat.of A M)).map S.f) := by
    -- Proof comment: in degree `n`, naturality identifies the public arrow with the flipped
    -- source-owner arrow.
    simpa [eLowX₁, eLowX₂] using
      (tor_module_flip_owner_iso (A := A) (M := M) n).hom.naturality S.f
  have hLowMapG :
      ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g)) ≫ eLowX₃.hom =
        eLowX₂.hom ≫
          (((Tor' (ModuleCat A) n).flip.obj (ModuleCat.of A M)).map S.g) := by
    -- Proof comment: and likewise for the final low-degree arrow.
    simpa [eLowX₂, eLowX₃] using
      (tor_module_flip_owner_iso (A := A) (M := M) n).hom.naturality S.g
  let δ :
      ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ⟶
        (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁)) :=
    eHighX₃.hom ≫ δFlipped ≫ eLowX₁.inv
  have hδ :
      δ ≫ eLowX₁.hom = eHighX₃.hom ≫ δFlipped := by
    -- Proof comment: the public connecting morphism is the flipped-source boundary conjugated by
    -- the endpoint owner comparisons.
    simp [δ, Category.assoc]
  let ePublic :
      (ComposableArrows.mk₅
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g))
        δ
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g))) ≅
        (ComposableArrows.mk₅
          (((Tor' (ModuleCat A) (n + 1)).flip.obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) (n + 1)).flip.obj (ModuleCat.of A M)).map S.g)
          δFlipped
          (((Tor' (ModuleCat A) n).flip.obj (ModuleCat.of A M)).map S.f)
          (((Tor' (ModuleCat A) n).flip.obj (ModuleCat.of A M)).map S.g)) :=
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
  -- Proof comment: exactness is invariant under the six endpoint isomorphisms of the five-term
  -- row, so the public row follows from the flipped-source row.
  exact (ComposableArrows.exact_iff_of_iso ePublic).2 hFlippedExact

/-- Helper for Chap10 Lemma 10 99 17: the degree-one public six-term row supplies the tail
window in the same existential shape as the higher five-term sequence. -/
lemma tor_module_one_tail_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    ∃ δ :
        ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          ((tensorLeft (ModuleCat.of A M)).obj S.X₁)),
      Function.Exact
        ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g).hom)
        δ.hom := by
  let T := ModuleCat.torTensorSixTermSequence (ModuleCat.of A M) hS
  refine ⟨T.map' 2 3, ?_⟩
  -- Proof comment: exactness at index `1` of the six-term row is the desired
  -- `Tor₁(M, S.X₂) → Tor₁(M, S.X₃) → M ⊗ S.X₁` window.
  simpa [T] using tor_one_module_middle_exact_of_shortExact (A := A) (M := M) hS

/-- Helper for Chap10 Lemma 10 99 17: the flipped source owner
`X ↦ Tor'_n^A(X, N)` is definitionally the `n`th left derived functor of `tensorRight N`. -/
theorem flippedSourceOwnerEqLeftDerivedObj
    (N X : ModuleCat A) (n : ℕ) :
    ((((Tor' (ModuleCat A) n).flip.obj N).obj X)) =
      ((tensorRight N).leftDerived n).obj X := by
  -- Proof comment: unfold only the owner orientation; no homological argument is involved here.
  rfl

/-- Helper for Chap10 Lemma 10 99 17: every short exact row of modules admits a first-variable
horseshoe row of projective resolutions. -/
theorem firstVariableHorseshoeRowNonemptyOfShortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    Nonempty (ModuleCat.FirstVariableHorseshoeRow (R := A) S) := by
  -- Proof comment: the horseshoe construction is now exposed by its canonical owner; this item
  -- only packages the already verified row as nonempty setup data for the long exact sequence.
  exact ⟨ModuleCat.first_variable_horseshoe_row_of_shortExact (R := A) hS⟩

/-- Helper for Chap10 Lemma 10 99 17: choose a first-variable horseshoe row for a short exact
row. -/
noncomputable def firstVariableHorseshoeRowOfShortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) :
    ModuleCat.FirstVariableHorseshoeRow (R := A) S :=
  Classical.choice (firstVariableHorseshoeRowNonemptyOfShortExact (A := A) hS)

/-- Helper for Chap10 Lemma 10 99 17: tensoring the two comparison maps in a first-variable
horseshoe row still gives composable maps of chain complexes. -/
theorem ModuleCat.FirstVariableHorseshoeRow.tensorized_zero
    {S : ShortComplex (ModuleCat A)}
    (H : ModuleCat.FirstVariableHorseshoeRow (R := A) S) (N : ModuleCat A) :
    (((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).map H.iota) ≫
        (((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).map H.pi) = 0 := by
  -- Proof comment: functoriality carries the horseshoe relation `H.iota ≫ H.pi = 0` to the
  -- tensorized row.
  rw [← Functor.map_comp, H.zero, Functor.map_zero]

/-- Helper for Chap10 Lemma 10 99 17: tensoring a first-variable horseshoe row by a fixed module
produces the short complex of chain complexes that feeds the homology long exact sequence. -/
noncomputable def ModuleCat.FirstVariableHorseshoeRow.tensorizedShortComplex
    {S : ShortComplex (ModuleCat A)}
    (H : ModuleCat.FirstVariableHorseshoeRow (R := A) S) (N : ModuleCat A) :
    ShortComplex (ChainComplex (ModuleCat A) ℕ) :=
  ShortComplex.mk
    (((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).map H.iota)
    (((tensorRight N).mapHomologicalComplex (ComplexShape.down ℕ)).map H.pi)
    (H.tensorized_zero N)

/-- Helper for Chap10 Lemma 10 99 17: tensoring a degreewise split first-variable horseshoe row
by a fixed module remains short exact as a row of chain complexes. -/
theorem tensorRightHorseshoeRowShortExact
    (N : ModuleCat A) {S : ShortComplex (ModuleCat A)}
    (H : ModuleCat.FirstVariableHorseshoeRow (R := A) S) :
    (H.tensorizedShortComplex N).ShortExact := by
  -- Proof comment: exactness of a short complex of chain complexes is checked degreewise; after
  -- tensoring, each degree is the image of the stored split short exact row.
  refine HomologicalComplex.shortExact_of_degreewise_shortExact
    (H.tensorizedShortComplex N) ?_
  intro n
  simpa [ModuleCat.FirstVariableHorseshoeRow.tensorizedShortComplex,
    CategoryTheory.Functor.mapHomologicalComplex_map_f] using
    ((H.split n).map (tensorRight N)).shortExact

/-- Helper for Chap10 Lemma 10 99 17: in the downward complex shape on `ℕ`, `n + 1` is adjacent
to `n`. -/
theorem downRel_succ (n : ℕ) : (ComplexShape.down ℕ).Rel (n + 1) n := by
  -- Proof comment: this is the index side condition for the homology connecting morphism.
  simp

/-- Helper for Chap10 Lemma 10 99 17: a first-variable horseshoe row gives the flipped-source
five-term exact row for `X ↦ Tor'_i^A(X, N)` in every degree. -/
theorem flippedSourceTorFiveTermExactOfHorseshoeRow
    (N : ModuleCat A) {S : ShortComplex (ModuleCat A)}
    (H : ModuleCat.FirstVariableHorseshoeRow (R := A) S) (n : ℕ) :
    ∃ δ :
        (((Tor' (ModuleCat A) (n + 1)).flip.obj N).obj S.X₃) ⟶
          (((Tor' (ModuleCat A) n).flip.obj N).obj S.X₁),
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat A) (n + 1)).flip.obj N).map S.f)
        (((Tor' (ModuleCat A) (n + 1)).flip.obj N).map S.g)
        δ
        (((Tor' (ModuleCat A) n).flip.obj N).map S.f)
        (((Tor' (ModuleCat A) n).flip.obj N).map S.g)).Exact := by
  let T := H.tensorizedShortComplex N
  let hT := tensorRightHorseshoeRowShortExact (A := A) N H
  let eHighX₁ :
      (((Tor' (ModuleCat A) (n + 1)).flip.obj N).obj S.X₁) ≅ T.X₁.homology (n + 1) := by
    -- Proof comment: compute the left high-degree endpoint on the left projective resolution.
    erw [flippedSourceOwnerEqLeftDerivedObj (A := A) N S.X₁ (n + 1)]
    exact (CategoryTheory.projectiveResolution S.X₁).isoLeftDerivedObj (tensorRight N) (n + 1)
  let eHighX₂ :
      (((Tor' (ModuleCat A) (n + 1)).flip.obj N).obj S.X₂) ≅ T.X₂.homology (n + 1) := by
    -- Proof comment: compute the middle high-degree endpoint on the horseshoe resolution.
    erw [flippedSourceOwnerEqLeftDerivedObj (A := A) N S.X₂ (n + 1)]
    exact H.P2.isoLeftDerivedObj (tensorRight N) (n + 1)
  let eHighX₃ :
      (((Tor' (ModuleCat A) (n + 1)).flip.obj N).obj S.X₃) ≅ T.X₃.homology (n + 1) := by
    -- Proof comment: compute the right high-degree endpoint on the right projective resolution.
    erw [flippedSourceOwnerEqLeftDerivedObj (A := A) N S.X₃ (n + 1)]
    exact (CategoryTheory.projectiveResolution S.X₃).isoLeftDerivedObj (tensorRight N) (n + 1)
  let eLowX₁ :
      (((Tor' (ModuleCat A) n).flip.obj N).obj S.X₁) ≅ T.X₁.homology n := by
    -- Proof comment: compute the left low-degree endpoint on the same left resolution.
    erw [flippedSourceOwnerEqLeftDerivedObj (A := A) N S.X₁ n]
    exact (CategoryTheory.projectiveResolution S.X₁).isoLeftDerivedObj (tensorRight N) n
  let eLowX₂ :
      (((Tor' (ModuleCat A) n).flip.obj N).obj S.X₂) ≅ T.X₂.homology n := by
    -- Proof comment: compute the middle low-degree endpoint on `H.P2`.
    erw [flippedSourceOwnerEqLeftDerivedObj (A := A) N S.X₂ n]
    exact H.P2.isoLeftDerivedObj (tensorRight N) n
  let eLowX₃ :
      (((Tor' (ModuleCat A) n).flip.obj N).obj S.X₃) ≅ T.X₃.homology n := by
    -- Proof comment: compute the right low-degree endpoint on the right resolution.
    erw [flippedSourceOwnerEqLeftDerivedObj (A := A) N S.X₃ n]
    exact (CategoryTheory.projectiveResolution S.X₃).isoLeftDerivedObj (tensorRight N) n
  have hIotaAug0 :
      H.iota.f 0 ≫ H.P2.π.f 0 =
        (CategoryTheory.projectiveResolution S.X₁).π.f 0 ≫ S.f := by
    -- Proof comment: the degree-zero component of the augmentation compatibility is exactly the
    -- naturality side condition for the first comparison map.
    simpa using congr_fun (congrArg HomologicalComplex.Hom.f H.iota_augment) 0
  have hPiAug0 :
      H.pi.f 0 ≫ (CategoryTheory.projectiveResolution S.X₃).π.f 0 =
        H.P2.π.f 0 ≫ S.g := by
    -- Proof comment: the right comparison map supplies the second naturality side condition.
    simpa using congr_fun (congrArg HomologicalComplex.Hom.f H.pi_augment) 0
  have hHighMapF :
      (((Tor' (ModuleCat A) (n + 1)).flip.obj N).map S.f) ≫ eHighX₂.hom =
        eHighX₁.hom ≫ HomologicalComplex.homologyMap T.f (n + 1) := by
    -- Proof comment: projective-resolution naturality identifies the first high-degree Tor map
    -- with the homology map induced by `H.iota`.
    simpa [T, ModuleCat.FirstVariableHorseshoeRow.tensorizedShortComplex] using
      (CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality
        (f := S.f)
        (P := CategoryTheory.projectiveResolution S.X₁)
        (Q := H.P2)
        (φ := H.iota)
        (comm := hIotaAug0)
        (F := tensorRight N)
        (n := n + 1))
  have hHighMapG :
      (((Tor' (ModuleCat A) (n + 1)).flip.obj N).map S.g) ≫ eHighX₃.hom =
        eHighX₂.hom ≫ HomologicalComplex.homologyMap T.g (n + 1) := by
    -- Proof comment: the second high-degree Tor map is induced by `H.pi`.
    simpa [T, ModuleCat.FirstVariableHorseshoeRow.tensorizedShortComplex] using
      (CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality
        (f := S.g)
        (P := H.P2)
        (Q := CategoryTheory.projectiveResolution S.X₃)
        (φ := H.pi)
        (comm := hPiAug0)
        (F := tensorRight N)
        (n := n + 1))
  have hLowMapF :
      (((Tor' (ModuleCat A) n).flip.obj N).map S.f) ≫ eLowX₂.hom =
        eLowX₁.hom ≫ HomologicalComplex.homologyMap T.f n := by
    -- Proof comment: the same naturality comparison works in degree `n`.
    simpa [T, ModuleCat.FirstVariableHorseshoeRow.tensorizedShortComplex] using
      (CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality
        (f := S.f)
        (P := CategoryTheory.projectiveResolution S.X₁)
        (Q := H.P2)
        (φ := H.iota)
        (comm := hIotaAug0)
        (F := tensorRight N)
        (n := n))
  have hLowMapG :
      (((Tor' (ModuleCat A) n).flip.obj N).map S.g) ≫ eLowX₃.hom =
        eLowX₂.hom ≫ HomologicalComplex.homologyMap T.g n := by
    -- Proof comment: and the final low-degree Tor map is induced by `H.pi`.
    simpa [T, ModuleCat.FirstVariableHorseshoeRow.tensorizedShortComplex] using
      (CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_hom_naturality
        (f := S.g)
        (P := H.P2)
        (Q := CategoryTheory.projectiveResolution S.X₃)
        (φ := H.pi)
        (comm := hPiAug0)
        (F := tensorRight N)
        (n := n))
  let δ :
      (((Tor' (ModuleCat A) (n + 1)).flip.obj N).obj S.X₃) ⟶
        (((Tor' (ModuleCat A) n).flip.obj N).obj S.X₁) :=
    eHighX₃.hom ≫ hT.δ (n + 1) n (downRel_succ n) ≫ eLowX₁.inv
  have hδ :
      δ ≫ eLowX₁.hom =
        eHighX₃.hom ≫ hT.δ (n + 1) n (downRel_succ n) := by
    -- Proof comment: the connecting morphism is the raw homology boundary conjugated by the
    -- endpoint comparison isomorphisms.
    simp [δ, Category.assoc]
  let eFlipped :
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat A) (n + 1)).flip.obj N).map S.f)
        (((Tor' (ModuleCat A) (n + 1)).flip.obj N).map S.g)
        δ
        (((Tor' (ModuleCat A) n).flip.obj N).map S.f)
        (((Tor' (ModuleCat A) n).flip.obj N).map S.g)) ≅
        (ComposableArrows.mk₅
          (HomologicalComplex.homologyMap T.f (n + 1))
          (HomologicalComplex.homologyMap T.g (n + 1))
          (hT.δ (n + 1) n (downRel_succ n))
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
  -- Proof comment: after conjugating all endpoints, exactness is the standard five-term
  -- homology sequence of the tensorized short exact row.
  exact (ComposableArrows.exact_iff_of_iso eFlipped).2 <|
    HomologicalComplex.HomologySequence.composableArrows₅_exact
      (S₁ := T) hT (n + 1) n (downRel_succ n)

/-- Helper for Chap10 Lemma 10 99 17: a short exact row gives the flipped-source five-term exact
sequence for `X ↦ Tor'_i^A(X, M)`. -/
lemma flippedSourceTorFiveTermExactOfShortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    ∃ δ :
        (((Tor' (ModuleCat A) (n + 1)).flip.obj (ModuleCat.of A M)).obj S.X₃) ⟶
          (((Tor' (ModuleCat A) n).flip.obj (ModuleCat.of A M)).obj S.X₁),
      (ComposableArrows.mk₅
        (((Tor' (ModuleCat A) (n + 1)).flip.obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) (n + 1)).flip.obj (ModuleCat.of A M)).map S.g)
        δ
        (((Tor' (ModuleCat A) n).flip.obj (ModuleCat.of A M)).map S.f)
        (((Tor' (ModuleCat A) n).flip.obj (ModuleCat.of A M)).map S.g)).Exact := by
  -- Proof comment: the long-exact-row transport is now proved from a horseshoe row; the only
  -- remaining construction is choosing such a row from the short exact sequence.
  exact
    flippedSourceTorFiveTermExactOfHorseshoeRow
      (A := A) (N := ModuleCat.of A M)
      (firstVariableHorseshoeRowOfShortExact (A := A) hS) n

/-- Helper for Chap10 Lemma 10 99 17: a short exact row gives the module-first public five-term
exact sequence for `K ↦ Tor_i^A(M, K)`. -/
lemma tor_module_five_term_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    ∃ δ :
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁)),
      (ComposableArrows.mk₅
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g))
        δ
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g))).Exact := by
  -- Proof comment: once the flipped-source row is available, owner transport supplies the
  -- module-first public Tor row needed by the descent argument.
  exact tor_module_five_term_exact_of_flippedSource (A := A) (M := M) (S := S) n
    (flippedSourceTorFiveTermExactOfShortExact (A := A) (M := M) hS n)

/-- Helper for Chap10 Lemma 10 99 17: the tail window of the module-first public Tor five-term
sequence. -/
lemma tor_module_tail_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    ∃ δ :
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁)),
      Function.Exact
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g).hom)
        δ.hom := by
  obtain ⟨δ, hFive⟩ :=
    tor_module_five_term_exact_of_shortExact (A := A) (M := M) hS n
  refine ⟨δ, ?_⟩
  -- Proof comment: exactness at the degree-`n + 1` target term is the required tail window.
  simpa [ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (ComposableArrows.mk₅
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g))
        δ
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g))).sc
          hFive.toIsComplex 1)).1
      (hFive.exact 1)

/-- Helper for Chap10 Lemma 10 99 17: the connecting-map window of the module-first public Tor
five-term sequence. -/
lemma tor_module_succ_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    ∃ δ :
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj S.X₃) ⟶
          (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj S.X₁)),
      Function.Exact δ.hom
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f).hom) := by
  obtain ⟨δ, hFive⟩ :=
    tor_module_five_term_exact_of_shortExact (A := A) (M := M) hS n
  refine ⟨δ, ?_⟩
  -- Proof comment: exactness at the degree-`n` source term gives the successor window.
  simpa [ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (ComposableArrows.mk₅
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g))
        δ
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g))).sc
          hFive.toIsComplex 2)).1
      (hFive.exact 2)

/-- Helper for Chap10 Lemma 10 99 17: the same-degree exactness window in the module-first
public Tor five-term sequence. This is the exactness slot used for multiplication by a scalar. -/
lemma tor_module_middle_exact_of_shortExact
    {S : ShortComplex (ModuleCat A)} (hS : S.ShortExact) (n : ℕ) :
    Function.Exact
      ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f).hom)
      ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g).hom) := by
  obtain ⟨δ, hFive⟩ :=
    tor_module_five_term_exact_of_shortExact (A := A) (M := M) hS n
  -- Proof comment: exactness at the degree-`n` middle object is the last short-complex window
  -- of the module-first five-term row.
  simpa [ComposableArrows.sc] using
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S := (ComposableArrows.mk₅
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).map S.g))
        δ
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.f))
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map S.g))).sc
          hFive.toIsComplex 3)).1
      (hFive.exact 3)

/-- Helper for Chap10 Lemma 10 99 17: if the kernel and quotient rows for multiplication by
`a` have the expected module-first Tor-vanishing, then scalar multiplication by `a` is injective
on `Tor_n^A(M, K)`. -/
lemma tor_module_smul_injective_of_kernel_and_quotient_vanishing
    {K : Type u} [AddCommGroup K] [Module A K] (a : A) (n : ℕ)
    (hker :
      IsZero
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (LinearMap.ker (LinearMap.lsmul A K a))))))
    (hquot :
      IsZero
        ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (K ⧸ LinearMap.range (LinearMap.lsmul A K a)))))) :
    Function.Injective
      fun t :
        ↑((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K))) ↦
        a • t := by
  let μ : K →ₗ[A] K := LinearMap.lsmul A K a
  let β₀ : K →ₗ[A] LinearMap.range μ := μ.rangeRestrict
  let γ₀ : LinearMap.range μ →ₗ[A] K := (LinearMap.range μ).subtype
  let q : K →ₗ[A] K ⧸ LinearMap.range μ := Submodule.mkQ (LinearMap.range μ)
  have hExactKerBase : Function.Exact (LinearMap.ker μ).subtype β₀ := by
    -- Proof comment: the kernel of the range-restricted multiplication map is the original
    -- multiplication kernel.
    rw [LinearMap.exact_iff]
    simp [β₀]
  let Sker : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk (LinearMap.ker μ).subtype β₀
      (Function.Exact.linearMap_comp_eq_zero hExactKerBase)
  let Squot : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk γ₀ q
      (Function.Exact.linearMap_comp_eq_zero
        (by
          simpa [γ₀, q] using
            (LinearMap.exact_subtype_mkQ (LinearMap.range μ))))
  have hSker : Sker.ShortExact := by
    -- Proof comment: `0 → ker μ → K → range μ → 0` is short exact.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [Sker] using hExactKerBase
    · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).2 <| by
        simpa [Sker, β₀] using μ.surjective_rangeRestrict
  have hSquot : Squot.ShortExact := by
    -- Proof comment: `0 → range μ → K → K / range μ → 0` is short exact.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      simpa [Squot, γ₀, q] using
        (LinearMap.exact_subtype_mkQ (LinearMap.range μ))
    · exact (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
    · exact (ModuleCat.epi_iff_surjective _).2 <| by
        simpa [Squot, q] using Submodule.mkQ_surjective (LinearMap.range μ)
  have hExactKer :
      Function.Exact
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.f).hom)
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.g).hom) := by
    -- Proof comment: read the same-degree exact window off the first multiplication row.
    simpa [Sker] using
      tor_module_middle_exact_of_shortExact (A := A) (M := M) (S := Sker) hSker n
  obtain ⟨δ, hExactQuot⟩ :=
    tor_module_succ_exact_of_shortExact (A := A) (M := M) (S := Squot) hSquot n
  have hKerMapZero :
      (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.f) = 0 := by
    -- Proof comment: the first row starts with a zero Tor object by hypothesis on `ker μ`.
    simpa [Sker] using hker.eq_of_src
      ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.f)) 0
  have hδZero : δ = 0 := by
    -- Proof comment: the second row starts with a zero higher Tor object by hypothesis on the
    -- quotient by the multiplication image.
    simpa [Squot] using hquot.eq_of_src δ 0
  have hβ_injective :
      Function.Injective
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.g).hom) := by
    have hkerβ :
        LinearMap.ker ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.g).hom) =
          ⊥ := by
      calc
        LinearMap.ker ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.g).hom)
            =
          LinearMap.range ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.f).hom) :=
              LinearMap.exact_iff.mp hExactKer
        _ = ⊥ := by
              have hzero :
                  ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.f).hom) = 0 :=
                congrArg ModuleCat.Hom.hom hKerMapZero
              simpa [hzero] using (LinearMap.range_eq_bot.mpr hzero)
    exact (LinearMap.ker_eq_bot).1 hkerβ
  have hγ_injective :
      Function.Injective
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Squot.f).hom) := by
    have hkerγ :
        LinearMap.ker ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Squot.f).hom) =
          ⊥ := by
      calc
        LinearMap.ker ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Squot.f).hom)
            = LinearMap.range δ.hom := LinearMap.exact_iff.mp hExactQuot
        _ = ⊥ := by
              have hzero : δ.hom = 0 := congrArg ModuleCat.Hom.hom hδZero
              simpa [hzero] using (LinearMap.range_eq_bot.mpr hzero)
    exact (LinearMap.ker_eq_bot).1 hkerγ
  have hμ_cat : Sker.g ≫ Squot.f = ModuleCat.ofHom μ := by
    -- Proof comment: composing the two multiplication rows recovers multiplication by `a`.
    ext x
    rfl
  have hTorμ :
      ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ))).hom =
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Squot.f).hom).comp
          ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.g).hom) := by
    have hmapComp :
        (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ)) =
          (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Sker.g) ≫
            (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map Squot.f) := by
      simpa [hμ_cat] using
        (((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map_comp Sker.g Squot.f)
    simpa using congrArg ModuleCat.Hom.hom hmapComp
  have hTorμ_injective :
      Function.Injective
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ))).hom := by
    rw [hTorμ]
    exact hγ_injective.comp hβ_injective
  have hmap_hom :
      ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map
        (ModuleCat.ofHom μ))).hom =
        LinearMap.lsmul A
          ↑((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K))) a := by
    simpa [μ] using
      congrArg ModuleCat.Hom.hom
        (tor_module_map_lsmul_eq_smul (A := A) (M := M) (n := n) (K := K) a)
  -- Proof comment: after the Tor map is identified with literal scalar multiplication,
  -- injectivity of the Tor map is exactly injectivity of `a • -`.
  intro x y hxy
  have hxy' :
      ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map
        (ModuleCat.ofHom μ))).hom x =
        ((((Tor (ModuleCat A) n).obj (ModuleCat.of A M)).map
          (ModuleCat.ofHom μ))).hom y := by
    rw [hmap_hom]
    simpa [LinearMap.lsmul_apply] using hxy
  exact hTorμ_injective hxy'

/-- Helper for Chap10 Lemma 10 99 17: localizing the module-first public Tor owner away from
`a` identifies it with the corresponding Tor object over `A[1 / a]`, hence it vanishes when the
localized module `M[1 / a]` is flat. -/
lemma tor_module_localizedAway_isZero_of_flat_localization_core
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

/-- Helper for Chap10 Lemma 10 99 17: one generator can be removed from the annihilator
hypothesis, losing one degree of Tor-vanishing, by combining scalar injectivity with localization
away from the removed generator. -/
lemma tor_module_generator_descent_step
    {s : ℕ} (g : Fin (s + 1) → A)
    (hlocalLast :
      Module.Flat (Localization.Away (g (Fin.last s)))
        (LocalizedModule.Away (g (Fin.last s)) M))
    (hfull :
      ∀ {K : Type u} [AddCommGroup K] [Module A K],
        Ideal.span (Set.range g) ≤ Module.annihilator A K →
          ∀ i : Fin (s + 2),
            IsZero
              ((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
                (ModuleCat.of A K)))) :
    ∀ {K : Type u} [AddCommGroup K] [Module A K],
      Ideal.span (Set.range (Fin.init g)) ≤ Module.annihilator A K →
        ∀ i : Fin (s + 1),
          IsZero
            ((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
              (ModuleCat.of A K))) := by
  intro K _ _ hK i
  let a : A := g (Fin.last s)
  have hKerAnn :
      Ideal.span (Set.range g) ≤
        Module.annihilator A (LinearMap.ker (LinearMap.lsmul A K a)) := by
    -- Proof comment: the older generators kill `K`, while the last generator kills the kernel of
    -- multiplication by itself.
    simpa [a] using
      span_range_le_annihilator_ker_last_lsmul (A := A) (g := g) hK
  have hQuotAnn :
      Ideal.span (Set.range g) ≤
        Module.annihilator A (K ⧸ LinearMap.range (LinearMap.lsmul A K a)) := by
    -- Proof comment: the quotient by the last multiplication image is killed by every generator
    -- in the enlarged family.
    simpa [a] using
      span_range_le_annihilator_quotient_last_lsmul (A := A) (g := g) hK
  have hker :
      IsZero
        ((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (LinearMap.ker (LinearMap.lsmul A K a))))) := by
    exact hfull hKerAnn ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self (s + 1))⟩
  have hquot :
      IsZero
        ((((Tor (ModuleCat A) ((i.1 + 1) + 1)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A (K ⧸ LinearMap.range (LinearMap.lsmul A K a))))) := by
    exact hfull hQuotAnn ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
  have hinj :
      Function.Injective
        fun t :
          ↑((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A K))) ↦
          a • t := by
    -- Proof comment: exactness of the two multiplication rows makes scalar multiplication on Tor
    -- injective.
    exact
      tor_module_smul_injective_of_kernel_and_quotient_vanishing
        (A := A) (M := M) (K := K) (a := a) (n := i.1 + 1) hker hquot
  have hlocZero :
      IsZero
        (ModuleCat.of (Localization.Away a)
          (LocalizedModule.Away a
            ↑((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
              (ModuleCat.of A K))))) := by
    -- Proof comment: after localizing away from the removed generator, flatness of `M[1/a]`
    -- kills this positive-degree Tor object.
    simpa [a] using
      tor_module_localizedAway_isZero_of_flat_localization_core
        (A := A) (M := M) (a := g (Fin.last s)) (n := i.1) (K := K) hlocalLast
  let T : Type u :=
    ↑((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A K)))
  have hlocSubsingleton : Subsingleton (LocalizedModule.Away a T) :=
    -- Proof comment: convert categorical zero after localization into the subsingleton
    -- hypothesis required by the elementary localization criterion.
    (ModuleCat.isZero_of_iff_subsingleton
      (R := Localization.Away a) (M := LocalizedModule.Away a T)).1
      (by simpa [T] using hlocZero)
  letI : Subsingleton (LocalizedModule.Away a T) := hlocSubsingleton
  -- Proof comment: localization is zero and scalar multiplication is injective, so the original
  -- Tor object is zero.
  change IsZero (ModuleCat.of A T)
  exact isZero_of_localizedAway_isZero_of_smul_injective (A := A) a hinj

/-- Helper for Chap10 Lemma 10 99 17: the canonical free `A / I`-cover kills module-first
`Tor₁^A(M, K)` once the free cover source has zero `Tor₁` and `M / IM` is flat over `A / I`. -/
lemma tor_module_one_isZero_of_annihilated_by_span_free_cover
    (hquot : Module.Flat Ā M̄)
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K)
    (hfree :
      IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (K →₀ Ā))))) :
    IsZero
      ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A K))) := by
  -- Proof comment: install the quotient-module structure so the canonical free cover is a
  -- short exact sequence of `A`-modules after restriction of scalars.
  letI : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
  letI : IsScalarTower A Ā K :=
    quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
  let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
  have hExactCover : Function.Exact
      (LinearMap.ker πBar).subtype πBar := by
    -- Proof comment: the quotient free cover is exact at the middle term by construction.
    simpa [πBar] using quotient_canonical_free_cover_exact (A := A) (f := f) hK
  let S : ShortComplex (ModuleCat A) :=
    ShortComplex.moduleCatMk
      ((LinearMap.ker πBar).subtype.restrictScalars A)
      (πBar.restrictScalars A)
      (Function.Exact.linearMap_comp_eq_zero hExactCover)
  have hS : S.ShortExact := by
    -- Proof comment: reuse the packaged short-exactness of this canonical cover.
    simpa [S, πBar] using
      quotientCanonicalFreeCover_shortExact (A := A) (f := f) hK
  let δ : ((ModuleCat.torTensorSixTermSequence (ModuleCat.of A M) hS).obj 2) ⟶
      ((ModuleCat.torTensorSixTermSequence (ModuleCat.of A M) hS).obj 3) :=
    (ModuleCat.torTensorSixTermSequence (ModuleCat.of A M) hS).map' 2 3
  have hExactMid :
      Function.Exact
        ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g).hom)
        δ.hom := by
    -- Proof comment: exactness at the degree-one Tor term is the middle window of the six-term row.
    simpa [δ] using tor_one_module_middle_exact_of_shortExact (A := A) (M := M) hS
  have hExactTail :
      Function.Exact δ.hom (((tensorLeft (ModuleCat.of A M)).map S.f).hom) := by
    -- Proof comment: the next exact window connects the boundary map to the tensor tail.
    simpa [δ] using tor_one_tensor_tail_exact_of_shortExact (A := A) (M := M) hS
  have hLeft : (((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g) = 0 := by
    -- Proof comment: the source of the map is the free quotient module, whose Tor object is zero.
    simpa [S] using hfree.eq_of_src
      ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).map S.g)) 0
  have hTensorInj :
      Function.Injective (((tensorLeft (ModuleCat.of A M)).map S.f).hom) := by
    -- Proof comment: quotient flatness makes the tensor tail of the canonical cover injective.
    simpa [S, πBar, ModuleCat.hom_whiskerLeft] using
      tensor_tail_injective_of_flat_canonical_cover (A := A) (M := M) (f := f) hquot hK
  have hδ : δ = 0 := by
    -- Proof comment: exactness of the tensor tail and injectivity force the boundary map to vanish.
    apply ModuleCat.hom_ext
    ext x
    apply hTensorInj
    exact congrArg (fun φ => φ x) (Function.Exact.linearMap_comp_eq_zero hExactTail)
  -- Proof comment: exactness between the zero incoming map and zero boundary map kills the target.
  simpa [S, δ] using isZero_of_exact_zero_zero hExactMid hLeft hδ

/-- Helper for Chap10 Lemma 10 99 17: the module-first public Tor owner vanishes in the
range `1, ..., r + 1` on every module annihilated by `Ideal.span (Set.range f)`. -/
lemma tor_module_annihilated_by_span_vanishes_in_range_of_free_cover_range
    (hquot : Module.Flat Ā M̄)
    (htor : ∀ i : Fin (r + 1), IsZero (TorQ[i.1 + 1]))
    {K : Type u} [AddCommGroup K] [Module A K]
    (hK : I ≤ Module.annihilator A K) :
    ∀ i : Fin (r + 1),
      IsZero
        ((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
          (ModuleCat.of A K))) := by
  -- Proof comment: the proved finite-support propagation supplies the free `A / I` inputs; the
  -- missing remaining step is the module-first higher exactness window for the canonical free
  -- cover of an `I`-annihilated module.
  have hfree :
      ∀ (ι : Type u) (i : Fin (r + 1)),
        IsZero
          ((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
            (ModuleCat.of A (ι →₀ Ā)))) := by
    intro ι i
    exact
      tor_module_finsuppQuotient_isZero_of_quotient_isZero
        (A := A) (M := M) (f := f) i.1 ι (htor i)
  have hAll :
      ∀ d : ℕ, d < r + 1 →
        ∀ {K : Type u} [AddCommGroup K] [Module A K],
          I ≤ Module.annihilator A K →
            IsZero
              ((((Tor (ModuleCat A) (d + 1)).obj (ModuleCat.of A M)).obj
                (ModuleCat.of A K))) := by
    -- Proof comment: strengthen the induction to all `I`-annihilated modules so that the
    -- canonical-cover kernel can be used as the induction input in the successor step.
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
        intro hd K _ _ hK
        cases d with
        | zero =>
            -- Proof comment: degree one is the already packaged free-cover/tensor-tail argument.
            have hFree :
                IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
                  (ModuleCat.of A (K →₀ Ā)))) := by
              exact hfree K 0
            exact
              tor_module_one_isZero_of_annihilated_by_span_free_cover
                (A := A) (M := M) (f := f) hquot hK hFree
        | succ n =>
            -- Proof comment: the successor step uses the canonical free cover of `K`; the free
            -- module term is handled by finite-support propagation and the kernel term by the
            -- induction hypothesis. The only unproved input is the module-first tail exactness
            -- window for this short exact row.
            letI : Module Ā K := quotient_module_of_annihilator_le (A := A) (f := f) hK
            letI : IsScalarTower A Ā K :=
              quotient_module_isScalarTower_of_annihilator_le (A := A) (f := f) hK
            let πBar : (K →₀ Ā) →ₗ[Ā] K := Finsupp.linearCombination Ā (id : K → K)
            have hExactCover : Function.Exact
                (LinearMap.ker πBar).subtype πBar := by
              simpa [πBar] using quotient_canonical_free_cover_exact (A := A) (f := f) hK
            let S : ShortComplex (ModuleCat A) :=
              ShortComplex.moduleCatMk
                ((LinearMap.ker πBar).subtype.restrictScalars A)
                (πBar.restrictScalars A)
                (Function.Exact.linearMap_comp_eq_zero hExactCover)
            have hFree :
                IsZero
                  ((((Tor (ModuleCat A) ((n + 1) + 1)).obj (ModuleCat.of A M)).obj
                    S.X₂)) := by
              simpa [S, πBar] using hfree K ⟨n + 1, hd⟩
            have hKerAnn : I ≤ Module.annihilator A (LinearMap.ker πBar) := by
              simpa [πBar] using
                span_le_annihilator_canonical_free_cover_ker (A := A) (f := f) hK
            have hKer :
                IsZero
                  ((((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
                    S.X₁)) := by
              have hn : n < r + 1 := lt_trans (Nat.lt_succ_self n) hd
              simpa [S, πBar] using ih n (Nat.lt_succ_self n) hn hKerAnn
            have hTail :
                ∃ δ :
                    ((((Tor (ModuleCat A) ((n + 1) + 1)).obj (ModuleCat.of A M)).obj
                        S.X₃) ⟶
                      (((Tor (ModuleCat A) (n + 1)).obj (ModuleCat.of A M)).obj
                        S.X₁)),
                  Function.Exact
                    ((((Tor (ModuleCat A) ((n + 1) + 1)).obj (ModuleCat.of A M)).map
                      S.g).hom)
                    δ.hom := by
              -- Proof comment: the named module-first five-term API supplies exactly the
              -- successor tail window needed by the canonical free-cover induction.
              exact
                tor_module_tail_exact_of_shortExact
                  (A := A) (M := M) (S := S)
                  (by
                    simpa [S, πBar] using
                      quotientCanonicalFreeCover_shortExact (A := A) (f := f) hK)
                  (n + 1)
            simpa [S, πBar] using
              isZero_tor_module_succ_of_tail_exact
                (A := A) (M := M) (S := S) (n + 1) hTail hFree hKer
  intro i
  -- Proof comment: instantiate the strengthened induction at the requested finite degree.
  exact hAll i.1 i.2 hK

/-- Helper for Chap10 Lemma 10 99 17: localized flatness on the generators and quotient
vanishing imply degree-one module-first Tor vanishing on every module. -/
lemma tor_module_one_vanishes_of_generator_descent
    (hlocal : ∀ i : Fin r, Module.Flat (Localization.Away (f i)) (LocalizedModule.Away (f i) M))
    (hquot : Module.Flat Ā M̄)
    (htor : ∀ i : Fin (r + 1), IsZero (TorQ[i.1 + 1]))
    (N : Type u) [AddCommGroup N] [Module A N] :
    IsZero ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A N))) := by
  -- Proof comment: the whole-ideal range is now stated in the module-first owner; the missing
  -- descent step is the module-first analogue of multiplication-by-the-last-generator.
  have hwhole :
      ∀ {K : Type u} [AddCommGroup K] [Module A K],
        I ≤ Module.annihilator A K →
          ∀ i : Fin (r + 1),
            IsZero
              ((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
                (ModuleCat.of A K))) := by
    intro K _ _ hK
    exact
      tor_module_annihilated_by_span_vanishes_in_range_of_free_cover_range
        (A := A) (M := M) (f := f) hquot htor hK
  cases r with
  | zero =>
      -- Proof comment: with no generators, the whole ideal is zero, so every module is already
      -- annihilated by it and the whole-ideal degree-one result applies directly.
      have hIbot : Ideal.span (Set.range f) = (⊥ : Ideal A) := by
        simp
      have hN : Ideal.span (Set.range f) ≤ Module.annihilator A N := by
        simpa [hIbot] using (bot_le : (⊥ : Ideal A) ≤ Module.annihilator A N)
      exact hwhole hN 0
  | succ s =>
      have hdesc :
          ∀ (t : ℕ) (g : Fin t → A),
            (∀ j : Fin t,
              Module.Flat (Localization.Away (g j)) (LocalizedModule.Away (g j) M)) →
            (∀ {K : Type u} [AddCommGroup K] [Module A K],
              Ideal.span (Set.range g) ≤ Module.annihilator A K →
                ∀ i : Fin (t + 1),
                  IsZero
                    ((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
                      (ModuleCat.of A K)))) →
            ∀ {K : Type u} [AddCommGroup K] [Module A K],
              (⊥ : Ideal A) ≤ Module.annihilator A K →
                IsZero
                  ((((Tor (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
                    (ModuleCat.of A K))) := by
        intro t
        induction t with
        | zero =>
            intro g _ hspan K _ _ hK
            -- Proof comment: after all generators have been removed, the degree-one entry of the
            -- current range is the desired Tor object.
            have hspanBot :
                Ideal.span (Set.range g) ≤ Module.annihilator A K := by
              simpa using hK
            simpa using hspan (K := K) hspanBot (0 : Fin 1)
        | succ t ih =>
            intro g hloc hspan K _ _ hK
            have hstep :
                ∀ {L : Type u} [AddCommGroup L] [Module A L],
                  Ideal.span (Set.range (Fin.init g)) ≤ Module.annihilator A L →
                    ∀ i : Fin (t + 1),
                      IsZero
                        ((((Tor (ModuleCat A) (i.1 + 1)).obj (ModuleCat.of A M)).obj
                          (ModuleCat.of A L))) := by
              -- Proof comment: remove the last generator using localized flatness at that
              -- generator and scalar injectivity on the corresponding Tor module.
              exact
                tor_module_generator_descent_step
                  (A := A) (M := M) (g := g) (hlocalLast := hloc (Fin.last t)) hspan
            exact ih (Fin.init g) (fun j ↦ hloc j.castSucc) hstep hK
      -- Proof comment: start from the whole ideal and descend through all generators until the
      -- zero ideal remains, which annihilates every module.
      exact hdesc (s + 1) f hlocal hwhole (bot_le : (⊥ : Ideal A) ≤ Module.annihilator A N)

end
