import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import stacks_proof.stacks_project.Chap12.Lemma_12_5_11
import stacks_proof.stacks_project.Chap12.Remark_12_29_2
import stacks_proof.stacks_project.Chap15.Lemma_15_59_10
import stacks_proof.stacks_project.Chap15.Lemma_15_88_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open DerivedCategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : ℕ → Type u} [∀ n, CommRing (A n)]
variable {ρ : ∀ n, A (n + 1) →+* A n}
variable [∀ n : ℕ, MonoidalCategory (ModuleCat (A n))]
variable [∀ n : ℕ, (curriedTensor (ModuleCat (A n))).Additive]
variable [∀ n : ℕ,
  ∀ X : ModuleCat (A n), ((curriedTensor (ModuleCat (A n))).obj X).Additive]

attribute [local instance] seqRingMod_abelian

local notation "DModSeq" => DerivedCategory (SeqRingMod A ρ)

/- Domain-style sampling for Lemma 15.88.8:
- primary domain: K-flat stagewise representatives of derived objects in
  `D(\mathrm{Mod}(\mathbf N, (A_n)))`;
- sampled owner declarations:
  `SeqRingMod`,
  `DerivedCategory.Q.obj`,
  `sequentialRingedModuleCochainEval`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.exists_epi_kFlatResolution`;
- best owner abstraction: a representative complex `M` together with an isomorphism
  `DerivedCategory.Q.obj M ≅ K`, with each stagewise evaluation complex carrying the canonical
  owner predicate `IsKFlat`;
- target layer here: a source-facing existence statement asserting that the stagewise evaluations
  of one representing complex satisfy the canonical K-flatness owner;
- primitive data: the representative complex `M` and its realization isomorphism
  `DerivedCategory.Q.obj M ≅ K`;
- derived API: the stagewise K-flatness assertions obtained by applying
  `sequentialRingedModuleCochainEval` and then the owner predicate `IsKFlat`.

Source/core/bridge triage:
- `source-facing`: the existence of a representative complex whose stagewise evaluations are
  K-flat;
- `core/canonical`: `DerivedCategory.Q.obj` for the realization surface and
  `CochainComplex.IsKFlat` for the stagewise property;
- `bridge/view`: `sequentialRingedModuleCochainEvaluation`; the canonical owner-level resolution
  theorem `CochainComplex.exists_epi_kFlatResolution` from Lemma `15.59.10` belongs to the proof
  route, not to the public owner surface. -/

-- Proof sketch: first use the owner-level companion
-- `exists_complex_representation_with_epi_transition_maps` from Lemma `15.88.7` to choose a
-- representative complex `M^•` of `K` whose evaluated transition maps are epimorphisms of
-- cochain complexes; internally this is obtained by replacing the canonical preimage complex
-- `DerivedCategory.Q.objPreimage K` by a quasi-isomorphic one. Then apply the owner-level
-- stagewise resolution theorem `CochainComplex.exists_epi_kFlatResolution` from Lemma `15.59.10`
-- to the evaluated complexes, replacing each stage by a quasi-isomorphic K-flat complex while
-- preserving compatibility with the transition maps, and reassemble the resulting stagewise data
-- into a representing complex of module systems.
/-- Helper for Lemma 15.88.8: each evaluated stage of a complex of module systems admits the
canonical ring-level K-flat resolution from Lemma `15.59.10`. -/
private lemma stagewise_exists_epi_kFlat_resolution
    (M : CochainComplex (SeqRingMod A ρ) ℤ) (n : ℕ) :
    ∃ (K : CochainComplex (ModuleCat (A n)) ℤ)
      (π : K ⟶ sequentialRingedModuleCochainEval A ρ n M),
      K.IsKFlat ∧ K.IsTermwiseFlat ∧ QuasiIso π ∧ Epi π := by
  -- Apply the ring-level K-flat replacement theorem directly to the evaluated stage complex.
  simpa using
    (CochainComplex.exists_epi_kFlatResolution
      (R := A n) (M := sequentialRingedModuleCochainEval A ρ n M))

/-- Helper for Lemma 15.88.8: Lemma `15.88.7` already provides the initial representative on the
public evaluation-step surface, so the remaining proof can stay entirely on
`sequentialRingedModuleCochainEvaluationStep A ρ n`. -/
private lemma exists_complex_representation_with_public_epi_transition_maps
    (K : DModSeq) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M) := by
  obtain ⟨M, e, hM⟩ := exists_complex_representation_with_epi_transition_maps (A := A) (ρ := ρ) K
  refine ⟨M, e, ?_⟩
  intro n
  -- The imported epi-transition model already computes the same successor map after unfolding the
  -- public stagewise evaluation abbreviations.
  simpa [sequentialRingedModuleCochainEvaluationStep, sequentialRingedModuleCochainEvaluation]
    using hM n

/-- Helper for Lemma 15.88.8: the stagewise evaluation family on `Mod(\mathbf N, (A_n))` is
conservative, so a morphism of systems is an isomorphism once every evaluated component is. -/
private theorem sequentialRingedModuleEvaluation_jointly_reflects_isomorphisms :
    JointlyReflectIsomorphisms (fun n : ℕ ↦ sequentialRingedModuleEvaluation A ρ n) := by
  refine ⟨fun {X Y} f _hf ↦ ?_⟩
  -- Unpack the sheaf morphism to the underlying natural transformation and test it componentwise.
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  simpa [sequentialRingedModuleEvaluation] using
    (inferInstance : IsIso (((sequentialRingedModuleEvaluation A ρ n).map f)))

/-- Helper for Lemma 15.88.8: evaluating the degree-`i` short-complex map of a chain map is
definitionally the same as taking the degree-`i` short-complex map after stagewise evaluation. -/
private theorem sequentialRingedModuleEval_shortComplex_map
    (n : ℕ) {M N : CochainComplex (SeqRingMod A ρ) ℤ}
    (α : M ⟶ N) (i : ℤ) :
    (((sequentialRingedModuleEvaluation A ρ n).mapShortComplex).map
        ((HomologicalComplex.shortComplexFunctor (SeqRingMod A ρ) (ComplexShape.up ℤ) i).map α)) =
      ((HomologicalComplex.shortComplexFunctor
          (ModuleCat (A n)) (ComplexShape.up ℤ) i).map
        ((sequentialRingedModuleCochainEvaluation A ρ n).map α)) := by
  -- Each component is literally the evaluated degreewise component of `α`.
  ext <;> rfl

/-- Helper for Lemma 15.88.8: if every evaluated short-complex map is a quasi-isomorphism, then
the evaluated homology map of the original short-complex morphism is an isomorphism at every
stage. -/
private theorem sequentialRingedModule_shortComplex_homologyMap_isIso_of_eval
    {S₁ S₂ : ShortComplex (SeqRingMod A ρ)}
    (φ : S₁ ⟶ S₂)
    (hφ : ∀ n : ℕ,
      ShortComplex.QuasiIso
        (((sequentialRingedModuleEvaluation A ρ n).mapShortComplex).map φ)) :
    ∀ n : ℕ,
      IsIso
        ((sequentialRingedModuleEvaluation A ρ n).map (ShortComplex.homologyMap φ)) := by
  intro n
  let F := sequentialRingedModuleEvaluation A ρ n
  have hφn :
      IsIso (ShortComplex.homologyMap (((sequentialRingedModuleEvaluation A ρ n).mapShortComplex).map φ)) := by
    -- The stagewise hypothesis is exactly the quasi-isomorphism criterion for the evaluated
    -- short-complex morphism.
    rw [← ShortComplex.quasiIso_iff]
    exact hφ n
  have hrewrite :
      F.map (ShortComplex.homologyMap φ) =
        (S₁.mapHomologyIso F).inv ≫
          ShortComplex.homologyMap ((F.mapShortComplex).map φ) ≫
          (S₂.mapHomologyIso F).hom := by
    -- Move the global homology map across evaluation using the canonical homology comparison
    -- isomorphisms.
    calc
      F.map (ShortComplex.homologyMap φ) =
          F.map (ShortComplex.homologyMap φ) ≫
            (S₂.mapHomologyIso F).inv ≫
              (S₂.mapHomologyIso F).hom := by
        simp [Category.assoc]
      _ =
          (S₁.mapHomologyIso F).inv ≫
            ShortComplex.homologyMap ((F.mapShortComplex).map φ) ≫
              (S₂.mapHomologyIso F).hom := by
        rw [ShortComplex.mapHomologyIso_inv_naturality]
        simp [Category.assoc]
  -- After rewriting, the evaluated homology map is a composite of isomorphisms.
  rw [hrewrite]
  infer_instance

/-- Helper for Lemma 15.88.8: a short-complex morphism in `\mathrm{Mod}(\mathbf N, (A_n))` is a
quasi-isomorphism once all of its stagewise evaluations are. -/
private theorem sequentialRingedModule_shortComplex_quasiIso_of_eval
    {S₁ S₂ : ShortComplex (SeqRingMod A ρ)}
    (φ : S₁ ⟶ S₂)
    (hφ : ∀ n : ℕ,
      ShortComplex.QuasiIso
        (((sequentialRingedModuleEvaluation A ρ n).mapShortComplex).map φ)) :
    ShortComplex.QuasiIso φ := by
  -- Reflect the homology-map isomorphism across the conservative evaluation family.
  rw [ShortComplex.quasiIso_iff]
  exact
    ((sequentialRingedModuleEvaluation_jointly_reflects_isomorphisms
        (A := A) (ρ := ρ)).isIso_iff (ShortComplex.homologyMap φ)).2
      (sequentialRingedModule_shortComplex_homologyMap_isIso_of_eval
        (A := A) (ρ := ρ) φ hφ)

/-- Helper for Lemma 15.88.8: stagewise quasi-isomorphism of the evaluated chain maps implies
degreewise quasi-isomorphism of the original chain map. -/
private theorem quasiIsoAt_of_stagewise_eval_quasiIso
    {M N : CochainComplex (SeqRingMod A ρ) ℤ}
    (α : M ⟶ N) (i : ℤ)
    (hα : ∀ n : ℕ,
      QuasiIso ((sequentialRingedModuleCochainEvaluation A ρ n).map α)) :
    QuasiIsoAt α i := by
  -- Reduce to the degree-`i` short-complex morphism and reflect that statement from the stagewise
  -- evaluations.
  rw [_root_.quasiIsoAt_iff]
  refine
    sequentialRingedModule_shortComplex_quasiIso_of_eval
      (A := A) (ρ := ρ)
      ((HomologicalComplex.shortComplexFunctor
          (SeqRingMod A ρ) (ComplexShape.up ℤ) i).map α) ?_
  intro n
  have hαn : QuasiIsoAt ((sequentialRingedModuleCochainEvaluation A ρ n).map α) i :=
    ((_root_.quasiIso_iff ((sequentialRingedModuleCochainEvaluation A ρ n).map α)).1 (hα n)) i
  -- Rewrite the evaluated short-complex morphism into the short-complex morphism of the
  -- evaluated chain map.
  rw [_root_.quasiIsoAt_iff] at hαn
  simpa [sequentialRingedModuleEval_shortComplex_map] using hαn

/-- Helper for Lemma 15.88.8: if a morphism of complexes in `\mathrm{Mod}(\mathbf N, (A_n))` is a
quasi-isomorphism after evaluating at every stage, then it is already a global quasi-isomorphism.
-/
private theorem quasiIso_of_stagewise_eval_quasiIso
    {M N : CochainComplex (SeqRingMod A ρ) ℤ}
    (α : M ⟶ N)
    (hα : ∀ n : ℕ,
      QuasiIso ((sequentialRingedModuleCochainEvaluation A ρ n).map α)) :
    QuasiIso α := by
  -- Route correction: the closing step should follow the source-faithful reflection argument from
  -- Lemma `15.88.7`, now written directly on the public evaluation functors.
  rw [_root_.quasiIso_iff]
  intro i
  exact quasiIsoAt_of_stagewise_eval_quasiIso (A := A) (ρ := ρ) α i hα

/-- Helper for Lemma 15.88.8: the successor-step pullback over an epimorphic transition should be
quasi-isomorphic to the source complex on the first projection. -/
private theorem quasiIso_tau₂_of_shortExact
    {R : Type u} [CommRing R]
    {S T : ShortComplex (CochainComplex (ModuleCat R) ℤ)} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T) (hτ₁ : QuasiIso φ.τ₁) (hτ₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  -- Route correction: stay on the local short-exact-row surface and use the derived-category
  -- triangle comparison directly, rather than importing the heavier chapter file.
  let φQ := triangleOfSES.map hS hT φ
  have hSQ : triangleOfSES hS ∈ distTriang (DerivedCategory (ModuleCat R)) := by
    simpa using triangleOfSES_distinguished hS
  have hTQ : triangleOfSES hT ∈ distTriang (DerivedCategory (ModuleCat R)) := by
    simpa using triangleOfSES_distinguished hT
  have hQ₁ : IsIso φQ.hom₁ := by
    simpa [φQ] using ((isIso_Q_map_iff_quasiIso (ModuleCat R) φ.τ₁).2 hτ₁)
  have hQ₃ : IsIso φQ.hom₃ := by
    simpa [φQ] using ((isIso_Q_map_iff_quasiIso (ModuleCat R) φ.τ₃).2 hτ₃)
  have hQ₂ : IsIso φQ.hom₂ := by
    simpa [φQ] using (isIso₂_of_isIso₁₃ φQ hSQ hTQ hQ₁ hQ₃ : IsIso φQ.hom₂)
  exact (isIso_Q_map_iff_quasiIso (ModuleCat R) φ.τ₂).1 (by simpa [φQ] using hQ₂)

/-- Helper for Lemma 15.88.8: the successor-step pullback over an epimorphic transition should be
quasi-isomorphic to the source complex on the first projection. -/
private theorem pullback_fst_quasiIso_of_epi_transition
    {R : Type u} [CommRing R]
    {X Y Z : CochainComplex (ModuleCat R) ℤ}
    (f : X ⟶ Z) (g : Y ⟶ Z) [Epi f] [QuasiIso g] :
    QuasiIso (pullback.fst f g) := by
  let Ssource : ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
    ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) (biprod.snd : X ⊞ Y ⟶ Y) (by simp)
  let Starget : ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
    ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Z) (biprod.snd : X ⊞ Z ⟶ Z) (by simp)
  have hSsource : Ssource.ShortExact := by
    -- First isolate the middle vertical map `𝟙_X ⊞ g` on the standard split rows.
    simpa [Ssource] using
      (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).shortExact
  have hStarget : Starget.ShortExact := by
    -- The target split row is the same standard biproduct short exact sequence.
    simpa [Starget] using
      (ShortComplex.Splitting.ofHasBinaryBiproduct X Z).shortExact
  let φmid : Ssource ⟶ Starget :=
    ShortComplex.Hom.mk (𝟙 X) (biprod.map (𝟙 X) g) g
      (by simp [Ssource, Starget])
      (by simp [Ssource, Starget])
  have hφmid : QuasiIso (biprod.map (𝟙 X) g) := by
    -- On the split rows, the outer quasi-isomorphisms are `𝟙_X` and `g`, so the middle map is a
    -- quasi-isomorphism by the short-exact-row comparison theorem.
    letI : QuasiIso (𝟙 X) := inferInstance
    exact
      quasiIso_tau₂_of_shortExact
        (R := R) hSsource hStarget φmid inferInstance inferInstance
  let sqPull : CommSq (pullback.fst f g) (pullback.snd f g) f g :=
    (IsPullback.of_hasPullback f g).toCommSq
  let Spull := sqPull.shortComplex'
  have hSpull : Spull.ShortExact := by
    -- The pullback row `0 → pullback → X ⊞ Y → Z → 0` is short exact because the pullback square
    -- is cartesian and the right map is epic.
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact
      (CategoryTheory.isPullback_iff_exact_biproduct_sequence sqPull).1
        (IsPullback.of_hasPullback f g)
  let sqSplit : CommSq (𝟙 X) f f (𝟙 Z) := CommSq.mk (by simp)
  let Ssplit := sqSplit.shortComplex'
  have hSsplit : Ssplit.ShortExact := by
    -- The comparison row `0 → X → X ⊞ Z → Z → 0` comes from the identity pullback square.
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact
      (CategoryTheory.isPullback_iff_exact_biproduct_sequence sqSplit).1
        (IsPullback.of_vert_isIso sqSplit)
  let φpull : Spull ⟶ Ssplit :=
    ShortComplex.Hom.mk (pullback.fst f g) (biprod.map (𝟙 X) g) (𝟙 Z)
      (by
        -- The left square is exactly the pullback universal identity after unpacking the two
        -- short-complex left maps.
        apply biprod.hom_ext <;> simp [Spull, Ssplit, sqPull, sqSplit, Category.assoc, pullback.condition])
      (by
        -- The right square is the defining compatibility of `biprod.map (𝟙_X) g` with the two
        -- right maps.
        simp [Spull, Ssplit, sqPull, sqSplit, Category.assoc])
  let φQ := triangleOfSES.map hSpull hSsplit φpull
  have hQpull : triangleOfSES hSpull ∈ distTriang (DerivedCategory (ModuleCat R)) := by
    simpa using triangleOfSES_distinguished hSpull
  have hQsplit : triangleOfSES hSsplit ∈ distTriang (DerivedCategory (ModuleCat R)) := by
    simpa using triangleOfSES_distinguished hSsplit
  have hQ₂ : IsIso φQ.hom₂ := by
    -- The middle comparison is the already established quasi-isomorphism `𝟙_X ⊞ g`.
    simpa [φQ] using
      ((isIso_Q_map_iff_quasiIso (ModuleCat R) (biprod.map (𝟙 X) g)).2 hφmid)
  have hQ₃ : IsIso φQ.hom₃ := by
    -- The right comparison is the identity on `Z`.
    simpa [φQ] using
      ((isIso_Q_map_iff_quasiIso (ModuleCat R) (𝟙 Z)).2 (by infer_instance : QuasiIso (𝟙 Z)))
  have hQ₁ : IsIso φQ.hom₁ := by
    -- Two-out-of-three on the morphism of distinguished triangles returns the left comparison as
    -- an isomorphism in the derived category.
    simpa [φQ] using
      (Pretriangulated.isIso₁_of_isIso₂₃ φQ hQpull hQsplit hQ₂ hQ₃ : IsIso φQ.hom₁)
  -- Translating back across `Q` shows that the pullback projection itself is a quasi-isomorphism.
  exact
    (isIso_Q_map_iff_quasiIso (ModuleCat R) (pullback.fst f g)).1
      (by simpa [φQ] using hQ₁)

/-- Helper for Lemma 15.88.8: a finite source-faithful prefix stores the chosen stagewise K-flat
complexes, their comparison maps to the fixed epi-transition representative `M`, and the strict
successor maps between consecutive stages. -/
private structure KFlatPrefix
    (M : CochainComplex (SeqRingMod A ρ) ℤ) (length : ℕ) where
  /-- The chosen K-flat stage complex at each index of the finite prefix. -/
  L : (m : Fin (length + 1)) → CochainComplex (ModuleCat (A m.1)) ℤ
  /-- The comparison map from the chosen stage complex to the evaluated stage of `M`. -/
  ψ : (m : Fin (length + 1)) →
    L m ⟶ sequentialRingedModuleCochainEval A ρ m.1 M
  /-- The strict successor map between consecutive chosen stage complexes. -/
  τ : (m : Fin length) →
    L (Fin.succ m) ⟶
      ((ModuleCat.restrictScalars (ρ m.1)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (L (Fin.castSucc m))
  /-- Each chosen stage complex is K-flat. -/
  isKFlat : (m : Fin (length + 1)) → (L m).IsKFlat
  /-- Each comparison map is a quasi-isomorphism. -/
  quasiIso_ψ : (m : Fin (length + 1)) → QuasiIso (ψ m)
  /-- The strict successor square commutes with the chosen comparison maps. -/
  ψ_compat : (m : Fin length) →
    ψ (Fin.succ m) ≫
        (sequentialRingedModuleCochainEvaluationStep A ρ m.1).app M =
      τ m ≫
        ((ModuleCat.restrictScalars (ρ m.1)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (ψ (Fin.castSucc m))

/-- Helper for Lemma 15.88.8: the source induction starts from a chosen K-flat resolution of the
stage-`0` evaluation, so the length-zero prefix has no successor data yet. -/
private noncomputable abbrev KFlatPrefix.base
    (M : CochainComplex (SeqRingMod A ρ) ℤ)
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀) :
    KFlatPrefix (A := A) (ρ := ρ) M 0 :=
  { L := fun
      | ⟨0, _⟩ => K₀
    ψ := fun
      | ⟨0, _⟩ => ψ₀
    τ := fun m ↦ nomatch m
    isKFlat := fun
      | ⟨0, _⟩ => hK₀
    quasiIso_ψ := fun
      | ⟨0, _⟩ => hψ₀
    ψ_compat := fun m ↦ nomatch m }

/-- Helper for Lemma 15.88.8: the terminal stage complex of a finite source-faithful prefix. -/
private noncomputable abbrev KFlatPrefix.last_complex
    {M : CochainComplex (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : KFlatPrefix (A := A) (ρ := ρ) M length) :
    CochainComplex (ModuleCat (A length)) ℤ :=
  S.L (Fin.last length)

/-- Helper for Lemma 15.88.8: the terminal comparison map of a finite source-faithful prefix. -/
private noncomputable abbrev KFlatPrefix.last_comparison
    {M : CochainComplex (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : KFlatPrefix (A := A) (ρ := ρ) M length) :
    S.last_complex ⟶ sequentialRingedModuleCochainEval A ρ length M :=
  S.ψ (Fin.last length)

/-- Helper for Lemma 15.88.8: the terminal stage of a finite source-faithful prefix is K-flat. -/
private theorem KFlatPrefix.last_isKFlat
    {M : CochainComplex (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : KFlatPrefix (A := A) (ρ := ρ) M length) :
    S.last_complex.IsKFlat := by
  -- This is exactly the last component of the stored K-flatness data.
  simpa [KFlatPrefix.last_complex] using S.isKFlat (Fin.last length)

/-- Helper for Lemma 15.88.8: the terminal comparison map of a finite source-faithful prefix is a
quasi-isomorphism. -/
private theorem KFlatPrefix.last_comparison_quasiIso
    {M : CochainComplex (SeqRingMod A ρ) ℤ} {length : ℕ}
    (S : KFlatPrefix (A := A) (ρ := ρ) M length) :
    QuasiIso S.last_comparison := by
  -- This is exactly the last component of the stored comparison quasi-isomorphisms.
  simpa [KFlatPrefix.last_comparison] using S.quasiIso_ψ (Fin.last length)

/-- Helper for Lemma 15.88.8: one source-faithful successor step should replace the pullback
`M_{n + 1} ×_{M_n} K_n` by a K-flat resolution and append it to the existing finite prefix. -/
private noncomputable abbrev KFlatPrefix.extend
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    {length : ℕ}
    (S : KFlatPrefix (A := A) (ρ := ρ) M length) :
    KFlatPrefix (A := A) (ρ := ρ) M (length + 1) := by
  let G : ModuleCat (A length) ⥤ ModuleCat (A (length + 1)) :=
    ModuleCat.restrictScalars (ρ length)
  let hGExact : exactFunctor (ModuleCat (A length)) (ModuleCat (A (length + 1))) G :=
    restrictScalars_exact (f := ρ length)
  letI : G.PreservesHomology := by
    letI : PreservesFiniteLimits G := (exactFunctor_iff G).1 hGExact |>.1
    letI : PreservesFiniteColimits G := (exactFunctor_iff G).1 hGExact |>.2
    -- Proof comment: exact restriction of scalars preserves the homology objects of cochain
    -- complexes.
    exact CategoryTheory.Functor.preservesHomologyOfExact G
  let F := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let step : sequentialRingedModuleCochainEval A ρ (length + 1) M ⟶
      F.obj (sequentialRingedModuleCochainEval A ρ length M) :=
    (sequentialRingedModuleCochainEvaluationStep A ρ length).app M
  letI : Epi step := by
    -- Proof comment: `step` is exactly the public epimorphic transition supplied by `hM`.
    simpa [step] using hM length
  let ψrestricted : F.obj S.last_complex ⟶
      F.obj (sequentialRingedModuleCochainEval A ρ length M) :=
    F.map S.last_comparison
  letI : QuasiIso S.last_comparison := S.last_comparison_quasiIso
  letI : QuasiIso ψrestricted := by
    -- Proof comment: the old terminal comparison remains a quasi-isomorphism after restriction of
    -- scalars because exact functors preserve homology.
    simpa [G, F, ψrestricted] using
      (HomologicalComplex.quasiIso_map_of_preservesHomology S.last_comparison G)
  let P : CochainComplex (ModuleCat (A (length + 1))) ℤ := pullback step ψrestricted
  let πpull : P ⟶ sequentialRingedModuleCochainEval A ρ (length + 1) M :=
    pullback.fst step ψrestricted
  letI : QuasiIso πpull := by
    -- Proof comment: this is the source pullback lemma for the cartesian square over the public
    -- epimorphic transition map.
    simpa [P, πpull] using
      (pullback_fst_quasiIso_of_epi_transition (R := A (length + 1)) step ψrestricted)
  obtain ⟨Knext, ψnext, hKnext, _, hψnext, _⟩ :=
    CochainComplex.exists_epi_kFlatResolution (R := A (length + 1)) (M := P)
  let ψlast : Knext ⟶ sequentialRingedModuleCochainEval A ρ (length + 1) M :=
    ψnext ≫ πpull
  let τlast : Knext ⟶ F.obj S.last_complex :=
    ψnext ≫ pullback.snd step ψrestricted
  letI : QuasiIso ψnext := hψnext
  letI : QuasiIso ψlast := by
    -- Proof comment: the new terminal comparison is the resolution map followed by the pullback
    -- projection, so it is a quasi-isomorphism by two-out-of-three.
    simpa [ψlast] using quasiIso_comp ψnext πpull
  refine
    { L := Fin.lastCases Knext S.L
      ψ := Fin.lastCases ψlast S.ψ
      τ := fun m ↦ by
        cases m using Fin.lastCases with
        | last =>
            -- Proof comment: the newly appended transition is exactly the map to the second
            -- pullback factor.
            simpa [τlast, F, KFlatPrefix.last_complex] using τlast
        | cast j =>
            -- Proof comment: every earlier transition is inherited unchanged from the shorter
            -- prefix.
            simpa [Fin.succ_castSucc] using S.τ j
      isKFlat := fun m ↦ by
        cases m using Fin.lastCases with
        | last =>
            -- Proof comment: the new last stage is K-flat by the chosen terminal resolution.
            simpa using hKnext
        | cast j =>
            -- Proof comment: K-flatness on the old stages is stored in the shorter prefix.
            simpa using S.isKFlat j
      quasiIso_ψ := fun m ↦ by
        cases m using Fin.lastCases with
        | last =>
            -- Proof comment: the new last comparison is the explicit quasi-isomorphic composite
            -- constructed above.
            simpa [ψlast] using (show QuasiIso ψlast from inferInstance)
        | cast j =>
            -- Proof comment: quasi-isomorphisms on the earlier stages are inherited verbatim.
            simpa using S.quasiIso_ψ j
      ψ_compat := fun m ↦ by
        cases m using Fin.lastCases with
        | last =>
            -- Proof comment: the new terminal square is the defining pullback relation, preceded
            -- by the resolution map `ψnext`.
            simpa [ψlast, τlast, step, ψrestricted, F, Category.assoc] using
              congrArg (fun k ↦ ψnext ≫ k) (pullback.condition step ψrestricted)
        | cast j =>
            -- Proof comment: the old compatibility squares are preserved unchanged on the
            -- `castSucc` part of the larger prefix.
            simpa [Fin.succ_castSucc] using S.ψ_compat j }

/-- Helper for Lemma 15.88.8: after extension, every earlier stage complex is recovered verbatim
on the `castSucc` part of the larger prefix. -/
@[simp] private theorem KFlatPrefix.extend_L_castSucc
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    {length : ℕ}
    (S : KFlatPrefix (A := A) (ρ := ρ) M length) (m : Fin (length + 1)) :
    (KFlatPrefix.extend (A := A) (ρ := ρ) (M := M) hM S).L (Fin.castSucc m) = S.L m := by
  -- Proof comment: `Fin.lastCases` is definitionally the old stage family away from the newly
  -- appended terminal index.
  simp [KFlatPrefix.extend]

/-- Helper for Lemma 15.88.8: after extension, every earlier comparison map is recovered
verbatim on the `castSucc` part of the larger prefix. -/
@[simp] private theorem KFlatPrefix.extend_ψ_castSucc
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    {length : ℕ}
    (S : KFlatPrefix (A := A) (ρ := ρ) M length) (m : Fin (length + 1)) :
    (KFlatPrefix.extend (A := A) (ρ := ρ) (M := M) hM S).ψ (Fin.castSucc m) = S.ψ m := by
  -- Proof comment: the extension only changes the newly appended terminal comparison map.
  simp [KFlatPrefix.extend]

/-- Helper for Lemma 15.88.8: recursively extend the source-faithful finite K-flat prefixes one
stage at a time along the public epimorphic transition maps. -/
private noncomputable def kFlatPrefixFamily
    (M : CochainComplex (SeqRingMod A ρ) ℤ)
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀) :
    (length : ℕ) → KFlatPrefix (A := A) (ρ := ρ) M length
  | 0 => KFlatPrefix.base (A := A) (ρ := ρ) M K₀ ψ₀ hK₀ hψ₀
  | length + 1 =>
      KFlatPrefix.extend (A := A) (ρ := ρ) (M := M) hM
        (kFlatPrefixFamily M hM K₀ ψ₀ hK₀ hψ₀ length)

/-- Helper for Lemma 15.88.8: the diagonal K-flat stage at `n` is the terminal complex of the
recursively chosen prefix of length `n`. -/
private noncomputable abbrev diagonal_kFlat_complex
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    CochainComplex (ModuleCat (A n)) ℤ :=
  (kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀ n).last_complex

/-- Helper for Lemma 15.88.8: the diagonal stagewise comparison at `n` is the terminal comparison
of the recursively chosen prefix of length `n`. -/
private noncomputable abbrev diagonal_kFlat_comparison
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n ⟶
      sequentialRingedModuleCochainEval A ρ n M :=
  (kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀ n).last_comparison

/-- Helper for Lemma 15.88.8: the last successor map in the `(n + 1)`-prefix is the raw diagonal
transition before transport-cleaning the copied stage `n` inside that larger prefix. -/
private noncomputable abbrev diagonal_kFlat_step_to_prefix_target
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ (n + 1) ⟶
      ((ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀ (n + 1)).L
          (Fin.castSucc (Fin.last n))) :=
  (kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀ (n + 1)).τ (Fin.last n)

/-- Helper for Lemma 15.88.8: the copied stage `n` inside the `(n + 1)`-prefix is literally the
same complex as the diagonal K-flat stage `n`. -/
@[simp] private theorem kFlatPrefixFamily_castSucc_last_complex
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    (kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀ (n + 1)).L
        (Fin.castSucc (Fin.last n)) =
      diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n := by
  -- Proof comment: recursive extension preserves the old terminal stage verbatim on the
  -- `castSucc` copy of stage `n`.
  simpa [diagonal_kFlat_complex, kFlatPrefixFamily] using
    (KFlatPrefix.extend_L_castSucc (A := A) (ρ := ρ) (M := M) hM
      (S := kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀ n)
      (m := Fin.last n))

/-- Helper for Lemma 15.88.8: the copied stage-`n` comparison inside the `(n + 1)`-prefix is
literally the diagonal comparison of stage `n`. -/
@[simp] private theorem kFlatPrefixFamily_castSucc_last_comparison
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    (kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀ (n + 1)).ψ
        (Fin.castSucc (Fin.last n)) =
      diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n := by
  -- Proof comment: recursive extension preserves the old terminal comparison on the `castSucc`
  -- copy of stage `n`.
  simpa [diagonal_kFlat_comparison, kFlatPrefixFamily] using
    (KFlatPrefix.extend_ψ_castSucc (A := A) (ρ := ρ) (M := M) hM
      (S := kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀ n)
      (m := Fin.last n))

/-- Helper for Lemma 15.88.8: before transport-cleaning the copied stage `n`, the last successor
map in the `(n + 1)`-prefix already satisfies the terminal comparison square. -/
private theorem diagonal_kFlat_step_to_prefix_target_comparison_compat
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ (n + 1) ≫
        (sequentialRingedModuleCochainEvaluationStep A ρ n).app M =
      diagonal_kFlat_step_to_prefix_target (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n ≫
        ((ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀ (n + 1)).ψ
            (Fin.castSucc (Fin.last n))) := by
  -- Proof comment: this is the stored compatibility at the last index of the `(n + 1)`-prefix.
  simpa [diagonal_kFlat_comparison, diagonal_kFlat_step_to_prefix_target,
    kFlatPrefixFamily, Fin.succ_last] using
    (kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀ (n + 1)).ψ_compat (Fin.last n)

/-- Helper for Lemma 15.88.8: after transport-cleaning the copied stage `n`, the diagonal K-flat
transition becomes a literal map to the diagonal K-flat stage `n`. -/
private noncomputable abbrev diagonal_kFlat_step
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ (n + 1) ⟶
      ((ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n) :=
  diagonal_kFlat_step_to_prefix_target (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n ≫
    (((ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (eqToIso
        (kFlatPrefixFamily_castSucc_last_complex (A := A) (ρ := ρ) (M := M)
          hM K₀ ψ₀ hK₀ hψ₀ n))).hom

/-- Helper for Lemma 15.88.8: after the same transport-cleaning, the diagonal K-flat transition
still satisfies the comparison square with the public evaluation step. -/
private theorem diagonal_kFlat_step_comparison_compat
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ (n + 1) ≫
        (sequentialRingedModuleCochainEvaluationStep A ρ n).app M =
      diagonal_kFlat_step (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n ≫
        ((ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n) := by
  -- Proof comment: transport-cleaning only replaces the copied target stage by the literal
  -- diagonal K-flat stage `n`.
  simpa [diagonal_kFlat_step] using
    diagonal_kFlat_step_to_prefix_target_comparison_compat
      (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ n

/-- Helper for Lemma 15.88.8: the underlying additive presheaf of the reassembled degree-`i`
term, obtained from the diagonal K-flat stage tower by `Functor.ofOpSequence`. -/
private abbrev diagonal_kFlat_reassembled_X_presheaf
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) :
    ℕᵒᵖ ⥤ AddCommGrpCat :=
  CategoryTheory.Functor.ofOpSequence
    (fun n ↦ AddCommGrpCat.ofHom
      ((diagonal_kFlat_step (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).f i).hom)

/-- Helper for Lemma 15.88.8: the `n`-th stage of the reassembled degree-`i` presheaf is the
degree-`i` term of the `n`-th diagonal K-flat stage complex. -/
@[simp] private theorem diagonal_kFlat_reassembled_X_presheaf_obj
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) (n : ℕᵒᵖ) :
    (diagonal_kFlat_reassembled_X_presheaf (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).obj n =
      AddCommGrpCat.of ((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).X i) := by
  cases n
  rfl

/-- Helper for Lemma 15.88.8: the successor map of the reassembled degree-`i` presheaf is the
degree-`i` component of the diagonal K-flat transition. -/
@[simp] private theorem diagonal_kFlat_reassembled_X_presheaf_map_succ
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) (n : ℕ) :
    (diagonal_kFlat_reassembled_X_presheaf (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).map
        ((homOfLE (Nat.le_succ n)).op) =
      AddCommGrpCat.ofHom
        ((diagonal_kFlat_step (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).f i).hom := by
  rfl

/-- Helper for Lemma 15.88.8: every longer transition in the reassembled degree-`i` presheaf
factors through the final successor map. -/
private theorem diagonal_kFlat_reassembled_X_presheaf_map_homOfLE_succ
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) {m k : ℕ} (h : m ≤ k) :
    (diagonal_kFlat_reassembled_X_presheaf (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).map
        (homOfLE (Nat.le_succ_of_le h)).op =
      (diagonal_kFlat_reassembled_X_presheaf (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).map
          ((homOfLE (Nat.le_succ k)).op) ≫
        (diagonal_kFlat_reassembled_X_presheaf (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).map
          (homOfLE h).op := by
  let F :=
    diagonal_kFlat_reassembled_X_presheaf (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i
  -- Proof comment: in `ℕᵒᵖ`, the long restriction arrow factors uniquely through the last
  -- successor step.
  have hh :
      (homOfLE (Nat.le_succ_of_le h)).op =
        (homOfLE (Nat.le_succ k)).op ≫ (homOfLE h).op := by
    subsingleton
  simpa [F, CategoryTheory.Functor.map_comp] using congrArg F.map hh

/-- Helper for Lemma 15.88.8: every transition map in the reassembled degree-`i` presheaf is
linear with respect to the corresponding ring transition map. -/
private theorem diagonal_kFlat_reassembled_X_presheaf_map_smul
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) :
    ∀ {m n : ℕ} (h : m ≤ n)
      (r : sequentialRingedModuleStageRing (A := A) (ρ := ρ) n)
      (x : (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).X i),
      AddCommGrpCat.Hom.hom
          ((diagonal_kFlat_reassembled_X_presheaf
              (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).map (homOfLE h).op)
          (r • x) =
        (((sequentialRingSystem A ρ).map (homOfLE h).op).hom r) •
          AddCommGrpCat.Hom.hom
            ((diagonal_kFlat_reassembled_X_presheaf
                (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).map (homOfLE h).op) x := by
  intro m n h
  induction h with
  | refl =>
      intro r x
      -- Proof comment: the identity transition is linear over the identity ring map.
      simp [sequentialRingSystem]
  | @step k h ih =>
      intro r x
      let F :=
        diagonal_kFlat_reassembled_X_presheaf
          (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i
      have hsucc :
          AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) (r • x) =
            (((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ k)).op)).hom r) •
              AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) x := by
        -- Proof comment: the final successor map is one of the stored chain maps in the diagonal
        -- K-flat tower, so its degree component is linear.
        simpa [F, diagonal_kFlat_reassembled_X_presheaf_map_succ, sequentialRingSystem] using
          (((diagonal_kFlat_step (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ k).f i).hom.map_smul r x)
      have hRing :
          (((sequentialRingSystem A ρ).map (homOfLE (Nat.le_succ_of_le h)).op).hom r) =
            ((sequentialRingSystem A ρ).map (homOfLE h).op).hom
              ((((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ k)).op)).hom r)) := by
        -- Proof comment: the ring transitions factor through the same final successor arrow.
        have hh :
            (homOfLE (Nat.le_succ_of_le h)).op =
              (homOfLE (Nat.le_succ k)).op ≫ (homOfLE h).op := by
          subsingleton
        simpa [sequentialRingSystem, CategoryTheory.Functor.map_comp, RingHom.comp_apply] using
          congrArg
            (fun f ↦ CommRingCat.Hom.hom ((sequentialRingSystem A ρ).map f) r)
            hh
      rw [diagonal_kFlat_reassembled_X_presheaf_map_homOfLE_succ
        (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i h]
      calc
        AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op) ≫ F.map (homOfLE h).op)
            (r • x) =
            AddCommGrpCat.Hom.hom (F.map (homOfLE h).op)
              (AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) (r • x)) := by
              rfl
        _ =
            AddCommGrpCat.Hom.hom (F.map (homOfLE h).op)
              ((((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ k)).op)).hom r) •
                AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) x) := by
              rw [hsucc]
        _ =
            ((sequentialRingSystem A ρ).map (homOfLE h).op).hom
                ((((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ k)).op)).hom r)) •
              AddCommGrpCat.Hom.hom (F.map (homOfLE h).op)
                (AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) x) := by
              simpa using
                ih
                  (((sequentialRingSystem A ρ).map ((homOfLE (Nat.le_succ k)).op)).hom r)
                  (AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) x)
        _ =
            (((sequentialRingSystem A ρ).map (homOfLE (Nat.le_succ_of_le h)).op).hom r) •
              AddCommGrpCat.Hom.hom (F.map (homOfLE h).op)
                (AddCommGrpCat.Hom.hom (F.map ((homOfLE (Nat.le_succ k)).op)) x) := by
              rw [← hRing]
        _ =
            (((sequentialRingSystem A ρ).map (homOfLE (Nat.le_succ_of_le h)).op).hom r) •
              AddCommGrpCat.Hom.hom
                (F.map ((homOfLE (Nat.le_succ k)).op) ≫ F.map (homOfLE h).op) x := by
              rfl

/-- Helper for Lemma 15.88.8: the transition maps of the reassembled degree-`i` additive
presheaf are linear over the sequential ring system. -/
private theorem diagonal_kFlat_reassembled_X_presheaf_linear
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) :
    ∀ {X Y : ℕᵒᵖ} (f : X ⟶ Y) (r : ↑((sequentialRingSystem A ρ).obj X))
      (m :
        ↑((diagonal_kFlat_reassembled_X_presheaf
            (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).obj X)),
      CategoryTheory.ConcreteCategory.hom
          ((diagonal_kFlat_reassembled_X_presheaf
              (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).map f)
          (r • m) =
        (CategoryTheory.ConcreteCategory.hom ((sequentialRingSystem A ρ).map f)) r •
          CategoryTheory.ConcreteCategory.hom
            ((diagonal_kFlat_reassembled_X_presheaf
                (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).map f)
            m := by
  intro X Y f r m
  cases X using Opposite.rec
  cases Y using Opposite.rec
  let h : Y ≤ X := by
    simpa using f.unop
  have hf : f = (homOfLE h).op := by
    subsingleton
  subst hf
  -- Proof comment: every arrow in `ℕᵒᵖ` is some restriction map `homOfLE`, so the linearity
  -- statement reduces to the factorization lemma above.
  simpa using
    diagonal_kFlat_reassembled_X_presheaf_map_smul
      (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i h r m

/-- Helper for Lemma 15.88.8: the indexing topology is chaotic, so the reassembled degree-`i`
presheaf is automatically a sheaf. -/
private theorem diagonal_kFlat_reassembled_X_isSheaf
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) :
    Presheaf.IsSheaf
      (diagonal_kFlat_reassembled_X_presheaf (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i) := by
  -- Proof comment: on the chaotic topology, every additive presheaf is already a sheaf.
  simpa [PresheafOfModules.ofPresheaf_presheaf] using
    (Presheaf.isSheaf_bot
      (diagonal_kFlat_reassembled_X_presheaf (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i))

/-- Helper for Lemma 15.88.8: the source-faithful reassembled degree-`i` object of
`\mathrm{Mod}(\mathbf N, (A_n))`. -/
private def diagonal_kFlat_reassembled_X
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) :
    SeqRingMod A ρ :=
  { val :=
      PresheafOfModules.ofPresheaf
        (diagonal_kFlat_reassembled_X_presheaf (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i)
        (diagonal_kFlat_reassembled_X_presheaf_linear
          (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i)
    isSheaf :=
      diagonal_kFlat_reassembled_X_isSheaf
        (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i }

/-- Helper for Lemma 15.88.8: evaluating the reassembled degree-`i` object at stage `n` recovers
the degree-`i` term of the `n`-th diagonal K-flat stage complex. -/
@[simp] private theorem diagonal_kFlat_reassembled_X_obj
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) (n : ℕ) :
    (diagonal_kFlat_reassembled_X (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).val.obj
        (Opposite.op n) =
      (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).X i := by
  rfl

/-- Helper for Lemma 15.88.8: the successor map of the reassembled degree-`i` object is exactly
the degree-`i` component of the diagonal K-flat transition. -/
@[simp] private theorem diagonal_kFlat_reassembled_X_map_succ
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) (n : ℕ) :
    (diagonal_kFlat_reassembled_X (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).val.map
        ((homOfLE (Nat.le_succ n)).op) =
      (diagonal_kFlat_step (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).f i := by
  rfl

/-- Helper for Lemma 15.88.8: the diagonal K-flat differentials commute with the successor maps,
so they assemble into a natural transformation between the reassembled degree objects. -/
private theorem diagonal_kFlat_reassembled_d_naturality
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i j : ℤ) (n : ℕ) :
    AddCommGrpCat.ofHom
        ((diagonal_kFlat_reassembled_X (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).val.map
          ((homOfLE (Nat.le_succ n)).op)).hom ≫
      AddCommGrpCat.ofHom
        ((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).d i j).hom =
    AddCommGrpCat.ofHom
        ((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ (n + 1)).d i j).hom ≫
      AddCommGrpCat.ofHom
        ((diagonal_kFlat_reassembled_X (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ j).val.map
          ((homOfLE (Nat.le_succ n)).op)).hom := by
  -- Proof comment: each diagonal transition is a chain map by construction.
  simpa [diagonal_kFlat_reassembled_X_map_succ] using
    (diagonal_kFlat_step (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).comm i j

/-- Helper for Lemma 15.88.8: the reassembled differential is linear over each stage ring. -/
private theorem diagonal_kFlat_reassembled_d_linear
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i j : ℤ) :
    ∀ (X : ℕᵒᵖ) (r : ↑((sequentialRingSystem A ρ).obj X))
      (m :
        ↑((diagonal_kFlat_reassembled_X (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).val.obj X)),
      CategoryTheory.ConcreteCategory.hom
          ((CategoryTheory.NatTrans.ofOpSequence
              (fun n ↦ AddCommGrpCat.ofHom
                ((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).d i j).hom)
              (diagonal_kFlat_reassembled_d_naturality
                (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i j)).app X)
          (r • m) =
        r •
          CategoryTheory.ConcreteCategory.hom
            ((CategoryTheory.NatTrans.ofOpSequence
                (fun n ↦ AddCommGrpCat.ofHom
                  ((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).d i j).hom)
                (diagonal_kFlat_reassembled_d_naturality
                  (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i j)).app X)
            m := by
  intro X r m
  -- Proof comment: the stagewise differential is linear over the local stage ring.
  cases X using Opposite.rec
  rfl

/-- Helper for Lemma 15.88.8: the reassembled differential `d : X^i → X^j` is the stagewise
family of diagonal K-flat differentials, viewed as a morphism in `SeqRingMod`. -/
private def diagonal_kFlat_reassembled_d
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i j : ℤ) :
    diagonal_kFlat_reassembled_X (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i ⟶
      diagonal_kFlat_reassembled_X (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ j :=
  { val :=
      PresheafOfModules.homMk
        (CategoryTheory.NatTrans.ofOpSequence
          (fun n ↦ AddCommGrpCat.ofHom
            ((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).d i j).hom)
          (diagonal_kFlat_reassembled_d_naturality
            (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i j))
        (diagonal_kFlat_reassembled_d_linear
          (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i j) }

/-- Helper for Lemma 15.88.8: evaluating the reassembled differential at stage `n` gives the
ordinary differential of the `n`-th diagonal K-flat stage complex. -/
@[simp] private theorem diagonal_kFlat_reassembled_d_app
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i j : ℤ) (n : ℕ) :
    (diagonal_kFlat_reassembled_d (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i j).val.app
        (Opposite.op n) =
      (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).d i j := by
  rfl

/-- Helper for Lemma 15.88.8: the reassembled differential has the same cochain shape relation as
the stagewise diagonal K-flat complexes. -/
private theorem diagonal_kFlat_reassembled_complex_shape
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀) :
    ∀ i j, ¬ (ComplexShape.up ℤ).Rel i j →
      diagonal_kFlat_reassembled_d (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i j = 0 := by
  intro i j hij
  ext n x
  change ((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).d i j).hom x = 0
  -- Proof comment: every stage of the diagonal tower is already a cochain complex.
  simpa using
    congrArg
      (fun f :
        (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).X i ⟶
          (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).X j ↦
            f.hom x)
      ((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).shape i j hij)

/-- Helper for Lemma 15.88.8: the reassembled differential squares to zero because this is true at
every stage of the diagonal K-flat tower. -/
private theorem diagonal_kFlat_reassembled_complex_d_comp_d
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀) :
    ∀ i j k, (ComplexShape.up ℤ).Rel i j → (ComplexShape.up ℤ).Rel j k →
      diagonal_kFlat_reassembled_d (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i j ≫
          diagonal_kFlat_reassembled_d (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ j k = 0 := by
  intro i j k hij hjk
  ext n x
  change
    (((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).d i j ≫
        (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).d j k).hom x) = 0
  -- Proof comment: the identity `d ≫ d = 0` is checked stagewise on the diagonal K-flat tower.
  simpa using
    congrArg
      (fun f :
        (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).X i ⟶
          (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).X k ↦
            f.hom x)
      ((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).d_comp_d'
        i j k hij hjk)

/-- Helper for Lemma 15.88.8: the diagonal K-flat stages reassemble into one global complex of
module systems. -/
private def diagonal_kFlat_reassembled_complex
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀) :
    CochainComplex (SeqRingMod A ρ) ℤ :=
  { X := diagonal_kFlat_reassembled_X (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀
    d := diagonal_kFlat_reassembled_d (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀
    shape := diagonal_kFlat_reassembled_complex_shape
      (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀
    d_comp_d' := diagonal_kFlat_reassembled_complex_d_comp_d
      (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ }

/-- Helper for Lemma 15.88.8: evaluating the reassembled complex at stage `n` gives the `n`-th
diagonal K-flat stage complex, degreewise. -/
private theorem diagonal_kFlat_reassembled_eval_obj_eq
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) (i : ℤ) :
    (sequentialRingedModuleCochainEval A ρ n
        (diagonal_kFlat_reassembled_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀)).X i =
      (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).X i := by
  simp [diagonal_kFlat_reassembled_complex]

/-- Helper for Lemma 15.88.8: the degreewise identifications in
`diagonal_kFlat_reassembled_eval_obj_eq` commute with the differentials. -/
private theorem diagonal_kFlat_reassembled_eval_iso_comm
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) (i j : ℤ) (_hij : (ComplexShape.up ℤ).Rel i j) :
    (eqToIso (diagonal_kFlat_reassembled_eval_obj_eq
        (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n i)).hom ≫
      (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).d i j =
    (sequentialRingedModuleCochainEval A ρ n
        (diagonal_kFlat_reassembled_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀)).d i j ≫
      (eqToIso (diagonal_kFlat_reassembled_eval_obj_eq
        (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n j)).hom := by
  -- Proof comment: both sides are the same stagewise differential after unfolding the evaluation.
  change (𝟙 _) ≫
      (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).d i j =
    (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).d i j ≫ 𝟙 _
  simp

/-- Helper for Lemma 15.88.8: evaluating the reassembled complex at stage `n` literally recovers
the `n`-th diagonal K-flat stage complex. -/
private noncomputable def diagonal_kFlat_reassembled_eval_iso
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    sequentialRingedModuleCochainEval A ρ n
        (diagonal_kFlat_reassembled_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀) ≅
      diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ eqToIso
      (diagonal_kFlat_reassembled_eval_obj_eq
        (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n i))
    (diagonal_kFlat_reassembled_eval_iso_comm
      (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n)

/-- Helper for Lemma 15.88.8: after conjugating by the evaluation isomorphisms, the evaluated
successor map of the reassembled complex is exactly the diagonal K-flat transition. -/
private theorem diagonal_kFlat_reassembled_eval_iso_naturality
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    (sequentialRingedModuleCochainEvaluationStep A ρ n).app
        (diagonal_kFlat_reassembled_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀) ≫
      (((ModuleCat.restrictScalars (ρ n)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (diagonal_kFlat_reassembled_eval_iso
          (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n)).hom =
    (diagonal_kFlat_reassembled_eval_iso
      (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ (n + 1)).hom ≫
      diagonal_kFlat_step (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n := by
  -- Proof comment: the reassembly was built so that the successor map is definitionally the
  -- chosen diagonal K-flat transition on every degree.
  ext i x
  simpa [diagonal_kFlat_reassembled_complex]

/-- Helper for Lemma 15.88.8: the stagewise diagonal comparison maps reassemble into a global chain
map from the reassembled K-flat complex back to the original complex. -/
private theorem diagonal_kFlat_reassembled_comparison_component_linear
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) :
    ∀ (X : ℕᵒᵖ) (r : ↑((sequentialRingSystem A ρ).obj X))
      (m :
        ↑((diagonal_kFlat_reassembled_X (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).val.obj X)),
      CategoryTheory.ConcreteCategory.hom
          ((CategoryTheory.NatTrans.ofOpSequence
              (fun n ↦ AddCommGrpCat.ofHom
                ((diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).f i).hom)
              (fun n ↦ by
                simpa [diagonal_kFlat_reassembled_X_presheaf_map_succ, Category.assoc] using
                  congrArg
                    (fun k ↦ k.f i)
                    (diagonal_kFlat_step_comparison_compat
                      (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ n))).app X)
          (r • m) =
        r •
          CategoryTheory.ConcreteCategory.hom
            ((CategoryTheory.NatTrans.ofOpSequence
                (fun n ↦ AddCommGrpCat.ofHom
                  ((diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).f i).hom)
                (fun n ↦ by
                  simpa [diagonal_kFlat_reassembled_X_presheaf_map_succ, Category.assoc] using
                    congrArg
                      (fun k ↦ k.f i)
                      (diagonal_kFlat_step_comparison_compat
                        (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ n))).app X)
            m := by
  intro X r m
  -- Proof comment: each stagewise comparison component is a morphism of modules over the local
  -- stage ring.
  cases X using Opposite.rec
  rfl

/-- Helper for Lemma 15.88.8: the stagewise compatibility squares for
`diagonal_kFlat_comparison` assemble into naturality for the reassembled degree components. -/
private theorem diagonal_kFlat_reassembled_comparison_naturality
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (i : ℤ) (n : ℕ) :
    AddCommGrpCat.ofHom
        ((diagonal_kFlat_reassembled_X (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i).val.map
          ((homOfLE (Nat.le_succ n)).op)).hom ≫
      AddCommGrpCat.ofHom (((M.X i).val.app (Opposite.op n)).hom) =
    AddCommGrpCat.ofHom (((M.X i).val.app (Opposite.op (n + 1))).hom) ≫
      AddCommGrpCat.ofHom
        ((diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).f i).hom := by
  -- Proof comment: this is exactly the stored comparison square in degree `i`.
  simpa [diagonal_kFlat_reassembled_X_map_succ, Category.assoc] using
    congrArg
      (fun k ↦ k.f i)
      (diagonal_kFlat_step_comparison_compat
        (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ n)

/-- Helper for Lemma 15.88.8: the reassembled stagewise diagonal comparison is a morphism of
cochain complexes. -/
private theorem diagonal_kFlat_reassembled_comparison_comm
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀) :
    ∀ i j (hij : (ComplexShape.up ℤ).Rel i j),
      diagonal_kFlat_reassembled_d (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ i j ≫
          { val :=
              PresheafOfModules.homMk
                (CategoryTheory.NatTrans.ofOpSequence
                  (fun n ↦ AddCommGrpCat.ofHom
                    ((diagonal_kFlat_comparison
                      (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).f j).hom)
                  (diagonal_kFlat_reassembled_comparison_naturality
                    (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ j))
                (diagonal_kFlat_reassembled_comparison_component_linear
                  (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ j) } =
        { val :=
            PresheafOfModules.homMk
              (CategoryTheory.NatTrans.ofOpSequence
                (fun n ↦ AddCommGrpCat.ofHom
                  ((diagonal_kFlat_comparison
                    (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).f i).hom)
                (diagonal_kFlat_reassembled_comparison_naturality
                  (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ i))
              (diagonal_kFlat_reassembled_comparison_component_linear
                (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ i) } ≫
          M.d i j := by
  intro i j hij
  ext n x
  change
    (((diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).d i j ≫
        (diagonal_kFlat_comparison
          (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).f j).hom x) =
      (((diagonal_kFlat_comparison
          (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).f i ≫ (M.d i j).val.app n).hom x)
  -- Proof comment: chain-map compatibility is checked stagewise against the diagonal comparison.
  simpa using
    congrArg
      (fun f :
        (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).X i ⟶
          (sequentialRingedModuleCochainEval A ρ n.unop M).X j ↦
            f.hom x)
      ((diagonal_kFlat_comparison
          (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n.unop).comm i j)

/-- Helper for Lemma 15.88.8: the reassembled stagewise diagonal comparison defines a global chain
map from the diagonal K-flat complex back to the original representative. -/
private def diagonal_kFlat_reassembled_comparison
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀) :
    diagonal_kFlat_reassembled_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ ⟶ M :=
  { f := fun i ↦
      { val :=
          PresheafOfModules.homMk
            (CategoryTheory.NatTrans.ofOpSequence
              (fun n ↦ AddCommGrpCat.ofHom
                ((diagonal_kFlat_comparison
                  (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).f i).hom)
              (diagonal_kFlat_reassembled_comparison_naturality
                (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ i))
            (diagonal_kFlat_reassembled_comparison_component_linear
              (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ i) }
    comm' := diagonal_kFlat_reassembled_comparison_comm
      (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀ }

/-- Helper for Lemma 15.88.8: evaluating the global comparison at stage `n` recovers the stagewise
diagonal comparison preceded by the canonical evaluation isomorphism. -/
private theorem diagonal_kFlat_reassembled_comparison_eval
    {M : CochainComplex (SeqRingMod A ρ) ℤ}
    (hM : ∀ n : ℕ, Epi (sequentialRingedModuleCochainEvaluationStep A ρ n M))
    (K₀ : CochainComplex (ModuleCat (A 0)) ℤ)
    (ψ₀ : K₀ ⟶ sequentialRingedModuleCochainEval A ρ 0 M)
    (hK₀ : K₀.IsKFlat)
    (hψ₀ : QuasiIso ψ₀)
    (n : ℕ) :
    (sequentialRingedModuleCochainEvaluation A ρ n).map
        (diagonal_kFlat_reassembled_comparison
          (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀) =
      (diagonal_kFlat_reassembled_eval_iso
        (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).hom ≫
        diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n := by
  -- Proof comment: both sides have the same degreewise components after evaluation at stage `n`.
  ext i x
  rfl

/-- Helper for Lemma 15.88.8: K-flatness transports across an isomorphism of stagewise module
complexes. -/
private theorem module_complex_isKFlat_of_iso
    {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat R) ℤ}
    (e : K ≅ L) (hK : K.IsKFlat) :
    L.IsKFlat := by
  -- Proof comment: transport the defining tensor-acyclicity condition across the induced tensor
  -- isomorphism on the right factor.
  rw [CochainComplex.isKFlat_iff] at hK ⊢
  intro M _ hM
  have hTensorK : (HomologicalComplex.tensorObj M K).Acyclic := hK hM
  let eTensor :
      HomologicalComplex.tensorObj M K ≅ HomologicalComplex.tensorObj M L :=
    tensor_right_iso (R := R) M e
  exact acyclic_of_iso (R := R) eTensor hTensorK

/-- Helper for Lemma 15.88.8: once the epi-transition representative from Lemma `15.88.7` is
chosen, the remaining source-faithful task is to run the pullback-and-resolution induction and
reassemble the compatible stagewise K-flat complexes into one global complex of systems. -/
private lemma exists_stagewise_kFlat_representation_from_epi_transition_model
    (K : DModSeq) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n : ℕ,
        (sequentialRingedModuleCochainEval A ρ n M).IsKFlat := by
  obtain ⟨M, e, hM⟩ :=
    exists_complex_representation_with_public_epi_transition_maps (A := A) (ρ := ρ) K
  obtain ⟨K₀, ψ₀, hK₀, _, hψ₀, _⟩ :=
    stagewise_exists_epi_kFlat_resolution (A := A) (ρ := ρ) M 0
  let hprefix :=
    kFlatPrefixFamily (A := A) (ρ := ρ) M hM K₀ ψ₀ hK₀ hψ₀
  let N :=
    diagonal_kFlat_reassembled_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀
  let α :=
    diagonal_kFlat_reassembled_comparison (A := A) (ρ := ρ) (M := M) hM K₀ ψ₀ hK₀ hψ₀
  have hα :
      ∀ n : ℕ, QuasiIso ((sequentialRingedModuleCochainEvaluation A ρ n).map α) := by
    intro n
    have hEval :
        QuasiIso
          ((diagonal_kFlat_reassembled_eval_iso
              (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).hom) := inferInstance
    have hStage :
        QuasiIso
          (diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n) :=
      KFlatPrefix.last_comparison_quasiIso (hprefix n)
    letI :
        QuasiIso
          ((diagonal_kFlat_reassembled_eval_iso
              (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).hom) := hEval
    letI :
        QuasiIso
          (diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n) := hStage
    -- Proof comment: the evaluated global comparison is the evaluation isomorphism followed by
    -- the known stagewise quasi-isomorphism from the finite prefix.
    simpa [α, diagonal_kFlat_reassembled_comparison_eval]
      using
        (quasiIso_comp
          ((diagonal_kFlat_reassembled_eval_iso
              (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).hom)
          (diagonal_kFlat_comparison (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n))
  have hQα : QuasiIso α :=
    quasiIso_of_stagewise_eval_quasiIso (A := A) (ρ := ρ) α hα
  have hIsoQα : IsIso (DerivedCategory.Q.map α) :=
    (isIso_Q_map_iff_quasiIso (SeqRingMod A ρ) α).2 hQα
  refine ⟨N, asIso (DerivedCategory.Q.map α) ≪≫ e, ?_⟩
  intro n
  have hStageKFlat :
      (diagonal_kFlat_complex (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).IsKFlat :=
    KFlatPrefix.last_isKFlat (hprefix n)
  -- Proof comment: transport K-flatness across the canonical evaluation isomorphism.
  exact
    module_complex_isKFlat_of_iso
      (R := A n)
      ((diagonal_kFlat_reassembled_eval_iso
        (A := A) (ρ := ρ) hM K₀ ψ₀ hK₀ hψ₀ n).symm)
      hStageKFlat

/-- Lemma 15.88.8: for an inverse system of rings `A₀ ← A₁ ← A₂ ← ⋯`, every object of
`D(\mathrm{Mod}(\mathbf N, (A_n)))` admits a representative by a system of cochain complexes
`(K_n^•)` in which every stage `K_n^•` is K-flat. -/
@[stacks 091G]
theorem exists_kFlat_complex_representation
    (K : DModSeq) :
    ∃ (M : CochainComplex (SeqRingMod A ρ) ℤ)
      (_ : DerivedCategory.Q.obj M ≅ K),
      ∀ n : ℕ,
        (sequentialRingedModuleCochainEval A ρ n M).IsKFlat := by
  -- Reduce to the source-faithful epi-transition model from Lemma `15.88.7`.
  simpa using
    exists_stagewise_kFlat_representation_from_epi_transition_model
      (A := A) (ρ := ρ) K

end
