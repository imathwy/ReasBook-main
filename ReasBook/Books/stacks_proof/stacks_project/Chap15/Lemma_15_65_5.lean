import Mathlib
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap13.Lemma_13_15_4
import StacksProject_2024.Chap13.Lemma_13_9_8
import StacksProject_2024.Chap13.Lemma_13_19_8
import StacksProject_2024.Chap15.Lemma_15_65_2
import StacksProject_2024.Chap15.Lemma_15_65_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [Ring R]

private abbrev ModCat := ModuleCat.{u} R
local notation "Cpx" => CochainComplex (ModCat (R := R)) ℤ
local notation "FiniteProjectiveClass" => (fun P : ModCat (R := R) ↦ Module.Finite R P ∧ Projective P)
local notation "FiniteFreeClass" => (fun P : ModCat (R := R) ↦ Module.Free R P ∧ Module.Finite R P)
local notation "Ho" => HomotopyCategory (ModCat (R := R)) (ComplexShape.up ℤ)
local notation "H" => DerivedCategory.homologyFunctor (ModCat (R := R))
private abbrev HoQ : Cpx ⥤ Ho :=
  HomotopyCategory.quotient (ModCat (R := R)) (ComplexShape.up ℤ)
private abbrev FreeObj : CategoryTheory.ObjectProperty (ModCat (R := R)) :=
  fun M ↦ Module.Free R M

/-- Helper for Lemma 15.65.5: free `R`-modules contain a zero object, so the generic bounded-above
replacement theorem can be applied to the free-module object property. -/
local instance freeObj_containsZero :
    CategoryTheory.ObjectProperty.ContainsZero (FreeObj (R := R)) where
  exists_zero := ⟨ModuleCat.of R PUnit,
    (ModuleCat.isZero_iff_subsingleton).2 inferInstance,
    Module.Free.of_subsingleton (R := R) (N := PUnit)⟩

/-- Helper for Lemma 15.65.5: every `R`-module admits an epimorphism from a free module. -/
local instance freeObj_hasEpiCover :
    CategoryTheory.ObjectProperty.HasEpiCover (FreeObj (R := R)) where
  exists_epi (M : ModCat (R := R)) := by
    refine ⟨(ModuleCat.free R).obj (M : Type u), ?_,
      (ModuleCat.adj R).counit.app M, ?_⟩
    · -- The standard finitely supported basis makes the chosen source free.
      change Module.Free R ((M : Type u) →₀ R)
      exact Module.Free.of_basis
        (Finsupp.basisSingleOne : Module.Basis (M : Type u) R ((M : Type u) →₀ R))
    · -- Each element is hit by the basis vector supported at that element.
      refine (ModuleCat.epi_iff_surjective _).2 ?_
      intro m
      refine ⟨ModuleCat.freeMk m, ?_⟩
      have hCounit :
          (ModuleCat.adj R).counit.app M = ModuleCat.freeDesc (fun x : (M : Type u) ↦ x) := by
        simpa [ModuleCat.adj_homEquiv] using ((ModuleCat.adj R).homEquiv_symm_id M).symm
      simpa [hCounit] using
        (ModuleCat.freeDesc_apply (R := R) (f := fun x : (M : Type u) ↦ x) m)

/-- Helper for Lemma 15.65.5: conjugating a homotopy-category map along
`DerivedCategory.quotientCompQhIso` recovers the corresponding `DerivedCategory.Q`-image. -/
private theorem quotientCompQhIso_homCongr_map
    {E K : Cpx} (f : E ⟶ K) :
    (Iso.homCongr
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K))
      (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f)) =
        DerivedCategory.Q.map f := by
  -- This is the naturality square for the comparison isomorphism `quotient ⋙ Qh ≅ Q`.
  change
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫
        DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K =
      DerivedCategory.Q.map f
  have hnat :
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K =
        (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app E ≫
          DerivedCategory.Q.map f := by
    simpa [Functor.comp_map] using
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.naturality f
  calc
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫
        DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K =
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app E ≫
          DerivedCategory.Q.map f) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app E ≫ k)
                hnat
    _ = DerivedCategory.Q.map f := by
          simpa using
            (Iso.inv_hom_id_assoc
              ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
              (DerivedCategory.Q.map f))

/-- Helper for Lemma 15.65.5: a pseudo-coherent complex admits an actual bounded-above
quasi-isomorphic model by termwise finite free modules. -/
private theorem exists_termwiseFiniteFree_quasiIso_of_isPseudoCoherent
    {K : Cpx} (hK : K.IsPseudoCoherent) :
    ∃ F : CochainComplex.MinusWithTermsIn FiniteFreeClass,
      ∃ α : (F : Cpx) ⟶ K, QuasiIso α := by
  rcases hK with ⟨E, ⟨b, hEb⟩, hEfree, α, hα⟩
  letI : E.IsTermwiseFiniteFree := hEfree
  let F : CochainComplex.MinusWithTermsIn FiniteFreeClass :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hEb⟩⟩, fun i ↦
      CochainComplex.IsTermwiseFiniteFree.out (E := E) i⟩
  let P : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hEb⟩⟩, fun i ↦ by
      -- Each finite free term is projective.
      change Projective (E.X i)
      infer_instance⟩
  let eHom :
      (DerivedCategory.Qh.obj (HoQ.obj E) ⟶
        DerivedCategory.Qh.obj (HoQ.obj K)) ≃
      (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj K) :=
    Iso.homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
  let αh :
      DerivedCategory.Qh.obj (HoQ.obj E) ⟶
        DerivedCategory.Qh.obj (HoQ.obj K) :=
    eHom.symm α
  -- Lift the derived isomorphism back to a strict chain map because the source is bounded above
  -- projective.
  obtain ⟨βh, hβh⟩ :=
    (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective
      (𝒜 := ModuleCat R) P K).surjective αh
  obtain ⟨β, rfl⟩ := HoQ.map_surjective βh
  have hQβ : DerivedCategory.Q.map β = α := by
    -- Transport the equality in `Qh` back through `quotientCompQhIso`.
    exact eHom.injective <| by
      simpa [αh, quotientCompQhIso_homCongr_map (R := R) (f := β)] using congrArg eHom hβh
  have hIsoQβ : IsIso (DerivedCategory.Q.map β) := by
    simpa [hQβ] using hα
  -- The lifted chain map is therefore a quasi-isomorphism.
  have hβQuasi : QuasiIso β := by
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) β).1 hIsoQβ
  exact ⟨F, β, hβQuasi⟩

/-- Helper for Lemma 15.65.5: a pseudo-coherent complex admits an actual bounded-above
quasi-isomorphic model by termwise finite projective modules. -/
private theorem exists_termwiseFiniteProjective_quasiIso_of_isPseudoCoherent
    {K : Cpx} (hK : K.IsPseudoCoherent) :
    ∃ P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass,
      ∃ α : (P : Cpx) ⟶ K, QuasiIso α := by
  obtain ⟨F, α, hα⟩ :=
    exists_termwiseFiniteFree_quasiIso_of_isPseudoCoherent (R := R) hK
  let P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass :=
    ⟨(F : CochainComplex.MinusWithTermsIn FiniteFreeClass), fun i ↦ by
      -- Forget the free structure and keep the finite/projective package.
      rcases F.term_mem i with ⟨hfree, hfinite⟩
      exact ⟨hfinite, by
        letI : Module.Free R ((F : Cpx).X i) := hfree
        infer_instance⟩⟩
  exact ⟨P, α, hα⟩

/-- Helper for Lemma 15.65.5: a finite projective module admits a split finite free cover. -/
private theorem exists_split_finiteFree_cover
    (M : ModuleCat R) [Module.Finite R M] [Projective M] :
    ∃ n : ℕ,
      ∃ π : ModuleCat.of R (Fin n → R) ⟶ M,
        ∃ ι : M ⟶ ModuleCat.of R (Fin n → R),
          Epi π ∧ ι ≫ π = 𝟙 M := by
  obtain ⟨n, π, ι, hπsurj, -, hπι⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R M
  refine ⟨n, ModuleCat.ofHom π, ModuleCat.ofHom ι, ?_, ?_⟩
  · -- Surjectivity of the chosen finite free cover is the categorical epimorphism statement.
    exact (ModuleCat.epi_iff_surjective _).2 hπsurj
  · -- The section is a literal splitting of the chosen cover.
    ext x
    simpa [LinearMap.comp_apply] using
      congrArg (fun f : M →ₗ[R] M ↦ f x) hπι

/-- Helper for Lemma 15.65.5: a split cover identifies its source with the biproduct of the
concrete kernel and the target module. The kernel is placed first to keep the comparison formulas
definitionally simple, and later source-style formulas may braid this biproduct once at the call
site. -/
private noncomputable def kernel_biprod_iso_of_split_cover
    {M G : ModuleCat R} (π : G ⟶ M) (ι : M ⟶ G)
    [Epi π] (hι : ι ≫ π = 𝟙 M) :
    G ≅ ModuleCat.of R (LinearMap.ker π.hom) ⊞ M := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact := by
    -- Proof comment: `kernel.ι π ⟶ G ⟶ M` is the standard short exact sequence of `π`.
    refine { exact := ShortComplex.exact_kernel π }
  let σ : S.Splitting :=
    ShortComplex.Splitting.ofExactOfSection S hS.exact ι hι inferInstance
  let e₀ : G ≅ kernel π ⊞ M := σ.isoBinaryBiproduct
  -- Proof comment: replace the abstract kernel object by the concrete submodule kernel used later.
  exact e₀ ≪≫ biprod.mapIso (ModuleCat.kernelIsoKer π) (Iso.refl M)

/-- Helper for Lemma 15.65.5: under the split-cover biproduct identification, the projection to
the target module is the original cover map. -/
private theorem kernel_biprod_iso_of_split_cover_hom_snd
    {M G : ModuleCat R} (π : G ⟶ M) (ι : M ⟶ G)
    [Epi π] (hι : ι ≫ π = 𝟙 M) :
    (kernel_biprod_iso_of_split_cover (R := R) π ι hι).hom ≫ biprod.snd = π := by
  -- Proof comment: `isoBinaryBiproduct` is defined by the splitting retraction and the quotient
  -- map, so the right projection is literally `π`.
  simp [kernel_biprod_iso_of_split_cover, ShortComplex.Splitting.isoBinaryBiproduct]

/-- Helper for Lemma 15.65.5: under the split-cover biproduct identification, the inclusion of
the target module is the chosen section of the cover. -/
private theorem kernel_biprod_iso_of_split_cover_inr_inv
    {M G : ModuleCat R} (π : G ⟶ M) (ι : M ⟶ G)
    [Epi π] (hι : ι ≫ π = 𝟙 M) :
    biprod.inr ≫ (kernel_biprod_iso_of_split_cover (R := R) π ι hι).inv = ι := by
  -- Proof comment: the inverse of `isoBinaryBiproduct` is built from the kernel inclusion and
  -- the chosen section, so the right summand inclusion recovers `ι`.
  simp [kernel_biprod_iso_of_split_cover, ShortComplex.Splitting.isoBinaryBiproduct]
  rfl

/-- Helper for Lemma 15.65.5: if `c ≤ i`, then the retained degree `i` lies in the image of the
lower brutal truncation embedding `n ↦ c + n`. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (c i : ℤ) (hci : c ≤ i) :
    (ComplexShape.embeddingUpIntGE c).f (Int.toNat (i - c)) = i := by
  -- The difference `i - c` is nonnegative exactly on the retained side of the truncation.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.65.5: in a retained degree, the lower brutal truncation term is
canonically the original term. -/
private noncomputable def lower_stupid_truncation_x_iso
    (E : Cpx) (c i : ℤ) (hci : c ≤ i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i ≅ E.X i :=
  E.stupidTruncXIso (ComplexShape.embeddingUpIntGE c)
    (embeddingUpIntGE_toNat_sub_eq c i hci)

/-- Helper for Lemma 15.65.5: the chosen proof `c ≤ i` does not affect the retained-degree
identification for lower brutal truncation. -/
private theorem lower_stupid_truncation_x_iso_hom_eq
    (E : Cpx) (c i : ℤ) {h h' : c ≤ i} :
    (lower_stupid_truncation_x_iso E c i h).hom =
      (lower_stupid_truncation_x_iso E c i h').hom := by
  -- The retained-degree isomorphism only depends on the inequality, not on its proof term.
  cases Subsingleton.elim h h'
  rfl

/-- Helper for Lemma 15.65.5: after transporting along the retained-degree identifications, the
differential of the lower brutal truncation is the original differential. -/
private theorem lower_stupid_truncation_d_via_x_iso
    (E : Cpx) (c : ℤ) {i j : ℤ}
    (hci : c ≤ i) (hcj : c ≤ j) :
    (lower_stupid_truncation_x_iso E c i hci).inv ≫
      (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
      (lower_stupid_truncation_x_iso E c j hcj).hom =
        E.d i j := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntGE c
  let i₀ : ℕ := Int.toNat (i - c)
  let j₀ : ℕ := Int.toNat (j - c)
  have hi₀ : e.f i₀ = i := embeddingUpIntGE_toNat_sub_eq c i hci
  have hj₀ : e.f j₀ = j := embeddingUpIntGE_toNat_sub_eq c j hcj
  -- First peel off the `extend` differential, then the `restriction` differential.
  change (lower_stupid_truncation_x_iso E c i hci).inv ≫
      ((E.restriction e).extend e).d i j ≫
      (lower_stupid_truncation_x_iso E c j hcj).hom =
        E.d i j
  rw [HomologicalComplex.extend_d_eq (K := E.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := E) (e := e) hi₀ hj₀]
  simp [lower_stupid_truncation_x_iso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso,
    e, i₀, j₀]

/-- Helper for Lemma 15.65.5: the component maps of the canonical lower-truncation inclusion. -/
private noncomputable def lower_stupid_truncation_inclusion_f
    (E : Cpx) (c i : ℤ) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i ⟶ E.X i :=
  if hci : c ≤ i then
    (lower_stupid_truncation_x_iso E c i hci).hom
  else
    0

/-- Helper for Lemma 15.65.5: in retained degrees, the canonical lower-truncation inclusion is
the transported identity map. -/
private theorem lower_stupid_truncation_inclusion_f_of_ge
    (E : Cpx) (c : ℤ) {i : ℤ} (hci : c ≤ i) :
    lower_stupid_truncation_inclusion_f E c i =
      (lower_stupid_truncation_x_iso E c i hci).hom := by
  -- Unfold the inclusion component and keep only the retained-degree branch.
  simp [lower_stupid_truncation_inclusion_f, hci]

/-- Helper for Lemma 15.65.5: in retained degrees, the canonical lower-truncation inclusion is an
isomorphism on components. -/
private theorem lower_stupid_truncation_inclusion_f_isIso_of_ge
    (E : Cpx) (c : ℤ) {i : ℤ} (hci : c ≤ i) :
    IsIso (lower_stupid_truncation_inclusion_f E c i) := by
  -- The retained component is literally one of the chosen degreewise identifications.
  rw [lower_stupid_truncation_inclusion_f_of_ge E c hci]
  infer_instance

/-- Helper for Lemma 15.65.5: the canonical componentwise map from the lower brutal truncation to
the original complex is a chain map. -/
private theorem lower_stupid_truncation_inclusion_comm
    (E : Cpx) (c : ℤ) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      lower_stupid_truncation_inclusion_f E c i ≫ E.d i j =
        (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
          lower_stupid_truncation_inclusion_f E c j := by
  intro i j hij
  by_cases hci : c ≤ i
  · have hcj : c ≤ j := by
      have hij' : j = i + 1 := by
        simpa [ComplexShape.up, eq_comm] using hij
      omega
    -- On retained degrees, the inclusion is the identity after transport.
    rw [lower_stupid_truncation_inclusion_f_of_ge E c hci,
      lower_stupid_truncation_inclusion_f_of_ge E c hcj]
    calc
      (lower_stupid_truncation_x_iso E c i hci).hom ≫ E.d i j =
          (lower_stupid_truncation_x_iso E c i hci).hom ≫
            ((lower_stupid_truncation_x_iso E c i hci).inv ≫
              (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
                (lower_stupid_truncation_x_iso E c j hcj).hom) := by
              rw [lower_stupid_truncation_d_via_x_iso E c hci hcj]
    _ = (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
            (lower_stupid_truncation_x_iso E c j hcj).hom := by
              simp
  · have hzero :
        Limits.IsZero ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i) := by
      -- Below the cutoff, the source term of the truncation is zero.
      exact E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i
        (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hci)
    by_cases hcj : c ≤ j
    · have hsrczero :
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j = 0 :=
        hzero.eq_of_src ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j) 0
      -- When the source term vanishes, the square is zero for formal reasons.
      simp [lower_stupid_truncation_inclusion_f, hci, hcj, hsrczero]
    · -- If both degrees are discarded, both components of the square are zero.
      simp [lower_stupid_truncation_inclusion_f, hci, hcj]

/-- Helper for Lemma 15.65.5: the lower brutal truncation has a canonical inclusion into the
original complex. -/
private noncomputable def lower_stupid_truncation_inclusion
    (E : Cpx) (c : ℤ) :
    E.stupidTrunc (ComplexShape.embeddingUpIntGE c) ⟶ E :=
  { f := fun i ↦ lower_stupid_truncation_inclusion_f E c i
    comm' := lower_stupid_truncation_inclusion_comm E c }

/-- Helper for Lemma 15.65.5: the predecessor in the cochain shape is `i - 1`. -/
private theorem cochain_prev_eq (i : ℤ) :
    (ComplexShape.up ℤ).prev i = i - 1 :=
  ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.65.5: the successor in the cochain shape is `i + 1`. -/
private theorem cochain_next_eq (i : ℤ) :
    (ComplexShape.up ℤ).next i = i + 1 :=
  ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.65.5: above the cutoff, the first object of the lower brutal truncation
short complex identifies with the original first object. -/
private noncomputable def lower_stupid_truncation_sc_X₁_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).X₁ ≅ (E.sc i).X₁ :=
  lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i)
    (by
      have hi_prev : c ≤ i - 1 := by omega
      simpa [cochain_prev_eq i] using hi_prev)

/-- Helper for Lemma 15.65.5: above the cutoff, the middle object of the lower brutal truncation
short complex identifies with the original middle object. -/
private noncomputable def lower_stupid_truncation_sc_X₂_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).X₂ ≅ (E.sc i).X₂ := by
  -- The middle object is exactly the degree-`i` term, which is retained above the cutoff.
  simpa [HomologicalComplex.sc] using
    (lower_stupid_truncation_x_iso E c i (by omega))

/-- Helper for Lemma 15.65.5: above the cutoff, the third object of the lower brutal truncation
short complex identifies with the original third object. -/
private noncomputable def lower_stupid_truncation_sc_X₃_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).X₃ ≅ (E.sc i).X₃ :=
  lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i)
    (by
      have hi_next : c ≤ i + 1 := by omega
      simpa [cochain_next_eq i] using hi_next)

/-- Helper for Lemma 15.65.5: above the cutoff, the first square of the short-complex
identification commutes. -/
private theorem lower_stupid_truncation_sc_f_comm_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (lower_stupid_truncation_sc_X₁_iso_of_gt E c i hci).hom ≫ (E.sc i).f =
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).f ≫
        (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom := by
  have hi_prev : c ≤ (ComplexShape.up ℤ).prev i := by
    rw [cochain_prev_eq i]
    omega
  have hi_mid : c ≤ i := by
    omega
  have hX₁ :
      (lower_stupid_truncation_sc_X₁_iso_of_gt E c i hci).hom =
        (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).hom := by
    exact
      lower_stupid_truncation_x_iso_hom_eq E c ((ComplexShape.up ℤ).prev i)
  have hX₂ :
      (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom =
        (lower_stupid_truncation_x_iso E c i hi_mid).hom := by
    exact lower_stupid_truncation_x_iso_hom_eq E c i (h := by omega) (h' := hi_mid)
  rw [hX₁, hX₂]
  -- After transport, the left short-complex map is just the predecessor differential.
  calc
    (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).hom ≫
        E.d ((ComplexShape.up ℤ).prev i) i =
      (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).hom ≫
        ((lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).inv ≫
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d ((ComplexShape.up ℤ).prev i) i ≫
            (lower_stupid_truncation_x_iso E c i hi_mid).hom) := by
              rw [lower_stupid_truncation_d_via_x_iso E c hi_prev hi_mid]
    _ = ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).f ≫
          (lower_stupid_truncation_x_iso E c i hi_mid).hom := by
            simp [HomologicalComplex.sc]

/-- Helper for Lemma 15.65.5: above the cutoff, the second square of the short-complex
identification commutes. -/
private theorem lower_stupid_truncation_sc_g_comm_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom ≫ (E.sc i).g =
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).g ≫
        (lower_stupid_truncation_sc_X₃_iso_of_gt E c i hci).hom := by
  have hi_mid : c ≤ i := by
    omega
  have hi_next : c ≤ (ComplexShape.up ℤ).next i := by
    rw [cochain_next_eq i]
    omega
  have hX₂ :
      (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom =
        (lower_stupid_truncation_x_iso E c i hi_mid).hom := by
    exact lower_stupid_truncation_x_iso_hom_eq E c i (h := by omega) (h' := hi_mid)
  have hX₃ :
      (lower_stupid_truncation_sc_X₃_iso_of_gt E c i hci).hom =
        (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i) hi_next).hom := by
    exact
      lower_stupid_truncation_x_iso_hom_eq E c ((ComplexShape.up ℤ).next i)
  rw [hX₂, hX₃]
  -- After transport, the right short-complex map is just the successor differential.
  calc
    (lower_stupid_truncation_x_iso E c i hi_mid).hom ≫
        E.d i ((ComplexShape.up ℤ).next i) =
      (lower_stupid_truncation_x_iso E c i hi_mid).hom ≫
        ((lower_stupid_truncation_x_iso E c i hi_mid).inv ≫
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i ((ComplexShape.up ℤ).next i) ≫
            (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i) hi_next).hom) := by
              rw [lower_stupid_truncation_d_via_x_iso E c hi_mid hi_next]
    _ = ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).g ≫
          (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i) hi_next).hom := by
            simp [HomologicalComplex.sc]

/-- Helper for Lemma 15.65.5: above the cutoff, the degree-`i` short complex of the lower brutal
truncation is canonically the same as the degree-`i` short complex of `E`. -/
private noncomputable def lower_stupid_truncation_sc_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i ≅ E.sc i :=
  ShortComplex.isoMk
    (lower_stupid_truncation_sc_X₁_iso_of_gt E c i hci)
    (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci)
    (lower_stupid_truncation_sc_X₃_iso_of_gt E c i hci)
    (lower_stupid_truncation_sc_f_comm_of_gt E c i hci)
    (lower_stupid_truncation_sc_g_comm_of_gt E c i hci)

/-- Helper for Lemma 15.65.5: above the cutoff, the canonical inclusion from the lower brutal
truncation induces an isomorphism on homology. -/
private theorem homologyMap_lower_stupid_truncation_inclusion_isIso_above
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    IsIso (HomologicalComplex.homologyMap (lower_stupid_truncation_inclusion E c) i) := by
  let φ :
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i) ⟶ E.sc i :=
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).map
      (lower_stupid_truncation_inclusion E c))
  have hi_prev : c ≤ i - 1 := by omega
  have hi_mid : c ≤ i := by omega
  have hi_next : c ≤ i + 1 := by omega
  have hφ : φ = (lower_stupid_truncation_sc_iso_of_gt E c i hci).hom := by
    -- All three components are the retained-degree inclusion maps.
    ext
    · simp [φ, lower_stupid_truncation_sc_iso_of_gt, lower_stupid_truncation_sc_X₁_iso_of_gt,
        HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
        lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge,
        hi_prev]
    · simp [φ, lower_stupid_truncation_sc_iso_of_gt, lower_stupid_truncation_sc_X₂_iso_of_gt,
        HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
        lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge,
        hi_mid]
    · simp [φ, lower_stupid_truncation_sc_iso_of_gt, lower_stupid_truncation_sc_X₃_iso_of_gt,
        HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
        lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge,
        hi_next]
  -- Transport invertibility along the canonical short-complex isomorphism.
  change IsIso (CategoryTheory.ShortComplex.homologyMap φ)
  rw [hφ]
  exact
    (show IsIso
      (CategoryTheory.ShortComplex.homologyMap
        (lower_stupid_truncation_sc_iso_of_gt E c i hci).hom) by
          infer_instance)

/-- Helper for Lemma 15.65.5: at the cutoff degree, the canonical inclusion from the lower brutal
truncation induces an epimorphism on cycles. -/
private theorem lower_stupid_truncation_cyclesMap_epi_at_cutoff
    (E : Cpx) (c : ℤ) :
    Epi (HomologicalComplex.cyclesMap (lower_stupid_truncation_inclusion E c) c) := by
  change Epi
    (ShortComplex.cyclesMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
        (lower_stupid_truncation_inclusion E c)))
  let φ :
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc c) ⟶ E.sc c :=
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
      (lower_stupid_truncation_inclusion E c))
  have hτ₂ : IsIso φ.τ₂ := by
    -- Degree `c` is retained, so the middle component is an isomorphism.
    simpa [φ, HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
      lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge] using
      (lower_stupid_truncation_inclusion_f_isIso_of_ge E c (show c ≤ c by simp))
  have hcnext : c ≤ (ComplexShape.up ℤ).next c := by
    rw [cochain_next_eq c]
    omega
  have hτ₃ : IsIso φ.τ₃ := by
    -- Degree `c + 1` is retained as well, so the right component is an isomorphism.
    simpa [φ, HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
      lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge, ComplexShape.up]
      using (lower_stupid_truncation_inclusion_f_isIso_of_ge E c hcnext)
  letI : IsIso φ.τ₂ := hτ₂
  letI : Mono φ.τ₃ := by infer_instance
  letI : IsIso (ShortComplex.cyclesMap φ) := by infer_instance
  infer_instance

/-- Helper for Lemma 15.65.5: at the cutoff degree, the canonical inclusion from the lower brutal
truncation induces an epimorphism on homology. -/
private theorem homologyMap_lower_stupid_truncation_inclusion_epi_at_cutoff
    (E : Cpx) (c : ℤ) :
    Epi (HomologicalComplex.homologyMap (lower_stupid_truncation_inclusion E c) c) := by
  -- Reduce to the short-complex homology map and descend the cycles epimorphism.
  simpa [HomologicalComplex.homologyMap, HomologicalComplex.cyclesMap] using
    (ShortComplex.epi_homologyMap_of_epi_cyclesMap'
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
        (lower_stupid_truncation_inclusion E c))
      (show Epi
        (ShortComplex.cyclesMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
            (lower_stupid_truncation_inclusion E c))) by
          simpa [HomologicalComplex.cyclesMap] using
            lower_stupid_truncation_cyclesMap_epi_at_cutoff (R := R) E c))

/-- Helper for Lemma 15.65.5: the lower brutal truncation is supported in degrees `≥ c`. -/
private theorem lower_stupid_truncation_isStrictlyGE
    (E : Cpx) (c : ℤ) :
    CochainComplex.IsStrictlyGE ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c) : Cpx)) c := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  -- Below the cutoff, the truncation is zero by construction.
  refine E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i ?_
  simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hi

/-- Helper for Lemma 15.65.5: a lower brutal truncation inherits any upper support bound from the
ambient complex. -/
private theorem lower_stupid_truncation_isStrictlyLE
    (E : Cpx) (c b : ℤ) [E.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c) : Cpx)) b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_cases hci : c ≤ i
  · let e := lower_stupid_truncation_x_iso E c i hci
    have hzero : Limits.IsZero (E.X i) := by
      simpa using E.isZero_of_isStrictlyLE b i hi
    -- A retained term above the upper bound is identified with a zero original term.
    exact hzero.of_iso e
  · have hzero :
        Limits.IsZero ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i) := by
      refine E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i ?_
      simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hci
    exact hzero

/-- Helper for Lemma 15.65.5: lower brutal truncation preserves termwise finite freeness. -/
private theorem isTermwiseFiniteFree_lower_stupid_truncation
    (E : Cpx) (c : ℤ) [E.IsTermwiseFiniteFree] :
    CochainComplex.IsTermwiseFiniteFree
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c) : Cpx)) := by
  refine ⟨fun i ↦ ?_⟩
  by_cases hci : c ≤ i
  · let e := lower_stupid_truncation_x_iso E c i hci
    rcases CochainComplex.IsTermwiseFiniteFree.out (E := E) i with ⟨hFree, hFinite⟩
    -- Retained terms are canonically the original finite free terms.
    exact
      ⟨Module.Free.of_equiv e.toLinearEquiv.symm,
        Module.Finite.of_surjective e.toLinearEquiv.symm.toLinearMap
          e.toLinearEquiv.symm.surjective⟩
  · have hzero : Limits.IsZero ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i) := by
      refine E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i ?_
      simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hci
    let _ :
        Subsingleton (((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i : ModuleCat R)) :=
      ModuleCat.subsingleton_of_isZero hzero
    let eZero :
        (((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i : ModuleCat R)) ≃ₗ[R]
          (Fin 0 → R) :=
      LinearEquiv.ofSubsingleton _ _
    have hFreeZero :
        Module.Free R ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i : ModuleCat R) :=
      Module.Free.of_equiv eZero.symm
    have hFiniteZero :
        Module.Finite R ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i : ModuleCat R) :=
      Module.Finite.of_surjective
        (0 : (Fin 0 → R) →ₗ[R] (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i) <| by
          intro x
          refine ⟨0, ?_⟩
          exact Subsingleton.elim _ _
    -- Discarded terms are zero, hence finite free.
    exact ⟨hFreeZero, hFiniteZero⟩

/-- Helper for Lemma 15.65.5: after lower brutal truncation at `m`, the comparison with the
original bounded-above model still has the required homology window for `m`-pseudo-coherence. -/
private theorem homology_window_of_lower_truncation_comparison
    {E K : Cpx} (m : ℤ) (a : E ⟶ K)
    (ha_iso : ∀ i : ℤ, m < i → IsIso (HomologicalComplex.homologyMap a i))
    (ha_epi : Epi (HomologicalComplex.homologyMap a m)) :
    (∀ i : ℤ,
      m < i →
        IsIso
          (HomologicalComplex.homologyMap
            (lower_stupid_truncation_inclusion E m ≫ a) i)) ∧
      Epi
        (HomologicalComplex.homologyMap
          (lower_stupid_truncation_inclusion E m ≫ a) m) := by
  constructor
  · intro i hi
    rw [HomologicalComplex.homologyMap_comp]
    letI :
        IsIso
          (HomologicalComplex.homologyMap
            (lower_stupid_truncation_inclusion E m) i) :=
      homologyMap_lower_stupid_truncation_inclusion_isIso_above E m i hi
    letI : IsIso (HomologicalComplex.homologyMap a i) := ha_iso i hi
    -- Above the cutoff, both factors are homology isomorphisms.
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    letI :
        Epi
          (HomologicalComplex.homologyMap
            (lower_stupid_truncation_inclusion E m) m) :=
      homologyMap_lower_stupid_truncation_inclusion_epi_at_cutoff E m
    letI : Epi (HomologicalComplex.homologyMap a m) := ha_epi
    -- At the cutoff, both factors are epimorphisms on homology.
    infer_instance

/-- Helper for Lemma 15.65.5: a bounded-above actual finite-free quasi-isomorphism already gives
all `m`-pseudo-coherent witnesses by lower brutal truncation. -/
private theorem isMPseudoCoherent_of_boundedAbove_termwiseFiniteFree_quasiIso
    {K : Cpx} {F : CochainComplex.MinusWithTermsIn FiniteFreeClass}
    (α : (F : Cpx) ⟶ K) (hα : QuasiIso α) :
    ∀ m : ℤ, K.IsMPseudoCoherent m := by
  intro m
  have hminus := CochainComplex.MinusWithTermsIn.minus (P := FiniteFreeClass) F
  obtain ⟨b, hFle⟩ := CochainComplex.MinusWithTermsIn.exists_isStrictlyLE (P := FiniteFreeClass) F
  let P : Cpx := (F : Cpx).stupidTrunc (ComplexShape.embeddingUpIntGE m)
  have hPge : P.IsStrictlyGE m := by
    -- Lower brutal truncation creates the desired lower support bound.
    simpa [P] using lower_stupid_truncation_isStrictlyGE (F : Cpx) m
  have hPle : P.IsStrictlyLE b := by
    letI : (F : Cpx).IsStrictlyLE b := hFle
    -- The original upper bound survives lower brutal truncation.
    simpa [P] using lower_stupid_truncation_isStrictlyLE (F : Cpx) m b
  have hPfree : P.IsTermwiseFiniteFree := by
    letI : (F : Cpx).IsTermwiseFiniteFree := ⟨fun i ↦ F.term_mem i⟩
    -- Retained terms stay finite free, and discarded terms are zero.
    simpa [P] using isTermwiseFiniteFree_lower_stupid_truncation (F : Cpx) m
  have hQαIso : IsIso (DerivedCategory.Q.map α) := by
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) α).2 hα
  have hαHomologyIso :
      ∀ i : ℤ, IsIso (HomologicalComplex.homologyMap α i) := by
    intro i
    exact
      (homologyMap_isIso_iff_homologyFunctor_map_Q_isIso
        (R := R) α i).2 inferInstance
  have hwindow :=
    homology_window_of_lower_truncation_comparison
      (R := R) m α (fun i _ ↦ hαHomologyIso i) (by
        letI : IsIso (HomologicalComplex.homologyMap α m) := hαHomologyIso m
        infer_instance)
  refine ⟨P, ⟨m, b, hPge, hPle⟩, hPfree, DerivedCategory.Q.map (lower_stupid_truncation_inclusion (F : Cpx) m ≫ α), ?_, ?_⟩
  · intro i hi
    have hIsoChain :
        IsIso
          (HomologicalComplex.homologyMap
            (lower_stupid_truncation_inclusion (F : Cpx) m ≫ α) i) :=
      hwindow.1 i hi
    -- Convert the chain-level homology isomorphism to the derived witness required by the
    -- definition of `IsMPseudoCoherent`.
    exact
      (homologyMap_isIso_iff_homologyFunctor_map_Q_isIso
        (R := R) (lower_stupid_truncation_inclusion (F : Cpx) m ≫ α) i).1 hIsoChain
  · have hEpiChain :
        Epi
          (HomologicalComplex.homologyMap
            (lower_stupid_truncation_inclusion (F : Cpx) m ≫ α) m) :=
      hwindow.2
    -- The cutoff epimorphism is likewise transported through the cochain/derived comparison.
    exact
      (homologyMap_epi_iff_homologyFunctor_map_Q_epi
        (R := R) (lower_stupid_truncation_inclusion (F : Cpx) m ≫ α) m).1 hEpiChain

/-- Helper for Lemma 15.65.5: a `0`-pseudo-coherent complex has eventually vanishing homology. -/
private theorem exists_homology_vanishing_bound_of_isZeroPseudoCoherent
    {K : Cpx} (hK : K.IsMPseudoCoherent 0) :
    ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.homology i) := by
  rcases hK with ⟨E, ⟨a, d, hEa, hEd⟩, hEfree, α, hαgt, hα0⟩
  refine ⟨max d 0, ?_⟩
  intro i hi
  have hd : d < i := lt_of_le_of_lt (le_max_left d 0) hi
  have hi0 : 0 < i := lt_of_le_of_lt (le_max_right d 0) hi
  letI : E.IsStrictlyLE d := hEd
  -- Above the upper support bound of the witness, the witness homology is already zero.
  have hEzero : IsZero (E.homology i) := by
    simpa using E.isZero_of_isLE d i hd
  let eE : (H i).obj (DerivedCategory.Q.obj E) ≅ E.homology i :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E
  let eK : (H i).obj (DerivedCategory.Q.obj K) ≅ K.homology i :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app K
  have hsourceZero : IsZero ((H i).obj (DerivedCategory.Q.obj E)) := by
    exact eE.isZero_iff.2 hEzero
  have htargetZero : IsZero ((H i).obj (DerivedCategory.Q.obj K)) := by
    -- In strictly positive degrees the `0`-pseudo-coherent witness is an isomorphism on homology.
    letI : IsIso ((H i).map α) := hαgt i hi0
    let eα : (H i).obj (DerivedCategory.Q.obj E) ≅ (H i).obj (DerivedCategory.Q.obj K) :=
      asIso ((H i).map α)
    exact eα.isZero_iff.1 hsourceZero
  -- Transport the derived homology vanishing back to ordinary cochain homology.
  exact eK.isZero_iff.1 htargetZero

/-- Helper for Lemma 15.65.5: homology vanishing above `b` already gives a bounded-above
quasi-isomorphic model by free modules. This isolates the remaining blocker in the source proof to
upgrading the free terms to finite free terms. -/
private theorem exists_boundedAbove_termwiseFree_quasiIso_of_homology_vanishing
    {K : CochainComplex (ModCat (R := R)) ℤ} {b : ℤ}
    (hvanish : ∀ i : ℤ, b < i → IsZero (K.homology i)) :
    ∃ Q : CochainComplex (ModCat (R := R)) ℤ,
      Q.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Free R (Q.X i)) ∧
          ∃ α : Q ⟶ K, QuasiIso α := by
  -- Apply the generic bounded-above replacement theorem with the free-module object property.
  obtain ⟨Q, α, hQ⟩ :=
    exists_quasiIso_with_terms_in_of_isZero_homology_above
      (P := FreeObj (R := R)) b K hvanish
  refine ⟨Q, hQ.strictlyLE, ?_, α, hQ.quasiIso⟩
  intro i
  -- The replacement theorem records that every term of `Q` is free.
  exact hQ.term_mem i

/-- Helper for Lemma 15.65.5: a quasi-isomorphism lets us transport all fixed-degree
`m`-pseudo-coherence statements from the target complex back to the source complex. -/
private theorem forall_isMPseudoCoherent_of_quasiIso_target
    {Q K : Cpx} (α : Q ⟶ K) (hα : QuasiIso α)
    (hK : ∀ m : ℤ, K.IsMPseudoCoherent m) :
    ∀ m : ℤ, Q.IsMPseudoCoherent m := by
  intro m
  -- Proof comment: `DerivedCategory.Q.map α` is an isomorphism, so the degree-`m` owner
  -- transports directly across the resulting derived-category isomorphism.
  have hQα : IsIso (DerivedCategory.Q.map α) := by
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) α).2 hα
  exact
    isMPseudoCoherent_of_iso
      (asIso (DerivedCategory.Q.map α)).symm m (hK m)

/-- Helper for Lemma 15.65.5: a pseudo-coherent cochain complex is `m`-pseudo-coherent in every
degree. This packages the already-closed `(1) → (2)` route for reuse below. -/
private theorem forall_isMPseudoCoherent_of_isPseudoCoherent
    {K : Cpx} (hK : K.IsPseudoCoherent) :
    ∀ m : ℤ, K.IsMPseudoCoherent m := by
  obtain ⟨F, α, hα⟩ :=
    exists_termwiseFiniteFree_quasiIso_of_isPseudoCoherent (R := R) hK
  -- Proof comment: once a bounded-above finite-free model exists, lower brutal truncation gives
  -- the fixed-degree witnesses uniformly in `m`.
  exact
    isMPseudoCoherent_of_boundedAbove_termwiseFiniteFree_quasiIso
      (R := R) α hα

/-- Helper for Lemma 15.65.5: a bounded-above termwise finite-free quasi-isomorphism already
packages the definition of pseudo-coherence of the target complex. -/
private theorem isPseudoCoherent_of_boundedAbove_termwiseFiniteFree_quasiIso
    {K : Cpx} {F : CochainComplex.MinusWithTermsIn FiniteFreeClass}
    (α : (F : Cpx) ⟶ K) (hα : QuasiIso α) :
    K.IsPseudoCoherent := by
  obtain ⟨b, hFle⟩ := CochainComplex.MinusWithTermsIn.exists_isStrictlyLE (P := FiniteFreeClass) F
  have hQα : IsIso (DerivedCategory.Q.map α) := by
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) α).2 hα
  -- Proof comment: the owner `MinusWithTermsIn FiniteFreeClass` supplies both the upper bound and
  -- the termwise finite-free structure required by Definition `15.65.1`.
  refine ⟨(F : Cpx), ⟨b, hFle⟩, ?_, DerivedCategory.Q.map α, hQα⟩
  exact ⟨fun i ↦ F.term_mem i⟩

/-- Helper for Lemma 15.65.5: once a bare bounded-above termwise finite-free complex and a
quasi-isomorphism have been constructed, the canonical `MinusWithTermsIn FiniteFreeClass` owner is
immediate. -/
private theorem exists_minusWithTermsIn_termwiseFiniteFree_quasiIso_of_strictlyLE
    {Q F : Cpx} {b : ℤ}
    (hFle : F.IsStrictlyLE b)
    [F.IsTermwiseFiniteFree]
    (β : F ⟶ Q) (hβ : QuasiIso β) :
    ∃ F' : CochainComplex.MinusWithTermsIn FiniteFreeClass,
      (F' : Cpx).IsStrictlyLE b ∧
        ∃ β' : (F' : Cpx) ⟶ Q, QuasiIso β' := by
  -- Proof comment: package the already-constructed bare model into the bounded-above owner and
  -- keep the same comparison map.
  let F' : CochainComplex.MinusWithTermsIn FiniteFreeClass :=
    ⟨⟨F, (CochainComplex.minus_iff (ModuleCat R) F).2 ⟨b, hFle⟩⟩,
      fun i ↦ CochainComplex.IsTermwiseFiniteFree.out (E := F) i⟩
  exact ⟨F', hFle, β, hβ⟩

/-- Helper for Lemma 15.65.5: the source-faithful descending finite-free construction naturally
produces a bare bounded-above termwise finite-free complex before it is repackaged in
`MinusWithTermsIn FiniteFreeClass`. -/
private theorem exists_strictlyLE_termwiseFiniteFree_quasiIso_of_free_target
    {Q : Cpx} {b : ℤ}
    (hQle : Q.IsStrictlyLE b)
    (hQfree : ∀ i : ℤ, Module.Free R (Q.X i))
    (hQall : ∀ m : ℤ, Q.IsMPseudoCoherent m) :
    ∃ F : Cpx,
      F.IsStrictlyLE b ∧
        F.IsTermwiseFiniteFree ∧
          ∃ β : F ⟶ Q, QuasiIso β := by
  -- TODO: follow the source-faithful descending attachment argument on the cone of a partial
  -- comparison `F ⟶ Q`, using the transferred pseudo-coherence data `hQall` and keeping the
  -- support bound `≤ b` fixed throughout.
  sorry

/-- Helper for Lemma 15.65.5: the remaining source-faithful descending construction upgrades a
bounded-above free target carrying all fixed-degree pseudo-coherence witnesses to a bounded-above
finite-free source with the same upper bound. -/
private theorem exists_boundedAbove_termwiseFiniteFree_quasiIso_of_free_target
    {Q : Cpx} {b : ℤ}
    (hQle : Q.IsStrictlyLE b)
    (hQfree : ∀ i : ℤ, Module.Free R (Q.X i))
    (hQall : ∀ m : ℤ, Q.IsMPseudoCoherent m) :
    ∃ F : CochainComplex.MinusWithTermsIn FiniteFreeClass,
      (F : Cpx).IsStrictlyLE b ∧
        ∃ β : (F : Cpx) ⟶ Q, QuasiIso β := by
  -- Route correction: separate the actual descending construction from the final owner packaging,
  -- so the remaining blocker is exactly the bare finite-free approximation.
  obtain ⟨F, hFle, hFfree, β, hβ⟩ :=
    exists_strictlyLE_termwiseFiniteFree_quasiIso_of_free_target
      (R := R) hQle hQfree hQall
  letI : F.IsTermwiseFiniteFree := hFfree
  exact
    exists_minusWithTermsIn_termwiseFiniteFree_quasiIso_of_strictlyLE
      (R := R) hFle β hβ

/-- Helper for Lemma 15.65.5: once the finite-generation upgrade is available for a bounded-above
free target, forgetting the free structure termwise gives the corresponding bounded-above finite
projective model with the same upper bound. -/
private theorem exists_boundedAbove_termwiseFiniteProjective_quasiIso_of_free_target
    {Q : Cpx} {b : ℤ}
    (hQle : Q.IsStrictlyLE b)
    (hQfree : ∀ i : ℤ, Module.Free R (Q.X i))
    (hQall : ∀ m : ℤ, Q.IsMPseudoCoherent m) :
    ∃ P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass,
      (P : Cpx).IsStrictlyLE b ∧
        ∃ β : (P : Cpx) ⟶ Q, QuasiIso β := by
  obtain ⟨F, hFle, β, hβ⟩ :=
    exists_boundedAbove_termwiseFiniteFree_quasiIso_of_free_target
      (R := R) hQle hQfree hQall
  let P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass :=
    ⟨(F : CochainComplex.MinusWithTermsIn FiniteFreeClass), fun i ↦ by
      -- Proof comment: forget the free structure and retain finite generation plus projectivity.
      rcases F.term_mem i with ⟨hfree, hfinite⟩
      exact ⟨hfinite, by
        letI : Module.Free R ((F : Cpx).X i) := hfree
        infer_instance⟩⟩
  exact ⟨P, hFle, β, hβ⟩

/-- Helper for Lemma 15.65.5: if a canonical stabilization middle complex
`P ⊞ mappingCocone (𝟙 C)` is already known to be bounded above by `b` and termwise finite free,
then the projection back to `P` is the required quasi-isomorphism. -/
private theorem finite_projective_stabilization_of_termwiseFiniteFree_middle
    {P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass} {b : ℤ} {C : Cpx}
    (hMiddleLe :
      (((P : Cpx) ⊞ CochainComplex.mappingCocone (𝟙 C)) : Cpx).IsStrictlyLE b)
    [(((P : Cpx) ⊞ CochainComplex.mappingCocone (𝟙 C)) : Cpx).IsTermwiseFiniteFree] :
    ∃ F : CochainComplex.MinusWithTermsIn FiniteFreeClass,
      (F : Cpx).IsStrictlyLE b ∧
        ∃ β : (F : Cpx) ⟶ (P : Cpx), QuasiIso β := by
  have hβ :
      QuasiIso
        (biprod.fst :
          ((P : Cpx) ⊞ CochainComplex.mappingCocone (𝟙 C)) ⟶ (P : Cpx)) := by
    -- Proof comment: the middle complex is canonically homotopy equivalent to `P`, hence the
    -- projection is a quasi-isomorphism.
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let e := CochainComplex.splitEpiFactorizationProjectionHomotopyEquiv (P : Cpx) C
    change IsIso ((e.toHomologyIso i).hom)
    infer_instance
  exact
    exists_minusWithTermsIn_termwiseFiniteFree_quasiIso_of_strictlyLE
      (R := R) hMiddleLe biprod.fst hβ

/-- Helper for Lemma 15.65.5: the only genuinely recursive input in the stabilization route is
the construction of a bounded-above complex `C` whose canonical middle complex
`P ⊞ mappingCocone (𝟙 C)` is already bounded above by the same cutoff and termwise finite free. -/
private theorem exists_stabilizing_termwiseFiniteFree_middle
    {P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass} {b : ℤ}
    (hP : (P : Cpx).IsStrictlyLE b) :
    ∃ C : Cpx,
      (((P : Cpx) ⊞ CochainComplex.mappingCocone (𝟙 C)) : Cpx).IsStrictlyLE b ∧
        (((P : Cpx) ⊞ CochainComplex.mappingCocone (𝟙 C)) : Cpx).IsTermwiseFiniteFree := by
  -- TODO: choose the recursive split finite-free covers of `P.X i ⊞ C.X (i + 1)` from the source
  -- proof and show that the canonical middle complex is supported in degrees `≤ b` with every
  -- term finite free.
  sorry

/-- Helper for Lemma 15.65.5: the remaining stabilization step replaces a bounded-above
finite-projective complex by a bounded-above finite-free complex with the same upper bound and a
quasi-isomorphism back to the original complex. -/
private theorem finite_projective_stabilization_same_bound
    {P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass} {b : ℤ}
    (hP : (P : Cpx).IsStrictlyLE b) :
    ∃ F : CochainComplex.MinusWithTermsIn FiniteFreeClass,
      (F : Cpx).IsStrictlyLE b ∧
        ∃ β : (F : Cpx) ⟶ (P : Cpx), QuasiIso β := by
  -- Route correction: separate the recursive choice of the stabilizing auxiliary complex `C` from
  -- the canonical `biprod.fst` quasi-isomorphism on `P ⊞ mappingCocone (𝟙 C)`.
  obtain ⟨C, hMiddleLe, hMiddleFree⟩ :=
    exists_stabilizing_termwiseFiniteFree_middle (R := R) (P := P) hP
  letI :
      (((P : Cpx) ⊞ CochainComplex.mappingCocone (𝟙 C)) : Cpx).IsTermwiseFiniteFree :=
    hMiddleFree
  exact
    finite_projective_stabilization_of_termwiseFiniteFree_middle
      (R := R) (P := P) (b := b) (C := C) hMiddleLe

/- Domain-style sampling for Lemma 15.65.5:
- primary domain: pseudo-coherence of cochain complexes via bounded-above finite-free and finite-
  projective models;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `CochainComplex.MinusWithTermsIn`;
- best owner abstraction: the pseudo-coherence owners stay `K.IsMPseudoCoherent` and
  `K.IsPseudoCoherent`, while bounded-above model data should be carried by the existing owner
  `CochainComplex.MinusWithTermsIn` specialized to the finite-projective or finite-free term
  class, rather than by a parallel local wrapper that repeats boundedness and termwise membership;
- primitive vs. derived:
  primitive data are a bounded-above owner complex in `MinusWithTermsIn ...` and a quasi-
  isomorphism to the target complex;
  derived API is the TFAE and the bounded-above finite-free existence statement below;
- source/core/bridge triage:
  `source-facing`: the TFAE and the finite-free existence theorem;
  `core/canonical`: `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, and `MinusWithTermsIn`;
  `bridge/view`: the existential model clauses relating a cochain complex to a chosen owner
    complex in `MinusWithTermsIn`.
-/

-- Proof sketch: `(1) → (3)` is immediate because finite free modules are finite projective. For
-- `(3) → (1)`, replace each finite projective term by a finite free module using a direct-summand
-- argument to obtain a bounded-above finite-free complex that is still quasi-isomorphic to `K`.
-- Then `(1) → (2)` comes from stupid truncations of a bounded-above finite-free model, while
-- `(2) → (3)` is built by the descending-induction argument of the Stacks proof, using Lemmas
-- `15.65.2` and `15.65.3` to keep control of pseudo-coherence and finiteness at each step.
/-- Lemma 15.65.5: for a cochain complex `K^•` of `R`-modules, the following are equivalent:
`K^•` is pseudo-coherent, `K^•` is `m`-pseudo-coherent for every `m : ℤ`, and `K^•` is
quasi-isomorphic to a bounded-above cochain complex of finite projective `R`-modules. -/
@[stacks 064U]
theorem cochainComplex_pseudoCoherent_tfae
    (K : Cpx) :
    [K.IsPseudoCoherent,
      ∀ m : ℤ, K.IsMPseudoCoherent m,
      ∃ P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass,
        ∃ α : (P : Cpx) ⟶ K, QuasiIso α].TFAE := by
  -- Proof comment: the source proof has three legs. This pass closes the two implications that
  -- only need previously established owner bridges, leaving the finite-projective-to-finite-free
  -- stabilization as the remaining source-faithful blocker.
  tfae_have 1 → 3 := by
    intro hK
    -- Replace the derived bounded-above finite-free witness by an actual quasi-isomorphic
    -- bounded-above finite-projective complex.
    exact exists_termwiseFiniteProjective_quasiIso_of_isPseudoCoherent (R := R) hK
  tfae_have 1 → 2 := by
    intro hK m
    -- Proof comment: reuse the packaged `(1) → (2)` bridge rather than rebuilding the bounded
    -- finite-free witness inside the `tfae` block.
    exact forall_isMPseudoCoherent_of_isPseudoCoherent (R := R) hK m
  tfae_have 2 → 3 := by
    intro hK
    obtain ⟨b, hb⟩ :=
      exists_homology_vanishing_bound_of_isZeroPseudoCoherent (R := R) (hK 0)
    obtain ⟨Q, hQle, hQfree, α, hα⟩ :=
      exists_boundedAbove_termwiseFree_quasiIso_of_homology_vanishing
        (R := R) (K := K) (b := b) hb
    have hQ : ∀ m : ℤ, Q.IsMPseudoCoherent m :=
      forall_isMPseudoCoherent_of_quasiIso_target (R := R) α hα hK
    obtain ⟨P, -, β, hβ⟩ :=
      exists_boundedAbove_termwiseFiniteProjective_quasiIso_of_free_target
        (R := R) hQle hQfree hQ
    letI : QuasiIso β := hβ
    letI : QuasiIso α := hα
    -- Proof comment: compose the refined bounded-above finite-projective model of the free target
    -- `Q` with the fixed quasi-isomorphism `Q ⟶ K`.
    exact ⟨P, β ≫ α, by infer_instance⟩
  tfae_have 3 → 1 := by
    intro hK
    rcases hK with ⟨P, α, hα⟩
    obtain ⟨b, hPle⟩ :=
      CochainComplex.MinusWithTermsIn.exists_isStrictlyLE
        (P := FiniteProjectiveClass) P
    obtain ⟨F, -, β, hβ⟩ :=
      finite_projective_stabilization_same_bound (R := R) (P := P) hPle
    letI : QuasiIso β := hβ
    letI : QuasiIso α := hα
    -- Proof comment: after stabilizing the bounded-above finite-projective model to a bounded-
    -- above finite-free one, pseudo-coherence is exactly the already-packaged finite-free witness.
    exact
      isPseudoCoherent_of_boundedAbove_termwiseFiniteFree_quasiIso
        (R := R) (β ≫ α) (by infer_instance)
  tfae_finish

-- Proof sketch: start from a bounded-above finite-free model of `K` given by pseudo-coherence and
-- descend from degree `b + 1`, extending the partial finite-free approximation one step at a time.
-- The cone of the partial map stays `(n - 1)`-pseudo-coherent by Lemma `15.65.2`, Lemma `15.65.3`
-- makes the relevant cohomology finite, and adjoining finitely many free generators yields the
-- next stage while keeping the complex zero above degree `b`.
/-- A pseudo-coherent cochain complex with vanishing cohomology above `b` admits a
quasi-isomorphic bounded-above termwise finite-free model concentrated in degrees `≤ b`. -/
theorem exists_boundedAbove_termwiseFiniteFree_quasiIso
    {K : Cpx} {b : ℤ}
    (hK : K.IsPseudoCoherent)
    (hvanish : ∀ i : ℤ, b < i → IsZero (K.homology i)) :
    ∃ F : CochainComplex.MinusWithTermsIn FiniteFreeClass,
      (F : Cpx).IsStrictlyLE b ∧
        ∃ α : (F : Cpx) ⟶ K, QuasiIso α := by
  obtain ⟨Q, hQle, hQfree, α, hα⟩ :=
    exists_boundedAbove_termwiseFree_quasiIso_of_homology_vanishing
      (R := R) (K := K) (b := b) hvanish
  have hKall : ∀ m : ℤ, K.IsMPseudoCoherent m :=
    forall_isMPseudoCoherent_of_isPseudoCoherent (R := R) hK
  have hQall : ∀ m : ℤ, Q.IsMPseudoCoherent m :=
    forall_isMPseudoCoherent_of_quasiIso_target (R := R) α hα hKall
  obtain ⟨F, hFle, β, hβ⟩ :=
    exists_boundedAbove_termwiseFiniteFree_quasiIso_of_free_target
      (R := R) hQle hQfree hQall
  letI : QuasiIso β := hβ
  letI : QuasiIso α := hα
  -- Proof comment: the frozen free target `Q` already carries the sharp support bound `≤ b`, so
  -- the refined finite-free source keeps that same bound after composition with `Q ⟶ K`.
  exact ⟨F, hFle, β ≫ α, by infer_instance⟩

end
end
