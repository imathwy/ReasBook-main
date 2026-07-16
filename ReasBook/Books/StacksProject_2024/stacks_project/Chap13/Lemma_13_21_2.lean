import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_21_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

/-
Domain-style sampling:
- primary domain: Cartan-Eilenberg resolutions of bounded-below cochain complexes in an abelian
  category with enough injectives;
- sampled owner declarations:
  `CartanEilenbergResolution`,
  `CochainComplex.InjectiveResolution`,
  `CategoryTheory.ShortComplex`,
  `CategoryTheory.InjectiveResolution`;
- best owner abstraction: the source-facing owner for the present lemma is
  `CartanEilenbergResolution`, while the columnwise and successive short-exact-sequence inputs used
  to build it are already canonically owned by `CochainComplex.InjectiveResolution`,
  `CategoryTheory.ShortComplex`, and `CategoryTheory.InjectiveResolution`;
- primitive data here: only the bounded-below source complex `K`;
- derived API here: the genuine existence statement that `K` admits a Cartan-Eilenberg
  resolution.

Source/core/bridge triage:
- `source-facing`: the existence statement below;
- `core/canonical`: the existing injective-resolution owners from Chapter 13 and mathlib;
- `bridge/view`: none in this file, since the target statement is already directly about the
  source-facing owner `CartanEilenbergResolution`.
-/

-- Proof sketch: choose a lower bound for `K`, then for each short exact sequence
-- `0 ⟶ Z^p ⟶ K^p ⟶ B^{p + 1} ⟶ 0` and `0 ⟶ B^{p + 1} ⟶ Z^{p + 1} ⟶ H^{p + 1}(K^•) ⟶ 0`
-- use the canonical owner `CochainComplex.InjectiveResolution` from Lemma 13.18.3 together with
-- the short-complex comparison data supplied directly by Lemma 13.18.9 to fit consecutive choices
-- into short exact sequences of complexes. Iterating this construction produces the
-- double complex and augmentation data required by the source-facing owner
-- `CartanEilenbergResolution`.
/-- Helper for Lemma 13.21.2: extract a concrete lower bound from the bounded-below hypothesis on
`K`. -/
lemma exists_strictlyGE_bound (K : CochainComplex.Plus 𝒜) :
    ∃ n : ℤ, K.obj.IsStrictlyGE n := by
  -- Unpack the canonical bounded-below owner into the source-proof lower cutoff `n`.
  exact (CochainComplex.plus_iff 𝒜 K.obj).1 K.property

/-- Helper for Lemma 13.21.2: in the cochain shape on `ℤ`, the predecessor of `p` is `p - 1`. -/
private theorem up_prev_eq (p : ℤ) :
    (ComplexShape.up ℤ).prev p = p - 1 := by
  -- Rewrite the predecessor through the defining relation `i + 1 = p`.
  apply ComplexShape.prev_eq'
  simpa [ComplexShape.up, ComplexShape.up'] using (show (p - 1 : ℤ) + 1 = p by omega)

/-- Helper for Lemma 13.21.2: in the cochain shape on `ℤ`, the successor of `p` is `p + 1`. -/
private theorem up_next_eq (p : ℤ) :
    (ComplexShape.up ℤ).next p = p + 1 := by
  -- Rewrite the successor through the defining relation `p + 1 = i`.
  apply ComplexShape.next_eq'
  simpa [ComplexShape.up, ComplexShape.up'] using (show (p : ℤ) + 1 = p + 1 by omega)

/-- Helper for Lemma 13.21.2: the cycles inclusion lands in the image factor of the outgoing
differential with zero composite. -/
private theorem cycles_term_image_comp_zero
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    K.obj.iCycles p ≫ factorThruImage (K.obj.d p (p + 1)) = 0 := by
  -- Cancel the mono image inclusion and rewrite the composite back to `d ∘ iCycles = 0`.
  apply (cancel_mono (image.ι (K.obj.d p (p + 1)))).1
  simp [Category.assoc]

/-- Helper for Lemma 13.21.2: the canonical cycles-to-image row at degree `p`. -/
private noncomputable def cycles_term_image_shortComplex
    (K : CochainComplex.Plus 𝒜) (p : ℤ) : ShortComplex 𝒜 :=
  ShortComplex.mk (K.obj.iCycles p) (factorThruImage (K.obj.d p (p + 1)))
    (cycles_term_image_comp_zero (𝒜 := 𝒜) K p)

/-- Helper for Lemma 13.21.2: the canonical row
`0 ⟶ Z^p ⟶ K^p ⟶ B^{p+1} ⟶ 0` is short exact. -/
private theorem obj_shortExact_cycles_term_image
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    (cycles_term_image_shortComplex (𝒜 := 𝒜) K p).ShortExact := by
  let hprev : (ComplexShape.up ℤ).prev p = p - 1 := up_prev_eq p
  let hnext : (ComplexShape.up ℤ).next p = p + 1 := up_next_eq p
  let S : ShortComplex 𝒜 := K.obj.sc' (p - 1) p (p + 1)
  let T : ShortComplex 𝒜 :=
    ShortComplex.mk (kernel.ι (factorThruImageSubobject S.g))
      (factorThruImageSubobject S.g) (kernel.condition _)
  have hT : T.ShortExact := by
    -- This is the standard kernel-image short exact sequence for the outgoing differential.
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  let i₁ : T.X₁ ≅ (cycles_term_image_shortComplex (𝒜 := 𝒜) K p).X₁ :=
    (kernelCompMono (factorThruImageSubobject S.g) (imageSubobject S.g).arrow) ≪≫
      S.cyclesIsoKernel.symm ≪≫ (K.obj.cyclesIsoSc' (p - 1) p (p + 1) hprev hnext).symm
  let i₂ : T.X₂ ≅ (cycles_term_image_shortComplex (𝒜 := 𝒜) K p).X₂ := Iso.refl _
  let i₃ : T.X₃ ≅ (cycles_term_image_shortComplex (𝒜 := 𝒜) K p).X₃ :=
    imageSubobjectIso S.g
  let e : T ≅ cycles_term_image_shortComplex (𝒜 := 𝒜) K p :=
    ShortComplex.isoMk i₁ i₂ i₃
      (by
        -- Transport the kernel inclusion to the standard cycles inclusion.
        simp [T, S, i₁, i₂, cycles_term_image_shortComplex, Category.assoc,
          K.obj.cyclesIsoSc'_inv_iCycles (p - 1) p (p + 1) hprev hnext])
      (by
        -- Transport the image-factor map from the subobject image to the categorical image.
        apply (cancel_mono (image.ι S.g)).1
        simp [T, S, i₂, i₃, cycles_term_image_shortComplex, Category.assoc])
  -- Transfer short exactness along the explicit isomorphism of rows.
  exact ShortComplex.shortExact_of_iso e hT

/-- Helper for Lemma 13.21.2: mapping the cycles-term-image row by the degree-zero single functor
preserves short exactness. -/
private theorem single_obj_shortExact_cycles_term_image
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    ((cycles_term_image_shortComplex (𝒜 := 𝒜) K p).map
      (CochainComplex.singleFunctor 𝒜 (0 : ℤ))).ShortExact := by
  -- Exact functors preserve the already established short exact row.
  exact
    @ShortComplex.ShortExact.map_of_exact
      𝒜 (CochainComplex 𝒜 ℤ) _ _
      (Preadditive.preadditiveHasZeroMorphisms)
      (Preadditive.preadditiveHasZeroMorphisms)
      (cycles_term_image_shortComplex (𝒜 := 𝒜) K p)
      (obj_shortExact_cycles_term_image (𝒜 := 𝒜) K p)
      (CochainComplex.singleFunctor 𝒜 (0 : ℤ))
      inferInstance inferInstance inferInstance

/-- Helper for Lemma 13.21.2: an injective resolution of an object packages as a strictly
nonnegative injective resolution of its degree-zero single complex. -/
private noncomputable def single_zero_resolution_bridge
    (X : 𝒜) (I : CategoryTheory.InjectiveResolution X) :
    CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor 𝒜 (0 : ℤ)).obj X) where
  complex :=
    ⟨⟨I.cochainComplex,
        (CochainComplex.plus_iff 𝒜 I.cochainComplex).2 ⟨0, inferInstance⟩⟩,
      fun n ↦ inferInstance⟩
  ι := I.ι'
  quasiIso := inferInstance

/-- Helper for Lemma 13.21.2: restricting a strictly nonnegative `ℤ`-indexed cochain complex to
`ℕ` and extending it back along `embeddingUpNat` recovers the original complex. -/
private noncomputable theorem strictlyGE_zero_restriction_extend_iso
    (L : CochainComplex 𝒜 ℤ) (hL : L.IsStrictlyGE 0) :
    ((L.restriction ComplexShape.embeddingUpNat).extend ComplexShape.embeddingUpNat) ≅ L := by
  -- Proof comment: in nonnegative degrees the comparison is the composite of the canonical
  -- `extendXIso` and `restrictionXIso`; in negative degrees both source and target terms are zero.
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro i
    by_cases hi : 0 ≤ i
    · exact
        (L.restriction ComplexShape.embeddingUpNat).extendXIso
          ComplexShape.embeddingUpNat (Int.toNat_of_nonneg hi) ≪≫
          (L.restrictionXIso ComplexShape.embeddingUpNat
            (i := Int.toNat i) (i' := i) (Int.toNat_of_nonneg hi))
    · let hsource :
        IsZero (((L.restriction ComplexShape.embeddingUpNat).extend
          ComplexShape.embeddingUpNat).X i) :=
        (L.restriction ComplexShape.embeddingUpNat).isZero_extend_X
          ComplexShape.embeddingUpNat i (by
            intro n hni
            exact hi (hni ▸ Int.natCast_nonneg n))
      let htarget : IsZero (L.X i) :=
        L.isZero_of_isStrictlyGE 0 i (lt_of_not_ge hi)
      exact hsource.iso htarget
  · intro i j hij
    by_cases hi : 0 ≤ i
    · have hij' : j = i + 1 := by
        simpa [ComplexShape.up, ComplexShape.up'] using hij
      have hj : 0 ≤ j := by
        omega
      -- Proof comment: after rewriting the extended and restricted differentials on the
      -- nonnegative branch, both sides reduce to the original differential of `L`.
      rw [HomologicalComplex.extend_d_eq
        (K := L.restriction ComplexShape.embeddingUpNat)
        (e := ComplexShape.embeddingUpNat)
        (by simpa [Int.toNat_of_nonneg hi] using
          (show (ComplexShape.embeddingUpNat.f (Int.toNat i) : ℤ) = i by simp [hi]))
        (by simpa [Int.toNat_of_nonneg hj] using
          (show (ComplexShape.embeddingUpNat.f (Int.toNat j) : ℤ) = j by simp [hj]))]
      rw [HomologicalComplex.restriction_d_eq
        (K := L) (e := ComplexShape.embeddingUpNat)
        (by simpa [Int.toNat_of_nonneg hi] using
          (show (ComplexShape.embeddingUpNat.f (Int.toNat i) : ℤ) = i by simp [hi]))
        (by simpa [Int.toNat_of_nonneg hj] using
          (show (ComplexShape.embeddingUpNat.f (Int.toNat j) : ℤ) = j by simp [hj]))]
      simp [Category.assoc]
    · let hsource :
        IsZero (((L.restriction ComplexShape.embeddingUpNat).extend
          ComplexShape.embeddingUpNat).X i) :=
        (L.restriction ComplexShape.embeddingUpNat).isZero_extend_X
          ComplexShape.embeddingUpNat i (by
            intro n hni
            exact hi (hni ▸ Int.natCast_nonneg n))
      -- Proof comment: once the source term is zero, both candidate composites agree
      -- automatically.
      exact hsource.eq_of_src _ _

/-- Helper for Lemma 13.21.2: restricting the augmentation of a strictly nonnegative injective
resolution of `single₀(X)` yields an augmentation of the underlying `ℕ`-indexed cocomplex. -/
private noncomputable theorem single_zero_object_resolution_augmentation
    {X : 𝒜}
    (J : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor 𝒜 (0 : ℤ)).obj X)) :
    (CochainComplex.single₀ 𝒜).obj X ⟶
      ((J : CochainComplex 𝒜 ℤ).restriction ComplexShape.embeddingUpNat) := by
  -- Proof comment: restriction along `embeddingUpNat` turns the source `ℤ`-indexed single complex
  -- back into the standard `single₀` complex on `ℕ`.
  simpa using HomologicalComplex.restrictionMap J.ι ComplexShape.embeddingUpNat

/-- Helper for Lemma 13.21.2: the restricted augmentation of a strictly nonnegative injective
resolution of `single₀(X)` is still a quasi-isomorphism. -/
private theorem single_zero_object_resolution_augmentation_quasiIso
    {X : 𝒜}
    (J : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor 𝒜 (0 : ℤ)).obj X)) :
    QuasiIso (single_zero_object_resolution_augmentation (𝒜 := 𝒜) J) := by
  -- Proof comment: restriction preserves the single-complex quasi-isomorphism from `J.ι`.
  simpa [single_zero_object_resolution_augmentation] using
    (inferInstance :
      QuasiIso (HomologicalComplex.restrictionMap J.ι ComplexShape.embeddingUpNat))

/-- Helper for Lemma 13.21.2: a strictly nonnegative injective resolution of `single₀(X)`
packages canonically as an objectwise injective resolution of `X`. -/
private noncomputable def single_zero_object_resolution_of_strictlyGE_zero
    {X : 𝒜}
    (J : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor 𝒜 (0 : ℤ)).obj X))
    (_hJ : (J : CochainComplex 𝒜 ℤ).IsStrictlyGE 0) :
    CategoryTheory.InjectiveResolution X :=
  { cocomplex := (J : CochainComplex 𝒜 ℤ).restriction ComplexShape.embeddingUpNat
    ι := single_zero_object_resolution_augmentation (𝒜 := 𝒜) J
    quasiIso := single_zero_object_resolution_augmentation_quasiIso (𝒜 := 𝒜) J }

/-- Helper for Lemma 13.21.2: after packaging a strictly nonnegative single-complex resolution as
an objectwise injective resolution, extending its cocomplex back to `ℤ` recovers the original
single-complex resolution. -/
private noncomputable theorem single_zero_object_resolution_cochainComplex_iso
    {X : 𝒜}
    (J : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor 𝒜 (0 : ℤ)).obj X))
    (hJ : (J : CochainComplex 𝒜 ℤ).IsStrictlyGE 0) :
    (single_zero_object_resolution_of_strictlyGE_zero (𝒜 := 𝒜) J hJ).cochainComplex ≅
      (J : CochainComplex 𝒜 ℤ) := by
  -- Proof comment: the packaged object resolution has cocomplex `J.restriction`, so its
  -- cochain complex is exactly the extension recovered by the strictlyGE-zero comparison above.
  simpa [single_zero_object_resolution_of_strictlyGE_zero,
    CategoryTheory.InjectiveResolution.cochainComplex] using
    strictlyGE_zero_restriction_extend_iso (𝒜 := 𝒜) (L := (J : CochainComplex 𝒜 ℤ)) hJ

/-- Helper for Lemma 13.21.2: composing on the left with an epimorphism does not change the
image subobject. -/
private theorem imageSubobject_comp_eq_of_epi_left
    {X Y Z : 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] :
    imageSubobject (f ≫ g) = imageSubobject g := by
  let h := imageSubobject_comp_le f g
  let φ := Subobject.ofLE _ _ h
  haveI : Epi φ := by
    -- Proof comment: the universal map between the two image subobjects is epi because the left
    -- factor already surjects onto the same image.
    dsimp [φ, h]
    infer_instance
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  -- Proof comment: an isomorphism of subobjects upgrades the comparison inequality to equality.
  exact Subobject.eq_of_comm (asIso φ) (by simp [φ])

/-- Helper for Lemma 13.21.2: for any short complex, the canonical boundary-to-cycles map lands
in homology with zero composite. This is the source-proof second row before transporting from the
ambient short complex to the cochain-complex objects `image`, `cycles`, and `homology`. -/
private theorem image_to_cycles_to_homology_comp_zero
    (S : ShortComplex 𝒜) :
    imageToKernel S.f S.g S.zero ≫ S.cyclesIsoKernel.symm.hom ≫ S.homologyπ = 0 := by
  -- Proof comment: compare after precomposing with the image factorization of `S.f`; this turns
  -- the image-to-kernel map back into the usual lift to the kernel subobject.
  apply (cancel_epi (factorThruImageSubobject S.f)).1
  have htoCycles :
      factorThruKernelSubobject S.g S.f S.zero ≫ S.cyclesIsoKernel.symm.hom = S.toCycles := by
    -- Proof comment: both maps become the original `S.f` after composing with the cycles
    -- inclusion, so the mono `iCycles` identifies them.
    apply (cancel_mono S.iCycles).1
    simp [Category.assoc, ShortComplex.toCycles_i]
  calc
    factorThruImageSubobject S.f ≫ imageToKernel S.f S.g S.zero ≫
        S.cyclesIsoKernel.symm.hom ≫ S.homologyπ
      =
        factorThruKernelSubobject S.g S.f S.zero ≫
          S.cyclesIsoKernel.symm.hom ≫ S.homologyπ := by
            rw [Category.assoc, Category.assoc,
              factorThruImageSubobject_comp_imageToKernel]
    _ = S.toCycles ≫ S.homologyπ := by rw [htoCycles]
    _ = 0 := ShortComplex.toCycles_comp_homologyπ (S := S)

/-- Helper for Lemma 13.21.2: the source-proof second row
`image(S.f) ⟶ cycles(S) ⟶ homology(S)` attached to a short complex. -/
private noncomputable def image_to_cycles_to_homology_shortComplex
    (S : ShortComplex 𝒜) : ShortComplex 𝒜 :=
  ShortComplex.mk
    (imageToKernel S.f S.g S.zero ≫ S.cyclesIsoKernel.symm.hom)
    S.homologyπ
    (image_to_cycles_to_homology_comp_zero (𝒜 := 𝒜) S)

/-- Helper for Lemma 13.21.2: for any short complex, the canonical row
`0 ⟶ image(S.f) ⟶ cycles(S) ⟶ homology(S) ⟶ 0` is short exact. -/
private theorem image_to_cycles_to_homology_shortExact
    (S : ShortComplex 𝒜) :
    (image_to_cycles_to_homology_shortComplex (𝒜 := 𝒜) S).ShortExact := by
  let T : ShortComplex 𝒜 := image_to_cycles_to_homology_shortComplex (𝒜 := 𝒜) S
  let U : ShortComplex 𝒜 :=
    ShortComplex.mk S.toCycles S.homologyπ (ShortComplex.toCycles_comp_homologyπ (S := S))
  have hfactor :
      factorThruImageSubobject S.f ≫ T.f = S.toCycles := by
    -- Proof comment: after factoring through the image of `S.f`, the canonical image-to-cycles
    -- map is exactly the standard boundary inclusion into cycles.
    apply (cancel_mono S.iCycles).1
    calc
      factorThruImageSubobject S.f ≫ T.f ≫ S.iCycles
          = factorThruImageSubobject S.f ≫ imageToKernel S.f S.g S.zero ≫
              S.cyclesIsoKernel.symm.hom ≫ S.iCycles := by
                simp [T, image_to_cycles_to_homology_shortComplex, Category.assoc]
      _ = factorThruKernelSubobject S.g S.f S.zero ≫
            S.cyclesIsoKernel.symm.hom ≫ S.iCycles := by
              rw [Category.assoc, factorThruImageSubobject_comp_imageToKernel]
      _ = S.toCycles ≫ S.iCycles := by
            simp [Category.assoc, ShortComplex.toCycles_i]
      _ = S.f := by rw [ShortComplex.toCycles_i]
  have himage :
      imageSubobject T.f = imageSubobject S.toCycles := by
    -- Proof comment: the source of `T.f` is already the image object of `S.f`, so composing on
    -- the left by the epi `factorThruImageSubobject S.f` does not change the image.
    symm
    simpa [hfactor] using
      imageSubobject_comp_eq_of_epi_left
        (factorThruImageSubobject S.f) T.f
  have hExactU : U.Exact := by
    -- Proof comment: `homologyπ` is the cokernel of `toCycles` by construction.
    simpa [U] using (ShortComplex.exact_cokernel S.toCycles)
  have hExactT : T.Exact := by
    -- Proof comment: rewrite the exact cokernel row for `toCycles` through the image equality
    -- above, keeping the same right map `homologyπ`.
    rw [ShortComplex.exact_iff_image_eq_kernel]
    calc
      imageSubobject T.f = imageSubobject S.toCycles := himage
      _ = kernelSubobject S.homologyπ := by
            simpa [U] using
              (ShortComplex.exact_iff_image_eq_kernel (S := U)).1 hExactU
      _ = kernelSubobject T.g := by simp [T, image_to_cycles_to_homology_shortComplex]
  have hleft :
      T.f ≫ S.iCycles = (imageSubobject S.f).arrow := by
    -- Proof comment: compare both candidate inclusions after precomposing with
    -- `factorThruImageSubobject S.f`; both recover the original map `S.f`.
    apply (cancel_epi (factorThruImageSubobject S.f)).1
    calc
      factorThruImageSubobject S.f ≫ T.f ≫ S.iCycles
          = S.toCycles ≫ S.iCycles := by rw [hfactor]
      _ = S.f := by rw [ShortComplex.toCycles_i]
      _ = factorThruImageSubobject S.f ≫ (imageSubobject S.f).arrow := by
            rw [imageSubobject_arrow_comp]
  haveI : Mono (T.f ≫ S.iCycles) := by
    simpa [hleft] using (inferInstance : Mono (imageSubobject S.f).arrow)
  have hMono : Mono T.f := by
    -- Proof comment: the cycles inclusion is mono, so monicity of the composite reflects back to
    -- the boundary inclusion.
    exact mono_of_mono_fac T.f S.iCycles
  -- Proof comment: combine the exactness of the middle term with the canonical mono/epi ends.
  exact ShortComplex.ShortExact.mk' hExactT hMono inferInstance

/-- Helper for Lemma 13.21.2: the canonical row
`0 ⟶ B^{p + 1} ⟶ Z^{p + 1} ⟶ H^{p + 1}(K^•)` extracted from
`K.obj.sc' p (p + 1) (p + 2)`. -/
private noncomputable def image_cycles_homology_shortComplex
    (K : CochainComplex.Plus 𝒜) (p : ℤ) : ShortComplex 𝒜 :=
  let S : ShortComplex 𝒜 := K.obj.sc' p (p + 1) (p + 2)
  let hprev : (ComplexShape.up ℤ).prev (p + 1) = p := by
    simpa [sub_eq_add_neg, add_assoc] using up_prev_eq (p + 1)
  let hnext : (ComplexShape.up ℤ).next (p + 1) = p + 2 := by
    simpa [add_assoc] using up_next_eq (p + 1)
  let T : ShortComplex 𝒜 := image_to_cycles_to_homology_shortComplex (𝒜 := 𝒜) S
  let i₂ : T.X₂ ≅ K.obj.cycles (p + 1) :=
    S.cyclesIsoKernel.symm ≪≫ (K.obj.cyclesIsoSc' p (p + 1) (p + 2) hprev hnext).symm
  let i₃ : T.X₃ ≅ K.obj.homology (p + 1) :=
    (K.obj.homologyIsoSc' p (p + 1) (p + 2) hprev hnext).symm
  ShortComplex.mk
    ((imageSubobjectIso S.f).inv ≫ T.f ≫ i₂.hom)
    (i₂.inv ≫ T.g ≫ i₃.hom)
    (by
      -- Proof comment: cancel the image and cycles transport isomorphisms and use the vanishing
      -- already built into the ambient short-complex row `T`.
      apply (cancel_mono (imageSubobjectIso S.f).hom).1
      simp [Category.assoc, T, i₂, i₃, image_to_cycles_to_homology_shortComplex])

/-- Helper for Lemma 13.21.2: the canonical row
`0 ⟶ B^{p + 1} ⟶ Z^{p + 1} ⟶ H^{p + 1}(K^•) ⟶ 0` is short exact. -/
private theorem obj_shortExact_image_cycles_homology
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    (image_cycles_homology_shortComplex (𝒜 := 𝒜) K p).ShortExact := by
  let S : ShortComplex 𝒜 := K.obj.sc' p (p + 1) (p + 2)
  let hprev : (ComplexShape.up ℤ).prev (p + 1) = p := by
    simpa [sub_eq_add_neg, add_assoc] using up_prev_eq (p + 1)
  let hnext : (ComplexShape.up ℤ).next (p + 1) = p + 2 := by
    simpa [add_assoc] using up_next_eq (p + 1)
  let T : ShortComplex 𝒜 := image_to_cycles_to_homology_shortComplex (𝒜 := 𝒜) S
  let i₂ : T.X₂ ≅ K.obj.cycles (p + 1) :=
    S.cyclesIsoKernel.symm ≪≫ (K.obj.cyclesIsoSc' p (p + 1) (p + 2) hprev hnext).symm
  let i₃ : T.X₃ ≅ K.obj.homology (p + 1) :=
    (K.obj.homologyIsoSc' p (p + 1) (p + 2) hprev hnext).symm
  let e : T ≅ image_cycles_homology_shortComplex (𝒜 := 𝒜) K p :=
    ShortComplex.isoMk (imageSubobjectIso S.f) i₂ i₃
      (by
        -- Proof comment: the left map of the transported row is defined by conjugating `T.f`
        -- through the image and cycles identifications.
        simp [T, i₂, i₃, image_cycles_homology_shortComplex, Category.assoc])
      (by
        -- Proof comment: the right map is transported in the same way along the cycles and
        -- homology identifications.
        simp [T, i₂, i₃, image_cycles_homology_shortComplex, Category.assoc])
  -- Proof comment: the objectwise row is exactly the generic second row rewritten in the owners
  -- `image`, `cycles`, and `homology` of the ambient cochain complex.
  exact ShortComplex.shortExact_of_iso e
    (image_to_cycles_to_homology_shortExact (𝒜 := 𝒜) S)

/-- Helper for Lemma 13.21.2: mapping the image-cycles-homology row by the degree-zero single
functor preserves short exactness. -/
private theorem single_obj_shortExact_image_cycles_homology
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    ((image_cycles_homology_shortComplex (𝒜 := 𝒜) K p).map
      (CochainComplex.singleFunctor 𝒜 (0 : ℤ))).ShortExact := by
  -- Proof comment: exact additive functors preserve the short exact second row just established.
  exact
    @ShortComplex.ShortExact.map_of_exact
      𝒜 (CochainComplex 𝒜 ℤ) _ _
      (Preadditive.preadditiveHasZeroMorphisms)
      (Preadditive.preadditiveHasZeroMorphisms)
      (image_cycles_homology_shortComplex (𝒜 := 𝒜) K p)
      (obj_shortExact_image_cycles_homology (𝒜 := 𝒜) K p)
      (CochainComplex.singleFunctor 𝒜 (0 : ℤ))
      inferInstance inferInstance inferInstance

/-- Helper for Lemma 13.21.2: once a specific lower bound is fixed, the Cartan-Eilenberg
resolution should be built by the textbook staircase of short exact sequences on cycles, terms,
images, and homology, applying Lemma 13.18.9 alternately at each degree. -/
theorem exists_cartanEilenbergResolution_of_isStrictlyGE
    (K : CochainComplex.Plus 𝒜) {n : ℤ} (hK : K.obj.IsStrictlyGE n) :
    Nonempty (CartanEilenbergResolution K) := by
  -- Route correction: the strictGE-zero `restriction`/`extend` transport is now available, so the
  -- remaining blocker is no longer exactness but owner packaging: convert the single-complex
  -- outputs of Lemma 13.18.9 back to objectwise injective resolutions and recurse on the degree.
  -- TODO: follow the source proof literally.
  -- 1. For each `p ≥ n`, form the two short exact rows
  --    `0 ⟶ Z^p ⟶ K^p ⟶ B^{p + 1} ⟶ 0` and
  --    `0 ⟶ B^{p + 1} ⟶ Z^{p + 1} ⟶ H^{p + 1}(K) ⟶ 0`,
  --    viewed as short exact sequences of single cochain complexes.
  -- 2. Start with an injective resolution of `Z^n`, then use
  --    `CochainComplex.exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution_strictlyGE_zero`
  --    twice at each stage to propagate compatible resolutions of `K^p`, `B^{p+1}`, `Z^{p+1}`,
  --    and `H^{p+1}(K)`.
  --    Each strictlyGE-zero single-complex output should be converted back to an objectwise
  --    `CategoryTheory.InjectiveResolution` using the transport lemma above.
  -- 3. Assemble the horizontal differential
  --    `I^{p,•} ⟶ J_B^{p+1,•} ⟶ J_Z^{p+1,•} ⟶ I^{p+1,•}`,
  --    extend the resulting nat-indexed row along `ComplexShape.embeddingUpIntGE n`, and package
  --    the resulting double complex, augmentation, and column/cycles/image/homology isomorphisms.
  -- The missing pieces are the reverse adapter back to object resolutions, the staircase step
  -- bundle, and the nat-indexed staircase packaging.
  let _ := hK
  sorry

/-- Lemma 13.21.2: every bounded-below cochain complex in an abelian category with enough
injectives admits a Cartan-Eilenberg resolution. -/
theorem exists_cartanEilenbergResolution (K : CochainComplex.Plus 𝒜) :
    Nonempty (CartanEilenbergResolution K) := by
  -- First choose the lower cutoff appearing in the textbook proof.
  obtain ⟨n, hK⟩ := exists_strictlyGE_bound (𝒜 := 𝒜) K
  -- Then invoke the source-faithful staircase construction above that cutoff.
  exact exists_cartanEilenbergResolution_of_isStrictlyGE K hK

end
