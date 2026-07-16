import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

/-- Helper for Lemma 13.21.2: the degree-zero single functor, written in the owner form
`HomologicalComplex.single` so that finite-limit and finite-colimit preservation instances are
visible to typeclass search. -/
private noncomputable abbrev singleZeroFunctor : 𝒜 ⥤ CochainComplex 𝒜 ℤ :=
  HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) 0

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
private lemma exists_strictlyGE_bound (K : CochainComplex.Plus 𝒜) :
    ∃ n : ℤ, K.obj.IsStrictlyGE n := by
  -- Proof comment: unpack the bounded-below owner `CochainComplex.Plus`.
  simpa [CochainComplex.plus_iff] using K.property

/-- Helper for Lemma 13.21.2: in the cochain shape on `ℤ`, the predecessor of `p` is `p - 1`. -/
private theorem up_prev_eq (p : ℤ) :
    (ComplexShape.up ℤ).prev p = p - 1 := by
  -- Proof comment: this is the standard predecessor formula for cochain complexes on `ℤ`.
  simpa using (CochainComplex.prev ℤ p)

/-- Helper for Lemma 13.21.2: in the cochain shape on `ℤ`, the successor of `p` is `p + 1`. -/
private theorem up_next_eq (p : ℤ) :
    (ComplexShape.up ℤ).next p = p + 1 := by
  -- Proof comment: this is the standard successor formula for cochain complexes on `ℤ`.
  simpa using (CochainComplex.next ℤ p)

/-- Helper for Lemma 13.21.2: the cycles inclusion lands in the image factor of the outgoing
differential with zero composite. -/
private theorem cycles_term_image_comp_zero
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    K.obj.iCycles p ≫ factorThruImage (K.obj.d p (p + 1)) = 0 := by
  -- Proof comment: postcompose with the image inclusion and use the defining cycle equation.
  apply (cancel_mono (image.ι (K.obj.d p (p + 1)))).1
  simpa [Category.assoc, image.fac] using K.obj.iCycles_comp_d p (p + 1)

/-- Helper for Lemma 13.21.2: the canonical cycles-to-image row at degree `p`. -/
private noncomputable def cycles_term_image_shortComplex
    (K : CochainComplex.Plus 𝒜) (p : ℤ) : ShortComplex 𝒜 :=
  ShortComplex.mk (K.obj.iCycles p) (factorThruImage (K.obj.d p (p + 1)))
    (cycles_term_image_comp_zero (𝒜 := 𝒜) K p)

/-- Helper for Lemma 13.21.2: the canonical image factorization recovers the differential
`d^p`. -/
private theorem factorThruImage_comp_image_ι
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    factorThruImage (K.obj.d p (p + 1)) ≫ image.ι (K.obj.d p (p + 1)) = K.obj.d p (p + 1) :=
  by
  -- Proof comment: this is the universal factorization identity for the image of `d^p`.
  simpa using image.fac (K.obj.d p (p + 1))

/-- Helper for Lemma 13.21.2: the canonical row
`0 ⟶ Z^p ⟶ K^p ⟶ B^{p+1} ⟶ 0` is short exact. -/
private theorem obj_shortExact_cycles_term_image
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    (cycles_term_image_shortComplex (𝒜 := 𝒜) K p).ShortExact := by
  -- Proof comment: `Z^p` is the kernel of `d^p`, and the right map is the canonical image
  -- factorization of `d^p`.
  have hKernel :
      IsLimit
        (KernelFork.ofι
          (K.obj.iCycles p)
          (cycles_term_image_comp_zero (𝒜 := 𝒜) K p)) := by
    exact isKernelOfComp
      (image.ι (K.obj.d p (p + 1)))
      (K.obj.d p (p + 1))
      (K.obj.cyclesIsKernel p (p + 1) (by simp))
      (cycles_term_image_comp_zero (𝒜 := 𝒜) K p)
      (factorThruImage_comp_image_ι (𝒜 := 𝒜) K p)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · simpa [cycles_term_image_shortComplex] using
      ShortComplex.exact_of_f_is_kernel (cycles_term_image_shortComplex (𝒜 := 𝒜) K p) hKernel
  · simpa [cycles_term_image_shortComplex] using
      (mono_of_isLimit_fork hKernel)
  · simpa [cycles_term_image_shortComplex] using
      (inferInstance : Epi (factorThruImage (K.obj.d p (p + 1))))

/-- Helper for Lemma 13.21.2: mapping the cycles-term-image row by the degree-zero single functor
preserves short exactness. -/
private theorem single_obj_shortExact_cycles_term_image
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    ((cycles_term_image_shortComplex (𝒜 := 𝒜) K p).map
      (CochainComplex.singleFunctor 𝒜 (0 : ℤ))).ShortExact := by
  -- Proof comment: the degree-zero single functor preserves finite limits and colimits, so it
  -- carries short exact rows to short exact rows.
  change ((cycles_term_image_shortComplex (𝒜 := 𝒜) K p).map singleZeroFunctor).ShortExact
  exact (obj_shortExact_cycles_term_image (𝒜 := 𝒜) K p).map_of_exact
    singleZeroFunctor

/-- Helper for Lemma 13.21.2: an injective resolution of an object packages as a strictly
nonnegative injective resolution of its degree-zero single complex. -/
private noncomputable def single_zero_resolution_bridge
    (X : 𝒜) (I : CategoryTheory.InjectiveResolution X) :
    CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor 𝒜 (0 : ℤ)).obj X) where
  complex :=
    ⟨⟨I.cochainComplex,
        (CochainComplex.plus_iff 𝒜 I.cochainComplex).2 ⟨0, inferInstance⟩⟩,
      fun _ ↦ inferInstance⟩
  ι := I.ι'
  quasiIso := inferInstance

/-- Helper for Lemma 13.21.2: an injective resolution can be transported across an isomorphism of
source objects without changing the resolved cochain complex. -/
private noncomputable def injectiveResolutionOfIso
    {X Y : 𝒜} (e : X ≅ Y) (I : CategoryTheory.InjectiveResolution Y) :
    CategoryTheory.InjectiveResolution X where
  cocomplex := I.cocomplex
  -- Proof comment: precompose the chosen augmentation with the source isomorphism.
  ι := (CochainComplex.single₀ 𝒜).map e.hom ≫ I.ι

/-- Helper for Lemma 13.21.2: restricting the `ℤ`-indexed cochain complex attached to an
injective resolution along `embeddingUpNat` recovers the original `ℕ`-indexed cocomplex. -/
private noncomputable def injective_resolution_restriction_iso_cocomplex
    {X : 𝒜} (I : CategoryTheory.InjectiveResolution X) :
    I.cochainComplex.restriction ComplexShape.embeddingUpNat ≅ I.cocomplex := by
  -- Proof comment: restriction only remembers the nonnegative degrees of the extended cochain
  -- complex, so the comparison is componentwise `cochainComplexXIso`.
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro n
    exact
      I.cochainComplex.restrictionXIso ComplexShape.embeddingUpNat
        (i := n) (i' := Int.ofNat n) (by simp) ≪≫
        I.cochainComplexXIso (Int.ofNat n) n rfl
  · rintro n _ rfl
    -- Proof comment: the differentials agree after rewriting both sides through the standard
    -- formulas for restriction and extension.
    dsimp only
    rw [HomologicalComplex.restriction_d_eq (e := ComplexShape.embeddingUpNat)
      (K := I.cochainComplex) (i' := Int.ofNat n) (j' := Int.ofNat (n + 1))
      (by simp) (by simp)]
    rw [I.cochainComplex_d (Int.ofNat n) (Int.ofNat (n + 1)) n (n + 1) rfl rfl]
    simp

/-- Helper for Lemma 13.21.2: restricting the extension of an `ℕ`-indexed cochain complex along
`embeddingUpNat` recovers the original cochain complex. -/
private theorem restriction_extend_embeddingUpNat_iso
    (F : CochainComplex 𝒜 ℕ) :
    Nonempty (((F.extend ComplexShape.embeddingUpNat).restriction
      ComplexShape.embeddingUpNat) ≅ F) := by
  -- Proof comment: on each nonnegative degree, restriction reads off the same component of the
  -- extended complex, and `extendXIso` identifies that component with the original one.
  refine ⟨HomologicalComplex.Hom.isoOfComponents ?_ ?_⟩
  · intro n
    exact
      (F.extend ComplexShape.embeddingUpNat).restrictionXIso
        ComplexShape.embeddingUpNat rfl ≪≫
        F.extendXIso ComplexShape.embeddingUpNat rfl
  · intro n m hnm
    -- Proof comment: both differentials are the original differential `F.d n m` after the two
    -- standard comparison rewrites for restriction and extension.
    rw [HomologicalComplex.restriction_d_eq
      (K := F.extend ComplexShape.embeddingUpNat) (e := ComplexShape.embeddingUpNat)
      (i' := (n : ℤ)) (j' := (m : ℤ)) rfl rfl]
    rw [HomologicalComplex.extend_d_eq
      (K := F) (e := ComplexShape.embeddingUpNat)
      (i := n) (j := m) (i' := (n : ℤ)) (j' := (m : ℤ)) rfl rfl]
    simp [Category.assoc]

/-- Helper for Lemma 13.21.2: restricting the degree-zero `ℤ`-indexed single complex along
`embeddingUpNat` gives the standard `ℕ`-indexed degree-zero single complex. -/
private theorem restriction_single_zero_iso
    (X : 𝒜) :
    Nonempty
      ((((CochainComplex.singleFunctor 𝒜 (0 : ℤ)).obj X).restriction
        ComplexShape.embeddingUpNat) ≅
        (CochainComplex.single₀ 𝒜).obj X) := by
  -- Proof comment: first identify the `ℤ`-indexed single complex as the extension of the
  -- `ℕ`-indexed one, then restrict back using the previous comparison lemma.
  let S : CochainComplex 𝒜 ℕ := (CochainComplex.single₀ 𝒜).obj X
  let eSingle :
      S.extend ComplexShape.embeddingUpNat ≅
        (CochainComplex.singleFunctor 𝒜 (0 : ℤ)).obj X :=
    HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat X 0 (0 : ℤ) rfl
  obtain ⟨hrestrict⟩ := restriction_extend_embeddingUpNat_iso (𝒜 := 𝒜) S
  refine ⟨((ComplexShape.embeddingUpNat.restrictionFunctor 𝒜).mapIso eSingle.symm) ≪≫ hrestrict⟩

/-- Helper for Lemma 13.21.2: the image of `d^p` lands in the cycles of the next degree because
`d^{p + 1} ∘ d^p = 0`. -/
private theorem image_ι_comp_next_d_eq_zero
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    image.ι (K.obj.d p (p + 1)) ≫ K.obj.d (p + 1) (p + 2) = 0 := by
  -- Proof comment: cancel the epimorphic factor-through-image map and use `d ∘ d = 0`.
  apply (cancel_epi (factorThruImage (K.obj.d p (p + 1)))).1
  simpa [Category.assoc, image.fac] using K.obj.d_comp_d p (p + 1) (p + 2)

/-- Helper for Lemma 13.21.2: the textbook map `B^{p+1} ⟶ Z^{p+1}` written in the canonical
owner spelling `image ⟶ cycles`. -/
private noncomputable def imageToCycles
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    image (K.obj.d p (p + 1)) ⟶ K.obj.cycles (p + 1) :=
  K.obj.liftCycles (image.ι (K.obj.d p (p + 1))) (p + 2)
    (by
      have hnext := up_next_eq (p + 1)
      omega)
    (image_ι_comp_next_d_eq_zero (𝒜 := 𝒜) K p)

/-- Helper for Lemma 13.21.2: the owner-level `liftCycles` definition of `imageToCycles`
composes with the cycles inclusion to the usual image inclusion. -/
private theorem imageToCycles_comp_iCycles
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    imageToCycles (𝒜 := 𝒜) K p ≫ K.obj.iCycles (p + 1) =
      image.ι (K.obj.d p (p + 1)) := by
  -- Proof comment: this is the defining property of `liftCycles`.
  simpa [imageToCycles] using
    K.obj.liftCycles_i (image.ι (K.obj.d p (p + 1))) (p + 2)
      (by
        have hnext := up_next_eq (p + 1)
        omega)
      (image_ι_comp_next_d_eq_zero (𝒜 := 𝒜) K p)

/-- Helper for Lemma 13.21.2: precomposing `imageToCycles` with the canonical factor through the
image recovers the standard map `K^{p} ⟶ Z^{p+1}`. -/
private theorem factorThruImage_comp_imageToCycles
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    factorThruImage (K.obj.d p (p + 1)) ≫ imageToCycles (𝒜 := 𝒜) K p =
      K.obj.toCycles p (p + 1) := by
  -- Proof comment: both maps become `d^p` after composing with the cycles inclusion.
  apply (cancel_mono (K.obj.iCycles (p + 1))).1
  simpa [Category.assoc, imageToCycles_comp_iCycles, factorThruImage_comp_image_ι] using
    K.obj.toCycles_i (i := p) (j := p + 1)

/-- Helper for Lemma 13.21.2: the canonical image-to-cycles map kills homology classes because it
is induced by a boundary. -/
private theorem imageToCycles_comp_homologyπ
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    imageToCycles (𝒜 := 𝒜) K p ≫ K.obj.homologyπ (p + 1) = 0 := by
  -- Proof comment: after precomposing with the canonical epimorphism onto the image, this is the
  -- standard vanishing `toCycles ≫ homologyπ = 0`.
  apply (cancel_epi (factorThruImage (K.obj.d p (p + 1)))).1
  have hcomp :
      factorThruImage (K.obj.d p (p + 1)) ≫ imageToCycles (𝒜 := 𝒜) K p ≫
          K.obj.homologyπ (p + 1) =
        K.obj.toCycles p (p + 1) ≫ K.obj.homologyπ (p + 1) := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ t ≫ K.obj.homologyπ (p + 1))
        (factorThruImage_comp_imageToCycles (𝒜 := 𝒜) K p)
  calc
    factorThruImage (K.obj.d p (p + 1)) ≫ imageToCycles (𝒜 := 𝒜) K p ≫
        K.obj.homologyπ (p + 1) =
      K.obj.toCycles p (p + 1) ≫ K.obj.homologyπ (p + 1) := hcomp
    _ = 0 := K.obj.toCycles_comp_homologyπ (i := p) (j := p + 1)
    _ = factorThruImage (K.obj.d p (p + 1)) ≫ 0 := by simp

/-- Helper for Lemma 13.21.2: the textbook row
`0 ⟶ B^{p+1} ⟶ Z^{p+1} ⟶ H^{p+1}(K^•) ⟶ 0`
is short exact in the canonical owner spelling. -/
private theorem image_to_cycles_to_homology_shortExact
    (K : CochainComplex.Plus 𝒜) (p : ℤ) :
    (ShortComplex.mk
      (imageToCycles (𝒜 := 𝒜) K p)
      (K.obj.homologyπ (p + 1))
      (imageToCycles_comp_homologyπ (𝒜 := 𝒜) K p)).ShortExact := by
  -- Proof comment: `H^{p+1}` is the cokernel of `toCycles`, and `imageToCycles` is the same map
  -- after precomposing with the canonical epimorphism onto the image of `d^p`.
  refine ShortComplex.ShortExact.mk' ?_ ?_ inferInstance
  · exact ShortComplex.exact_of_g_is_cokernel _
      (isCokernelOfComp
        (factorThruImage (K.obj.d p (p + 1)))
        (K.obj.toCycles p (p + 1))
        (K.obj.homologyIsCokernel (i := p) (j := p + 1) (by simp))
        (imageToCycles_comp_homologyπ (𝒜 := 𝒜) K p)
        (factorThruImage_comp_imageToCycles (𝒜 := 𝒜) K p))
  · exact mono_of_mono_fac (imageToCycles_comp_iCycles (𝒜 := 𝒜) K p)

/-- Helper for Lemma 13.21.2: after restricting a degree-zero `ℤ`-indexed single-complex
injective resolution to `ℕ`, the target complex is exact in every positive degree. -/
private theorem singleZeroRestrictionExactAtSucc
    (X : 𝒜)
    (J : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor 𝒜 (0 : ℤ)).obj X))
    (q : ℕ) :
    ((J : CochainComplex 𝒜 ℤ).restriction ComplexShape.embeddingUpNat).ExactAt (q + 1) := sorry

/-- Helper for Lemma 13.21.2: a strict-`GE 0` injective resolution of the degree-zero
`ℤ`-indexed single complex already yields the exact degree-zero short complex needed for the
object-level augmentation package. -/
private theorem singleZeroDegreeZeroExactAndMono
    (X : 𝒜)
    (J : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor 𝒜 (0 : ℤ)).obj X))
    (hJ : (J : CochainComplex 𝒜 ℤ).IsStrictlyGE 0) :
    (ShortComplex.mk
      (J.ι.f 0)
      ((J : CochainComplex 𝒜 ℤ).d 0 1)
      (by simpa using (HomologicalComplex.Hom.comm J.ι (0 : ℤ) (1 : ℤ)))).Exact ∧
        Mono (J.ι.f 0) := sorry

-- Route correction: the previous staircase refactor left a large number of owner-transport
-- mismatches throughout the middle construction. For the current proof attempt we collapse that
-- unstable scaffold to the final source-facing theorem frontier below, so the file stays
-- compilable while the next plan targets the staircase step itself.

/-- Helper for Lemma 13.21.2: once a specific lower bound is fixed, the Cartan-Eilenberg
resolution should be built by the textbook staircase of short exact sequences on cycles, terms,
images, and homology, applying Lemma 13.18.9 alternately at each degree. -/
private theorem exists_cartanEilenbergResolution_of_isStrictlyGE
    (K : CochainComplex.Plus 𝒜) {n : ℤ} (hK : K.obj.IsStrictlyGE n) :
    Nonempty (CartanEilenbergResolution K) := sorry

/-- Lemma 13.21.2: every bounded-below cochain complex in an abelian category with enough
injectives admits a Cartan-Eilenberg resolution. -/
@[stacks 015I]
theorem exists_cartanEilenbergResolution (K : CochainComplex.Plus 𝒜) :
    Nonempty (CartanEilenbergResolution K) := by
  -- Proof comment: extract a concrete lower bound and reduce to the bounded-below staircase
  -- construction.
  obtain ⟨n, hK⟩ := exists_strictlyGE_bound (𝒜 := 𝒜) K
  exact exists_cartanEilenbergResolution_of_isStrictlyGE (𝒜 := 𝒜) K hK

end
