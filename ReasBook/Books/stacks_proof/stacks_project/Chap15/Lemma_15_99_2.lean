import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import StacksProject_2024.Chap13.Lemma_13_16_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_67_4
import StacksProject_2024.Chap15.Lemma_15_99_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "RHomPkg" => MonoidalClosed DMod

open scoped DerivedInternalHom
open scoped ModuleComplexInternalHom

/- Domain-style sampling for 15.99.2:
- primary domain: isomorphism criteria for the tensor-right/internal-Hom comparison in `D(R)`,
  propagated along truncation triangles;
- sampled owner declarations:
  `CategoryTheory.derivedInternalHom_tensor_right_comparison`,
  `CategoryTheory.derivedInternalHomTensorRightComparison_hom_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_finiteInjectiveDimension`,
  `CategoryTheory.HasFiniteTorDimension`,
  `DerivedCategory.TStructure.t.truncLE`;
- best owner abstraction:
  `source-facing`: the textbook isomorphism criterion for the canonical comparison morphism from
    Lemma `15.74.3`, now reduced through the owner-level criterion of Lemma `15.99.1`;
  `core/canonical`: the chosen monoidal-closed owner `H : MonoidalClosed DMod`, the comparison
    morphism `derivedInternalHom_tensor_right_comparison H K L M`, the source-facing notation
    `RHom[H](L, M)`, and the Chapter 15 owners `HasFiniteInjectiveDimension`,
    `HasFiniteTorDimension`, and `X.IsPseudoCoherent`;
  `bridge/view`: the lower truncations `τ_{\le n} K` used to reduce to Lemma `15.99.1`.
- primitive vs. derived:
  the primitive inputs are the owner `H`, the finite-injective-dimension hypotheses on `L` and
  `M`, the finite-tor-dimension hypothesis on `RHom[H](L, M)`, and the pseudo-coherence of the
  lower truncations of `K`; the bounded-below hypothesis needed to invoke Lemma `15.99.1` is
  derived locally from the injective-amplitude witness inside `hL`, so there is no need for an
  additional public bridge declaration here.
-/

/-- Helper for Lemma 15.99.2: the Chapter 15 internal-Hom complex agrees definitionally with
`CochainComplex.HomComplex`. -/
lemma module_complex_internal_hom_eq_hom_complex
    (A I : Cpx) :
    module_complex_internal_hom A I = CochainComplex.HomComplex A I :=
  rfl

/-- Helper for Lemma 15.99.2: if the source complex is supported in degrees `≥ a` and the target
complex is supported in degrees `≤ b`, then the Hom complex is supported in degrees `≤ b - a`. -/
lemma homComplex_isStrictlyLE_of_isStrictlyGE_of_isStrictlyLE
    (A I : Cpx) {a b : ℤ}
    (hAge : A.IsStrictlyGE a)
    (hIle : I.IsStrictlyLE b) :
    CochainComplex.IsStrictlyLE (CochainComplex.HomComplex A I) (b - a) := by
  rw [CochainComplex.isStrictlyGE_iff] at hAge
  rw [CochainComplex.isStrictlyLE_iff] at hIle
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  let Z : ℤ → ModuleCat R := fun p ↦ (ihom (A.X p)).obj (I.X (n + p))
  letI : ∀ p : ℤ, IsZero (Z p) := by
    intro p
    -- Proof comment: above total degree `b - a`, each summand `Hom(A^p, I^{n+p})` vanishes
    -- because either the source index is below `a` or the target index is above `b`.
    by_cases hp : p < a
    · change IsZero ((ihom (A.X p)).obj (I.X (n + p)))
      have hzeroA : IsZero (A.X p) := hAge p hp
      infer_instance
    · have hpa : a ≤ p := le_of_not_gt hp
      have hnp : b < n + p := by
        omega
      change IsZero ((ihom (A.X p)).obj (I.X (n + p)))
      have hzeroI : IsZero (I.X (n + p)) := hIle (n + p) hnp
      infer_instance
  have hzeroPi : IsZero (∏ᶜ Z) := by
    infer_instance
  -- Proof comment: transport the vanishing of the degreewise product back to the Hom complex.
  exact hzeroPi.of_iso <| by
    simpa [Z, module_complex_internal_hom_eq_hom_complex (A := A) (I := I)] using
      (module_complex_internal_hom_piIso A I n)

/-- Helper for Lemma 15.99.2: if the source complex is supported in degrees `≤ b` and the target
complex is supported in degrees `≥ a`, then the Hom complex is supported in degrees `≥ a - b`. -/
lemma homComplex_isStrictlyGE_of_isStrictlyLE_of_isStrictlyGE
    (A I : Cpx) {a b : ℤ}
    (hAle : A.IsStrictlyLE b)
    (hIge : I.IsStrictlyGE a) :
    CochainComplex.IsStrictlyGE (CochainComplex.HomComplex A I) (a - b) := by
  rw [CochainComplex.isStrictlyLE_iff] at hAle
  rw [CochainComplex.isStrictlyGE_iff] at hIge
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  let Z : ℤ → ModuleCat R := fun p ↦ (ihom (A.X p)).obj (I.X (n + p))
  letI : ∀ p : ℤ, IsZero (Z p) := by
    intro p
    -- Proof comment: below total degree `a - b`, each summand `Hom(A^p, I^{n+p})` vanishes
    -- because either the source index is above `b` or the target index is below `a`.
    have hp : p < a - n ∨ b < p := by
      omega
    rcases hp with hp | hp
    · have hnp : n + p < a := by
        omega
      change IsZero ((ihom (A.X p)).obj (I.X (n + p)))
      have hzeroI : IsZero (I.X (n + p)) := hIge (n + p) hnp
      infer_instance
    · change IsZero ((ihom (A.X p)).obj (I.X (n + p)))
      have hzeroA : IsZero (A.X p) := hAle p hp
      infer_instance
  have hzeroPi : IsZero (∏ᶜ Z) := by
    infer_instance
  -- Proof comment: again use the canonical product decomposition of the Hom complex in degree `n`.
  exact hzeroPi.of_iso <| by
    simpa [Z, module_complex_internal_hom_eq_hom_complex (A := A) (I := I)] using
      (module_complex_internal_hom_piIso A I n)

/-- Helper for Lemma 15.99.2: tensoring two strictly bounded-below complexes adds their lower
cutoffs. -/
lemma tensorObj_isStrictlyGE_of_isStrictlyGE
    {E F : Cpx} {a b : ℤ}
    (hE : E.IsStrictlyGE a) (hF : F.IsStrictlyGE b) :
    CochainComplex.IsStrictlyGE (HomologicalComplex.tensorObj E F) (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  change 𝟙 ((CategoryTheory.GradedObject.Monoidal.tensorObj E.X F.X) n) = 0
  -- Proof comment: below degree `a + b`, each tensor summand has one factor below its lower
  -- support bound, so the corresponding inclusion is already zero.
  apply CategoryTheory.GradedObject.Monoidal.tensorObj_ext
  intro p q h
  have hpq : p < a ∨ q < b := by
    omega
  rcases hpq with hp | hq
  · let T : ModuleCat R ⥤ ModuleCat R :=
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).flip.obj (F.X q)
    have hzero : IsZero (E.X p) := E.isZero_of_isStrictlyGE a p hp
    have hsrc : IsZero (T.obj (E.X p)) := CategoryTheory.Functor.map_isZero T hzero
    simpa [T, Category.assoc] using
      hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0
  · let T : ModuleCat R ⥤ ModuleCat R :=
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat R)).obj (E.X p)
    have hzero : IsZero (F.X q) := F.isZero_of_isStrictlyGE b q hq
    have hsrc : IsZero (T.obj (F.X q)) := CategoryTheory.Functor.map_isZero T hzero
    simpa [T, Category.assoc] using
      hsrc.eq_of_src (CategoryTheory.GradedObject.Monoidal.ιTensorObj E.X F.X p q n h) 0

/-- Helper for Lemma 15.99.2: finite injective dimension forces a lower cohomological bound. -/
lemma exists_isGE_of_hasFiniteInjectiveDimension
    (L : DMod) (hL : HasFiniteInjectiveDimension L) :
    ∃ n : ℤ, L.IsGE n := by
  -- Proof comment: unpack the injective-amplitude witness and transport the lower bound from its
  -- bounded injective representative back to `L`.
  rcases hL with ⟨a, b, hAmp⟩
  rcases hAmp with ⟨I, hIge, hIle, hIinj, ⟨e⟩⟩
  refine ⟨a, ?_⟩
  have hQge : (DerivedCategory.Q.obj I).IsGE a := by
    infer_instance
  let _ := hIge
  let _ := hIle
  let _ := hIinj
  let _ := hQge
  exact t.isGE_of_iso e.symm a

/-- Helper for Lemma 15.99.2: tensoring the standard truncation triangle with
`R\mathrm{Hom}_R(L, M)` preserves distinguishedness. -/
lemma tensor_truncation_triangle_distinguished
    (H : RHomPkg) (K L M : DMod) (n : ℤ) :
    let F : DMod ⥤ DMod := derivedTensorProduct (RHom[H](L, M))
    let T : Triangle DMod := (t.triangleLEGE n (n + 1) rfl).obj K
    (F.mapTriangle.obj T) ∈ distTriang DMod := by
  let F : DMod ⥤ DMod := derivedTensorProduct (RHom[H](L, M))
  let T : Triangle DMod := (t.triangleLEGE n (n + 1) rfl).obj K
  have hT : T ∈ distTriang DMod := by
    -- Proof comment: start from the canonical truncation triangle in the standard t-structure.
    simpa [T] using t.triangleLEGE_distinguished n (n + 1) rfl K
  let _ : F.IsTriangulated := derivedTensorProduct_isTriangulated (RHom[H](L, M))
  -- Proof comment: exact functors carry distinguished triangles to distinguished triangles.
  simpa [F, T] using F.map_distinguished T hT

/-- Helper for Lemma 15.99.2: the standard truncation triangle stays distinguished after
applying `K ↦ R\mathrm{Hom}_R(R\mathrm{Hom}_R(K, L), M)`. -/
lemma double_internalHom_truncation_triangle_distinguished
    (H : RHomPkg) (K L M : DMod) (n : ℤ) :
    let Tsrc : Triangle DMod := (t.triangleLEGE n (n + 1) rfl).obj K
    let F₁ : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj L
    let F₂ : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj M
    let Top₁ : Triangle DModᵒᵖ := (triangleOpEquivalence DMod).functor.obj (Opposite.op Tsrc)
    let Tmid : Triangle DMod := F₁.mapTriangle.obj Top₁
    let Top₂ : Triangle DModᵒᵖ := (triangleOpEquivalence DMod).functor.obj (Opposite.op Tmid)
    (F₂.mapTriangle.obj Top₂) ∈ distTriang DMod := by
  let Tsrc : Triangle DMod := (t.triangleLEGE n (n + 1) rfl).obj K
  let F₁ : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj L
  let F₂ : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj M
  let Top₁ : Triangle DModᵒᵖ := (triangleOpEquivalence DMod).functor.obj (Opposite.op Tsrc)
  let Tmid : Triangle DMod := F₁.mapTriangle.obj Top₁
  let Top₂ : Triangle DModᵒᵖ := (triangleOpEquivalence DMod).functor.obj (Opposite.op Tmid)
  have hTsrc : Tsrc ∈ distTriang DMod := by
    -- Proof comment: start from the canonical truncation triangle of `K`.
    simpa [Tsrc] using t.triangleLEGE_distinguished n (n + 1) rfl K
  have hTop₁ : Top₁ ∈ distTriang DModᵒᵖ := by
    -- Proof comment: the first internal-Hom functor is contravariant, so pass to the opposite
    -- triangle before mapping it.
    simpa [Top₁, Tsrc] using CategoryTheory.Pretriangulated.op_distinguished Tsrc hTsrc
  letI : F₁.CommShift ℤ := inferInstance
  letI : F₁.IsTriangulated := inferInstance
  have hTmid : Tmid ∈ distTriang DMod := by
    -- Proof comment: fixed-target internal Hom is triangulated once the shift-compatibility
    -- instance is exposed locally.
    simpa [Tmid, Top₁, F₁] using F₁.map_distinguished Top₁ hTop₁
  have hTop₂ : Top₂ ∈ distTriang DModᵒᵖ := by
    -- Proof comment: the outer internal-Hom functor is again contravariant, so pass to the
    -- opposite category a second time.
    simpa [Top₂, Tmid] using CategoryTheory.Pretriangulated.op_distinguished Tmid hTmid
  letI : F₂.CommShift ℤ := inferInstance
  letI : F₂.IsTriangulated := inferInstance
  -- Proof comment: mapping the second opposite truncation triangle by the outer internal Hom
  -- produces the desired distinguished triangle in `D(R)`.
  simpa [F₂, Top₂] using F₂.map_distinguished Top₂ hTop₂

/-- Helper for Lemma 15.99.2: a strict tensor-model lower bound transports to the public derived
tensor product. -/
lemma tensor_of_strictlyGE_models_isGE
    (E A : Cpx) {a b : ℤ} [E.IsKFlat]
    (hE : E.IsStrictlyGE a)
    (hA : A.IsStrictlyGE b) :
    ((DerivedCategory.Q.obj E) ⊗[R]^L (DerivedCategory.Q.obj A)).IsGE (a + b) := by
  let e :
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj E A) ≅
        ((DerivedCategory.Q.obj E) ⊗[R]^L (DerivedCategory.Q.obj A)) :=
    (Functor.Monoidal.μIso (DerivedCategory.Q : Cpx ⥤ DMod) E A) ≪≫
      derivedCategory_tensorObj_iso_derivedTensorProduct
        (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj A)
  have hTensorStrict :
      (HomologicalComplex.tensorObj E A).IsStrictlyGE (a + b) :=
    tensorObj_isStrictlyGE_of_isStrictlyGE hE hA
  let _ : (HomologicalComplex.tensorObj E A).IsStrictlyGE (a + b) := hTensorStrict
  have hModel :
      (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E A)).IsGE (a + b) := by
    infer_instance
  let _ : (DerivedCategory.Q.obj (HomologicalComplex.tensorObj E A)).IsGE (a + b) := hModel
  -- Proof comment: first compute the support bound on the strict tensor complex, then transport
  -- it through the monoidal quotient comparison and the tensor/derived-tensor identification.
  exact t.isGE_of_iso e.symm (a + b)

/-- Helper for Lemma 15.99.2: a strict support estimate on `HomComplex A I` gives the matching
upper bound on the derived internal Hom when the target model is K-injective. -/
lemma derivedInternalHom_of_strictlyGE_strictlyLE_models_isLE
    (H : RHomPkg) (A I : Cpx) {a d : ℤ} [I.IsKInjective]
    (hAge : A.IsStrictlyGE a)
    (hIle : I.IsStrictlyLE d) :
    RHom[H](DerivedCategory.Q.obj A, DerivedCategory.Q.obj I).IsLE (d - a) := by
  let e :=
    k_injective_target_module_complex_internal_hom_represents_derivedInternalHom
      (R := R) H A I
  have hHomStrict :
      CochainComplex.IsStrictlyLE (CochainComplex.HomComplex A I) (d - a) :=
    homComplex_isStrictlyLE_of_isStrictlyGE_of_isStrictlyLE A I hAge hIle
  let _ : CochainComplex.IsStrictlyLE (CochainComplex.HomComplex A I) (d - a) := hHomStrict
  have hModel :
      (DerivedCategory.Q.obj (CochainComplex.HomComplex A I)).IsLE (d - a) := by
    infer_instance
  let _ : (DerivedCategory.Q.obj (CochainComplex.HomComplex A I)).IsLE (d - a) := hModel
  -- Proof comment: the K-injective target model computes the derived internal Hom on the nose, so
  -- the strict upper support bound transfers directly through the representing isomorphism.
  exact t.isLE_of_iso e.symm (d - a)

/-- Helper for Lemma 15.99.2: a strict support estimate on the source model of a derived internal
Hom with K-injective target gives the corresponding lower bound. -/
lemma derivedInternalHom_of_strictlyLE_strictlyGE_models_isGE
    (H : RHomPkg) (A I : Cpx) {b a : ℤ} [I.IsKInjective]
    (hAle : A.IsStrictlyLE b)
    (hIge : I.IsStrictlyGE a) :
    RHom[H](DerivedCategory.Q.obj A, DerivedCategory.Q.obj I).IsGE (a - b) := by
  let e :=
    k_injective_target_module_complex_internal_hom_represents_derivedInternalHom
      (R := R) H A I
  have hHomStrict :
      CochainComplex.IsStrictlyGE (CochainComplex.HomComplex A I) (a - b) :=
    homComplex_isStrictlyGE_of_isStrictlyLE_of_isStrictlyGE A I hAle hIge
  let _ : CochainComplex.IsStrictlyGE (CochainComplex.HomComplex A I) (a - b) := hHomStrict
  have hModel :
      (DerivedCategory.Q.obj (CochainComplex.HomComplex A I)).IsGE (a - b) := by
    infer_instance
  let _ : (DerivedCategory.Q.obj (CochainComplex.HomComplex A I)).IsGE (a - b) := hModel
  -- Proof comment: as above, once the strict Hom complex is known to be supported in degrees
  -- `≥ a - b`, the derived internal Hom inherits the same lower bound via the representing iso.
  exact t.isGE_of_iso e.symm (a - b)

/-- Helper for Lemma 15.99.2: weakening the lower cutoff preserves membership in
`D(R)^{\ge -}`. -/
lemma isGE_of_le
    {X : DMod} {a b : ℤ}
    (hX : X.IsGE b) (hab : a ≤ b) :
    X.IsGE a := by
  rw [DerivedCategory.isGE_iff] at hX ⊢
  intro i hi
  -- Proof comment: vanishing below the stronger cutoff `b` also gives vanishing below every
  -- weaker cutoff `a ≤ b`.
  exact hX i (lt_of_lt_of_le hi hab)

/-- Helper for Lemma 15.99.2: finite tor dimension yields a K-flat termwise-flat representative
supported in sufficiently high degrees. -/
lemma exists_strictlyGE_kFlat_termwiseFlat_representation_of_hasFiniteTorDimension
    (X : DMod) (hX : HasFiniteTorDimension X) :
    ∃ (a : ℤ) (E : Cpx) (_ : X ≅ DerivedCategory.Q.obj E),
      E.IsStrictlyGE a ∧ E.IsKFlat ∧ E.IsTermwiseFlat := by
  rcases (hasFiniteTorDimension_iff X).1 hX with ⟨a, b, hAmp⟩
  have hXge : HasTorAmplitudeGE X a := hAmp.hasTorAmplitudeGE
  -- Proof comment: finite tor dimension gives one finite interval `[a, b]`, and the canonical
  -- Chapter 15 representative theorem upgrades its lower endpoint to the required K-flat,
  -- termwise-flat model.
  rcases (hasTorAmplitudeGE_iff_exists_representative (R := R) X a).1 hXge with
    ⟨E, e, hEge, hEKFlat, hEFlat⟩
  exact ⟨a, E, e, hEge, hEKFlat, hEFlat⟩

/-- Helper for Lemma 15.99.2: one linear cutoff controls both tail terms appearing in the
truncation-triangle argument. -/
lemma truncGE_tail_images_are_isGE_with_linear_bound
    (H : RHomPkg)
    (K L M : DMod)
    (hL : HasFiniteInjectiveDimension L)
    (hM : HasFiniteInjectiveDimension M)
    (hLM : HasFiniteTorDimension (RHom[H](L, M))) :
    ∃ c : ℤ, ∀ n : ℤ,
      (RHom[H](L, M) ⊗[R]^L ((t.truncGE (n + 1)).obj K)).IsGE (n - c) ∧
        RHom[H](RHom[H](((t.truncGE (n + 1)).obj K), L), M).IsGE (n - c) := by
  obtain ⟨aE, E, eE, hEge, hEKFlat, _hEFlat⟩ :=
    exists_strictlyGE_kFlat_termwiseFlat_representation_of_hasFiniteTorDimension
      (X := RHom[H](L, M)) hLM
  obtain ⟨I, aL, bL, _hIge, hIle, hIinj, ⟨eI⟩⟩ :=
    exists_bounded_injective_representation L hL
  obtain ⟨J, aM, bM, hJge, _hJle, hJinj, ⟨eJ⟩⟩ :=
    exists_bounded_injective_representation M hM
  let _ : E.IsKFlat := hEKFlat
  let _ : I.IsKInjective := CochainComplex.isKInjective_of_injective I aL
  let _ : J.IsKInjective := CochainComplex.isKInjective_of_injective J aM
  refine ⟨max (-aE - 1) (bL - aM - 1), ?_⟩
  intro n
  have hTailGE : ((t.truncGE (n + 1)).obj K).IsGE (n + 1) := by
    infer_instance
  have hTailRep :
      ∃ A : Cpx,
        A.IsStrictlyGE (n + 1) ∧
          Nonempty (DerivedCategory.Q.obj A ≅ ((t.truncGE (n + 1)).obj K)) := by
    -- Proof comment: replace the truncation tail by the canonical bounded-below representative
    -- produced from its preimage and the t-structure lower bound.
    simpa using
      (exists_boundedBelow_representation ((t.truncGE (n + 1)).obj K) ⟨n + 1, hTailGE⟩)
  obtain ⟨A, hAge, ⟨eA⟩⟩ := hTailRep
  have hTensorModel :
      ((DerivedCategory.Q.obj E) ⊗[R]^L (DerivedCategory.Q.obj A)).IsGE (aE + (n + 1)) :=
    tensor_of_strictlyGE_models_isGE (R := R) E A hEge hAge
  let _ :
      ((DerivedCategory.Q.obj E) ⊗[R]^L (DerivedCategory.Q.obj A)).IsGE (aE + (n + 1)) :=
    hTensorModel
  have hTensorMapA :
      IsIso ((derivedTensorProductMap H eA.hom).app (RHom[H](L, M))) := by
    dsimp [derivedTensorProductMap]
    infer_instance
  let eTensor :
      ((DerivedCategory.Q.obj E) ⊗[R]^L (DerivedCategory.Q.obj A)) ≅
        (RHom[H](L, M) ⊗[R]^L ((t.truncGE (n + 1)).obj K)) :=
    ((derivedTensorProduct (DerivedCategory.Q.obj A)).mapIso eE.symm) ≪≫
      asIso ((derivedTensorProductMap H eA.hom).app (RHom[H](L, M)))
  have hTensorTarget :
      (RHom[H](L, M) ⊗[R]^L ((t.truncGE (n + 1)).obj K)).IsGE (aE + (n + 1)) :=
    t.isGE_of_iso eTensor (aE + (n + 1))
  have hTensorWeak :
      (RHom[H](L, M) ⊗[R]^L ((t.truncGE (n + 1)).obj K)).IsGE
        (n - max (-aE - 1) (bL - aM - 1)) := by
    -- Proof comment: the common cutoff is chosen weak enough to be dominated by the tensor-model
    -- lower bound and the double-`RHom` lower bound simultaneously.
    refine isGE_of_le hTensorTarget ?_
    omega
  have hHomComplexLE :
      CochainComplex.IsStrictlyLE (CochainComplex.HomComplex A I) (bL - (n + 1)) :=
    homComplex_isStrictlyLE_of_isStrictlyGE_of_isStrictlyLE A I hAge hIle
  have hDoubleModel :
      RHom[H](DerivedCategory.Q.obj (CochainComplex.HomComplex A I), DerivedCategory.Q.obj J)
        .IsGE (aM - (bL - (n + 1))) :=
    derivedInternalHom_of_strictlyLE_strictlyGE_models_isGE
      (R := R) H (CochainComplex.HomComplex A I) J hHomComplexLE hJge
  let _ :
      RHom[H](DerivedCategory.Q.obj (CochainComplex.HomComplex A I), DerivedCategory.Q.obj J)
        .IsGE (aM - (bL - (n + 1))) :=
    hDoubleModel
  let innerRep :
      DerivedCategory.Q.obj (CochainComplex.HomComplex A I) ≅
        RHom[H](DerivedCategory.Q.obj A, DerivedCategory.Q.obj I) :=
    k_injective_target_module_complex_internal_hom_represents_derivedInternalHom
      (R := R) H A I
  let mapA :=
    derivedInternalHomMap H (derivedInternalHomMap H eA.hom (𝟙 L)) (𝟙 M)
  let mapI :=
    derivedInternalHomMap H
      (derivedInternalHomMap H (𝟙 (DerivedCategory.Q.obj A)) eI.hom) (𝟙 M)
  let mapRep :=
    derivedInternalHomMap H innerRep.hom (𝟙 M)
  let mapJ :=
    derivedInternalHomMap H (𝟙 (DerivedCategory.Q.obj (CochainComplex.HomComplex A I))) eJ.hom
  have hInnerA : IsIso (derivedInternalHomMap H eA.hom (𝟙 L)) := by
    dsimp [derivedInternalHomMap]
    infer_instance
  have hMapA : IsIso mapA := by
    let _ : IsIso (derivedInternalHomMap H eA.hom (𝟙 L)) := hInnerA
    -- Proof comment: changing the tail representative changes the outer source object by an
    -- isomorphism, hence the iterated internal Hom by an isomorphism as well.
    dsimp [mapA, derivedInternalHomMap]
    infer_instance
  have hInnerI :
      IsIso (derivedInternalHomMap H (𝟙 (DerivedCategory.Q.obj A)) eI.hom) := by
    dsimp [derivedInternalHomMap]
    infer_instance
  have hMapI : IsIso mapI := by
    let _ : IsIso (derivedInternalHomMap H (𝟙 (DerivedCategory.Q.obj A)) eI.hom) := hInnerI
    -- Proof comment: the chosen injective model for `L` gives an isomorphic inner internal Hom,
    -- so the outer internal Hom sees an isomorphic source object.
    dsimp [mapI, derivedInternalHomMap]
    infer_instance
  have hMapRep : IsIso mapRep := by
    dsimp [mapRep, derivedInternalHomMap]
    infer_instance
  have hMapJ : IsIso mapJ := by
    dsimp [mapJ, derivedInternalHomMap]
    infer_instance
  let eDouble :
      RHom[H](DerivedCategory.Q.obj (CochainComplex.HomComplex A I), DerivedCategory.Q.obj J) ≅
        RHom[H](RHom[H](((t.truncGE (n + 1)).obj K), L), M) :=
    asIso mapJ ≪≫ (asIso mapRep).symm ≪≫ (asIso mapI).symm ≪≫ (asIso mapA).symm
  have hDoubleTarget :
      RHom[H](RHom[H](((t.truncGE (n + 1)).obj K), L), M).IsGE
        (aM - (bL - (n + 1))) :=
    t.isGE_of_iso eDouble (aM - (bL - (n + 1)))
  have hDoubleWeak :
      RHom[H](RHom[H](((t.truncGE (n + 1)).obj K), L), M).IsGE
        (n - max (-aE - 1) (bL - aM - 1)) := by
    -- Proof comment: the same numerical constant also lies below the outer derived-Hom cutoff.
    refine isGE_of_le hDoubleTarget ?_
    omega
  exact ⟨hTensorWeak, hDoubleWeak⟩

/-- Helper for Lemma 15.99.2: every lower truncation `τ_{\le n} K` satisfies the comparison
isomorphism from Lemma `15.99.1` under the hypotheses of the current statement. -/
lemma truncLE_tensor_right_comparison_isIso
    (H : RHomPkg)
    (K L M : DMod)
    (hL : HasFiniteInjectiveDimension L)
    (hM : HasFiniteInjectiveDimension M)
    (hτK : ∀ n : ℤ, ((t.truncLE n).obj K).IsPseudoCoherent)
    (n : ℤ) :
    IsIso
      (derivedInternalHom_tensor_right_comparison H ((t.truncLE n).obj K) L M) := by
  have hLge : ∃ a : ℤ, L.IsGE a :=
    exists_isGE_of_hasFiniteInjectiveDimension L hL
  -- Proof comment: apply Lemma `15.99.1` to `τ≤n K`, using pseudo-coherence of the truncation,
  -- the bounded-below consequence of finite injective dimension for `L`, and finite injective
  -- dimension for `M`.
  exact
    derivedInternalHomTensorRightComparison_hom_isIso_of_isPerfect_or_of_pseudoCoherent_boundedBelow_finiteInjectiveDimension
      H ((t.truncLE n).obj K) L M (Or.inr ⟨hτK n, hLge, hM⟩)

/-- Helper for Lemma 15.99.2: a uniform linear lower bound on the two truncation tails can be
specialized to any fixed homology degree by choosing `n` large enough. -/
lemma exists_tail_cutoff_for_homology_degree
    (H : RHomPkg)
    (K L M : DMod)
    (i c : ℤ)
    (hbound : ∀ n : ℤ,
      (RHom[H](L, M) ⊗[R]^L ((t.truncGE (n + 1)).obj K)).IsGE (n - c) ∧
        RHom[H](RHom[H](((t.truncGE (n + 1)).obj K), L), M).IsGE (n - c)) :
    ∃ n : ℤ,
      (RHom[H](L, M) ⊗[R]^L ((t.truncGE (n + 1)).obj K)).IsGE (i + 1) ∧
        RHom[H](RHom[H](((t.truncGE (n + 1)).obj K), L), M).IsGE (i + 1) := by
  refine ⟨i + c + 1, ?_⟩
  obtain ⟨hTensor, hDouble⟩ := hbound (i + c + 1)
  have hcut : (i + c + 1) - c = i + 1 := by
    omega
  -- Proof comment: evaluate the linear bound at `n = i + c + 1`, where the promised cutoff is
  -- exactly the degree `i + 1` needed to kill `i`-th homology of the tail terms.
  simpa [hcut] using And.intro hTensor hDouble

/-- Lemma 15.99.2: the tensor-right comparison map
`R\mathrm{Hom}_R(L, M) \otimes_R^{\mathbf L} K \to
R\mathrm{Hom}_R(R\mathrm{Hom}_R(K, L), M)` is an isomorphism when `L` and `M` have finite
injective dimension, `R\mathrm{Hom}_R(L, M)` has finite tor dimension, and every lower truncation
`τ_{\le n} K` is pseudo-coherent. -/
@[stacks 0A69]
theorem derivedInternalHomTensorRightComparison_hom_isIso_of_finiteInjectiveDimension_of_finiteTorDimension_of_truncLE_isPseudoCoherent
    (H : RHomPkg)
    (K L M : DMod)
    (hL : HasFiniteInjectiveDimension L)
    (hM : HasFiniteInjectiveDimension M)
    (hLM : HasFiniteTorDimension (RHom[H](L, M)))
    (hτK : ∀ n : ℤ, ((t.truncLE n).obj K).IsPseudoCoherent) :
    IsIso (derivedInternalHom_tensor_right_comparison H K L M) := by
  -- Proof comment: first extract the bounded-below witness needed to apply Lemma `15.99.1` to
  -- each lower truncation `τ≤ n K`.
  have hLge : ∃ n : ℤ, L.IsGE n :=
    exists_isGE_of_hasFiniteInjectiveDimension L hL
  have hTensorTriangle :
      ∀ n : ℤ,
        let F : DMod ⥤ DMod := derivedTensorProduct (RHom[H](L, M))
        let T : Triangle DMod := (t.triangleLEGE n (n + 1) rfl).obj K
        (F.mapTriangle.obj T) ∈ distTriang DMod :=
    fun n ↦ tensor_truncation_triangle_distinguished H K L M n
  have hDoubleInternalHomTriangle :
      ∀ n : ℤ,
        let Tsrc : Triangle DMod := (t.triangleLEGE n (n + 1) rfl).obj K
        let F₁ : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj L
        let F₂ : DModᵒᵖ ⥤ DMod := (MonoidalClosed.internalHom).flip.obj M
        let Top₁ : Triangle DModᵒᵖ := (triangleOpEquivalence DMod).functor.obj (Opposite.op Tsrc)
        let Tmid : Triangle DMod := F₁.mapTriangle.obj Top₁
        let Top₂ : Triangle DModᵒᵖ := (triangleOpEquivalence DMod).functor.obj (Opposite.op Tmid)
        (F₂.mapTriangle.obj Top₂) ∈ distTriang DMod :=
    fun n ↦ double_internalHom_truncation_triangle_distinguished H K L M n
  have hTruncIso :
      ∀ n : ℤ,
        IsIso
          (derivedInternalHom_tensor_right_comparison H ((t.truncLE n).obj K) L M) :=
    fun n ↦ truncLE_tensor_right_comparison_isIso H K L M hL hM hτK n
  have hTailBound :
      ∃ c : ℤ, ∀ n : ℤ,
        (RHom[H](L, M) ⊗[R]^L ((t.truncGE (n + 1)).obj K)).IsGE (n - c) ∧
          RHom[H](RHom[H](((t.truncGE (n + 1)).obj K), L), M).IsGE (n - c) :=
    truncGE_tail_images_are_isGE_with_linear_bound H K L M hL hM hLM
  have hTailCutoff :
      ∀ i : ℤ, ∃ n : ℤ,
        (RHom[H](L, M) ⊗[R]^L ((t.truncGE (n + 1)).obj K)).IsGE (i + 1) ∧
          RHom[H](RHom[H](((t.truncGE (n + 1)).obj K), L), M).IsGE (i + 1) := by
    intro i
    rcases hTailBound with ⟨c, hc⟩
    -- Proof comment: the linear bound from the source proof now yields the exact `i + 1`
    -- truncation cutoff needed for the fixed-degree homology comparison.
    exact exists_tail_cutoff_for_homology_degree H K L M i c hc
  -- Route correction: the previous attempt stalled on an over-general comparison theorem. The
  -- source-faithful route is now reduced to the actual missing ingredients: low-degree vanishing
  -- for the two tail images and the resulting homology-level conjugation across `truncLEι`.
  -- TODO(Lemma 15.99.2): choose `n` so the tensor tail and the iterated-`RHom` tail lie in
  -- `D^{≥ i + 1}` for the fixed degree `i`; then package the right-hand truncation triangle for
  -- `K ↦ RHom_R(RHom_R(K, L), M)`, use `isIso_homologyMap_mor₁_of_distTriang_obj₃_isGE` on both
  -- mapped triangles, and finish by naturality of
  -- `derivedInternalHom_tensor_right_comparison` along `((t.truncLEι n).app K)`.
  let _ := hTensorTriangle
  let _ := hDoubleInternalHomTriangle
  let _ := hLge
  let _ := hTruncIso
  let _ := hTailBound
  let _ := hTailCutoff
  let _ := hM
  let _ := hLM
  let _ := hτK
  sorry

end

end CategoryTheory
