import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Limits.MonoCoprod
import StacksProject_2024.Chap13.«13_18_6_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe w v u

namespace CochainComplex

/-
Domain-style sampling for Lemma 19.12.4:
- primary domain: functorial cochain-complex approximations in a Grothendieck abelian category,
  used to kill maps from a chosen acyclic family up to homotopy and later upgraded to
  K-injective resolutions;
- sampled owner declarations:
  `HasFunctorialInjectiveEmbeddings`,
  `CochainComplex.ResolutionFunctor`,
  `CochainComplex.IsKInjective`,
  `NatTrans.mono_iff_mono_app`;
- best owner abstraction: this Chapter 19 construction is a cochain-complex-level generalization
  of the Chapter 13 `CochainComplex.ResolutionFunctor` owner family, so its
  primitive owner should also live in the `CochainComplex` namespace; the primitive data is a
  functorial approximation `FunctorialComplexApproximation C`, consisting of an endofunctor on
  `CochainComplex C ℤ`, a natural comparison map, and the facts that this comparison
  natural transformation is mono and objectwise a quasi-isomorphism;
- primitive data: the functorial approximation itself;
- derived API: the null-homotopy killing property of Lemma 19.12.4 and the later injective-term
  and K-injective enhancements, together with the inherited degreewise monomorphism facts.

Source/core/bridge triage:
- `source-facing`: the existence of a functorial complex approximation whose comparison maps kill
  maps from the chosen acyclic family up to homotopy;
- `core/canonical`: `FunctorialComplexApproximation C`;
- `bridge/view`: later specializations adding injective-subobject and K-injective target
  properties.
-/

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type w}

/-- A functorial cochain-complex approximation by a monomorphic quasi-isomorphic enlargement.
This is the shared primitive owner for the Chapter 19 constructions built from such
approximations; the induced degreewise monomorphisms are derived from the complex-level mono
field. -/
structure FunctorialComplexApproximation (C : Type u) [Category.{v} C] [Abelian C] where
  /-- The underlying endofunctor on cochain complexes. -/
  toFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ
  /-- The natural comparison map from a complex to its chosen enlargement. -/
  ι : 𝟭 (CochainComplex C ℤ) ⟶ toFunctor
  /-- The comparison natural transformation is monomorphic. -/
  mono_ι : Mono ι
  /-- Each comparison map is a quasi-isomorphism. -/
  quasiIso_app (M : CochainComplex C ℤ) : QuasiIso (ι.app M)

namespace FunctorialComplexApproximation

variable {C : Type u} [Category.{v} C] [Abelian C]

instance (J : FunctorialComplexApproximation C) : Mono J.ι :=
  J.mono_ι

/-- Each comparison morphism of a functorial complex approximation is mono. -/
theorem mono_app (J : FunctorialComplexApproximation C) (M : CochainComplex C ℤ) :
    Mono (J.ι.app M) :=
  (NatTrans.mono_iff_mono_app J.ι).1 J.mono_ι M

end FunctorialComplexApproximation

/-- Helper for Lemma 19.12.4: replace each acyclic complex by the cone on its identity. -/
private noncomputable abbrev coneReplacement
    (K : I → CochainComplex C ℤ) (i : I) : CochainComplex C ℤ :=
  CochainComplex.mappingCone (𝟙 (K i))

/-- Helper for Lemma 19.12.4: the canonical map from a complex into the cone on its identity. -/
private noncomputable abbrev coneReplacementMap
    (K : I → CochainComplex C ℤ) (i : I) : K i ⟶ coneReplacement K i :=
  CochainComplex.mappingCone.inr (𝟙 (K i))

/-- Helper for Lemma 19.12.4: the cone-on-identity inclusion is termwise split mono, hence mono as
a morphism of cochain complexes. -/
private theorem mappingCone_inr_id_mono
    (X : CochainComplex C ℤ) :
    Mono (CochainComplex.mappingCone.inr (𝟙 X)) := by
  -- The degreewise right inverse `mappingCone.snd` lets us cancel each component of `inr`.
  refine HomologicalComplex.mono_of_mono_f _ ?_
  intro n
  refine ⟨fun {Z} a b hab ↦ ?_⟩
  have h :=
    congrArg
      (fun k => k ≫ (CochainComplex.mappingCone.snd (𝟙 X)).v n n (add_zero n))
      hab
  simpa using h

/-- Helper for Lemma 19.12.4: the cone-on-identity inclusion is homotopic to zero. -/
private theorem mappingCone_inr_id_nullhomotopic
    (X : CochainComplex C ℤ) :
    Nonempty (Homotopy (CochainComplex.mappingCone.inr (𝟙 X)) 0) := by
  -- Route correction: use the homotopy-cofiber null-homotopy for the right inclusion with
  -- `φ = 𝟙_X`, rather than trying to extract a degree `-1` cochain by hand.
  refine ⟨?_⟩
  simpa [CochainComplex.mappingCone, Category.id_comp] using
    (HomologicalComplex.homotopyCofiber.inrCompHomotopy
      (φ := (𝟙 X))
      (hc := fun j ↦ ⟨j - 1, by simp⟩))

section AcyclicKillingData

variable [IsGrothendieckAbelian.{w} C]

/-- Helper for Lemma 19.12.4: the `w`-small owner of all pairs `(i, w : K i ⟶ M)`. -/
private noncomputable abbrev sourceIndexSmall
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) : Type w :=
  Shrink.{w} (Σ i : I, K i ⟶ M)

/-- Helper for Lemma 19.12.4: recover the represented pair `(i, w : K i ⟶ M)` from the shrunken
index owner. -/
private noncomputable abbrev sourceIndexPair
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ)
    (p : sourceIndexSmall K M) : Σ i : I, K i ⟶ M :=
  (equivShrink (Σ i : I, K i ⟶ M)).symm p

/-- Helper for Lemma 19.12.4: the source summand indexed by a chosen pair `(i, w : K i ⟶ M)`. -/
private noncomputable abbrev acyclicKillingSourceObj
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ)
    (p : sourceIndexSmall K M) : CochainComplex C ℤ :=
  let q := sourceIndexPair K M p
  K q.1

/-- Helper for Lemma 19.12.4: the cone replacement summand indexed by a chosen pair
`(i, w : K i ⟶ M)`. -/
private noncomputable abbrev acyclicKillingReplacementObj
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ)
    (p : sourceIndexSmall K M) : CochainComplex C ℤ :=
  let q := sourceIndexPair K M p
  coneReplacement K q.1

/-- Helper for Lemma 19.12.4: the coproduct of all source complexes mapping to `M`. -/
private noncomputable abbrev acyclicKillingSource
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :=
  ∐ fun p : sourceIndexSmall K M ↦ acyclicKillingSourceObj K M p

/-- Helper for Lemma 19.12.4: the coproduct of all cone replacements attached to maps into `M`. -/
private noncomputable abbrev acyclicKillingReplacement
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :=
  ∐ fun p : sourceIndexSmall K M ↦ acyclicKillingReplacementObj K M p

/-- Helper for Lemma 19.12.4: the left coproduct map built from the cone-on-identity inclusions. -/
private noncomputable abbrev acyclicKillingLeftMap
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    acyclicKillingSource K M ⟶ acyclicKillingReplacement K M :=
  Limits.Sigma.map (fun p : sourceIndexSmall K M ↦
    let q := sourceIndexPair K M p
    coneReplacementMap K q.1)

/-- Helper for Lemma 19.12.4: the upper coproduct map recording all maps `K i ⟶ M`. -/
private noncomputable abbrev acyclicKillingTopMap
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    acyclicKillingSource K M ⟶ M :=
  Limits.Sigma.desc (fun p : sourceIndexSmall K M ↦
    let q := sourceIndexPair K M p
    q.2)

/-- Helper for Lemma 19.12.4: postcomposition with `f` on the shrunken index owner. -/
private noncomputable def acyclicKillingSmallIndexMap
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    sourceIndexSmall K M → sourceIndexSmall K N :=
  fun p ↦
    let q := sourceIndexPair K M p
    equivShrink (Σ i : I, K i ⟶ N) ⟨q.1, q.2 ≫ f⟩

/-- Helper for Lemma 19.12.4: reindexing along postcomposition preserves the source summand. -/
private theorem acyclic_killing_source_index_pair_smallIndexMap
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (p : sourceIndexSmall K M) :
    sourceIndexPair K N (acyclicKillingSmallIndexMap K f p) =
      ⟨(sourceIndexPair K M p).1, (sourceIndexPair K M p).2 ≫ f⟩ := by
  -- Unfold once; `equivShrink` and its inverse cancel definitionally on the represented pair.
  simp [acyclicKillingSmallIndexMap, sourceIndexPair]

/-- Helper for Lemma 19.12.4: postcomposition on the shrunken index keeps the represented owner
complex `K i` fixed. -/
private theorem acyclicKillingSmallIndexMap_fst
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (p : sourceIndexSmall K M) :
    (sourceIndexPair K N (acyclicKillingSmallIndexMap K f p)).1 =
      (sourceIndexPair K M p).1 := by
  -- Proof comment: the explicit represented pair after postcomposition only changes the arrow
  -- component, so the owner index is unchanged.
  simpa using congrArg Sigma.fst (acyclic_killing_source_index_pair_smallIndexMap K f p)

/-- Helper for Lemma 19.12.4: reindexing along postcomposition preserves the source summand. -/
private theorem acyclic_killing_source_obj_eq
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (p : sourceIndexSmall K M) :
    acyclicKillingSourceObj K M p =
      acyclicKillingSourceObj K N (acyclicKillingSmallIndexMap K f p) := by
  -- Normalize the represented pair after postcomposition; only the map `w` changes, not the
  -- chosen owner `i`.
  simpa [acyclicKillingSourceObj] using
    congrArg (fun q : Σ i : I, K i ⟶ N => K q.1)
      (acyclic_killing_source_index_pair_smallIndexMap K f p).symm

/-- Helper for Lemma 19.12.4: the canonical transport on source summands induced by
postcomposition. -/
private noncomputable abbrev acyclicKillingSourceObjMap
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (p : sourceIndexSmall K M) :
    acyclicKillingSourceObj K M p ⟶
      acyclicKillingSourceObj K N (acyclicKillingSmallIndexMap K f p) :=
  eqToHom (acyclic_killing_source_obj_eq K f p)

/-- Helper for Lemma 19.12.4: reindexing along postcomposition preserves the replacement
summand. -/
private theorem acyclic_killing_replacement_obj_eq
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (p : sourceIndexSmall K M) :
    acyclicKillingReplacementObj K M p =
      acyclicKillingReplacementObj K N (acyclicKillingSmallIndexMap K f p) := by
  -- The normalized pair still has the same owner `i`, so the cone replacement is unchanged.
  simpa [acyclicKillingReplacementObj] using
    congrArg (fun q : Σ i : I, K i ⟶ N => coneReplacement K q.1)
      (acyclic_killing_source_index_pair_smallIndexMap K f p).symm

/-- Helper for Lemma 19.12.4: the canonical transport on replacement summands induced by
postcomposition. -/
private noncomputable abbrev acyclicKillingReplacementObjMap
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (p : sourceIndexSmall K M) :
    acyclicKillingReplacementObj K M p ⟶
      acyclicKillingReplacementObj K N (acyclicKillingSmallIndexMap K f p) :=
  eqToHom (acyclic_killing_replacement_obj_eq K f p)

/-- Helper for Lemma 19.12.4: the shrunken index map is the identity for `𝟙_M`. -/
private theorem acyclic_killing_small_index_map_id
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    acyclicKillingSmallIndexMap K (𝟙 M) = id := by
  -- Route correction: the universe repair is now baked into `Shrink`, so the identity law is an
  -- honest computation on the represented pair `(i, w)`.
  funext p
  simp [acyclicKillingSmallIndexMap, sourceIndexPair]

/-- Helper for Lemma 19.12.4: reindexing twice corresponds to postcomposition by the composite on
the represented pair. -/
private theorem acyclic_killing_source_index_pair_smallIndexMap_comp
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P)
    (p : sourceIndexSmall K M) :
    sourceIndexPair K P
        ((acyclicKillingSmallIndexMap K g ∘ acyclicKillingSmallIndexMap K f) p) =
      ⟨(sourceIndexPair K M p).1, (sourceIndexPair K M p).2 ≫ f ≫ g⟩ := by
  -- Normalize the first reindexing step and then the second; the represented owner `i` stays
  -- fixed, and only the arrow part composes by associativity.
  rw [Function.comp]
  rw [acyclic_killing_source_index_pair_smallIndexMap K g (acyclicKillingSmallIndexMap K f p)]
  rw [acyclic_killing_source_index_pair_smallIndexMap K f p]
  simpa [Category.assoc]

/-- Helper for Lemma 19.12.4: the shrunken index map respects composition. -/
private theorem acyclic_killing_small_index_map_comp
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P) :
    acyclicKillingSmallIndexMap K (f ≫ g) =
      acyclicKillingSmallIndexMap K g ∘ acyclicKillingSmallIndexMap K f := by
  -- Compare both functions after decoding the shrunken index back to the represented pair.
  funext p
  apply (equivShrink (Σ i : I, K i ⟶ P)).symm.injective
  simpa [Category.assoc] using
    (acyclic_killing_source_index_pair_smallIndexMap K (f ≫ g) p).trans
      (acyclic_killing_source_index_pair_smallIndexMap_comp K f g p).symm

/-- Helper for Lemma 19.12.4: the source-side transport on an individual summand is the identity
after normalizing the represented pair. -/
private theorem acyclic_killing_source_obj_map_eq_id
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (p : sourceIndexSmall K M) :
    (acyclic_killing_source_obj_eq K f p) ▸ acyclicKillingSourceObjMap K f p =
      𝟙 (acyclicKillingSourceObj K M p) := by
  -- TODO: replace this raw transport statement by the `Sigma.ι`-level computation lemma for
  -- `acyclicKillingSourceMap`; direct dependent elimination still blocks on the preserved owner
  -- equality `K (sourceIndexPair ...).1 = K (sourceIndexPair ...).1`.
  sorry

/-- Helper for Lemma 19.12.4: the replacement-side transport on an individual summand is the
identity after normalizing the represented pair. -/
private theorem acyclic_killing_replacement_obj_map_eq_id
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (p : sourceIndexSmall K M) :
    (acyclic_killing_replacement_obj_eq K f p) ▸ acyclicKillingReplacementObjMap K f p =
      𝟙 (acyclicKillingReplacementObj K M p) := by
  -- TODO: prove the replacement-side analogue via the coproduct-injection formula for
  -- `acyclicKillingReplacementMap`; direct elimination still blocks on the cone family transport.
  sorry

/-- Helper for Lemma 19.12.4: the cone-inclusion summand commutes with the source/replacement
transport induced by postcomposition. -/
private theorem acyclicKillingLeftComponent_natural
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (p : sourceIndexSmall K M) :
    coneReplacementMap K (sourceIndexPair K M p).1 ≫
        acyclicKillingReplacementObjMap K f p =
      acyclicKillingSourceObjMap K f p ≫
        coneReplacementMap K
          (sourceIndexPair K N (acyclicKillingSmallIndexMap K f p)).1 := by
  -- TODO: reprove this after exposing the source/replacement maps only through their `Sigma.ι`
  -- formulas; rewriting the owner index inside the cone family still triggers dependent transport.
  sorry

/-- Helper for Lemma 19.12.4: the source transport followed by the represented arrow into `N`
recovers postcomposition by `f`. -/
private theorem acyclicKillingTopComponent_natural
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)
    (p : sourceIndexSmall K M) :
    acyclicKillingSourceObjMap K f p ≫
        (sourceIndexPair K N (acyclicKillingSmallIndexMap K f p)).2 =
      (sourceIndexPair K M p).2 ≫ f := by
  -- TODO: discharge this as the target component of the source `Sigma.ι` computation lemma; raw
  -- rewriting on `sourceIndexPair ... .2` still depends on the blocked owner transport.
  sorry

/-- Helper for Lemma 19.12.4: the source-side summand transport respects postcomposition after
aligning the composite reindexing with the direct reindexing. -/
private theorem acyclicKillingSourceObj_eq_smallIndexMap_comp
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P)
    (p : sourceIndexSmall K M) :
    acyclicKillingSourceObj K P (acyclicKillingSmallIndexMap K g
        (acyclicKillingSmallIndexMap K f p)) =
      acyclicKillingSourceObj K P
        ((acyclicKillingSmallIndexMap K g ∘ acyclicKillingSmallIndexMap K f) p) := by
  -- The direct and iterated reindexings agree on the represented source object.
  simpa [Function.comp] using
    congrArg (fun r : sourceIndexSmall K P ↦ acyclicKillingSourceObj K P r)
      (congrArg (fun h ↦ h p) (acyclic_killing_small_index_map_comp K f g).symm)

/-- Helper for Lemma 19.12.4: the source objects for the composed-index function and the direct
postcomposition index agree. -/
private theorem acyclicKillingSourceObj_eq_smallIndexMap_direct
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P)
    (p : sourceIndexSmall K M) :
    acyclicKillingSourceObj K P
        ((acyclicKillingSmallIndexMap K g ∘ acyclicKillingSmallIndexMap K f) p) =
      acyclicKillingSourceObj K P (acyclicKillingSmallIndexMap K (f ≫ g) p) := by
  simpa using
    congrArg (fun r : sourceIndexSmall K P ↦ acyclicKillingSourceObj K P r)
      (congrArg (fun h ↦ h p) (acyclic_killing_small_index_map_comp K f g)).symm

/-- Helper for Lemma 19.12.4: the source-side summand transport respects postcomposition after
aligning the composite reindexing with the direct reindexing. -/
private theorem acyclicKillingSourceObjMap_comp
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P)
    (p : sourceIndexSmall K M) :
    acyclicKillingSourceObjMap K f p ≫
        acyclicKillingSourceObjMap K g (acyclicKillingSmallIndexMap K f p) ≫
        eqToHom (acyclicKillingSourceObj_eq_smallIndexMap_comp K f g p) ≫
        eqToHom (acyclicKillingSourceObj_eq_smallIndexMap_direct K f g p) =
      acyclicKillingSourceObjMap K (f ≫ g) p := by
  -- TODO: once the source map is exposed by a transport-stable `Sigma.ι` formula, this composite
  -- transport comparison should be deleted in favor of a direct coproduct computation.
  sorry

/-- Helper for Lemma 19.12.4: the replacement-side summand transport respects postcomposition
after aligning the composite reindexing with the direct reindexing. -/
private theorem acyclicKillingReplacementObj_eq_smallIndexMap_comp
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P)
    (p : sourceIndexSmall K M) :
    acyclicKillingReplacementObj K P (acyclicKillingSmallIndexMap K g
        (acyclicKillingSmallIndexMap K f p)) =
      acyclicKillingReplacementObj K P
        ((acyclicKillingSmallIndexMap K g ∘ acyclicKillingSmallIndexMap K f) p) := by
  -- The direct and iterated reindexings agree on the represented replacement object.
  simpa [Function.comp] using
    congrArg (fun r : sourceIndexSmall K P ↦ acyclicKillingReplacementObj K P r)
      (congrArg (fun h ↦ h p) (acyclic_killing_small_index_map_comp K f g).symm)

/-- Helper for Lemma 19.12.4: the replacement objects for the composed-index function and the
direct postcomposition index agree. -/
private theorem acyclicKillingReplacementObj_eq_smallIndexMap_direct
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P)
    (p : sourceIndexSmall K M) :
    acyclicKillingReplacementObj K P
        ((acyclicKillingSmallIndexMap K g ∘ acyclicKillingSmallIndexMap K f) p) =
      acyclicKillingReplacementObj K P (acyclicKillingSmallIndexMap K (f ≫ g) p) := by
  simpa using
    congrArg (fun r : sourceIndexSmall K P ↦ acyclicKillingReplacementObj K P r)
      (congrArg (fun h ↦ h p) (acyclic_killing_small_index_map_comp K f g)).symm

/-- Helper for Lemma 19.12.4: the replacement-side summand transport respects postcomposition
after aligning the composite reindexing with the direct reindexing. -/
private theorem acyclicKillingReplacementObjMap_comp
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P)
    (p : sourceIndexSmall K M) :
    acyclicKillingReplacementObjMap K f p ≫
        acyclicKillingReplacementObjMap K g (acyclicKillingSmallIndexMap K f p) ≫
        eqToHom (acyclicKillingReplacementObj_eq_smallIndexMap_comp K f g p) ≫
        eqToHom (acyclicKillingReplacementObj_eq_smallIndexMap_direct K f g p) =
      acyclicKillingReplacementObjMap K (f ≫ g) p := by
  -- TODO: replace this raw replacement-side transport chain by the corresponding
  -- `Sigma.ι`-level formula for `acyclicKillingReplacementMap`.
  sorry

/-- Helper for Lemma 19.12.4: the induced map on the source coproducts. -/
private noncomputable abbrev acyclicKillingSourceMap
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    acyclicKillingSource K M ⟶ acyclicKillingSource K N :=
  Limits.Sigma.map' (acyclicKillingSmallIndexMap K f)
    (acyclicKillingSourceObjMap K f)

/-- Helper for Lemma 19.12.4: the induced map on the replacement coproducts. -/
private noncomputable abbrev acyclicKillingReplacementMap
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    acyclicKillingReplacement K M ⟶ acyclicKillingReplacement K N :=
  Limits.Sigma.map' (acyclicKillingSmallIndexMap K f)
    (acyclicKillingReplacementObjMap K f)

/-- Helper for Lemma 19.12.4: the source coproduct map is the identity on identity morphisms. -/
private theorem acyclic_killing_source_map_id
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    acyclicKillingSourceMap K (𝟙 M) = 𝟙 (acyclicKillingSource K M) := by
  -- Compare the coproduct maps on each source summand.
  apply Limits.Sigma.hom_ext
  intro p
  rw [Limits.Sigma.ι_comp_map']
  -- Route correction: rewrite the shrunken index map to `id` before collapsing the transport.
  simp [acyclicKillingSourceMap, acyclic_killing_small_index_map_id,
    acyclicKillingSourceObjMap, acyclic_killing_source_obj_eq]

/-- Helper for Lemma 19.12.4: the replacement coproduct map is the identity on identity
morphisms. -/
private theorem acyclic_killing_replacement_map_id
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    acyclicKillingReplacementMap K (𝟙 M) = 𝟙 (acyclicKillingReplacement K M) := by
  -- Compare the coproduct maps on each replacement summand.
  apply Limits.Sigma.hom_ext
  intro p
  rw [Limits.Sigma.ι_comp_map']
  -- Route correction: rewrite the shrunken index map to `id` before collapsing the transport.
  simp [acyclicKillingReplacementMap, acyclic_killing_small_index_map_id,
    acyclicKillingReplacementObjMap, acyclic_killing_replacement_obj_eq]

/-- Helper for Lemma 19.12.4: the source coproduct map respects composition. -/
private theorem acyclic_killing_source_map_comp
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P) :
    acyclicKillingSourceMap K (f ≫ g) =
      acyclicKillingSourceMap K f ≫ acyclicKillingSourceMap K g := by
  -- TODO: once the source-side component transport comparison is restored, re-run the
  -- `Sigma.map'_comp_map'` argument to obtain functoriality on the source coproduct.
  sorry

/-- Helper for Lemma 19.12.4: the replacement coproduct map respects composition. -/
private theorem acyclic_killing_replacement_map_comp
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P) :
    acyclicKillingReplacementMap K (f ≫ g) =
      acyclicKillingReplacementMap K f ≫ acyclicKillingReplacementMap K g := by
  -- TODO: repeat the same coproduct-composition argument on the replacement family after the
  -- replacement-side transport comparison is restored.
  sorry

/-- Helper for Lemma 19.12.4: the left coproduct map is natural in the target complex. -/
private theorem acyclicKillingLeftMap_natural
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    acyclicKillingLeftMap K M ≫ acyclicKillingReplacementMap K f =
      acyclicKillingSourceMap K f ≫ acyclicKillingLeftMap K N := by
  -- TODO: after restoring the component formula on each summand, rebuild this coproduct-level
  -- naturality square by `Sigma.map_comp_map'` and `Sigma.map'_comp_map`.
  sorry

/-- Helper for Lemma 19.12.4: the upper coproduct map is natural in the target complex. -/
private theorem acyclicKillingTopMap_natural
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    acyclicKillingTopMap K M ≫ f =
      acyclicKillingSourceMap K f ≫ acyclicKillingTopMap K N := by
  -- TODO: compare both sides on each coproduct inclusion after the source-side component
  -- transport has been normalized.
  sorry

/-- Helper for Lemma 19.12.4: the source pushout object attached to `M`. -/
private noncomputable abbrev acyclicKillingStepObj
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :=
  pushout (acyclicKillingLeftMap K M) (acyclicKillingTopMap K M)

/-- Helper for Lemma 19.12.4: the induced map between the source pushout objects. -/
private noncomputable abbrev acyclicKillingStepMap
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    acyclicKillingStepObj K M ⟶ acyclicKillingStepObj K N :=
  pushout.map
    (acyclicKillingLeftMap K M) (acyclicKillingTopMap K M)
    (acyclicKillingLeftMap K N) (acyclicKillingTopMap K N)
    (acyclicKillingReplacementMap K f) f (acyclicKillingSourceMap K f)
    (acyclicKillingLeftMap_natural K f) (acyclicKillingTopMap_natural K f)

/-- Helper for Lemma 19.12.4: the induced pushout map is the identity for `𝟙_M`. -/
private theorem acyclicKillingStepMap_id
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    acyclicKillingStepMap K (𝟙 M) = 𝟙 (acyclicKillingStepObj K M) := by
  -- Once the three side maps are identities, `pushout.map` is the identity on the pushout.
  simpa [acyclicKillingStepMap, acyclic_killing_source_map_id,
    acyclic_killing_replacement_map_id] using
    (pushout.map_id (f := acyclicKillingLeftMap K M) (g := acyclicKillingTopMap K M))

/-- Helper for Lemma 19.12.4: the induced pushout map respects composition. -/
private theorem acyclicKillingStepMap_comp
    (K : I → CochainComplex C ℤ)
    {M N P : CochainComplex C ℤ} (f : M ⟶ N) (g : N ⟶ P) :
    acyclicKillingStepMap K (f ≫ g) =
      acyclicKillingStepMap K f ≫ acyclicKillingStepMap K g := by
  -- The comparison maps between the pushouts compose as soon as the span maps do.
  simpa [acyclicKillingStepMap, acyclic_killing_source_map_comp,
    acyclic_killing_replacement_map_comp] using
    (pushout.map_comp
      (i₁ := acyclicKillingSourceMap K f)
      (j₁ := acyclicKillingSourceMap K g)
      (i₂ := acyclicKillingReplacementMap K f)
      (j₂ := acyclicKillingReplacementMap K g)
      (i₃ := f)
      (j₃ := g)
      (e₁ := acyclicKillingLeftMap_natural K f)
      (e₂ := acyclicKillingTopMap_natural K f)
      (e₃ := acyclicKillingLeftMap_natural K g)
      (e₄ := acyclicKillingTopMap_natural K g)).symm

/-- Helper for Lemma 19.12.4: the Stacks pushout construction on cochain complexes. -/
private noncomputable def acyclicKillingStepFunctor
    (K : I → CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj M := acyclicKillingStepObj K M
  map := acyclicKillingStepMap K
  map_id := acyclicKillingStepMap_id K
  map_comp := acyclicKillingStepMap_comp K

/-- Helper for Lemma 19.12.4: the right pushout legs are natural in the target complex. -/
private theorem acyclicKillingInclusion_naturality
    (K : I → CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N) :
    f ≫ pushout.inr (acyclicKillingLeftMap K N) (acyclicKillingTopMap K N) =
      pushout.inr (acyclicKillingLeftMap K M) (acyclicKillingTopMap K M) ≫
        acyclicKillingStepMap K f := by
  -- This is the `inr` computation of the defining `pushout.map`.
  symm
  rw [acyclicKillingStepMap, pushout.inr_desc]

/-- Helper for Lemma 19.12.4: the canonical comparison maps for the Stacks pushout construction.

The components are the right pushout legs of the coproduct square over all maps `K i ⟶ M`. -/
private noncomputable def acyclicKillingInclusion
    (K : I → CochainComplex C ℤ) :
    𝟭 (CochainComplex C ℤ) ⟶ acyclicKillingStepFunctor K where
  app M := pushout.inr (acyclicKillingLeftMap K M) (acyclicKillingTopMap K M)
  naturality := fun {_ _} f ↦ acyclicKillingInclusion_naturality K f

/-- Helper for Lemma 19.12.4: the left coproduct map is mono because it is the coproduct of the
termwise mono cone inclusions. -/
private theorem acyclic_killing_left_map_mono
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    Mono (acyclicKillingLeftMap K M) := by
  -- TODO: prove this degreewise after evaluation, using a transport-stable coproduct mono API for
  -- the family `fun p ↦ (coneReplacementMap K (sourceIndexPair K M p).1).f n`.
  sorry

/-- Helper for Lemma 19.12.4: the canonical inclusions into the pushouts are monomorphisms.

The source proof reduces this to the left pushout leg, and in an abelian category pushouts of
monomorphisms are monomorphisms. -/
private theorem acyclicKillingInclusion_mono
    (K : I → CochainComplex C ℤ) :
    Mono (acyclicKillingInclusion K) := by
  -- In an abelian category, pushouts of monomorphisms are monomorphisms. Apply this objectwise
  -- to the canonical pushout square defining the approximation.
  refine (NatTrans.mono_iff_mono_app _).2 ?_
  intro M
  letI : Mono (acyclicKillingLeftMap K M) := acyclic_killing_left_map_mono K M
  change Mono (pushout.inr (acyclicKillingLeftMap K M) (acyclicKillingTopMap K M))
  exact Abelian.mono_inr_of_isColimit (f := acyclicKillingLeftMap K M)
    (g := acyclicKillingTopMap K M) (pushout.isColimit _ _)

/-- Helper for Lemma 19.12.4: the cone of a quasi-isomorphism is acyclic. -/
private theorem mappingCone_acyclic_of_quasiIso
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (hf : QuasiIso f) :
    (CochainComplex.mappingCone f).Acyclic := by
  -- Pass to the homotopy category, where the standard mapping-cone triangle detects
  -- quasi-isomorphisms through the acyclic subcategory.
  have hq :
      HomotopyCategory.quasiIso C (ComplexShape.up ℤ) ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff (C := C) (c := ComplexShape.up ℤ) f).2 hf
  have hq' :
      (HomotopyCategory.subcategoryAcyclic C).trW
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) := by
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := C)] using hq
  have hmem :
      HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone f)) := by
    -- The mapping-cone triangle packages the cone as the `trW` witness of `f`.
    simpa using
      ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 hq'
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (C := C) (CochainComplex.mappingCone f)).1 hmem

/-- Helper for Lemma 19.12.4: an acyclic mapping cone forces the original map to be a
quasi-isomorphism. -/
private theorem quasiIso_of_mappingCone_acyclic
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (hCone : (CochainComplex.mappingCone f).Acyclic) :
    QuasiIso f := by
  -- The converse cone criterion uses the same distinguished triangle in the homotopy category.
  have hmem :
      HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone f)) :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (C := C) (CochainComplex.mappingCone f)).2 hCone
  have hq :
      HomotopyCategory.quasiIso C (ComplexShape.up ℤ) ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) := by
    -- The acyclic cone is exactly the distinguished-triangle criterion for `f`.
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := C)] using
      ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).2 hmem
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff (C := C) (c := ComplexShape.up ℤ) f).1 hq

/-- Helper for Lemma 19.12.4: a coproduct of short-complex homology objects computes the homology
of the coproduct complex when the ambient coproduct is exact. -/
private noncomputable abbrev shortComplexCoproductHomologyIso
    {α : Type w} [HasCoproductsOfShape α C] [HasExactColimitsOfShape (Discrete α) C]
    (p : ℤ) (F : α → CochainComplex C ℤ) :
    ((ShortComplex.homologyFunctor C).obj
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) p).obj (∐ F))) ≅
      ∐ fun i ↦ ((F i).sc p).homology := by
  -- TODO: port the Chapter 13 exact-coproduct homology comparison with the additional local
  -- preservation instance needed for `shortComplexFunctor`.
  sorry

/-- Helper for Lemma 19.12.4: exact coproducts preserve acyclicity of cochain complexes. -/
private theorem coproductAcyclicOfAcyclic
    {α : Type w} [HasCoproductsOfShape α C] [HasExactColimitsOfShape (Discrete α) C]
    (F : α → CochainComplex C ℤ) (hF : ∀ i, (F i).Acyclic) :
    (∐ F).Acyclic := by
  -- TODO: after `shortComplexCoproductHomologyIso` is restored, rewrite each homology object of
  -- `∐ F` as a coproduct of zero objects coming from the acyclic summands.
  sorry

/-- Helper for Lemma 19.12.4: the cone on the identity is contractible, hence acyclic. -/
private theorem mappingCone_id_acyclic
    (X : CochainComplex C ℤ) :
    (CochainComplex.mappingCone (𝟙 X)).Acyclic := by
  -- The mapping cone of the identity is null-homotopic already in the homotopy category.
  have hzeroQ :
      IsZero ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCone (𝟙 X))) := by
    rw [HomotopyCategory.isZero_quotient_obj_iff]
    exact ⟨CochainComplex.mappingCone.homotopyToZeroOfId X⟩
  have hmem :
      HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone (𝟙 X))) := by
    rw [HomotopyCategory.mem_subcategoryAcyclic_iff]
    intro n
    exact Functor.map_isZero (HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n) hzeroQ
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (C := C) (CochainComplex.mappingCone (𝟙 X))).1 hmem

/-- Helper for Lemma 19.12.4: a map between acyclic complexes is automatically a
quasi-isomorphism. -/
private theorem quasiIso_of_acyclic_source_target
    {L M : CochainComplex C ℤ} (f : L ⟶ M)
    (hL : L.Acyclic) (hM : M.Acyclic) :
    QuasiIso f := by
  -- Every homology map lands between zero objects, so it is an isomorphism degreewise.
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hLZero : IsZero (L.homology n) := by
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := L) (i := n)).1
      ((HomologicalComplex.acyclic_iff L).1 hL n)
  have hMZero : IsZero (M.homology n) := by
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := M) (i := n)).1
      ((HomologicalComplex.acyclic_iff M).1 hM n)
  exact CategoryTheory.Limits.isIso_of_source_target_iso_zero
    ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map f)
    hLZero.isoZero hMZero.isoZero

/-- Helper for Lemma 19.12.4: a quasi-isomorphism out of an acyclic complex has acyclic target. -/
private theorem acyclic_of_quasiIso_of_acyclic_source
    {L M : CochainComplex C ℤ} (f : L ⟶ M)
    (hf : QuasiIso f) (hL : L.Acyclic) :
    M.Acyclic := by
  -- Transport zero homology across the degreewise homology isomorphisms of the quasi-isomorphism.
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hLZero : IsZero (L.homology n) := by
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := L) (i := n)).1
      ((HomologicalComplex.acyclic_iff L).1 hL n)
  have hIso :
      IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map f) := by
    exact (quasiIsoAt_iff_isIso_homologyMap (f := f) (i := n)).1
      ((quasiIso_iff f).1 hf n)
  exact (CategoryTheory.Iso.isZero_iff
    (asIso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map f))).1 hLZero

/-- Helper for Lemma 19.12.4: a quasi-isomorphism into an acyclic complex has acyclic source. -/
private theorem acyclic_of_quasiIso_of_acyclic_target
    {L M : CochainComplex C ℤ} (f : L ⟶ M)
    (hf : QuasiIso f) (hM : M.Acyclic) :
    L.Acyclic := by
  -- The same transport works after reading the homology isomorphisms in the opposite direction.
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hMZero : IsZero (M.homology n) := by
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := M) (i := n)).1
      ((HomologicalComplex.acyclic_iff M).1 hM n)
  have hIso :
      IsIso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map f) := by
    exact (quasiIsoAt_iff_isIso_homologyMap (f := f) (i := n)).1
      ((quasiIso_iff f).1 hf n)
  exact (CategoryTheory.Iso.isZero_iff
    (asIso ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map f))).2 hMZero

/-- Helper for Lemma 19.12.4: a monomorphic quasi-isomorphism has acyclic cokernel. -/
private theorem acyclicCokernel_of_mono_quasiIso
    {L M : CochainComplex C ℤ} (f : L ⟶ M) [Mono f] (hf : QuasiIso f) :
    (cokernel f).Acyclic := by
  -- Evaluation preserves monomorphisms, so the Chapter 13 owner theorem applies degreewise.
  have hmono : ∀ n : ℤ, Mono (f.f n) := by
    intro n
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map f)
    infer_instance
  exact cokernel_acyclic_of_termwiseMono_quasiIso (α := f) hmono

/-- Helper for Lemma 19.12.4: a monomorphism with acyclic cokernel is a quasi-isomorphism. -/
private theorem quasiIsoOfMonoOfAcyclicCokernel
    {L M : CochainComplex C ℤ} (f : L ⟶ M) [Mono f]
    (hCoker : (cokernel f).Acyclic) :
    QuasiIso f := by
  -- TODO: repackage `ShortComplex.cokernelSequence f` with an explicit mono witness on its first
  -- map, then descend the mapping-cone quasi-isomorphism to the acyclic cokernel.
  sorry

/-- Helper for Lemma 19.12.4: the source coproduct is acyclic because it is a coproduct of the
acyclic complexes `K i`. -/
private theorem acyclicKillingSource_acyclic
    (K : I → CochainComplex C ℤ) (hK : ∀ i : I, (K i).Acyclic)
    (M : CochainComplex C ℤ) :
    (acyclicKillingSource K M).Acyclic := by
  -- Each summand is one of the chosen acyclic complexes, and exact coproducts preserve this.
  exact coproductAcyclicOfAcyclic
    (fun p : sourceIndexSmall K M ↦ acyclicKillingSourceObj K M p)
    (fun p ↦ hK (sourceIndexPair K M p).1)

/-- Helper for Lemma 19.12.4: the replacement coproduct is acyclic because each cone on an
identity map is contractible. -/
private theorem acyclicKillingReplacement_acyclic
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    (acyclicKillingReplacement K M).Acyclic := by
  -- The replacement summands are cones on identities, hence individually acyclic.
  exact coproductAcyclicOfAcyclic
    (fun p : sourceIndexSmall K M ↦ acyclicKillingReplacementObj K M p)
    (fun p ↦ mappingCone_id_acyclic (C := C) (K (sourceIndexPair K M p).1))

/-- Helper for Lemma 19.12.4: the left coproduct map is a quasi-isomorphism because both its
source and target are acyclic. -/
private theorem acyclicKillingLeftMap_quasiIso
    (K : I → CochainComplex C ℤ) (hK : ∀ i : I, (K i).Acyclic)
    (M : CochainComplex C ℤ) :
    QuasiIso (acyclicKillingLeftMap K M) := by
  -- After the exact-coproduct step, the source and replacement sides are both acyclic.
  exact quasiIso_of_acyclic_source_target
    (acyclicKillingLeftMap K M)
    (acyclicKillingSource_acyclic (C := C) K hK M)
    (acyclicKillingReplacement_acyclic (C := C) K M)

/-- Helper for Lemma 19.12.4: the pushout comparison identifies the quotient of the right
inclusion with the quotient of the left coproduct map. -/
private noncomputable def acyclicKillingInclusionCokernelIso
    (K : I → CochainComplex C ℤ) (M : CochainComplex C ℤ) :
    cokernel ((acyclicKillingInclusion K).app M) ≅ cokernel (acyclicKillingLeftMap K M) :=
  sorry

/-- Helper for Lemma 19.12.4: each canonical inclusion into the pushout is a quasi-isomorphism. -/
private theorem acyclicKillingInclusion_quasiIso
    [IsGrothendieckAbelian.{w} C]
    (K : I → CochainComplex C ℤ) (hK : ∀ i : I, (K i).Acyclic)
    (M : CochainComplex C ℤ) :
    QuasiIso ((acyclicKillingInclusion K).app M) := by
  -- TODO: finish the pushout acyclic-cokernel argument once the quotient comparison is repaired.
  sorry

/-- Helper for Lemma 19.12.4: every chosen map `w : K i ⟶ M` becomes null-homotopic after the
canonical pushout inclusion. -/
private theorem acyclicKillingComponent_homotopy
    (K : I → CochainComplex C ℤ) (i : I) (M : CochainComplex C ℤ) (w : K i ⟶ M) :
    Nonempty (Homotopy (w ≫ (acyclicKillingInclusion K).app M) 0) := by
  -- TODO: normalize the distinguished summand of the pushout relation and then postcompose the
  -- standard null-homotopy of `coneReplacementMap K i`.
  sorry

end AcyclicKillingData

-- Proof sketch: for each acyclic `K i`, choose a termwise monomorphism `K i ⟶ L i` that is
-- homotopic to zero and whose target is quasi-isomorphic to zero, for instance the cone on the
-- identity. Form the pushout over the coproduct of all maps `K i ⟶ M`; this yields a functorial
-- monomorphism of cochain complexes `j_M : M ⟶ \mathbf M(M)`, hence a degreewise monomorphism,
-- with acyclic cokernel, hence a
-- quasi-isomorphism, and the universal property of the pushout makes every composite
-- `K i ⟶ M ⟶ \mathbf M(M)` homotopic to zero.
/-- Lemma 19.12.4: for a Grothendieck abelian category and a family of acyclic cochain complexes
`(K_i^\bullet)`, there exists a functorial degreewise monomorphic quasi-isomorphic enlargement
`j_{M^\bullet} : M^\bullet \to \mathbf M^\bullet(M^\bullet)` such that for every `i` and every
map `w : K_i^\bullet \to M^\bullet`, the composite `j_{M^\bullet} \circ w` is homotopic to zero. -/
@[stacks 079M]
theorem exists_acyclic_killing_resolution_functor [IsGrothendieckAbelian.{w} C]
    (K : I → CochainComplex C ℤ) (hK : ∀ i : I, (K i).Acyclic) :
    ∃ J : FunctorialComplexApproximation C,
      ∀ (i : I) (M : CochainComplex C ℤ) (w : K i ⟶ M),
        Nonempty (Homotopy (w ≫ J.ι.app M) 0) := by
  classical
  -- Route correction: follow the source proof verbatim by replacing each `K i` with the cone on
  -- its identity and then taking the pushout over the coproduct of all maps into `M`.
  let J : FunctorialComplexApproximation C :=
    { toFunctor := acyclicKillingStepFunctor K
      ι := acyclicKillingInclusion K
      mono_ι := acyclicKillingInclusion_mono K
      quasiIso_app := acyclicKillingInclusion_quasiIso K hK }
  refine ⟨J, ?_⟩
  intro i M w
  simpa using acyclicKillingComponent_homotopy K i M w

end

end CochainComplex
