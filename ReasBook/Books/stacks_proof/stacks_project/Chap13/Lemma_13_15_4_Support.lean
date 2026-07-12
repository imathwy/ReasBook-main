import Mathlib
import StacksProject_2024.Chap12.Definition_12_5_3
import StacksProject_2024.Chap12.Lemma_12_5_12
import StacksProject_2024.Chap12.Lemma_12_5_13
import StacksProject_2024.Chap13.Definition_13_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open HomologicalComplex ComplexShape
open scoped ZeroObject

universe v u

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 13.15.4:
- primary domain: bounded-above replacements of cochain complexes by complexes whose terms lie in
  an object property, together with quasi-isomorphisms and degreewise epimorphy;
- sampled owner declarations in this domain:
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.ι`,
  `CochainComplex.Minus`,
  `CochainComplex.Minus.ι`,
  `CochainComplex.minus`,
  `QuasiIso`,
  `ObjectProperty.HasEpiCover`;
- best owner abstraction:
  `CochainComplex.MinusWithTermsIn P` should be the full subcategory of the canonical bounded-above
  owner `CochainComplex.Minus A` cut out by the termwise `P`-condition, with owner inclusion
  `ObjectProperty.ι _ : MinusWithTermsIn P ⥤ Minus A`; the two predicates below are the
  source-facing layer adding the comparison morphism and its quasi-isomorphism / epimorphism
  properties, while the owner conversion `toMinusWithTermsIn` remains a bridge;
- primitive-vs-derived split:
  primitive data are the comparison morphism `α : Q ⟶ K` together with the three source-faithful
  properties `QuasiIso α`, `Q.IsStrictlyLE a`, and the termwise predicate
  `term_mem (n : ℤ) : P (Q.X n)`;
  the termwise-epimorphic variant adds the source-facing degreewise epimorphism predicate
  `term_epi (n : ℤ) : Epi (α.f n)`, while any complex-level `Epi α` fact is derived API from the
  canonical owner lemma `HomologicalComplex.epi_of_epi_f`.

Source/core/bridge triage:
- `source-facing`: `IsStrictlyLEQuasiIsoWithTermsIn` and
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- `core/canonical`: `CochainComplex.MinusWithTermsIn P`, `QuasiIso`, `ObjectProperty.HasEpiCover`,
  and the componentwise `Epi` predicate;
- `bridge/view`: the owner inclusion `ObjectProperty.ι _ : MinusWithTermsIn P ⥤ Minus A` and its
  composite with `CochainComplex.Minus.ι A`,
  `IsStrictlyLEQuasiIsoWithTermsIn.toMinusWithTermsIn`, and the existence theorems below, which
  package a source-level bounded-above replacement into these owner predicates.
-/

namespace CochainComplex

section

variable [HasZeroMorphisms A]

/-- The bounded-above cochain complexes whose terms satisfy the object property `P`. -/
abbrev MinusWithTermsIn (P : ObjectProperty A) :=
  ObjectProperty.FullSubcategory fun K : Minus A ↦
    ∀ n : ℤ, P (K.obj.X n)

namespace MinusWithTermsIn

instance (P : ObjectProperty A) : CoeOut (MinusWithTermsIn P) (Minus A) where
  coe K := K.obj

instance (P : ObjectProperty A) :
    CoeOut (MinusWithTermsIn P) (CochainComplex A ℤ) where
  coe K := K.obj.obj

/-- The inclusion of bounded-above cochain complexes with terms in `P` into all cochain
complexes. -/
abbrev ι (P : ObjectProperty A) : MinusWithTermsIn P ⥤ CochainComplex A ℤ :=
  ObjectProperty.ι _ ⋙ CochainComplex.Minus.ι A

/-- A bounded-above cochain complex with terms in `P` is bounded above. -/
theorem minus {P : ObjectProperty A} (K : MinusWithTermsIn P) :
    CochainComplex.minus A (K : CochainComplex A ℤ) := by
  simpa using (K : Minus A).property

/-- Each term of a bounded-above cochain complex with terms in `P` again satisfies `P`. -/
theorem term_mem {P : ObjectProperty A} (K : MinusWithTermsIn P) (n : ℤ) :
    P ((K : CochainComplex A ℤ).X n) := by
  simpa using K.property n

/-- A bounded-above cochain complex with terms in `P` is zero in all sufficiently high degrees. -/
theorem exists_isStrictlyLE {P : ObjectProperty A} (K : MinusWithTermsIn P) :
    ∃ b : ℤ, (K : CochainComplex A ℤ).IsStrictlyLE b :=
  (CochainComplex.minus_iff A (K : CochainComplex A ℤ)).1 K.minus

end MinusWithTermsIn

end

end CochainComplex

section

variable [HasZeroMorphisms A] [CategoryWithHomology A]

/-- A morphism `α : Q ⟶ K` exhibits `Q` as a bounded-above cochain complex whose terms satisfy
the object property `P` and which is quasi-isomorphic to `K`. -/
structure IsStrictlyLEQuasiIsoWithTermsIn
    (P : ObjectProperty A) (a : ℤ) (K Q : CochainComplex A ℤ) (α : Q ⟶ K) : Prop where
  quasiIso : QuasiIso α
  strictlyLE : Q.IsStrictlyLE a
  term_mem (n : ℤ) : P (Q.X n)

namespace IsStrictlyLEQuasiIsoWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K Q : CochainComplex A ℤ} {α : Q ⟶ K}

/-- The source-facing bounded-above replacement data canonically packages its resolving complex as
an element of the owner `CochainComplex.MinusWithTermsIn P`. -/
abbrev toMinusWithTermsIn (h : IsStrictlyLEQuasiIsoWithTermsIn P a K Q α) :
    CochainComplex.MinusWithTermsIn P :=
  ⟨⟨Q, (CochainComplex.minus_iff A Q).2 ⟨a, h.strictlyLE⟩⟩, h.term_mem⟩

end IsStrictlyLEQuasiIsoWithTermsIn

/-- A morphism `α : Q ⟶ K` exhibits `Q` as a bounded-above cochain complex with terms in `P`
which is quasi-isomorphic to `K` and termwise epimorphic. -/
structure IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn
    (P : ObjectProperty A) (a : ℤ) (K Q : CochainComplex A ℤ) (α : Q ⟶ K) : Prop extends
    IsStrictlyLEQuasiIsoWithTermsIn P a K Q α where
  term_epi (n : ℤ) : Epi (α.f n)

namespace IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn

variable {P : ObjectProperty A} {a : ℤ} {K Q : CochainComplex A ℤ} {α : Q ⟶ K}

/-- A termwise-epimorphic morphism of cochain complexes is epimorphic as a morphism of
complexes. -/
theorem epi (h : IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α) : Epi α :=
  epi_of_epi_f α h.term_epi

/-- The termwise-epimorphic bounded-above replacement data packages its resolving complex as an
element of the owner `CochainComplex.MinusWithTermsIn P`. -/
abbrev toMinusWithTermsIn (h : IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α) :
    CochainComplex.MinusWithTermsIn P :=
  h.toIsStrictlyLEQuasiIsoWithTermsIn.toMinusWithTermsIn

end IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn

end

section

variable [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.HasEpiCover]

/-- Helper for Lemma 13.15.4: choose a zero object lying in `P`. -/
private noncomputable abbrev property_zero_object : A :=
  P.exists_prop_of_containsZero.choose

/-- Helper for Lemma 13.15.4: the chosen `P`-zero object is zero. -/
private theorem property_zero_object_isZero :
    IsZero (property_zero_object (P := P)) :=
  P.exists_prop_of_containsZero.choose_spec.1

/-- Helper for Lemma 13.15.4: the chosen `P`-zero object satisfies `P`. -/
private theorem property_zero_object_mem :
    P (property_zero_object (P := P)) :=
  P.exists_prop_of_containsZero.choose_spec.2

/-- Helper for Lemma 13.15.4: the descending induction starts from the cochain complex whose every
term is the chosen zero object in `P`. -/
private noncomputable def property_zero_complex : CochainComplex A ℤ where
  X := fun _ ↦ property_zero_object (P := P)
  d := fun _ _ ↦ 0
  shape := by
    intro i j hij
    simp
  d_comp_d' := by
    intro i j k hij hjk
    simp

/-- Helper for Lemma 13.15.4: the chosen `P`-zero complex is itself a zero object in the category
of cochain complexes. -/
private theorem isZero_property_zero_complex :
    IsZero (property_zero_complex (P := P)) := by
  let Z := property_zero_object (P := P)
  let _ : IsZero Z := property_zero_object_isZero (P := P)
  refine ⟨?_, ?_⟩
  · intro X
    refine ⟨⟨⟨0⟩, ?_⟩⟩
    intro f
    ext i
    exact (property_zero_object_isZero (P := P)).eq_of_src _ _
  · intro X
    refine ⟨⟨⟨0⟩, ?_⟩⟩
    intro f
    ext i
    exact (property_zero_object_isZero (P := P)).eq_of_tgt _ _

/-- Helper for Lemma 13.15.4: vanishing homology above `a` makes the complex exact above `a`. -/
private theorem isLE_of_isZero_homology_above
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    K.IsLE a := by
  -- Rewrite the upper-exactness predicate degreewise in terms of homology.
  rw [CochainComplex.isLE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hK n hn

/-- Helper for Lemma 13.15.4: the upper truncation map is a quasi-isomorphism under homology
vanishing above `a`. -/
private theorem quasiIso_ιTruncLE_of_isZero_homology_above
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    QuasiIso (K.ιTruncLE a) := by
  -- Once `K` is exact above `a`, the canonical truncation map is a quasi-isomorphism.
  letI : K.IsLE a := isLE_of_isZero_homology_above (a := a) (K := K) hK
  infer_instance

/-- Helper for Lemma 13.15.4: every term of the chosen `P`-zero complex lies in `P`. -/
private theorem property_zero_complex_term_mem
    (n : ℤ) :
    P ((property_zero_complex (P := P)).X n) := by
  -- Each term is definitionally the chosen zero object that already lies in `P`.
  simpa [property_zero_complex] using property_zero_object_mem (P := P)

/-- Helper for Lemma 13.15.4: above the cutoff, the chosen `P`-zero-complex comparison map is
termwise epimorphic because the target term is already zero. -/
private theorem property_zero_complex_term_epi_of_isStrictlyLE
    (a n : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) (hn : a < n) :
    Epi ((0 : (property_zero_complex (P := P)).X n ⟶ K.X n)) := by
  -- Above `a`, the target term vanishes, so the zero map is automatically epimorphic.
  let hzero : IsZero (K.X n) := K.isZero_of_isStrictlyLE a n hn
  exact hzero.epi _

/-- Helper for Lemma 13.15.4: above the cutoff, the chosen `P`-zero-complex comparison map
induces an isomorphism on homology because both source and target homology objects vanish. -/
private theorem property_zero_complex_homologyMap_isIso_of_isStrictlyLE
    (a n : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) (hn : a < n) :
    IsIso (HomologicalComplex.homologyMap (0 : property_zero_complex (P := P) ⟶ K) n) := by
  let f0 : property_zero_complex (P := P) ⟶ K := 0
  have hsource :
      IsZero ((property_zero_complex (P := P)).homology n) := by
    -- The chosen `P`-zero complex has zero homology because the entire complex is zero.
    exact (HomologicalComplex.homologyFunctor A (up ℤ) n).map_isZero
      (isZero_property_zero_complex (P := P))
  letI : K.IsStrictlyLE a := hK
  have htarget : IsZero (K.homology n) := K.isZero_of_isLE a n hn
  -- A morphism between zero objects is invertible with zero inverse.
  refine ⟨⟨0, ?_, ?_⟩⟩
  · simpa [f0] using (hsource.eq_of_src (𝟙 ((property_zero_complex (P := P)).homology n)) 0).symm
  · simpa [f0] using (htarget.eq_of_src (𝟙 (K.homology n)) 0).symm

/-- Helper for Lemma 13.15.4: above the cutoff, the chosen `P`-zero-complex comparison induces an
epimorphism on cycles because the target cycles object is zero. -/
private theorem property_zero_complex_cycles_epi_of_isStrictlyLE
    (a n : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) (hn : a < n) :
    Epi (kernel.map ((property_zero_complex (P := P)).d n (n + 1)) (K.d n (n + 1))
      (0 : (property_zero_complex (P := P)).X n ⟶ K.X n)
      (0 : (property_zero_complex (P := P)).X (n + 1) ⟶ K.X (n + 1))
      ((0 : property_zero_complex (P := P) ⟶ K).comm n (n + 1)).symm) := by
  let f0 : property_zero_complex (P := P) ⟶ K := 0
  let g0 :
      kernel ((property_zero_complex (P := P)).d n (n + 1)) ⟶ kernel (K.d n (n + 1)) :=
    kernel.map ((property_zero_complex (P := P)).d n (n + 1)) (K.d n (n + 1))
      (f0.f n) (f0.f (n + 1)) ((f0.comm n (n + 1)).symm)
  have hsource : IsZero (K.X n) := K.isZero_of_isStrictlyLE a n hn
  have hcycles : IsZero (kernel (K.d n (n + 1))) := by
    -- The cycles object is a subobject of the already vanishing source term `K.X n`.
    exact Limits.IsZero.of_mono (kernel.ι (K.d n (n + 1))) hsource
  have hEpi : Epi g0 := hcycles.epi _
  change Epi g0
  exact hEpi

/-- Helper for Lemma 13.15.4: the source induction hypothesis `IH_n` packaged as a full cochain
complex with zero tail below `n`, terms in `P` on and above `n`, and the comparison data to `K`.
-/
private structure BoundedAboveReplacementStage
    (a : ℤ) (K : CochainComplex A ℤ) (n : ℤ) where
  Q : CochainComplex A ℤ
  α : Q ⟶ K
  strictlyLE : Q.IsStrictlyLE a
  zero_below : ∀ i : ℤ, i < n → IsZero (Q.X i)
  term_mem : ∀ i : ℤ, n ≤ i → P (Q.X i)
  term_epi : ∀ i : ℤ, n ≤ i → Epi (α.f i)
  homologyMap_isIso : ∀ i : ℤ, n < i → IsIso (HomologicalComplex.homologyMap α i)
  cycles_epi :
    Epi (kernel.map (Q.d n (n + 1)) (K.d n (n + 1)) (α.f n) (α.f (n + 1))
      ((α.comm n (n + 1)).symm))

namespace BoundedAboveReplacementStage

variable {P} {a : ℤ} {K : CochainComplex A ℤ} {n : ℤ}

/-- Helper for Lemma 13.15.4: the comparison morphism on cycles in the cutoff degree of a stage.
-/
private noncomputable abbrev cyclesMap
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    kernel (S.Q.d n (n + 1)) ⟶ kernel (K.d n (n + 1)) :=
  kernel.map (S.Q.d n (n + 1)) (K.d n (n + 1)) (S.α.f n) (S.α.f (n + 1))
    ((S.α.comm n (n + 1)).symm)

/-- Helper for Lemma 13.15.4: the map `K.X (n - 1) ⟶ Z^n(K)` used in the source pullback square.
-/
private noncomputable abbrev previousToCycles :
    K.X (n - 1) ⟶ kernel (K.d n (n + 1)) :=
  kernel.lift (K.d n (n + 1)) (K.d (n - 1) n) (by
    -- The source route enters the pullback through the cycle object `Z^n(K)`.
    simpa using K.d_comp_d (n - 1) n (n + 1))

/-- Helper for Lemma 13.15.4: the pullback
`K.X (n - 1) ×_{Z^n(K)} Z^n(Q)` from the source induction step. -/
private noncomputable abbrev extensionPullback
    (S : BoundedAboveReplacementStage (P := P) a K n) : A :=
  pullback previousToCycles (cyclesMap (S := S))

/-- Helper for Lemma 13.15.4: choose the `P`-object covering the source pullback in the step
`IH_n -> IH_(n - 1)`. -/
private noncomputable abbrev extensionCoverObject
    (S : BoundedAboveReplacementStage (P := P) a K n) : A :=
  ((inferInstance : P.HasEpiCover).exists_epi (extensionPullback (S := S))).choose

/-- Helper for Lemma 13.15.4: the chosen cover object for the source pullback again lies in `P`.
-/
private theorem extensionCover_mem
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    P (extensionCoverObject (S := S)) :=
  ((inferInstance : P.HasEpiCover).exists_epi (extensionPullback (S := S))).choose_spec.1

/-- Helper for Lemma 13.15.4: the chosen epimorphism from the `P`-cover onto the source pullback.
-/
private noncomputable abbrev extensionCoverMap
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extensionCoverObject (S := S) ⟶ extensionPullback (S := S) :=
  ((inferInstance : P.HasEpiCover).exists_epi (extensionPullback (S := S))).choose_spec.2.choose

/-- Helper for Lemma 13.15.4: the chosen map onto the source pullback is epimorphic. -/
private theorem extensionCover_epi
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    Epi (extensionCoverMap (S := S)) :=
  ((inferInstance : P.HasEpiCover).exists_epi (extensionPullback (S := S))).choose_spec.2.choose_spec

/-- Helper for Lemma 13.15.4: the first pullback projection gives the new comparison component
`Q^{n-1} ⟶ K^{n-1}` in the source extension step. -/
private noncomputable abbrev extensionCoverToPrevious
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extensionCoverObject (S := S) ⟶ K.X (n - 1) :=
  extensionCoverMap (S := S) ≫ pullback.fst previousToCycles (cyclesMap (S := S))

/-- Helper for Lemma 13.15.4: the second pullback projection gives the new cycle-valued
differential component into `Q^n`. -/
private noncomputable abbrev extensionCoverToStageCycles
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extensionCoverObject (S := S) ⟶ kernel (S.Q.d n (n + 1)) :=
  extensionCoverMap (S := S) ≫ pullback.snd previousToCycles (cyclesMap (S := S))

/-- Helper for Lemma 13.15.4: the new comparison component is epi because it is the composite of
the chosen pullback cover with the pullback projection along the epi cycles map. -/
private theorem extensionCoverToPrevious_epi
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    Epi (extensionCoverToPrevious (S := S)) := by
  -- The source proof uses the pullback of the epi cycles map, so the first projection remains epi.
  letI : Epi (cyclesMap (S := S)) := S.cycles_epi
  letI : Epi (extensionCoverMap (S := S)) := extensionCover_epi (S := S)
  infer_instance

/-- Helper for Lemma 13.15.4: the chosen cover satisfies the pullback compatibility needed to
define the new differential and comparison component simultaneously. -/
private theorem extensionCover_condition
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extensionCoverToPrevious (S := S) ≫ previousToCycles =
      extensionCoverToStageCycles (S := S) ≫ cyclesMap (S := S) := by
  -- This is exactly the pullback equation transported along the chosen cover map.
  simpa [extensionCoverToPrevious, extensionCoverToStageCycles, Category.assoc] using
    congrArg (fun k ↦ extensionCoverMap (S := S) ≫ k)
      (pullback.condition (f := previousToCycles) (g := cyclesMap (S := S)))

/-- Helper for Lemma 13.15.4: the square defining `extensionPullback` is the canonical pullback
square on `previousToCycles` and the stage cycles map. -/
private theorem extensionPullback_isPullback
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsPullback
      (pullback.fst previousToCycles (cyclesMap (S := S)))
      (pullback.snd previousToCycles (cyclesMap (S := S)))
      previousToCycles
      (cyclesMap (S := S)) := by
  -- Proof comment: this is exactly the owner pullback square of the chosen source object.
  exact IsPullback.of_hasPullback previousToCycles (cyclesMap (S := S))

/-- Helper for Lemma 13.15.4: the pullback square on `previousToCycles` and the stage cycles map
induces an isomorphism on the vertical kernel comparison. -/
private theorem extensionPullback_kernel_map_isIso
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsIso
      (kernel.map
        (pullback.snd previousToCycles (cyclesMap (S := S)))
        previousToCycles
        (pullback.fst previousToCycles (cyclesMap (S := S)))
        (cyclesMap (S := S))
        (pullback.condition
          (f := previousToCycles)
          (g := cyclesMap (S := S))).symm) := by
  -- Proof comment: the Stacks cutoff square is an actual pullback square, so the owner vertical
  -- kernel transport is invertible.
  exact CategoryTheory.Limits.isIso_kernel_map_vertical_of_isPullback
    (extensionPullback_isPullback (S := S))

/-- Helper for Lemma 13.15.4: because the stage cycles map is epi, the pullback square defining
`extensionPullback` is also a pushout square. -/
private theorem extensionPullback_isPushout
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsPushout
      (pullback.snd previousToCycles (cyclesMap (S := S)))
      (pullback.fst previousToCycles (cyclesMap (S := S)))
      (cyclesMap (S := S))
      previousToCycles := by
  -- Proof comment: in an abelian category, a pullback square with epi right edge is also a
  -- pushout square.
  letI : Epi (cyclesMap (S := S)) := S.cycles_epi
  exact CategoryTheory.isPushout_of_isPullback_of_epi_right
    (extensionPullback_isPullback (S := S)).flip

/-- Helper for Lemma 13.15.4: the pushout form of `extensionPullback` gives an isomorphism on the
vertical cokernel comparison. -/
private theorem extensionPullback_cokernel_map_isIso
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsIso
      (cokernel.map
        (pullback.fst previousToCycles (cyclesMap (S := S)))
        (cyclesMap (S := S))
        (pullback.snd previousToCycles (cyclesMap (S := S)))
        previousToCycles
        (pullback.condition
          (f := previousToCycles)
          (g := cyclesMap (S := S)))) := by
  -- Proof comment: after converting the pullback square to a pushout square, the owner vertical
  -- cokernel transport is invertible.
  exact CategoryTheory.Limits.isIso_cokernel_map_vertical_of_isPushout
    (extensionPullback_isPushout (S := S))

/-- Helper for Chap13 Lemma 13 15 4: if `η` is epi, then the canonical comparison
`kernel (η ≫ θ) ⟶ kernel θ` is epi. -/
private theorem kernelMap_comp_epi
    {X Y Z : A} (η : X ⟶ Y) [Epi η] (θ : Y ⟶ Z) :
    Epi (kernel.map (η ≫ θ) θ η (𝟙 Z) (by simp)) := by
  -- Proof comment: the square with bottom edge `𝟙 Z` is a pushout as soon as the top edge `η`
  -- is epi, so the ambient abelian-category kernel comparison theorem applies.
  let sq : IsPushout η (η ≫ θ) θ (𝟙 Z) :=
    IsPushout.of_horiz_isIso_epi (CommSq.mk (by simp))
  simpa using CategoryTheory.Abelian.epi_kernel_map_of_isPushout sq.flip

/-- Helper for Lemma 13.15.4: the raw one-step extension changes only the cutoff degree
`n - 1`. -/
private noncomputable def extendRawX
    (S : BoundedAboveReplacementStage (P := P) a K n) (i : ℤ) : A :=
  if i = n - 1 then extensionCoverObject (S := S) else S.Q.X i

/-- Helper for Lemma 13.15.4: at the new cutoff degree the raw extension uses the chosen
pullback cover. -/
private theorem extendRawX_eq_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extendRawX (S := S) (n - 1) = extensionCoverObject (S := S) := by
  -- The raw extension was defined to replace exactly the degree `n - 1` term.
  simp [extendRawX]

/-- Helper for Lemma 13.15.4: away from the new cutoff degree the raw extension agrees with the
previous stage. -/
private theorem extendRawX_eq_stage_of_ne
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ}
    (hi : i ≠ n - 1) :
    extendRawX (S := S) i = S.Q.X i := by
  -- Off the cutoff degree, the raw object family is unchanged.
  simp [extendRawX, hi]

/-- Helper for Lemma 13.15.4: every degree on or above `n` is unchanged in the raw extension. -/
private theorem extendRawX_eq_stage_of_le
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ}
    (hi : n ≤ i) :
    extendRawX (S := S) i = S.Q.X i := by
  -- The only modified degree is `n - 1`, which lies strictly below the inherited tail.
  apply extendRawX_eq_stage_of_ne (S := S)
  omega

/-- Helper for Lemma 13.15.4: the new cutoff term of the raw extension again lies in `P`. -/
private theorem extendRawX_term_mem_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    P (extendRawX (S := S) (n - 1)) := by
  -- The replacement term is the chosen `P`-cover of the source pullback.
  rw [extendRawX_eq_cutoff (S := S)]
  exact extensionCover_mem (S := S)

/-- Helper for Lemma 13.15.4: the cycle lift `K.X (n - 1) ⟶ Z^n(K)` composes with the kernel
inclusion to the previous differential. -/
private theorem previousToCycles_comp_ι :
    previousToCycles (K := K) (n := n) ≫ kernel.ι (K.d n (n + 1)) = K.d (n - 1) n := by
  -- Unfold the kernel lift and use its defining equation.
  simp [previousToCycles]

/-- Helper for Lemma 13.15.4: the induced cycles map agrees with the stage comparison map after
postcomposing with the target cycles inclusion. -/
private theorem cyclesMap_comp_ι
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    cyclesMap (S := S) ≫ kernel.ι (K.d n (n + 1)) =
      kernel.ι (S.Q.d n (n + 1)) ≫ S.α.f n := by
  -- This is the defining compatibility of `kernel.map` for the stage comparison square.
  simp [cyclesMap]

/-- Helper for Lemma 13.15.4: the raw extension contributes the new differential
`Q^{n - 1} ⟶ Q^n` by composing the chosen cover with the cycles inclusion of the previous stage.
-/
private noncomputable def extendRawCutoffD
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extendRawX (S := S) (n - 1) ⟶ extendRawX (S := S) n :=
  eqToHom (extendRawX_eq_cutoff (S := S)) ≫
    extensionCoverToStageCycles (S := S) ≫
      kernel.ι (S.Q.d n (n + 1)) ≫
        eqToHom ((extendRawX_eq_stage_of_le (S := S) (i := n) le_rfl).symm)

/-- Helper for Lemma 13.15.4: the raw extension comparison in degree `n - 1` is the chosen map
from the pullback cover to `K^{n - 1}`. -/
private noncomputable def extendRawCutoffα
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extendRawX (S := S) (n - 1) ⟶ K.X (n - 1) :=
  eqToHom (extendRawX_eq_cutoff (S := S)) ≫ extensionCoverToPrevious (S := S)

/-- Helper for Lemma 13.15.4: the new cutoff comparison map is epi, since it is just the chosen
pullback-cover projection up to the obvious transport. -/
private theorem extendRawCutoffα_epi
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    Epi (extendRawCutoffα (S := S)) := by
  -- Epimorphy is preserved under the domain transport and already holds for the pullback cover
  -- projection to `K.X (n - 1)`.
  letI : Epi (extensionCoverToPrevious (S := S)) := extensionCoverToPrevious_epi (S := S)
  simpa [extendRawCutoffα] using
    (inferInstance :
      Epi (eqToHom (extendRawX_eq_cutoff (S := S)) ≫ extensionCoverToPrevious (S := S)))

/-- Helper for Lemma 13.15.4: the new cutoff differential squares to zero against the inherited
tail differential because it factors through the cycles object. -/
private theorem extendRawCutoffD_comp_stage_d
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extendRawCutoffD (S := S) ≫
        eqToHom (extendRawX_eq_stage_of_le (S := S) (i := n) le_rfl) ≫
          S.Q.d n (n + 1) = 0 := by
  -- After canceling the transport back to `S.Q.X n`, the composite lands in the kernel of the
  -- inherited differential.
  simp [extendRawCutoffD, Category.assoc]

/-- Helper for Lemma 13.15.4: the new cutoff comparison square commutes before the rest of the
complex is packaged. -/
private theorem extendRawCutoff_comm
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extendRawCutoffα (S := S) ≫ K.d (n - 1) n =
      extendRawCutoffD (S := S) ≫
        eqToHom (extendRawX_eq_stage_of_le (S := S) (i := n) le_rfl) ≫
          S.α.f n := by
  -- Postcompose the pullback compatibility with the relevant cycle inclusions on both sides.
  calc
    extendRawCutoffα (S := S) ≫ K.d (n - 1) n
        = eqToHom (extendRawX_eq_cutoff (S := S)) ≫
            (extensionCoverToPrevious (S := S) ≫ K.d (n - 1) n) := by
            simp [extendRawCutoffα, Category.assoc]
    _ = eqToHom (extendRawX_eq_cutoff (S := S)) ≫
          (extensionCoverToStageCycles (S := S) ≫
            kernel.ι (S.Q.d n (n + 1)) ≫ S.α.f n) := by
          simpa [Category.assoc, previousToCycles_comp_ι (K := K) (n := n),
            cyclesMap_comp_ι (S := S)] using
            congrArg
              (fun k ↦ eqToHom (extendRawX_eq_cutoff (S := S)) ≫
                k ≫ kernel.ι (K.d n (n + 1)))
              (extensionCover_condition (S := S))
    _ = extendRawCutoffD (S := S) ≫
          eqToHom (extendRawX_eq_stage_of_le (S := S) (i := n) le_rfl) ≫
            S.α.f n := by
          simp [extendRawCutoffD, Category.assoc]

/-- Helper for Lemma 13.15.4: a successor degree above the inherited tail still lies in the
inherited tail. -/
private theorem succ_le_of_le_of_eq_succ {i j : ℤ}
    (hi : n ≤ i) (hij : i + 1 = j) :
    n ≤ j := by
  omega

/-- Helper for Lemma 13.15.4: if the source index is the new cutoff degree and `j = i + 1`,
then `j = n`. -/
private theorem cutoff_target_eq_of_eq_prev {i j : ℤ}
    (hi : i = n - 1) (hij : i + 1 = j) :
    j = n := by
  omega

/-- Helper for Lemma 13.15.4: the packaged one-step extension uses the new cutoff differential at
`n - 1 → n`, inherits the old tail on arrows starting in degree `≥ n`, and is zero below the
new cutoff. -/
private noncomputable def extend_raw_d
    (S : BoundedAboveReplacementStage (P := P) a K n) (i j : ℤ) :
    extendRawX (S := S) i ⟶ extendRawX (S := S) j :=
  if hij : i + 1 = j then
    if hi : i = n - 1 then
      eqToHom (congrArg (extendRawX (S := S)) hi) ≫
        extendRawCutoffD (S := S) ≫
        eqToHom
          (congrArg (extendRawX (S := S))
            (cutoff_target_eq_of_eq_prev (n := n) hi hij).symm)
    else if hn : n ≤ i then
      eqToHom (extendRawX_eq_stage_of_le (S := S) (i := i) hn) ≫
        S.Q.d i j ≫
        eqToHom
          ((extendRawX_eq_stage_of_le (S := S) (i := j)
            (succ_le_of_le_of_eq_succ (n := n) hn hij)).symm)
    else
      0
  else
    0

/-- Helper for Lemma 13.15.4: the packaged raw differential is exactly the cutoff differential on
the new arrow `n - 1 → n`. -/
private theorem extend_raw_d_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extend_raw_d (S := S) (n - 1) n = extendRawCutoffD (S := S) := by
  -- Proof comment: both transports collapse to identities at the distinguished cutoff arrow.
  simp [extend_raw_d, cutoff_target_eq_of_eq_prev]

/-- Helper for Lemma 13.15.4: on the inherited tail, the packaged raw differential is just the
old stage differential up to the canonical transports coming from the unchanged objects. -/
private theorem extend_raw_d_of_le
    (S : BoundedAboveReplacementStage (P := P) a K n) {i j : ℤ}
    (hi : n ≤ i) (hij : i + 1 = j) :
    extend_raw_d (S := S) i j =
      eqToHom (extendRawX_eq_stage_of_le (S := S) (i := i) hi) ≫
        S.Q.d i j ≫
        eqToHom
          ((extendRawX_eq_stage_of_le (S := S) (i := j)
            (succ_le_of_le_of_eq_succ (n := n) hi hij)).symm) := by
  -- Proof comment: away from the cutoff, the only active branch is the inherited-tail branch.
  have hneq : i ≠ n - 1 := by
    omega
  simp [extend_raw_d, hij, hneq, hi]

/-- Helper for Lemma 13.15.4: below the new cutoff, every successor differential in the packaged
raw extension is zero. -/
private theorem extend_raw_d_of_lt
    (S : BoundedAboveReplacementStage (P := P) a K n) {i j : ℤ}
    (hi : i < n - 1) (hij : i + 1 = j) :
    extend_raw_d (S := S) i j = 0 := by
  -- Proof comment: the packaged extension only starts being nontrivial at degree `n - 1`.
  have hneq : i ≠ n - 1 := by omega
  have hnot : ¬ n ≤ i := by omega
  simp [extend_raw_d, hij, hneq, hnot]

/-- Helper for Lemma 13.15.4: the packaged raw differential still has cochain shape. -/
private theorem extend_raw_shape
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    ∀ i j : ℤ, ¬ i + 1 = j → extend_raw_d (S := S) i j = 0 := by
  intro i j hij
  -- Proof comment: every non-successor arrow is zero by definition.
  simp [extend_raw_d, hij]

/-- Helper for Lemma 13.15.4: the packaged raw differential squares to zero because below the new
cutoff it is zero, at the cutoff it factors through cycles, and on the tail it is inherited from
the previous stage. -/
private theorem extend_raw_d_comp_d
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    ∀ i j k : ℤ, i + 1 = j → j + 1 = k →
      extend_raw_d (S := S) i j ≫ extend_raw_d (S := S) j k = 0 := by
  intro i j k hij hjk
  by_cases hcut : i = n - 1
  · -- Proof comment: at the cutoff, the first differential is the new cycle-valued arrow and the
    -- second differential is the inherited tail arrow, so the composite is the raw cutoff
    -- factorization through cycles.
    have hj : j = n := cutoff_target_eq_of_eq_prev (n := n) hcut hij
    have hk : k = n + 1 := by
      omega
    subst i
    subst j
    subst k
    rw [extend_raw_d_cutoff (S := S)]
    rw [extend_raw_d_of_le (S := S) (i := n) (j := n + 1) le_rfl rfl]
    have hzero := extendRawCutoffD_comp_stage_d (S := S)
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ t ≫
          eqToHom
            ((extendRawX_eq_stage_of_le (S := S) (i := n + 1)
              (succ_le_of_le_of_eq_succ (n := n) le_rfl rfl)).symm))
        hzero
  · by_cases htail : n ≤ i
    · -- Proof comment: on the inherited tail, both differentials are transported copies of the
      -- old stage differentials, so `d ≫ d = 0` is inherited from `S.Q`.
      have hj : n ≤ j := succ_le_of_le_of_eq_succ (n := n) htail hij
      rw [extend_raw_d_of_le (S := S) (i := i) (j := j) htail hij]
      rw [extend_raw_d_of_le (S := S) (i := j) (j := k) hj hjk]
      simp [Category.assoc]
    · -- Proof comment: strictly below the new cutoff, the first differential already vanishes.
      have hi : i < n - 1 := by
        omega
      rw [extend_raw_d_of_lt (S := S) (i := i) (j := j) hi hij]
      simp

/-- Helper for Lemma 13.15.4: the packaged raw extension is the actual cochain complex obtained
from the raw cutoff override. -/
private noncomputable def extend_raw_complex
    (S : BoundedAboveReplacementStage (P := P) a K n) : CochainComplex A ℤ :=
  { X := extendRawX (S := S)
    d := extend_raw_d (S := S)
    shape := extend_raw_shape (S := S)
    d_comp_d' := extend_raw_d_comp_d (S := S) }

/-- Helper for Lemma 13.15.4: on degrees `≥ n`, the packaged raw extension keeps exactly the old
stage objects. -/
private theorem extend_raw_complex_X_of_le
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ}
    (hi : n ≤ i) :
    (extend_raw_complex (S := S)).X i = S.Q.X i :=
  extendRawX_eq_stage_of_le (S := S) hi

/-- Helper for Lemma 13.15.4: the new cutoff object of the packaged raw extension is the chosen
pullback cover. -/
private theorem extend_raw_complex_X_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extend_raw_complex (S := S)).X (n - 1) = extensionCoverObject (S := S) :=
  extendRawX_eq_cutoff (S := S)

/-- Helper for Lemma 13.15.4: on arrows starting in degree `≥ n`, the packaged raw extension
inherits the old stage differential up to the canonical transports. -/
private theorem extend_raw_complex_d_of_le
    (S : BoundedAboveReplacementStage (P := P) a K n) {i j : ℤ}
    (hi : n ≤ i) (hij : i + 1 = j) :
    (extend_raw_complex (S := S)).d i j =
      eqToHom (extend_raw_complex_X_of_le (S := S) (i := i) hi) ≫
        S.Q.d i j ≫
        eqToHom
          ((extend_raw_complex_X_of_le (S := S) (i := j)
            (succ_le_of_le_of_eq_succ (n := n) hi hij)).symm) := by
  -- Proof comment: this is just the tail branch of `extend_raw_d`.
  exact extend_raw_d_of_le (S := S) hi hij

/-- Helper for Lemma 13.15.4: at the new cutoff arrow, the packaged raw extension uses the raw
cutoff differential. -/
private theorem extend_raw_complex_d_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extend_raw_complex (S := S)).d (n - 1) n = extendRawCutoffD (S := S) :=
  extend_raw_d_cutoff (S := S)

/-- Helper for Lemma 13.15.4: below the new cutoff, the packaged raw extension still has zero
objects because it inherits the previous stage there. -/
private theorem extend_raw_complex_zero_below
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ}
    (hi : i < n - 1) :
    IsZero ((extend_raw_complex (S := S)).X i) := by
  -- Proof comment: all degrees strictly below `n - 1` already vanish in the previous stage.
  simpa [extend_raw_complex, extendRawX_eq_stage_of_ne (S := S) (i := i) (by omega)] using
    S.zero_below i (by omega)

/-- Helper for Lemma 13.15.4: the new cutoff object of the packaged raw extension still belongs
to `P`. -/
private theorem extend_raw_complex_term_mem_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    P ((extend_raw_complex (S := S)).X (n - 1)) := by
  -- Proof comment: the cutoff object is exactly the chosen `P`-cover of the pullback.
  simpa [extend_raw_complex_X_cutoff (S := S)] using extensionCover_mem (S := S)

/-- Helper for Lemma 13.15.4: the packaged comparison map uses the new cutoff component at
degree `n - 1`, inherits the old stage map on the tail, and is zero below the new cutoff. -/
private noncomputable def extend_raw_f
    (S : BoundedAboveReplacementStage (P := P) a K n) (i : ℤ) :
    (extend_raw_complex (S := S)).X i ⟶ K.X i :=
  if hi : i = n - 1 then
    eqToHom (congrArg ((extend_raw_complex (S := S)).X) hi) ≫
      extendRawCutoffα (S := S) ≫
        eqToHom (congrArg K.X hi.symm)
  else if hn : n ≤ i then
    eqToHom (extend_raw_complex_X_of_le (S := S) (i := i) hn) ≫ S.α.f i
  else
    0

/-- Helper for Lemma 13.15.4: the packaged comparison map uses the raw cutoff component at
degree `n - 1`. -/
private theorem extend_raw_f_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extend_raw_f (S := S) (n - 1) = extendRawCutoffα (S := S) := by
  -- Proof comment: at the cutoff degree the transport collapses to the identity.
  rw [extend_raw_f, dif_pos rfl]
  simp

/-- Helper for Lemma 13.15.4: on the inherited tail, the packaged comparison map is the old stage
comparison map up to the canonical transport. -/
private theorem extend_raw_f_of_le
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ}
    (hi : n ≤ i) :
    extend_raw_f (S := S) i =
      eqToHom (extend_raw_complex_X_of_le (S := S) (i := i) hi) ≫ S.α.f i := by
  -- Proof comment: above the cutoff the comparison map is inherited unchanged.
  have hneq : i ≠ n - 1 := by
    omega
  simp [extend_raw_f, hneq, hi]

/-- Helper for Lemma 13.15.4: below the new cutoff, the packaged comparison map is zero. -/
private theorem extend_raw_f_of_lt
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ}
    (hi : i < n - 1) :
    extend_raw_f (S := S) i = 0 := by
  -- Proof comment: the source route leaves all lower degrees trivial until later stages.
  have hneq : i ≠ n - 1 := by omega
  have hnot : ¬ n ≤ i := by omega
  simp [extend_raw_f, hneq, hnot]

/-- Helper for Lemma 13.15.4: the packaged comparison map is a chain map. The cutoff square is
the isolated raw commutativity square, the tail squares are inherited from `S`, and below the
new cutoff everything is zero. -/
private theorem extend_raw_comm
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    ∀ i j : ℤ,
      extend_raw_f (S := S) i ≫ K.d i j =
        (extend_raw_complex (S := S)).d i j ≫ extend_raw_f (S := S) j := by
  intro i j
  by_cases hij : i + 1 = j
  · by_cases hcut : i = n - 1
    · -- Proof comment: the unique new square is exactly the raw cutoff square already proved.
      have hj : j = n := cutoff_target_eq_of_eq_prev (n := n) hcut hij
      subst i
      subst j
      rw [extend_raw_f_cutoff (S := S)]
      rw [extend_raw_complex_d_cutoff (S := S)]
      rw [extend_raw_f_of_le (S := S) (i := n) le_rfl]
      simpa [Category.assoc] using extendRawCutoff_comm (S := S)
    · by_cases htail : n ≤ i
      · -- Proof comment: on the inherited tail, the commutative square is transported directly
        -- from the stage chain map `S.α`.
        have hj : n ≤ j := succ_le_of_le_of_eq_succ (n := n) htail hij
        rw [extend_raw_f_of_le (S := S) (i := i) htail]
        rw [extend_raw_complex_d_of_le (S := S) (i := i) (j := j) htail hij]
        rw [extend_raw_f_of_le (S := S) (i := j) hj]
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ eqToHom (extend_raw_complex_X_of_le (S := S) (i := i) htail) ≫ t)
            (S.α.comm i j)
      · -- Proof comment: below the new cutoff the source component and the outgoing differential
        -- both vanish, so the square is trivially commutative.
        have hi : i < n - 1 := by
          omega
        rw [extend_raw_f_of_lt (S := S) (i := i) hi]
        have hzero : (extend_raw_complex (S := S)).d i j = 0 := by
          simpa [extend_raw_complex] using extend_raw_d_of_lt (S := S) (i := i) (j := j) hi hij
        rw [hzero]
        simp
  · -- Proof comment: for a non-successor arrow, both differentials are zero by cochain shape.
    have hshape : (extend_raw_complex (S := S)).d i j = 0 := by
      simpa [extend_raw_complex] using extend_raw_shape (S := S) i j hij
    rw [hshape]
    simpa using congrArg (fun t ↦ extend_raw_f (S := S) i ≫ t) (K.shape i j hij)

/-- Helper for Lemma 13.15.4: the packaged comparison map from the one-step raw extension to `K`.
-/
private noncomputable def extend_raw_α
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extend_raw_complex (S := S) ⟶ K :=
  { f := extend_raw_f (S := S)
    comm' := by
      intro i j hij
      exact extend_raw_comm (S := S) i j }

/-- Helper for Lemma 13.15.4: on degrees `≥ n`, the packaged comparison map agrees with the old
stage comparison up to the canonical transport. -/
private theorem extend_raw_α_f_of_le
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ}
    (hi : n ≤ i) :
    (extend_raw_α (S := S)).f i =
      eqToHom (extend_raw_complex_X_of_le (S := S) (i := i) hi) ≫ S.α.f i :=
  extend_raw_f_of_le (S := S) hi

/-- Helper for Lemma 13.15.4: at the new cutoff degree, the packaged comparison map uses the raw
cutoff component. -/
private theorem extend_raw_α_f_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extend_raw_α (S := S)).f (n - 1) = extendRawCutoffα (S := S) :=
  extend_raw_f_cutoff (S := S)

/-- Helper for Lemma 13.15.4: the packaged comparison map is epi at the new cutoff degree. -/
private theorem extend_raw_α_epi_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    Epi ((extend_raw_α (S := S)).f (n - 1)) := by
  -- Proof comment: this is exactly the raw cutoff epimorphism, rewritten through the packaging.
  rw [extend_raw_α_f_cutoff (S := S)]
  exact extendRawCutoffα_epi (S := S)

/-- Helper for Lemma 13.15.4: on the inherited tail, the packaged comparison map remains
termwise epimorphic. -/
private theorem extend_raw_α_epi_of_le
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ}
    (hi : n ≤ i) :
    Epi ((extend_raw_α (S := S)).f i) := by
  -- Proof comment: the tail component is the old stage component up to a domain transport.
  letI : Epi (S.α.f i) := S.term_epi i hi
  simpa [extend_raw_α_f_of_le (S := S) hi] using
    (inferInstance :
      Epi (eqToHom (extend_raw_complex_X_of_le (S := S) (i := i) hi) ≫ S.α.f i))

/-- Helper for Lemma 13.15.4: once the descending stage index has reached the actual cutoff
range `n ≤ a + 1`, the packaged raw one-step extension is still strictly bounded above by `a`. -/
private theorem extend_raw_complex_strictlyLE
    (S : BoundedAboveReplacementStage (P := P) a K n) (hn : n ≤ a + 1) :
    (extend_raw_complex (S := S)).IsStrictlyLE a := by
  -- Proof comment: for any degree strictly above `a`, the new cutoff degree `n - 1` is too low
  -- to intervene, so the packaged raw extension agrees with the old stage.
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have hne : i ≠ n - 1 := by
    omega
  letI : S.Q.IsStrictlyLE a := S.strictlyLE
  simpa [extend_raw_complex, extendRawX_eq_stage_of_ne (S := S) (i := i) hne] using
    S.Q.isZero_of_isStrictlyLE a i hi

/-- Helper for Lemma 13.15.4: the packaged raw one-step extension keeps all terms from the object
property `P` on and above the new cutoff degree `n - 1`. -/
private theorem extend_raw_complex_term_mem
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ}
    (hi : n - 1 ≤ i) :
    P ((extend_raw_complex (S := S)).X i) := by
  -- Proof comment: the new cutoff term is the chosen `P`-cover, and every higher degree is
  -- inherited unchanged from the previous stage.
  by_cases hcut : i = n - 1
  · subst hcut
    exact extend_raw_complex_term_mem_cutoff (S := S)
  · have htail : n ≤ i := by
      omega
    rw [extend_raw_complex_X_of_le (S := S) (i := i) htail]
    exact S.term_mem i htail

/-- Helper for Lemma 13.15.4: the packaged comparison map is termwise epimorphic on and above the
new cutoff degree `n - 1`. -/
private theorem extend_raw_α_epi
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ}
    (hi : n - 1 ≤ i) :
    Epi ((extend_raw_α (S := S)).f i) := by
  -- Proof comment: at the new cutoff degree this is the pullback-cover projection, while above it
  -- the component map is inherited from the previous stage.
  by_cases hcut : i = n - 1
  · subst hcut
    exact extend_raw_α_epi_cutoff (S := S)
  · have htail : n ≤ i := by
      omega
    exact extend_raw_α_epi_of_le (S := S) htail

end BoundedAboveReplacementStage

/-- Helper for Lemma 13.15.4: the descending induction starts at cutoff `a + 1` with the chosen
`P`-zero complex mapping to `K`. -/
private noncomputable def boundedAboveReplacementStage_base
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    BoundedAboveReplacementStage (P := P) a K (a + 1) := by
  -- The base stage uses the chosen `P`-zero complex, since `K` already vanishes above `a`.
  have hStrictlyLE : (property_zero_complex (P := P)).IsStrictlyLE a := by
    -- Every term is zero, so the complex is bounded above by any cutoff.
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (HomologicalComplex.eval A (up ℤ) i).map_isZero
      (isZero_property_zero_complex (P := P))
  have hZeroBelow : ∀ i : ℤ, i < a + 1 → IsZero ((property_zero_complex (P := P)).X i) := by
    intro i hi
    exact (HomologicalComplex.eval A (up ℤ) i).map_isZero
      (isZero_property_zero_complex (P := P))
  have hTermMem : ∀ i : ℤ, a + 1 ≤ i → P ((property_zero_complex (P := P)).X i) := by
    intro i hi
    exact property_zero_complex_term_mem (P := P) i
  have hTermEpi : ∀ i : ℤ, a + 1 ≤ i →
      Epi ((0 : ((property_zero_complex (P := P)).X i ⟶ K.X i))) := by
    intro i hi
    have hi' : a < i := by
      omega
    exact property_zero_complex_term_epi_of_isStrictlyLE (P := P) a i K hK hi'
  have hHomologyIso : ∀ i : ℤ, a + 1 < i →
      IsIso (HomologicalComplex.homologyMap (0 : property_zero_complex (P := P) ⟶ K) i) := by
    intro i hi
    have hi' : a < i := by
      omega
    exact property_zero_complex_homologyMap_isIso_of_isStrictlyLE (P := P) a i K hK hi'
  have hCyclesEpi :
      Epi (kernel.map ((property_zero_complex (P := P)).d (a + 1) ((a + 1) + 1))
        (K.d (a + 1) ((a + 1) + 1))
        (0 : (property_zero_complex (P := P)).X (a + 1) ⟶ K.X (a + 1))
        (0 : (property_zero_complex (P := P)).X ((a + 1) + 1) ⟶ K.X ((a + 1) + 1))
        ((0 : property_zero_complex (P := P) ⟶ K).comm (a + 1) ((a + 1) + 1)).symm) := by
    have ha' : a < a + 1 := by
      omega
    exact property_zero_complex_cycles_epi_of_isStrictlyLE (P := P) a (a + 1) K hK ha'
  -- Each field of `IH_(a+1)` is one of the chosen-`P`-zero-complex base facts isolated above.
  exact
    { Q := property_zero_complex (P := P)
      α := 0
      strictlyLE := hStrictlyLE
      zero_below := hZeroBelow
      term_mem := hTermMem
      term_epi := hTermEpi
      homologyMap_isIso := hHomologyIso
      cycles_epi := hCyclesEpi }

/-- Helper for Lemma 13.15.4: the recursive stage index stays within the cutoff range required by
the bound-aware extension step. -/
private theorem boundedAboveReplacementStage_index_le_cutoff
    (a : ℤ) (m : ℕ) :
    a + 1 - Int.ofNat m ≤ a + 1 := by
  -- Proof comment: each recursive step subtracts a natural number from the initial cutoff `a+1`.
  have hm : 0 ≤ Int.ofNat m := by exact Int.natCast_nonneg m
  linarith

/-- Helper for Chap13 Lemma 13 15 4: the common homology-window stage index is at least the
object-window stage index used in the final realization step. -/
private theorem boundedAboveReplacementStage_object_index_le_homology_index
    (a i : ℤ) :
    Int.toNat (a + 1 - i) ≤ Int.toNat (a + 2 - i) := by
  -- Proof comment: the homology window is shifted by one degree, so its stabilization index can
  -- only be later.
  exact Int.toNat_le_toNat (by omega)

namespace BoundedAboveReplacementStage

variable {P} {a : ℤ} {K : CochainComplex A ℤ} {n : ℤ}

/-- Helper for Chap13 Lemma 13 15 4: in degree `n`, the packaged raw extension keeps the previous
stage object unchanged. -/
private theorem extend_raw_complex_X_at_cutoff_target
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extend_raw_complex (S := S)).X n = S.Q.X n := by
  -- Proof comment: degree `n` lies on the inherited tail, so the object is unchanged.
  simpa using extend_raw_complex_X_of_le (S := S) (i := n) le_rfl

/-- Helper for Chap13 Lemma 13 15 4: in degree `n`, the packaged raw comparison map is exactly
the previous stage comparison map after the canonical tail identification. -/
private theorem extend_raw_α_f_at_cutoff_target
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extend_raw_α (S := S)).f n =
      eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)) ≫ S.α.f n := by
  -- Proof comment: this is the degree-`n` instance of the general tail formula for
  -- `extend_raw_α`.
  simpa [extend_raw_complex_X_at_cutoff_target (S := S)] using
    extend_raw_α_f_of_le (S := S) (i := n) le_rfl

/-- Helper for Chap13 Lemma 13 15 4: the kernel of the packaged cutoff differential is the kernel
of the raw pullback-to-cycles map after removing the harmless transport and monomorphism factors.
-/
private noncomputable def extendCutoffKernelSourceIso
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    kernel ((extend_raw_complex (S := S)).d (n - 1) ((n - 1) + 1)) ≅
      kernel (extensionCoverToStageCycles (S := S)) := by
  -- Proof comment: rewrite the cutoff differential to the explicit raw map, then remove the
  -- trailing codomain transport, the mono kernel inclusion, and finally the leading domain
  -- transport.
  let hnn : n = (n - 1) + 1 := by
    omega
  let hidxX :
      (extend_raw_complex (S := S)).X n =
        (extend_raw_complex (S := S)).X ((n - 1) + 1) :=
    congrArg (fun i ↦ (extend_raw_complex (S := S)).X i) hnn
  let hindex :
      (extend_raw_complex (S := S)).d (n - 1) ((n - 1) + 1) =
        (extend_raw_complex (S := S)).d (n - 1) n ≫ eqToHom hidxX := by
    simpa [hidxX] using
      (HomologicalComplex.d_comp_eqToHom
        (C := extend_raw_complex (S := S))
        (i := n - 1) (j := (n - 1) + 1) (j' := n)
        (by simp) (by simp)).symm
  let hcutoff :
      (extend_raw_complex (S := S)).d (n - 1) n =
        eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
          extensionCoverToStageCycles (S := S) ≫
            kernel.ι (S.Q.d n (n + 1)) ≫
              eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)).symm := by
    simpa [extendRawCutoffD, extend_raw_complex_X_at_cutoff_target (S := S)] using
      extend_raw_complex_d_cutoff (S := S)
  let eIndex :
      kernel
          ((extend_raw_complex (S := S)).d (n - 1) n ≫ eqToHom hidxX) ≅
        kernel ((extend_raw_complex (S := S)).d (n - 1) n) := by
    simpa [Category.assoc] using
      (kernelCompMono
        ((extend_raw_complex (S := S)).d (n - 1) n)
        (eqToHom hidxX))
  let eTail :
      kernel
          (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
            extensionCoverToStageCycles (S := S) ≫
              kernel.ι (S.Q.d n (n + 1)) ≫
                eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)).symm) ≅
        kernel
          (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
            extensionCoverToStageCycles (S := S) ≫
              kernel.ι (S.Q.d n (n + 1))) :=
    kernelIsoOfEq (by simp [Category.assoc]) ≪≫
      kernelCompMono
        (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
          extensionCoverToStageCycles (S := S) ≫
            kernel.ι (S.Q.d n (n + 1)))
        (eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)).symm)
  let eKernel :
      kernel
          (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
            extensionCoverToStageCycles (S := S) ≫
              kernel.ι (S.Q.d n (n + 1))) ≅
        kernel
          (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
            extensionCoverToStageCycles (S := S)) :=
    kernelIsoOfEq (by simp [Category.assoc]) ≪≫
      kernelCompMono
        (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
          extensionCoverToStageCycles (S := S))
        (kernel.ι (S.Q.d n (n + 1)))
  exact
    kernelIsoOfEq hindex ≪≫
      eIndex ≪≫
      kernelIsoOfEq hcutoff ≪≫
      eTail ≪≫
      eKernel ≪≫
      kernelIsIsoComp
        (eqToHom (extend_raw_complex_X_cutoff (S := S)))
        (extensionCoverToStageCycles (S := S))

/-- Helper for Chap13 Lemma 13 15 4: the target cutoff cycles object is the kernel of
`previousToCycles`, since `previousToCycles` factors the old differential through the kernel
inclusion. -/
private noncomputable def extendCutoffKernelTargetIso :
    kernel (K.d (n - 1) ((n - 1) + 1)) ≅
      kernel (previousToCycles (K := K) (n := n)) := by
  -- Proof comment: rewrite the previous differential as `previousToCycles` followed by the
  -- cycles inclusion, then remove that terminal monomorphism.
  let hnn : n = (n - 1) + 1 := by
    omega
  let hidxX :
      K.X n =
        K.X ((n - 1) + 1) :=
    congrArg (fun i ↦ K.X i) hnn
  let hindex :
      K.d (n - 1) ((n - 1) + 1) =
        K.d (n - 1) n ≫ eqToHom hidxX := by
    simpa [hidxX] using
      (HomologicalComplex.d_comp_eqToHom
        (C := K)
        (i := n - 1) (j := (n - 1) + 1) (j' := n)
        (by simp) (by simp)).symm
  let htarget :
      K.d (n - 1) n =
        previousToCycles (K := K) (n := n) ≫ kernel.ι (K.d n (n + 1)) := by
    simpa using (previousToCycles_comp_ι (K := K) (n := n)).symm
  let eIndex :
      kernel (K.d (n - 1) n ≫ eqToHom hidxX) ≅
        kernel (K.d (n - 1) n) := by
    simpa [Category.assoc] using
      (kernelCompMono
        (K.d (n - 1) n)
        (eqToHom hidxX))
  exact
    kernelIsoOfEq hindex ≪≫
      eIndex ≪≫
      kernelIsoOfEq htarget ≪≫
      kernelCompMono
        (previousToCycles (K := K) (n := n))
        (kernel.ι (K.d n (n + 1)))

/-- Helper for Chap13 Lemma 13 15 4: postcomposing the source cutoff-kernel transport with the
packaged kernel inclusion collapses the composite transport back to the cutoff inclusion itself. -/
private theorem extendCutoffKernelSourceIso_hom_comp_ι
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extendCutoffKernelSourceIso (S := S)).hom ≫
        kernel.ι (extensionCoverToStageCycles (S := S)) =
      kernel.ι ((extend_raw_complex (S := S)).d (n - 1) ((n - 1) + 1)) ≫
        eqToHom (extend_raw_complex_X_cutoff (S := S)) := by
  -- Proof comment: expand the composite kernel transport once and let the owner `...hom_comp_ι`
  -- lemmas cancel each transport layer from right to left until only the packaged cutoff
  -- inclusion remains.
  let hnn : n = (n - 1) + 1 := by
    omega
  let hidxX :
      (extend_raw_complex (S := S)).X n =
        (extend_raw_complex (S := S)).X ((n - 1) + 1) :=
    congrArg (fun i ↦ (extend_raw_complex (S := S)).X i) hnn
  let hindex :
      (extend_raw_complex (S := S)).d (n - 1) ((n - 1) + 1) =
        (extend_raw_complex (S := S)).d (n - 1) n ≫ eqToHom hidxX := by
    simpa [hidxX] using
      (HomologicalComplex.d_comp_eqToHom
        (C := extend_raw_complex (S := S))
        (i := n - 1) (j := (n - 1) + 1) (j' := n)
        (by simp) (by simp)).symm
  let hcutoff :
      (extend_raw_complex (S := S)).d (n - 1) n =
        eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
          extensionCoverToStageCycles (S := S) ≫
            kernel.ι (S.Q.d n (n + 1)) ≫
              eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)).symm := by
    simpa [extendRawCutoffD, extend_raw_complex_X_at_cutoff_target (S := S)] using
      extend_raw_complex_d_cutoff (S := S)
  let eIndex :
      kernel
          ((extend_raw_complex (S := S)).d (n - 1) n ≫ eqToHom hidxX) ≅
        kernel ((extend_raw_complex (S := S)).d (n - 1) n) := by
    simpa [Category.assoc] using
      (kernelCompMono
        ((extend_raw_complex (S := S)).d (n - 1) n)
        (eqToHom hidxX))
  let eTail :
      kernel
          (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
            extensionCoverToStageCycles (S := S) ≫
              kernel.ι (S.Q.d n (n + 1)) ≫
                eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)).symm) ≅
        kernel
          (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
            extensionCoverToStageCycles (S := S) ≫
              kernel.ι (S.Q.d n (n + 1))) :=
    kernelIsoOfEq (by simp [Category.assoc]) ≪≫
      kernelCompMono
        (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
          extensionCoverToStageCycles (S := S) ≫
            kernel.ι (S.Q.d n (n + 1)))
        (eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)).symm)
  let eKernel :
      kernel
          (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
            extensionCoverToStageCycles (S := S) ≫
              kernel.ι (S.Q.d n (n + 1))) ≅
        kernel
          (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
            extensionCoverToStageCycles (S := S)) :=
    kernelIsoOfEq (by simp [Category.assoc]) ≪≫
      kernelCompMono
        (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
          extensionCoverToStageCycles (S := S))
        (kernel.ι (S.Q.d n (n + 1)))
  change
    ((kernelIsoOfEq hindex ≪≫
      eIndex ≪≫
      kernelIsoOfEq hcutoff ≪≫
      eTail ≪≫
      eKernel ≪≫
      kernelIsIsoComp
        (eqToHom (extend_raw_complex_X_cutoff (S := S)))
        (extensionCoverToStageCycles (S := S))).hom) ≫
        kernel.ι (extensionCoverToStageCycles (S := S)) =
      kernel.ι ((extend_raw_complex (S := S)).d (n - 1) ((n - 1) + 1)) ≫
        eqToHom (extend_raw_complex_X_cutoff (S := S))
  simp [Category.assoc, eIndex, eTail, eKernel, hindex, hcutoff]

/-- Helper for Chap13 Lemma 13 15 4: postcomposing the inverse target cutoff-kernel transport
with the old differential kernel inclusion removes the harmless index and kernel-inclusion
transports, leaving the canonical map into `kernel previousToCycles`. -/
private theorem extendCutoffKernelTargetIso_inv_comp_ι :
    (extendCutoffKernelTargetIso (K := K) (n := n)).inv ≫
        kernel.ι (K.d (n - 1) ((n - 1) + 1)) =
      kernel.ι (previousToCycles (K := K) (n := n)) := by
  -- Proof comment: the inverse transport is the target-side analogue of the source-side kernel
  -- normalization, so the same kernel owner lemmas strip away the index transport and terminal
  -- mono from right to left.
  let hnn : n = (n - 1) + 1 := by
    omega
  let hidxX :
      K.X n =
        K.X ((n - 1) + 1) :=
    congrArg (fun i ↦ K.X i) hnn
  let hindex :
      K.d (n - 1) ((n - 1) + 1) =
        K.d (n - 1) n ≫ eqToHom hidxX := by
    simpa [hidxX] using
      (HomologicalComplex.d_comp_eqToHom
        (C := K)
        (i := n - 1) (j := (n - 1) + 1) (j' := n)
        (by simp) (by simp)).symm
  let htarget :
      K.d (n - 1) n =
        previousToCycles (K := K) (n := n) ≫ kernel.ι (K.d n (n + 1)) := by
    simpa using (previousToCycles_comp_ι (K := K) (n := n)).symm
  let eIndex :
      kernel (K.d (n - 1) n ≫ eqToHom hidxX) ≅
        kernel (K.d (n - 1) n) := by
    simpa [Category.assoc] using
      (kernelCompMono
        (K.d (n - 1) n)
        (eqToHom hidxX))
  change
    ((kernelIsoOfEq hindex ≪≫
      eIndex ≪≫
      kernelIsoOfEq htarget ≪≫
      kernelCompMono
        (previousToCycles (K := K) (n := n))
        (kernel.ι (K.d n (n + 1)))).inv) ≫
        kernel.ι (K.d (n - 1) ((n - 1) + 1)) =
      kernel.ι (previousToCycles (K := K) (n := n))
  simp [Category.assoc, eIndex, hindex, htarget]

/-- Helper for Chap13 Lemma 13 15 4: after removing the packaged cutoff transports, the new
cycles comparison factors through the raw pullback square used in the source proof. -/
private theorem extendCutoffKernelMapFactorization
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    kernel.map ((extend_raw_complex (S := S)).d (n - 1) ((n - 1) + 1))
        (K.d (n - 1) ((n - 1) + 1))
        ((extend_raw_α (S := S)).f (n - 1)) ((extend_raw_α (S := S)).f ((n - 1) + 1))
        (((extend_raw_α (S := S)).comm (n - 1) ((n - 1) + 1)).symm) =
      (extendCutoffKernelSourceIso (S := S)).hom ≫
        kernel.map
          (extensionCoverToStageCycles (S := S))
          (previousToCycles (K := K) (n := n))
          (extensionCoverToPrevious (S := S))
          (cyclesMap (S := S))
          (extensionCover_condition (S := S)).symm ≫
        (extendCutoffKernelTargetIso (K := K) (n := n)).inv := by
  -- Proof comment: compare both kernel morphisms after postcomposing with the target kernel
  -- inclusion. The left side is the defining equation of `kernel.map`, while the right side
  -- collapses by the source and target transport lemmas proved just above.
  apply (cancel_mono (kernel.ι (K.d (n - 1) ((n - 1) + 1)))).1
  calc
    kernel.map ((extend_raw_complex (S := S)).d (n - 1) ((n - 1) + 1))
          (K.d (n - 1) ((n - 1) + 1))
          ((extend_raw_α (S := S)).f (n - 1)) ((extend_raw_α (S := S)).f ((n - 1) + 1))
          (((extend_raw_α (S := S)).comm (n - 1) ((n - 1) + 1)).symm) ≫
        kernel.ι (K.d (n - 1) ((n - 1) + 1))
        =
          kernel.ι ((extend_raw_complex (S := S)).d (n - 1) ((n - 1) + 1)) ≫
            ((extend_raw_α (S := S)).f (n - 1)) := by
          simp [Category.assoc]
    _ =
        kernel.ι ((extend_raw_complex (S := S)).d (n - 1) ((n - 1) + 1)) ≫
          eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
            extensionCoverToPrevious (S := S) := by
      rw [extend_raw_α_f_cutoff]
      rfl
    _ =
        (extendCutoffKernelSourceIso (S := S)).hom ≫
          kernel.ι (extensionCoverToStageCycles (S := S)) ≫
            extensionCoverToPrevious (S := S) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ k ≫ extensionCoverToPrevious (S := S))
              (extendCutoffKernelSourceIso_hom_comp_ι (S := S)).symm
    _ =
        ((extendCutoffKernelSourceIso (S := S)).hom ≫
          kernel.map
            (extensionCoverToStageCycles (S := S))
            (previousToCycles (K := K) (n := n))
            (extensionCoverToPrevious (S := S))
            (cyclesMap (S := S))
            (extensionCover_condition (S := S)).symm ≫
          (extendCutoffKernelTargetIso (K := K) (n := n)).inv) ≫
            kernel.ι (K.d (n - 1) ((n - 1) + 1)) := by
          simp [Category.assoc, extendCutoffKernelTargetIso_inv_comp_ι]

/-- Helper for Lemma 13.15.4: the new cycles comparison at the cutoff degree of the raw extension
is epimorphic after transporting both kernels to the pullback square used in the source proof. -/
private theorem extend_cycles_epi_via_kernel_transport
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    Epi (kernel.map ((extend_raw_complex (S := S)).d (n - 1) ((n - 1) + 1))
      (K.d (n - 1) ((n - 1) + 1))
      ((extend_raw_α (S := S)).f (n - 1)) ((extend_raw_α (S := S)).f ((n - 1) + 1))
      (((extend_raw_α (S := S)).comm (n - 1) ((n - 1) + 1)).symm)) := by
  -- Proof comment: after removing the packaged transport isomorphisms, the cutoff cycles map is
  -- the composition of the cover-induced epi comparison with the pullback-kernel isomorphism.
  letI : Epi (extensionCoverMap (S := S)) := extensionCover_epi (S := S)
  have hCover :
      Epi (kernel.map
        (extensionCoverMap (S := S) ≫
          pullback.snd previousToCycles (cyclesMap (S := S)))
        (pullback.snd previousToCycles (cyclesMap (S := S)))
        (extensionCoverMap (S := S)) (𝟙 _)
        (by simp)) := by
    simpa [extensionCoverToStageCycles] using
      (kernelMap_comp_epi
        (extensionCoverMap (S := S))
        (pullback.snd previousToCycles (cyclesMap (S := S))))
  have hPullback :
      IsIso (kernel.map
        (pullback.snd previousToCycles (cyclesMap (S := S)))
        (previousToCycles (K := K) (n := n))
        (pullback.fst previousToCycles (cyclesMap (S := S)))
        (cyclesMap (S := S))
        (pullback.condition (f := previousToCycles) (g := cyclesMap (S := S))).symm) :=
    extensionPullback_kernel_map_isIso (S := S)
  have hMiddle :
      Epi (kernel.map
        (extensionCoverToStageCycles (S := S))
        (previousToCycles (K := K) (n := n))
        (extensionCoverToPrevious (S := S))
        (cyclesMap (S := S))
        (extensionCover_condition (S := S)).symm) := by
    have hComp :
        kernel.map
          (extensionCoverToStageCycles (S := S))
          (previousToCycles (K := K) (n := n))
          (extensionCoverToPrevious (S := S))
          (cyclesMap (S := S))
          (extensionCover_condition (S := S)).symm =
          kernel.map
            (extensionCoverMap (S := S) ≫
              pullback.snd previousToCycles (cyclesMap (S := S)))
            (pullback.snd previousToCycles (cyclesMap (S := S)))
            (extensionCoverMap (S := S))
            (𝟙 _)
            (by simp [Category.assoc]) ≫
          kernel.map
            (pullback.snd previousToCycles (cyclesMap (S := S)))
            (previousToCycles (K := K) (n := n))
            (pullback.fst previousToCycles (cyclesMap (S := S)))
            (cyclesMap (S := S))
            (pullback.condition (f := previousToCycles) (g := cyclesMap (S := S))).symm := by
      -- Proof comment: this is the functoriality of kernels for the composite square obtained by
      -- first forgetting the chosen pullback cover and then using the owner pullback square.
      ext
      simp [extensionCoverToPrevious, extensionCoverToStageCycles, Category.assoc]
    rw [hComp]
    infer_instance
  rw [extendCutoffKernelMapFactorization (S := S)]
  infer_instance

/-- Helper for Lemma 13.15.4: above the cutoff degree, the raw extension inherits the stage
homology isomorphisms from the previous stage. -/
private theorem extend_tail_homologyMap_isIso
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ} (hi : n < i) :
    IsIso (HomologicalComplex.homologyMap (extend_raw_α (S := S)) i) := by
  -- Proof comment: on the whole short-complex window around `i`, the raw extension agrees with
  -- the previous stage up to the canonical `eqToIso` transports on objects.
  have hiPrev : n ≤ i - 1 := by
    omega
  have hiNext : n ≤ i + 1 := by
    omega
  let e₁ :
      ((extend_raw_complex (S := S)).X (i - 1)) ≅ S.Q.X (i - 1) :=
    eqToIso (extend_raw_complex_X_of_le (S := S) (i := i - 1) hiPrev)
  let e₂ :
      ((extend_raw_complex (S := S)).X i) ≅ S.Q.X i :=
    eqToIso (extend_raw_complex_X_of_le (S := S) (i := i) (by omega))
  let e₃ :
      ((extend_raw_complex (S := S)).X (i + 1)) ≅ S.Q.X (i + 1) :=
    eqToIso (extend_raw_complex_X_of_le (S := S) (i := i + 1) hiNext)
  have hcomm12 :
      e₁.hom ≫ (S.Q.sc' (i - 1) i (i + 1)).f =
        ((extend_raw_complex (S := S)).sc' (i - 1) i (i + 1)).f ≫ e₂.hom := by
    -- Proof comment: postcompose the tail differential formula with the middle transport.
    simpa [e₁, e₂, HomologicalComplex.sc', Category.assoc] using
      (congrArg
        (fun t ↦ t ≫ e₂.hom)
        (extend_raw_complex_d_of_le (S := S) (i := i - 1) (j := i) hiPrev (by omega))).symm
  have hcomm23 :
      e₂.hom ≫ (S.Q.sc' (i - 1) i (i + 1)).g =
        ((extend_raw_complex (S := S)).sc' (i - 1) i (i + 1)).g ≫ e₃.hom := by
    -- Proof comment: the right differential is treated by the same tail transport.
    simpa [e₂, e₃, HomologicalComplex.sc', Category.assoc] using
      (congrArg
        (fun t ↦ t ≫ e₃.hom)
        (extend_raw_complex_d_of_le (S := S) (i := i) (j := i + 1) (by omega) (by omega))).symm
  let eSc :
      ((extend_raw_complex (S := S)).sc' (i - 1) i (i + 1)) ≅
        (S.Q.sc' (i - 1) i (i + 1)) :=
    CategoryTheory.ShortComplex.isoMk e₁ e₂ e₃ hcomm12 hcomm23
  let eArrow :
      CategoryTheory.Arrow.mk
          ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (i - 1) i (i + 1)).map
            (extend_raw_α (S := S))) ≅
        CategoryTheory.Arrow.mk
          ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (i - 1) i (i + 1)).map S.α) :=
    CategoryTheory.Arrow.isoMk eSc (Iso.refl _)
      (by
        -- Proof comment: after rewriting the three tail components, the mapped short-complex
        -- morphism is exactly the stage map.
        ext
        · simpa [e₁] using (extend_raw_α_f_of_le (S := S) (i := i - 1) hiPrev).symm
        · simpa [e₂] using (extend_raw_α_f_of_le (S := S) (i := i) (by omega)).symm
        · simpa [e₃] using (extend_raw_α_f_of_le (S := S) (i := i + 1) hiNext).symm)
  have hStageAt : QuasiIsoAt S.α i := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact S.homologyMap_isIso i hi
  have hStageSc :
      CategoryTheory.ShortComplex.QuasiIso
        ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (i - 1) i (i + 1)).map S.α) := by
    rw [← quasiIsoAt_iff' (f := S.α) (i := i - 1) (j := i) (k := i + 1) (by simp) (by simp)]
    exact hStageAt
  have hExtendSc :
      CategoryTheory.ShortComplex.QuasiIso
        ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (i - 1) i (i + 1)).map
          (extend_raw_α (S := S))) := by
    exact
      (CategoryTheory.ShortComplex.quasiIso_iff_of_arrow_mk_iso
        _ _ eArrow).2 hStageSc
  have hExtendAt : QuasiIsoAt (extend_raw_α (S := S)) i := by
    rw [quasiIsoAt_iff' (f := extend_raw_α (S := S)) (i := i - 1) (j := i) (k := i + 1)
      (by simp) (by simp)]
    exact hExtendSc
  rw [quasiIsoAt_iff_isIso_homologyMap] at hExtendAt
  exact hExtendAt

/-- Helper for Lemma 13.15.4: a short-complex window comparison with a bounded-above replacement
stage transfers `QuasiIsoAt` to the compared map. -/
private theorem quasiIsoAt_of_windowComparison
    {a n i : ℤ} {K Q : CochainComplex A ℤ}
    (S : BoundedAboveReplacementStage (P := P) a K n) (α : Q ⟶ K)
    (hleft : S.Q.X (i - 1) = Q.X (i - 1))
    (hmid : S.Q.X i = Q.X i)
    (hright : S.Q.X (i + 1) = Q.X (i + 1))
    (hcomm12 :
      eqToHom hleft.symm ≫ (S.Q.sc' (i - 1) i (i + 1)).f =
        (Q.sc' (i - 1) i (i + 1)).f ≫ eqToHom hmid.symm)
    (hcomm23 :
      eqToHom hmid.symm ≫ (S.Q.sc' (i - 1) i (i + 1)).g =
        (Q.sc' (i - 1) i (i + 1)).g ≫ eqToHom hright.symm)
    (hαleft :
      eqToHom hleft.symm ≫ S.α.f (i - 1) = α.f (i - 1))
    (hαmid :
      eqToHom hmid.symm ≫ S.α.f i = α.f i)
    (hαright :
      eqToHom hright.symm ≫ S.α.f (i + 1) = α.f (i + 1))
    (hStageAt : QuasiIsoAt S.α i) :
    QuasiIsoAt α i := by
  let e₁ : Q.X (i - 1) ≅ S.Q.X (i - 1) :=
    eqToIso hleft.symm
  let e₂ : Q.X i ≅ S.Q.X i :=
    eqToIso hmid.symm
  let e₃ : Q.X (i + 1) ≅ S.Q.X (i + 1) :=
    eqToIso hright.symm
  let eSc :
      Q.sc' (i - 1) i (i + 1) ≅ S.Q.sc' (i - 1) i (i + 1) :=
    CategoryTheory.ShortComplex.isoMk e₁ e₂ e₃ hcomm12 hcomm23
  let eArrow :
      CategoryTheory.Arrow.mk
          ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (i - 1) i (i + 1)).map α) ≅
        CategoryTheory.Arrow.mk
          ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (i - 1) i (i + 1)).map S.α) :=
    CategoryTheory.Arrow.isoMk eSc (Iso.refl _)
      (by
        -- Proof comment: the compared short-complex map matches the stage map componentwise
        -- after transporting the three source objects.
        ext
        · simpa [e₁] using hαleft
        · simpa [e₂] using hαmid
        · simpa [e₃] using hαright)
  have hStageSc :
      CategoryTheory.ShortComplex.QuasiIso
        ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (i - 1) i (i + 1)).map S.α) := by
    -- Proof comment: rewrite the stagewise homology isomorphism as the corresponding short-
    -- complex quasi-isomorphism.
    rw [← quasiIsoAt_iff' (f := S.α) (i := i - 1) (j := i) (k := i + 1) (by simp) (by simp)]
    exact hStageAt
  have hComparedSc :
      CategoryTheory.ShortComplex.QuasiIso
        ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (i - 1) i (i + 1)).map α) := by
    -- Proof comment: the arrow isomorphism moves the stage quasi-isomorphism to the compared
    -- window for `α`.
    exact
      (CategoryTheory.ShortComplex.quasiIso_iff_of_arrow_mk_iso
        _ _ eArrow).2 hStageSc
  -- Proof comment: finally read the compared short-complex quasi-isomorphism back as
  -- `QuasiIsoAt α i`.
  rw [quasiIsoAt_iff' (f := α) (i := i - 1) (j := i) (k := i + 1) (by simp) (by simp)]
  exact hComparedSc

/-- Helper for Chap13 Lemma 13 15 4: at the cutoff step, the raw source term maps first into the
old cycles object before entering the old middle degree. -/
private noncomputable def extendCutoffToCycles
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extend_raw_complex (S := S)).X (n - 1) ⟶ kernel (S.Q.d n (n + 1)) :=
  eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫ extensionCoverToStageCycles (S := S)

/-- Helper for Chap13 Lemma 13 15 4: the old cycles object includes into the cutoff middle term of
the raw extension through the inherited tail identification. -/
private noncomputable def extendCutoffCyclesInclusion
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    kernel (S.Q.d n (n + 1)) ⟶ (extend_raw_complex (S := S)).X n :=
  kernel.ι (S.Q.d n (n + 1)) ≫
    eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)).symm

/-- Helper for Chap13 Lemma 13 15 4: the cutoff differential is the composition of the new map to
old cycles with the inherited inclusion of those cycles into the old middle degree. -/
private theorem extendCutoffToCycles_comp_inclusion
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extendCutoffToCycles (S := S) ≫ extendCutoffCyclesInclusion (S := S) =
      (extend_raw_complex (S := S)).d (n - 1) n := by
  -- Proof comment: this is just the explicit cutoff differential rewritten so that the new map to
  -- cycles and the inherited cycles inclusion are exposed as separate factors.
  simpa [extendCutoffToCycles, extendCutoffCyclesInclusion, Category.assoc,
    extendRawCutoffD] using
    (extend_raw_complex_d_cutoff (S := S)).symm

/-- Helper for Chap13 Lemma 13 15 4: after precomposing by the cutoff source transport, the
pullback compatibility of the chosen cover becomes a square from the raw cutoff term to the old
cycles object. -/
private theorem extendCutoffToCycles_condition
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extendCutoffToCycles (S := S) ≫ cyclesMap (S := S) =
      extendRawCutoffα (S := S) ≫ previousToCycles (K := K) (n := n) := by
  -- Proof comment: transport the original pullback equation from the chosen cover object to the
  -- actual cutoff term of the packaged raw extension.
  simpa [extendCutoffToCycles, extendRawCutoffα, Category.assoc] using
    congrArg
      (fun k ↦ eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫ k)
      (extensionCover_condition (S := S)).symm

/-- Helper for Chap13 Lemma 13 15 4: the inherited cycles inclusion still lands in the kernel of
the degree-`n` tail differential of the raw extension. -/
private theorem extendCutoffCyclesInclusion_comp_d
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extendCutoffCyclesInclusion (S := S) ≫
        (extend_raw_complex (S := S)).d n (n + 1) = 0 := by
  -- Proof comment: rewrite the raw tail differential once and cancel the harmless tail
  -- transports, leaving the old kernel condition in the previous stage.
  let hXsucc :
      (extend_raw_complex (S := S)).X (n + 1) = S.Q.X (n + 1) :=
    extend_raw_complex_X_of_le (S := S) (i := n + 1) (by omega)
  have hg :
      (extend_raw_complex (S := S)).d n (n + 1) =
        eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)) ≫
          S.Q.d n (n + 1) ≫ eqToHom hXsucc.symm := by
    simpa using
      extend_raw_complex_d_of_le (S := S) (i := n) (j := n + 1) le_rfl (by omega)
  rw [hg]
  simp [extendCutoffCyclesInclusion, Category.assoc]

/-- Helper for Chap13 Lemma 13 15 4: the explicit cutoff cycles object is a kernel of the degree
`n` tail differential in the packaged raw extension. -/
private noncomputable def extendCutoffCyclesIsKernel
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsLimit (KernelFork.ofι (extendCutoffCyclesInclusion (S := S))
      (extendCutoffCyclesInclusion_comp_d (S := S))) := by
  -- Proof comment: transport a cycle in the packaged cutoff window back to the unchanged stage
  -- object in degree `n`, then use the ordinary kernel universal property there.
  refine KernelFork.IsLimit.ofι (extendCutoffCyclesInclusion (S := S))
    (extendCutoffCyclesInclusion_comp_d (S := S))
    (fun {Z} k hk ↦ by
      let hXsucc :
          (extend_raw_complex (S := S)).X (n + 1) = S.Q.X (n + 1) :=
        extend_raw_complex_X_of_le (S := S) (i := n + 1) (by omega)
      have hd :
          (extend_raw_complex (S := S)).d n (n + 1) =
            eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)) ≫
              S.Q.d n (n + 1) ≫ eqToHom hXsucc.symm := by
        simpa using
          extend_raw_complex_d_of_le (S := S) (i := n) (j := n + 1) le_rfl (by omega)
      have hk' : (k ≫ eqToHom (extend_raw_complex_X_at_cutoff_target (S := S))) ≫
          S.Q.d n (n + 1) = 0 := by
        rw [hd] at hk
        exact (cancel_mono (eqToHom hXsucc.symm)).1 (by simpa [Category.assoc] using hk)
      exact kernel.lift (S.Q.d n (n + 1))
        (k ≫ eqToHom (extend_raw_complex_X_at_cutoff_target (S := S))) hk')
    (fun {Z} k hk ↦ by
      simp [extendCutoffCyclesInclusion, Category.assoc])
    (fun {Z} k hk m hm ↦ by
      apply (cancel_mono (kernel.ι (S.Q.d n (n + 1)))).1
      apply (cancel_mono (eqToHom (extend_raw_complex_X_at_cutoff_target (S := S)).symm)).1
      simpa [extendCutoffCyclesInclusion, Category.assoc] using
        hm.trans ((by
          simp [extendCutoffCyclesInclusion, Category.assoc]) : _))

/-- Helper for Chap13 Lemma 13 15 4: the source boundary map of the cutoff short-complex window
is exactly the explicit morphism from the new cutoff term to the old cycles object. -/
private theorem extendCutoffToCycles_eq_lift
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extendCutoffCyclesIsKernel (S := S)).lift
        (KernelFork.ofι ((extend_raw_complex (S := S)).d (n - 1) n)
          (by simpa using (extend_raw_complex (S := S)).d_comp_d (n - 1) n (n + 1))) =
      extendCutoffToCycles (S := S) := by
  -- Proof comment: both maps into the explicit cycles object compose with the cutoff inclusion to
  -- the same packaged differential, so the kernel universal property identifies them.
  apply Fork.IsLimit.hom_ext (extendCutoffCyclesIsKernel (S := S))
  calc
    (extendCutoffCyclesIsKernel (S := S)).lift
          (KernelFork.ofι ((extend_raw_complex (S := S)).d (n - 1) n)
            (by simpa using (extend_raw_complex (S := S)).d_comp_d (n - 1) n (n + 1))) ≫
        extendCutoffCyclesInclusion (S := S)
        = (extend_raw_complex (S := S)).d (n - 1) n := by
            simpa using
              (@Fork.IsLimit.lift_ι _ _ _ _ _ _ _
                (KernelFork.ofι ((extend_raw_complex (S := S)).d (n - 1) n)
                  (by simpa using (extend_raw_complex (S := S)).d_comp_d (n - 1) n (n + 1)))
                (extendCutoffCyclesIsKernel (S := S)))
    _ = extendCutoffToCycles (S := S) ≫ extendCutoffCyclesInclusion (S := S) := by
          symm
          exact extendCutoffToCycles_comp_inclusion (S := S)

/-- Helper for Chap13 Lemma 13 15 4: the explicit source cutoff cycles projection kills the
cutoff boundary map to the old cycles object. -/
private theorem extendCutoffSourceLeftHomologyData_wπ
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extendCutoffCyclesIsKernel (S := S)).lift
          (KernelFork.ofι ((extend_raw_complex (S := S)).d (n - 1) n)
            (by simpa using (extend_raw_complex (S := S)).d_comp_d (n - 1) n (n + 1))) ≫
        cokernel.π (extendCutoffToCycles (S := S)) = 0 := by
  -- Proof comment: after identifying the source boundary map with `extendCutoffToCycles`, this is
  -- the defining cokernel relation.
  rw [extendCutoffToCycles_eq_lift (S := S)]
  exact cokernel.condition (extendCutoffToCycles (S := S))

/-- Helper for Chap13 Lemma 13 15 4: the explicit cycles inclusion is the kernel map in the
cutoff short-complex window. -/
private theorem extendCutoffSourceLeftHomologyData_wi
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extendCutoffCyclesInclusion (S := S) ≫
        ((extend_raw_complex (S := S)).sc' (n - 1) n (n + 1)).g = 0 := by
  -- Proof comment: the cutoff short-complex right differential is the degree-`n` tail map of
  -- the packaged raw extension, so this is exactly the inherited kernel relation.
  simpa [HomologicalComplex.sc'] using
    extendCutoffCyclesInclusion_comp_d (S := S)

/-- Helper for Chap13 Lemma 13 15 4: the explicit cycles object is a kernel in the cutoff
short-complex window. -/
private noncomputable def extendCutoffSourceLeftHomologyData_hi
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsLimit (KernelFork.ofι (extendCutoffCyclesInclusion (S := S))
      (extendCutoffSourceLeftHomologyData_wi (S := S))) := by
  -- Proof comment: the cutoff short-complex right differential is definitionally the raw degree-`n`
  -- differential, so the already constructed kernel carries over directly.
  simpa [HomologicalComplex.sc'] using extendCutoffCyclesIsKernel (S := S)

/-- Helper for Chap13 Lemma 13 15 4: the explicit source cutoff boundary map obtained from the
chosen kernel is the canonical map to the old cycles object. -/
private theorem extendCutoffSourceBoundary_eq_extendCutoffToCycles
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extendCutoffSourceLeftHomologyData_hi (S := S)).lift
          (KernelFork.ofι
            (((extend_raw_complex (S := S)).sc' (n - 1) n (n + 1)).f)
            (((extend_raw_complex (S := S)).sc' (n - 1) n (n + 1)).zero)) =
      extendCutoffToCycles (S := S) := by
  -- Proof comment: with the chosen kernel witness, the source `f'` is exactly the canonical lift
  -- of the cutoff differential into the cycles object.
  simpa [HomologicalComplex.sc'] using extendCutoffToCycles_eq_lift (S := S)

/-- Helper for Chap13 Lemma 13 15 4: the explicit cutoff source boundary map vanishes after the
projection to the chosen cokernel object. -/
private theorem extendCutoffSourceLeftHomologyData_wπ'
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    (extendCutoffSourceLeftHomologyData_hi (S := S)).lift
          (KernelFork.ofι
            (((extend_raw_complex (S := S)).sc' (n - 1) n (n + 1)).f)
            (((extend_raw_complex (S := S)).sc' (n - 1) n (n + 1)).zero)) ≫
        cokernel.π (extendCutoffToCycles (S := S)) = 0 := by
  -- Proof comment: after identifying the source `f'` with `extendCutoffToCycles`, this is the
  -- defining cokernel relation.
  rw [extendCutoffSourceBoundary_eq_extendCutoffToCycles (S := S)]
  exact cokernel.condition (extendCutoffToCycles (S := S))

/-- Helper for Chap13 Lemma 13 15 4: the chosen cokernel object is a cokernel for the cutoff
source boundary map in the explicit left homology data. -/
private noncomputable def extendCutoffSourceLeftHomologyData_hπ
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsColimit (CokernelCofork.ofπ (cokernel.π (extendCutoffToCycles (S := S)))
      (extendCutoffSourceLeftHomologyData_wπ' (S := S))) := by
  let f :
      ((extend_raw_complex (S := S)).X (n - 1)) ⟶ kernel (S.Q.d n (n + 1)) :=
    (extendCutoffSourceLeftHomologyData_hi (S := S)).lift
      (KernelFork.ofι
        (((extend_raw_complex (S := S)).sc' (n - 1) n (n + 1)).f)
        (((extend_raw_complex (S := S)).sc' (n - 1) n (n + 1)).zero))
  -- Proof comment: transport the standard chosen cokernel of `extendCutoffToCycles` across the
  -- equality identifying the explicit source boundary map with that canonical map.
  have hCanonical :
      IsColimit
        (CokernelCofork.ofπ (cokernel.π (extendCutoffToCycles (S := S)))
          (cokernel.condition (extendCutoffToCycles (S := S)))) := by
    refine IsColimit.ofIsoColimit (cokernelIsCokernel (extendCutoffToCycles (S := S))) ?_
    exact Cofork.ext (Iso.refl _) (by simp)
  have hIff :
      ∀ ⦃W : A⦄ (φ : kernel (S.Q.d n (n + 1)) ⟶ W),
        extendCutoffToCycles (S := S) ≫ φ = 0 ↔ f ≫ φ = 0 := by
    intro W φ
    simpa [f, extendCutoffSourceBoundary_eq_extendCutoffToCycles (S := S)]
  simpa [f, extendCutoffSourceBoundary_eq_extendCutoffToCycles (S := S)] using
    (CokernelCofork.isColimitOfIsColimitOfIff' hCanonical f hIff)

private noncomputable def extendCutoffSourceLeftHomologyData
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    ((extend_raw_complex (S := S)).sc' (n - 1) n (n + 1)).LeftHomologyData :=
  { K := kernel (S.Q.d n (n + 1))
    H := cokernel (extendCutoffToCycles (S := S))
    i := extendCutoffCyclesInclusion (S := S)
    π := cokernel.π (extendCutoffToCycles (S := S))
    wi := extendCutoffSourceLeftHomologyData_wi (S := S)
    hi := extendCutoffSourceLeftHomologyData_hi (S := S)
    wπ := extendCutoffSourceLeftHomologyData_wπ' (S := S)
    hπ := extendCutoffSourceLeftHomologyData_hπ (S := S) }

/-- Helper for Chap13 Lemma 13 15 4: the source cutoff left-homology boundary map is the explicit
map from the new cutoff term to the old cycles object. -/
private theorem extendCutoffSourceLeftHomologyData_f'
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    ((extendCutoffSourceLeftHomologyData (S := S)).f') = extendCutoffToCycles (S := S) := by
  -- Proof comment: the bundled source `LeftHomologyData` uses exactly the same kernel witness as
  -- the explicit cutoff boundary map above.
  simpa [extendCutoffSourceLeftHomologyData, CategoryTheory.ShortComplex.LeftHomologyData.f'] using
    extendCutoffSourceBoundary_eq_extendCutoffToCycles (S := S)

/-- Helper for Chap13 Lemma 13 15 4: the target cutoff window uses the standard kernel/cokernel
left homology data on `K.sc' (n - 1) n (n + 1)`. -/
private noncomputable def extendCutoffTargetLeftHomologyData :
    (K.sc' (n - 1) n (n + 1)).LeftHomologyData :=
  CategoryTheory.ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel (K.sc' (n - 1) n (n + 1))

/-- Helper for Chap13 Lemma 13 15 4: the target cutoff left-homology boundary map is the usual
map from `K.X (n - 1)` to cycles in degree `n`. -/
private theorem extendCutoffTargetLeftHomologyData_f' :
    (extendCutoffTargetLeftHomologyData (K := K) (n := n)).f' =
      previousToCycles (K := K) (n := n) := by
  -- Proof comment: the target data is the standard kernel/cokernel choice, whose boundary map is
  -- definitionally the canonical kernel lift.
  rfl

/-- Helper for Chap13 Lemma 13 15 4: the explicit cutoff boundary map factors through the chosen
cover object and the owner pullback leg into the old cycles object. -/
private theorem extendCutoffToCycles_eq_coverMap_comp_pullbackSnd
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    extendCutoffToCycles (S := S) =
      eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫
        extensionCoverMap (S := S) ≫
          pullback.snd previousToCycles (cyclesMap (S := S)) := by
  -- Proof comment: unfold the chosen map to old cycles and expose the owner pullback leg used by
  -- the source cover.
  simp [extendCutoffToCycles, extensionCoverToStageCycles, Category.assoc]

/-- Helper for Chap13 Lemma 13 15 4: the left-homology map at the cutoff first passes from the
chosen cover to the owner pullback cokernel. -/
private noncomputable def extendCutoffCoverCokernelMap
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    cokernel (extendCutoffToCycles (S := S)) ⟶
      cokernel (pullback.snd previousToCycles (cyclesMap (S := S))) :=
  cokernel.map
    (extendCutoffToCycles (S := S))
    (pullback.snd previousToCycles (cyclesMap (S := S)))
    (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫ extensionCoverMap (S := S))
    (𝟙 _)
    (by
      rw [Category.comp_id]
      simpa [Category.assoc] using
        extendCutoffToCycles_eq_coverMap_comp_pullbackSnd (S := S))

/-- Helper for Lemma 13.15.4: replacing the source of `pullback.snd` by the chosen epi cover does
not change its cokernel. -/
private theorem extendCutoffCoverCokernelMap_isIso
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsIso (extendCutoffCoverCokernelMap (S := S)) := by
  let e :
      (extend_raw_complex (S := S)).X (n - 1) ⟶ extensionPullback (S := S) :=
    eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫ extensionCoverMap (S := S)
  letI : Epi e := by
    -- Proof comment: the comparison to the pullback differs from the chosen cover map only by a
    -- transport at the source, so it remains epimorphic.
    letI : Epi (extensionCoverMap (S := S)) := extensionCover_epi (S := S)
    letI : IsIso (eqToHom (extend_raw_complex_X_cutoff (S := S))) := by infer_instance
    change Epi (eqToHom (extend_raw_complex_X_cutoff (S := S)) ≫ extensionCoverMap (S := S))
    infer_instance
  -- Proof comment: `cokernel.map` along an epi source change and an isomorphic target is already
  -- an isomorphism in the ambient kernel/cokernel API.
  simpa [extendCutoffCoverCokernelMap, e] using
    (inferInstance :
      IsIso
        (cokernel.map
          (extendCutoffToCycles (S := S))
          (pullback.snd previousToCycles (cyclesMap (S := S)))
          e
          (𝟙 _)
          (by
            rw [Category.comp_id]
            simpa [e, Category.assoc] using
              extendCutoffToCycles_eq_coverMap_comp_pullbackSnd (S := S))))

/-- Helper for Chap13 Lemma 13 15 4: the owner pushout square identifies the pullback cokernel
with the actual target cutoff left homology object. -/
private theorem extensionPullbackTargetCokernelMap_isIso
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsIso
      (cokernel.map
        (pullback.snd previousToCycles (cyclesMap (S := S)))
        (previousToCycles (K := K) (n := n))
        (pullback.fst previousToCycles (cyclesMap (S := S)))
        (cyclesMap (S := S))
        (pullback.condition
          (f := previousToCycles)
          (g := cyclesMap (S := S))).symm) := by
  -- Proof comment: the owner pullback square is also a pushout square, so the horizontal cokernel
  -- comparison landing in the actual target left homology object is invertible.
  simpa using CategoryTheory.Limits.isIso_cokernel_map_of_isPushout
    (extensionPullback_isPushout (S := S))

/-- Helper for Chap13 Lemma 13 15 4: the cutoff short-complex morphism induces the expected
cycles and homology maps on the explicit source/target left homology data. -/
private noncomputable def extendCutoffLeftHomologyMapData
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    CategoryTheory.ShortComplex.LeftHomologyMapData
      (((HomologicalComplex.shortComplexFunctor' A (up ℤ) (n - 1) n (n + 1)).map
        (extend_raw_α (S := S))))
      (extendCutoffSourceLeftHomologyData (S := S))
      (extendCutoffTargetLeftHomologyData (K := K) (n := n)) := default

/-- Helper for Chap13 Lemma 13 15 4: the cutoff left-homology map of the raw extension is
the composition of the cover-induced cokernel comparison with the owner pushout comparison. -/
private theorem extendCutoffLeftHomologyMap_eq_factorizedCokernelMap
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    CategoryTheory.ShortComplex.leftHomologyMap'
        (((HomologicalComplex.shortComplexFunctor' A (up ℤ) (n - 1) n (n + 1)).map
          (extend_raw_α (S := S))))
        (extendCutoffSourceLeftHomologyData (S := S))
        (extendCutoffTargetLeftHomologyData (K := K) (n := n)) =
      extendCutoffCoverCokernelMap (S := S) ≫
        cokernel.map
          (pullback.snd previousToCycles (cyclesMap (S := S)))
          (previousToCycles (K := K) (n := n))
          (pullback.fst previousToCycles (cyclesMap (S := S)))
          (cyclesMap (S := S))
          (pullback.condition
            (f := previousToCycles)
            (g := cyclesMap (S := S))).symm := by
  let targetCokernelMap :
      cokernel (pullback.snd previousToCycles (cyclesMap (S := S))) ⟶
        cokernel (previousToCycles (K := K) (n := n)) :=
    cokernel.map
      (pullback.snd previousToCycles (cyclesMap (S := S)))
      (previousToCycles (K := K) (n := n))
      (pullback.fst previousToCycles (cyclesMap (S := S)))
      (cyclesMap (S := S))
      (pullback.condition
        (f := previousToCycles)
        (g := cyclesMap (S := S))).symm
  let γFactorized :
      CategoryTheory.ShortComplex.LeftHomologyMapData
        (((HomologicalComplex.shortComplexFunctor' A (up ℤ) (n - 1) n (n + 1)).map
          (extend_raw_α (S := S))))
        (extendCutoffSourceLeftHomologyData (S := S))
        (extendCutoffTargetLeftHomologyData (K := K) (n := n)) :=
    {
    φK := cyclesMap (S := S)
    φH := extendCutoffCoverCokernelMap (S := S) ≫ targetCokernelMap
    commi := by
      -- Proof comment: on cycles, the cutoff window map is the inherited stage cycles map after
      -- removing the transport that identifies degree `n` of the raw extension with `S.Q.X n`.
      have h1 :
          cyclesMap (S := S) ≫ (extendCutoffTargetLeftHomologyData (K := K) (n := n)).i =
            kernel.ι (S.Q.d n (n + 1)) ≫ S.α.f n := by
        change cyclesMap (S := S) ≫ kernel.ι (K.d n (n + 1)) =
          kernel.ι (S.Q.d n (n + 1)) ≫ S.α.f n
        exact cyclesMap_comp_ι (S := S)
      have h2 :
          kernel.ι (S.Q.d n (n + 1)) ≫ S.α.f n =
            (extendCutoffSourceLeftHomologyData (S := S)).i ≫
              ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (n - 1) n (n + 1)).map
                (extend_raw_α (S := S))).τ₂ := by
        simp [extendCutoffSourceLeftHomologyData, extendCutoffCyclesInclusion,
          extend_raw_α_f_at_cutoff_target (S := S), Category.assoc]
      exact h1.trans h2
    commf' := by
      -- Proof comment: the source boundary map is exactly the cutoff map to old cycles, whose
      -- compatibility with `cyclesMap` is the pullback square used to choose the cover.
      simpa [targetCokernelMap, extendCutoffSourceLeftHomologyData_f' (S := S),
        extendCutoffTargetLeftHomologyData_f' (K := K) (n := n),
        extend_raw_α_f_cutoff (S := S)] using
        (extendCutoffToCycles_condition (S := S))
    commπ := by
      -- Proof comment: each `cokernel.map` is characterized by its effect after precomposition
      -- with the source cokernel projection, so the composite gives the advertised factorization.
      have h1 :
          (extendCutoffSourceLeftHomologyData (S := S)).π ≫
              (extendCutoffCoverCokernelMap (S := S) ≫ targetCokernelMap) =
            cokernel.π
              (pullback.snd previousToCycles (cyclesMap (S := S))) ≫ targetCokernelMap := by
        simp [extendCutoffSourceLeftHomologyData, extendCutoffCoverCokernelMap,
          targetCokernelMap, Category.assoc]
      have h2 :
          cokernel.π
              (pullback.snd previousToCycles (cyclesMap (S := S))) ≫ targetCokernelMap =
            cyclesMap (S := S) ≫ cokernel.π (previousToCycles (K := K) (n := n)) := by
        simp [targetCokernelMap, Category.assoc]
      have h3 :
          cyclesMap (S := S) ≫ cokernel.π (previousToCycles (K := K) (n := n)) =
            cyclesMap (S := S) ≫
              (extendCutoffTargetLeftHomologyData (K := K) (n := n)).π := by
        rfl
      exact h1.trans (h2.trans h3)
    }
  exact γFactorized.leftHomologyMap'_eq

/-- Helper for Lemma 13.15.4: the new homology map at the cutoff degree of the raw extension is
an isomorphism. -/
private theorem extend_homologyMap_isIso_at_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsIso (HomologicalComplex.homologyMap (extend_raw_α (S := S)) n) := by
  letI : IsIso S.extendCutoffCoverCokernelMap :=
    extendCutoffCoverCokernelMap_isIso (S := S)
  letI :
      IsIso
        (cokernel.map
          (pullback.snd previousToCycles (cyclesMap (S := S)))
          (previousToCycles (K := K) (n := n))
          (pullback.fst previousToCycles (cyclesMap (S := S)))
          (cyclesMap (S := S))
          (pullback.condition
            (f := previousToCycles)
            (g := cyclesMap (S := S))).symm) :=
    extensionPullbackTargetCokernelMap_isIso (S := S)
  have hSc :
      CategoryTheory.ShortComplex.QuasiIso
        ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (n - 1) n (n + 1)).map
          (extend_raw_α (S := S))) := by
    -- Proof comment: the cutoff left-homology map factors through two already invertible cokernel
    -- comparisons, so the cutoff short-complex morphism is a quasi-isomorphism.
    rw [CategoryTheory.ShortComplex.quasiIso_iff_isIso_leftHomologyMap'
      (((HomologicalComplex.shortComplexFunctor' A (up ℤ) (n - 1) n (n + 1)).map
        (extend_raw_α (S := S))))
      (extendCutoffSourceLeftHomologyData (S := S))
      (extendCutoffTargetLeftHomologyData (K := K) (n := n))]
    rw [extendCutoffLeftHomologyMap_eq_factorizedCokernelMap (S := S)]
    exact
      IsIso.comp_isIso'
        (extendCutoffCoverCokernelMap_isIso (S := S))
        (extensionPullbackTargetCokernelMap_isIso (S := S))
  have hAt : QuasiIsoAt (extend_raw_α (S := S)) n := by
    -- Proof comment: convert the cutoff short-complex quasi-isomorphism back to the degree-`n`
    -- cochain-complex statement via the standard `sc'` window equivalence.
    rw [quasiIsoAt_iff' (f := extend_raw_α (S := S)) (i := n - 1) (j := n) (k := n + 1)
      (by simp) (by simp)]
    exact hSc
  rw [quasiIsoAt_iff_isIso_homologyMap] at hAt
  exact hAt

/-- Helper for Lemma 13.15.4: one step of the descending induction, with the source-faithful
bound `n ≤ a + 1` recorded explicitly in the stage API. -/
private noncomputable def extend
    (S : BoundedAboveReplacementStage (P := P) a K n) (hn : n ≤ a + 1) :
    BoundedAboveReplacementStage (P := P) a K (n - 1) := by
  -- Proof comment: the new stage keeps the packaged raw extension and comparison map, while the
  -- cutoff homology/cycles facts are supplied by the dedicated transport lemmas above.
  refine
    { Q := extend_raw_complex (S := S)
      α := extend_raw_α (S := S)
      strictlyLE := extend_raw_complex_strictlyLE (S := S) hn
      zero_below := ?_
      term_mem := ?_
      term_epi := ?_
      homologyMap_isIso := ?_
      cycles_epi := extend_cycles_epi_via_kernel_transport (S := S) }
  · intro i hi
    exact extend_raw_complex_zero_below (S := S) hi
  · intro i hi
    exact extend_raw_complex_term_mem (S := S) hi
  · intro i hi
    exact extend_raw_α_epi (S := S) hi
  · intro i hi
    by_cases hcut : i = n
    · -- Proof comment: the new degree `n` is the load-bearing cutoff step treated separately.
      subst hcut
      exact extend_homologyMap_isIso_at_cutoff (S := S)
    · -- Proof comment: every higher degree lies on the inherited tail, so the old stage
      -- quasi-isomorphism data applies after the tail identifications.
      have htail : n < i := by
        omega
      exact extend_tail_homologyMap_isIso (S := S) htail

end BoundedAboveReplacementStage

/-- Helper for Lemma 13.15.4: a direct comparison of differentials on the left side of the
realized window yields the `f`-commutativity hypothesis for
`quasiIsoAt_of_windowComparison`. -/
private theorem realizedWindowLeftDifferentialEq
    {a n i : ℤ} {K Q : CochainComplex A ℤ}
    (S : BoundedAboveReplacementStage (P := P) a K n)
    (hstageLeft : S.Q.X (i - 1) = Q.X (i - 1))
    (hstageMid : S.Q.X i = Q.X i)
    (hleftD :
      eqToHom hstageLeft.symm ≫ S.Q.d (i - 1) i =
        Q.d (i - 1) i ≫ eqToHom hstageMid.symm) :
    eqToHom hstageLeft.symm ≫ ((S.Q.sc' (i - 1) i (i + 1)).f) =
      (Q.sc' (i - 1) i (i + 1)).f ≫ eqToHom hstageMid.symm := by
  -- Proof comment: `sc'.f` is the underlying differential, so the claimed commutativity is just
  -- the transported differential comparison.
  simpa [HomologicalComplex.sc'] using hleftD

/-- Helper for Lemma 13.15.4: comparing the right differential of a stage window with the
realized complex yields the `g`-commutativity hypothesis for
`quasiIsoAt_of_windowComparison`. -/
private theorem realizedWindowRightDifferentialEq
    {a n i : ℤ} {K Q : CochainComplex A ℤ}
    (S : BoundedAboveReplacementStage (P := P) a K n)
    (hstageMid : S.Q.X i = Q.X i)
    (hstageRight : S.Q.X (i + 1) = Q.X (i + 1))
    (hrightD :
      eqToHom hstageMid.symm ≫ S.Q.d i (i + 1) =
        Q.d i (i + 1) ≫ eqToHom hstageRight.symm) :
    eqToHom hstageMid.symm ≫ ((S.Q.sc' (i - 1) i (i + 1)).g) =
      (Q.sc' (i - 1) i (i + 1)).g ≫ eqToHom hstageRight.symm := by
  -- Proof comment: `sc'.g` is the underlying differential, so the result is the transported
  -- right-differential comparison itself.
  simpa [HomologicalComplex.sc'] using hrightD

/-- Helper for Lemma 13.15.4: once the middle comparison-map component is written using the
realized object equality, the desired transported equality follows by cancellation. -/
private theorem realizedWindowMidComponentEq
    {a n i : ℤ} {K Q : CochainComplex A ℤ}
    (S : BoundedAboveReplacementStage (P := P) a K n)
    (α : Q ⟶ K)
    (hstageMid : S.Q.X i = Q.X i)
    (hmidComponent : S.α.f i = eqToHom hstageMid ≫ α.f i) :
    eqToHom hstageMid.symm ≫ S.α.f i = α.f i := by
  -- Proof comment: precompose by the inverse transport and simplify the resulting `eqToHom`
  -- cancellation.
  simpa [Category.assoc, hstageMid] using
    congrArg (fun t ↦ eqToHom hstageMid.symm ≫ t) hmidComponent

/-- Helper for Lemma 13.15.4: composing the stage-tail comparison with the realized-tail
comparison gives the right comparison-map component required by the window transfer lemma. -/
private theorem realizedWindowRightComponentEq
    {a n i : ℤ} {K Q T : CochainComplex A ℤ}
    (S : BoundedAboveReplacementStage (P := P) a K n)
    (α : Q ⟶ K) (β : T ⟶ K)
    (hstageRightFromMid : S.Q.X (i + 1) = T.X (i + 1))
    (hrealizedRight : T.X (i + 1) = Q.X (i + 1))
    (hstageRight : S.Q.X (i + 1) = Q.X (i + 1))
    (hstageRight_def : hstageRight = hstageRightFromMid.trans hrealizedRight)
    (hmidTail : S.α.f (i + 1) = eqToHom hstageRightFromMid ≫ β.f (i + 1))
    (hrealizedTail : β.f (i + 1) = eqToHom hrealizedRight ≫ α.f (i + 1)) :
    eqToHom hstageRight.symm ≫ S.α.f (i + 1) = α.f (i + 1) := by
  -- Proof comment: substitute the two tail comparison formulas and then collapse the composite
  -- transport to the chosen right-hand object identification.
  rw [hmidTail, hrealizedTail, hstageRight_def]
  simp [Category.assoc]

/-- Helper for Lemma 13.15.4: the recursive construction lowers the cutoff by one at each step. -/
private def descendingCutoff (a : ℤ) : ℕ → ℤ
  | 0 => a + 1
  | m + 1 => descendingCutoff a m - 1

/-- Helper for Lemma 13.15.4: the recursive cutoff equals the closed form
`a + 1 - Int.ofNat m`. -/
private theorem descendingCutoff_eq (a : ℤ) :
    ∀ m : ℕ, descendingCutoff a m = a + 1 - Int.ofNat m
  | 0 => by simp [descendingCutoff]
  | m + 1 => by
      rw [descendingCutoff, descendingCutoff_eq a m]
      simp [Nat.cast_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 13.15.4: every recursive cutoff still lies at or below the initial bound
`a + 1`. -/
private theorem descendingCutoff_le_top (a : ℤ) (m : ℕ) :
    descendingCutoff a m ≤ a + 1 := by
  simpa [descendingCutoff_eq] using boundedAboveReplacementStage_index_le_cutoff a m

/-- Helper for Lemma 13.15.4: recursively descend the cutoff index by repeatedly extending the
bounded-above replacement stage. -/
private noncomputable def descendingReplacementStage
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m)
  | 0 => by
      simpa [descendingCutoff] using boundedAboveReplacementStage_base (P := P) a K hK
  | m + 1 =>
      BoundedAboveReplacementStage.extend
        (descendingReplacementStage a K hK m)
        (descendingCutoff_le_top a m)

/-- Helper for Lemma 13.15.4: the stage at depth `m + 1` is obtained by extending the stage at
depth `m`. -/
private theorem descendingReplacementStage_succ
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) (m : ℕ) :
    descendingReplacementStage (P := P) a K hK (m + 1) =
      BoundedAboveReplacementStage.extend
        (descendingReplacementStage (P := P) a K hK m)
        (descendingCutoff_le_top a m) :=
  rfl

/-- Helper for Lemma 13.15.4: increasing the recursive depth lowers the cutoff
`a + 1 - Int.ofNat m`. -/
private theorem descendingStageCutoffAntitone
    (a : ℤ) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    descendingCutoff a m₂ ≤ descendingCutoff a m₁ := by
  simpa [descendingCutoff_eq] using
    (show a + 1 - Int.ofNat m₂ ≤ a + 1 - Int.ofNat m₁ from by
      exact sub_le_sub_left (show (m₁ : ℤ) ≤ m₂ from by exact_mod_cast hm) (a + 1))

/-- Helper for Lemma 13.15.4: once the closed-form cutoff has reached a degree, so has the
recursive cutoff. -/
private theorem descendingCutoff_le_of_closedForm
    (a : ℤ) (m : ℕ) {i : ℤ} (hi : a + 1 - Int.ofNat m ≤ i) :
    descendingCutoff a m ≤ i := by
  simpa [descendingCutoff_eq] using hi

/-- Helper for Lemma 13.15.4: the recursive cutoff in a successor degree also reaches the next
successor. -/
private theorem descendingCutoff_succ_le_of_closedForm
    (a : ℤ) (m : ℕ) {i : ℤ} (hi : a + 1 - Int.ofNat m ≤ i) :
    descendingCutoff a m ≤ i + 1 := by
  exact le_trans (descendingCutoff_le_of_closedForm a m hi) (by omega)

/-- Helper for Lemma 13.15.4: above the inherited cutoff, the next recursive stage keeps the same
objects. -/
private theorem descendingReplacementStage_X_of_le
    {a : ℤ} {K : CochainComplex A ℤ}
    (stage : (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m))
    (hstageSucc : ∀ m : ℕ,
      stage (m + 1) =
        BoundedAboveReplacementStage.extend (stage m)
          (descendingCutoff_le_top a m))
    (m : ℕ) {i : ℤ} (hi : descendingCutoff a m ≤ i) :
    (stage (m + 1)).Q.X i = (stage m).Q.X i := by
  rw [hstageSucc m]
  exact BoundedAboveReplacementStage.extend_raw_complex_X_of_le (S := stage m) (i := i) hi

/-- Helper for Lemma 13.15.4: above the inherited cutoff, the next recursive stage keeps the same
comparison-map component up to the canonical transport. -/
private theorem descendingReplacementStage_α_f_of_le
    {a : ℤ} {K : CochainComplex A ℤ}
    (stage : (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m))
    (hstageSucc : ∀ m : ℕ,
      stage (m + 1) =
        BoundedAboveReplacementStage.extend (stage m)
          (descendingCutoff_le_top a m))
    (m : ℕ) {i : ℤ} (hi : descendingCutoff a m ≤ i) :
    (stage (m + 1)).α.f i =
      eqToHom (descendingReplacementStage_X_of_le (P := P) stage hstageSucc m hi) ≫
        (stage m).α.f i := by
  let E := BoundedAboveReplacementStage.extend (stage m) (descendingCutoff_le_top a m)
  have hX : E.Q.X i = (stage m).Q.X i := by
    simpa [E, BoundedAboveReplacementStage.extend] using
      (BoundedAboveReplacementStage.extend_raw_complex_X_of_le (S := stage m) (i := i) hi)
  have hmain : E.α.f i = eqToHom hX ≫ (stage m).α.f i := by
    -- Proof comment: on the explicit extension stage, this is exactly the owner tail-component
    -- identity.
    simpa [E, BoundedAboveReplacementStage.extend] using
      (BoundedAboveReplacementStage.extend_raw_α_f_of_le (S := stage m) (i := i) hi)
  have htransport :
      ∀ {T : BoundedAboveReplacementStage (P := P) a K (descendingCutoff a (m + 1))}
        (e : T = E) (hT : T.Q.X i = (stage m).Q.X i),
        T.α.f i = eqToHom hT ≫ (stage m).α.f i := by
    intro T e hT
    cases e
    have hh : hT = hX := Subsingleton.elim _ _
    cases hh
    exact hmain
  exact htransport (hstageSucc m) (descendingReplacementStage_X_of_le (P := P) stage hstageSucc m hi)

/-- Helper for Lemma 13.15.4: above the inherited cutoff, the next recursive stage keeps the same
successor differential up to the canonical transports. -/
private theorem descendingReplacementStage_d_of_le
    {a : ℤ} {K : CochainComplex A ℤ}
    (stage : (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m))
    (hstageSucc : ∀ m : ℕ,
      stage (m + 1) =
        BoundedAboveReplacementStage.extend (stage m)
          (descendingCutoff_le_top a m))
    (m : ℕ) {i : ℤ} (hi : descendingCutoff a m ≤ i) :
    (stage (m + 1)).Q.d i (i + 1) =
      eqToHom (descendingReplacementStage_X_of_le (P := P) stage hstageSucc m hi) ≫
        (stage m).Q.d i (i + 1) ≫
        eqToHom
          ((descendingReplacementStage_X_of_le (P := P) stage hstageSucc m
            (le_trans hi (by omega))).symm) := by
  let E := BoundedAboveReplacementStage.extend (stage m) (descendingCutoff_le_top a m)
  have hX : E.Q.X i = (stage m).Q.X i := by
    simpa [E, BoundedAboveReplacementStage.extend] using
      (BoundedAboveReplacementStage.extend_raw_complex_X_of_le (S := stage m) (i := i) hi)
  have hXsucc : E.Q.X (i + 1) = (stage m).Q.X (i + 1) := by
    simpa [E, BoundedAboveReplacementStage.extend] using
      (BoundedAboveReplacementStage.extend_raw_complex_X_of_le (S := stage m) (i := i + 1)
        (le_trans hi (by omega)))
  have hmain :
      E.Q.d i (i + 1) =
        eqToHom hX ≫ (stage m).Q.d i (i + 1) ≫ eqToHom hXsucc.symm := by
    -- Proof comment: on the explicit extension stage, this is exactly the owner tail-differential
    -- identity.
    simpa [E, BoundedAboveReplacementStage.extend] using
      (BoundedAboveReplacementStage.extend_raw_complex_d_of_le (S := stage m) (i := i)
        (j := i + 1) hi (by simp))
  have htransport :
      ∀ {T : BoundedAboveReplacementStage (P := P) a K (descendingCutoff a (m + 1))}
        (e : T = E) (hT : T.Q.X i = (stage m).Q.X i)
        (hTsucc : T.Q.X (i + 1) = (stage m).Q.X (i + 1)),
        T.Q.d i (i + 1) =
          eqToHom hT ≫ (stage m).Q.d i (i + 1) ≫ eqToHom hTsucc.symm := by
    intro T e hT hTsucc
    cases e
    have hh : hT = hX := Subsingleton.elim _ _
    have hhsucc : hTsucc = hXsucc := Subsingleton.elim _ _
    cases hh
    cases hhsucc
    exact hmain
  exact htransport (hstageSucc m)
    (descendingReplacementStage_X_of_le (P := P) stage hstageSucc m hi)
    (descendingReplacementStage_X_of_le (P := P) stage hstageSucc m (le_trans hi (by omega)))

/-- Helper for Lemma 13.15.4: once a degree lies on the stabilized tail of the descending stage
tower, later stages have the same object in that degree. -/
private theorem descendingStageTailObjectEq
    {a : ℤ} {K : CochainComplex A ℤ}
    (stage : (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m))
    (hstageSucc : ∀ m : ℕ,
      stage (m + 1) =
        BoundedAboveReplacementStage.extend (stage m)
          (descendingCutoff_le_top a m))
    (m₁ m₂ : ℕ) (hm : m₁ ≤ m₂) {i : ℤ} (hi : descendingCutoff a m₁ ≤ i) :
    (stage m₂).Q.X i = (stage m₁).Q.X i := by
  induction hm generalizing i with
  | refl =>
      rfl
  | @step m₂ hm ih =>
      have hi₂ : descendingCutoff a m₂ ≤ i := by
        exact le_trans (descendingStageCutoffAntitone a hm) hi
      exact (descendingReplacementStage_X_of_le (P := P) stage hstageSucc m₂ hi₂).trans (ih hi)

/-- Helper for Lemma 13.15.4: on the stabilized tail, later stage comparison-map components agree
with earlier ones up to the canonical object transport. -/
private theorem descendingStageTailComponentEq
    {a : ℤ} {K : CochainComplex A ℤ}
    (stage : (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m))
    (hstageSucc : ∀ m : ℕ,
      stage (m + 1) =
        BoundedAboveReplacementStage.extend (stage m)
          (descendingCutoff_le_top a m))
    (m₁ m₂ : ℕ) (hm : m₁ ≤ m₂) {i : ℤ} (hi : descendingCutoff a m₁ ≤ i) :
    (stage m₂).α.f i =
      eqToHom (descendingStageTailObjectEq (P := P) stage hstageSucc m₁ m₂ hm hi) ≫
        (stage m₁).α.f i := by
  induction hm generalizing i with
  | refl =>
      simp
  | @step m₂ hm ih =>
      have hi₂ : descendingCutoff a m₂ ≤ i := by
        exact le_trans (descendingStageCutoffAntitone a hm) hi
      have hsucc :=
        descendingReplacementStage_α_f_of_le (P := P) stage hstageSucc m₂ hi₂
      calc
        (stage (m₂ + 1)).α.f i =
            eqToHom (descendingReplacementStage_X_of_le (P := P) stage hstageSucc m₂ hi₂) ≫
              (stage m₂).α.f i := hsucc
        _ =
            eqToHom (descendingReplacementStage_X_of_le (P := P) stage hstageSucc m₂ hi₂) ≫
              (eqToHom (descendingStageTailObjectEq (P := P) stage hstageSucc m₁ m₂ hm hi) ≫
                (stage m₁).α.f i) := by
              rw [ih hi]
        _ =
            eqToHom (descendingStageTailObjectEq (P := P) stage hstageSucc m₁ (m₂ + 1)
              (Nat.le.step hm) hi) ≫ (stage m₁).α.f i := by
              simp [Category.assoc, descendingStageTailObjectEq]

/-- Helper for Lemma 13.15.4: on the stabilized tail, later stage successor differentials agree
with earlier ones up to the canonical source and target transports. -/
private theorem descendingStageTailDifferentialEq
    {a : ℤ} {K : CochainComplex A ℤ}
    (stage : (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m))
    (hstageSucc : ∀ m : ℕ,
      stage (m + 1) =
        BoundedAboveReplacementStage.extend (stage m)
          (descendingCutoff_le_top a m))
    (m₁ m₂ : ℕ) (hm : m₁ ≤ m₂) {i : ℤ} (hi : descendingCutoff a m₁ ≤ i) :
    (stage m₂).Q.d i (i + 1) =
      eqToHom (descendingStageTailObjectEq (P := P) stage hstageSucc m₁ m₂ hm hi) ≫
        (stage m₁).Q.d i (i + 1) ≫
        eqToHom
          ((descendingStageTailObjectEq (P := P) stage hstageSucc m₁ m₂ hm (i := i + 1)
            (le_trans hi (by omega))).symm) := by
  induction hm generalizing i with
  | refl =>
      simp
  | @step m₂ hm ih =>
      have hi₂ : descendingCutoff a m₂ ≤ i := by
        exact le_trans (descendingStageCutoffAntitone a hm) hi
      have hsucc :=
        descendingReplacementStage_d_of_le (P := P) stage hstageSucc m₂ hi₂
      calc
        (stage (m₂ + 1)).Q.d i (i + 1) =
            eqToHom (descendingReplacementStage_X_of_le (P := P) stage hstageSucc m₂ hi₂) ≫
              (stage m₂).Q.d i (i + 1) ≫
              eqToHom
                ((descendingReplacementStage_X_of_le (P := P) stage hstageSucc m₂
                  (le_trans hi₂ (by omega))).symm) := hsucc
        _ =
            eqToHom (descendingReplacementStage_X_of_le (P := P) stage hstageSucc m₂ hi₂) ≫
              (eqToHom (descendingStageTailObjectEq (P := P) stage hstageSucc m₁ m₂ hm hi) ≫
                (stage m₁).Q.d i (i + 1) ≫
                eqToHom
                  ((descendingStageTailObjectEq (P := P) stage hstageSucc m₁ m₂ hm
                    (i := i + 1) (le_trans hi (by omega))).symm)) ≫
              eqToHom
                ((descendingReplacementStage_X_of_le (P := P) stage hstageSucc m₂
                  (le_trans hi₂ (by omega))).symm) := by
              rw [ih hi]
        _ =
            eqToHom (descendingStageTailObjectEq (P := P) stage hstageSucc m₁ (m₂ + 1)
              (Nat.le.step hm) hi) ≫
              (stage m₁).Q.d i (i + 1) ≫
              eqToHom
                ((descendingStageTailObjectEq (P := P) stage hstageSucc m₁ (m₂ + 1)
                  (Nat.le.step hm) (i := i + 1) (le_trans hi (by omega))).symm) := by
              simp [Category.assoc, descendingStageTailObjectEq]

/-- Helper for Lemma 13.15.4: after normalizing the predecessor branch `i - 1 ⟶ i`, the left
window differential of the deep stage is exactly the realized differential used to build `Q`. -/
private theorem realizedWindowLeftDifferentialTransport
    {a : ℤ} {K : CochainComplex A ℤ}
    (stage : (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m))
    (hstageSucc : ∀ m : ℕ,
      stage (m + 1) =
        BoundedAboveReplacementStage.extend (stage m)
          (descendingCutoff_le_top a m))
    (mX mH : ℤ → ℕ)
    (hmH_eq : ∀ i : ℤ, mH i = mX (i - 1))
    (hmX_le_mH : ∀ i : ℤ, mX i ≤ mH i)
    (hmX_stageCutoff_le : ∀ i : ℤ, descendingCutoff a (mX i) ≤ i)
    (Qd : ∀ i j : ℤ, (stage (mX i)).Q.X i ⟶ (stage (mX j)).Q.X j)
    (realizedObjectEqSucc :
      ∀ i : ℤ, (stage (mX i)).Q.X (i + 1) = (stage (mX (i + 1))).Q.X (i + 1))
    (hQdSucc :
      ∀ i : ℤ,
        Qd i (i + 1) =
          (stage (mX i)).Q.d i (i + 1) ≫ eqToHom (realizedObjectEqSucc i))
    (i : ℤ)
    (hstageLeft :
      (stage (mH i)).Q.X (i - 1) = (stage (mX (i - 1))).Q.X (i - 1))
    (hstageMid :
      (stage (mH i)).Q.X i = (stage (mX i)).Q.X i) :
    eqToHom hstageLeft.symm ≫ (stage (mH i)).Q.d (i - 1) i =
      Qd (i - 1) i ≫ eqToHom hstageMid.symm := by
  -- Route correction: the intended proof normalizes the predecessor branch through the canonical
  -- base-stage codomain transport `mH i = mX (i - 1)` and then rewrites the realized map with
  -- `hQdSucc (i - 1)`.
  -- TODO: package the dependent `eqToHom` composition
  -- `eqToHom hmidStage ≫ eqToHom (hmidBase.trans hmidStage).symm = eqToHom hmidBase.symm`
  -- as a dedicated bridge, then finish by `simpa` from the normalized differential and `hQdSucc`.
  sorry

/-- Helper for Lemma 13.15.4: after assembling the realized complex from the descending stages,
its degree-`i` short-complex window is compared with the deeper stage `stage (mH i)` and inherits
the corresponding `QuasiIsoAt`. -/
private theorem realizedQuasiIsoAt
    {a : ℤ} {K : CochainComplex A ℤ}
    (stage : (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m))
    (hstageSucc : ∀ m : ℕ,
      stage (m + 1) =
        BoundedAboveReplacementStage.extend (stage m)
          (descendingCutoff_le_top a m))
    (mX mH : ℤ → ℕ)
    (hmH_eq : ∀ i : ℤ, mH i = mX (i - 1))
    (hmX_le_mH : ∀ i : ℤ, mX i ≤ mH i)
    (hmX_succ_le : ∀ i : ℤ, mX (i + 1) ≤ mX i)
    (hmX_stageCutoff_le : ∀ i : ℤ, descendingCutoff a (mX i) ≤ i)
    (hmH_stageCutoff_lt : ∀ i : ℤ, descendingCutoff a (mH i) < i)
    (Qd : ∀ i j : ℤ, (stage (mX i)).Q.X i ⟶ (stage (mX j)).Q.X j)
    (hQShape : ∀ i j : ℤ, ¬ (up ℤ).Rel i j → Qd i j = 0)
    (hQdComp : ∀ i j k : ℤ, (up ℤ).Rel i j → (up ℤ).Rel j k → Qd i j ≫ Qd j k = 0)
    (realizedObjectEqSucc :
      ∀ i : ℤ, (stage (mX i)).Q.X (i + 1) = (stage (mX (i + 1))).Q.X (i + 1))
    (hQdSucc :
      ∀ i : ℤ,
        Qd i (i + 1) =
          (stage (mX i)).Q.d i (i + 1) ≫ eqToHom (realizedObjectEqSucc i))
    (hαCommSucc :
      ∀ i : ℤ,
        Qd i (i + 1) ≫ (stage (mX (i + 1))).α.f (i + 1) =
          (stage (mX i)).α.f i ≫ K.d i (i + 1))
    (i : ℤ) :
    let Q : CochainComplex A ℤ :=
      { X := fun j ↦ (stage (mX j)).Q.X j
        d := Qd
        shape := hQShape
        d_comp_d' := hQdComp }
    let α : Q ⟶ K :=
      { f := fun j ↦ (stage (mX j)).α.f j
        comm' := by
          intro j k hjk
          have hsucc : j + 1 = k := by simpa using hjk
          subst k
          simpa using (hαCommSucc j).symm }
    QuasiIsoAt α i := by
  let Q : CochainComplex A ℤ :=
    { X := fun j ↦ (stage (mX j)).Q.X j
      d := Qd
      shape := hQShape
      d_comp_d' := hQdComp }
  let α : Q ⟶ K :=
    { f := fun j ↦ (stage (mX j)).α.f j
      comm' := by
        intro j k hjk
        have hsucc : j + 1 = k := by simpa using hjk
        subst k
        simpa using (hαCommSucc j).symm }
  have hstageLeftStage :
      (stage (mH i)).Q.X (i - 1) = (stage (mX (i - 1))).Q.X (i - 1) := by
    rw [hmH_eq i]
  have hstageLeft :
      (stage (mH i)).Q.X (i - 1) = Q.X (i - 1) := by
    simpa [Q] using hstageLeftStage
  have hstageMidStage :
      (stage (mH i)).Q.X i = (stage (mX i)).Q.X i := by
    exact
      descendingStageTailObjectEq (P := P) stage hstageSucc (mX i) (mH i) (hmX_le_mH i) (i := i)
        (hmX_stageCutoff_le i)
  have hstageMid :
      (stage (mH i)).Q.X i = Q.X i := by
    simpa [Q] using hstageMidStage
  have hstageRightFromMid :
      (stage (mH i)).Q.X (i + 1) = (stage (mX i)).Q.X (i + 1) := by
    exact
      descendingStageTailObjectEq (P := P) stage hstageSucc (mX i) (mH i) (hmX_le_mH i)
        (i := i + 1) (le_trans (hmX_stageCutoff_le i) (by omega))
  have hrealizedRight :
      (stage (mX i)).Q.X (i + 1) = Q.X (i + 1) := by
    simpa [Q] using realizedObjectEqSucc i
  have hstageRight :
      (stage (mH i)).Q.X (i + 1) = Q.X (i + 1) := by
    exact hstageRightFromMid.trans hrealizedRight
  -- Route correction: the predecessor-degree transport is handled once in
  -- `realizedWindowLeftDifferentialTransport`, and the final proof only assembles cached window
  -- comparisons.
  have hcomm12 :
      eqToHom hstageLeft.symm ≫ ((stage (mH i)).Q.sc' (i - 1) i (i + 1)).f =
        (Q.sc' (i - 1) i (i + 1)).f ≫ eqToHom hstageMid.symm := by
    have hleftD :
        eqToHom hstageLeft.symm ≫ (stage (mH i)).Q.d (i - 1) i =
          Q.d (i - 1) i ≫ eqToHom hstageMid.symm := by
      have hsucc : i - 1 + 1 = i := by
        omega
      have hsuccX : mX (i - 1 + 1) = mX i := by
        exact congrArg mX hsucc
      have hmPred : mX (i - 1) ≤ mH i := by
        simpa [hmH_eq i]
      have hstageMidBase :
          (stage (mH i)).Q.X i = (stage (mX (i - 1))).Q.X i := by
        exact
          descendingStageTailObjectEq (P := P) stage hstageSucc (mX (i - 1)) (mH i) hmPred
            (i := i) (le_trans (hmX_stageCutoff_le (i - 1)) (by omega))
      have hstageMidBaseRaw :
          (stage (mH i)).Q.X (i - 1 + 1) = (stage (mX (i - 1))).Q.X (i - 1 + 1) := by
        simpa [hsucc] using hstageMidBase
      have hstageMidRaw :
          (stage (mH i)).Q.X (i - 1 + 1) = (stage (mX (i - 1 + 1))).Q.X (i - 1 + 1) := by
        exact hstageMidBaseRaw.trans (realizedObjectEqSucc (i - 1))
      have hstageMidQ :
          hstageMid = (by simpa [Q] using hstageMidStage) := by
        exact Subsingleton.elim _ _
      -- Proof comment: the left predecessor transport is now normalized inside the dedicated
      -- helper, so the call site only rewrites the stage-level equality into the realized `Q`
      -- spelling.
      have hleftDStage :
          eqToHom hstageLeftStage.symm ≫ (stage (mH i)).Q.d (i - 1) i =
            Qd (i - 1) i ≫ eqToHom hstageMidStage.symm := by
        exact
          realizedWindowLeftDifferentialTransport (P := P) stage hstageSucc mX mH hmH_eq
            hmX_le_mH hmX_stageCutoff_le Qd realizedObjectEqSucc hQdSucc i hstageLeftStage
            hstageMidStage
      have hstageLeftQ : hstageLeft = (by simpa [Q] using hstageLeftStage) := by
        exact Subsingleton.elim _ _
      simpa [Q, hstageLeftQ, hstageMidQ] using hleftDStage
    exact realizedWindowLeftDifferentialEq (P := P) (S := stage (mH i)) hstageLeft hstageMid
      hleftD
  have hcomm23 :
      eqToHom hstageMid.symm ≫ ((stage (mH i)).Q.sc' (i - 1) i (i + 1)).g =
        (Q.sc' (i - 1) i (i + 1)).g ≫ eqToHom hstageRight.symm := by
    have hrightD :
        eqToHom hstageMid.symm ≫ (stage (mH i)).Q.d i (i + 1) =
          Q.d i (i + 1) ≫ eqToHom hstageRight.symm := by
      calc
        eqToHom hstageMid.symm ≫ (stage (mH i)).Q.d i (i + 1) =
            (stage (mX i)).Q.d i (i + 1) ≫ eqToHom hstageRightFromMid.symm := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ eqToHom hstageMid.symm ≫ t)
                  (descendingStageTailDifferentialEq (P := P) stage hstageSucc (mX i) (mH i)
                    (hmX_le_mH i) (i := i) (hmX_stageCutoff_le i))
        _ = Q.d i (i + 1) ≫ eqToHom hstageRight.symm := by
              simpa [Q, hQdSucc i, hstageRight, Category.assoc]
    exact realizedWindowRightDifferentialEq (P := P) (S := stage (mH i)) hstageMid hstageRight
      hrightD
  have hαleft :
      eqToHom hstageLeft.symm ≫ (stage (mH i)).α.f (i - 1) = α.f (i - 1) := by
    have hleftComponent :
        (stage (mH i)).α.f (i - 1) = eqToHom hstageLeft ≫ α.f (i - 1) := by
      have hleftComponentStage :
          (stage (mH i)).α.f (i - 1) =
            eqToHom hstageLeftStage ≫ (stage (mX (i - 1))).α.f (i - 1) := by
        simpa using
          descendingStageTailComponentEq (P := P) stage hstageSucc (mX (i - 1)) (mH i)
            (by simpa [hmH_eq i]) (i := i - 1) (hmX_stageCutoff_le (i - 1))
      have hhleft : hstageLeft = hstageLeftStage := by
        exact Subsingleton.elim _ _
      simpa [Q, α, hhleft] using hleftComponentStage
    exact
      realizedWindowMidComponentEq (P := P) (S := stage (mH i)) (i := i - 1) α hstageLeft
        hleftComponent
  have hαmid :
      eqToHom hstageMid.symm ≫ (stage (mH i)).α.f i = α.f i := by
    have hmidComponent :
        (stage (mH i)).α.f i = eqToHom hstageMid ≫ α.f i := by
      simpa [α] using
        descendingStageTailComponentEq (P := P) stage hstageSucc (mX i) (mH i) (hmX_le_mH i)
          (i := i) (hmX_stageCutoff_le i)
    exact realizedWindowMidComponentEq (P := P) (S := stage (mH i)) α hstageMid hmidComponent
  have hαright :
      eqToHom hstageRight.symm ≫ (stage (mH i)).α.f (i + 1) = α.f (i + 1) := by
    have hmidTail :
        (stage (mH i)).α.f (i + 1) =
          eqToHom hstageRightFromMid ≫ (stage (mX i)).α.f (i + 1) := by
      simpa using
        descendingStageTailComponentEq (P := P) stage hstageSucc (mX i) (mH i) (hmX_le_mH i)
          (i := i + 1) (le_trans (hmX_stageCutoff_le i) (by omega))
    have hrealizedTail :
        (stage (mX i)).α.f (i + 1) =
          eqToHom hrealizedRight ≫ α.f (i + 1) := by
      simpa [α] using
        descendingStageTailComponentEq (P := P) stage hstageSucc (mX (i + 1)) (mX i)
          (hmX_succ_le i) (i := i + 1) (hmX_stageCutoff_le (i + 1))
    exact
      realizedWindowRightComponentEq (P := P) (S := stage (mH i)) α (stage (mX i)).α
        hstageRightFromMid hrealizedRight hstageRight rfl hmidTail hrealizedTail
  have hStageAt : QuasiIsoAt (stage (mH i)).α i := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact (stage (mH i)).homologyMap_isIso i (hmH_stageCutoff_lt i)
  exact
    BoundedAboveReplacementStage.quasiIsoAt_of_windowComparison (P := P) (S := stage (mH i))
      (α := α) hstageLeft hstageMid hstageRight hcomm12 hcomm23 hαleft hαmid hαright hStageAt

/-- Helper for Lemma 13.15.4: the realized descending-stage comparison map is a quasi-isomorphism
once each degree is compared with the deeper stage `stage (mH i)`. -/
private theorem realizedQuasiIso
    {a : ℤ} {K : CochainComplex A ℤ}
    (stage : (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m))
    (hstageSucc : ∀ m : ℕ,
      stage (m + 1) =
        BoundedAboveReplacementStage.extend (stage m)
          (descendingCutoff_le_top a m))
    (mX mH : ℤ → ℕ)
    (hmH_eq : ∀ i : ℤ, mH i = mX (i - 1))
    (hmX_le_mH : ∀ i : ℤ, mX i ≤ mH i)
    (hmX_succ_le : ∀ i : ℤ, mX (i + 1) ≤ mX i)
    (hmX_stageCutoff_le : ∀ i : ℤ, descendingCutoff a (mX i) ≤ i)
    (hmH_stageCutoff_lt : ∀ i : ℤ, descendingCutoff a (mH i) < i)
    (Qd : ∀ i j : ℤ, (stage (mX i)).Q.X i ⟶ (stage (mX j)).Q.X j)
    (hQShape : ∀ i j : ℤ, ¬ (up ℤ).Rel i j → Qd i j = 0)
    (hQdComp : ∀ i j k : ℤ, (up ℤ).Rel i j → (up ℤ).Rel j k → Qd i j ≫ Qd j k = 0)
    (realizedObjectEqSucc :
      ∀ i : ℤ, (stage (mX i)).Q.X (i + 1) = (stage (mX (i + 1))).Q.X (i + 1))
    (hQdSucc :
      ∀ i : ℤ,
        Qd i (i + 1) =
          (stage (mX i)).Q.d i (i + 1) ≫ eqToHom (realizedObjectEqSucc i))
    (hαCommSucc :
      ∀ i : ℤ,
        Qd i (i + 1) ≫ (stage (mX (i + 1))).α.f (i + 1) =
          (stage (mX i)).α.f i ≫ K.d i (i + 1)) :
    let Q : CochainComplex A ℤ :=
      { X := fun j ↦ (stage (mX j)).Q.X j
        d := Qd
        shape := hQShape
        d_comp_d' := hQdComp }
    let α : Q ⟶ K :=
      { f := fun j ↦ (stage (mX j)).α.f j
        comm' := by
          intro j k hjk
          have hsucc : j + 1 = k := by simpa using hjk
          subst k
          simpa using (hαCommSucc j).symm }
    QuasiIso α := by
  let Q : CochainComplex A ℤ :=
    { X := fun j ↦ (stage (mX j)).Q.X j
      d := Qd
      shape := hQShape
      d_comp_d' := hQdComp }
  let α : Q ⟶ K :=
    { f := fun j ↦ (stage (mX j)).α.f j
      comm' := by
        intro j k hjk
        have hsucc : j + 1 = k := by simpa using hjk
        subst k
        simpa using (hαCommSucc j).symm }
  -- Proof comment: `QuasiIso` is checked degreewise, so we discharge each degree with the
  -- standalone realized-window comparison theorem above.
  rw [quasiIso_iff]
  intro i
  exact
    realizedQuasiIsoAt (P := P) stage hstageSucc mX mH hmH_eq hmX_le_mH hmX_succ_le
      hmX_stageCutoff_le hmH_stageCutoff_lt Qd hQShape hQdComp realizedObjectEqSucc hQdSucc
      hαCommSucc i

/-- Helper for Lemma 13.15.4: realizing the descending tower of bounded-above replacement stages
produces the global termwise-epimorphic quasi-isomorphism promised in part (1). -/
private theorem boundedAboveReplacementStage_realize_with_cutoff_bound
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α := by
  -- Proof comment: realize the descending induction by recursively extending the bounded-above
  -- stages and then reading each degree from the first stage where that degree has been built.
  let stage : (m : ℕ) → BoundedAboveReplacementStage (P := P) a K (descendingCutoff a m) :=
    descendingReplacementStage (P := P) a K hK
  let mX : ℤ → ℕ := fun i ↦ Int.toNat (a + 1 - i)
  let mH : ℤ → ℕ := fun i ↦ mX (i - 1)
  have hmX_cutoff_le (i : ℤ) : a + 1 - Int.ofNat (mX i) ≤ i := by
    -- Proof comment: `mX i` is the least recursive depth whose cutoff has reached degree `i`.
    dsimp [mX]
    by_cases hi : 0 ≤ a + 1 - i
    · rw [Int.toNat_of_nonneg hi]
      omega
    · have hi' : a + 1 - i < 0 := lt_of_not_ge hi
      rw [Int.toNat_of_nonpos (le_of_lt hi')]
      omega
  have hmX_cutoff_lt_succ (i : ℤ) : a + 1 - Int.ofNat (mX i) < i + 1 := by
    exact lt_of_le_of_lt (hmX_cutoff_le i) (by omega)
  have hmX_mono (i j : ℤ) (hij : i ≤ j) : mX j ≤ mX i := by
    -- Proof comment: deeper stages are needed only when the degree moves downward.
    dsimp [mX]
    exact Int.toNat_le_toNat (by omega)
  have hmH_eq (i : ℤ) : mH i = mX (i - 1) := rfl
  have hmX_le_mH (i : ℤ) : mX i ≤ mH i := by
    simpa [mH] using hmX_mono (i - 1) i (by omega)
  have hmX_succ_le (i : ℤ) : mX (i + 1) ≤ mX i := by
    exact hmX_mono i (i + 1) (by omega)
  have hmX_succ_le_mH (i : ℤ) : mX (i + 1) ≤ mH i := by
    exact le_trans (hmX_succ_le i) (hmX_le_mH i)
  have hmH_cutoff_le_prev (i : ℤ) : a + 1 - Int.ofNat (mH i) ≤ i - 1 := by
    simpa [mH] using hmX_cutoff_le (i - 1)
  have hmH_cutoff_lt (i : ℤ) : a + 1 - Int.ofNat (mH i) < i := by
    exact lt_of_le_of_lt (hmH_cutoff_le_prev i) (by omega)
  have hmX_stageCutoff_le (i : ℤ) : descendingCutoff a (mX i) ≤ i := by
    exact descendingCutoff_le_of_closedForm a (mX i) (hmX_cutoff_le i)
  have hmX_stageCutoff_lt_succ (i : ℤ) : descendingCutoff a (mX i) < i + 1 := by
    simpa [descendingCutoff_eq] using hmX_cutoff_lt_succ i
  have hmH_stageCutoff_lt (i : ℤ) : descendingCutoff a (mH i) < i := by
    simpa [descendingCutoff_eq] using hmH_cutoff_lt i
  have hstageSucc : ∀ m : ℕ,
      stage (m + 1) =
        BoundedAboveReplacementStage.extend (stage m)
          (descendingCutoff_le_top a m) := by
    intro m
    simpa [stage] using descendingReplacementStage_succ (P := P) a K hK m
  have stageTailObjectEq := descendingStageTailObjectEq (P := P) stage hstageSucc
  have stageTailComponentEq := descendingStageTailComponentEq (P := P) stage hstageSucc
  have stageTailDifferentialEq := descendingStageTailDifferentialEq (P := P) stage hstageSucc
  let QX : ℤ → A := fun i ↦ (stage (mX i)).Q.X i
  have realizedObjectEqSucc (i : ℤ) :
      (stage (mX i)).Q.X (i + 1) = QX (i + 1) := by
    -- Proof comment: the realized successor target is read from the next recursive stage, so one
    -- tail-stability transport identifies it with the current stage.
    dsimp [QX]
    exact
      stageTailObjectEq (mX (i + 1)) (mX i) (hmX_succ_le i) (i := i + 1)
        (hmX_stageCutoff_le (i + 1))
  have realizedObjectEqTwoSucc (i : ℤ) :
      (stage (mX i)).Q.X (i + 2) = QX (i + 2) := by
    -- Proof comment: two successor targets are compared by first descending one stage and then
    -- reading the realized degree from the first stage whose cutoff reaches degree `i + 2`.
    dsimp [QX]
    exact
      stageTailObjectEq (mX (i + 2)) (mX i)
        (hmX_mono i (i + 2) (by omega)) (i := i + 2)
        (hmX_stageCutoff_le (i + 2))
  let Qd : ∀ i j : ℤ, QX i ⟶ QX j := fun i j ↦ by
    by_cases h : i + 1 = j
    · subst j
      exact (stage (mX i)).Q.d i (i + 1) ≫ eqToHom (realizedObjectEqSucc i)
    · exact 0
  have hQdSucc (i : ℤ) :
      Qd i (i + 1) =
        (stage (mX i)).Q.d i (i + 1) ≫ eqToHom (realizedObjectEqSucc i) := by
    -- Proof comment: on successor indices the realized differential is exactly the stabilized
    -- stage differential followed by the realized target identification.
    simp [Qd]
  have hQShape : ∀ i j : ℤ, ¬ (up ℤ).Rel i j → Qd i j = 0 := by
    intro i j hij
    -- Proof comment: away from successor indices the realized differential is declared to be
    -- zero, exactly matching the cochain shape.
    have hij' : i + 1 ≠ j := by
      simpa using hij
    simp [Qd, hij']
  have hQdCompSucc (i : ℤ) : Qd i (i + 1) ≫ Qd (i + 1) (i + 1 + 1) = 0 := by
    -- Proof comment: rewrite the second realized differential into the same deep stage as the
    -- first one, then use the stage relation `d ≫ d = 0`.
    have htwo : i + 1 + 1 = i + 2 := by omega
    have realizedObjectEqTwoSucc' :
        (stage (mX i)).Q.X (i + 1 + 1) = QX (i + 1 + 1) := by
      simpa [htwo] using realizedObjectEqTwoSucc i
    have htail0 :
        eqToHom (realizedObjectEqSucc i) ≫ Qd (i + 1) (i + 1 + 1) =
          (stage (mX i)).Q.d (i + 1) (i + 1 + 1) ≫ eqToHom realizedObjectEqTwoSucc' := by
      have hstageRight0 :
          (stage (mX i)).Q.X (i + 1 + 1) = (stage (mX (i + 1))).Q.X (i + 1 + 1) := by
        exact
          stageTailObjectEq (mX (i + 1)) (mX i) (hmX_succ_le i) (i := i + 1 + 1)
            (le_trans (hmX_stageCutoff_le (i + 1)) (by omega))
      have hstage0 :
          (stage (mX i)).Q.d (i + 1) (i + 1 + 1) =
            eqToHom (realizedObjectEqSucc i) ≫
              (stage (mX (i + 1))).Q.d (i + 1) (i + 1 + 1) ≫
              eqToHom hstageRight0.symm := by
        exact
          stageTailDifferentialEq (mX (i + 1)) (mX i) (hmX_succ_le i) (i := i + 1)
            (hmX_stageCutoff_le (i + 1))
      have htransport0 :
          hstageRight0.trans (realizedObjectEqSucc (i + 1)) = realizedObjectEqTwoSucc' := by
        simp [hstageRight0, realizedObjectEqTwoSucc', realizedObjectEqSucc, QX]
      rw [hQdSucc]
      have hstage' :=
        congrArg (fun t ↦ t ≫ eqToHom realizedObjectEqTwoSucc') hstage0
      simpa [htransport0, Category.assoc] using hstage'.symm
    calc
      Qd i (i + 1) ≫ Qd (i + 1) (i + 1 + 1) =
          (stage (mX i)).Q.d i (i + 1) ≫
            ((stage (mX i)).Q.d (i + 1) (i + 1 + 1) ≫ eqToHom realizedObjectEqTwoSucc') := by
          simpa [Qd, Category.assoc] using
            congrArg (fun t ↦ (stage (mX i)).Q.d i (i + 1) ≫ t) htail0
      _ = ((stage (mX i)).Q.d i (i + 1) ≫ (stage (mX i)).Q.d (i + 1) (i + 1 + 1)) ≫
            eqToHom realizedObjectEqTwoSucc' := by
          simp [Category.assoc]
      _ = 0 := by
          simpa [Category.assoc] using
            congrArg (fun t ↦ t ≫ eqToHom realizedObjectEqTwoSucc')
              ((stage (mX i)).Q.d_comp_d i (i + 1) (i + 1 + 1))
  have hQdComp :
      ∀ i j k : ℤ, (up ℤ).Rel i j → (up ℤ).Rel j k → Qd i j ≫ Qd j k = 0 := by
    intro i j k hij hjk
    -- Proof comment: every composable cochain pair is a successor pair, so the general case
    -- reduces to the successor computation above.
    have hj : i + 1 = j := by simpa using hij
    have hk : j + 1 = k := by simpa using hjk
    subst j
    subst k
    exact hQdCompSucc i
  let Q : CochainComplex A ℤ :=
    { X := QX
      d := Qd
      shape := hQShape
      d_comp_d' := hQdComp }
  have hαCommSucc (i : ℤ) :
      Q.d i (i + 1) ≫ (stage (mX (i + 1))).α.f (i + 1) =
        (stage (mX i)).α.f i ≫ K.d i (i + 1) := by
    -- Proof comment: the successor component of the realized chain map is inherited from the
    -- deep stage after identifying the realized target with that stage.
    have hcomponent :
        eqToHom (realizedObjectEqSucc i) ≫ (stage (mX (i + 1))).α.f (i + 1) =
          (stage (mX i)).α.f (i + 1) := by
      simpa [realizedObjectEqSucc] using
        (stageTailComponentEq (mX (i + 1)) (mX i) (hmX_succ_le i) (i := i + 1)
          (hmX_stageCutoff_le (i + 1))).symm
    calc
      Q.d i (i + 1) ≫ (stage (mX (i + 1))).α.f (i + 1) =
          (stage (mX i)).Q.d i (i + 1) ≫ (stage (mX i)).α.f (i + 1) := by
          simpa [Q, Qd, Category.assoc] using
            congrArg (fun t ↦ (stage (mX i)).Q.d i (i + 1) ≫ t) hcomponent
      _ = (stage (mX i)).α.f i ≫ K.d i (i + 1) := by
          simpa [Category.assoc] using (stage (mX i)).α.comm i (i + 1)
  let α : Q ⟶ K :=
    { f := fun i ↦ (stage (mX i)).α.f i
      comm' := by
        intro i j hij
        have h : i + 1 = j := by simpa using hij
        subst j
        simpa using (hαCommSucc i).symm }
  have hQStrictlyLE : Q.IsStrictlyLE a := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    -- Proof comment: every realized degree is taken from some stage, and each stage is already
    -- strictly bounded above by `a`.
    letI : (stage (mX i)).Q.IsStrictlyLE a := (stage (mX i)).strictlyLE
    change IsZero ((stage (mX i)).Q.X i)
    exact (stage (mX i)).Q.isZero_of_isStrictlyLE a i hi
  have hQTermMem (i : ℤ) : P (Q.X i) := by
    -- Proof comment: the chosen recursive stage has already constructed the realized degree.
    change P ((stage (mX i)).Q.X i)
    exact (stage (mX i)).term_mem i (hmX_stageCutoff_le i)
  have hQTermEpi (i : ℤ) : Epi (α.f i) := by
    -- Proof comment: the same stage also provides the termwise epimorphism at that degree.
    change Epi ((stage (mX i)).α.f i)
    exact (stage (mX i)).term_epi i (hmX_stageCutoff_le i)
  have hαQuasiIso : QuasiIso α := by
    -- Proof comment: the per-degree realized-window comparison has been split into the standalone
    -- theorem `realizedQuasiIsoAt`, leaving this final step as a thin cached wrapper.
    simpa [Q, QX, α] using
      realizedQuasiIso (P := P) stage hstageSucc mX mH hmH_eq hmX_le_mH hmX_succ_le
        hmX_stageCutoff_le hmH_stageCutoff_lt Qd hQShape hQdComp realizedObjectEqSucc hQdSucc
        hαCommSucc
    /-
    have hstageLeft :
        (stage (mH i)).Q.X (i - 1) = Q.X (i - 1) := by
      change (stage (mX (i - 1))).Q.X (i - 1) = (stage (mX (i - 1))).Q.X (i - 1)
      simp [Q, QX, mH]
    have hstageMid :
        (stage (mH i)).Q.X i = Q.X i := by
      change (stage (mH i)).Q.X i = (stage (mX i)).Q.X i
      exact
        stageTailObjectEq (mX i) (mH i) (hmX_le_mH i) (i := i)
          (hmX_stageCutoff_le i)
    have hstageRightFromMid :
        (stage (mH i)).Q.X (i + 1) = (stage (mX i)).Q.X (i + 1) := by
      exact
        stageTailObjectEq (mX i) (mH i) (hmX_le_mH i) (i := i + 1)
          (le_trans (hmX_stageCutoff_le i) (by omega))
    have hrealizedRight :
        (stage (mX i)).Q.X (i + 1) = Q.X (i + 1) := by
      simpa [Q, QX] using realizedObjectEqSucc i
    have hstageRight :
        (stage (mH i)).Q.X (i + 1) = Q.X (i + 1) := by
      exact hstageRightFromMid.trans hrealizedRight
    have hcomm12 :
        eqToHom hstageLeft.symm ≫ ((stage (mH i)).Q.sc' (i - 1) i (i + 1)).f =
          (Q.sc' (i - 1) i (i + 1)).f ≫ eqToHom hstageMid.symm := by
      have hleftD :
          eqToHom hstageLeft.symm ≫ (stage (mH i)).Q.d (i - 1) i =
            Q.d (i - 1) i ≫ eqToHom hstageMid.symm := by
        have hsucc : i - 1 + 1 = i := by omega
        have hmidSucc :
            (stage (mH i)).Q.X (i - 1 + 1) = Q.X (i - 1 + 1) := by
          simpa [Q, QX, mH] using realizedObjectEqSucc (i - 1)
        have hmidRealized : (stage (mH i)).Q.X i = Q.X i := by
          calc
            (stage (mH i)).Q.X i = (stage (mH i)).Q.X (i - 1 + 1) := by
              congr 1
              omega
            _ = Q.X (i - 1 + 1) := hmidSucc
            _ = Q.X i := by
              congr 1
              omega
        have hhmid : hmidRealized = hstageMid := Subsingleton.elim _ _
        cases hhmid
        -- Proof comment: after normalizing the successor index `i - 1 + 1` to `i`, the
        -- predecessor differential is exactly the successor branch used to define `Q.d`.
        simp [Q, Qd, QX, mH, hstageLeft, hmidRealized, hsucc, Category.assoc]
      -- Proof comment: move the left differential transport into a cached helper so the final
      -- degreewise quasi-isomorphism proof only assembles named comparisons.
      exact realizedWindowLeftDifferentialEq (P := P) (S := stage (mH i))
        hstageLeft hstageMid hleftD
    have hcomm23 :
        eqToHom hstageMid.symm ≫ ((stage (mH i)).Q.sc' (i - 1) i (i + 1)).g =
          (Q.sc' (i - 1) i (i + 1)).g ≫ eqToHom hstageRight.symm := by
      have hrightD :
          eqToHom hstageMid.symm ≫ (stage (mH i)).Q.d i (i + 1) =
            Q.d i (i + 1) ≫ eqToHom hstageRight.symm := by
        calc
          eqToHom hstageMid.symm ≫ (stage (mH i)).Q.d i (i + 1) =
              (stage (mX i)).Q.d i (i + 1) ≫ eqToHom hstageRightFromMid.symm := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t ↦ eqToHom hstageMid.symm ≫ t)
                    (stageTailDifferentialEq (mX i) (mH i) (hmX_le_mH i) (i := i)
                      (hmX_stageCutoff_le i))
          _ = Q.d i (i + 1) ≫ eqToHom hstageRight.symm := by
                simp [Q, Qd, hstageRight, Category.assoc]
      -- Proof comment: the only nontrivial right-hand transport is the stabilized tail comparison
      -- from the deep stage to the realized stage, so we discharge it through the cached helper.
      exact realizedWindowRightDifferentialEq (P := P) (S := stage (mH i))
        hstageMid hstageRight hrightD
    have hαleft :
        eqToHom hstageLeft.symm ≫ (stage (mH i)).α.f (i - 1) = α.f (i - 1) := by
      simp [α, Q, QX, mH, hstageLeft]
    have hαmid :
        eqToHom hstageMid.symm ≫ (stage (mH i)).α.f i = α.f i := by
      have hmidComponent :
          (stage (mH i)).α.f i = eqToHom hstageMid ≫ α.f i := by
        simpa [α] using
          stageTailComponentEq (mX i) (mH i) (hmX_le_mH i) (i := i)
            (hmX_stageCutoff_le i)
      -- Proof comment: the middle comparison-map transport is a one-line cancellation once the
      -- stage-tail component equality has been identified.
      exact realizedWindowMidComponentEq (P := P) (S := stage (mH i)) α
        hstageMid hmidComponent
    have hαright :
        eqToHom hstageRight.symm ≫ (stage (mH i)).α.f (i + 1) = α.f (i + 1) := by
      have hmidTail :
          (stage (mH i)).α.f (i + 1) =
            eqToHom hstageRightFromMid ≫ (stage (mX i)).α.f (i + 1) := by
        simpa using
          stageTailComponentEq (mX i) (mH i) (hmX_le_mH i) (i := i + 1)
            (le_trans (hmX_stageCutoff_le i) (by omega))
      have hrealizedTail :
          (stage (mX i)).α.f (i + 1) =
            eqToHom hrealizedRight ≫ α.f (i + 1) := by
        simpa [α] using
          stageTailComponentEq (mX (i + 1)) (mX i) (hmX_succ_le i) (i := i + 1)
            (hmX_stageCutoff_le (i + 1))
      -- Proof comment: compose the deep-stage tail comparison with the realized tail comparison
      -- in a cached helper so the final window-transfer theorem only sees the resulting equality.
      exact realizedWindowRightComponentEq (P := P) (S := stage (mH i)) α (stage (mX i)).α
        hstageRightFromMid hrealizedRight hstageRight rfl hmidTail hrealizedTail
    have hStageAt : QuasiIsoAt (stage (mH i)).α i := by
      rw [quasiIsoAt_iff_isIso_homologyMap]
      exact (stage (mH i)).homologyMap_isIso i (hmH_stageCutoff_lt i)
    have hαAt : QuasiIsoAt α i := by
      exact
        BoundedAboveReplacementStage.quasiIsoAt_of_windowComparison
          (P := P) (S := stage (mH i)) (α := α)
          hstageLeft hstageMid hstageRight hcomm12 hcomm23 hαleft hαmid hαright hStageAt
    exact hαAt
    -/
  refine ⟨Q, α, ?_⟩
  refine
    { quasiIso := hαQuasiIso
      strictlyLE := hQStrictlyLE
      term_mem := hQTermMem
      term_epi := hQTermEpi }

-- Proof sketch: argue by descending induction on the degree. At stage `n - 1`, choose an
-- epimorphism from an object of `P` onto the pullback `K.X (n - 1) ×_{K.X n} ker(d_Q^n)`, then
-- extend the partial complex and comparison map. The inductive construction yields a bounded-above
-- complex `Q` with terms in `P`, a termwise-epimorphic map `Q ⟶ K`, and a quasi-isomorphism.
/-- Helper for Lemma 13.15.4 Support: the realized bounded-above replacement theorem is exposed
as a thin auxiliary statement for the public wrapper in `Lemma_13_15_4.lean`. -/
theorem exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE_aux
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α := by
  -- The heavy descending-stage realization proof is cached above in the support file.
  -- Route correction: the source proof is the descending cycle-pullback construction, not a
  -- derived-category existence argument. The local helper
  -- `boundedAboveReplacementStage_realize_with_cutoff_bound` now isolates the remaining source-
  -- faithful work: closing the cutoff extension step and then realizing the descending tower.
  simpa using boundedAboveReplacementStage_realize_with_cutoff_bound
    (P := P) a K hK

-- Proof sketch: first replace `K` by the stupid truncation `K.truncLE a`, which is
-- quasi-isomorphic to `K` under the vanishing of homology above `a`. Then apply part (1) to the
-- bounded-above complex `K.truncLE a` and compose the resulting quasi-isomorphism with
-- `K.ιTruncLE a`.
/-- Helper for Lemma 13.15.4 Support: truncating above `a` and applying part (1) yields the
bounded-above replacement used by the public part (2) wrapper. -/
theorem exists_quasiIso_with_terms_in_of_isZero_homology_above_aux
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsStrictlyLEQuasiIsoWithTermsIn P a K Q α := by
  -- The source proof first replaces `K` by the upper truncation `K.truncLE a`.
  let hι : QuasiIso (K.ιTruncLE a) :=
    quasiIso_ιTruncLE_of_isZero_homology_above (a := a) (K := K) hK
  letI : QuasiIso (K.ιTruncLE a) := hι
  have htrunc : (K.truncLE a).IsStrictlyLE a := by infer_instance
  -- Apply part (1) to the bounded-above truncation and then compose with `K.truncLE a ⟶ K`.
  obtain ⟨Q, β, hβ⟩ :=
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE_aux
      (P := P) a (K.truncLE a) htrunc
  letI : QuasiIso β := hβ.quasiIso
  refine ⟨Q, β ≫ K.ιTruncLE a, ?_⟩
  -- Composition preserves the quasi-isomorphism, while the bounded-above and termwise `P`
  -- conditions are inherited from the replacement of `K.truncLE a`.
  refine
    { quasiIso := by infer_instance
      strictlyLE := hβ.strictlyLE
      term_mem := hβ.term_mem }

end
