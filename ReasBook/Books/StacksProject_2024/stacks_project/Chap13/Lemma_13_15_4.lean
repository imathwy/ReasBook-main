import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_5_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1

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
  sorry

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
  sorry

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
  have hm : 0 ≤ Int.ofNat m := by exact Int.ofNat_nonneg m
  linarith

namespace BoundedAboveReplacementStage

variable {P} {a : ℤ} {K : CochainComplex A ℤ} {n : ℤ}

/-- Helper for Lemma 13.15.4: the new cycles comparison at the cutoff degree of the raw extension
is epimorphic after transporting both kernels to the pullback square used in the source proof. -/
private theorem extend_cycles_epi_via_kernel_transport
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    Epi (kernel.map ((extend_raw_complex (S := S)).d (n - 1) n) (K.d (n - 1) n)
      ((extend_raw_α (S := S)).f (n - 1)) ((extend_raw_α (S := S)).f n)
      (((extend_raw_α (S := S)).comm (n - 1) n).symm)) := by
  -- TODO: rewrite the source and target kernels to the normalized cutoff maps
  -- `extensionCoverToStageCycles S` and `previousToCycles`, compare them through the pullback
  -- square defining `extensionPullback S`, and transport the resulting epi back to the packaged
  -- cutoff differential.
  sorry

/-- Helper for Lemma 13.15.4: above the cutoff degree, the raw extension inherits the stage
homology isomorphisms from the previous stage. -/
private theorem extend_tail_homologyMap_isIso
    (S : BoundedAboveReplacementStage (P := P) a K n) {i : ℤ} (hi : n < i) :
    IsIso (HomologicalComplex.homologyMap (extend_raw_α (S := S)) i) := by
  -- TODO: identify the raw extension with `S` on the whole tail `≥ n`, transport the induced
  -- homology map through those tail identifications, and then apply `S.homologyMap_isIso i hi`.
  sorry

/-- Helper for Lemma 13.15.4: the new homology map at the cutoff degree of the raw extension is
an isomorphism. -/
private theorem extend_homologyMap_isIso_at_cutoff
    (S : BoundedAboveReplacementStage (P := P) a K n) :
    IsIso (HomologicalComplex.homologyMap (extend_raw_α (S := S)) n) := by
  -- TODO: normalize `HomologicalComplex.homologyMap (extend_raw_α S) n` to the cutoff
  -- `cokernel.map` attached to the pullback square, convert that pullback to a pushout using
  -- `CategoryTheory.isPushout_of_isPullback_of_epi_right`, and conclude with
  -- `CategoryTheory.Limits.isIso_cokernel_map_vertical_of_isPushout`.
  sorry

/-- Helper for Lemma 13.15.4: one step of the descending induction, with the source-faithful
bound `n ≤ a + 1` recorded explicitly in the stage API. -/
private noncomputable def extend
    (S : BoundedAboveReplacementStage (P := P) a K n) (hn : n ≤ a + 1) :
    BoundedAboveReplacementStage (P := P) a K (n - 1) := sorry

end BoundedAboveReplacementStage

/-- Helper for Lemma 13.15.4: realizing the descending tower of bounded-above replacement stages
produces the global termwise-epimorphic quasi-isomorphism promised in part (1). -/
private theorem boundedAboveReplacementStage_realize_with_cutoff_bound
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α := by
  -- TODO: recurse on `m : ℕ` with stages
  -- `BoundedAboveReplacementStage P a K (a + 1 - Int.ofNat m)`, starting from
  -- `boundedAboveReplacementStage_base`; use `BoundedAboveReplacementStage.extend` together with
  -- `boundedAboveReplacementStage_index_le_cutoff` to descend one step at a time, prove
  -- consecutive-stage tail agreement, define the final complex and comparison map degreewise from
  -- the first stage reaching each degree, and close the quasi-isomorphism by `quasiIso_iff` plus
  -- `quasiIsoAt_iff_isIso_homologyMap`.
  sorry

-- Proof sketch: argue by descending induction on the degree. At stage `n - 1`, choose an
-- epimorphism from an object of `P` onto the pullback `K.X (n - 1) ×_{K.X n} ker(d_Q^n)`, then
-- extend the partial complex and comparison map. The inductive construction yields a bounded-above
-- complex `Q` with terms in `P`, a termwise-epimorphic map `Q ⟶ K`, and a quasi-isomorphism.
/-- Lemma 13.15.4 (1): if a cochain complex `K` is zero in degrees above `a`, then there exists a
bounded-above cochain complex `Q` whose terms satisfy the object property `P`, together with a
quasi-isomorphism `Q ⟶ K` that is termwise epimorphic. -/
theorem exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α := by
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
/-- Lemma 13.15.4 (2): if the homology of a cochain complex `K` vanishes in degrees above `a`,
then there exists a bounded-above cochain complex `Q` whose terms satisfy the object property `P`,
together with a quasi-isomorphism `Q ⟶ K`. -/
theorem exists_quasiIso_with_terms_in_of_isZero_homology_above
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
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE P a (K.truncLE a) htrunc
  letI : QuasiIso β := hβ.quasiIso
  refine ⟨Q, β ≫ K.ιTruncLE a, ?_⟩
  -- Composition preserves the quasi-isomorphism, while the bounded-above and termwise `P`
  -- conditions are inherited from the replacement of `K.truncLE a`.
  refine
    { quasiIso := by infer_instance
      strictlyLE := hβ.strictlyLE
      term_mem := hβ.term_mem }

end
