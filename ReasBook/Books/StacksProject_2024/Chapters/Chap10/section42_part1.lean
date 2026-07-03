import Mathlib
import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_42_1 (from Chap10) -/
universe u v w
open scoped IntermediateField

section

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

namespace Algebra

/- Domain-style sampling for Definition 10.42.1:
- primary domain: field extensions, transcendence bases, and separable algebraic intermediate
  extensions;
- sampled owner API:
  `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`,
  `Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable`,
  `Algebra.isSeparable_iff`,
  `perfectField_iff_isSeparable_algebraicClosure`;
- best owner abstractions: the source-facing chapter owners `Algebra.IsSeparablyGenerated` and
  `Algebra.IsSeparableOver`, with `Algebra.IsSeparable` as the algebraic specialization;
- primitive data:
  `IsSeparablyGenerated`: existence of a transcendence basis over which the extension is
  separable;
  `IsSeparableOver`: closure of separably generatedness on finitely generated intermediate fields;
- derived API: transport across algebra equivalences, perfect-field constructions, and the
  algebraic bridges `IsSeparablyGenerated.isSeparable` and `IsSeparableOver.isSeparable`.

Source/core/bridge triage:
- `source-facing`: the two Stacks Project notions introduced in Definition 10.42.1;
- `core/canonical`: the owner classes `Algebra.IsSeparablyGenerated` and
  `Algebra.IsSeparableOver`;
- `bridge/view`: transport lemmas and the algebraic comparison theorems
  `IsSeparablyGenerated.isSeparable` and `IsSeparableOver.isSeparable`.
-/

/-- Definition 10.42.1 (1): a field extension `K / k` is separably generated if there exists a
transcendence basis `s ⊆ K` over `k` such that the extension `K / k(s)` is separable algebraic. -/
@[stacks 030O "(1)", mk_iff isSeparablyGenerated_iff]
class IsSeparablyGenerated : Prop where
  /-- A separably generated extension admits a transcendence basis whose generated intermediate
  field makes the extension separable. -/
  exists_isTranscendenceBasis_and_isSeparable :
    ∃ s : Set K,
      IsTranscendenceBasis k (Subtype.val : s → K) ∧
        Algebra.IsSeparable (IntermediateField.adjoin k s) K

namespace IsSeparablyGenerated

variable {k' : Type u} {K' : Type v} [Field k'] [Field K'] [Algebra k' K']
variable {L : Type w} [Field L] [Algebra k' L]

/-- Transport `IsSeparablyGenerated` across a `k`-algebra equivalence. -/
theorem of_algEquiv (hK : IsSeparablyGenerated k' K') (e : K' ≃ₐ[k'] L) :
    IsSeparablyGenerated k' L := by
  rcases hK with ⟨s, hs, hsep⟩
  let t : Set L := e '' s
  refine ⟨t, ?_, ?_⟩
  · have ht : Set.range (e ∘ (Subtype.val : s → K')) = t := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    exact (e.isTranscendenceBasis hs).to_subtype_range' ht
  · have hmapAdjoin :
        (IntermediateField.adjoin k' s).map e.toAlgHom = IntermediateField.adjoin k' t := by
      rw [IntermediateField.adjoin_map]
      rfl
    let e' : ↥(IntermediateField.adjoin k' s) ≃ₐ[k'] ↥(IntermediateField.adjoin k' t) :=
      (IntermediateField.equivMap (IntermediateField.adjoin k' s) e.toAlgHom).trans
        (IntermediateField.equivOfEq hmapAdjoin)
    let he :
        RingHom.comp (algebraMap ↥(IntermediateField.adjoin k' t) L) ↑e'.toRingEquiv =
          RingHom.comp ↑e.toRingEquiv (algebraMap ↥(IntermediateField.adjoin k' s) K') := by
      ext x
      rfl
    haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin k' s) K' := hsep
    exact Algebra.IsSeparable.of_equiv_equiv e'.toRingEquiv e.toRingEquiv he

/-- Over a perfect base field, every finitely generated extension is separably generated. -/
theorem of_perfectField [PerfectField k'] [EssFiniteType k' K'] :
    IsSeparablyGenerated k' K' := by
  rcases exists_isTranscendenceBasis_and_isSeparable_of_perfectField k' K' with ⟨s, hs, hsep⟩
  exact ⟨(s : Set K'), hs, hsep⟩

/-- For an algebraic extension, separably generatedness recovers the canonical mathlib notion
`Algebra.IsSeparable`. -/
theorem isSeparable (hK : IsSeparablyGenerated k' K') [Algebra.IsAlgebraic k' K'] :
    Algebra.IsSeparable k' K' := by
  rcases hK with ⟨s, hs, hsep⟩
  have hs_empty : s = ∅ := by
    exact Set.eq_empty_iff_forall_notMem.mpr fun y hy ↦ hs.1.isEmpty_of_isAlgebraic.false ⟨y, hy⟩
  subst s
  have hsep' : Algebra.IsSeparable (IntermediateField.adjoin k' (∅ : Set K')) K' := by
    simpa using hsep
  haveI : Algebra.IsSeparable (⊥ : IntermediateField k' K') K' := by
    rw [← IntermediateField.adjoin_empty k' K']
    exact hsep'
  haveI : Algebra.IsSeparable k' (⊥ : IntermediateField k' K') :=
    AlgEquiv.Algebra.isSeparable (IntermediateField.botEquiv k' K').symm
  exact Algebra.IsSeparable.trans k' (⊥ : IntermediateField k' K') K'

end IsSeparablyGenerated

/-- Definition 10.42.1 (2): a field extension `K / k` is separable if every finitely generated
intermediate extension `K'` of `K / k` is separably generated over `k`. -/
@[stacks 030O "(2)", mk_iff isSeparableOver_iff]
class IsSeparableOver : Prop where
  /-- Every finitely generated intermediate field of `K / k` is separably generated over `k`. -/
  isSeparablyGenerated_of_fg (L : IntermediateField k K) (hL : L.FG) :
    IsSeparablyGenerated k L

namespace IsSeparableOver

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
variable {L : Type w} [Field L] [Algebra F L]

private theorem fg_map {M : IntermediateField F E} (f : E →ₐ[F] L) (hM : M.FG) :
    (M.map f).FG :=
  IntermediateField.essFiniteType_iff.mp <|
    (EssFiniteType.iff_of_algEquiv (M.equivMap f)).mp <|
      IntermediateField.essFiniteType_iff.mpr hM

/-- Transport `IsSeparableOver` across a `k`-algebra equivalence. -/
theorem of_algEquiv (hK : IsSeparableOver F E) (e : E ≃ₐ[F] L) :
    IsSeparableOver F L := by
  refine ⟨fun M hM ↦ ?_⟩
  have hmap : (M.map e.symm.toAlgHom).FG := fg_map e.symm.toAlgHom hM
  have hmapSep : IsSeparablyGenerated F (M.map e.symm.toAlgHom) :=
    hK.isSeparablyGenerated_of_fg _ hmap
  exact hmapSep.of_algEquiv (M.equivMap e.symm.toAlgHom).symm

/-- An intermediate field of an extension that is separable in the Stacks Project sense is again
separable in the same sense. -/
theorem of_intermediateField (hK : IsSeparableOver F E) (L : IntermediateField F E) :
    IsSeparableOver F L := by
  refine ⟨fun M hM ↦ ?_⟩
  have hmap : (M.map L.val).FG := fg_map L.val hM
  exact (hK.isSeparablyGenerated_of_fg _ hmap).of_algEquiv (M.equivMap L.val).symm

/-- Over a perfect base field, every extension is separable in the Stacks Project sense. -/
theorem of_perfectField [PerfectField F] : IsSeparableOver F E := by
  refine ⟨fun M hM ↦ ?_⟩
  letI : Algebra.EssFiniteType F ↥M := (IntermediateField.essFiniteType_iff).2 hM
  exact IsSeparablyGenerated.of_perfectField

/-- For an algebraic extension, separability in the Stacks Project sense recovers the canonical
mathlib notion `Algebra.IsSeparable`. -/
theorem isSeparable (hK : IsSeparableOver F E) [Algebra.IsAlgebraic F E] :
    Algebra.IsSeparable F E := by
  rw [Algebra.isSeparable_iff]
  intro x
  let M : IntermediateField F E := IntermediateField.adjoin F ({x} : Set E)
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hM : IsSeparableOver F M := hK.of_intermediateField M
  have hMsepgen_top : IsSeparablyGenerated F (⊤ : IntermediateField F M) := by
    letI : FiniteDimensional F M := by
      simpa [M] using IntermediateField.adjoin.finiteDimensional hx
    exact hM.isSeparablyGenerated_of_fg ⊤ (IntermediateField.fg_top F M)
  have hMsepgen : IsSeparablyGenerated F M := by
    simpa using hMsepgen_top.of_algEquiv IntermediateField.topEquiv
  haveI : Algebra.IsAlgebraic F M := by
    simpa [M] using IntermediateField.isAlgebraic_adjoin_simple hx
  haveI : Algebra.IsSeparable F M := hMsepgen.isSeparable
  have hxM : x ∈ M := by
    simpa [M] using IntermediateField.mem_adjoin_simple_self F x
  exact ⟨hx, IntermediateField.isSeparable_of_mem_isSeparable F E hxM⟩

end IsSeparableOver

/- The owner specifications of Definition 10.42.1 are the companion theorems
`isSeparablyGenerated_iff` and `isSeparableOver_iff`; no extra bundled conjunction wrapper is
kept. -/

/-- A separable algebraic extension is separably generated, with empty transcendence basis. -/
instance [Algebra.IsSeparable k K] :
    IsSeparablyGenerated k K := by
  refine ⟨∅, ?_, ?_⟩
  · constructor
    · exact algebraicIndependent_empty
    · intro s hs hsub
      simpa [Set.range_eq_empty] using
        (Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ hs.isEmpty_of_isAlgebraic.false ⟨x, hx⟩).symm
  · rw [IntermediateField.adjoin_empty]
    infer_instance

/-- A finitely generated extension of a perfect field is separably generated. -/
@[instance low] instance [PerfectField k] [EssFiniteType k K] :
    IsSeparablyGenerated k K :=
  IsSeparablyGenerated.of_perfectField

/-- A separable algebraic extension is separable in the Stacks Project sense. -/
instance [Algebra.IsSeparable k K] : IsSeparableOver k K := by
  exact ⟨fun L _ ↦ inferInstance⟩

/-- Low-priority instance: over a perfect field, every extension is separable in the Stacks
Project sense. -/
@[instance low] instance [PerfectField k] : IsSeparableOver k K :=
  IsSeparableOver.of_perfectField

end Algebra

end

/-! ### Lemma_10_42_2 (from Chap10) -/
/-
Domain-style sampling for Lemma 10.42.2:
- primary domain: Stacks Project separability for field extensions and intermediate fields;
- sampled owner declarations:
  `Algebra.IsSeparableOver`,
  `Algebra.IsSeparableOver.of_intermediateField`,
  `Algebra.IsSeparableOver.of_algEquiv`,
  `Algebra.IsSeparableOver.isSeparable`;
- best owner abstraction: the chapter owner predicate `Algebra.IsSeparableOver`;
- primitive data: the owner predicate on `K / k` together with an intermediate field `K'`;
- derived API: transport to intermediate fields, transport across algebra equivalences, and the
  algebraic specialization to `Algebra.IsSeparable`.

Layer triage:
- `source-facing`: stability of Stacks Project separability under passing to an intermediate field;
- `core/canonical`: `Algebra.IsSeparableOver`;
- `bridge/view`: the owner theorem `Algebra.IsSeparableOver.of_intermediateField`.

Since Definition 10.42.1 already introduced the owner predicate and this lemma adds no new data,
the file should remain a pure recall surface rather than a parallel local theorem or wrapper.
-/

/- Lemma 10.42.2: if `K / k` is separable in the Stacks Project sense and `K'` is an
intermediate field in the tower `K / K' / k`, then the subextension `K' / k` is separable in the
same sense. -/
recall Algebra.IsSeparableOver.of_intermediateField

/-! ### Lemma_10_42_3 (from Chap10) -/
open scoped IntermediateField

universe u v

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- A point `y` is a one-element separable generator over the transcendence basis `x` if adjoining
`y` to the field generated by `x` yields all of `K`, and `y` is separable over that generated
field. -/
def IsOneSeparableGeneratorOver
    (x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K) (y : K) : Prop :=
  IntermediateField.adjoin k (Set.range x ∪ {y}) = ⊤ ∧
    IsSeparable (IntermediateField.adjoin k (Set.range x)) y

/-- Helper for Lemma 10.42.3: a transcendence basis witnessing separable generation can be
reindexed by `Fin (Cardinal.toNat (Algebra.trdeg k K))` without changing the generated
intermediate field. -/
lemma exists_fin_reindexed_transcendence_basis
    [Algebra.EssFiniteType k K]
    {s : Set K} (hs : IsTranscendenceBasis k (Subtype.val : s → K)) :
    ∃ x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K,
      IsTranscendenceBasis k x ∧
        IntermediateField.adjoin k (Set.range x) = IntermediateField.adjoin k s := by
  classical
  -- First show that finite generation forces the transcendence degree to be finite.
  have htrdeg : Algebra.trdeg k K < Cardinal.aleph0 := by
    obtain ⟨t, ht⟩ := IntermediateField.fg_top k K
    have ht_alg : Algebra.IsAlgebraic (Algebra.adjoin k (t : Set K)) K := by
      rw [← IntermediateField.isAlgebraic_adjoin_iff_top, ht, Algebra.isAlgebraic_iff_isIntegral]
      exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
    letI : Algebra.IsAlgebraic (Algebra.adjoin k (t : Set K)) K := ht_alg
    exact lt_of_le_of_lt (Algebra.IsAlgebraic.trdeg_le_cardinalMk k (t : Set K))
      (by simpa using t.finite_toSet.lt_aleph0)
  -- The witness set is therefore finite, so we may identify it with a finite `Fin` type.
  have hs_finite : s.Finite := by
    simpa [Set.Finite, ← Cardinal.mk_lt_aleph0_iff, hs.cardinalMk_eq_trdeg] using htrdeg
  letI : Finite s := hs_finite.to_subtype
  have hs_card : Nat.card s = Cardinal.toNat (Algebra.trdeg k K) := by
    simpa [Nat.card] using congrArg Cardinal.toNat hs.cardinalMk_eq_trdeg
  let e : s ≃ Fin (Cardinal.toNat (Algebra.trdeg k K)) := Finite.equivFinOfCardEq hs_card
  let x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K := fun i ↦ ((e.symm i : s) : K)
  have hx_range : Set.range x = s := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hy
      refine ⟨e ⟨y, hy⟩, ?_⟩
      simp [x]
  have hx_subtype : IsTranscendenceBasis k ((↑) : Set.range x → K) := by
    rw [hx_range]
    exact hs
  have hx_injective : Function.Injective x := by
    intro i j hij
    exact e.symm.injective (Subtype.val_injective hij)
  refine ⟨x, hx_subtype.of_subtype_range hx_injective, ?_⟩
  -- Reindexing does not change the underlying subset of generators.
  simpa [hx_range]

/-- Helper for Lemma 10.42.3: adjoining one element over `IntermediateField.adjoin k S` and then
restricting scalars back to `k` is the same as adjoining that element to `S` over `k`. -/
lemma restrictScalars_adjoin_singleton_eq_adjoin_union
    (S : Set K) (y : K) :
    ((IntermediateField.adjoin k S)⟮y⟯).restrictScalars k =
      IntermediateField.adjoin k (S ∪ {y}) := by
  -- This is the interface rewrite turning the primitive-element output into the target shape.
  calc
    ((IntermediateField.adjoin k S)⟮y⟯).restrictScalars k =
        IntermediateField.adjoin k S ⊔ IntermediateField.adjoin k ({y} : Set K) := by
          simpa using
            (IntermediateField.restrictScalars_adjoin_eq_sup (F := k) (E := K)
              (IntermediateField.adjoin k S) ({y} : Set K))
    _ = IntermediateField.adjoin k (S ∪ {y}) := by
      rw [IntermediateField.adjoin_union]

/-- Helper for Lemma 10.42.3: after adjoining a transcendence basis, a finitely generated field
extension becomes finite-dimensional over the generated intermediate field. -/
lemma finiteDimensional_over_adjoin_of_isTranscendenceBasis
    [Algebra.EssFiniteType k K]
    {ι : Type*} {x : ι → K} (hx : IsTranscendenceBasis k x) :
    FiniteDimensional (IntermediateField.adjoin k (Set.range x)) K := by
  -- The transcendence basis makes the extension algebraic, and finite generation upgrades that
  -- algebraicity to module-finiteness.
  letI : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K := hx.isAlgebraic_field
  letI : Algebra.EssFiniteType (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.EssFiniteType.of_comp k (IntermediateField.adjoin k (Set.range x)) K
  letI : Module.Finite (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  infer_instance

-- Proof sketch: choose a transcendence basis witnessing separable generation, replace it by a
-- basis indexed by `Fin (Cardinal.toNat (Algebra.trdeg k K))`, and then apply the primitive
-- element theorem to the finite separable extension over the generated intermediate field.
/-- Lemma 10.42.3: if `K / k` is a separably generated, finitely generated field extension and
`r = Cardinal.toNat (Algebra.trdeg k K)`, then there are `r` elements of `K` forming a
transcendence basis over `k` together with one additional element whose union with that basis
generates `K`, and which is separable over the field generated by the basis. -/
theorem exists_transcendence_basis_and_one_separable_generator
    [Algebra.EssFiniteType k K]
    [Algebra.IsSeparablyGenerated k K] :
    ∃ x : Fin (Cardinal.toNat (Algebra.trdeg k K)) → K,
      IsTranscendenceBasis k x ∧ ∃ y : K, IsOneSeparableGeneratorOver x y := by
  let hsepgen : Algebra.IsSeparablyGenerated k K := inferInstance
  rcases hsepgen with ⟨s, hs, hsep⟩
  -- Start from the separating transcendence basis provided by separable generation.
  rcases exists_fin_reindexed_transcendence_basis (k := k) (K := K) hs with ⟨x, hx, hx_adjoin⟩
  have hsep' : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K := by
    rw [hx_adjoin]
    exact hsep
  have hfd : FiniteDimensional (IntermediateField.adjoin k (Set.range x)) K :=
    finiteDimensional_over_adjoin_of_isTranscendenceBasis (k := k) (K := K) hx
  letI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K := hsep'
  letI : FiniteDimensional (IntermediateField.adjoin k (Set.range x)) K := hfd
  -- Apply the primitive element theorem over the intermediate field generated by the basis.
  obtain ⟨y, hy⟩ := Field.exists_primitive_element
    (IntermediateField.adjoin k (Set.range x)) K
  refine ⟨x, hx, y, ?_⟩
  constructor
  · -- Restrict scalars to rewrite the primitive-element equality into a `k`-adjoin statement.
    have hy_restrict :
        ((IntermediateField.adjoin k (Set.range x))⟮y⟯).restrictScalars k = ⊤ := by
      simpa using
        congrArg
          (fun M : IntermediateField (IntermediateField.adjoin k (Set.range x)) K ↦
            M.restrictScalars k)
          hy
    simpa [restrictScalars_adjoin_singleton_eq_adjoin_union] using hy_restrict
  · -- Elementwise separability follows from the separable algebra structure over the basis field.
    simpa using Algebra.IsSeparable.isSeparable (IntermediateField.adjoin k (Set.range x)) y

end
