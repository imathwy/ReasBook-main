import Mathlib.FieldTheory.SeparablyGenerated

-- Declarations for this item will be appended below by the statement pipeline.

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
