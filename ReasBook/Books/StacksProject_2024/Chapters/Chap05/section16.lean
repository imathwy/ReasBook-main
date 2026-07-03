import Mathlib.Topology.Constructible

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_5_16_1 (from Chap05) -/
universe u

open Set Topology TopologicalSpace

section

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for constructible subsets in Noetherian spaces:
- primary domain: constructible, locally closed, and Noetherian topological subsets
- inspected declarations:
  `Topology.IsConstructible.isFiniteUnionOfLocallyClosed`,
  `IsLocallyClosed.isConstructible_of_isCompact_of_retrocompact_compl`,
  `Topology.IsConstructible.sUnion`,
  `TopologicalSpace.NoetherianSpace.isCompact`,
  `isRetrocompact_of_noetherianSpace`
- best owner abstraction: `Topology.IsConstructible`

Layer triage:
- `source-facing`: the equivalence between constructibility and finite unions of locally closed
  subsets in a Noetherian space
- `core/canonical`: the owner predicate `Topology.IsConstructible`
- `bridge/view`: the chapter predicate `IsFiniteUnionOfLocallyClosed`

Primitive data is only the ambient `NoetherianSpace` instance together with the locally closed
pieces in a finite union. The finite-union predicate is a bridge/view API, so the reverse
direction should unpack it and rebuild constructibility from the owner-level operations on
`IsConstructible`, reusing the earlier locally closed-to-constructible bridge rather than
reintroducing a parallel proof of the same conversion.
-/

-- Proof sketch: the forward implication is the existing owner-level bridge
-- `IsConstructible.isFiniteUnionOfLocallyClosed`. For the converse, unpack the finite union and
-- apply the earlier theorem that a locally closed compact subset with retrocompact complement is
-- constructible; in a Noetherian space those compactness and retrocompactness hypotheses are
-- automatic for every subset.
/-- Lemma 5.16.1: in a Noetherian topological space, the constructible subsets are exactly the
finite unions of locally closed subsets. -/
theorem isConstructible_iff_isFiniteUnionOfLocallyClosed_of_noetherian
    [NoetherianSpace X] {s : Set X} :
    IsConstructible s ↔ IsFiniteUnionOfLocallyClosed s := by
  constructor
  · exact IsConstructible.isFiniteUnionOfLocallyClosed
  · rintro ⟨S, hSfinite, hS, rfl⟩
    refine IsConstructible.sUnion hSfinite fun Z hZ ↦ ?_
    exact (hS Z hZ).isConstructible_of_isCompact_of_retrocompact_compl
      (NoetherianSpace.isCompact Z) (isRetrocompact_of_noetherianSpace Zᶜ)

end

/-! ### Lemma_5_16_2 (from Chap05) -/
universe u v

open Set TopologicalSpace Topology

namespace Topology

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [NoetherianSpace X] {f : X → Y}

/- Domain-style sampling for constructible pullbacks in Noetherian spaces:
- primary domain: constructible subsets, retrocompact opens, and pullback stability in topology;
- sampled owner/domain declarations:
  `IsConstructible.preimage`,
  `IsConstructible.preimage_of_isOpenEmbedding`,
  `IsConstructible.preimage_of_isClosedEmbedding`,
  `isRetrocompact_of_noetherianSpace`;
- best owner abstraction: `Topology.IsConstructible.preimage`;
- primitive-vs-derived split: the primitive data are the constructible subset `E`, the continuity
  of `f`, and the source-side `NoetherianSpace` instance. The retrocompact-open preimage condition
  required by the owner theorem is derived from `isRetrocompact_of_noetherianSpace`, so it should
  not remain separate public data here.

Layer triage:
- `source-facing`: Stacks Lemma 5.16.2, the Noetherian-source specialization of constructible
  pullback stability;
- `core/canonical`: `Topology.IsConstructible.preimage`;
- `bridge/view`: this file's specialization obtained by deriving the retrocompact-open pullback
  hypothesis from `NoetherianSpace X`.
-/

-- Proof sketch: apply the owner theorem `Topology.IsConstructible.preimage`. In a Noetherian
-- source space every subset is retrocompact, so the required retrocompactness of the preimage of
-- an open retrocompact subset of `Y` is automatic.
/-- Lemma 5.16.2: for a continuous map with Noetherian source, the preimage of a constructible set
is constructible. -/
theorem IsConstructible.preimage_of_continuous_of_noetherianSpace
    {E : Set Y} (hE : IsConstructible E) (hf : Continuous f) :
    IsConstructible (f ⁻¹' E) :=
  hE.preimage hf fun _ _ _ ↦ isRetrocompact_of_noetherianSpace _

end

end Topology

/-! ### Lemma_5_16_3 (from Chap05) -/
universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

namespace Topology

section

variable {X : Type u} [TopologicalSpace X]

-- Proof sketch: first use `IsConstructible.isFiniteUnionOfLocallyClosed` on `E`, then apply the
-- earlier irreducible-space theorem that a finite union of locally closed subsets has dense trace
-- on `Z` exactly when it contains an open dense subset of `Z`.
/-- A constructible subset has, on each irreducible closed trace, either a nonempty open subtrace
or a non-dense trace. -/
theorem IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense {E : Set X}
    (hE : IsConstructible E) (Z : IrreducibleCloseds X) :
    (∃ U : Opens Z, (U : Set Z).Nonempty ∧ (U : Set Z) ⊆ (Z : Set X) ↓∩ E) ∨
      ¬ Dense ((Z : Set X) ↓∩ E) := by
  have hE_lc : IsFiniteUnionOfLocallyClosed E := hE.isFiniteUnionOfLocallyClosed
  letI : Nonempty Z := by
    rcases Z.isIrreducible.nonempty with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  by_cases hDense : Dense (((Z : Set X) ↓∩ E) : Set Z)
  · left
    obtain ⟨U, hU_dense, hU_subset⟩ :=
      (Z.isIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed
        hE_lc).2 hDense
    exact ⟨U, hU_dense.nonempty, hU_subset⟩
  · exact Or.inr hDense

end

end Topology

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.3: the trace of `A ∩ E` inside `Y` is the image of the trace of `E`
inside `A` under the canonical inclusion `A → Y`. -/
lemma image_trace_inclusion_eq_trace {E : Set X} {A Y : Closeds X}
    (hAY : (A : Set X) ⊆ Y) :
    ((inclusion hAY) '' ((((A : Set X) ↓∩ E) : Set A)) : Set Y) =
      ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) := by
  -- Unpack both sides pointwise and identify the same underlying ambient point.
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using And.intro a.2 ha
  · intro hy
    simp only [Set.mem_preimage, Set.mem_inter_iff] at hy
    refine ⟨⟨y.1, hy.1⟩, hy.2, ?_⟩
    ext
    rfl

/-- Helper for Lemma 5.16.3: a constructible trace on a smaller closed subset remains
constructible after pushing it into the ambient closed subspace. -/
lemma constructible_trace_image_of_smaller_closed {E : Set X} {A Y : Closeds X}
    (hAY : (A : Set X) ⊆ Y) (hA : IsConstructible ((A : Set X) ↓∩ E)) :
    IsConstructible ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) := by
  -- Push forward along the closed embedding `A → Y` and rewrite the image as the expected trace.
  have hClosedEmbedding : IsClosedEmbedding (inclusion hAY : A → Y) :=
    Topology.IsClosedEmbedding.inclusion hAY (A.2.preimage continuous_subtype_val)
  have hImage :
      IsConstructible ((inclusion hAY) '' ((((A : Set X) ↓∩ E) : Set A)) : Set Y) :=
    hA.image_of_isClosedEmbedding hClosedEmbedding
      (isRetrocompact_of_noetherianSpace ((Set.range (inclusion hAY : A → Y))ᶜ))
  simpa [image_trace_inclusion_eq_trace (E := E) hAY] using hImage

omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.3: removing a nonempty open subset from a closed subspace produces a
proper closed subset of the ambient space whose trace in the original subspace is the complement
of that open subset. -/
lemma proper_closed_below_of_open_complement (Y : Closeds X) (U : Opens Y)
    (hU_nonempty : (U : Set Y).Nonempty) :
    ∃ A : Closeds X, A < Y ∧ ((Y : Set X) ↓∩ (A : Set X)) = (U : Set Y)ᶜ := by
  let Aset : Set X := (Subtype.val : Y → X) '' ((U : Set Y)ᶜ)
  have hAclosed : IsClosed Aset :=
    Y.2.isClosedMap_subtype_val _ U.2.isClosed_compl
  let A : Closeds X := ⟨Aset, hAclosed⟩
  have hAY : (A : Set X) ⊆ Y := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hTrace : ((Y : Set X) ↓∩ (A : Set X)) = (U : Set Y)ᶜ := by
    -- The image of the closed complement inside `Y` is exactly that complement.
    ext y
    constructor
    · intro hy
      rcases hy with ⟨z, hz, hzEq⟩
      have hzEq' : z = y := by
        apply Subtype.ext
        simpa using hzEq
      simpa [hzEq'] using hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hAneY : A ≠ Y := by
    -- A point of the nonempty open `U` witnesses that the complement is proper.
    intro hAYeq
    have hUnivEq : (Set.univ : Set Y) = (U : Set Y)ᶜ := by
      calc
        (Set.univ : Set Y) = ((Y : Set X) ↓∩ (A : Set X)) := by
          ext y
          simp [hAYeq]
        _ = (U : Set Y)ᶜ := hTrace
    obtain ⟨y, hyU⟩ := hU_nonempty
    have hyCompl : y ∈ (U : Set Y)ᶜ := by
      simpa [hUnivEq] using (show y ∈ (Set.univ : Set Y) from trivial)
    exact hyCompl hyU
  exact ⟨A, lt_of_le_of_ne hAY hAneY, hTrace⟩

omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.3: a non-dense trace is already supported on a proper closed subset of
the ambient closed subspace. -/
lemma proper_closed_below_of_not_dense_trace {E : Set X} (Y : Closeds X)
    (hNotDense : ¬ Dense (((Y : Set X) ↓∩ E) : Set Y)) :
    ∃ A : Closeds X, A < Y ∧
      ((Y : Set X) ↓∩ E) = ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) := by
  let T : Set Y := ((Y : Set X) ↓∩ E)
  let Aset : Set X := (Subtype.val : Y → X) '' closure T
  have hAclosed : IsClosed Aset := Y.2.isClosedMap_subtype_val _ isClosed_closure
  let A : Closeds X := ⟨Aset, hAclosed⟩
  have hAY : (A : Set X) ⊆ Y := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hClosureTrace : ((Y : Set X) ↓∩ (A : Set X)) = closure T := by
    -- By construction, `A` is the ambient image of the closure of the trace inside `Y`.
    ext y
    constructor
    · intro hy
      rcases hy with ⟨z, hz, hzEq⟩
      have hzEq' : z = y := by
        apply Subtype.ext
        simpa using hzEq
      simpa [hzEq'] using hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hTraceEq :
      T = ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) := by
    -- Every point of the trace lies in its closure, so intersecting with `A` does not change it.
    ext y
    constructor
    · intro hy
      have hyA : y ∈ ((Y : Set X) ↓∩ (A : Set X)) := by
        rw [hClosureTrace]
        exact subset_closure hy
      simp only [Set.mem_preimage, Set.mem_inter_iff] at hy hyA ⊢
      exact ⟨hyA, hy⟩
    · intro hy
      simp only [Set.mem_preimage, Set.mem_inter_iff] at hy
      exact hy.2
  have hAneY : A ≠ Y := by
    -- If `A = Y`, then the closure of the trace is all of `Y`, contradicting non-density.
    intro hAYeq
    have hClosureUniv : closure T = (Set.univ : Set Y) := by
      calc
        closure T = ((Y : Set X) ↓∩ (A : Set X)) := hClosureTrace.symm
        _ = (Set.univ : Set Y) := by
          ext y
          simp [hAYeq]
    exact hNotDense (dense_iff_closure_eq.2 hClosureUniv)
  exact ⟨A, lt_of_le_of_ne hAY hAneY, by simpa [T] using hTraceEq⟩

/-
Domain-style sampling for constructible subsets detected on irreducible closed traces:
- primary domain: constructible subsets in Noetherian spaces, tested by their traces on
  irreducible closed subspaces;
- inspected declarations:
  `Topology.IsConstructible`,
  `Topology.IsConstructible.isFiniteUnionOfLocallyClosed`,
  `IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed`,
  `Topology.IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`,
  the canonical subtype-trace notation `↓∩`;
- best owner abstraction: `Topology.IsConstructible`.

Layer triage:
- `source-facing`: the Stacks Project criterion for constructibility via traces on irreducible
  closed subsets;
- `core/canonical`: the owner predicate `Topology.IsConstructible`;
- `bridge/view`: the bundled irreducible closed subspace `Z : IrreducibleCloseds X` together with
  the canonical subtype trace `(Z : Set X) ↓∩ E`.

Primitive data is the ambient Noetherian topology together with the owner predicate
`IsConstructible E`. The finite-union-of-locally-closed decomposition of a trace and the
nonempty-open trace alternative are both derived API, supplied respectively by
`IsConstructible.isFiniteUnionOfLocallyClosed` and the owner-facing theorem
`IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`. The bundled irreducible closed
subspaces and the subtype-trace notation are the canonical bridge/view API, so the numbered item
should reuse that owner-facing theorem rather than carrying a parallel forward-direction argument.
-/

-- Proof sketch: the forward implication is the owner-facing theorem
-- `IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`. For the converse, argue by
-- Noetherian induction on closed subsets whose trace is not constructible, reduce to the
-- irreducible case, and use the stated dichotomy to contradict minimality.
/-- Lemma 5.16.3: in a Noetherian topological space, a subset `E` is constructible if and only if
for every irreducible closed subset `Z`, the trace of `E` on `Z` either contains a nonempty open
subset of `Z` or is not dense in `Z`. -/
theorem isConstructible_iff_forall_irreducibleCloseds_containsNonemptyOpen_or_not_dense
    (E : Set X) :
    IsConstructible E ↔
      ∀ Z : IrreducibleCloseds X,
        (∃ U : Opens Z, (U : Set Z).Nonempty ∧ (U : Set Z) ⊆ (Z : Set X) ↓∩ E) ∨
          ¬ Dense ((Z : Set X) ↓∩ E) := by
  constructor
  · intro hE Z
    exact hE.exists_nonemptyOpen_subset_trace_or_not_dense Z
  · intro hTrace
    -- Execute the textbook minimal-counterexample proof as well-founded induction on closed sets.
    have hClosedTrace : ∀ Y : Closeds X, IsConstructible ((Y : Set X) ↓∩ E) := by
      intro Y
      induction Y using WellFoundedLT.induction with
      | ind Y ih =>
          by_cases hYempty : (Y : Set X) = ∅
          · -- The empty closed subspace has empty trace.
            have hYbot : Y = ⊥ := Closeds.ext (by simpa using hYempty)
            subst hYbot
            have hEmptyTrace : ((((⊥ : Closeds X) : Set X) ↓∩ E) : Set (⊥ : Closeds X)) = ∅ := by
              ext x
              exact False.elim x.2
            rw [hEmptyTrace]
            exact IsConstructible.empty
          · by_cases hYirred : IsIrreducible (Y : Set X)
            · -- In the irreducible case, use the stated dichotomy on the trace.
              have hYtrace :
                  (∃ U : Opens Y, (U : Set Y).Nonempty ∧ (U : Set Y) ⊆ (Y : Set X) ↓∩ E) ∨
                    ¬ Dense ((Y : Set X) ↓∩ E) := by
                let Z : IrreducibleCloseds X := ⟨(Y : Set X), hYirred, Y.2⟩
                simpa [Z] using hTrace Z
              rcases hYtrace with ⟨U, hU_nonempty, hU_subset⟩ | hY_not_dense
              · -- Split the trace into the given open piece and the constructible remainder.
                obtain ⟨A, hAYlt, hAtrace⟩ :=
                  proper_closed_below_of_open_complement Y U hU_nonempty
                have hA_constructible : IsConstructible ((A : Set X) ↓∩ E) := ih A hAYlt
                have hA_in_Y :
                    IsConstructible ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) :=
                  constructible_trace_image_of_smaller_closed hAYlt.le hA_constructible
                letI : NoetherianSpace Y := TopologicalSpace.NoetherianSpace.set (Y : Set X)
                have hU_constructible : IsConstructible (U : Set Y) :=
                  (isRetrocompact_of_noetherianSpace (U : Set Y)).isConstructible U.2
                have hTraceUnion :
                    ((Y : Set X) ↓∩ E) =
                      (U : Set Y) ∪ ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) := by
                  ext y
                  constructor
                  · intro hy
                    by_cases hyU : y ∈ (U : Set Y)
                    · exact Or.inl hyU
                    · right
                      have hyA : y ∈ ((Y : Set X) ↓∩ (A : Set X)) := by
                        rw [hAtrace]
                        exact hyU
                      simp only [Set.mem_preimage, Set.mem_inter_iff] at hy hyA ⊢
                      exact ⟨hyA, hy⟩
                  · rintro (hyU | hyA)
                    · exact hU_subset hyU
                    · simp only [Set.mem_preimage, Set.mem_inter_iff] at hyA
                      exact hyA.2
                rw [hTraceUnion]
                exact hU_constructible.union hA_in_Y
              · -- A non-dense trace is already carried by a proper closed subset.
                obtain ⟨A, hAYlt, hTraceEq⟩ :=
                  proper_closed_below_of_not_dense_trace (E := E) Y hY_not_dense
                have hA_constructible : IsConstructible ((A : Set X) ↓∩ E) := ih A hAYlt
                have hA_in_Y :
                    IsConstructible ((Y : Set X) ↓∩ ((A : Set X) ∩ E)) :=
                  constructible_trace_image_of_smaller_closed hAYlt.le hA_constructible
                rw [hTraceEq]
                exact hA_in_Y
            · -- If the closed subset is reducible, decompose it into two proper closed pieces.
              have hYnonempty : ((Y : Set X) : Set X).Nonempty :=
                Set.nonempty_iff_ne_empty.mpr hYempty
              have hYnotPreirred : ¬ IsPreirreducible (Y : Set X) := by
                intro hYpreirred
                exact hYirred ⟨hYnonempty, hYpreirred⟩
              simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hYnotPreirred
              obtain ⟨Z₁, Z₂, hZ₁_closed, hZ₂_closed, hY_subset, hZ₁_proper, hZ₂_proper⟩ :=
                hYnotPreirred
              lift Z₁ to Closeds X using hZ₁_closed
              lift Z₂ to Closeds X using hZ₂_closed
              have hYZ₁_constructible : IsConstructible (((Y ⊓ Z₁ : Closeds X) : Set X) ↓∩ E) :=
                ih (Y ⊓ Z₁) (inf_lt_left.2 hZ₁_proper)
              have hYZ₂_constructible : IsConstructible (((Y ⊓ Z₂ : Closeds X) : Set X) ↓∩ E) :=
                ih (Y ⊓ Z₂) (inf_lt_left.2 hZ₂_proper)
              have hYZ₁_in_Y :
                  IsConstructible ((Y : Set X) ↓∩ ((((Y ⊓ Z₁ : Closeds X) : Set X)) ∩ E)) :=
                constructible_trace_image_of_smaller_closed (E := E) inf_le_left
                  hYZ₁_constructible
              have hYZ₂_in_Y :
                  IsConstructible ((Y : Set X) ↓∩ ((((Y ⊓ Z₂ : Closeds X) : Set X)) ∩ E)) :=
                constructible_trace_image_of_smaller_closed (E := E) inf_le_left
                  hYZ₂_constructible
              have hTraceUnion :
                  ((Y : Set X) ↓∩ E) =
                    ((Y : Set X) ↓∩ ((((Y ⊓ Z₁ : Closeds X) : Set X)) ∩ E)) ∪
                      ((Y : Set X) ↓∩ ((((Y ⊓ Z₂ : Closeds X) : Set X)) ∩ E)) := by
                ext y
                constructor
                · intro hy
                  have hyCover : y.1 ∈ (Z₁ : Set X) ∪ (Z₂ : Set X) := hY_subset y.2
                  rcases hyCover with hyZ₁ | hyZ₂
                  · left
                    simp only [Set.mem_preimage, Set.mem_inter_iff] at hy ⊢
                    exact ⟨⟨y.2, hyZ₁⟩, hy⟩
                  · right
                    simp only [Set.mem_preimage, Set.mem_inter_iff] at hy ⊢
                    exact ⟨⟨y.2, hyZ₂⟩, hy⟩
                · rintro (hy | hy) <;>
                    simp only [Set.mem_preimage, Set.mem_inter_iff] at hy
                  · exact hy.2
                  · exact hy.2
              rw [hTraceUnion]
              exact hYZ₁_in_Y.union hYZ₂_in_Y
    -- Apply the closed-subspace induction to the universal closed subset and unwrap the subtype.
    have hTop : IsConstructible (((Set.univ : Set X) ↓∩ E) : Set (Set.univ : Set X)) := by
      simpa using hClosedTrace ⊤
    exact
      (isConstructible_preimage_iff_of_isOpenEmbedding isOpen_univ.isOpenEmbedding_subtypeVal
        (by simp [isRetrocompact_of_noetherianSpace]) (by simp)).1 hTop

end

/-! ### Lemma_5_16_4 (from Chap05) -/
universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

namespace Topology

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

/-
Domain-style sampling for constructible neighborhoods detected by irreducible closed traces:
- primary domain: constructible subsets in Noetherian spaces, local neighborhoods, and dense traces
  on irreducible closed subspaces;
- sampled owner declarations:
  `Topology.IsConstructible`,
  `Topology.IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense`,
  `TopologicalSpace.IrreducibleCloseds`,
  the canonical trace notation `↓∩`;
- best owner abstraction: `Topology.IsConstructible`;
- primitive vs. derived split: the primitive datum is the owner predicate `IsConstructible E`; the
  dense-trace criterion is derived local API on the canonical bridge object
  `Y : IrreducibleCloseds X`, so the numbered item should live as an owner theorem rather than as a
  parallel global wrapper.

Layer triage:
- `source-facing`: the Stacks criterion for when a constructible subset is a neighborhood of a
  point;
- `core/canonical`: the owner predicate `Topology.IsConstructible`;
- `bridge/view`: dense traces on `IrreducibleCloseds X` via `(Y : Set X) ↓∩ E`.
-/

-- Proof sketch: if `E ∈ 𝓝 x`, then its trace on any irreducible closed subspace through `x`
-- contains a neighborhood of `x` in that subspace, hence is dense there. Conversely, among closed
-- subsets through `x` on which the trace is not a neighborhood, choose a minimal one using
-- Noetherianity; prove it is irreducible, use the dense-trace hypothesis and the previous lemma
-- that a dense constructible subset of an irreducible Noetherian space contains a nonempty open,
-- and derive a contradiction.
omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.4: an ambient neighborhood of `x` restricts to a dense trace on every
irreducible closed subspace through `x`. -/
lemma dense_trace_of_mem_nhds {E : Set X} {x : X} (hEx : E ∈ 𝓝 x)
    (Y : IrreducibleCloseds X) (hxY : x ∈ Y) :
    Dense ((Y : Set X) ↓∩ E) := by
  -- Pull the ambient neighborhood back to the irreducible closed subspace.
  have hTraceNhds : ((Y : Set X) ↓∩ E) ∈ 𝓝 (⟨x, hxY⟩ : Y) := by
    simpa using (preimage_coe_mem_nhds_subtype.2 (nhdsWithin_le_nhds hEx))
  rcases mem_nhds_iff.mp hTraceNhds with ⟨U, hU_subset, hU_open, hxU⟩
  letI : IrreducibleSpace Y := Subtype.irreducibleSpace Y.isIrreducible
  -- Any nonempty open subset of an irreducible space is dense.
  exact Dense.mono hU_subset (hU_open.dense ⟨⟨x, hxY⟩, hxU⟩)

omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.4: a neighborhood of the trace on a smaller closed subspace can be
lifted to an ambient open neighborhood whose restriction still lands in the target trace. -/
lemma trace_mem_nhds_parent_of_trace_mem_nhds_closed {E : Set X} {A Y : Closeds X}
    (hAY : A ≤ Y) {x : X} (hxA : x ∈ A)
    (hA : ((A : Set X) ↓∩ E) ∈ 𝓝 (⟨x, hxA⟩ : A)) :
    ∃ V : Opens Y, (⟨x, hAY hxA⟩ : Y) ∈ V ∧
      (V : Set Y) ∩ ((Y : Set X) ↓∩ (A : Set X)) ⊆ ((Y : Set X) ↓∩ E) := by
  -- Realize the neighborhood on `A` as the pullback of an ambient neighborhood in `X`.
  have hA' :=
    (mem_nhds_subtype (A : Set X) ⟨x, hxA⟩ (((A : Set X) ↓∩ E) : Set A)).1 hA
  rcases hA' with ⟨u, hu, hpre⟩
  rcases mem_nhds_iff.mp hu with ⟨s, hs_subset, hs_open, hxs⟩
  let V : Opens Y := ⟨(Y : Set X) ↓∩ s, hs_open.preimage continuous_subtype_val⟩
  refine ⟨V, ?_, ?_⟩
  · -- The lifted ambient open set still contains `x`.
    simpa [V] using hxs
  · -- Points of `V` lying in `A` map back into the trace on `A`, hence into `E`.
    intro y hy
    rcases hy with ⟨hyV, hyA⟩
    have hys : y.1 ∈ s := by
      simpa [V] using hyV
    have hyA' : y.1 ∈ A := by
      simpa [Set.mem_preimage, Set.mem_inter_iff] using hyA
    have hmemU : (⟨y.1, hyA'⟩ : A) ∈ Subtype.val ⁻¹' u := by
      change y.1 ∈ u
      exact hs_subset hys
    have hmemTrace : (⟨y.1, hyA'⟩ : A) ∈ ((A : Set X) ↓∩ E) := hpre hmemU
    simpa [Set.mem_preimage, Set.mem_inter_iff] using hmemTrace

omit [NoetherianSpace X] in
/-- Helper for Lemma 5.16.4: removing an open subtrace from a closed subspace leaves a proper
closed complement inside the ambient space. -/
lemma proper_closed_of_open_trace_complement (Y : Closeds X) (U : Opens Y)
    (hU_nonempty : (U : Set Y).Nonempty) :
    ∃ A : Closeds X, A < Y ∧ ((Y : Set X) ↓∩ (A : Set X)) = (U : Set Y)ᶜ := by
  -- Build the closed complement in the ambient space as the image of the complement inside `Y`.
  let Aset : Set X := (Subtype.val : Y → X) '' ((U : Set Y)ᶜ)
  have hAclosed : IsClosed Aset :=
    Y.2.isClosedMap_subtype_val _ U.2.isClosed_compl
  let A : Closeds X := ⟨Aset, hAclosed⟩
  have hAY : (A : Set X) ⊆ Y := by
    rintro x ⟨y, hy, rfl⟩
    exact y.2
  have hTrace : ((Y : Set X) ↓∩ (A : Set X)) = (U : Set Y)ᶜ := by
    -- The image of the closed complement inside `Y` is exactly that complement.
    ext y
    constructor
    · intro hy
      rcases hy with ⟨z, hz, hzEq⟩
      have hzEq' : z = y := by
        apply Subtype.ext
        simpa using hzEq
      simpa [hzEq'] using hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hAneY : A ≠ Y := by
    -- A point of the nonempty open subset witnesses that the complement is proper.
    intro hAYeq
    have hUnivEq : (Set.univ : Set Y) = (U : Set Y)ᶜ := by
      calc
        (Set.univ : Set Y) = ((Y : Set X) ↓∩ (A : Set X)) := by
          ext y
          simp [hAYeq]
        _ = (U : Set Y)ᶜ := hTrace
    obtain ⟨y, hyU⟩ := hU_nonempty
    have hyCompl : y ∈ (U : Set Y)ᶜ := by
      simpa [hUnivEq] using (show y ∈ (Set.univ : Set Y) from trivial)
    exact hyCompl hyU
  exact ⟨A, lt_of_le_of_ne hAY hAneY, hTrace⟩

/-- Lemma 5.16.4: for a constructible subset `E` of a Noetherian topological space `X`, `E` is a
neighborhood of `x` if and only if for every irreducible closed subset `Y` of `X` containing `x`,
the trace of `E` on the subspace `Y` is dense in `Y`. -/
theorem IsConstructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace
    {E : Set X} (hE : IsConstructible E) {x : X} :
    E ∈ 𝓝 x ↔
      ∀ Y : IrreducibleCloseds X, x ∈ Y →
        Dense ((Y : Set X) ↓∩ E) := by
  constructor
  · intro hEx Y hxY
    -- Restrict the ambient neighborhood to the irreducible closed trace.
    exact dense_trace_of_mem_nhds hEx Y hxY
  · intro hDense
    -- Follow the source proof by induction on closed subsets through `x`.
    have hTraceNhds :
        ∀ Y : Closeds X, ∀ hxY : x ∈ Y, ((Y : Set X) ↓∩ E) ∈ 𝓝 (⟨x, hxY⟩ : Y) := by
      intro Y
      induction Y using WellFoundedLT.induction with
      | ind Y ih =>
          intro hxY
          by_cases hYirred : IsIrreducible (Y : Set X)
          · -- In the irreducible case, use the dense-trace hypothesis and split off an open piece.
            let Z : IrreducibleCloseds X := ⟨(Y : Set X), hYirred, Y.2⟩
            have hDenseY : Dense ((Y : Set X) ↓∩ E) := by
              simpa [Z] using hDense Z hxY
            rcases hE.exists_nonemptyOpen_subset_trace_or_not_dense Z with
              hOpen | hNotDense
            · rcases hOpen with ⟨U, hU_nonempty, hU_subset⟩
              by_cases hxU : (⟨x, hxY⟩ : Y) ∈ U
              · -- If the open trace already contains `x`, it is the desired neighborhood.
                exact mem_nhds_iff.2 ⟨U, hU_subset, U.2, hxU⟩
              · -- Otherwise remove that open piece and appeal to induction on the closed complement.
                obtain ⟨A, hAYlt, hAtrace⟩ :=
                  proper_closed_of_open_trace_complement Y U hU_nonempty
                have hxA : x ∈ A := by
                  have hxAtrace : (⟨x, hxY⟩ : Y) ∈ ((Y : Set X) ↓∩ (A : Set X)) := by
                    rw [hAtrace]
                    exact hxU
                  simpa [Set.mem_preimage, Set.mem_inter_iff] using hxAtrace
                have hA_nhds :
                    ((A : Set X) ↓∩ E) ∈ 𝓝 (⟨x, hxA⟩ : A) :=
                  ih A hAYlt hxA
                obtain ⟨V, hxV, hV_subset⟩ :=
                  trace_mem_nhds_parent_of_trace_mem_nhds_closed (E := E) hAYlt.le hxA hA_nhds
                have hUnionSubset :
                    (U : Set Y) ∪ (V : Set Y) ⊆ ((Y : Set X) ↓∩ E) := by
                  intro y hy
                  rcases hy with hyU | hyV
                  · exact hU_subset hyU
                  · by_cases hyU : y ∈ (U : Set Y)
                    · exact hU_subset hyU
                    · have hyA : y ∈ ((Y : Set X) ↓∩ (A : Set X)) := by
                        rw [hAtrace]
                        exact hyU
                      exact hV_subset ⟨hyV, hyA⟩
                exact mem_nhds_iff.2 ⟨(U : Set Y) ∪ (V : Set Y), hUnionSubset, U.2.union V.2,
                  Or.inr hxV⟩
            · exact False.elim (hNotDense hDenseY)
          · -- If the closed subset is reducible, glue the smaller closed pieces through `x`.
            have hYnonempty : ((Y : Set X) : Set X).Nonempty := ⟨x, hxY⟩
            have hYnotPreirred : ¬ IsPreirreducible (Y : Set X) := by
              intro hYpreirred
              exact hYirred ⟨hYnonempty, hYpreirred⟩
            simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hYnotPreirred
            obtain ⟨Z₁, Z₂, hZ₁_closed, hZ₂_closed, hY_subset, hZ₁_proper, hZ₂_proper⟩ :=
              hYnotPreirred
            lift Z₁ to Closeds X using hZ₁_closed
            lift Z₂ to Closeds X using hZ₂_closed
            by_cases hxZ₁ : x ∈ Z₁
            · by_cases hxZ₂ : x ∈ Z₂
              · -- If `x` lies in both pieces, intersect the two induced neighborhoods.
                have hA₁_nhds :
                    (((Y ⊓ Z₁ : Closeds X) : Set X) ↓∩ E) ∈
                      𝓝 (⟨x, show x ∈ (Y ⊓ Z₁ : Closeds X) by exact ⟨hxY, hxZ₁⟩⟩ :
                        (Y ⊓ Z₁ : Closeds X)) :=
                  ih (Y ⊓ Z₁) (inf_lt_left.2 hZ₁_proper) ⟨hxY, hxZ₁⟩
                have hA₂_nhds :
                    (((Y ⊓ Z₂ : Closeds X) : Set X) ↓∩ E) ∈
                      𝓝 (⟨x, show x ∈ (Y ⊓ Z₂ : Closeds X) by exact ⟨hxY, hxZ₂⟩⟩ :
                        (Y ⊓ Z₂ : Closeds X)) :=
                  ih (Y ⊓ Z₂) (inf_lt_left.2 hZ₂_proper) ⟨hxY, hxZ₂⟩
                obtain ⟨V₁, hxV₁, hV₁_subset⟩ :=
                  trace_mem_nhds_parent_of_trace_mem_nhds_closed (E := E) inf_le_left
                    ⟨hxY, hxZ₁⟩ hA₁_nhds
                obtain ⟨V₂, hxV₂, hV₂_subset⟩ :=
                  trace_mem_nhds_parent_of_trace_mem_nhds_closed (E := E) inf_le_left
                    ⟨hxY, hxZ₂⟩ hA₂_nhds
                have hInterSubset :
                    (V₁ : Set Y) ∩ (V₂ : Set Y) ⊆ ((Y : Set X) ↓∩ E) := by
                  intro y hy
                  have hyCover : y.1 ∈ (Z₁ : Set X) ∪ (Z₂ : Set X) := hY_subset y.2
                  rcases hyCover with hyZ₁ | hyZ₂
                  · have hyA₁ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₁ : Closeds X) : Set X)) := by
                      simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₁]
                    exact hV₁_subset ⟨hy.1, hyA₁⟩
                  · have hyA₂ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₂ : Closeds X) : Set X)) := by
                      simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₂]
                    exact hV₂_subset ⟨hy.2, hyA₂⟩
                exact mem_nhds_iff.2 ⟨(V₁ : Set Y) ∩ (V₂ : Set Y), hInterSubset, V₁.2.inter V₂.2,
                  ⟨hxV₁, hxV₂⟩⟩
              · -- If `x` misses the second piece, its complement is already a neighborhood.
                have hA₁_nhds :
                    (((Y ⊓ Z₁ : Closeds X) : Set X) ↓∩ E) ∈
                      𝓝 (⟨x, show x ∈ (Y ⊓ Z₁ : Closeds X) by exact ⟨hxY, hxZ₁⟩⟩ :
                        (Y ⊓ Z₁ : Closeds X)) :=
                  ih (Y ⊓ Z₁) (inf_lt_left.2 hZ₁_proper) ⟨hxY, hxZ₁⟩
                obtain ⟨V₁, hxV₁, hV₁_subset⟩ :=
                  trace_mem_nhds_parent_of_trace_mem_nhds_closed (E := E) inf_le_left
                    ⟨hxY, hxZ₁⟩ hA₁_nhds
                let W₂ : Opens Y :=
                  ⟨(((Y : Set X) ↓∩ ((Y ⊓ Z₂ : Closeds X) : Set X))ᶜ),
                    by
                      simpa using
                        ((Y ⊓ Z₂ : Closeds X).2.isOpen_compl.preimage continuous_subtype_val)⟩
                have hxW₂ : (⟨x, hxY⟩ : Y) ∈ W₂ := by
                  simp [W₂, Set.mem_preimage, Set.mem_inter_iff, hxY, hxZ₂]
                have hInterSubset :
                    (V₁ : Set Y) ∩ (W₂ : Set Y) ⊆ ((Y : Set X) ↓∩ E) := by
                  intro y hy
                  have hyCover : y.1 ∈ (Z₁ : Set X) ∪ (Z₂ : Set X) := hY_subset y.2
                  rcases hy with ⟨hyV₁, hyW₂⟩
                  rcases hyCover with hyZ₁ | hyZ₂
                  · have hyA₁ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₁ : Closeds X) : Set X)) := by
                      simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₁]
                    exact hV₁_subset ⟨hyV₁, hyA₁⟩
                  · have hyA₂ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₂ : Closeds X) : Set X)) := by
                      simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₂]
                    exact False.elim (hyW₂ hyA₂)
                exact mem_nhds_iff.2 ⟨(V₁ : Set Y) ∩ (W₂ : Set Y), hInterSubset, V₁.2.inter W₂.2,
                  ⟨hxV₁, hxW₂⟩⟩
            · -- The cover forces `x` into the second piece, so the previous argument is symmetric.
              have hxZ₂ : x ∈ Z₂ := by
                have hxCover : x ∈ (Z₁ : Set X) ∪ (Z₂ : Set X) := hY_subset hxY
                rcases hxCover with hxZ₁' | hxZ₂
                · exact False.elim (hxZ₁ hxZ₁')
                · exact hxZ₂
              have hA₂_nhds :
                  (((Y ⊓ Z₂ : Closeds X) : Set X) ↓∩ E) ∈
                    𝓝 (⟨x, show x ∈ (Y ⊓ Z₂ : Closeds X) by exact ⟨hxY, hxZ₂⟩⟩ :
                      (Y ⊓ Z₂ : Closeds X)) :=
                ih (Y ⊓ Z₂) (inf_lt_left.2 hZ₂_proper) ⟨hxY, hxZ₂⟩
              obtain ⟨V₂, hxV₂, hV₂_subset⟩ :=
                trace_mem_nhds_parent_of_trace_mem_nhds_closed (E := E) inf_le_left
                  ⟨hxY, hxZ₂⟩ hA₂_nhds
              let W₁ : Opens Y :=
                ⟨(((Y : Set X) ↓∩ ((Y ⊓ Z₁ : Closeds X) : Set X))ᶜ),
                  by
                    simpa using
                      ((Y ⊓ Z₁ : Closeds X).2.isOpen_compl.preimage continuous_subtype_val)⟩
              have hxW₁ : (⟨x, hxY⟩ : Y) ∈ W₁ := by
                simp [W₁, Set.mem_preimage, Set.mem_inter_iff, hxY, hxZ₁]
              have hInterSubset :
                  (W₁ : Set Y) ∩ (V₂ : Set Y) ⊆ ((Y : Set X) ↓∩ E) := by
                intro y hy
                have hyCover : y.1 ∈ (Z₁ : Set X) ∪ (Z₂ : Set X) := hY_subset y.2
                rcases hy with ⟨hyW₁, hyV₂⟩
                rcases hyCover with hyZ₁ | hyZ₂
                · have hyA₁ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₁ : Closeds X) : Set X)) := by
                    simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₁]
                  exact False.elim (hyW₁ hyA₁)
                · have hyA₂ : y ∈ ((Y : Set X) ↓∩ ((Y ⊓ Z₂ : Closeds X) : Set X)) := by
                    simp [Set.mem_preimage, Set.mem_inter_iff, hyZ₂]
                  exact hV₂_subset ⟨hyV₂, hyA₂⟩
              exact mem_nhds_iff.2 ⟨(W₁ : Set Y) ∩ (V₂ : Set Y), hInterSubset, W₁.2.inter V₂.2,
                ⟨hxW₁, hxV₂⟩⟩
    -- Apply the closed-subspace induction to the universal closed subset and unwrap the subtype.
    have hTopNhds :
        ((((⊤ : Closeds X) : Set X) ↓∩ E) : Set (⊤ : Closeds X)) ∈
          𝓝 (⟨x, show x ∈ (⊤ : Closeds X) by trivial⟩ : (⊤ : Closeds X)) :=
      hTraceNhds ⊤ (by trivial)
    have hWithin : E ∈ 𝓝[(Set.univ : Set X)] x := by
      simpa using (preimage_coe_mem_nhds_subtype.1 hTopNhds)
    simpa using hWithin

end

end Topology

/-! ### Lemma_5_16_5 (from Chap05) -/
universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

section

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

/-
Domain-style sampling for openness detected on irreducible closed traces:
- primary domain: open and constructible subsets of Noetherian spaces, tested on irreducible closed
  subspaces;
- sampled owner declarations:
  `IsOpen`,
  `Topology.IsConstructible`,
  `isConstructible_iff_forall_irreducibleCloseds_containsNonemptyOpen_or_not_dense`,
  `Topology.IsConstructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace`,
  `TopologicalSpace.IrreducibleCloseds`;
- best owner abstraction: the numbered item stays source-facing on `IsOpen E`, while using
  `IsConstructible` and `IrreducibleCloseds` as the canonical owner and bridge layers;
- primitive vs. derived split: the primitive datum is only `IsOpen E`; constructibility and the
  pointwise dense-trace criterion are derived API supplied by Lemmas `5.16.3` and `5.16.4`, so
  this file should reuse those owners instead of introducing a parallel trace wrapper.

Layer triage:
- `source-facing`: the Stacks criterion for openness via irreducible closed traces;
- `core/canonical`: `IsOpen`, `Topology.IsConstructible`, and `TopologicalSpace.IrreducibleCloseds`;
- `bridge/view`: the canonical subtype trace notation `↓∩` together with the two previous chapter
  criteria on constructibility and neighborhoods.
-/

-- Proof sketch: if `E` is open, then its trace on any irreducible closed subset is itself an open
-- subset of that subspace, so the trace is either empty or already provides the required witness.
-- Conversely, reinterpret the empty case as non-density and apply Lemma `5.16.3` to recover that
-- `E` is constructible; then for each `x ∈ E`, every irreducible closed subset through `x` has
-- nonempty trace, hence contains a nonempty open subtrace, which is dense by irreducibility. Lemma
-- `5.16.4` upgrades those dense traces to `E ∈ 𝓝 x`, and therefore `E` is open.
/-- Lemma 5.16.5: a subset `E` of a Noetherian space `X` is open if and only if for every
irreducible closed subset `Y` of `X`, the intersection `E ∩ Y` is empty or contains a nonempty
open subset of `Y`, written as `Y ∩ U` for some open subset `U` of `X`. -/
theorem isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open (E : Set X) :
    IsOpen E ↔
      ∀ Y : IrreducibleCloseds X,
        ((Y : Set X) ↓∩ E) = ∅ ∨
          ∃ U : Opens Y, (U : Set Y).Nonempty ∧ (U : Set Y) ⊆ (Y : Set X) ↓∩ E := by
  constructor
  · intro hE Y
    by_cases hYE : ((Y : Set X) ↓∩ E : Set Y) = ∅
    · exact Or.inl hYE
    · refine Or.inr ⟨⟨(Y : Set X) ↓∩ E, ?_⟩, Set.nonempty_iff_ne_empty.mpr hYE, subset_rfl⟩
      simpa using hE.preimage continuous_subtype_val
  · intro hE
    have hE_constructible : IsConstructible E :=
      (isConstructible_iff_forall_irreducibleCloseds_containsNonemptyOpen_or_not_dense E).2
        fun Y ↦
          match hE Y with
          | .inl hYE =>
              .inr <| by
                letI : Nonempty Y := by
                  rcases Y.isIrreducible.nonempty with ⟨y, hy⟩
                  exact ⟨⟨y, hy⟩⟩
                rw [hYE, dense_iff_closure_eq, closure_empty]
                exact Set.empty_ne_univ
          | .inr hU => .inl hU
    refine isOpen_iff_mem_nhds.2 fun x hxE ↦ ?_
    refine (hE_constructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace).2 ?_
    intro Y hxY
    rcases hE Y with hYE | ⟨U, hU_nonempty, hU_subset⟩
    · exfalso
      exact (Set.nonempty_iff_ne_empty.mp ⟨⟨x, hxY⟩, hxE⟩) hYE
    · letI : IrreducibleSpace Y := Subtype.irreducibleSpace Y.isIrreducible
      exact Dense.mono hU_subset (U.2.dense hU_nonempty)

end
