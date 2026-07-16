import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_84_1
import stacks_proof.stacks_project.Chap10.Definition_10_88_7
import stacks_proof.stacks_project.Chap10.Example_10_91_1
import stacks_proof.stacks_project.Chap10.Lemma_10_92_2
import stacks_proof.stacks_project.Chap10.Lemma_10_153_4
import stacks_proof.stacks_project.Chap10.Theorem_10_84_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Module

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Domain-style sampling:
- primary domain: Chapter 10 owner predicates for Mittag-Leffler modules and internal direct-sum
  decompositions of modules;
- sampled declarations of the same kind:
  `Module.IsDirectSumOfCountablyGenerated` from `Definition_10_84_1`,
  `Module.MittagLeffler` from `Definition_10_88_7`,
  `DirectSum.IsInternal.submodule_iSupIndep`,
  `DirectSum.IsInternal.submodule_iSup_eq_top`,
  and mathlib's canonical bridge
  `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`;
- best owner abstraction: the DecidableEq-free existence of a family of submodules with
  `iSupIndep`, supremum `⊤`, and finitely presented summands; `DirectSum.IsInternal` is only a
  bridge/view because its use on a family indexed by `ι` requires a proof-only `[DecidableEq ι]`;
- primitive data: an index type, a family of submodules, independence of that family, total
  supremum, and finite presentation of each summand;
- derived API: the companion bridge theorem below converting to and from `DirectSum.IsInternal`;
- layer: `IsDirectSumOfFinitePresentation` is `source-facing`, while the internal-direct-sum
  criterion is a `bridge/view`.
-/

variable (R M)

/-- An `R`-module is a direct sum of finitely presented submodules. -/
def IsDirectSumOfFinitePresentation : Prop :=
  ∃ (ι : Type w) (A : ι → Submodule R M),
    iSupIndep A ∧ iSup A = (⊤ : Submodule R M) ∧ ∀ i, Module.FinitePresentation R (A i)

-- Proof sketch: use the canonical mathlib criterion
-- `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top` to translate between the public
-- DecidableEq-free owner and the internal-direct-sum view.
/-- `Module.IsDirectSumOfFinitePresentation` is equivalent to the existence of an internal
direct-sum decomposition by finitely presented submodules. This companion theorem keeps
`DirectSum.IsInternal` as a bridge view, not as the owner predicate, because it requires a
proof-only `DecidableEq` witness on the index type. -/
theorem isDirectSumOfFinitePresentation_iff_exists_internal :
    IsDirectSumOfFinitePresentation.{u, v, w} R M ↔
      ∃ (ι : Type w) (_ : DecidableEq ι) (A : ι → Submodule R M),
        DirectSum.IsInternal A ∧ ∀ i, Module.FinitePresentation R (A i) := by
  constructor
  · rintro ⟨ι, A, hindep, htop, hfp⟩
    classical
    refine ⟨ι, inferInstance, A, ?_, hfp⟩
    exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hindep, htop⟩
  · rintro ⟨ι, _, A, hA, hfp⟩
    rcases (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp hA with
      ⟨hindep, htop⟩
    exact ⟨ι, A, hindep, htop, hfp⟩

/-- Helper for Chap10 Lemma 10 153 13: after splitting off any finitely presented direct summand,
every element of the complementary summand lies in a finitely presented direct summand of that
complement. -/
def HasFinitePresentationComplementSummandProperty : Prop :=
  ∀ ⦃N N' : Submodule R M⦄, IsCompl N N' → Module.FinitePresentation R N' →
    ∀ x : N, ∃ F F' : Submodule R N,
      x ∈ F ∧ Module.FinitePresentation R F ∧ IsCompl F F'

/-- Helper for Chap10 Lemma 10 153 13: a countably generated module admits a generating sequence
indexed by `ℕ`. -/
lemma exists_countable_generator_sequence (hcg : CountablyGenerated R M) :
    ∃ x : ℕ → M, Submodule.span R (Set.range x) = ⊤ := by
  rcases (Module.countablyGenerated_iff (R := R) (M := M)).mp hcg with ⟨s, hs, hspan⟩
  rcases Set.countable_iff_exists_subset_range.mp hs with ⟨x, hsx⟩
  -- Enlarging a countable spanning set to the range of a sequence preserves the top span.
  refine ⟨x, top_le_iff.mp ?_⟩
  rw [← hspan]
  exact Submodule.span_mono hsx

/-- Helper for Chap10 Lemma 10 153 13: splitting the current complement refines the ambient
direct-sum decomposition by adjoining the new piece to the old stage. -/
lemma isCompl_sup_of_split_inside_complement_presented
    {K C A C' : Submodule R M} (hKC : IsCompl K C) (hAC' : Disjoint A C')
    (hC : A ⊔ C' = C) :
    IsCompl (K ⊔ A) C' := by
  -- Rewriting the old complement as `A ⊔ C'` lets modularity upgrade the complement relation.
  rw [← hC] at hKC
  exact hAC'.isCompl_sup_left_of_isCompl_sup_right hKC

/-- Helper for Chap10 Lemma 10 153 13: if `A` sits inside a complement `C`, is disjoint from
`C' ≤ C`, and `K` is complementary to `C`, then `A` is disjoint from `K ⊔ C'`. -/
lemma disjoint_piece_sup_of_isCompl_presented
    {K C A C' : Submodule R M} (hKC : IsCompl C K) (hAle : A ≤ C)
    (hAC' : Disjoint A C') (hC'le : C' ≤ C) :
    Disjoint A (K ⊔ C') := by
  rw [disjoint_iff]
  apply le_bot_iff.mp
  intro x hx
  rcases Submodule.mem_inf.1 hx with ⟨hxA, hxKC'⟩
  rcases Submodule.mem_sup.1 hxKC' with ⟨k, hkK, c', hc'C', hEq⟩
  have hxC : x ∈ C := hAle hxA
  have hc'C : c' ∈ C := hC'le hc'C'
  have hkC : k ∈ C := by
    have hx_sum : k + c' ∈ C := hEq ▸ hxC
    exact (Submodule.add_mem_iff_left C hc'C).1 hx_sum
  have hkZero : k = 0 := by
    have hkInf : k ∈ C ⊓ K := Submodule.mem_inf.2 ⟨hkC, hkK⟩
    have hkBot : k ∈ (⊥ : Submodule R M) := by
      simpa [hKC.disjoint.eq_bot] using hkInf
    simpa using hkBot
  have hxC' : x ∈ C' := by
    rw [← hEq, hkZero, zero_add]
    exact hc'C'
  have hxBot : x ∈ (A ⊓ C') := Submodule.mem_inf.2 ⟨hxA, hxC'⟩
  have : x ∈ (⊥ : Submodule R M) := by
    simpa [hAC'.eq_bot] using hxBot
  simpa using this

/-- Helper for Chap10 Lemma 10 153 13: each recursive stage is the finite supremum of the pieces
chosen so far. -/
lemma finitePresentationStage_eq_iSup_pieces
    {K A : ℕ → Submodule R M} (hK0 : K 0 = ⊥)
    (hstep : ∀ n, K (n + 1) = K n ⊔ A n) :
    ∀ n, K n = ⨆ i ∈ Finset.range n, A i := by
  have hfinset : ∀ n, K n = (Finset.range n).sup A := by
    intro n
    induction n with
    | zero =>
        simpa using hK0
    | succ n ih =>
        calc
          K (n + 1) = K n ⊔ A n := hstep n
          _ = (Finset.range n).sup A ⊔ A n := by rw [ih]
          _ = (Finset.range (n + 1)).sup A := by
            simp [Finset.range_add_one, Finset.sup_insert, sup_comm]
  intro n
  simpa [Finset.sup_eq_iSup] using hfinset n

/-- Helper for Chap10 Lemma 10 153 13: a disjoint supremum of two finitely presented submodules
is finitely presented. -/
lemma finitePresentation_sup_of_disjoint
    {K A : Submodule R M} (hKA : Disjoint K A)
    (hKfp : Module.FinitePresentation R K) (hAfp : Module.FinitePresentation R A) :
    Module.FinitePresentation R ↥(K ⊔ A) := by
  letI : Module.FinitePresentation R K := hKfp
  letI : Module.FinitePresentation R A := hAfp
  let f : K × A →ₗ[R] ↥(K ⊔ A) :=
    LinearMap.codRestrict (K ⊔ A) (K.subtype.coprod A.subtype) fun z ↦ by
      rcases z with ⟨k, a⟩
      exact Submodule.mem_sup.2 ⟨k, k.2, a, a.2, rfl⟩
  have hcoprod_inj : Function.Injective (K.subtype.coprod A.subtype) := by
    -- Disjointness identifies the kernel of the sum map from `K × A` with zero.
    rw [← LinearMap.ker_eq_bot]
    rw [LinearMap.ker_coprod_of_disjoint_range, Submodule.ker_subtype, Submodule.ker_subtype,
      Submodule.prod_bot]
    simpa [Submodule.range_subtype] using hKA
  have hf_inj : Function.Injective f := by
    intro z₁ z₂ hz
    apply hcoprod_inj
    exact Subtype.ext_iff.mp hz
  have hf_surj : Function.Surjective f := by
    intro y
    rcases Submodule.mem_sup.1 y.2 with ⟨k, hk, a, ha, hka⟩
    refine ⟨⟨⟨k, hk⟩, ⟨a, ha⟩⟩, ?_⟩
    apply Subtype.ext
    simpa [f, hka]
  letI : Module.FinitePresentation R (K × A) := inferInstance
  let e : (K × A) ≃ₗ[R] ↥(K ⊔ A) := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  -- Transport finite presentation across the explicit product-to-supremum equivalence.
  exact Module.FinitePresentation.of_equiv e

/-- Helper for Chap10 Lemma 10 153 13: inside a complement to a finitely presented summand, a
chosen element lies in a finitely presented direct summand of the complement, viewed back inside
the ambient module. -/
lemma exists_finitePresentation_piece_of_mem_complement
    (hM : HasFinitePresentationComplementSummandProperty R M)
    {K C : Submodule R M} (hCK : IsCompl C K)
    (hKfp : Module.FinitePresentation R K) (x : C) :
    ∃ A C' : Submodule R M,
      (x : M) ∈ A ∧
      A ≤ C ∧
      Disjoint A C' ∧
      A ⊔ C' = C ∧
      Module.FinitePresentation R A := by
  obtain ⟨F, F', hxF, hFfp, hFF'⟩ := hM hCK hKfp x
  let A : Submodule R M := F.map C.subtype
  let C' : Submodule R M := F'.map C.subtype
  have hxA : (x : M) ∈ A := by
    exact ⟨x, hxF, rfl⟩
  have hAle : A ≤ C := C.map_subtype_le F
  have hAC' : Disjoint A C' := by
    -- The split inside `C` remains split after applying the inclusion `C → M`.
    exact Submodule.disjoint_map (Submodule.subtype_injective C) hFF'.disjoint
  have hsup : A ⊔ C' = C := by
    -- Mapping the internal split of the complement into `M` recovers the whole complement.
    rw [← Submodule.map_sup, hFF'.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
  have hAfp : Module.FinitePresentation R A := by
    exact Module.FinitePresentation.of_equiv (C.equivSubtypeMap F)
  exact ⟨A, C', hxA, hAle, hAC', hsup, hAfp⟩

/-- Helper for Chap10 Lemma 10 153 13: a stage consists of a finitely presented direct summand
together with its complementary submodule. -/
structure FinitePresentationStage where
  K : Submodule R M
  C : Submodule R M
  isCompl : IsCompl C K
  finitePresentation_K : Module.FinitePresentation R K

/-- Helper for Chap10 Lemma 10 153 13: a successor step splits a finitely presented piece from the
current complement and enlarges the finitely presented stage. -/
structure FinitePresentationStep (x : M) (S : FinitePresentationStage (R := R) (M := M)) where
  A : Submodule R M
  next : FinitePresentationStage (R := R) (M := M)
  piece_le : A ≤ S.C
  piece_disjoint_next : Disjoint A next.C
  piece_sup_next : A ⊔ next.C = S.C
  finitePresentation_A : Module.FinitePresentation R A
  next_stage_eq : next.K = S.K ⊔ A
  mem_next : x ∈ next.K

/-- Helper for Chap10 Lemma 10 153 13: from one stage and one ambient element, split off the next
finitely presented piece. -/
lemma exists_finitePresentation_step
    (hM : HasFinitePresentationComplementSummandProperty R M)
    (x : M) (S : FinitePresentationStage (R := R) (M := M)) :
    Nonempty (FinitePresentationStep (R := R) (M := M) x S) := by
  let e := Submodule.prodEquivOfIsCompl S.C S.K S.isCompl
  let xC : S.C := (e.symm x).1
  have hx_decomp' : e (e.symm x) = x := e.apply_symm_apply x
  have hx_decomp : (xC : M) + (((e.symm x).2 : S.K) : M) = x := by
    -- Project `x` to the current complement and old stage.
    simpa [e, xC] using hx_decomp'
  obtain ⟨A, C', hxA, hAle, hAC', hsup, hAfp⟩ :=
    exists_finitePresentation_piece_of_mem_complement (R := R) (M := M) hM S.isCompl
      S.finitePresentation_K xC
  have hKA : Disjoint S.K A := by
    -- The new piece lies in the current complement, hence is disjoint from the old stage.
    exact (S.isCompl.disjoint.mono_left hAle).symm
  have hnextFp : Module.FinitePresentation R ↥(S.K ⊔ A) :=
    finitePresentation_sup_of_disjoint (R := R) (M := M) hKA S.finitePresentation_K hAfp
  have hnextCompl : IsCompl C' (S.K ⊔ A) := by
    -- Refining the complement produces the next stage/complement pair.
    exact
      (isCompl_sup_of_split_inside_complement_presented (R := R) (M := M) S.isCompl.symm hAC'
        hsup).symm
  let nextStage : FinitePresentationStage (R := R) (M := M) :=
    ⟨S.K ⊔ A, C', hnextCompl, hnextFp⟩
  have hx_next : x ∈ nextStage.K := by
    -- Reinsert the projected complement component into the enlarged stage.
    rw [Submodule.mem_sup]
    refine ⟨((e.symm x).2 : S.K), (e.symm x).2.2, (xC : M), hxA, ?_⟩
    simpa [nextStage, add_comm] using hx_decomp
  refine ⟨⟨A, nextStage, hAle, ?_, ?_, hAfp, rfl, hx_next⟩⟩
  · simpa [nextStage] using hAC'
  · simpa [nextStage] using hsup

/-- Helper for Chap10 Lemma 10 153 13: recursively choose finitely presented stages, complements,
and pieces attached to a generating sequence. -/
lemma exists_finitePresentation_stage_chain
    (hM : HasFinitePresentationComplementSummandProperty R M) (x : ℕ → M) :
    ∃ K C A : ℕ → Submodule R M,
      K 0 = ⊥ ∧
      C 0 = ⊤ ∧
      (∀ n, IsCompl (C n) (K n)) ∧
      (∀ n, Module.FinitePresentation R (K n)) ∧
      (∀ n, A n ≤ C n) ∧
      (∀ n, Disjoint (A n) (C (n + 1))) ∧
      (∀ n, A n ⊔ C (n + 1) = C n) ∧
      (∀ n, Module.FinitePresentation R (A n)) ∧
      (∀ n, K (n + 1) = K n ⊔ A n) ∧
      (∀ n, x n ∈ K (n + 1)) := by
  classical
  let base : FinitePresentationStage (R := R) (M := M) :=
    ⟨⊥, ⊤, isCompl_top_bot, inferInstance⟩
  let chooseStep :
      ∀ n, (S : FinitePresentationStage (R := R) (M := M)) →
        FinitePresentationStep (R := R) (M := M) (x n) S := fun n S ↦
        Classical.choice (exists_finitePresentation_step (R := R) (M := M) hM (x n) S)
  let stage : ℕ → FinitePresentationStage (R := R) (M := M) :=
    Nat.rec base fun n S ↦ (chooseStep n S).next
  let A' : ℕ → Submodule R M := fun n ↦ (chooseStep n (stage n)).A
  refine ⟨fun n ↦ (stage n).K, fun n ↦ (stage n).C, A', rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro n
    exact (stage n).isCompl
  · intro n
    exact (stage n).finitePresentation_K
  · intro n
    exact (chooseStep n (stage n)).piece_le
  · intro n
    simpa [A', stage, chooseStep] using (chooseStep n (stage n)).piece_disjoint_next
  · intro n
    simpa [A', stage, chooseStep] using (chooseStep n (stage n)).piece_sup_next
  · intro n
    exact (chooseStep n (stage n)).finitePresentation_A
  · intro n
    simpa [A', stage, chooseStep] using (chooseStep n (stage n)).next_stage_eq
  · intro n
    simpa [A', stage, chooseStep] using (chooseStep n (stage n)).mem_next

/-- Helper for Chap10 Lemma 10 153 13: the finite-presentation complement summand property turns
a countably generated module into a direct sum of finitely presented submodules. -/
lemma isDirectSumOfFinitePresentation_of_hasFinitePresentationComplementSummandProperty
    (hcg : CountablyGenerated R M)
    (hM : HasFinitePresentationComplementSummandProperty R M) :
    IsDirectSumOfFinitePresentation.{u, v, w} R M := by
  classical
  -- Extract the countable generating sequence and run the recursive splitting construction.
  obtain ⟨x, hxspan⟩ := exists_countable_generator_sequence (R := R) (M := M) hcg
  obtain ⟨K, C, A, hK0, _, hCompl, _, hAle, hADisj, hASup, hAfp, hKstep, hxstage⟩ :=
    exists_finitePresentation_stage_chain (R := R) (M := M) hM x
  have hstage : ∀ n, K n = ⨆ i ∈ Finset.range n, A i :=
    finitePresentationStage_eq_iSup_pieces (R := R) (M := M) hK0 hKstep
  have hC_le : ∀ {m n}, m ≤ n → C n ≤ C m := by
    intro m n hmn
    induction hmn with
    | refl =>
        exact le_rfl
    | @step n hmn ih =>
        have hsucc : C (n + 1) ≤ C n := by
          rw [← hASup n]
          exact le_sup_right
        exact hsucc.trans ih
  have hindep : iSupIndep A := by
    -- Independence follows by bounding earlier pieces in the old stage and later pieces in the
    -- next complement, exactly as in the finite-free construction.
    rw [iSupIndep_def]
    intro i
    have hAiOther :
        (⨆ j, ⨆ (_ : j ≠ i), A j) ≤ K i ⊔ C (i + 1) := by
      refine iSup_le fun j ↦ iSup_le fun hij ↦ ?_
      rcases lt_or_gt_of_ne hij with hji | hij'
      · have hAjKi : A j ≤ K i := by
          rw [hstage i]
          exact le_iSup_of_le j <| le_iSup_of_le (by simpa using hji) le_rfl
        exact hAjKi.trans le_sup_left
      · have hAjCsucc : A j ≤ C (i + 1) := (hAle j).trans <| hC_le (Nat.succ_le_of_lt hij')
        exact hAjCsucc.trans le_sup_right
    have hAiBound : Disjoint (A i) (K i ⊔ C (i + 1)) := by
      exact disjoint_piece_sup_of_isCompl_presented (R := R) (M := M) (hCompl i) (hAle i)
        (hADisj i) ((by
          rw [← hASup i]
          exact le_sup_right) : C (i + 1) ≤ C i)
    exact hAiBound.mono_right hAiOther
  have hstage_le : ∀ n, K n ≤ ⨆ m, A m := by
    intro n
    rw [hstage n]
    exact iSup_le fun i ↦ iSup_le fun _ ↦ le_iSup A i
  have hxmem : ∀ n, x n ∈ ⨆ m, A m := by
    intro n
    exact hstage_le (n + 1) (hxstage n)
  have htop : iSup A = ⊤ := by
    -- Since every generator lies in the supremum of the pieces, their supremum is all of `M`.
    apply top_le_iff.mp
    rw [← hxspan]
    exact Submodule.span_le.2 fun y hy ↦ by
      rcases hy with ⟨n, rfl⟩
      exact hxmem n
  let B : ULift.{w} ℕ → Submodule R M := fun i ↦ A i.down
  have hindepB : iSupIndep B := by
    -- Reindex by `ULift` so the decomposition lives in the universe required by the owner
    -- predicate.
    exact hindep.comp (f := fun i : ULift.{w} ℕ ↦ i.down) ULift.down_bijective.1
  have htopB : iSup B = ⊤ := by
    calc
      iSup B = iSup A := by
        exact ULift.down_surjective.iSup_comp A
      _ = ⊤ := htop
  have hfpB : ∀ i, Module.FinitePresentation R (B i) := by
    intro i
    exact hAfp i.down
  exact ⟨ULift.{w} ℕ, B, hindepB, htopB, hfpB⟩

end

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Chap10 Lemma 10 153 13: a complemented submodule of a countably generated module
is countably generated. -/
lemma countablyGenerated_of_isCompl_left
    {N N' : Submodule R M} (hNN' : IsCompl N N') (hcg : CountablyGenerated R M) :
    CountablyGenerated R N := by
  let p : M →ₗ[R] N := Submodule.linearProjOfIsCompl N N' hNN'
  have hp_surj : Function.Surjective p := by
    intro x
    refine ⟨x, ?_⟩
    -- Projecting a point already in the left summand leaves it unchanged.
    simpa [p] using Submodule.linearProjOfIsCompl_apply_left N N' hNN' x
  -- Countable generation descends along the split projection.
  exact Module.countablyGenerated_of_surjective p hp_surj hcg

/-- Helper for Chap10 Lemma 10 153 13: a complemented submodule of a Mittag-Leffler module is
Mittag-Leffler. -/
lemma mittagLeffler_of_isCompl_left
    {N N' : Submodule R M} (hNN' : IsCompl N N') (hML : MittagLeffler R M) :
    MittagLeffler R N := by
  let p : M →ₗ[R] N := Submodule.linearProjOfIsCompl N N' hNN'
  have hp : p.comp N.subtype = LinearMap.id := by
    ext x
    -- The canonical projection is a retraction of the inclusion of the left summand.
    simpa [p] using Submodule.linearProjOfIsCompl_apply_left N N' hNN' x
  letI : MittagLeffler R M := hML
  -- Apply the already proved split-summand closure of the Mittag-Leffler property.
  exact Module.mittagLeffler_of_split N.subtype p hp

/-- Helper for Chap10 Lemma 10 153 13: Lemma 10.92.2 specialized to the cyclic map generated by
one vector. -/
lemma existsFactorizationFixingCyclicMap
    {N : Type v} [AddCommGroup N] [Module R N]
    (hcg : CountablyGenerated R N) (hML : MittagLeffler R N) (x : N) :
    ∃ (Q : ModuleCat.{v} R) (_ : Module.FinitePresentation R Q)
      (g : N →ₗ[R] Q) (h : Q →ₗ[R] N), h (g x) = x := by
  let f : R →ₗ[R] N := LinearMap.toSpanSingleton R N x
  obtain ⟨Q, hQ, g, h, hfix⟩ :=
    Module.exists_endomorphism_factorsThroughFinitePresentation_fixing_finite_map
      (R := R) (M := N) (P := R) hcg hML f
  refine ⟨Q, hQ, g, h, ?_⟩
  -- Evaluate the fixed cyclic map at `1` to recover the original vector.
  have hfix_one := congrArg (fun k : R →ₗ[R] N ↦ k 1) hfix
  simpa [f] using hfix_one

section HenselianProjector

/-- Helper for Chap10 Lemma 10 153 13: the range of an idempotent endomorphism of a finitely
presented module is finitely presented. -/
lemma finitePresentation_range_of_idempotent
    {Q : Type v} [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q]
    (b : Module.End R Q) (hb : IsIdempotentElem b) :
    Module.FinitePresentation R (LinearMap.range b) := by
  let g : Q →ₗ[R] LinearMap.ker b :=
    LinearMap.codRestrict (LinearMap.ker b) (LinearMap.id - b) fun x ↦ by
      have hb_x : b (b x) = b x := by
        simpa [IsIdempotentElem, Module.End.mul_eq_comp, LinearMap.comp_apply] using
          congrArg (fun f : Module.End R Q ↦ f x) hb
      -- The complementary projection `id - b` lands in the kernel of `b`.
      simp [LinearMap.mem_ker, hb_x]
  let l : LinearMap.ker b →ₗ[R] Q := (LinearMap.ker b).subtype
  have hl : g.comp l = LinearMap.id := by
    ext z
    -- On the kernel of `b`, the complementary projection is the identity.
    simp [g, l, LinearMap.mem_ker.mp z.2]
  have hf : Function.Injective (LinearMap.range b).subtype :=
    Submodule.injective_subtype _
  have hExact : Function.Exact (LinearMap.range b).subtype g := by
    -- The kernel of `id - b` is the range of an idempotent, giving a split exact sequence.
    rw [LinearMap.exact_iff, LinearMap.ker_codRestrict,
      ← LinearMap.IsIdempotentElem.range_eq_ker hb, Submodule.range_subtype]
  exact Module.finitePresentation_of_split_exact (LinearMap.range b).subtype g l hl hf hExact

variable [HenselianLocalRing R]

/-- Helper for Chap10 Lemma 10 153 13: in a product of local rings, an element fixing a vector has
an inner inverse that fixes the same vector. -/
lemma piLocal_exists_innerInverse_smul_fixed
    {ι : Type u} {A : ι → Type v} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    {P : Type w} [AddCommGroup P] [Module ((i : ι) → A i) P]
    (t : (i : ι) → A i) {q : P} (hq : t • q = q) :
    ∃ c : (i : ι) → A i, c * t * c = c ∧ c • q = q := by
  classical
  let c : (i : ι) → A i := fun i ↦ if h : IsUnit (t i) then ↑h.unit⁻¹ else 0
  let u : (i : ι) → A i := fun i ↦
    if h : IsUnit (t i) then -↑h.unit⁻¹
    else ↑((IsLocalRing.isUnit_or_isUnit_one_sub_self (t i)).resolve_left h).unit⁻¹
  have hctc : c * t * c = c := by
    funext i
    by_cases h : IsUnit (t i)
    · -- On a unit coordinate, choose the inverse; then `c * t * c = c`.
      dsimp [c]
      simp only [dif_pos h]
      rw [h.val_inv_mul]
      simp
    · -- On a nonunit coordinate, choose zero, which satisfies the inner-inverse equation.
      dsimp [c]
      simp only [dif_neg h]
      simp
  have hcsub : c - 1 = u * (t - 1) := by
    funext i
    by_cases h : IsUnit (t i)
    · -- If `t_i` is a unit, `c_i - 1` is a multiple of `t_i - 1`.
      dsimp [c, u]
      simp only [dif_pos h]
      have hv : (↑h.unit⁻¹ : A i) * t i = 1 := h.val_inv_mul
      calc
        ↑h.unit⁻¹ - 1 = ↑h.unit⁻¹ - ↑h.unit⁻¹ * t i := by rw [hv]
        _ = -↑h.unit⁻¹ * (t i - 1) := by ring
    · -- If `t_i` is not a unit, localness makes `1 - t_i` a unit and gives the same divisibility.
      have h1 : IsUnit (1 - t i) :=
        (IsLocalRing.isUnit_or_isUnit_one_sub_self (t i)).resolve_left h
      dsimp [c, u]
      simp only [dif_neg h]
      have hv : (↑h1.unit⁻¹ : A i) * (1 - t i) = 1 := h1.val_inv_mul
      calc
        (0 : A i) - 1 = -1 := by ring
        _ = - (↑h1.unit⁻¹ * (1 - t i)) := by rw [hv]
        _ = ↑h1.unit⁻¹ * (t i - 1) := by ring
  have ht_sub : (t - 1) • q = 0 := by
    -- The fixed-vector equation is exactly annihilation by `t - 1`.
    rw [sub_smul, hq, one_smul, sub_self]
  have hc_sub_smul : (c - 1) • q = 0 := by
    -- Since `c - 1` is a multiple of `t - 1`, it also annihilates `q`.
    rw [hcsub, mul_smul, ht_sub, smul_zero]
  have hcq_sub : c • q - q = 0 := by
    simpa [sub_smul, one_smul] using hc_sub_smul
  refine ⟨c, hctc, ?_⟩
  exact sub_eq_zero.mp hcq_sub

/-- Helper for Chap10 Lemma 10 153 13: over a henselian local base, the product decomposition of a
finite algebra turns the product-local construction into an inner inverse in the algebra. -/
lemma finiteAlgebra_exists_innerInverse_smul_fixed
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]
    {P : Type w} [AddCommGroup P] [Module S P]
    (t : S) {q : P} (hq : t • q = q) :
    ∃ c : S, c * t * c = c ∧ c • q = q := by
  classical
  obtain ⟨ι, instFintype, A, instAComm, instAAlg, instAHenselian, instAFinite, ⟨e⟩⟩ :=
    exists_pi_algEquiv_henselianLocalRing_of_finite (R := R) (S := S)
  letI : Fintype ι := instFintype
  letI : ∀ i, CommRing (A i) := instAComm
  letI : ∀ i, Algebra R (A i) := instAAlg
  letI : ∀ i, HenselianLocalRing (A i) := instAHenselian
  letI : ∀ i, Module.Finite R (A i) := instAFinite
  letI : Module ((i : ι) → A i) P := Module.compHom P e.symm.toRingHom
  have hqprod : e t • q = q := by
    -- Transport the fixed-vector equation across the algebra equivalence.
    change e.symm (e t) • q = q
    simpa using hq
  obtain ⟨c', hc'tc', hc'q⟩ :=
    piLocal_exists_innerInverse_smul_fixed (t := e t) (q := q) hqprod
  refine ⟨e.symm c', ?_, ?_⟩
  · -- Ring equations are checked after applying the algebra equivalence.
    apply e.injective
    simpa using hc'tc'
  · -- The transported product action is the original `S`-action.
    change e.symm c' • q = q
    simpa using hc'q

/-- Helper for Chap10 Lemma 10 153 13: a finite-presentation endomorphism fixing a vector admits
an inner inverse, obtained from the finite algebra generated by the endomorphism. -/
lemma existsInnerInverseOnFinitePresentationFactor_fixedVector
    {Q : Type v} [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q]
    (a : Module.End R Q) {q : Q} (hq : a q = q) :
    ∃ c : Module.End R Q, c.comp (a.comp c) = c ∧ c q = q := by
  classical
  letI : Module.Finite R Q := inferInstance
  obtain ⟨P, hPmonic, hPaeval⟩ := LinearMap.exists_monic_and_aeval_eq_zero R a
  let I : Ideal (Polynomial R) := Ideal.span ({P} : Set (Polynomial R))
  have hI : ∀ f ∈ I, (Polynomial.aeval a) f = 0 := by
    intro f hf
    rcases (Ideal.mem_span_singleton'.mp hf) with ⟨g, rfl⟩
    -- The quotient relation is killed because `P` annihilates the endomorphism `a`.
    rw [map_mul, hPaeval, mul_zero]
  let ρ : AdjoinRoot P →ₐ[R] Module.End R Q :=
    Ideal.Quotient.liftₐ I (Polynomial.aeval a) hI
  have hroot : ρ (AdjoinRoot.root P) = a := by
    -- The distinguished root acts as the original endomorphism.
    rw [AdjoinRoot.root, AdjoinRoot.mk]
    change ρ ((Ideal.Quotient.mk I) Polynomial.X) = a
    dsimp [ρ]
    calc
      (Ideal.Quotient.liftₐ I (Polynomial.aeval a) hI)
          ((Ideal.Quotient.mk I) Polynomial.X)
          = (Ideal.Quotient.lift I (Polynomial.aeval a).toRingHom hI)
              ((Ideal.Quotient.mk I) Polynomial.X) := by
              exact Ideal.Quotient.liftₐ_apply I (Polynomial.aeval a) hI
                ((Ideal.Quotient.mk I) Polynomial.X)
      _ = (Polynomial.aeval a) Polynomial.X :=
        Ideal.Quotient.lift_mk I (Polynomial.aeval a).toRingHom hI
      _ = a := Polynomial.aeval_X a
  letI : Module.Finite R (AdjoinRoot P) := hPmonic.finite_adjoinRoot
  letI : Module (AdjoinRoot P) Q := Module.compHom Q ρ.toRingHom
  have hqroot : (AdjoinRoot.root P) • q = q := by
    -- The fixed-vector equation becomes a fixed-vector equation for the root action.
    change ρ (AdjoinRoot.root P) q = q
    simpa [hroot] using hq
  obtain ⟨c, hctc, hcq⟩ :=
    finiteAlgebra_exists_innerInverse_smul_fixed (R := R) (S := AdjoinRoot P)
      (P := Q) (AdjoinRoot.root P) (q := q) hqroot
  refine ⟨ρ c, ?_, ?_⟩
  · -- Mapping `c * root * c = c` to endomorphisms gives `ρ c ∘ a ∘ ρ c = ρ c`.
    change ρ c * (a * ρ c) = ρ c
    have hmap := congrArg ρ hctc
    simpa [map_mul, hroot, mul_assoc] using hmap
  · -- The chosen finite-algebra element fixes the vector after applying the representation.
    change ρ c q = q
    simpa using hcq

end HenselianProjector

/-- Helper for Chap10 Lemma 10 153 13: an inner inverse on a finite-presentation factor transports
through a factorization fixing one vector to a finitely presented direct summand. -/
lemma existsFinitePresentationDirectSummandOfInnerInverseFactorization
    {N : Type v} [AddCommGroup N] [Module R N]
    {Q : Type w} [AddCommGroup Q] [Module R Q] [Module.FinitePresentation R Q]
    (g : N →ₗ[R] Q) (h : Q →ₗ[R] N) (x : N) (hfix : h (g x) = x)
    (c : Module.End R Q) (hcfix : c (g x) = g x)
    (hcac : c.comp ((g.comp h).comp c) = c) :
    ∃ F F' : Submodule R N,
      x ∈ F ∧ Module.FinitePresentation R F ∧ IsCompl F F' := by
  let p : Module.End R N := h.comp (c.comp g)
  have hp : IsIdempotentElem p := by
    change p * p = p
    ext y
    have hcac_y : c ((g.comp h) (c (g y))) = c (g y) := by
      simpa [LinearMap.comp_apply] using congrArg (fun f : Q →ₗ[R] Q ↦ f (g y)) hcac
    -- The inner-inverse relation makes the transported endomorphism idempotent.
    calc
      p (p y) = h (c ((g.comp h) (c (g y)))) := rfl
      _ = h (c (g y)) := by rw [hcac_y]
      _ = p y := rfl
  have hpx : p x = x := by
    -- The transported idempotent fixes the original vector because `c` fixes its image in `Q`.
    calc
      p x = h (c (g x)) := rfl
      _ = h (g x) := by rw [hcfix]
      _ = x := hfix
  let d : Module.End R Q := c.comp (g.comp h)
  have hd : IsIdempotentElem d := by
    change d * d = d
    ext z
    have hcac_z : c ((g.comp h) (c ((g.comp h) z))) = c ((g.comp h) z) := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : Q →ₗ[R] Q ↦ f ((g.comp h) z)) hcac
    -- The finite factor idempotent is `c ∘ g ∘ h`.
    calc
      d (d z) = c ((g.comp h) (c ((g.comp h) z))) := rfl
      _ = c ((g.comp h) z) := by rw [hcac_z]
      _ = d z := rfl
  have hdfp : Module.FinitePresentation R (LinearMap.range d) :=
    finitePresentation_range_of_idempotent (R := R) d hd
  have hfp : Module.FinitePresentation R (LinearMap.range p) := by
    let f : LinearMap.range d →ₗ[R] LinearMap.range p :=
      LinearMap.codRestrict (LinearMap.range p) (h.comp (LinearMap.range d).subtype) fun z ↦ by
        have hzfix : d z = z := (LinearMap.IsIdempotentElem.mem_range_iff hd).mp z.2
        have hp_hz : p (h z) = h z := by
          calc
            p (h z) = h (c ((g.comp h) z)) := rfl
            _ = h (d z) := rfl
            _ = h z := by rw [hzfix]
        exact (LinearMap.IsIdempotentElem.mem_range_iff hp).mpr hp_hz
    let k : LinearMap.range p →ₗ[R] LinearMap.range d :=
      LinearMap.codRestrict (LinearMap.range d) (c.comp (g.comp (LinearMap.range p).subtype))
        fun y ↦ by
          have hd_cgy : d (c (g y)) = c (g y) := by
            have hcac_y : c ((g.comp h) (c (g y))) = c (g y) := by
              simpa [LinearMap.comp_apply] using congrArg (fun f : Q →ₗ[R] Q ↦ f (g y)) hcac
            exact hcac_y
          -- The inverse map lands in `range d` by the same inner-inverse relation.
          exact (LinearMap.IsIdempotentElem.mem_range_iff hd).mpr hd_cgy
    have hleft : Function.LeftInverse k f := by
      intro z
      apply Subtype.ext
      have hzfix : d z = z := (LinearMap.IsIdempotentElem.mem_range_iff hd).mp z.2
      -- The inverse check on `range d` is just its fixed-point criterion.
      calc
        c (g (h z)) = d z := rfl
        _ = z := hzfix
    have hright : Function.RightInverse k f := by
      intro y
      apply Subtype.ext
      have hyfix : p y = y := (LinearMap.IsIdempotentElem.mem_range_iff hp).mp y.2
      -- The two maps are inverse because points in `range p` are already fixed by `p`.
      calc
        h (c (g y)) = p y := rfl
        _ = y := hyfix
    let e : LinearMap.range d ≃ₗ[R] LinearMap.range p :=
      LinearEquiv.ofBijective f ⟨Function.LeftInverse.injective hleft,
        Function.RightInverse.surjective hright⟩
    -- Transfer finite presentation from the finite-factor idempotent range to the transported
    -- range.
    exact Module.FinitePresentation.of_equiv e
  refine ⟨LinearMap.range p, LinearMap.ker p, ?_, hfp, LinearMap.IsIdempotentElem.isCompl hp⟩
  -- Membership in the range is the fixed-point criterion for an idempotent.
  exact (LinearMap.IsIdempotentElem.mem_range_iff hp).mpr hpx

variable [HenselianLocalRing R]

/-- Helper for Chap10 Lemma 10 153 13: the henselian Mittag-Leffler input gives the one-element
finite-presentation splitting property needed by the recursive direct-sum construction. -/
lemma hasFinitePresentationComplementSummandProperty_of_henselianLocalRing_of_countablyGenerated_of_mittagLeffler
    (hcg : CountablyGenerated R M) (hML : MittagLeffler R M) :
    HasFinitePresentationComplementSummandProperty R M := by
  intro N N' hNN' _hN'fp x
  -- Work intrinsically in the complementary summand `N`, inheriting the two hypotheses by the
  -- split projection from `M`.
  have hcgN : CountablyGenerated R N :=
    countablyGenerated_of_isCompl_left (R := R) (M := M) hNN' hcg
  have hMLN : MittagLeffler R N :=
    mittagLeffler_of_isCompl_left (R := R) (M := M) hNN' hML
  -- Factor the cyclic map generated by `x` through a finitely presented module.
  obtain ⟨Q, hQfp, g, h, hfix⟩ :=
    existsFactorizationFixingCyclicMap (R := R) hcgN hMLN x
  letI : Module.FinitePresentation R Q := hQfp
  let a : Module.End R Q := g.comp h
  have ha_fixed : a (g x) = g x := by
    -- The finite factor endomorphism fixes the image of `x`.
    simpa [a, LinearMap.comp_apply] using congrArg g hfix
  obtain ⟨c, hcac, hcfix⟩ :=
    existsInnerInverseOnFinitePresentationFactor_fixedVector (R := R) a ha_fixed
  -- Transport the derived idempotent back to `N` and take its range and kernel.
  exact
    existsFinitePresentationDirectSummandOfInnerInverseFactorization
      (R := R) g h x hfix c hcfix hcac

-- Proof sketch: for each generator of `M`, use the finite-presentation factorization lemma and the
-- henselian splitting argument from the textbook to split off a finitely presented direct summand
-- containing that generator; iterate over a countable generating family and identify `M` with the
-- internal direct sum of the resulting finitely presented summands.
/-- Chap10 Lemma 10 153 13: over a henselian local ring, every countably generated Mittag-Leffler module
is an internal direct sum of finitely presented `R`-submodules. This is the canonical Lean form of
the textbook statement that such a module is a direct sum of finitely presented modules. -/
@[stacks 05D6]
theorem isDirectSumOfFinitePresentation_of_henselianLocalRing_of_countablyGenerated_of_mittagLeffler
    (hcg : CountablyGenerated R M) (hML : MittagLeffler R M) :
    IsDirectSumOfFinitePresentation R M := by
  -- Reduce the theorem to the structural recursive decomposition once the henselian
  -- Mittag-Leffler one-element splitting property is available.
  exact isDirectSumOfFinitePresentation_of_hasFinitePresentationComplementSummandProperty
    (R := R) (M := M) hcg
    (hasFinitePresentationComplementSummandProperty_of_henselianLocalRing_of_countablyGenerated_of_mittagLeffler
      (R := R) (M := M) hcg hML)

end

end Module
