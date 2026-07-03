

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_85_1 (from Chap10) -/
universe u v

section

variable {R : Type u} [Ring R]

/- Domain triage:
* primary domain: projective modules and countable generation;
* sampled owner declarations:
  `Module.CountablyGenerated`,
  `Theorem_10_84_5.projective_isDirectSumOfCountablyGeneratedProjective`,
  and the direct-sum free-module instance `Module.Free.dfinsupp`;
* owner abstraction: `Module.Projective R P` with the derived predicate
  `Module.CountablyGenerated R P`;
* layer: `source-facing`, since the lemma states a chapter-level reduction criterion for when all
  projective modules are free. -/

-- Proof sketch: the forward implication is immediate. For the converse, apply Theorem `10.84.5`
-- to write any projective `R`-module as an internal direct sum of countably generated projective
-- submodules; by hypothesis each summand is free, and an internal direct sum of free modules is
-- free.
/-- Lemma 10.85.1: every projective `R`-module is free if and only if every countably generated
projective `R`-module is free. -/
theorem allProjectiveModulesFree_iff_allCountablyGeneratedProjectiveModulesFree :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.Projective R P],
      Module.Free R P) ↔
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.Projective R P],
      Module.CountablyGenerated R P → Module.Free R P) := by
  constructor
  · intro h P _ _ _ _
    -- The forward implication is immediate: a stronger freeness statement already covers the
    -- countably generated projective case.
    exact h P
  · intro h P _ _ _
    classical
    -- Decompose the projective module into countably generated projective summands using
    -- Theorem 10.84.5.
    rcases (projective_isDirectSumOfCountablyGeneratedProjective.{u, v, max u v}
        (R := R) (P := P)) with ⟨ι, _, A, hA, hcountproj⟩
    have hfreeA : ∀ i, Module.Free R (A i) := by
      intro i
      -- Each summand is free by the converse hypothesis, since Theorem 10.84.5 packages both
      -- projectivity and countable generation for that summand.
      letI : Module.Projective R (A i) := (hcountproj i).projective
      exact h (A i) (hcountproj i).countablyGenerated
    letI : ∀ i, Module.Free R (A i) := hfreeA
    -- Collect bases from the free summands along the internal direct-sum decomposition to obtain
    -- a basis of the whole module.
    exact Module.Free.of_basis <|
      hA.collectedBasis fun i ↦ Module.Free.chooseBasis R (A i)

end

/-! ### Lemma_10_85_2 (from Chap10) -/
universe u v

namespace Module

section

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/-- A module has the finite-free complement summand property if, after splitting off any finite
free direct summand, every element of the complementary summand lies in a free direct summand of
that complement. -/
def HasFiniteFreeComplementSummandProperty : Prop :=
  ∀ ⦃N N' : Submodule R M⦄, IsCompl N N' → Module.Finite R N' → Module.Free R N' →
    ∀ x : N, ∃ F F' : Submodule R N, x ∈ F ∧ Module.Free R F ∧ IsCompl F F'

end

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.85.2: a countably generated module admits a generating sequence indexed by
`ℕ`. -/
lemma exists_generator_sequence (hcg : CountablyGenerated R M) :
    ∃ x : ℕ → M, Submodule.span R (Set.range x) = ⊤ := by
  rcases (Module.countablyGenerated_iff (R := R) (M := M)).mp hcg with ⟨s, hs, hspan⟩
  rcases Set.countable_iff_exists_subset_range.mp hs with ⟨x, hsx⟩
  -- Passing from a countable spanning set to a sequence only enlarges the span.
  refine ⟨x, top_le_iff.mp ?_⟩
  rw [← hspan]
  exact Submodule.span_mono hsx

/-- Helper for Lemma 10.85.2: inside a complement to a finite free summand, a chosen element lies
in a finite free direct summand of that complement. -/
lemma exists_finite_free_piece_of_mem_complement
    (hM : HasFiniteFreeComplementSummandProperty R M)
    {K C : Submodule R M} (hCK : IsCompl C K)
    (hKfinite : Module.Finite R K) (hKfree : Module.Free R K) (x : C) :
    ∃ A C' : Submodule R M,
      (x : M) ∈ A ∧
      A ≤ C ∧
      Disjoint A C' ∧
      A ⊔ C' = C ∧
      Module.Finite R A ∧
      Module.Free R A := by
  classical
  obtain ⟨F, F', hxF, hFfree, hFF'⟩ := hM hCK hKfinite hKfree x
  let b : Basis (Module.Free.ChooseBasisIndex R F) R F := Module.Free.chooseBasis R F
  let s : Finset (Module.Free.ChooseBasisIndex R F) := (b.repr ⟨x, hxF⟩).support
  let A₀ : Submodule R F := Submodule.span R (b '' (↑s : Set (Module.Free.ChooseBasisIndex R F)))
  let B₀ : Submodule R F := Submodule.span R (b '' ((↑s : Set (Module.Free.ChooseBasisIndex R F))ᶜ))
  have hxA₀ : (⟨x, hxF⟩ : F) ∈ A₀ := by
    -- The chosen element only uses finitely many basis coordinates.
    simpa [A₀, s] using Basis.mem_span_repr_support b ⟨x, hxF⟩
  have hA₀B₀ : IsCompl A₀ B₀ := by
    -- Splitting the basis by support yields a complementary decomposition.
    simpa [A₀, B₀] using
      (b.linearIndependent.isCompl_span_image b.span_eq (s := (↑s : Set _))
        (t := ((↑s : Set _)ᶜ)) isCompl_compl)
  let v : s → F := fun i ↦ b i
  have hv : LinearIndependent R v := by
    simpa [v] using
      (b.linearIndependent.comp (fun i : s ↦ (i : Module.Free.ChooseBasisIndex R F))
        fun i j h ↦ Subtype.ext h)
  have hA₀eq : Submodule.span R (Set.range v) = A₀ := by
    simp [A₀, v, Set.image_eq_range]
  have hA₀finite : Module.Finite R A₀ := by
    -- A finite support span has a finite basis indexed by the support.
    exact hA₀eq ▸ Module.Finite.of_basis (Basis.span hv)
  have hA₀free : Module.Free R A₀ := by
    -- The same support basis gives freeness of the finite piece.
    exact hA₀eq ▸ Module.Free.of_basis (Basis.span hv)
  let Ain : Submodule R C := A₀.map F.subtype
  let Bin : Submodule R C := B₀.map F.subtype
  have hxAin : x ∈ Ain := by
    exact ⟨⟨x, hxF⟩, hxA₀, rfl⟩
  have hAinBin_disjoint : Disjoint Ain Bin := by
    exact Submodule.disjoint_map (Submodule.subtype_injective F) hA₀B₀.disjoint
  have hAinBin_sup : Ain ⊔ Bin = F := by
    dsimp [Ain, Bin]
    rw [← Submodule.map_sup, hA₀B₀.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
  have hAinfinite : Module.Finite R Ain := by
    exact Module.Finite.equiv (F.equivSubtypeMap A₀)
  have hAinfree : Module.Free R Ain := by
    exact Module.Free.of_equiv (F.equivSubtypeMap A₀)
  have hAinCin : IsCompl Ain (Bin ⊔ F') := by
    have hFF'' : IsCompl (Ain ⊔ Bin) F' := by
      simpa [hAinBin_sup] using hFF'
    exact hAinBin_disjoint.isCompl_sup_right_of_isCompl_sup_left hFF''
  let A : Submodule R M := Ain.map C.subtype
  let C' : Submodule R M := (Bin ⊔ F').map C.subtype
  have hxA : (x : M) ∈ A := by
    exact ⟨x, hxAin, rfl⟩
  have hAle : A ≤ C := C.map_subtype_le Ain
  have hAC' : Disjoint A C' := by
    exact Submodule.disjoint_map (Submodule.subtype_injective C) hAinCin.disjoint
  have hsup : A ⊔ C' = C := by
    -- Mapping the internal split in `C` back to ambient `M` recovers the whole complement.
    rw [← Submodule.map_sup, hAinCin.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
  have hAfinite : Module.Finite R A := by
    exact Module.Finite.equiv (C.equivSubtypeMap Ain)
  have hAfree : Module.Free R A := by
    exact Module.Free.of_equiv (C.equivSubtypeMap Ain)
  exact ⟨A, C', hxA, hAle, hAC', hsup, hAfinite, hAfree⟩

/-- Helper for Lemma 10.85.2: splitting the current complement refines the ambient direct-sum
decomposition by adjoining the new finite free piece to the old stage. -/
lemma isCompl_sup_of_split_inside_complement
    {K C A C' : Submodule R M} (hKC : IsCompl K C) (hAC' : Disjoint A C')
    (hC : A ⊔ C' = C) :
    IsCompl (K ⊔ A) C' := by
  -- After rewriting the old complement as `A ⊔ C'`, modularity upgrades the complement relation.
  rw [← hC] at hKC
  exact hAC'.isCompl_sup_left_of_isCompl_sup_right hKC

/-- Helper for Lemma 10.85.2: if `A` sits inside a complement `C`, is disjoint from `C' ≤ C`,
and `K` is complementary to `C`, then `A` is disjoint from `K ⊔ C'`. -/
lemma disjoint_piece_sup_of_isCompl
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

/-- Helper for Lemma 10.85.2: a stage consists of a finite free direct summand together with its
complementary submodule. -/
structure FiniteFreeStage where
  K : Submodule R M
  C : Submodule R M
  isCompl : IsCompl C K
  finite_K : Module.Finite R K
  free_K : Module.Free R K

/-- Helper for Lemma 10.85.2: a successor step splits a finite free piece from the current
complement and enlarges the finite free stage. -/
structure FiniteFreeStep (x : M) (S : FiniteFreeStage (R := R) (M := M)) where
  A : Submodule R M
  next : FiniteFreeStage (R := R) (M := M)
  piece_le : A ≤ S.C
  piece_disjoint_next : Disjoint A next.C
  piece_sup_next : A ⊔ next.C = S.C
  finite_A : Module.Finite R A
  free_A : Module.Free R A
  next_stage_eq : next.K = S.K ⊔ A
  mem_next : x ∈ next.K

/-- Helper for Lemma 10.85.2: adjoining a disjoint finite free piece to a finite free stage keeps
the enlarged stage finite free. -/
lemma finite_free_sup_of_disjoint
    {K A : Submodule R M} (hKA : Disjoint K A)
    (hKfinite : Module.Finite R K) (hKfree : Module.Free R K)
    (hAfinite : Module.Finite R A) (hAfree : Module.Free R A) :
    Module.Finite R ↥(K ⊔ A) ∧ Module.Free R ↥(K ⊔ A) := by
  letI : Module.Finite R K := hKfinite
  letI : Module.Free R K := hKfree
  letI : Module.Finite R A := hAfinite
  letI : Module.Free R A := hAfree
  let f : K × A →ₗ[R] ↥(K ⊔ A) :=
    LinearMap.codRestrict (K ⊔ A) (K.subtype.coprod A.subtype) fun z ↦ by
      rcases z with ⟨k, a⟩
      exact Submodule.mem_sup.2 ⟨k, k.2, a, a.2, rfl⟩
  have hcoprod_inj : Function.Injective (K.subtype.coprod A.subtype) := by
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
  letI : Module.Finite R (K × A) := inferInstance
  letI : Module.Free R (K × A) := inferInstance
  let e : (K × A) ≃ₗ[R] ↥(K ⊔ A) := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  -- Transport finite generation and freeness across the canonical product equivalence.
  exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩

/-- Helper for Lemma 10.85.2: from one stage and one ambient element, split off the next finite
free piece exactly as in the textbook induction step. -/
lemma exists_finite_free_step
    (hM : HasFiniteFreeComplementSummandProperty R M)
    (x : M) (S : FiniteFreeStage (R := R) (M := M)) :
    Nonempty (FiniteFreeStep (R := R) (M := M) x S) := by
  classical
  let e := Submodule.prodEquivOfIsCompl S.C S.K S.isCompl
  let xC : S.C := (e.symm x).1
  have hx_decomp' : e (e.symm x) = x := e.apply_symm_apply x
  have hx_decomp : (xC : M) + (((e.symm x).2 : S.K) : M) = x := by
    -- Project `x` to the current complement and the finite free stage.
    simpa [e, xC] using hx_decomp'
  obtain ⟨A, C', hxA, hAle, hAC', hsup, hAfinite, hAfree⟩ :=
    exists_finite_free_piece_of_mem_complement (R := R) (M := M) hM S.isCompl S.finite_K
      S.free_K xC
  have hKA : Disjoint S.K A := by
    -- The new piece still lies in the current complement, hence is disjoint from the old stage.
    exact (S.isCompl.disjoint.mono_left hAle).symm
  obtain ⟨hnextFinite, hnextFree⟩ :=
    finite_free_sup_of_disjoint (R := R) (M := M) hKA S.finite_K S.free_K hAfinite hAfree
  have hnextCompl : IsCompl C' (S.K ⊔ A) := by
    -- Refining the complement produces the next stage/complement pair.
    exact
      (isCompl_sup_of_split_inside_complement (R := R) (M := M) S.isCompl.symm hAC' hsup).symm
  let nextStage : FiniteFreeStage (R := R) (M := M) :=
    ⟨S.K ⊔ A, C', hnextCompl, hnextFinite, hnextFree⟩
  have hx_next : x ∈ nextStage.K := by
    -- Reinsert the projected complement component into the enlarged stage.
    change x ∈ S.K ⊔ A
    rw [Submodule.mem_sup]
    refine ⟨((e.symm x).2 : S.K), (e.symm x).2.2, (xC : M), hxA, ?_⟩
    simpa [add_comm] using hx_decomp
  refine ⟨⟨A, nextStage, hAle, ?_, ?_, hAfinite, hAfree, rfl, hx_next⟩⟩
  · simpa [nextStage] using hAC'
  · simpa [nextStage] using hsup

/-- Helper for Lemma 10.85.2: recursively choose the finite free stages, complements, and pieces
attached to a generating sequence. -/
lemma exists_finite_free_stage_chain
    (hM : HasFiniteFreeComplementSummandProperty R M) (x : ℕ → M) :
    ∃ K C A : ℕ → Submodule R M,
      K 0 = ⊥ ∧
      C 0 = ⊤ ∧
      (∀ n, IsCompl (C n) (K n)) ∧
      (∀ n, Module.Finite R (K n)) ∧
      (∀ n, Module.Free R (K n)) ∧
      (∀ n, A n ≤ C n) ∧
      (∀ n, Disjoint (A n) (C (n + 1))) ∧
      (∀ n, A n ⊔ C (n + 1) = C n) ∧
      (∀ n, Module.Finite R (A n)) ∧
      (∀ n, Module.Free R (A n)) ∧
      (∀ n, K (n + 1) = K n ⊔ A n) ∧
      (∀ n, x n ∈ K (n + 1)) := by
  classical
  let base : FiniteFreeStage (R := R) (M := M) :=
    ⟨⊥, ⊤, isCompl_top_bot, inferInstance, inferInstance⟩
  let chooseStep :
      ∀ n, (S : FiniteFreeStage (R := R) (M := M)) →
        FiniteFreeStep (R := R) (M := M) (x n) S := fun n S ↦
        Classical.choice (exists_finite_free_step (R := R) (M := M) hM (x n) S)
  let stage : ℕ → FiniteFreeStage (R := R) (M := M) :=
    Nat.rec base fun n S ↦ (chooseStep n S).next
  let A' : ℕ → Submodule R M := fun n ↦ (chooseStep n (stage n)).A
  refine ⟨fun n ↦ (stage n).K, fun n ↦ (stage n).C, A', rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · intro n
    exact (stage n).isCompl
  · intro n
    exact (stage n).finite_K
  · intro n
    exact (stage n).free_K
  · intro n
    exact (chooseStep n (stage n)).piece_le
  · intro n
    simpa [A', stage, chooseStep] using (chooseStep n (stage n)).piece_disjoint_next
  · intro n
    simpa [A', stage, chooseStep] using (chooseStep n (stage n)).piece_sup_next
  · intro n
    exact (chooseStep n (stage n)).finite_A
  · intro n
    exact (chooseStep n (stage n)).free_A
  · intro n
    simpa [A', stage, chooseStep] using (chooseStep n (stage n)).next_stage_eq
  · intro n
    simpa [A', stage, chooseStep] using (chooseStep n (stage n)).mem_next

/-- Helper for Lemma 10.85.2: each recursive stage is the finite supremum of the pieces chosen so
far. -/
lemma stage_eq_iSup_pieces
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

/-- Helper for Lemma 10.85.2: the recursively chosen pieces are pairwise disjoint because each new
piece stays inside the current complement while all earlier pieces lie in the current stage. -/
lemma pieces_pairwise_disjoint
    {K C A : ℕ → Submodule R M}
    (hCompl : ∀ n, IsCompl (C n) (K n))
    (hAle : ∀ n, A n ≤ C n)
    (hstage : ∀ n, K n = ⨆ i ∈ Finset.range n, A i) :
    Pairwise fun i j ↦ Disjoint (A i) (A j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
  · have hAiKj : A i ≤ K j := by
      rw [hstage j]
      exact le_iSup_of_le i <| le_iSup_of_le (by simpa using hij_lt) le_rfl
    -- Compare the earlier piece with the complement containing the later piece.
    exact ((hCompl j).symm.disjoint.mono_left hAiKj).mono_right (hAle j)
  · have hAjKi : A j ≤ K i := by
      rw [hstage i]
      exact le_iSup_of_le j <| le_iSup_of_le (by simpa using hij_gt) le_rfl
    -- The reverse inequality gives the symmetric disjointness statement.
    exact (((hCompl i).symm.disjoint.mono_left hAjKi).mono_right (hAle i)).symm

-- Proof sketch: choose a countable generating sequence `x₁, x₂, …` for `M` and inductively split
-- off finite free direct summands `F₁, F₂, …` so that `F₁ ⊕ ⋯ ⊕ Fₙ` contains the first `n`
-- generators. The hypothesis applied to the complement after stage `n` produces `Fₙ₊₁`, and the
-- resulting countable direct-sum decomposition exhibits `M` as a free module.
/-- Lemma 10.85.2: a countably generated `R`-module is free if, whenever `M = N ⊕ N'` with `N'`
finite free, every element of `N` lies in a free direct summand of `N`. -/
theorem free_of_countablyGenerated_of_hasFiniteFreeComplementSummandProperty
    (hcg : CountablyGenerated R M)
    (hM : HasFiniteFreeComplementSummandProperty R M) :
    Module.Free R M := by
  classical
  -- Extract the countable generating sequence used in the source proof.
  obtain ⟨x, hxspan⟩ := exists_generator_sequence (R := R) (M := M) hcg
  obtain ⟨K, C, A, hK0, _, hCompl, hKfinite, hKfree, hAle, hADisj, hASup, hAfinite, hAfree,
    hKstep, hxstage⟩ := exists_finite_free_stage_chain (R := R) (M := M) hM x
  have hstage : ∀ n, K n = ⨆ i ∈ Finset.range n, A i :=
    stage_eq_iSup_pieces (R := R) (M := M) hK0 hKstep
  have hpair : Pairwise fun i j ↦ Disjoint (A i) (A j) :=
    pieces_pairwise_disjoint (R := R) (M := M) hCompl hAle hstage
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
    -- Route correction: pairwise disjointness alone is not enough here; the source proof uses the
    -- stage/complement containment to bound all earlier pieces by `K i` and all later ones by
    -- `C (i + 1)`.
    rw [iSupIndep_def]
    intro i
    have hAiKi : Disjoint (A i) (K i) := (hCompl i).disjoint.mono_left (hAle i)
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
      exact disjoint_piece_sup_of_isCompl (R := R) (M := M) (hCompl i) (hAle i) (hADisj i)
        ((by
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
    -- The recursively chosen pieces contain every generator, so they span all of `M`.
    apply top_le_iff.mp
    rw [← hxspan]
    exact Submodule.span_le.2 fun y hy ↦ by
      rcases hy with ⟨n, rfl⟩
      exact hxmem n
  have hinternal : DirectSum.IsInternal A :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨hindep, htop⟩
  letI : ∀ n, Module.Free R (A n) := hAfree
  let e : (DirectSum ℕ fun i ↦ ↥(A i)) ≃ₗ[R] M :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hinternal
  -- Route correction: the source proof ends by identifying `M` with the internal direct sum of
  -- the pairwise disjoint finite free pieces rather than by chasing a separate basis recursively.
  exact Module.Free.of_equiv e

end

end Module
