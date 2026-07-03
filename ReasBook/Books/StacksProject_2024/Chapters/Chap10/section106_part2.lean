import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_106_2 (from Chap10) -/
open IsLocalRing

universe u

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

local notation "m" => maximalIdeal R
local notation "κ" => ResidueField R
local notation "grR" => idealAssociatedGradedRing m

/- Domain-style sampling pass.

Primary domain: local commutative algebra of regular local rings and their basic derived
ring-theoretic consequences.

Sampled owner declarations:
* `IsRegularLocalRing` and `IsRegularLocalRing.iff_finrank_cotangentSpace` from mathlib's
  regular-local-ring owner API;
* the direct downstream owner use `regularLocalRing_uniqueFactorizationMonoid` in
  `Chap15/Lemma_15_122_2.lean`, which consumes the domain consequence through typeclass search.

Best owner abstraction: the ambient owner is `IsRegularLocalRing R`. The target declaration here is
derived API: the canonical ring-theoretic consequence that such an `R` is a domain.

Primitive vs. derived:
* primitive data: only the owner hypothesis `[IsRegularLocalRing R]`;
* derived API: the instance `IsDomain R`.

Source/core/bridge triage:
* source-facing: the Stacks lemma asserting that a regular local ring is a domain;
* core/canonical: the owner predicate `IsRegularLocalRing R`;
* bridge/view: this file's derived typeclass instance `IsDomain R`. -/

/-- Helper for Lemma 10.106.2: every nonzero element lies in some maximal power of the maximal
ideal. -/
private theorem exists_mem_pow_and_not_mem_pow_succ_of_ne_zero (x : R) (hx : x ≠ 0) :
    ∃ n : ℕ, x ∈ m ^ n ∧ x ∉ m ^ (n + 1) := by
  classical
  have hintersection : (⨅ n : ℕ, m ^ n) = (⊥ : Ideal R) :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing m Ideal.IsPrime.ne_top'
  have hnot_all : ¬ ∀ n : ℕ, x ∈ m ^ n := by
    intro hx_all
    have hx_inf : x ∈ (⨅ n : ℕ, m ^ n) := by
      rw [Ideal.mem_iInf]
      exact hx_all
    have hx_bot : x ∈ (⊥ : Ideal R) := by
      simpa [hintersection] using hx_inf
    exact hx ((Ideal.mem_bot).1 hx_bot)
  have hexists : ∃ n : ℕ, x ∉ m ^ (n + 1) := by
    by_contra h
    apply hnot_all
    intro n
    cases n with
    | zero =>
        simpa using (show x ∈ (⊤ : Ideal R) from Ideal.mem_top)
    | succ k =>
        exact by
          by_contra hx_mem
          exact h ⟨k, hx_mem⟩
  refine ⟨Nat.find hexists, ?_, Nat.find_spec hexists⟩
  cases hfind : Nat.find hexists with
  | zero =>
      simpa [hfind]
  | succ k =>
      have hk : ¬ x ∉ m ^ (k + 1) := by
        apply Nat.find_min hexists
        simpa [hfind] using Nat.lt_succ_self k
      exact by
        by_contra hx_mem
        exact hk hx_mem

/-- Helper for Lemma 10.106.2: the associated graded ring of a regular local ring has no zero
divisors because Lemma 10.106.1 identifies it with a polynomial ring over the residue field. -/
private theorem associated_graded_noZeroDivisors : NoZeroDivisors grR := by
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hdim : ringKrullDim R = d := by
    -- A regular local ring has dimension equal to the minimal number of generators of `m`.
    simpa [d] using
      ((isRegularLocalRing_iff (R := R)).1 (inferInstance : IsRegularLocalRing R)).symm
  rcases
      regularLocalRing_associatedGraded_nonempty_algEquiv_mvPolynomial (R := R) (d := d) hdim
    with ⟨e⟩
  -- Pull the domain property back across the polynomial presentation of the associated graded ring.
  exact e.symm.toMulEquiv.noZeroDivisors _

/-- Helper for Lemma 10.106.2: a stage class in the associated graded ring vanishes exactly when
its representative already lies in the next power of the maximal ideal. -/
private theorem idealAssociatedGradedStageClass_eq_zero_iff_mem_succ {n : ℕ}
    (x : RingTheory.Sequence.idealAssociatedGradedStage m R n) :
    idealAssociatedGradedStageClass m n x = 0 ↔
      (x : R) ∈ RingTheory.Sequence.idealAssociatedGradedStage m R (n + 1) := by
  constructor
  · intro hx
    have hgrade :
        (⟨idealAssociatedGradedStageClass m n x,
            idealAssociatedGradedStageClass_mem_grade m n x⟩ :
          idealAssociatedGradedRingGrade m n) = 0 := by
      apply Subtype.ext
      simpa using hx
    have hpiece :
        (Submodule.Quotient.mk x : RingTheory.Sequence.idealAssociatedGradedPiece m R n) = 0 := by
      -- Transport the vanishing statement across the grade/piece equivalence from the dependency.
      have happly :
          idealAssociatedGradedRingGrade_equiv_piece m n
              ⟨idealAssociatedGradedStageClass m n x,
                idealAssociatedGradedStageClass_mem_grade m n x⟩ = 0 := by
        have happly' :
            idealAssociatedGradedRingGrade_equiv_piece m n
                ⟨idealAssociatedGradedStageClass m n x,
                  idealAssociatedGradedStageClass_mem_grade m n x⟩ =
              idealAssociatedGradedRingGrade_equiv_piece m n 0 := by
          exact
            congrArg
              (fun z : idealAssociatedGradedRingGrade m n ↦ idealAssociatedGradedRingGrade_equiv_piece m n z)
              hgrade
        calc
          idealAssociatedGradedRingGrade_equiv_piece m n
              ⟨idealAssociatedGradedStageClass m n x,
                idealAssociatedGradedStageClass_mem_grade m n x⟩ =
            idealAssociatedGradedRingGrade_equiv_piece m n 0 := happly'
          _ = 0 := LinearEquiv.map_zero (idealAssociatedGradedRingGrade_equiv_piece m n)
      simpa [idealAssociatedGradedRingGrade_equiv_piece_apply_stage] using happly
    -- Zero in the quotient means the representative lies in the next filtration stage.
    simpa using
      (Submodule.Quotient.mk_eq_zero
        ((RingTheory.Sequence.idealAssociatedGradedStage m R (n + 1)).submoduleOf
          (RingTheory.Sequence.idealAssociatedGradedStage m R n))).1 hpiece
  · intro hx
    have hpiece :
        (Submodule.Quotient.mk x : RingTheory.Sequence.idealAssociatedGradedPiece m R n) = 0 := by
      -- Repackage next-stage membership as vanishing in the quotient piece.
      exact
        (Submodule.Quotient.mk_eq_zero
          ((RingTheory.Sequence.idealAssociatedGradedStage m R (n + 1)).submoduleOf
            (RingTheory.Sequence.idealAssociatedGradedStage m R n))).2 <| by
            simpa using hx
    have hgrade :
        (⟨idealAssociatedGradedStageClass m n x,
            idealAssociatedGradedStageClass_mem_grade m n x⟩ :
          idealAssociatedGradedRingGrade m n) = 0 := by
      -- Move the quotient vanishing back to the owner grade.
      have happly :
          idealAssociatedGradedRingGrade_equiv_piece m n
              ⟨idealAssociatedGradedStageClass m n x,
                idealAssociatedGradedStageClass_mem_grade m n x⟩ = 0 := by
        simpa [idealAssociatedGradedRingGrade_equiv_piece_apply_stage] using hpiece
      have happly' :
          idealAssociatedGradedRingGrade_equiv_piece m n
              ⟨idealAssociatedGradedStageClass m n x,
                idealAssociatedGradedStageClass_mem_grade m n x⟩ =
            idealAssociatedGradedRingGrade_equiv_piece m n 0 := by
        calc
          idealAssociatedGradedRingGrade_equiv_piece m n
              ⟨idealAssociatedGradedStageClass m n x,
                idealAssociatedGradedStageClass_mem_grade m n x⟩ = 0 := happly
          _ = idealAssociatedGradedRingGrade_equiv_piece m n 0 := by
              symm
              exact LinearEquiv.map_zero (idealAssociatedGradedRingGrade_equiv_piece m n)
      exact (idealAssociatedGradedRingGrade_equiv_piece m n).injective happly'
    -- Forgetting the grade subtype recovers the vanishing of the original stage class.
    exact congrArg (fun z : idealAssociatedGradedRingGrade m n ↦ (z : grR)) hgrade

/-- Helper for Lemma 10.106.2: if a product lands one step deeper in the maximal-ideal filtration,
then one factor was already one step deeper. -/
private theorem mem_pow_succ_or_mem_pow_succ_of_mul_mem_pow_add_succ
    {a b : ℕ} {f g : R}
    (hf : f ∈ m ^ a) (hg : g ∈ m ^ b) (hfg : f * g ∈ m ^ (a + b + 1)) :
    f ∈ m ^ (a + 1) ∨ g ∈ m ^ (b + 1) := by
  let xf : RingTheory.Sequence.idealAssociatedGradedStage m R a := ⟨f, by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using hf⟩
  let xg : RingTheory.Sequence.idealAssociatedGradedStage m R b := ⟨g, by
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using hg⟩
  let xfg : RingTheory.Sequence.idealAssociatedGradedStage m R (a + b) := ⟨f * g, by
    -- The adic filtration is multiplicative.
    simpa [RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top,
      pow_add] using Ideal.mul_mem_mul hf hg⟩
  have hproduct_zero :
      idealAssociatedGradedStageClass m a xf * idealAssociatedGradedStageClass m b xg = 0 := by
    have hxfg_zero : idealAssociatedGradedStageClass m (a + b) xfg = 0 := by
      -- The deeper filtration hypothesis is exactly the zero criterion in the associated graded ring.
      apply (idealAssociatedGradedStageClass_eq_zero_iff_mem_succ (R := R) (n := a + b) xfg).2
      simpa [xfg, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
        using hfg
    -- Route correction: translate the product into the associated graded ring before using
    -- no-zero-divisors, rather than trying to compare powers directly in `R`.
    calc
      idealAssociatedGradedStageClass m a xf * idealAssociatedGradedStageClass m b xg =
          idealAssociatedGradedStageClass m (a + b) xfg := by
            symm
            simpa [xf, xg, xfg] using idealAssociatedGradedStageClass_mul_local m xf xg
      _ = 0 := hxfg_zero
  let _ : NoZeroDivisors grR := associated_graded_noZeroDivisors (R := R)
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hproduct_zero with hzero_f | hzero_g
  · left
    -- Vanishing of the `a`-stage class means `f` already lies in `m^(a + 1)`.
    simpa [xf, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using (idealAssociatedGradedStageClass_eq_zero_iff_mem_succ (R := R) (n := a) xf).1 hzero_f
  · right
    -- Vanishing of the `b`-stage class means `g` already lies in `m^(b + 1)`.
    simpa [xg, RingTheory.Sequence.idealAssociatedGradedStage, Ideal.smul_eq_mul, Ideal.mul_top]
      using (idealAssociatedGradedStageClass_eq_zero_iff_mem_succ (R := R) (n := b) xg).1 hzero_g

-- Proof sketch: use Krull's intersection theorem to get `⋂ n, (maximalIdeal R)^n = 0`. If
-- `f * g = 0` with both `f` and `g` nonzero, choose maximal integers `a` and `b` such that
-- `f ∈ (maximalIdeal R)^a` and `g ∈ (maximalIdeal R)^b`. Then
-- `f * g = 0 ∈ (maximalIdeal R)^(a + b + 1)`, and Lemma `10.106.1` forces either
-- `f ∈ (maximalIdeal R)^(a + 1)` or `g ∈ (maximalIdeal R)^(b + 1)`, contradicting maximality.
/-- Lemma 10.106.2: any regular local ring is a domain. -/
instance regularLocalRing_isDomain : IsDomain R := by
  let _ : NoZeroDivisors R := by
    refine ⟨?_⟩
    intro f g hfg
    by_cases hf0 : f = 0
    · exact Or.inl hf0
    by_cases hg0 : g = 0
    · exact Or.inr hg0
    rcases exists_mem_pow_and_not_mem_pow_succ_of_ne_zero (R := R) f hf0 with
      ⟨a, hfa, hfa_succ⟩
    rcases exists_mem_pow_and_not_mem_pow_succ_of_ne_zero (R := R) g hg0 with
      ⟨b, hgb, hgb_succ⟩
    have hmul_mem : f * g ∈ m ^ (a + b + 1) := by
      -- The zero product lies in every power, so the filtration lemma applies.
      simpa [hfg] using (Ideal.zero_mem (m ^ (a + b + 1)))
    rcases
        mem_pow_succ_or_mem_pow_succ_of_mul_mem_pow_add_succ (R := R) hfa hgb hmul_mem
      with hfa_next | hgb_next
    · exact False.elim (hfa_succ hfa_next)
    · exact False.elim (hgb_succ hgb_next)
  -- A nontrivial commutative ring without zero divisors is a domain.
  exact NoZeroDivisors.to_isDomain R

end

/-! ### Lemma_10_106_3 (from Chap10) -/
universe u

open RingTheory Sequence IsLocalRing
open scoped Pointwise

section

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Helper for Lemma 10.106.3: the ideal generated by the head parameter of a chosen family. -/
def headParameterIdeal {A : Type u} [CommRing A] [IsLocalRing A] {d : ℕ}
    (x : Fin (d + 1) → maximalIdeal A) : Ideal A :=
  Ideal.span ({((x 0 : maximalIdeal A) : A)} : Set A)

/-- Helper for Lemma 10.106.3: the quotient by the head parameter remains nontrivial. -/
lemma headParameterIdeal_ne_top {A : Type u} [CommRing A] [IsLocalRing A] {d : ℕ}
    (x : Fin (d + 1) → maximalIdeal A) :
    headParameterIdeal x ≠ ⊤ := by
  intro htop
  have hle : headParameterIdeal x ≤ maximalIdeal A := by
    dsimp [headParameterIdeal]
    exact
      (Ideal.span_singleton_le_iff_mem (I := maximalIdeal A) (x := ((x 0 : maximalIdeal A) : A))).2
        (x 0).2
  have hmax : maximalIdeal A = ⊤ := top_le_iff.mp (htop ▸ hle)
  exact (maximalIdeal.isMaximal A).ne_top hmax

/-- Helper for Lemma 10.106.3: the quotient image of each tail parameter remains in the quotient
maximal ideal. -/
lemma tail_image_mem_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A] {d : ℕ}
    (x : Fin (d + 1) → maximalIdeal A)
    [IsLocalRing (A ⧸ headParameterIdeal x)] (i : Fin d) :
    Ideal.Quotient.mk (headParameterIdeal x) (((x i.succ : maximalIdeal A) : A)) ∈
      maximalIdeal (A ⧸ headParameterIdeal x) := by
  let I : Ideal A := headParameterIdeal x
  let S := A ⧸ I
  have hmap :
      Ideal.map (Ideal.Quotient.mk I) (maximalIdeal A) = maximalIdeal S := by
    exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hmem :
      Ideal.Quotient.mk I (((x i.succ : maximalIdeal A) : A)) ∈
        Ideal.map (Ideal.Quotient.mk I) (maximalIdeal A) := by
    refine (Ideal.mem_map_iff_of_surjective (f := Ideal.Quotient.mk I)
      (hf := Ideal.Quotient.mk_surjective) (I := maximalIdeal A)
      (y := Ideal.Quotient.mk I (((x i.succ : maximalIdeal A) : A)))).2 ?_
    exact ⟨((x i.succ : maximalIdeal A) : A), (x i.succ).2, rfl⟩
  simpa [I, S, hmap] using hmem

/-- Helper for Lemma 10.106.3: mapping the full parameter ideal to the head quotient kills only
the head generator and leaves the mapped tail family. -/
lemma map_parameterIdeal_eq_tail_parameterIdeal {A : Type u} [CommRing A] [IsLocalRing A]
    {d : ℕ} (x : Fin (d + 1) → maximalIdeal A)
    [IsLocalRing (A ⧸ headParameterIdeal x)] :
    let xbar : Fin d → maximalIdeal (A ⧸ headParameterIdeal x) := fun i ↦
      ⟨Ideal.Quotient.mk (headParameterIdeal x) (((x i.succ : maximalIdeal A) : A)),
        tail_image_mem_maximalIdeal x i⟩
    Ideal.map (Ideal.Quotient.mk (headParameterIdeal x)) (parameterIdeal x) = parameterIdeal xbar := by
  let I : Ideal A := headParameterIdeal x
  let S := A ⧸ I
  let xbar : Fin d → maximalIdeal S := fun i ↦
    ⟨Ideal.Quotient.mk I (((x i.succ : maximalIdeal A) : A)), tail_image_mem_maximalIdeal x i⟩
  suffices
      hspan :
        Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range fun i ↦ ((x i : maximalIdeal A) : A))) =
          Ideal.span (Set.range fun i ↦ ((xbar i : maximalIdeal S) : S)) by
    simpa [parameterIdeal_eq_span, xbar] using hspan
  rw [Ideal.map_span]
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
    refine Fin.cases ?_ ?_ i
    · have hx0 : Ideal.Quotient.mk I (((x 0 : maximalIdeal A) : A)) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem]
        dsimp [I, headParameterIdeal]
        exact Ideal.subset_span (by simp)
      simpa [hx0]
    · intro j
      exact Ideal.subset_span ⟨j, rfl⟩
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.subset_span ⟨((x i.succ : maximalIdeal A) : A), ⟨i.succ, rfl⟩, rfl⟩

/-- Helper for Lemma 10.106.3: the tuple-based parameter ideal agrees with the list-based ideal
on the same ordered family. -/
private theorem parameterIdeal_eq_idealOfList_ofFn {d : ℕ} (x : Fin d → maximalIdeal R) :
    Ideal.ofList (List.ofFn fun i : Fin d ↦ ((x i : maximalIdeal R) : R)) = parameterIdeal x := by
  rw [Ideal.ofList, parameterIdeal_eq_span]
  congr 1
  ext r
  constructor
  · intro hr
    rcases List.mem_ofFn.mp hr with ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact List.mem_ofFn.mpr ⟨i, rfl⟩

/- Domain-style sampling pass.

Primary domain: local commutative algebra of regular local rings, regular systems of parameters,
regular sequences, and the self-module Cohen-Macaulay condition.

Sampled owner declarations:
* `IsLocalRing.IsRegularSystemOfParameters`;
* `IsLocalRing.parameterIdeal`;
* `ringKrullDim_quotient_parameterIdeal_eq_sub` from `Chap10/Lemma_10_60_14.lean`;
* `Module.CohenMacaulay`.

Best owner abstraction: the source-facing chosen-family owner is
`IsLocalRing.IsRegularSystemOfParameters x` for a family `x : Fin d → maximalIdeal R`, and the
prefix quotients are canonically `R ⧸ parameterIdeal (x ∘ Fin.castLE hi)`. The public statements
below should therefore live at that owner level; the underlying `List.ofFn` regular sequence is a
derived bridge/view, while the Cohen-Macaulay conclusion lands directly in the owner
`Module.CohenMacaulay R R`.

Primitive vs. derived:
* primitive data: the regular-local owner hypothesis `[IsRegularLocalRing R]`, a length `d`, a
  chosen family `x : Fin d → maximalIdeal R`, and the owner hypothesis
  `hx : IsRegularSystemOfParameters x`;
* derived API: regularity of the underlying sequence `List.ofFn fun i ↦ (x i : R)`,
  regular-locality and dimension formulas for the prefix quotients
  `R ⧸ parameterIdeal (x ∘ Fin.castLE hi)`, and the self-module owner instance
  `Module.CohenMacaulay R R`.

Source/core/bridge triage:
* source-facing: parts (1)–(3), stated for a regular system of parameters and its canonical prefix
  quotients;
* core/canonical: `IsRegularLocalRing R`, `IsRegularSystemOfParameters`, `parameterIdeal`, and
  `Module.CohenMacaulay R R`;
* bridge/view: the regularity statement for the underlying list
  `List.ofFn fun i ↦ (x i : R)`.
-/

namespace IsLocalRing

omit [IsRegularLocalRing R] in
/-- Helper for Lemma 10.106.3: if an appended list is regular, then its left prefix is already
regular. -/
private theorem isRegular_left_of_isRegular_append {M : Type*} [AddCommGroup M] [Module R M]
    {rs ts : List R} (hreg : IsRegular M (rs ++ ts)) :
    IsRegular M rs := by
  -- Split the weak regularity condition across the append and keep only the left part.
  refine ⟨((isWeaklyRegular_append_iff (M := M) rs ts).mp hreg.toIsWeaklyRegular).1, ?_⟩
  intro htop
  -- If the prefix already generated `⊤`, then the whole appended list would do so as well.
  have hle :
      Ideal.ofList rs • (⊤ : Submodule R M) ≤
        Ideal.ofList (rs ++ ts) • (⊤ : Submodule R M) := by
    rw [Ideal.ofList_append]
    exact Submodule.smul_mono_left le_sup_left
  have htop_le :
      (⊤ : Submodule R M) ≤ Ideal.ofList (rs ++ ts) • (⊤ : Submodule R M) := by
    calc
      (⊤ : Submodule R M) = Ideal.ofList rs • (⊤ : Submodule R M) := htop
      _ ≤ Ideal.ofList (rs ++ ts) • (⊤ : Submodule R M) := hle
  have htop' : (⊤ : Submodule R M) = Ideal.ofList (rs ++ ts) • (⊤ : Submodule R M) := by
    exact (le_antisymm le_top htop_le).symm
  exact hreg.top_ne_smul htop'

/-- Helper for Lemma 10.106.3: the owner quotient module `QuotSMulTop r A` is equivalent to the
principal quotient ring for regularity questions on the tail. -/
private theorem isRegular_quotSMulTop_iff_quotient_span_singleton
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    IsRegular (QuotSMulTop r A) rs ↔
      IsRegular (A ⧸ Ideal.span ({r} : Set A))
        (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) := by
  have hspan : Ideal.span ({r} : Set A) = r • (⊤ : Ideal A) := by
    -- The principal ring quotient is the same additive quotient as `A / rA`.
    simp [smul_eq_mul, ← Submodule.ideal_span_singleton_smul]
  let e : QuotSMulTop r A ≃+ A ⧸ Ideal.span ({r} : Set A) :=
    (Ideal.quotientEquivAlgOfEq A hspan).symm.toRingEquiv.toAddEquiv
  -- Transport regularity through the quotient equivalence while mapping the scalars.
  refine e.isRegular_congr <| List.forall₂_map_right_iff.mpr ?_
  rw [List.forall₂_same]
  intro a ha x
  change e (a • x) = Ideal.Quotient.mk (Ideal.span ({r} : Set A)) a • e x
  rcases Quotient.exists_rep x with ⟨y, rfl⟩
  -- On representatives, the scalar action becomes multiplication by the residue class of `a`.
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  simp [e, smul_eq_mul]

/-- Helper for Lemma 10.106.3: quotienting first by the head element and then by the mapped tail
is the same as quotienting once by the whole list. -/
private theorem full_tail_quotient_ringEquiv_head_le
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    Ideal.span ({r} : Set A) ≤ Ideal.ofList (r :: rs) := by
  -- The head generator is one of the generators of the full list ideal.
  simpa [Ideal.ofList_cons] using
    (le_sup_left : Ideal.span ({r} : Set A) ≤ Ideal.span ({r} : Set A) ⊔ Ideal.ofList rs)

/-- Helper for Lemma 10.106.3: after quotienting by the head element, the remaining list ideal is
the image of the full ideal. -/
private theorem full_tail_quotient_ringEquiv_map_eq
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A)))) =
      (Ideal.ofList (r :: rs)).map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))) := by
  -- Modding out by the head generator only kills that first entry.
  rw [Ideal.map_ofList, List.map_cons, Ideal.ofList_cons]
  simp

/-- Helper for Lemma 10.106.3: quotienting by the head element and then by a mapped tail list is
canonically equivalent to quotienting once by the full list. -/
private noncomputable def full_tail_quotient_ringEquiv
    {A : Type u} [CommRing A] {r : A} {rs : List A} :
    ((A ⧸ Ideal.span ({r} : Set A)) ⧸
      Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set A))))) ≃+*
      A ⧸ Ideal.ofList (r :: rs) :=
  (Ideal.quotEquivOfEq (full_tail_quotient_ringEquiv_map_eq (A := A) (r := r) (rs := rs))).trans
    (DoubleQuot.quotQuotEquivQuotOfLE
      (full_tail_quotient_ringEquiv_head_le (A := A) (r := r) (rs := rs)))

/-- Helper for Lemma 10.106.3: the quotient by the head parameter carries the residual tail family
as a family in the maximal ideal. -/
abbrev head_quotient_tail {d : ℕ} (x : Fin (d + 1) → maximalIdeal R)
    [IsLocalRing (R ⧸ headParameterIdeal x)] :
    Fin d → maximalIdeal (R ⧸ headParameterIdeal x) :=
  fun i ↦
    ⟨Ideal.Quotient.mk (headParameterIdeal x) (((x i.succ : maximalIdeal R) : R)),
      tail_image_mem_maximalIdeal x i⟩

/-- Helper for Lemma 10.106.3: after quotienting by the head parameter of a regular system of
parameters, the quotient images of the remaining parameters again form a regular system of
parameters. -/
private theorem head_quotient_tail_isRegularSystemOfParameters {d : ℕ}
    {x : Fin (d + 1) → maximalIdeal R} (hx : IsRegularSystemOfParameters x) :
    let S := R ⧸ headParameterIdeal x
    letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr (headParameterIdeal_ne_top x)
    letI : IsLocalRing S :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (headParameterIdeal x))
        Ideal.Quotient.mk_surjective
    IsRegularSystemOfParameters (head_quotient_tail x) := by
  let S := R ⧸ headParameterIdeal x
  letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr (headParameterIdeal_ne_top x)
  letI : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (headParameterIdeal x))
      Ideal.Quotient.mk_surjective
  have hparameter :
      parameterIdeal (head_quotient_tail x) = maximalIdeal S := by
    -- The quotient map kills the head generator and sends the full parameter ideal to the tail
    -- parameter ideal, which is therefore the maximal ideal downstairs.
    calc
      parameterIdeal (head_quotient_tail x) =
          Ideal.map (Ideal.Quotient.mk (headParameterIdeal x)) (parameterIdeal x) := by
            symm
            simpa [head_quotient_tail] using map_parameterIdeal_eq_tail_parameterIdeal (A := R) x
      _ = Ideal.map (Ideal.Quotient.mk (headParameterIdeal x)) (maximalIdeal R) := by rw [hx.2]
      _ = maximalIdeal S := by
            exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (headParameterIdeal x))
              Ideal.Quotient.mk_surjective
  have hdim : ringKrullDim S = d := by
    -- The later regular-local quotient theorem already packages the one-step dimension drop.
    simpa [S, headParameterIdeal] using
      (head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx).2
  -- The quotient tail now satisfies the defining dimension and maximal-ideal-generation clauses.
  exact (isRegularSystemOfParameters_iff_of_ringKrullDim_eq (R := S) hdim (head_quotient_tail x)).2
    hparameter

/-- Helper for Lemma 10.106.3: in a regular system of parameters, the head element is nonzero. -/
private theorem head_parameter_ne_zero {d : ℕ} {x : Fin (d + 1) → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) :
    ((x 0 : maximalIdeal R) : R) ≠ 0 := by
  let S := R ⧸ headParameterIdeal x
  letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr (headParameterIdeal_ne_top x)
  letI : IsLocalRing S :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (headParameterIdeal x))
      Ideal.Quotient.mk_surjective
  have hdimS : ringKrullDim S = d :=
    by
      simpa [S, headParameterIdeal] using
        (head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx).2
  intro hx0
  have hhead_bot : headParameterIdeal x = (⊥ : Ideal R) := by
    -- If the head were zero, its principal ideal would be the zero ideal.
    simp [headParameterIdeal, hx0]
  have hdimS' : ringKrullDim S = d + 1 := by
    -- But quotienting by the zero ideal does not change the dimension.
    calc
      ringKrullDim S = ringKrullDim (R ⧸ (⊥ : Ideal R)) := by
        change ringKrullDim (R ⧸ headParameterIdeal x) = ringKrullDim (R ⧸ (⊥ : Ideal R))
        rw [hhead_bot]
      _ = ringKrullDim R := ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)
      _ = d + 1 := (isRegularSystemOfParameters_iff x).1 hx |>.1
  have henat : (d + 1 : ℕ∞) = d := by
    exact (WithBot.coe_inj).mp <| by
      calc
        (((d + 1 : ℕ∞) : WithBot ℕ∞)) = ringKrullDim S := by simpa using hdimS'.symm
        _ = (((d : ℕ∞) : WithBot ℕ∞)) := by simpa using hdimS
  have hnat : d + 1 = d := by
    exact_mod_cast henat
  exact Nat.succ_ne_self d hnat

/-- Helper for Lemma 10.106.3: in a domain, any nonzero scalar acts regularly on the self-module.
-/
private theorem self_isSMulRegular_of_ne_zero [IsDomain R] {a : R} (ha : a ≠ 0) :
    IsSMulRegular R a := by
  -- Convert the nonvanishing scalar into a nonzerodivisor, then use flatness of `R` over itself.
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R)
    (mem_nonZeroDivisors_iff_ne_zero.mpr ha)

/-- Helper for Lemma 10.106.3: after importing Lemma 10.106.2 on the canonical associated-graded
API, the head parameter acts regularly on `R` because a regular local ring is a domain. -/
private theorem head_parameter_isSMulRegular {d : ℕ} {x : Fin (d + 1) → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) :
    IsSMulRegular R (((x 0 : maximalIdeal R) : R)) := by
  have ha0 : (((x 0 : maximalIdeal R) : R)) ≠ 0 := head_parameter_ne_zero (R := R) hx
  -- Route correction: after owner unification in the associated-graded API, the source bridge
  -- from Lemma 10.106.2 is available again, so the head nonzero element acts regularly.
  exact self_isSMulRegular_of_ne_zero (R := R) ha0

/-- Helper for Lemma 10.106.3: the parameter ideal of a prefix family is the ideal generated by
the corresponding prefix of the underlying ordered list. -/
private theorem parameterIdeal_prefix_eq_idealOfList_take {d i : ℕ}
    (x : Fin d → maximalIdeal R) (hi : i ≤ d) :
    parameterIdeal (x ∘ Fin.castLE hi) =
      Ideal.ofList ((List.ofFn fun j : Fin d ↦ ((x j : maximalIdeal R) : R)).take i) := by
  -- Rewrite the tuple-based parameter ideal as the list-based ideal on the corresponding prefix.
  calc
    parameterIdeal (x ∘ Fin.castLE hi) =
        Ideal.ofList (List.ofFn fun j : Fin i ↦ (((x ∘ Fin.castLE hi) j : maximalIdeal R) : R)) := by
          symm
          exact parameterIdeal_eq_idealOfList_ofFn (R := R) (x := x ∘ Fin.castLE hi)
    _ = Ideal.ofList ((List.ofFn fun j : Fin d ↦ ((x j : maximalIdeal R) : R)).take i) := by
          congr 1
          simpa [Function.comp] using
            (Fin.ofFn_take_eq_take_ofFn hi (fun j : Fin d ↦ ((x j : maximalIdeal R) : R)))

/-- Helper for Lemma 10.106.3: once the tail is regular on the head quotient, reattaching the
head nonzerodivisor recovers regularity of the full ordered list. -/
private theorem regular_of_head_parameter_and_quotient_tail {d : ℕ}
    {x : Fin (d + 1) → maximalIdeal R}
    (hhead : IsSMulRegular R (((x 0 : maximalIdeal R) : R)))
    (htail :
      IsRegular (QuotSMulTop (((x 0 : maximalIdeal R) : R)) R)
        (List.ofFn fun i : Fin d ↦ (((x i.succ : maximalIdeal R) : R)))) :
    IsRegular R (List.ofFn fun i : Fin (d + 1) ↦ (((x i : maximalIdeal R) : R))) := by
  have hcons :
      IsRegular R
        ((((x 0 : maximalIdeal R) : R) ::
          List.ofFn fun i : Fin d ↦ (((x i.succ : maximalIdeal R) : R)))) := by
    -- Reattach the verified quotient-tail regularity behind the head parameter.
    exact IsRegular.cons hhead htail
  have hlist :
      List.ofFn (fun i : Fin (d + 1) ↦ (((x i : maximalIdeal R) : R))) =
        (((x 0 : maximalIdeal R) : R) ::
          List.ofFn fun i : Fin d ↦ (((x i.succ : maximalIdeal R) : R))) := by
    -- `List.ofFn_cons` identifies the ordered family with its head and successor tail.
    simpa using
      (List.ofFn_cons (((x 0 : maximalIdeal R) : R))
        (fun i : Fin d ↦ (((x i.succ : maximalIdeal R) : R))))
  rwa [hlist]

-- Proof sketch: a regular system of parameters is already the canonical chosen-family owner for a
-- minimal generating family of `maximalIdeal R`. Part (1) is therefore only the derived bridge
-- from that owner to the regularity of the underlying ordered sequence.
/-- Lemma 10.106.3 (1): if `x : Fin d → maximalIdeal R` is a regular system of parameters, then
the underlying list `List.ofFn fun i ↦ (x i : R)` is a regular sequence. -/
theorem IsRegularSystemOfParameters.isRegular {d : ℕ} {x : Fin d → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) :
    IsRegular R (List.ofFn fun i ↦ (x i : R)) := by
  -- Route correction: with Lemma 10.106.2 imported through the unified associated-graded owner,
  -- the source proof is the head-quotient descent rather than a separate ad hoc list induction.
  induction d generalizing R with
  | zero =>
      -- The empty parameter family gives the empty regular sequence.
      simpa using (IsRegular.nil R R)
  | succ d ih =>
      let a : R := ((x 0 : maximalIdeal R) : R)
      let rs : List R := List.ofFn fun i : Fin d ↦ (((x i.succ : maximalIdeal R) : R))
      let S := R ⧸ headParameterIdeal x
      letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr (headParameterIdeal_ne_top x)
      letI : IsLocalRing S :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk (headParameterIdeal x))
          Ideal.Quotient.mk_surjective
      letI : IsRegularLocalRing S :=
        by
          simpa [S, headParameterIdeal] using
            (head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx).1
      have htail_sys : IsRegularSystemOfParameters (head_quotient_tail x) := by
        simpa [S] using head_quotient_tail_isRegularSystemOfParameters (R := R) hx
      have htail_reg :
          IsRegular S
            (List.ofFn fun i : Fin d ↦ (((head_quotient_tail x i : maximalIdeal S) : S))) := by
        simpa [S] using ih (R := S) htail_sys
      have hrs_map :
          List.ofFn (fun i : Fin d ↦ (((head_quotient_tail x i : maximalIdeal S) : S))) =
            rs.map (Ideal.Quotient.mk (headParameterIdeal x)) := by
        -- The quotient-tail family is exactly the mapped successor list.
        simpa [S, rs, head_quotient_tail] using
          (List.ofFn_comp'
            (f := fun i : Fin d ↦ (((x i.succ : maximalIdeal R) : R)))
            (g := Ideal.Quotient.mk (headParameterIdeal x)))
      rw [hrs_map] at htail_reg
      have htail_quot : IsRegular (QuotSMulTop a R) rs := by
        -- Transport tail regularity from the quotient ring back to the quotient module by the head.
        exact
          (isRegular_quotSMulTop_iff_quotient_span_singleton (A := R) (r := a) (rs := rs)).2 <| by
            simpa [S, a, headParameterIdeal] using htail_reg
      have hhead : IsSMulRegular R a := by
        -- Lemma 10.106.2 turns the head nonvanishing statement into the required regular action.
        simpa [a] using head_parameter_isSMulRegular (R := R) hx
      exact regular_of_head_parameter_and_quotient_tail (R := R) (x := x) hhead htail_quot

-- Proof sketch: quotient successively by the initial entries of a regular system of parameters.
-- The quotient owner is stated canonically with the prefix parameter ideal
-- `parameterIdeal (x ∘ Fin.castLE hi)` rather than via an ad hoc list prefix.
/-- Lemma 10.106.3 (2): if `x : Fin d → maximalIdeal R` is a regular system of parameters, then
every quotient by a prefix parameter ideal is again a regular local ring. -/
theorem IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal {d i : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) (hi : i ≤ d) :
    IsRegularLocalRing (R ⧸ parameterIdeal (x ∘ Fin.castLE hi)) := by
  induction i generalizing R d with
  | zero =>
      have hbot : parameterIdeal (x ∘ Fin.castLE hi) = (⊥ : Ideal R) := by
        rw [parameterIdeal_eq_span]
        simp
      -- The empty prefix quotient is just `R` itself.
      rw [hbot]
      exact IsRegularLocalRing.of_ringEquiv (R := R) (RingEquiv.quotientBot R).symm
  | succ i ih =>
      cases d with
      | zero =>
          exact (Nat.not_succ_le_zero i hi).elim
      | succ d =>
          let a : R := ((x 0 : maximalIdeal R) : R)
          let xsTail : List R := List.ofFn fun j : Fin d ↦ ((x j.succ : maximalIdeal R) : R)
          let rs : List R := xsTail.take i
          let S := R ⧸ headParameterIdeal x
          letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr (headParameterIdeal_ne_top x)
          letI : IsLocalRing S :=
            IsLocalRing.of_surjective' (Ideal.Quotient.mk (headParameterIdeal x))
              Ideal.Quotient.mk_surjective
          letI : IsRegularLocalRing S :=
            by
              simpa [S, headParameterIdeal] using
                (head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx).1
          have hi' : i ≤ d := Nat.le_of_succ_le_succ hi
          have htail_sys : IsRegularSystemOfParameters (head_quotient_tail x) := by
            simpa [S] using head_quotient_tail_isRegularSystemOfParameters (R := R) hx
          have htail_regular :
              IsRegularLocalRing
                (S ⧸ parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi')) := by
            -- Recurse on the quotient ring and the tail family.
            exact ih (R := S) (d := d) htail_sys hi'
          have hleft :
              parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi') =
                Ideal.ofList (rs.map (Ideal.Quotient.mk (headParameterIdeal x))) := by
            -- Identify the tail prefix ideal downstairs with the mapped list prefix.
            calc
              parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi') =
                  Ideal.ofList
                    ((List.ofFn
                        fun j : Fin d ↦
                          ((head_quotient_tail x j : maximalIdeal S) : S)).take i) := by
                        simpa [S] using
                          parameterIdeal_prefix_eq_idealOfList_take (R := S)
                            (x := head_quotient_tail x) hi'
              _ =
                  Ideal.ofList
                    (((xsTail.map (Ideal.Quotient.mk (headParameterIdeal x))).take i)) := by
                      congr 1
                      simpa [xsTail] using
                        congrArg (fun l : List S ↦ l.take i)
                          (List.ofFn_comp'
                            (f := fun j : Fin d ↦ ((x j.succ : maximalIdeal R) : R))
                            (g := Ideal.Quotient.mk (headParameterIdeal x)))
              _ = Ideal.ofList (rs.map (Ideal.Quotient.mk (headParameterIdeal x))) := by
                    simp [rs, xsTail, List.map_take]
          have hright :
              parameterIdeal (x ∘ Fin.castLE hi) = Ideal.ofList (a :: rs) := by
            -- The prefix family upstairs is the head element followed by the chosen list prefix.
            calc
              parameterIdeal (x ∘ Fin.castLE hi) =
                  Ideal.ofList
                    ((List.ofFn fun j : Fin (d + 1) ↦ ((x j : maximalIdeal R) : R)).take (i + 1)) := by
                      simpa using parameterIdeal_prefix_eq_idealOfList_take (R := R) x hi
              _ = Ideal.ofList (a :: rs) := by
                    have hlist :
                        List.ofFn (fun j : Fin (d + 1) ↦ ((x j : maximalIdeal R) : R)) =
                          a :: xsTail := by
                      simpa [a, xsTail] using
                        (List.ofFn_cons ((x 0 : maximalIdeal R) : R)
                          (fun j : Fin d ↦ ((x j.succ : maximalIdeal R) : R)))
                    rw [hlist]
                    simp [rs]
          let e₁ :
              (S ⧸ parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi')) ≃+*
                (S ⧸ Ideal.ofList (rs.map (Ideal.Quotient.mk (headParameterIdeal x)))) :=
            Ideal.quotEquivOfEq hleft
          let e₂ :
              (S ⧸ Ideal.ofList (rs.map (Ideal.Quotient.mk (headParameterIdeal x)))) ≃+*
                (R ⧸ Ideal.ofList (a :: rs)) :=
            by
              simpa [S, a, headParameterIdeal] using
                (full_tail_quotient_ringEquiv (A := R) (r := a) (rs := rs))
          let e₃ :
              (R ⧸ Ideal.ofList (a :: rs)) ≃+*
                (R ⧸ parameterIdeal (x ∘ Fin.castLE hi)) :=
            Ideal.quotEquivOfEq hright.symm
          -- Transport regular-locality across the canonical iterated-quotient equivalence.
          exact IsRegularLocalRing.of_ringEquiv (R := S ⧸ parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi'))
            (e₁.trans (e₂.trans e₃))

-- Proof sketch: the owner-level quotient-dimension formula is already available from
-- `ringKrullDim_quotient_parameterIdeal_eq_sub`; the present statement is its additive reformulation
-- specialized to a regular system of parameters.
/-- Lemma 10.106.3 (3): if `x : Fin d → maximalIdeal R` is a regular system of parameters, then
the quotient by its first `i` parameters has Krull dimension `d - i`, written canonically as
`ringKrullDim (R ⧸ parameterIdeal (x ∘ Fin.castLE hi)) + i = ringKrullDim R`. -/
theorem IsRegularSystemOfParameters.ringKrullDim_quotient_parameterIdeal_add_eq {d i : ℕ}
    {x : Fin d → maximalIdeal R} (hx : IsRegularSystemOfParameters x) (hi : i ≤ d) :
    ringKrullDim (R ⧸ parameterIdeal (x ∘ Fin.castLE hi)) + i = ringKrullDim R := by
  induction i generalizing R d with
  | zero =>
      have hbot : parameterIdeal (x ∘ Fin.castLE hi) = (⊥ : Ideal R) := by
        rw [parameterIdeal_eq_span]
        simp
      rw [hbot]
      simpa using ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)
  | succ i ih =>
      cases d with
      | zero =>
          exact (Nat.not_succ_le_zero i hi).elim
      | succ d =>
          let a : R := ((x 0 : maximalIdeal R) : R)
          let xsTail : List R := List.ofFn fun j : Fin d ↦ ((x j.succ : maximalIdeal R) : R)
          let rs : List R := xsTail.take i
          let S := R ⧸ headParameterIdeal x
          letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr (headParameterIdeal_ne_top x)
          letI : IsLocalRing S :=
            IsLocalRing.of_surjective' (Ideal.Quotient.mk (headParameterIdeal x))
              Ideal.Quotient.mk_surjective
          letI : IsRegularLocalRing S :=
            by
              simpa [S, headParameterIdeal] using
                (head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx).1
          have hi' : i ≤ d := Nat.le_of_succ_le_succ hi
          have htail_sys : IsRegularSystemOfParameters (head_quotient_tail x) := by
            simpa [S] using head_quotient_tail_isRegularSystemOfParameters (R := R) hx
          have htail_dim :
              ringKrullDim (S ⧸ parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi')) + i =
                ringKrullDim S := by
            exact ih (R := S) (d := d) htail_sys hi'
          have hleft :
              parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi') =
                Ideal.ofList (rs.map (Ideal.Quotient.mk (headParameterIdeal x))) := by
            calc
              parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi') =
                  Ideal.ofList
                    ((List.ofFn
                        fun j : Fin d ↦
                          ((head_quotient_tail x j : maximalIdeal S) : S)).take i) := by
                        simpa [S] using
                          parameterIdeal_prefix_eq_idealOfList_take (R := S)
                            (x := head_quotient_tail x) hi'
              _ =
                  Ideal.ofList
                    ((xsTail.map (Ideal.Quotient.mk (headParameterIdeal x))).take i) := by
                      congr 1
                      simpa [xsTail] using
                        congrArg (fun l : List S ↦ l.take i)
                          (List.ofFn_comp'
                            (f := fun j : Fin d ↦ ((x j.succ : maximalIdeal R) : R))
                            (g := Ideal.Quotient.mk (headParameterIdeal x)))
              _ = Ideal.ofList (rs.map (Ideal.Quotient.mk (headParameterIdeal x))) := by
                    simp [rs, xsTail, List.map_take]
          have hright :
              parameterIdeal (x ∘ Fin.castLE hi) = Ideal.ofList (a :: rs) := by
            calc
              parameterIdeal (x ∘ Fin.castLE hi) =
                  Ideal.ofList
                    ((List.ofFn fun j : Fin (d + 1) ↦ ((x j : maximalIdeal R) : R)).take (i + 1)) := by
                      simpa using parameterIdeal_prefix_eq_idealOfList_take (R := R) x hi
              _ = Ideal.ofList (a :: rs) := by
                    have hlist :
                        List.ofFn (fun j : Fin (d + 1) ↦ ((x j : maximalIdeal R) : R)) =
                          a :: xsTail := by
                      simpa [a, xsTail] using
                        (List.ofFn_cons ((x 0 : maximalIdeal R) : R)
                          (fun j : Fin d ↦ ((x j.succ : maximalIdeal R) : R)))
                    rw [hlist]
                    simp [rs]
          let e₁ :
              (S ⧸ parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi')) ≃+*
                (S ⧸ Ideal.ofList (rs.map (Ideal.Quotient.mk (headParameterIdeal x)))) :=
            Ideal.quotEquivOfEq hleft
          let e₂ :
              (S ⧸ Ideal.ofList (rs.map (Ideal.Quotient.mk (headParameterIdeal x)))) ≃+*
                (R ⧸ Ideal.ofList (a :: rs)) := by
              simpa [S, a, headParameterIdeal] using
                (full_tail_quotient_ringEquiv (A := R) (r := a) (rs := rs))
          let e₃ :
              (R ⧸ Ideal.ofList (a :: rs)) ≃+*
                (R ⧸ parameterIdeal (x ∘ Fin.castLE hi)) :=
            Ideal.quotEquivOfEq hright.symm
          have hquot_eq :
              ringKrullDim (R ⧸ parameterIdeal (x ∘ Fin.castLE hi)) =
                ringKrullDim (S ⧸ parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi')) := by
            simpa using
              (ringKrullDim_eq_of_ringEquiv (e₁.trans (e₂.trans e₃))).symm
          have hdimS : ringKrullDim S = d :=
            by
              simpa [S, headParameterIdeal] using
                (head_parameter_quotient_regular_local_and_dim (R := R) (x := x) hx).2
          have hdimR : ringKrullDim R = d + 1 :=
            (isRegularSystemOfParameters_iff x).1 hx |>.1
          calc
            ringKrullDim (R ⧸ parameterIdeal (x ∘ Fin.castLE hi)) + (i + 1) =
                ringKrullDim (S ⧸ parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi')) + (i + 1) := by
                  rw [hquot_eq]
            _ = (ringKrullDim (S ⧸ parameterIdeal (head_quotient_tail x ∘ Fin.castLE hi')) + i) + 1 := by
                  simp [add_assoc]
            _ = ringKrullDim S + 1 := by rw [htail_dim]
            _ = ringKrullDim R := by rw [hdimS, hdimR]

-- Proof sketch: unpack the extension witness in
-- `IsPartOfRegularSystemOfParameters`, apply the full regular-system theorem to the appended
-- family, and identify the prefix parameter ideal with `parameterIdeal x`.
/-- If `x` is part of a regular system of parameters, then quotienting by the ideal generated by
`x` yields a regular local ring. This is the owner-level derived view on
`IsPartOfRegularSystemOfParameters`; no extra wrapper around the prefix family is needed. -/
theorem IsPartOfRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal
    {d c : ℕ} {x : Fin c → maximalIdeal R} (hx : IsPartOfRegularSystemOfParameters d x) :
    IsRegularLocalRing (R ⧸ parameterIdeal x) := by
  rcases hx with ⟨y, hy⟩
  let hprefix : c ≤ c + (d - c) := Nat.le_add_right c (d - c)
  have hregular :
      IsRegularLocalRing
        (R ⧸ parameterIdeal (Fin.append x y ∘ Fin.castLE hprefix)) :=
    IsRegularSystemOfParameters.isRegularLocalRing_quotient_parameterIdeal (R := R) hy hprefix
  have hparam :
      parameterIdeal (Fin.append x y ∘ Fin.castLE hprefix) = parameterIdeal x := by
    -- The first `c` entries of the appended family are exactly `x`.
    exact congrArg parameterIdeal <| by
      funext i
      simp [Function.comp]
  rw [hparam] at hregular
  exact hregular

-- Proof sketch: unpack the extension witness in
-- `IsPartOfRegularSystemOfParameters`, use regularity of the full appended regular system of
-- parameters, and pass to the initial segment corresponding to `x`.
/-- If `x` is part of a regular system of parameters, then its underlying list is a regular
sequence. This is the canonical list-level bridge derived from the owner
`IsPartOfRegularSystemOfParameters`. -/
theorem IsPartOfRegularSystemOfParameters.isRegular
    {d c : ℕ} {x : Fin c → maximalIdeal R} (hx : IsPartOfRegularSystemOfParameters d x) :
    IsRegular R (List.ofFn fun i ↦ (x i : R)) := by
  rcases hx with ⟨y, hy⟩
  have hfull :
      IsRegular R
        (List.ofFn fun i : Fin (c + (d - c)) ↦ (((Fin.append x y i : maximalIdeal R) : R))) := by
    -- Apply the main theorem to the completed regular system of parameters.
    exact IsRegularSystemOfParameters.isRegular (R := R) hy
  have happ :
      List.ofFn (fun i : Fin (c + (d - c)) ↦ (((Fin.append x y i : maximalIdeal R) : R))) =
        List.ofFn (fun i : Fin c ↦ ((x i : maximalIdeal R) : R)) ++
          List.ofFn (fun i : Fin (d - c) ↦ ((y i : maximalIdeal R) : R)) := by
    -- `List.ofFn_fin_append` identifies the full list with its left prefix plus right tail.
    have happend :
        (fun i : Fin (c + (d - c)) ↦ (((Fin.append x y i : maximalIdeal R) : R))) =
          Fin.append
            (fun i : Fin c ↦ ((x i : maximalIdeal R) : R))
            (fun i : Fin (d - c) ↦ ((y i : maximalIdeal R) : R)) := by
      refine funext (Fin.addCases (fun i ↦ ?_) fun i ↦ ?_)
      · simp [Fin.append, Fin.addCases_left]
      · simp [Fin.append, Fin.addCases_right]
    rw [happend]
    exact
      List.ofFn_fin_append
        (fun i : Fin c ↦ ((x i : maximalIdeal R) : R))
        (fun i : Fin (d - c) ↦ ((y i : maximalIdeal R) : R))
  rw [happ] at hfull
  -- The left prefix of a regular appended sequence is regular.
  simpa using isRegular_left_of_isRegular_append (M := R) hfull

end IsLocalRing

/-- Helper for Lemma 10.106.3: in a Noetherian local ring, a regular sequence whose length already
equals the Krull dimension makes the self-module Cohen--Macaulay. -/
private theorem cohenMacaulay_self_of_isRegular_of_length_eq_ringKrullDim
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S] {xs : List S}
    (hreg : IsRegular S xs) (hlen : xs.length = ringKrullDim S) :
    Module.CohenMacaulay S S := by
  have hSdim : Module.supportDim S S = xs.length := by
    rw [Module.supportDim_self_eq_ringKrullDim, ← hlen]
  -- Extend the regular sequence up to the module depth and show that no further tail can remain.
  obtain ⟨xs', hreg', hdepth⟩ := IsRegular.exists_append_eq_moduleDepth hreg
  letI : Nontrivial S := hreg.nontrivial
  have hIneTop : Ideal.ofList (xs ++ xs') • (⊤ : Submodule S S) ≠ ⊤ := by
    simpa [ne_comm] using hreg'.top_ne_smul
  letI : Nontrivial (S ⧸ (Ideal.ofList (xs ++ xs') • (⊤ : Submodule S S))) :=
    Submodule.Quotient.nontrivial_iff.2 hIneTop
  have hquot_nonbot :
      Module.supportDim S (S ⧸ (Ideal.ofList (xs ++ xs') • (⊤ : Submodule S S))) ≠ ⊥ :=
    Module.supportDim_ne_bot_of_nontrivial S _
  have hlen_le :
      (((xs ++ xs').length : ℕ∞) : WithBot ℕ∞) ≤ Module.supportDim S S := by
    -- The quotient support dimension is nonnegative, so the regular sequence cannot be extended.
    rw [← Module.supportDim_add_length_eq_supportDim_of_isRegular (M := S) (rs := xs ++ xs') hreg']
    simpa [add_comm] using
      WithBot.le_add_self hquot_nonbot ((((xs ++ xs').length : ℕ∞) : WithBot ℕ∞))
  have htail_len : xs'.length = 0 := by
    have hsum_le :
        (((xs.length + xs'.length : ℕ) : ℕ∞) : WithBot ℕ∞) ≤
          (((xs.length : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa [hSdim, List.length_append] using hlen_le
    have hsum_le_nat : xs.length + xs'.length ≤ xs.length := by
      exact_mod_cast hsum_le
    omega
  have htail : xs' = [] := List.length_eq_zero_iff.mp htail_len
  -- With no tail left, the support-dimension equality is exactly the Cohen--Macaulay condition.
  refine Module.CohenMacaulay.mk ?_
  rw [hdepth, htail]
  simpa using hSdim

-- Proof sketch: choose a regular system of parameters for `R`, apply the regularity and prefix
-- quotient statements above, and conclude by the depth-equals-dimension owner criterion for the
-- self-module `R`.
/-- Lemma 10.106.3 (4): a regular local ring is Cohen-Macaulay when viewed as a module over
itself. -/
instance regularLocalRing_selfModule_cohenMacaulay : Module.CohenMacaulay R R := by
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hdim : ringKrullDim R = d := by
    simpa [d] using
      ((isRegularLocalRing_iff (R := R)).1 (inferInstance : IsRegularLocalRing R)).symm
  obtain ⟨x, hx⟩ :=
    (isRegularLocalRing_iff_exists_regularSystemOfParameters (R := R) (d := d) hdim).1
      (inferInstance : IsRegularLocalRing R)
  let xs : List R := List.ofFn fun i ↦ (x i : R)
  have hreg : IsRegular R xs := by
    -- The chosen regular system of parameters gives the source regular sequence.
    simpa [xs] using IsLocalRing.IsRegularSystemOfParameters.isRegular (R := R) hx
  have hlen : (xs.length : WithBot ℕ∞) = ringKrullDim R := by
    -- Its length is the Krull dimension because the system is indexed by `Fin d`.
    calc
      (xs.length : WithBot ℕ∞) = d := by simp [xs]
      _ = ringKrullDim R := by simpa using hdim.symm
  -- A full-length regular sequence on the self-module is the Cohen--Macaulay criterion.
  exact cohenMacaulay_self_of_isRegular_of_length_eq_ringKrullDim hreg hlen

/-- A regular ring is Cohen-Macaulay. -/
instance regularRing_cohenMacaulayRing {S : Type*} [CommRing S] [IsRegularRing S] :
    CohenMacaulayRing S where
  toIsNoetherian := inferInstance
  toLocallyCohenMacaulay := by
    refine
      { toFinite := inferInstance
        localizedModule_cohenMacaulay := ?_ }
    intro p
    -- Route correction: keep the `CohenMacaulayRing` owner file free of later regular-ring
    -- imports, and recover the global bridge here from the regular-local localization theorem.
    let _ : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
      IsRegularRing.isRegularLocalRing_atPrime p
    infer_instance

end
