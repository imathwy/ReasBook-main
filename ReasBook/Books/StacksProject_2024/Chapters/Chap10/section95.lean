import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_95_1 (from Chap10) -/
open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

/- Source/core/bridge triage:
* source-facing: descent of the Mittag-Leffler property along a faithfully flat base change;
* core/canonical owner: `Module.MittagLeffler`, sampled via
  `mittagLeffler_iff_tensorProduct_piRight_injective`,
  `TensorProduct.piRightHom`, and `Module.FaithfullyFlat.lTensor_injective_iff_injective`;
* adjacent bridge theorem checked and rejected as the main owner reuse:
  `Module.mittagLeffler_restrictScalars_of_mittagLeffler_of_flat` from Lemma `10.89.11`, whose
  extra hypotheses `[MittagLeffler R S] [Module.Flat S M]` change the semantics of the present
  faithfully flat descent statement;
* bridge/view: compare the tensor-product-with-products map over `R` with its base change to `S`
  and reflect injectivity along the faithfully flat extension.
-/
-- Proof sketch: use the canonical injectivity criterion for `Module.MittagLeffler` from
-- Proposition `10.89.5`. For each family `(Q a)` of `R`-modules, reflect injectivity of
-- `TensorProduct.piRightHom R R M Q` from its left tensor with `S` via
-- `Module.FaithfullyFlat.lTensor_injective_iff_injective`; after the standard tensor-associativity
-- and product-compatibility identifications, the resulting map is exactly the `S`-linear
-- `TensorProduct.piRightHom` for `S ⊗[R] M`, which is injective by the assumed
-- `Module.MittagLeffler S (S ⊗[R] M)`.
/-- Lemma 10.95.1: if the faithfully flat base change `S ⊗[R] M` is a Mittag-Leffler `S`-module,
then `M` is a Mittag-Leffler `R`-module. -/
theorem mittagLeffler_of_mittagLeffler_tensorProduct_of_faithfullyFlat
    [MittagLeffler S (S ⊗[R] M)] :
    MittagLeffler R M := by
  sorry

end

end Module

/-! ### Lemma_10_95_2 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

namespace Module

omit [Module.FaithfullyFlat R S] in
/-- Helper for Lemma 10.95.2: a finite sum of pure tensors whose module factors lie in a set `u`
belongs to the base change of the span of `u`. -/
lemma sum_tmul_mem_baseChange_span_of_range_subset
    {u : Set M} {k : ℕ} (a : Fin k → S) (m : Fin k → M) (hm : ∀ j, m j ∈ u) :
    (∑ j, a j ⊗ₜ[R] m j) ∈ (Submodule.span R u).baseChange S := by
  -- Each pure tensor lands in the base change because its module factor lies in the chosen span.
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  exact Submodule.tmul_mem_baseChange_of_mem (a j) (Submodule.subset_span (hm j))

omit [Module.FaithfullyFlat R S] in
/-- Helper for Lemma 10.95.2: if the base change of a submodule is all of `S ⊗[R] M`, then the
tensor product of the inclusion map is surjective. -/
lemma subtype_lTensor_surjective_of_baseChange_eq_top
    (P : Submodule R M) (hP : P.baseChange S = ⊤) :
    Function.Surjective (P.subtype.lTensor S) := by
  have hP_range : LinearMap.range (P.subtype.baseChange S) = ⊤ := by
    -- The definition of `baseChange` is the range of the tensorized inclusion.
    simpa [Submodule.baseChange] using hP
  have hsurj_baseChange : Function.Surjective (P.subtype.baseChange S) := by
    -- A linear map is surjective precisely when its range is `⊤`.
    rw [← LinearMap.range_eq_top]
    exact hP_range
  -- The tensorized inclusion is definitionally the base-changed inclusion.
  simpa [LinearMap.baseChange_eq_ltensor] using hsurj_baseChange

/-- Helper for Lemma 10.95.2: faithful flatness reflects the fact that a submodule with full base
change is already the whole module. -/
lemma submodule_eq_top_of_baseChange_eq_top
    (P : Submodule R M) (hP : P.baseChange S = ⊤) :
    P = ⊤ := by
  have hsurjTensor : Function.Surjective (P.subtype.lTensor S) :=
    subtype_lTensor_surjective_of_baseChange_eq_top (R := R) (S := S) P hP
  have hsurj : Function.Surjective P.subtype := by
    simpa using
      (Module.FaithfullyFlat.lTensor_surjective_iff_surjective
        (R := R) (M := S) (f := P.subtype)).mp hsurjTensor
  -- Surjectivity of the subtype map says that every element of `M` already lies in `P`.
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨y, rfl⟩ := hsurj x
  exact y.2

/-- Lemma 10.95.2: if the faithfully flat base change `S ⊗[R] M` is spanned over `S` by a
countable subset, then `M` is spanned over `R` by a countable subset. This is the canonical Lean
form of the textbook statement that countable generation descends from `M ⊗_R S`. -/
theorem countablyGenerated_of_countablyGenerated_tensorProduct_of_faithfullyFlat
    (h : CountablyGenerated S (S ⊗[R] M)) :
    CountablyGenerated R M := by
  classical
  rw [Module.countablyGenerated_iff] at h ⊢
  rcases h with ⟨s, hs, hspan⟩
  have hdecomp (x : s) : ∃ k : ℕ, ∃ a : Fin k → S, ∃ m : Fin k → M,
      x.1 = ∑ j, a j ⊗ₜ[R] m j := by
    -- Decompose each chosen tensor generator into a finite sum of pure tensors.
    simpa using TensorProduct.exists_sum_tmul_eq x.1
  choose k a m hm using hdecomp
  let u : Set M := ⋃ x : s, Set.range (m x)
  let P : Submodule R M := Submodule.span R u
  have hu : u.Countable := by
    -- The module factors form a countable union of finite ranges indexed by the countable set `s`.
    letI : Countable s := hs.to_subtype
    simpa [u] using Set.countable_iUnion (fun x : s ↦ Set.countable_range (m x))
  have hs_subset : s ⊆ P.baseChange S := by
    intro y hy
    let x : s := ⟨y, hy⟩
    have hm_mem : ∀ j, m x j ∈ u := by
      intro j
      exact Set.mem_iUnion.2 ⟨x, Set.mem_range_self j⟩
    have hx_mem : (∑ j, a x j ⊗ₜ[R] m x j) ∈ P.baseChange S := by
      -- Every summand belongs to the base change of `P`, so the whole finite sum does as well.
      simpa [P] using
        sum_tmul_mem_baseChange_span_of_range_subset
          (R := R) (S := S) (u := u) (a := a x) (m := m x) hm_mem
    have hx' : x.1 ∈ P.baseChange S := by
      -- Rewrite the chosen tensor decomposition back to the original generator.
      rw [hm x]
      exact hx_mem
    -- Replacing the generator by its chosen tensor decomposition puts it into `P.baseChange S`.
    simpa [x] using hx'
  have hP : P.baseChange S = ⊤ := by
    -- Since `s` spans the tensor product and every generator lies in `P.baseChange S`,
    -- the base-changed submodule is the whole tensor product.
    apply eq_top_iff.mpr
    rw [← hspan]
    exact Submodule.span_le.2 hs_subset
  refine ⟨u, hu, ?_⟩
  -- Faithful flatness descends the equality `P.baseChange S = ⊤` back to `P = ⊤`.
  simpa [P] using
    submodule_eq_top_of_baseChange_eq_top (R := R) (S := S) (M := M) P hP

end Module

end

/-! ### Lemma_10_95_3 (from Chap10) -/
open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

/- Source/core/bridge triage:
* source-facing: descent of the countably generated projective condition along a faithfully flat
  base change;
* core/canonical owners: the chapter owner `Module.CountablyGenerated` from
  `Definition_10_84_1` and the owner predicate `Module.Projective`;
* sampled upstream declarations in this domain:
  `Module.countablyGenerated_iff`,
  `Module.countablyGenerated_of_countablyGenerated_tensorProduct_of_faithfullyFlat`,
  `Module.projective_iff_flat_mittagLeffler_and_isDirectSumOfCountablyGenerated`;
* bridge/view: the theorem below packages the source statement in terms of these owner
  predicates, so no local duplicate owner for countable generation is needed here.
-/

-- Proof sketch: descend countable generation by Lemma `10.95.2`; for projectivity, use Theorem
-- `10.93.3` on the base-changed module, descend flatness and the Mittag-Leffler property by
-- faithful flatness, and use the countably generated hypothesis to obtain the required
-- countably-generated direct-sum decomposition on the `R`-side.
/-- Lemma 10.95.3: if the faithfully flat base change `S ⊗[R] M` is countably generated and
projective over `S`, then `M` is countably generated and projective over `R`. This is the
canonical Lean form of the textbook statement for `M ⊗_R S`. -/
theorem countablyGenerated_projective_of_countablyGenerated_projective_tensorProduct_of_faithfullyFlat
    [Module.Projective S (S ⊗[R] M)] (hcg : Module.CountablyGenerated S (S ⊗[R] M)) :
    Module.CountablyGenerated R M ∧ Module.Projective R M := sorry

end

end Module

/-! ### Lemma_10_95_4 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance high] Algebra.TensorProduct.leftAlgebra Algebra.toModule

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.95.4: base change is monotone with respect to inclusion of
`R`-submodules. -/
lemma baseChange_mono {P P' : Submodule R M} (h : P ≤ P') :
    P.baseChange S ≤ P'.baseChange S := by
  -- Rewrite both base changes as spans of pure tensors so monotonicity reduces to `span_mono`.
  rw [Submodule.baseChange_eq_span (A := S), Submodule.baseChange_eq_span (A := S)]
  refine Submodule.span_mono ?_
  intro z hz
  rcases hz with ⟨m, hm, rfl⟩
  exact ⟨m, h hm, rfl⟩

/-- Helper for Lemma 10.95.4: every tensor lies in the base change of the span of finitely many
module elements. -/
lemma exists_finset_span_mem_baseChange (y : S ⊗[R] M) :
    ∃ s : Finset M, y ∈ (Submodule.span R (s : Set M)).baseChange S := by
  classical
  -- Expand the tensor as a finite sum of pure tensors and keep only the module components.
  obtain ⟨t, ht⟩ := TensorProduct.exists_finset (R := R) y
  refine ⟨t.image Prod.snd, ?_⟩
  rw [ht]
  refine Submodule.sum_mem _ ?_
  intro p hp
  have hp_mem : p.2 ∈ Submodule.span R (t.image Prod.snd : Set M) := by
    apply Submodule.subset_span
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem Prod.snd hp)
  exact Submodule.tmul_mem_baseChange_of_mem (R := R) (A := S) p.1 hp_mem

/-- Helper for Lemma 10.95.4: the span of a countable subset is countably generated. -/
lemma countablyGenerated_span_of_countable {s : Set M} (hs : s.Countable) :
    (Submodule.span R s).CountablyGenerated := by
  -- This is exactly the defining formulation of countable generation for submodules.
  rw [Submodule.countablyGenerated_iff]
  exact ⟨s, hs, rfl⟩

-- Proof sketch: choose countably many generators for `Q`, write each generator as a finite sum of
-- pure tensors, and let `P` be the submodule spanned by all module components appearing in those
-- sums. This spanning set is still countable, and every generator of `Q` lies in `P.baseChange S`,
-- hence the whole submodule `Q` is contained in `P.baseChange S`.
/-- Lemma 10.95.4: every countably generated `S`-submodule `Q` of the scalar extension
`S ⊗[R] M` is contained in the base change of a countably generated `R`-submodule `P ≤ M`. This
is the canonical Lean form of saying that the image of `P ⊗_R S → M ⊗_R S` contains `Q`. -/
theorem exists_countablyGenerated_submodule_whose_baseChange_contains
    {Q : Submodule S (S ⊗[R] M)}
    (hQ : Q.CountablyGenerated) :
    ∃ P : Submodule R M, P.CountablyGenerated ∧ Q ≤ P.baseChange S := by
  classical
  rcases (Submodule.countablyGenerated_iff.mp hQ) with ⟨t, ht_countable, ht_span⟩
  let support : S ⊗[R] M → Finset M := fun y ↦
    Classical.choose (exists_finset_span_mem_baseChange (R := R) (S := S) (M := M) y)
  have support_mem :
      ∀ y : S ⊗[R] M, y ∈ (Submodule.span R (support y : Set M)).baseChange S := by
    -- Each chosen support was defined precisely so that it spans a base change containing `y`.
    intro y
    exact Classical.choose_spec
      (exists_finset_span_mem_baseChange (R := R) (S := S) (M := M) y)
  let U : Set M := ⋃ y : t, (support y : Set M)
  let P : Submodule R M := Submodule.span R U
  have hU_countable : U.Countable := by
    -- A countable family of finite supports still has countable union.
    letI : Countable t := ht_countable.to_subtype
    simpa [U] using Set.countable_iUnion (fun y : t ↦ Finset.countable_toSet (support y))
  have hPcg : P.CountablyGenerated := by
    -- The final submodule is spanned by the countable union of all chosen supports.
    exact countablyGenerated_span_of_countable (R := R) (hs := hU_countable)
  have hQle : Q ≤ P.baseChange S := by
    -- It suffices to check the chosen generators of `Q`.
    rw [← ht_span]
    refine Submodule.span_le.2 ?_
    intro y hy
    let y' : t := ⟨y, hy⟩
    have hspan_le : Submodule.span R (support y' : Set M) ≤ P := by
      -- The support of a chosen generator is part of the union used to define `P`.
      refine Submodule.span_mono ?_
      intro m hm
      exact Set.mem_iUnion.2 ⟨y', hm⟩
    have hy_mem : y ∈ (Submodule.span R (support y' : Set M)).baseChange S := by
      -- Reuse the finite-support containment for this specific generator.
      simpa using support_mem y
    exact baseChange_mono (R := R) (S := S) (M := M) hspan_le hy_mem
  exact ⟨P, hPcg, hQle⟩

end

/-! ### Lemma_10_95_5 (from Chap10) -/
open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance high] Algebra.TensorProduct.leftAlgebra Algebra.toModule

universe u v w x

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {I : Type x}

/-- Helper for Lemma 10.95.5: base change of a countably generated submodule is countably
generated. -/
lemma countablyGenerated_baseChange {P : Submodule R M}
    (hP : P.CountablyGenerated) :
    (P.baseChange S).CountablyGenerated := by
  rcases (Submodule.countablyGenerated_iff (P := P)).mp hP with ⟨s, hs, hspan⟩
  -- Rewrite the base change of a span as the span of the pure tensors `1 ⊗ m`.
  refine (Submodule.countablyGenerated_iff (P := P.baseChange S)).2 ?_
  refine ⟨((TensorProduct.mk R S M) 1) '' s, hs.image _, ?_⟩
  rw [← hspan, Submodule.baseChange_span]

/-- Helper for Lemma 10.95.5: a countable supremum of countably generated submodules is still
countably generated. -/
lemma countablyGenerated_iSup_of_countable {α : Sort*} [Countable α]
    (A : α → Submodule R M) (hA : ∀ a, (A a).CountablyGenerated) :
    (⨆ a, A a).CountablyGenerated := by
  let spanning : α → Set M := fun a ↦
    Classical.choose ((Submodule.countablyGenerated_iff (P := A a)).mp (hA a))
  have hspanning_countable : ∀ a, (spanning a).Countable := by
    intro a
    exact (Classical.choose_spec ((Submodule.countablyGenerated_iff (P := A a)).mp (hA a))).1
  have hspanning_eq : ∀ a, Submodule.span R (spanning a) = A a := by
    intro a
    exact (Classical.choose_spec ((Submodule.countablyGenerated_iff (P := A a)).mp (hA a))).2
  let U : Set M := ⋃ a, spanning a
  have hU_countable : U.Countable := by
    -- A countable union of countable spanning sets stays countable.
    simpa [U] using Set.countable_iUnion hspanning_countable
  -- The supremum is the span of the union of all chosen spanning sets.
  refine (Submodule.countablyGenerated_iff (P := ⨆ a, A a)).2 ⟨U, hU_countable, ?_⟩
  calc
    Submodule.span R U = ⨆ a, Submodule.span R (spanning a) := by
      simpa [U] using (Submodule.span_iUnion (R := R) (s := spanning))
    _ = ⨆ a, A a := by
      simp [hspanning_eq]

/-- Helper for Lemma 10.95.5: the supremum of two countably generated submodules is countably
generated. -/
lemma countablyGenerated_sup {P P' : Submodule R M}
    (hP : P.CountablyGenerated) (hP' : P'.CountablyGenerated) :
    (P ⊔ P').CountablyGenerated := by
  rcases (Submodule.countablyGenerated_iff (P := P)).mp hP with ⟨s, hs, hspan⟩
  rcases (Submodule.countablyGenerated_iff (P := P')).mp hP' with ⟨t, ht, htspan⟩
  -- A union of two countable spanning sets spans the supremum.
  refine (Submodule.countablyGenerated_iff (P := P ⊔ P')).2 ?_
  refine ⟨s ∪ t, hs.union ht, ?_⟩
  calc
    Submodule.span R (s ∪ t) = Submodule.span R s ⊔ Submodule.span R t := by
      rw [Submodule.span_union]
    _ = P ⊔ P' := by
      rw [hspan, htspan]

/-- Helper for Lemma 10.95.5: a countably generated submodule of the internal direct sum is
contained in the sum of a countable subfamily of summands. -/
lemma exists_countable_subfamily_le_of_countablyGenerated
    (Q : I → Submodule S (S ⊗[R] M))
    (hQindep : iSupIndep Q)
    (hQtop : iSup Q = ⊤)
    {P : Submodule S (S ⊗[R] M)}
    (hP : P.CountablyGenerated) :
    ∃ J : Set I, J.Countable ∧ P ≤ ⨆ i : J, Q i.1 := by
  classical
  let hInternal : DirectSum.IsInternal Q :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hQindep hQtop
  let _ : DirectSum.Decomposition Q :=
    DirectSum.IsInternal.chooseDecomposition (ℳ := Q) hInternal
  rcases (Submodule.countablyGenerated_iff (P := P)).mp hP with ⟨t, ht, hspan⟩
  let support : t → Finset I := fun y ↦ (DirectSum.decompose Q y.1).support
  let J : Set I := ⋃ y : t, (support y : Set I)
  have hJ : J.Countable := by
    -- Countably many finite supports still give a countable union of indices.
    let _ : Countable t := ht.to_subtype
    simpa [J, support] using Set.countable_iUnion (fun y : t ↦ Finset.countable_toSet (support y))
  refine ⟨J, hJ, ?_⟩
  rw [← hspan]
  refine Submodule.span_le.2 ?_
  intro y hy
  let y' : t := ⟨y, hy⟩
  -- Expand a generator into finitely many direct-sum components, all indexed inside `J`.
  rw [← DirectSum.sum_support_decompose Q y]
  refine Submodule.sum_mem _ ?_
  intro i hi
  have hiJ : i ∈ J := by
    exact Set.mem_iUnion.2 ⟨y', hi⟩
  exact Submodule.mem_iSup_of_mem ⟨i, hiJ⟩ (DirectSum.decompose Q y i).2

-- Proof sketch: start with `N'_0 = N` and inductively enlarge to countably generated submodules
-- `N'_ℓ` so that each next base change contains every summand `Q i` that meets the current image.
-- Apply Lemma `10.95.4` to the countable sum of those summands at each step, then take the union
-- over the countable iteration to obtain `N'` and the corresponding subset `I'`.
/-- Lemma 10.95.5: if `S ⊗[R] M` is the sum of an independent family of countably generated
`S`-submodules `Q i`, equivalently an internal direct-sum decomposition by countably generated
summands, then every countably generated `R`-submodule `N` of `M` is contained in a countably
generated `R`-submodule whose base change is the sum of a subfamily of the `Q i`. This is the
canonical Lean form of the statement that the image of `N' ⊗_R S → M ⊗_R S` is `⨁_{i ∈ I'} Q i`.
-/
theorem exists_countablyGenerated_supermodule_with_baseChange_eq_iSup_subfamily
    (Q : I → Submodule S (S ⊗[R] M))
    (hQindep : iSupIndep Q)
    (hQtop : iSup Q = ⊤)
    (hQcg : ∀ i, (Q i).CountablyGenerated)
    {N : Submodule R M}
    (hN : N.CountablyGenerated) :
    ∃ (N' : Submodule R M) (_ : N ≤ N') (_ : N'.CountablyGenerated) (I' : Set I),
      N'.baseChange S = ⨆ i : I', Q i.1 := by
  classical
  let Stage := { P : Submodule R M // P.CountablyGenerated }
  have hsucc :
      ∀ A : Stage, ∃ B : Stage, A.1 ≤ B.1 ∧
        ∃ J : Set I, J.Countable ∧
          A.1.baseChange S ≤ ⨆ i : J, Q i.1 ∧
          (⨆ i : J, Q i.1) ≤ B.1.baseChange S := by
    intro A
    rcases exists_countable_subfamily_le_of_countablyGenerated
        (Q := Q) hQindep hQtop
        (P := A.1.baseChange S)
        (countablyGenerated_baseChange (R := R) (S := S) (M := M) A.2) with
      ⟨J, hJ, hAJ⟩
    let _ : Countable J := hJ.to_subtype
    have hQJcg : (⨆ i : J, Q i.1).CountablyGenerated := by
      -- The chosen subfamily is countably generated because both the index set and summands are.
      exact countablyGenerated_iSup_of_countable
        (R := S) (M := S ⊗[R] M) (A := fun i : J ↦ Q i.1) (fun i ↦ hQcg i.1)
    rcases exists_countablyGenerated_submodule_whose_baseChange_contains
        (R := R) (S := S) (M := M) (Q := ⨆ i : J, Q i.1) hQJcg with
      ⟨P, hPcg, hJP⟩
    refine ⟨⟨A.1 ⊔ P, countablyGenerated_sup (R := R) (M := M) A.2 hPcg⟩, le_sup_left, ?_⟩
    -- Enlarge by `P` so the next stage base change contains the whole touched subfamily.
    refine ⟨J, hJ, hAJ, ?_⟩
    exact hJP.trans (baseChange_mono (R := R) (S := S) (M := M) le_sup_right)
  let next : Stage → Stage := fun A ↦ Classical.choose (hsucc A)
  have hnext_le : ∀ A : Stage, A.1 ≤ (next A).1 := by
    intro A
    exact (Classical.choose_spec (hsucc A)).1
  have hnext_data :
      ∀ A : Stage,
        ∃ J : Set I, J.Countable ∧
          A.1.baseChange S ≤ ⨆ i : J, Q i.1 ∧
          (⨆ i : J, Q i.1) ≤ (next A).1.baseChange S := by
    intro A
    exact (Classical.choose_spec (hsucc A)).2
  let Jnext : Stage → Set I := fun A ↦ Classical.choose (hnext_data A)
  have hJnext_countable : ∀ A : Stage, (Jnext A).Countable := by
    intro A
    exact (Classical.choose_spec (hnext_data A)).1
  have hJnext_base_le :
      ∀ A : Stage, A.1.baseChange S ≤ ⨆ i : Jnext A, Q i.1 := by
    intro A
    exact (Classical.choose_spec (hnext_data A)).2.1
  have hJnext_fill :
      ∀ A : Stage, (⨆ i : Jnext A, Q i.1) ≤ (next A).1.baseChange S := by
    intro A
    exact (Classical.choose_spec (hnext_data A)).2.2
  let NSeq : ℕ → Stage := Nat.rec ⟨N, hN⟩ fun _ A ↦ next A
  let NSub : ℕ → Submodule R M := fun n ↦ (NSeq n).1
  let JSeq : ℕ → Set I := fun n ↦ Jnext (NSeq n)
  have hNSub_cg : ∀ n, (NSub n).CountablyGenerated := by
    intro n
    exact (NSeq n).2
  have hNSub_succ : ∀ n, NSub n ≤ NSub (n + 1) := by
    intro n
    simpa [NSub, NSeq] using hnext_le (NSeq n)
  have hNSub_mono : Monotone NSub := monotone_nat_of_le_succ hNSub_succ
  have hstage_base_le : ∀ n, (NSub n).baseChange S ≤ ⨆ i : JSeq n, Q i.1 := by
    intro n
    simpa [NSub, JSeq] using hJnext_base_le (NSeq n)
  have hstage_fill : ∀ n, (⨆ i : JSeq n, Q i.1) ≤ (NSub (n + 1)).baseChange S := by
    intro n
    simpa [NSub, JSeq, NSeq] using hJnext_fill (NSeq n)
  let NChain : ℕ →o Submodule R M :=
    { toFun := NSub
      monotone' := hNSub_mono }
  let N' : Submodule R M := ⨆ n, NSub n
  let I' : Set I := ⋃ n, JSeq n
  have hN_le : N ≤ N' := by
    -- The initial submodule is the zeroth stage of the recursive construction.
    simpa [N', NSub, NSeq] using (le_iSup NSub 0)
  have hN'cg : N'.CountablyGenerated := by
    -- Countable generation survives the countable union of the increasing stages.
    exact countablyGenerated_iSup_of_countable (R := R) (M := M) NSub hNSub_cg
  have hbase_le : N'.baseChange S ≤ ⨆ i : I', Q i.1 := by
    rw [Submodule.baseChange_eq_span (A := S)]
    refine Submodule.span_le.2 ?_
    intro z hz
    rcases hz with ⟨m, hm, rfl⟩
    have hm_stage : ∃ n, m ∈ NSub n := by
      simpa [N', NChain] using (Submodule.mem_iSup_of_chain NChain m).mp hm
    rcases hm_stage with ⟨n, hmN⟩
    have hmem_stage : (1 : S) ⊗ₜ[R] m ∈ (NSub n).baseChange S := by
      exact Submodule.tmul_mem_baseChange_of_mem (R := R) (A := S) (1 : S) hmN
    have hmem_subfamily : (1 : S) ⊗ₜ[R] m ∈ ⨆ i : JSeq n, Q i.1 := by
      exact hstage_base_le n hmem_stage
    have hsubfamily_le : (⨆ i : JSeq n, Q i.1) ≤ ⨆ i : I', Q i.1 := by
      refine iSup_le fun i ↦ ?_
      exact le_iSup_of_le ⟨i.1, Set.mem_iUnion.2 ⟨n, i.2⟩⟩ le_rfl
    exact hsubfamily_le hmem_subfamily
  have hbase_ge : (⨆ i : I', Q i.1) ≤ N'.baseChange S := by
    refine iSup_le ?_
    intro i
    rcases Set.mem_iUnion.1 i.2 with ⟨n, hin⟩
    have hi_subfamily : Q i.1 ≤ ⨆ j : JSeq n, Q j.1 := by
      exact le_iSup_of_le ⟨i.1, hin⟩ le_rfl
    have hi_stage : Q i.1 ≤ (NSub (n + 1)).baseChange S := by
      exact hi_subfamily.trans (hstage_fill n)
    have hstage_to_limit : (NSub (n + 1)).baseChange S ≤ N'.baseChange S := by
      exact baseChange_mono (R := R) (S := S) (M := M) (le_iSup NSub (n + 1))
    exact hi_stage.trans hstage_to_limit
  refine ⟨N', hN_le, hN'cg, I', ?_⟩
  -- The recursive closure is exactly the sum of the accumulated touched summands.
  exact le_antisymm hbase_le hbase_ge

end

/-! ### Theorem_10_95_6 (from Chap10) -/
open scoped TensorProduct

universe u v w

namespace Module.Projective

section

variable {R : Type u} [CommRing R]
variable {M : Type w} [AddCommGroup M] [Module R M]

/- Domain triage:
- primary domain: faithfully flat descent for projective modules over commutative rings;
- sampled owner declarations of the same kind:
  `Module.Projective`,
  `Module.countablyGenerated_projective_of_countablyGenerated_projective_tensorProduct_of_faithfullyFlat`,
  `projective_isDirectSumOfCountablyGeneratedProjective`,
  and the direct-sum owner instance `Module.Projective R (Π₀ i, A i)`;
- best owner abstraction: the owner predicate `Module.Projective R M`;
- primitive data: the faithfully flat `R`-algebra `S`, the `R`-module `M`, and the projective
  base change `S ⊗[R] M`;
- derived API: descent of the owner predicate `Module.Projective` from the base-changed module
  back to `M`.

Layering:
- this numbered item is `core/canonical` in the owner namespace `Module.Projective`: there is no
  upstream exact-interface descent theorem to recall, so the theorem below remains the chapter's
  canonical owner-level entry rather than a local wrapper.
-/
-- Proof sketch: decompose the projective `S`-module `S ⊗[R] M` as a direct sum of countably
-- generated projective summands using Theorem `10.84.5`; then descend countably generated
-- projective pieces by Lemma `10.95.3` along a transfinite Kaplansky dévissage as in the
-- textbook proof, and conclude that `M` is a direct sum of projective modules, hence projective.
/-- Theorem 10.95.6: if `R → S` is faithfully flat and the base change `S ⊗[R] M` is projective
as an `S`-module, then `M` is projective as an `R`-module. -/
theorem of_projective_tensorProduct_of_faithfullyFlat
    (S : Type v) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [Module.Projective S (S ⊗[R] M)] :
    Module.Projective R M := sorry

end

end Module.Projective
