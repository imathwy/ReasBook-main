import Mathlib
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_5_1 (from Chap10) -/
universe u v

open Function

section FiniteModule

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/- Definition 10.5.1 (1): a finite, or finitely generated, `R`-module is the canonical typeclass
`Module.Finite R M`. -/
recall Module.Finite

namespace Module.Finite

-- Proof sketch: use `Module.Finite.exists_fin'` for the forward implication and
-- `Module.Finite.of_surjective` for the converse.
/-- A module is finite exactly when it is the quotient of a finite free module `Fin n → R`. -/
theorem iff_exists_surjective_free :
    Module.Finite R M ↔ ∃ n : ℕ, ∃ f : (Fin n → R) →ₗ[R] M, Surjective f := by
  constructor
  · intro hM
    letI := hM
    simpa using Module.Finite.exists_fin' R M
  · rintro ⟨n, f, hf⟩
    exact Module.Finite.of_surjective f hf

end Module.Finite

end FiniteModule

section FinitePresentation

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

/- Definition 10.5.1 (2): a finitely presented `R`-module is the canonical typeclass
`Module.FinitePresentation R M`. -/
recall Module.FinitePresentation

namespace Module.FinitePresentation

-- Proof sketch: combine `Module.FinitePresentation.exists_fin` with
-- `Submodule.fg_iff_exists_fin_linearMap`; for the converse, use the owner-level kernel criterion
-- `Module.FinitePresentation.fg_ker_iff` after identifying `ker g` with `range f`.
/-- A module is finitely presented exactly when it admits an exact sequence
`(Fin m → R) → (Fin n → R) → M → 0`, encoded as `Exact f g` together with the surjectivity of
`g`. -/
theorem iff_exists_exact_free_sequence :
    Module.FinitePresentation R M ↔
      ∃ n m : ℕ,
        ∃ f : (Fin m → R) →ₗ[R] (Fin n → R),
          ∃ g : (Fin n → R) →ₗ[R] M,
            Exact f g ∧ Surjective g := by
  constructor
  · intro hM
    letI := hM
    obtain ⟨n, K, e, hKfg⟩ := Module.FinitePresentation.exists_fin R M
    obtain ⟨m, f, hfK⟩ := (Submodule.fg_iff_exists_fin_linearMap R (Fin n → R)).mp hKfg
    let g : (Fin n → R) →ₗ[R] M := e.symm.toLinearMap ∘ₗ Submodule.mkQ K
    refine ⟨n, m, f, g, ?_, ?_⟩
    · change Exact f (e.symm.toLinearMap ∘ₗ Submodule.mkQ K)
      rw [LinearMap.exact_iff, LinearEquiv.ker_comp, Submodule.ker_mkQ, hfK]
    · intro x
      obtain ⟨y, hy⟩ := Submodule.mkQ_surjective K (e x)
      refine ⟨y, ?_⟩
      change e.symm (Submodule.mkQ K y) = x
      rw [hy, e.symm_apply_apply]
  · rintro ⟨n, m, f, g, hfg, hg⟩
    rw [LinearMap.exact_iff] at hfg
    exact (Module.FinitePresentation.fg_ker_iff g hg).1 (hfg.symm ▸ Submodule.fg_range f)

end Module.FinitePresentation

end FinitePresentation

/-! ### Lemma_10_5_2 (from Chap10) -/
universe u v w

/- Domain-style sampling:
- primary domain: projective modules and factorization of linear maps through a target map whose
  range contains the source range;
- sampled owner declarations: `Module.projective_lifting_property`,
  `Module.Projective.of_basis`, and `Module.Projective.of_free`;
- best owner abstraction: `Module.Projective R P`, with
  `Module.projective_lifting_property` as the canonical lifting API;
- primitive data: a projective source module `P`, maps `g : P →ₗ[R] N` and `f : M →ₗ[R] N`, and a
  range inclusion `g.range ≤ f.range`;
- derived API: the range-inclusion factorization theorem below and its finite-free specialization;
- layer: `LinearMap.exists_comp_eq_of_range_le` is a `bridge/view`, while
  `exists_factorization_of_range_le_of_free` remains the `source-facing` finite-free statement. -/

namespace LinearMap

theorem exists_comp_eq_of_range_le
    {R : Type u} [Semiring R]
    {P : Type v} [AddCommMonoid P] [Module R P] [Module.Projective R P]
    {M : Type w} [AddCommMonoid M] [Module R M]
    {N : Type _} [AddCommMonoid N] [Module R N]
    (g : P →ₗ[R] N) (f : M →ₗ[R] N)
    (h : g.range ≤ f.range) :
    ∃ l : P →ₗ[R] M, f.comp l = g := by
  let g' : P →ₗ[R] f.range := g.codRestrict f.range fun x ↦ h <| mem_range_self g x
  obtain ⟨l, hl⟩ :=
    Module.projective_lifting_property f.rangeRestrict g' f.surjective_rangeRestrict
  refine ⟨l, ?_⟩
  exact ext fun x ↦ congrArg Subtype.val <| LinearMap.congr_fun hl x

end LinearMap

/-- Lemma 10.5.2: if the image of a linear map `α : (Fin n → R) →ₗ[R] M` from the finite free
module `R^{\oplus n}` is contained in the image of `β : N →ₗ[R] M`, then `α` factors through
`β`. In canonical Lean form, this is the finite-free special case of
`Module.projective_lifting_property`. -/
theorem exists_factorization_of_range_le_of_free
    {R : Type u} [Semiring R]
    {M : Type v} [AddCommMonoid M] [Module R M]
    {N : Type w} [AddCommMonoid N] [Module R N]
    {n : ℕ}
    (α : (Fin n → R) →ₗ[R] M) (β : N →ₗ[R] M)
    (h : α.range ≤ β.range) :
    ∃ γ : (Fin n → R) →ₗ[R] N, β.comp γ = α := by
  exact LinearMap.exists_comp_eq_of_range_le α β h

/-! ### Lemma_10_5_3 (from Chap10) -/
universe u v w x

section

variable {R : Type u} [Ring R]
variable {M1 : Type v} [AddCommGroup M1] [Module R M1]
variable {M2 : Type w} [AddCommGroup M2] [Module R M2]
variable {M3 : Type x} [AddCommGroup M3] [Module R M3]

/- In a short exact sequence `0 → M1 → M2 → M3 → 0` of `R`-modules, if `M1`
and `M3` are finite, then `M2` is finite. This is exactly the canonical theorem
`Module.Finite.of_exact`. -/
recall Module.Finite.of_exact

namespace Module

-- Proof sketch: combine part (5) applied to the induced exact sequence on kernels of finite free
-- presentations with part (4), or equivalently argue via the snake lemma on a diagram of finite
-- free presentations of `M1` and `M3`.
/-- Lemma 10.5.3 (1): in a short exact sequence `0 → M1 → M2 → M3 → 0` of `R`-modules, if `M1`
and `M3` are finitely presented, then `M2` is finitely presented. -/
theorem finitePresentation_of_exact
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.FinitePresentation R M1] [Module.FinitePresentation R M3] :
    Module.FinitePresentation R M2 := by
  have hker : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hfg
  haveI : Module.FinitePresentation R (LinearMap.ker g) := by
    exact Module.FinitePresentation.of_equiv
      ((LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hker.symm))
  exact Module.finitePresentation_of_ker g hg

end Module

/- In a short exact sequence `0 → M1 → M2 → M3 → 0` of `R`-modules, if `M2`
is finite, then `M3` is finite. This is exactly the canonical theorem
`Module.Finite.of_surjective`. -/
recall Module.Finite.of_surjective

namespace Module

-- Proof sketch: apply `Module.finitePresentation_of_surjective` to `g`; exactness identifies
-- `ker g` with `range f`, and `range f` is finitely generated because `M1` is finite.
/-- Lemma 10.5.3 (2): in a short exact sequence `0 → M1 → M2 → M3 → 0` of `R`-modules, if `M2`
is finitely presented and `M1` is finite, then `M3` is finitely presented. -/
theorem finitePresentation_of_surjective_of_exact
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.FinitePresentation R M2] [Module.Finite R M1] :
    Module.FinitePresentation R M3 := by
  rw [LinearMap.exact_iff] at hfg
  exact Module.finitePresentation_of_surjective g hg (hfg.symm ▸ Submodule.fg_range f)

end Module

namespace Module.Finite

-- Proof sketch: `Module.FinitePresentation.fg_ker` gives finite generation of `ker g` from the
-- finite presentation of `M3` and finiteness of `M2`; exactness identifies `ker g` with
-- `range f`, and injectivity of `f` transports finiteness from `range f` back to `M1`.
/-- Lemma 10.5.3 (3): in a short exact sequence `0 → M1 → M2 → M3 → 0` of `R`-modules, if `M3`
is finitely presented and `M2` is finite, then `M1` is finite. -/
theorem of_exact_of_finitePresentation
    (f : M1 →ₗ[R] M2) (g : M2 →ₗ[R] M3)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.FinitePresentation R M3] [Module.Finite R M2] :
    Module.Finite R M1 := by
  have hker : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hfg
  have hrange : Module.Finite R (LinearMap.range f) :=
    Module.Finite.of_fg (hker.symm ▸ Module.FinitePresentation.fg_ker g hg)
  exact (Module.Finite.equiv_iff (LinearEquiv.ofInjective f hf)).2 hrange

end Module.Finite

end

/-! ### Lemma_10_5_4 (from Chap10) -/
universe u v

open RelSeries Submodule LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Two submodules form one cyclic-quotient step when the larger contains the smaller and the
quotient is isomorphic to `R ⧸ I` for some ideal `I`. -/
def IsQuotientEquivQuotient (N₁ N₂ : Submodule R M) : Prop :=
  N₁ ≤ N₂ ∧ ∃ I : Ideal R, Nonempty ((N₂ ⧸ N₁.submoduleOf N₂) ≃ₗ[R] R ⧸ I)

/-- The owner relation series whose successive quotients are cyclic quotients `R ⧸ I`. -/
abbrev CyclicFiltration (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :=
  RelSeries {(N₁, N₂) : Submodule R M × Submodule R M | IsQuotientEquivQuotient N₁ N₂}

omit [Module.Finite R M] in
-- Proof sketch: identify `(N ⊔ R∙x) / N` with the image of the restricted quotient map
-- `N ⊔ R∙x → M / N`, show that image is exactly the cyclic span of the class of `x`, and then
-- transport that cyclic span to `R / torsionOf (N.mkQ x)`.
/-- Helper for Lemma 10.5.4: the quotient `(N ⊔ R∙x) / N` is the cyclic span of the class of `x`
in `M ⧸ N`. -/
private theorem adjoin_singleton_quotient_equiv_span_class
    (N : Submodule R M) (x : M) :
    Nonempty (((↥(N ⊔ span R ({x} : Set M)) ⧸ N.submoduleOf (N ⊔ span R ({x} : Set M))) ≃ₗ[R]
      span R ({N.mkQ x} : Set (M ⧸ N)))) := by
  let N' : Submodule R M := N ⊔ span R ({x} : Set M)
  let f : N' →ₗ[R] M ⧸ N := N.mkQ.comp N'.subtype
  -- Route correction: package the one-generator step through the first isomorphism theorem
  -- for the restricted quotient map, instead of rebuilding the same bijectivity argument inline.
  have hker : LinearMap.ker f = N.submoduleOf N' := by
    -- The restricted quotient map kills exactly the elements already lying in `N`.
    ext y
    simp [f, N', submoduleOf, LinearMap.ker_comp]
  have hrange : LinearMap.range f = span R ({N.mkQ x} : Set (M ⧸ N)) := by
    -- Its image is the image of `N ⊔ R∙x` in `M ⧸ N`, and the `N` part vanishes.
    calc
      LinearMap.range f = N'.map N.mkQ := by
        simp [f, N', LinearMap.range_comp, range_subtype]
      _ = span R ({N.mkQ x} : Set (M ⧸ N)) := by
        rw [show N' = N ⊔ span R ({x} : Set M) by rfl, Submodule.map_sup, Submodule.map_span]
        simp
  -- The first isomorphism theorem turns the kernel/range computation into the desired quotient.
  refine ⟨(Submodule.quotEquivOfEq (LinearMap.ker f) (N.submoduleOf N') hker).symm.trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))⟩

omit [Module.Finite R M] in
/-- Helper for Lemma 10.5.4: the quotient `(N ⊔ R∙x) / N` is linearly equivalent to a quotient of
`R` by the torsion ideal of the class of `x` in `M ⧸ N`. -/
private theorem adjoin_singleton_quotient_equiv_torsionOf
    (N : Submodule R M) (x : M) :
    Nonempty (((↥(N ⊔ span R ({x} : Set M)) ⧸ N.submoduleOf (N ⊔ span R ({x} : Set M))) ≃ₗ[R]
      R ⧸ Ideal.torsionOf R (M ⧸ N) (N.mkQ x))) := by
  obtain ⟨e⟩ := adjoin_singleton_quotient_equiv_span_class (R := R) (M := M) N x
  -- The cyclic span of one element is canonically `R` modulo its torsion ideal.
  exact ⟨e ≪≫ₗ (Ideal.quotTorsionOfEquivSpanSingleton R (M ⧸ N) (N.mkQ x)).symm⟩

omit [Module.Finite R M] in
/-- Helper for Lemma 10.5.4: adjoining one element to a submodule gives a cyclic-quotient step. -/
private theorem isQuotientEquivQuotient_sup_span (N : Submodule R M) (x : M) :
    IsQuotientEquivQuotient N (N ⊔ span R ({x} : Set M)) := by
  obtain ⟨e⟩ := adjoin_singleton_quotient_equiv_torsionOf (R := R) (M := M) N x
  -- The one-step quotient is now explicitly identified with a quotient `R ⧸ I`.
  exact ⟨le_sup_left, ⟨Ideal.torsionOf R (M ⧸ N) (N.mkQ x), ⟨e⟩⟩⟩

omit [Module.Finite R M] in
-- Proof sketch: rewrite a tuple as `Fin.cons x m`, use the induction hypothesis for the tail, and
-- append the one-step cyclic quotient from `span (range m)` to `span (range (Fin.cons x m))`.
/-- Helper for Lemma 10.5.4: adding a head element to a finite tuple enlarges the span by the
corresponding singleton span. -/
private theorem span_range_fin_cons {n : ℕ} (x : M) (m : Fin n → M) :
    span R (Set.range (Fin.cons x m)) = span R (Set.range m) ⊔ span R ({x} : Set M) := by
  -- The range of a `Fin.cons` tuple is the inserted head together with the tail range.
  rw [Fin.range_cons, Submodule.span_insert, sup_comm]

omit [Module.Finite R M] in
-- Proof sketch: start from the zero submodule for the empty tuple, then append one cyclic step
-- each time a new generator is adjoined.
/-- Helper for Lemma 10.5.4: a finite tuple of elements yields a cyclic filtration from `0` to the
span of the tuple. -/
private theorem exists_relSeries_cyclic_of_tuple :
    ∀ {n : ℕ} (m : Fin n → M),
      ∃ s : CyclicFiltration R M,
        s.head = ⊥ ∧ s.last = span R (Set.range m) := by
  intro n m
  induction n with
  | zero =>
      -- The empty tuple spans `⊥`, so the singleton series at `⊥` already does the job.
      refine ⟨RelSeries.singleton _ (⊥ : Submodule R M), rfl, ?_⟩
      simp
  | succ n ih =>
      let x : M := m 0
      let m' : Fin n → M := Fin.tail m
      have hm : Fin.cons x m' = m := by
        simpa [x, m'] using Fin.cons_self_tail m
      obtain ⟨s, hs_head, hs_last⟩ := ih m'
      have hstep_tail :
          IsQuotientEquivQuotient (span R (Set.range m')) (span R (Set.range m)) := by
        -- The full span is obtained from the tail span by adjoining the head generator.
        rw [← hm, span_range_fin_cons]
        exact isQuotientEquivQuotient_sup_span (R := R) (M := M)
          (N := span R (Set.range m')) x
      have hstep :
          IsQuotientEquivQuotient s.last (span R (Set.range m)) := by
        rw [hs_last]
        exact hstep_tail
      -- Append the final cyclic quotient step to the filtration built for the tail tuple.
      refine ⟨s.snoc (span R (Set.range m)) hstep, ?_, ?_⟩
      · simpa [hs_head] using RelSeries.head_snoc s (span R (Set.range m)) hstep
      · simpa using RelSeries.last_snoc s (span R (Set.range m)) hstep

-- Proof sketch: choose a finite generating family of `M`, build the filtration by adjoining the
-- generators one at a time, and identify each successive quotient with a quotient `R ⧸ I` via the
-- canonical map `R → M / N` sending `1` to the class of the new generator.
/-- Lemma 10.5.4: a finite `R`-module admits a finite filtration
`0 = M₀ ≤ M₁ ≤ ⋯ ≤ Mₙ = M` by finite submodules such that each successive quotient
  `Mᵢ₊₁ / Mᵢ` is linearly isomorphic to a quotient `R ⧸ Iᵢ` of the ring. -/
theorem exists_finite_cyclic_filtration :
    ∃ s : CyclicFiltration R M, s.head = ⊥ ∧ s.last = ⊤ := by
  obtain ⟨n, m, hm⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨s, hs_head, hs_last⟩ := exists_relSeries_cyclic_of_tuple (R := R) (M := M) m
  -- A chosen finite generating family spans all of `M`, so the tuple filtration ends at `⊤`.
  refine ⟨s, hs_head, ?_⟩
  rw [hs_last, hm]

end

/-! ### Lemma_10_5_5 (from Chap10) -/
/- Lemma 10.5.5: let `R → S` be a ring map and let `M` be an `S`-module. If `M` is finite as an
`R`-module via restriction of scalars, then `M` is finite as an `S`-module. This is exactly the
canonical theorem `Module.Finite.of_restrictScalars_finite`. -/
recall Module.Finite.of_restrictScalars_finite
