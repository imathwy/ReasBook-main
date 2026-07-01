import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
