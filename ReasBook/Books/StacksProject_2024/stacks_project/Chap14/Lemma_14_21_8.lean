import StacksProject_2024.Chap14.Lemma_14_21_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Simplicial
open scoped Simplicial

universe u

namespace SSet

/- Domain-style sampling for Lemma 14.21.8:
- primary domain: finite simplicial sets and filtrations of subcomplex inclusions by successive
  single-simplex extensions;
- sampled owner-style declarations:
  `SSet.Finite`,
  `SSet.Subcomplex.N`,
  `SSet.Subcomplex.ofSimplex`,
  `RelSeries`;
- best owner abstraction:
  `source-facing`: the existence of a finite chain `U = W₀ ⊆ ⋯ ⊆ W_r = V` whose successive
  inclusions are single-simplex extensions with the boundary of the attached simplex already in
  the previous stage;
  `core/canonical`: finiteness through `SSet.Finite`, single-step extension data through
  `Subcomplex.N`, `Subcomplex.N.boundary_range_le`, and `Subcomplex.ofSimplex`, and finite chains
  through `RelSeries`;
  `bridge/view`: the anonymous adjacent-step relation on `V.Subcomplex`, used only inside the
  filtration existence theorem because it has no separate owner-level downstream role;
- primitive data:
  only the new simplex `x : U.N`, the boundary-factorization predicate `x.boundary_range_le`, and
  the equality `U ⊔ Subcomplex.ofSimplex x.simplex = W` for each step of the chain;
- derived API:
  the ambient finiteness owner `SSet.Finite` and the source-facing finite chain expressed by
  `RelSeries`.

The finite-chain owner is `RelSeries`, so the public source-facing existence statement should use
that canonical owner directly. The adjacent-step predicate is only a bridge/view used inside this
one theorem, so it should not survive as a second public owner declaration. In particular,
`SSet.Finite V` already supplies the degreewise finiteness consequences needed for the textbook
hypothesis, so the filtration theorem should consume that owner canonically as an instance rather
than as a separate named public hypothesis. -/

-- Proof sketch: convert the finiteness hypotheses on nondegenerate simplices into a finite number
-- of missing nondegenerate simplices of `V` outside `U`, and induct on that number. At each step,
-- pick one of minimal degree, adjoin all of its degeneracies to obtain the next subcomplex, verify
-- that every proper face of the chosen simplex already lies in the previous stage by minimality,
-- and iterate until reaching `V`.
/-- Helper for Lemma 14.21.8: the missing nondegenerate simplices of a finite simplicial set form a
finite type. -/
private theorem missing_nondegenerate_finite
    {V : SSet.{u}} [V.Finite] (U : V.Subcomplex) : Finite U.N := by
  -- Forgetting the ambient-membership condition embeds `U.N` into the finite type `V.N`.
  exact Finite.of_injective (fun x : U.N => x.toN) (fun x y h => by
    simpa [SSet.Subcomplex.N.ext_iff] using h)

/-- Helper for Lemma 14.21.8: if no missing nondegenerate simplices remain, then the subcomplex is
already all of `V`. -/
private theorem eq_top_of_isEmpty_missing_nondegenerate
    {V : SSet.{u}} (U : V.Subcomplex) (h : IsEmpty U.N) : U = ⊤ := by
  -- Every nondegenerate simplex of `V` already lies in `U`, so `U` is top.
  rw [U.eq_top_iff_contains_nonDegenerate]
  intro n x hx
  by_contra hxU
  exact h.false (SSet.Subcomplex.N.mk x hx hxU)

/-- Helper for Lemma 14.21.8: a codimension-one face of a minimal missing simplex already lies in
the old subcomplex. -/
private theorem minimal_missing_simplex_face_mem
    {V : SSet.{u}} {U : V.Subcomplex} {x : U.N}
    (hmin : ∀ y : U.N, y.dim < x.dim → False)
    {n : ℕ} (hdim : x.dim = n + 1) (i : Fin (n + 2)) :
    V.δ i (x.cast hdim).simplex ∈ U.obj _ := by
  -- A missing face would produce a smaller missing nondegenerate simplex, contradicting minimality.
  by_contra hxface
  obtain ⟨y, f, hf, hy⟩ := Subcomplex.existsN (A := U) (V.δ i (x.cast hdim).simplex) hxface
  have hle : y.dim ≤ n := SimplexCategory.le_of_epi f
  have hylt : y.dim < x.dim := by
    rw [hdim]
    exact Nat.lt_succ_of_le hle
  exact hmin y hylt

/-- Helper for Lemma 14.21.8: the boundary of a minimal missing simplex lands in the previous
stage. -/
private theorem minimal_missing_simplex_boundary_range_le
    {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)
    (hmin : ∀ y : U.N, y.dim < x.dim → False) :
    x.boundary_range_le := by
  obtain ⟨d, sx, hsx, hsx_not, rfl⟩ := x.mk_surjective
  cases d with
  | zero =>
      intro m y hy
      -- In degree `0` the boundary is empty, so there is no boundary simplex to check.
      have _ : Subsingleton (Fin (0 + 1)) := by
        simpa using (inferInstance : Subsingleton (Fin 1))
      have hy' := hy
      simp only [SSet.Subcomplex.range, CategoryTheory.Subfunctor.range_obj, Set.mem_range,
        SSet.boundary, Function.Surjective, SSet.Subcomplex.N.mk_dim] at hy'
      rcases hy' with ⟨⟨a, ha⟩, hval⟩
      apply False.elim
      apply ha
      intro b
      refine ⟨0, ?_⟩
      exact Subsingleton.elim _ _
  | succ n =>
      intro m y hy
      -- Any boundary simplex factors through some face `δ i`, and minimality puts that face in
      -- `U`.
      have hy' := hy
      simp only [SSet.Subcomplex.range, CategoryTheory.Subfunctor.range_obj, Set.mem_range] at hy'
      rcases hy' with ⟨⟨z, hz⟩, rfl⟩
      obtain ⟨θ, rfl⟩ := SSet.stdSimplex.objEquiv.symm.surjective z
      change V.map θ.op sx ∈ U.obj _
      change ¬ Function.Surjective θ.toOrderHom at hz
      obtain ⟨i, θ', hθ⟩ := SimplexCategory.eq_comp_δ_of_not_surjective θ hz
      simpa [hθ, op_comp, Functor.map_comp] using
        U.map θ'.op (minimal_missing_simplex_face_mem hmin rfl i)

/-- Helper for Lemma 14.21.8: if a simplex is still missing after adjoining `x`, then it was
already missing before adjoining `x`. -/
private theorem notMem_of_notMem_adjoin_simplex
    {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)
    (y : (U ⊔ Subcomplex.ofSimplex x.simplex).N) :
    y.simplex ∉ U.obj _ := by
  -- Membership in `U` would also give membership in the adjoined subcomplex.
  intro hyU
  exact y.notMem (by simpa using Or.inl hyU)

/-- Helper for Lemma 14.21.8: adjoining a missing simplex strictly decreases the missing
nondegenerate set. -/
private theorem adjoin_simplex_missing_embedding
    {V : SSet.{u}} {U : V.Subcomplex} (x : U.N) :
    let W := U ⊔ Subcomplex.ofSimplex x.simplex
    ∃ f : W.N → U.N, Function.Injective f ∧ ¬ Function.Surjective f := by
  let W := U ⊔ Subcomplex.ofSimplex x.simplex
  refine ⟨fun y ↦ Subcomplex.N.mk y.simplex y.nonDegenerate
      (notMem_of_notMem_adjoin_simplex x y), ?_, ?_⟩
  · intro y z h
    -- The forgetful map remembers the same ambient nondegenerate simplex, so it is injective.
    apply (SSet.Subcomplex.N.ext_iff y z).2
    simpa using congrArg SSet.Subcomplex.N.toN h
  · intro hsurj
    -- The attached simplex `x` is no longer missing from `W`, so it cannot lie in the image.
    obtain ⟨y, hy⟩ := hsurj x
    have htoN : y.toN = x.toN := by
      simpa using congrArg SSet.Subcomplex.N.toN hy
    have hy_le : y.toN.subcomplex ≤ W := by
      rw [htoN, SSet.Subcomplex.ofSimplex_le_iff]
      exact Or.inr (Subcomplex.mem_ofSimplex_obj x.simplex)
    exact y.notMem (hy_le _ (Subcomplex.mem_ofSimplex_obj y.simplex))

/-- Lemma 14.21.8: if `U ⊆ V` is an inclusion of simplicial sets, if `V` is degreewise finite,
and if `V` has finitely many nondegenerate simplices, then there
exists a finite filtration from `U` to `V` whose successive inclusions are single-simplex
extensions in the sense of Lemma 14.21.7. Here the finite chain is expressed by the canonical
owner `RelSeries`, starting at `U` and ending at `⊤ : V.Subcomplex`; the adjacent-step predicate
is kept inline because it is only a bridge/view for this one source-facing theorem. The degreewise
finiteness of `V` is already part of the canonical owner `SSet.Finite V`, and the corresponding
finiteness data for `U` is derived by the subcomplex instance. -/
theorem exists_singleSimplexExtensionFiltration
    {V : SSet.{u}} [V.Finite] (U : V.Subcomplex) :
    ∃ s : RelSeries
      ({ p | ∃ x : p.1.N,
        x.boundary_range_le ∧ p.1 ⊔ Subcomplex.ofSimplex x.simplex = p.2 } :
        SetRel V.Subcomplex V.Subcomplex),
      s.head = U ∧ s.last = (⊤ : V.Subcomplex) := by
  let r : SetRel V.Subcomplex V.Subcomplex :=
    { p | ∃ x : p.1.N,
        x.boundary_range_le ∧ p.1 ⊔ Subcomplex.ofSimplex x.simplex = p.2 }
  have hmain : ∀ n : ℕ, ∀ A : V.Subcomplex, Nat.card A.N = n →
      ∃ s : RelSeries r, s.head = A ∧ s.last = (⊤ : V.Subcomplex) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k ih A hA
    let _ : Finite A.N := missing_nondegenerate_finite A
    by_cases hnonempty : Nonempty A.N
    · let _ : Nonempty A.N := hnonempty
      -- Choose a missing nondegenerate simplex of minimal dimension.
      obtain ⟨x, hxmin⟩ := Finite.exists_min (α := A.N) fun y => y.dim
      have hmin : ∀ y : A.N, y.dim < x.dim → False := by
        intro y hy
        exact not_lt_of_ge (hxmin y) hy
      let W := A ⊔ Subcomplex.ofSimplex x.simplex
      have hcard_lt : Nat.card W.N < k := by
        -- Adjoining the chosen simplex removes at least that simplex from the missing set.
        let _ : Finite W.N := missing_nondegenerate_finite W
        let _ : Fintype A.N := Fintype.ofFinite A.N
        let _ : Fintype W.N := Fintype.ofFinite W.N
        obtain ⟨f, hf_inj, hf_nsurj⟩ := adjoin_simplex_missing_embedding x
        have hlt' : Fintype.card W.N < Fintype.card A.N :=
          Fintype.card_lt_of_injective_not_surjective f hf_inj hf_nsurj
        exact hA ▸ by simpa [Nat.card_eq_fintype_card] using hlt'
      obtain ⟨s, hs_head, hs_last⟩ := ih (Nat.card W.N) hcard_lt W rfl
      have hstep : (A, W) ∈ r := by
        refine ⟨x, minimal_missing_simplex_boundary_range_le x hmin, rfl⟩
      have hstep' : (A, s.head) ∈ r := by
        simpa [hs_head] using hstep
      refine ⟨s.cons A hstep', ?_, ?_⟩
      · simp
      · simpa [hs_last]
    · -- If nothing is missing, we are already at the terminal stage.
      have hisempty : IsEmpty A.N := not_nonempty_iff.mp hnonempty
      have htop : A = (⊤ : V.Subcomplex) := eq_top_of_isEmpty_missing_nondegenerate A hisempty
      refine ⟨RelSeries.singleton r A, ?_, ?_⟩
      · simp
      · simpa [htop]
  let _ : Finite U.N := missing_nondegenerate_finite U
  exact hmain (Nat.card U.N) U rfl

end SSet
