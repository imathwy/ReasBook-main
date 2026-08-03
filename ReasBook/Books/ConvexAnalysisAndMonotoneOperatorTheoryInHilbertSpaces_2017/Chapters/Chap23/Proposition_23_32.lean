import BauschkeLean.Chap01.Text_1_0_9
import BauschkeLean.Chap01.Text_1_0_10
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap23.Definition_23_1
import BauschkeLean.Chap23.ResolventRealizer

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {A B : SetValuedOperator H H}

-- Source/core/bridge triage:
-- `source-facing`: Proposition 23.32 gives sufficient hypotheses for the resolvent-composition
--   identity attached to the pair `(A, B)`.
-- `core/canonical`: the owner declarations are the resolvent `J[...]` and the Chapter 1
--   set-valued-operator surfaces `comp`, `dom`, and `gra`.
-- `bridge/view`: later files should reuse these theorem-level identities directly rather than
--   restating the same composition formula through ad hoc wrappers.

-- Semantic recall: `lean_leansearch` returned only unrelated algebra-spectrum resolvent results,
-- so this item follows the local Chapter 23 resolvent owner `J[...]` and the Chapter 1
-- set-valued-operator surfaces `dom`, `gra`, and `comp`.

/-- Resolvent helper: in the unscaled `γ = 1` case, resolvent membership is exactly
the residual membership condition `x - p ∈ A p`. -/
private theorem mem_resolvent_iff_sub_mem
    (A : SetValuedOperator H H) (x p : H) :
    p ∈ J[A] x ↔ x - p ∈ A p := by
  -- Normalize the Chapter 23 resolvent API to the `γ = 1` residual criterion.
  simpa using (mem_resolvent_smul_iff_sub_mem_smul A (1 : PosReal) x p)

/-- Resolvent helper: in the unscaled `γ = 1` case, resolvent membership is exactly
graph membership `(p, x - p) ∈ gra A`. -/
private theorem mem_resolvent_iff_mem_graph
    (A : SetValuedOperator H H) (x p : H) :
    p ∈ J[A] x ↔ (p, x - p) ∈ gra A := by
  -- Normalize the Chapter 23 graph criterion to the `γ = 1` resolvent surface.
  simpa using (mem_resolvent_smul_iff_mem_graph A (1 : PosReal) x p)

/-- Resolvent helper: the pointwise sum of two monotone operators is monotone. -/
private theorem isMonotone_add
    {A B : SetValuedOperator H H} (hA : A.IsMonotone) (hB : B.IsMonotone) :
    (A + B).IsMonotone := by
  -- Decompose both sum-memberships into witnesses from the two summands.
  intro x u y v hu hv
  rcases Set.mem_add.mp hu with ⟨a, ha, b, hb, rfl⟩
  rcases Set.mem_add.mp hv with ⟨c, hc, d, hd, rfl⟩
  have hAc : 0 ≤ ⟪x - y, a - c⟫_ℝ := (isMonotone_iff A).1 hA ha hc
  have hBd : 0 ≤ ⟪x - y, b - d⟫_ℝ := (isMonotone_iff B).1 hB hb hd
  have hsum : 0 ≤ ⟪x - y, (a - c) + (b - d)⟫_ℝ := by
    simpa [inner_add_right] using add_nonneg hAc hBd
  -- Reassemble the residual as the pairing for the sum operator.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

variable [CompleteSpace H]

/-- Resolvent helper: the composition `J[A].comp J[B] x` is the singleton containing
the iterated `γ = 1` resolvent realizer. -/
private theorem resolventComp_eq_singleton_resolventMap
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) (x : H) :
    J[A].comp J[B] x =
      ({resolventMap A hA (1 : PosReal) (resolventMap B hB (1 : PosReal) x)} : Set H) := by
  let y := resolventMap B hB (1 : PosReal) x
  let p := resolventMap A hA (1 : PosReal) y
  have hJB : J[B] x = ({y} : Set H) := by
    -- Collapse the outer resolvent to its canonical singleton value.
    simpa [y] using resolvent_smul_eq_singleton_resolventMap_of_maximal B hB (1 : PosReal) x
  have hJA : J[A] y = ({p} : Set H) := by
    -- Collapse the inner resolvent at the chosen middle point as well.
    simpa [p] using resolvent_smul_eq_singleton_resolventMap_of_maximal A hA (1 : PosReal) y
  ext u
  constructor
  · intro hu
    -- Any composition witness must pass through the unique point in `J[B] x`.
    rw [SetValuedOperator.mem_comp] at hu
    rcases hu with ⟨z, hz, hu⟩
    rw [hJB] at hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    rw [hJA] at hu
    simpa [p] using hu
  · intro hu
    -- The unique middle point produces the unique point in the composition.
    rw [SetValuedOperator.mem_comp]
    refine ⟨y, ?_, ?_⟩
    · rw [hJB]
      simp [y]
    · rw [hJA]
      simpa [p] using hu

/-- Resolvent helper: once a point belongs to `J[A].comp J[B] x`, singleton-valued
resolvents force the whole composition to equal `{p}`. -/
private theorem resolventComp_eq_singleton_of_mem
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B) {x p : H}
    (hp : p ∈ J[A].comp J[B] x) :
    J[A].comp J[B] x = ({p} : Set H) := by
  have hcomp := resolventComp_eq_singleton_resolventMap hA hB x
  -- Compare the given point with the canonical singleton representative.
  rw [hcomp] at hp
  rw [Set.mem_singleton_iff] at hp
  rw [hcomp, hp]

/-- Resolvent helper: the source-proof witness for clause (1) lies in
`J[(A + B)] x`. -/
private theorem resolventCompWitness_mem_resolventAdd_of_domSubsetAtResolvent
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsubset : ∀ ⦃y p : H⦄, y ∈ dom B → p ∈ J[A] y → B y ⊆ B p) (x : H) :
    resolventMap A hA (1 : PosReal) (resolventMap B hB (1 : PosReal) x) ∈ J[(A + B)] x := by
  let y := resolventMap B hB (1 : PosReal) x
  let p := resolventMap A hA (1 : PosReal) y
  have hJB : J[B] x = ({y} : Set H) := by
    -- Realize the outer resolvent value as its canonical singleton.
    simpa [y] using resolvent_smul_eq_singleton_resolventMap_of_maximal B hB (1 : PosReal) x
  have hJA : J[A] y = ({p} : Set H) := by
    -- Realize the inner resolvent value as its canonical singleton.
    simpa [p] using resolvent_smul_eq_singleton_resolventMap_of_maximal A hA (1 : PosReal) y
  have hy_res : y ∈ J[B] x := by
    rw [hJB]
    simp [y]
  have hp_res : p ∈ J[A] y := by
    rw [hJA]
    simp [p]
  have hxy_mem : x - y ∈ B y := (mem_resolvent_iff_sub_mem B x y).1 hy_res
  have hy_dom : y ∈ dom B := by
    -- The residual witness shows that `B y` is nonempty.
    rw [mem_dom_iff]
    exact ⟨x - y, hxy_mem⟩
  have hxy_mem' : x - y ∈ B p := hsubset hy_dom hp_res hxy_mem
  have hyp_mem : y - p ∈ A p := (mem_resolvent_iff_sub_mem A y p).1 hp_res
  have hxp_mem : x - p ∈ (A + B) p := by
    -- Assemble the two residual pieces into a witness for `(A + B) p`.
    refine Set.mem_add.2 ⟨y - p, hyp_mem, x - y, hxy_mem', ?_⟩
    abel_nf
  exact (mem_resolvent_iff_sub_mem (A + B) x p).2 hxp_mem

omit [CompleteSpace H] in
/-- Resolvent helper: the graph-step hypothesis in clause (2) implies the
resolvent-step hypothesis in clause (1). -/
private theorem domSubsetAtResolvent_of_graphStepSubset
    (hsubset : ∀ ⦃x u : H⦄, (x, u) ∈ gra A → B (x + u) ⊆ B x) :
    ∀ ⦃y p : H⦄, y ∈ dom B → p ∈ J[A] y → B y ⊆ B p := by
  intro y p _ hp
  -- Translate the resolvent point into a graph point to apply the source hypothesis.
  have hp_graph : (p, y - p) ∈ gra A := (mem_resolvent_iff_mem_graph A y p).1 hp
  have hstep : B (p + (y - p)) ⊆ B p := hsubset hp_graph
  simpa using hstep

/-- Resolvent helper: the canonical `J[(A + B)]` point lies in `J[A].comp J[B] x`
under the clause (3) graph-step hypothesis. -/
private theorem resolventAddWitness_mem_resolventComp_of_graphStepSuperset
    (hAaddB : Maximal IsMonotone (A + B))
    (hsubset : ∀ ⦃x u : H⦄, (x, u) ∈ gra A → B x ⊆ B (x + u)) (x : H) :
    resolventMap (A + B) hAaddB (1 : PosReal) x ∈ J[A].comp J[B] x := by
  let p := resolventMap (A + B) hAaddB (1 : PosReal) x
  have hJadd : J[(A + B)] x = ({p} : Set H) := by
    -- Start from the canonical singleton description of the maximal resolvent.
    simpa [p] using
      resolvent_smul_eq_singleton_resolventMap_of_maximal (A + B) hAaddB (1 : PosReal) x
  have hp_res : p ∈ J[(A + B)] x := by
    rw [hJadd]
    simp [p]
  have hxp_mem : x - p ∈ (A + B) p := (mem_resolvent_iff_sub_mem (A + B) x p).1 hp_res
  rcases Set.mem_add.mp hxp_mem with ⟨a, ha, b, hb, hab⟩
  have hgraph : (p, a) ∈ gra A := by
    -- Record the `A`-component as a graph point for the step hypothesis.
    simpa [mem_graph] using ha
  have hb' : b ∈ B (p + a) := (hsubset hgraph) hb
  have hB_res : p + a ∈ J[B] x := by
    -- The `B`-component gives the resolvent condition at the middle point `p + a`.
    have hxb : x - (p + a) = b := by
      calc
        x - (p + a) = (x - p) - a := by abel_nf
        _ = (a + b) - a := by rw [hab]
        _ = b := by abel_nf
    refine (mem_resolvent_iff_sub_mem B x (p + a)).2 ?_
    simpa [hxb] using hb'
  have hA_res : p ∈ J[A] (p + a) := by
    -- The `A`-component says exactly that `p` resolves the middle point.
    refine (mem_resolvent_iff_sub_mem A (p + a) p).2 ?_
    have hpa : p + a - p = a := by
      abel_nf
    simpa [hpa] using ha
  -- Assemble the two resolvent memberships into a composition witness.
  rw [SetValuedOperator.mem_comp]
  exact ⟨p + a, hB_res, hA_res⟩

/-- First sufficient condition for the resolvent-composition identity. -/
theorem resolvent_add_eq_resolvent_comp_of_dom_subset_at_resolvent
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsubset : ∀ ⦃y p : H⦄, y ∈ dom B → p ∈ J[A] y → B y ⊆ B p) :
    J[(A + B)] = J[A].comp J[B] := by
  ext x u
  let p := resolventMap A hA (1 : PosReal) (resolventMap B hB (1 : PosReal) x)
  have hp : p ∈ J[(A + B)] x := by
    -- Build the source-proof witness for the resolvent of `A + B`.
    simpa [p] using
      resolventCompWitness_mem_resolventAdd_of_domSubsetAtResolvent hA hB hsubset x
  have hp_scaled : p ∈ J[((1 : ℝ) • (A + B))] x := by
    -- Rewrite the witness onto the scaled owner expected by the singleton lemma.
    simpa [p] using hp
  have hleft : J[(A + B)] x = ({p} : Set H) := by
    -- Monotonicity makes the nonempty resolvent value a singleton.
    simpa using
      resolvent_smul_eq_singleton_of_mem (isMonotone_add hA.1 hB.1) (1 : PosReal) hp_scaled
  have hright : J[A].comp J[B] x = ({p} : Set H) := by
    -- The composition is already the singleton at the iterated resolvent point.
    simpa [p] using resolventComp_eq_singleton_resolventMap hA hB x
  rw [hleft, hright]

/-- Second sufficient condition for the resolvent-composition identity. -/
theorem resolvent_add_eq_resolvent_comp_of_graph_step_subset
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hsubset : ∀ ⦃x u : H⦄, (x, u) ∈ gra A → B (x + u) ⊆ B x) :
    J[(A + B)] = J[A].comp J[B] := by
  -- Reduce clause (2) to clause (1) through the graph-to-resolvent bridge.
  exact resolvent_add_eq_resolvent_comp_of_dom_subset_at_resolvent hA hB
    (domSubsetAtResolvent_of_graphStepSubset hsubset)

/-- Third sufficient condition for the resolvent-composition identity. -/
theorem resolvent_add_eq_resolvent_comp_of_maximal_add_and_graph_step_superset
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hAaddB : Maximal IsMonotone (A + B))
    (hsubset : ∀ ⦃x u : H⦄, (x, u) ∈ gra A → B x ⊆ B (x + u)) :
    J[(A + B)] = J[A].comp J[B] := by
  ext x u
  let p := resolventMap (A + B) hAaddB (1 : PosReal) x
  have hp : p ∈ J[A].comp J[B] x := by
    -- Build the reverse source-proof witness from `J[(A + B)] x`.
    simpa [p] using
      resolventAddWitness_mem_resolventComp_of_graphStepSuperset hAaddB hsubset x
  have hleft : J[(A + B)] x = ({p} : Set H) := by
    -- The maximality of `A + B` gives the canonical singleton resolvent value.
    simpa [p] using
      resolvent_smul_eq_singleton_resolventMap_of_maximal (A + B) hAaddB (1 : PosReal) x
  have hright : J[A].comp J[B] x = ({p} : Set H) := by
    -- The composition must equal the singleton containing the witness point.
    exact resolventComp_eq_singleton_of_mem hA hB hp
  rw [hleft, hright]

/-- Proposition 23.32. Let `A, B : H → 2^H` be maximally monotone. Suppose that one of the
following holds:

1. Every resolvent point `p ∈ J[A] y` above `y ∈ dom B` satisfies `B y ⊆ B p`.
2. Every graph point `(x, u) ∈ gra A` satisfies `B (x + u) ⊆ B x`.
3. `A + B` is maximally monotone and every graph point `(x, u) ∈ gra A` satisfies
   `B x ⊆ B (x + u)`.

Then `J[(A + B)] = J[A].comp J[B]`. -/
theorem resolvent_add_eq_resolvent_comp
    (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (hcases :
      (∀ ⦃y p : H⦄, y ∈ dom B → p ∈ J[A] y → B y ⊆ B p) ∨
        (∀ ⦃x u : H⦄, (x, u) ∈ gra A → B (x + u) ⊆ B x) ∨
          (Maximal IsMonotone (A + B) ∧
            ∀ ⦃x u : H⦄, (x, u) ∈ gra A → B x ⊆ B (x + u))) :
    J[(A + B)] = J[A].comp J[B] := by
  -- Split the textbook trichotomy and dispatch each branch to the matching owner theorem.
  rcases hcases with hdom | hrest
  · exact resolvent_add_eq_resolvent_comp_of_dom_subset_at_resolvent hA hB hdom
  · rcases hrest with hgraph | hmax
    · exact resolvent_add_eq_resolvent_comp_of_graph_step_subset hA hB hgraph
    · rcases hmax with ⟨hAaddB, hsup⟩
      -- The last clause only needs conjunction unpacking before the ready-made closure theorem.
      exact
        resolvent_add_eq_resolvent_comp_of_maximal_add_and_graph_step_superset
          hA hB hAaddB hsup

end SetValuedOperator
