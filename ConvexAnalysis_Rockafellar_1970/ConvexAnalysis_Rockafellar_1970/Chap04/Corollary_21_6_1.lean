import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

section

variable {𝕜 : Type v} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable {I : Type z}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 21.6.1 is the Helly-type solvability criterion for a finite mixed
  system of convex inequalities on a finite-dimensional vector space, all required to be
  satisfied inside a given convex set `C`. Specializing to a concrete coordinate model recovers
  the textbook `n + 1` bound.
- `core/canonical`: the owner abstraction is the direct feasible-set owner
  `convexInequalitySolutionSet relation f μ`, together with the single-constraint owner sets
  `(relation i).solutionSet (f i) (μ i)`.
- `bridge/view`: the textbook speaks about finitely many strict and weak inequalities; the
  chapter canonicalizes that data by the primitive families `relation`, `f`, and `μ`, with the
  feasible set derived as their indexed intersection rather than by a separate packaged wrapper.

Domain-style sampling used here:
- `ConvexInequalityRelation.solutionSet`;
- `convexInequalitySolutionSet`;
- `convex_convexInequalitySolutionSet`;
- `Convex.helly_theorem'`.

Primitive data vs derived API:
- primitive data: the finite families `relation`, `f`, `μ` and the ambient convex set `C`;
- derived API: feasibility of a finite subsystem, expressed by the owner feasible set on a
  `Finset` subsystem, and global feasibility as the `Finset.univ` specialization. The pointwise
  existential reading is only the immediate `Set.Nonempty`/membership expansion of this owner
  statement, so it should not remain as a parallel public theorem.

Ambient refinement:
- the owner APIs used here already live on arbitrary finite-dimensional modules over ordered
  fields, so concrete coordinate models are presentation only and should not remain in the public
  statement.

Layer target: `source-facing`, stated on the canonical finite-dimensional owner layer and using
the owner feasible-set API directly.
-/

-- Proof sketch: adjoin `C` to the finite family of owner constraint sets
-- `(relation i).solutionSet (f i) (μ i)`. Each member is convex: `C` by hypothesis, and every
-- owner constraint set by assumption. The small-subsystem assumption gives nonempty intersections
-- for all subfamilies of cardinality at most `Module.finrank 𝕜 E + 1`, so Helly's theorem
-- yields a point in the intersection of `C` with all owner constraint sets, i.e. in
-- `C ∩ convexInequalitySolutionSet relation f μ`.
/-- Primitive finite-operational owner form on a subsystem `s`: if every
sub-subsystem `J ⊆ s` with cardinality at most `Module.finrank 𝕜 E + 1` has a point in `C`
satisfying all constraints in `J`, then `s` itself has a point in `C` satisfying all constraints
in `s`. This owner statement is kept at the primitive convex-set layer: it assumes convexity of
each single-constraint owner set on `s`, rather than a stronger sufficient condition on the
left-hand sides. -/
theorem convexInequalitySolutionSetOn_nonempty_of_small_subsystems_feasible_of_constraintConvexity
    {β : Type*} [LE β] [LT β]
    (s : Finset I) (relation : I → ConvexInequalityRelation) (f : I → E → β) (μ : I → β)
    (h_constraint_convex :
      ∀ i ∈ s, Convex 𝕜 ((relation i).solutionSet (f i) (μ i)))
    {C : Set E} (hC : Convex 𝕜 C)
    (h_subsystem :
      ∀ J : Finset I, J ⊆ s → J.card ≤ Module.finrank 𝕜 E + 1 →
        (C ∩ convexInequalitySolutionSetOn J relation f μ).Nonempty) :
    (C ∩ convexInequalitySolutionSetOn s relation f μ).Nonempty := by
  classical
  let constraintSet : I → Set E := fun i ↦ (relation i).solutionSet (f i) (μ i)
  let family : Option I → Set E := Option.elim' C constraintSet
  let s' : Finset (Option I) := insert none (s.image some)
  have h_family :
      (⋂ i ∈ s', family i).Nonempty := by
    have h_convex : ∀ i ∈ s', Convex 𝕜 (family i) := by
      intro i hi
      cases i with
      | none => simpa [family] using hC
      | some i =>
          have hi_s : i ∈ s := by
            simpa [s'] using hi
          simpa [family, constraintSet] using h_constraint_convex i hi_s
    have h_inter :
        ∀ G ⊆ s', G.card ≤ Module.finrank 𝕜 E + 1 →
          (⋂ i ∈ G, family i).Nonempty := by
      intro G hGs hG
      have hG_subset_s : G.eraseNone ⊆ s := by
        intro i hi
        have hiG : (some i) ∈ G := by simpa using hi
        have hiS' : (some i) ∈ s' := hGs hiG
        simpa [s'] using hiS'
      rcases h_subsystem G.eraseNone hG_subset_s ((Finset.card_eraseNone_le G).trans hG) with
        ⟨x, hxC, hxG⟩
      have hxG' := mem_convexInequalitySolutionSetOn.mp hxG
      refine ⟨x, by
        simpa using
          (show ∀ i ∈ G, x ∈ family i from by
            intro i hi
            cases i with
            | none => simpa [family] using hxC
            | some i =>
                have hi' : i ∈ G.eraseNone := by
                  simpa using hi
                simpa [family, constraintSet] using hxG' i hi')⟩
    exact Convex.helly_theorem' h_convex h_inter
  rcases h_family with ⟨x, hx⟩
  have hx' : ∀ i ∈ s', x ∈ family i := by
    simpa [s'] using hx
  have hxC : x ∈ C := by
    have : x ∈ family none := hx' none (by simp [s'])
    simpa [family] using this
  have hx_feasible_on_s : x ∈ convexInequalitySolutionSetOn s relation f μ := by
    refine mem_convexInequalitySolutionSetOn.2 ?_
    intro i hi
    have : x ∈ family (.some i) := hx' (.some i) (by simpa [s'] using hi)
    simpa [family, constraintSet] using this
  exact ⟨x, hxC, hx_feasible_on_s⟩

/-- Finite-operational source-facing owner form of Corollary 21.6.1 on a subsystem `s`, derived
from Helly's theorem using intrinsic convex-on-`C` data for each left-hand side. This keeps the
public source-facing layer at `ConvexOn 𝕜 C` rather than the stronger global owner
`Function.IsConvex`. -/
section WithTopBotCodomain

variable {α : Type w} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
  [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

theorem convexInequalitySolutionSetOn_nonempty_of_small_subsystems_feasible
    (s : Finset I) (relation : I → ConvexInequalityRelation) (f : I → E → WithTopBot α)
    (μ : I → WithTopBot α) {C : Set E} (hC : Convex 𝕜 C)
    (hf : ∀ i ∈ s, ConvexOn 𝕜 C (f i))
    (h_subsystem :
      ∀ J : Finset I, J ⊆ s → J.card ≤ Module.finrank 𝕜 E + 1 →
        (C ∩ convexInequalitySolutionSetOn J relation f μ).Nonempty) :
    (C ∩ convexInequalitySolutionSetOn s relation f μ).Nonempty := by
  classical
  let constraintSet : I → Set E := fun i ↦ C ∩ (relation i).solutionSet (f i) (μ i)
  let family : Option I → Set E := Option.elim' C constraintSet
  let s' : Finset (Option I) := insert none (s.image some)
  have h_family : (⋂ i ∈ s', family i).Nonempty := by
    have h_convex : ∀ i ∈ s', Convex 𝕜 (family i) := by
      intro i hi
      cases i with
      | none =>
          simpa [family] using hC
      | some i =>
          have hi_s : i ∈ s := by
            simpa [s'] using hi
          have hfi : ConvexOn 𝕜 C (f i) := hf i hi_s
          have hconv_i : Convex 𝕜 (C ∩ (relation i).solutionSet (f i) (μ i)) := by
            cases hri : relation i with
            | le =>
                simpa [hri, ConvexInequalityRelation.solutionSet, Set.setOf_and] using
                  hfi.convex_le (μ i)
            | lt =>
                simpa [hri, ConvexInequalityRelation.solutionSet, Set.setOf_and] using
                  hfi.convex_lt (μ i)
          simpa [family, constraintSet] using hconv_i
    have h_inter :
        ∀ G ⊆ s', G.card ≤ Module.finrank 𝕜 E + 1 →
          (⋂ i ∈ G, family i).Nonempty := by
      intro G hGs hG
      have hG_subset_s : G.eraseNone ⊆ s := by
        intro i hi
        have hiG : (some i) ∈ G := by simpa using hi
        have hiS' : (some i) ∈ s' := hGs hiG
        simpa [s'] using hiS'
      rcases h_subsystem G.eraseNone hG_subset_s ((Finset.card_eraseNone_le G).trans hG) with
        ⟨x, hxC, hxG⟩
      have hxG' := mem_convexInequalitySolutionSetOn.mp hxG
      refine ⟨x, by
        simpa using
          (show ∀ i ∈ G, x ∈ family i from by
            intro i hi
            cases i with
            | none =>
                simpa [family] using hxC
            | some i =>
                have hi' : i ∈ G.eraseNone := by
                  simpa using hi
                have hxi : x ∈ (relation i).solutionSet (f i) (μ i) := hxG' i hi'
                have hxiC : x ∈ C ∩ (relation i).solutionSet (f i) (μ i) := ⟨hxC, hxi⟩
                simpa [family, constraintSet] using hxiC)⟩
    exact Convex.helly_theorem' h_convex h_inter
  rcases h_family with ⟨x, hx⟩
  have hx' : ∀ i ∈ s', x ∈ family i := by
    simpa [s'] using hx
  have hxC : x ∈ C := by
    have : x ∈ family none := hx' none (by simp [s'])
    simpa [family] using this
  have hx_feasible_on_s : x ∈ convexInequalitySolutionSetOn s relation f μ := by
    refine mem_convexInequalitySolutionSetOn.2 ?_
    intro i hi
    have : x ∈ family (.some i) := hx' (.some i) (by simpa [s'] using hi)
    have hx_inter : x ∈ C ∩ (relation i).solutionSet (f i) (μ i) := by
      simpa [family, constraintSet] using this
    exact hx_inter.2
  exact ⟨x, hxC, hx_feasible_on_s⟩

end WithTopBotCodomain

/-- Primitive global owner form (finite index type): if every subsystem of at most
`Module.finrank 𝕜 E + 1` constraints has a point in `C`, then the whole system has a point in
`C`. This is the `s = Finset.univ` specialization of the primitive subsystem owner theorem. -/
theorem convexInequalitySolutionSet_nonempty_of_small_subsystems_feasible_of_constraintConvexity
    {β : Type*} [LE β] [LT β] [Finite I]
    (relation : I → ConvexInequalityRelation) (f : I → E → β) (μ : I → β)
    (h_constraint_convex : ∀ i, Convex 𝕜 ((relation i).solutionSet (f i) (μ i)))
    {C : Set E} (hC : Convex 𝕜 C)
    (h_subsystem :
      ∀ J : Finset I, J.card ≤ Module.finrank 𝕜 E + 1 →
        (C ∩ convexInequalitySolutionSetOn J relation f μ).Nonempty) :
    (C ∩ convexInequalitySolutionSet relation f μ).Nonempty := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  have h_subsystem_univ :
      ∀ J : Finset I, J ⊆ (Finset.univ : Finset I) →
        J.card ≤ Module.finrank 𝕜 E + 1 →
        (C ∩ convexInequalitySolutionSetOn J relation f μ).Nonempty := by
    intro J _ hJ
    exact h_subsystem J hJ
  have h_univ :
      (C ∩ convexInequalitySolutionSetOn (Finset.univ : Finset I) relation f μ).Nonempty :=
    convexInequalitySolutionSetOn_nonempty_of_small_subsystems_feasible_of_constraintConvexity
      (s := Finset.univ) relation f μ
      (fun i _ ↦ h_constraint_convex i) hC h_subsystem_univ
  have h_univ_eq :
      convexInequalitySolutionSetOn (Finset.univ : Finset I) relation f μ =
        convexInequalitySolutionSet relation f μ := by
    ext x
    simp [convexInequalitySolutionSetOn]
  simpa [h_univ_eq] using h_univ

/-- Corollary 21.6.1: if every subsystem of at most `Module.finrank 𝕜 E + 1` constraints in a
finite mixed convex inequality system has a solution in a convex set `C`, then the whole system
has a solution in `C`. This is the `s = Finset.univ` specialization of the finite-operational
owner theorem above. The usual pointwise existence form is obtained immediately by expanding
`.Nonempty` and `mem_convexInequalitySolutionSet`. -/
section WithTopBotCodomain

variable {α : Type w} [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
  [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

theorem convexInequalitySolutionSet_nonempty_of_small_subsystems_feasible
    [Finite I]
    (relation : I → ConvexInequalityRelation) (f : I → E → WithTopBot α)
    (μ : I → WithTopBot α) {C : Set E} (hC : Convex 𝕜 C)
    (hf : ∀ i, ConvexOn 𝕜 C (f i))
    (h_subsystem :
      ∀ J : Finset I, J.card ≤ Module.finrank 𝕜 E + 1 →
        (C ∩ convexInequalitySolutionSetOn J relation f μ).Nonempty) :
    (C ∩ convexInequalitySolutionSet relation f μ).Nonempty := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  have h_subsystem_univ :
      ∀ J : Finset I, J ⊆ (Finset.univ : Finset I) →
        J.card ≤ Module.finrank 𝕜 E + 1 →
        (C ∩ convexInequalitySolutionSetOn J relation f μ).Nonempty := by
    intro J _ hJ
    exact h_subsystem J hJ
  have h_univ :
      (C ∩ convexInequalitySolutionSetOn (Finset.univ : Finset I) relation f μ).Nonempty :=
    convexInequalitySolutionSetOn_nonempty_of_small_subsystems_feasible
      (s := Finset.univ) relation f μ hC (fun i _ ↦ hf i) h_subsystem_univ
  have h_univ_eq :
      convexInequalitySolutionSetOn (Finset.univ : Finset I) relation f μ =
        convexInequalitySolutionSet relation f μ := by
    ext x
    simp [convexInequalitySolutionSetOn]
  simpa [h_univ_eq] using h_univ

end WithTopBotCodomain

end
