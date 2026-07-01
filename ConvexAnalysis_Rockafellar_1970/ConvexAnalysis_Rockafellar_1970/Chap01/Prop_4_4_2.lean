import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {E : Type u}
variable {𝕜 : Type w}
variable {α : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 4.4.2 says that convexity depends only on what happens on the
  effective domain.
- `core/canonical`: the primitive owner statement is relative and set-based:
  convexity of the finite-height epigraph `epi[S] f` is equivalent to convexity of
  `epi[S ∩ dom(f)] f`; the global equivalence is the specialization `S = Set.univ`.
- `bridge/view`: the core bridge is `epigraph_inter_effectiveDomain_eq`,
  with the global statement recovered by setting `S = Set.univ`.

Domain-style sampling used here:
- `effectiveDomain` and `mem_effectiveDomain` from Definition 4.4;
- `epigraph_inter_effectiveDomain_eq` and `epigraph_effectiveDomain_eq` from Definition 4.4;
- `epi` and `epi[s]`.

Primitive data vs derived API:
- primitive input: the function `f : E → WithTopBot α`;
- derived bridge data: the effective domain `dom(f)` and
  `epigraph_inter_effectiveDomain_eq`.
-/

section

variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid α] [SMul 𝕜 α] [Preorder α]

namespace Function

/-- Helper for Prop 4.4.2: equal relative epigraphs have equivalent convexity owners. -/
lemma convex_epi_iff_of_eq {f : E → WithTopBot α} {S T : Set E}
    (hST : (epi[S] f) = (epi[T] f)) :
    Convex 𝕜 (epi[S] f) ↔ Convex 𝕜 (epi[T] f) := by
  -- Transport convexity across the identified epigraph sets.
  simp only [hST]

/-- Helper for Prop 4.4.2: convexity of `epi[S] f` depends only on `S ∩ dom(f)`. -/
theorem convex_epi_restrict_iff_inter_dom {f : E → WithTopBot α} {S : Set E} :
    Convex 𝕜 (epi[S] f) ↔ Convex 𝕜 (epi[S ∩ dom(f)] f) := by
  -- Restricting to the effective domain does not change the relative epigraph.
  exact
    convex_epi_iff_of_eq (f := f)
      ((epigraph_inter_effectiveDomain_eq (f := f) (S := S)).symm)

/-- Helper for Prop 4.4.2: convexity of `epi[S] f` restricts to `S ∩ dom(f)`. -/
theorem convex_epi_restrict_inter_dom {f : E → WithTopBot α} {S : Set E}
    (hf : Convex 𝕜 (epi[S] f)) :
    Convex 𝕜 (epi[S ∩ dom(f)] f) := by
  -- Use the relative equivalence in the forward direction.
  exact (convex_epi_restrict_iff_inter_dom (f := f) (S := S)).1 hf

/-- Helper for Prop 4.4.2: convexity on `S ∩ dom(f)` already gives convexity on `S`. -/
theorem convex_epi_restrict_of_inter_dom {f : E → WithTopBot α} {S : Set E}
    (hf : Convex 𝕜 (epi[S ∩ dom(f)] f)) :
    Convex 𝕜 (epi[S] f) := by
  -- Use the same equivalence in the reverse direction.
  exact (convex_epi_restrict_iff_inter_dom (f := f) (S := S)).2 hf

/-- Prop 4.4.2: `epi f` is convex if and only if `epi[dom(f)] f` is convex. -/
theorem convex_epi_iff_dom {f : E → WithTopBot α} :
    Convex 𝕜 (epi f) ↔ Convex 𝕜 (epi[dom(f)] f) := by
  -- Specialize the relative owner statement to the unrestricted base set.
  convert (convex_epi_restrict_iff_inter_dom (f := f) (S := (Set.univ : Set E))) using 1
  -- The base set normalization `univ ∩ dom(f) = dom(f)` recovers the textbook form.
  · simp [Set.univ_inter]

/-- Helper for Prop 4.4.2: convexity of `epi f` implies convexity on `dom(f)`. -/
theorem convex_epi_on_dom {f : E → WithTopBot α}
    (hf : Convex 𝕜 (epi f)) :
    Convex 𝕜 (epi[dom(f)] f) := by
  -- Read off the forward implication from the global equivalence.
  exact (convex_epi_iff_dom (f := f)).1 hf

/-- Helper for Prop 4.4.2: convexity on `dom(f)` implies convexity of `epi f`. -/
theorem convex_epi_of_dom {f : E → WithTopBot α}
    (hf : Convex 𝕜 (epi[dom(f)] f)) :
    Convex 𝕜 (epi f) := by
  -- Read off the reverse implication from the global equivalence.
  exact (convex_epi_iff_dom (f := f)).2 hf

end Function

end

end
