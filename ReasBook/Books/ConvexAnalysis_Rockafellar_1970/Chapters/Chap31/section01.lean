

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_31_1 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u

section

variable {𝕜 : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} {EStar : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasPairing E EStar 𝕜]
variable {f g : E → WithTopBot 𝕜}

local instance : HasPairing E EStar (WithTopBot 𝕜) := instHasPairingWithTopBot

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "IsClosedProperConcave[" 𝕜 "]" => @Function.IsClosedProperConcave 𝕜
local notation "primalObjective" => fun x : E ↦ f x - g x
local notation "convexDual" => (f⋆ : EStar → WithTopBot 𝕜)
local notation "concaveDual" => (g∗ : EStar → WithTopBot 𝕜)
local notation "primalRiQualification" => Set.Nonempty (riDom[𝕜](f) ∩ riDom[𝕜](-g))
local notation "dualRiQualification" =>
  Set.Nonempty (riDom[𝕜](-concaveDual) ∩ riDom[𝕜](convexDual))
local notation "primalFenchelQualification" =>
  f.IsConvex 𝕜 ∧ f.IsProper ∧ g.IsConcave 𝕜 ∧ g.IsProperConcave ∧ primalRiQualification
local notation "closedFenchelQualification" =>
  IsClosedProperConvex[𝕜] f ∧ IsClosedProperConcave[𝕜] g ∧ dualRiQualification
local notation "primalValue" => (⨅ x : E, primalObjective x)
local notation "dualObjective" => fun xStar : EStar ↦ concaveDual xStar - convexDual xStar
local notation "dualValue" => (⨆ xStar : EStar, dualObjective xStar)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 31.1 is the base Fenchel-duality theorem for the identity pairing
  problem `inf_x (f x - g x)` together with the branchwise attainment and finiteness conclusions.
- `core/canonical`: the owner abstractions already present upstream are
  `Function.IsClosedProperConvex`, `Function.IsClosedProperConcave`, the conjugates `f⋆` and
  `g∗`, and the effective-domain owner `riDom[𝕜](·)`.
- `bridge/view`: the theorem stays source-facing on the primal and dual objective functions, while
  the closed branch is phrased through the existing closed/proper owners rather than through a
  parallel local packaging layer.

Domain-style sampling used here:
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `Function.IsClosedProperConcave` and `concaveConjugate` from `Chap06.Definition_6_30_2` and
  `Chap06.Definition_6_30_4`;
- the convex conjugate owner `(·)⋆` from `Chap03.Defn_12_2`;
- the effective-domain owner `riDom[𝕜](·)` from `Chap01.Definition_4_4`.
- the Chapter 31 qualification owner layer from `Theorem_31_2`, `Lemma_31_0_9`,
  `Lemma_31_0_13`, and ultimately `Theorem_6_30_16`, now exposed here on the
  finite-dimensional topological-module pairing layer.

Primitive data vs derived API:
- primitive source data: the convex function `f`, the concave function `g`, and the paired dual
  space `EStar`;
- primitive owner data already upstream: closed/proper/convexity on the Chapter 12/6 owner layer,
  plus the two conjugation operators;
- derived API in this file: the zero-gap identity, branchwise attainment, and the finiteness
  consequences.

Layer target: `source-facing`, with the dual qualification kept as a theorem-level source
predicate on the canonical theorem surface, with the dual carrier `EStar` still explicit in the
binders because it is not recoverable from `f` and `g`.
-/

-- Proof sketch: combine weak duality for `x ↦ f x - g x` with the Chapter 31 perturbation
-- argument for the identity map. Condition (a) yields the primal strong-consistency side through
-- the relative-interior intersection, while condition (b) yields the dual strong-consistency side
-- through the conjugate-domain intersection after passing to the closed perturbation function.
/-- Theorem 31.1: for a proper convex function `f` and a proper concave function `g` on a
finite-dimensional topological module with pairing, the primal value `inf_x (f x - g x)` equals the
dual value `sup_xStar (g* xStar - f* xStar)` whenever either
(a) `f` is proper convex, `g` is proper concave, and `riDom[𝕜](f)` meets `riDom[𝕜](-g)`,
or (b) both `f` and `g` are closed proper, rendered by the canonical owners
`IsClosedProperConvex[𝕜] f` and `IsClosedProperConcave[𝕜] g`, and the conjugate-side relative
interiors `riDom[𝕜](-g∗)` and `riDom[𝕜](f⋆)` meet. -/
theorem iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification
    (hqual : primalFenchelQualification ∨ closedFenchelQualification) :
    primalValue = dualValue := sorry

-- Proof sketch: use the clause (a) qualification to obtain zero duality gap for the identity-map
-- Fenchel perturbation, then apply the Chapter 31 Kuhn-Tucker existence criterion on the dual side
-- to turn that zero-gap statement into an attained supremum.
/-- Under the relative-interior qualification (a), the dual supremum in Fenchel duality is
attained. -/
theorem exists_isMaxOn_concaveConjugate_sub_convexConjugate_of_riDom_inter_nonempty
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave)
    (hri : primalRiQualification) :
    ∃ xStar : EStar,
      IsMaxOn dualObjective Set.univ xStar := sorry

-- Proof sketch: under clause (b), first identify the common primal and dual values by Fenchel
-- duality for the closed identity-map perturbation. Then use the closed-case attainment criterion
-- to promote the finite perturbation value at `0` to a minimizer of `x ↦ f x - g x`.
/-- Under the conjugate-side qualification (b), the primal infimum in Fenchel duality is
attained. -/
theorem exists_isMinOn_sub_of_dual_riDom_inter_nonempty
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hri : dualRiQualification) :
    ∃ x : E, IsMinOn primalObjective Set.univ x := sorry

-- Proof sketch: combine the attainment conclusions from clauses (a) and (b) with the zero-gap
-- identity. The attained primal and dual values coincide, so each side is represented by a
-- finite scalar value in `𝕜` and hence is finite.
/-- If both Fenchel qualification clauses hold, then the primal infimum is finite. -/
theorem iInf_sub_finite_of_both_fenchel_qualifications
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hri_primal : primalRiQualification)
    (hri_dual : dualRiQualification) :
    ⊥ < primalValue ∧ primalValue < ⊤ := sorry

-- Proof sketch: the previous finiteness argument is symmetric under the zero-gap equality: once
-- both qualification clauses give primal and dual attainment, the common optimal value must also
-- be finite on the dual side.
/-- If both Fenchel qualification clauses hold, then the dual supremum is finite. -/
theorem iSup_concaveConjugate_sub_convexConjugate_finite_of_both_fenchel_qualifications
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hri_primal : primalRiQualification)
    (hri_dual : dualRiQualification) :
    ⊥ < dualValue ∧ dualValue < ⊤ := sorry

end

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
variable {E : Type u} {EStar : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasLinearPairing E EStar 𝕜]
variable {f g : E → WithTopBot 𝕜}

local instance : HasPairing E EStar (WithTopBot 𝕜) := instHasPairingWithTopBot
local notation "primalObjective" => fun x : E ↦ f x - g x
local notation "convexDual" => (f⋆ : EStar → WithTopBot 𝕜)
local notation "concaveDual" => (g∗ : EStar → WithTopBot 𝕜)
local notation "primalValue" => (⨅ x : E, primalObjective x)
local notation "dualObjective" => fun xStar : EStar ↦ concaveDual xStar - convexDual xStar
local notation "dualValue" => (⨆ xStar : EStar, dualObjective xStar)
local notation "primalPolyhedralGQualification" => Set.Nonempty (riDom[𝕜](f) ∩ dom(-g))
local notation "dualPolyhedralGQualification" =>
  Set.Nonempty (dom(-concaveDual) ∩ riDom[𝕜](convexDual))
local notation "primalPolyhedralFQualification" => Set.Nonempty (dom(f) ∩ riDom[𝕜](-g))
local notation "dualPolyhedralFQualification" =>
  Set.Nonempty (riDom[𝕜](-concaveDual) ∩ dom(convexDual))

/-!
Source/core/bridge triage for the polyhedral branch.

- `source-facing`: the final two theorems are the polyhedral qualification variants of
  Theorem 31.1, still stated directly as Fenchel-duality equalities for the primal objective
  `x ↦ f x - g x`.
- `core/canonical`: the relevant owner abstractions are `Function.HasPolyhedralEpigraph`,
  `dom(·)`, `riDom[𝕜](·)`, the conjugates `f⋆` and `g∗`, and the Chapter 31
  polyhedral separation owner
  `exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_dom_nonempty_of_polyhedral` from
  `Lemma_31_0_3`.
- `bridge/view`: these statements remain source-facing, but their ambient layer is refined to the
  actual owner level of the polyhedral weakening rather than a parallel weaker wrapper.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph` from `Chap04.Text_19_0_8`;
- `Function.HasPolyhedralEpigraph.isClosedProperConvex` from `Chap04.Corollary_19_1_2`;
- `exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_dom_nonempty_of_polyhedral` from
  `Chap06.Lemma_31_0_3`;
- `PairingNondegenerate` from `Chap06.Lemma_31_0_3`.

Primitive data vs derived API:
- primitive inputs: the convex/proper data on the nonpolyhedral side, the polyhedral-epigraph
  owner on the polyhedral side, and the nondegeneracy owner
  `PairingNondegenerate`;
- derived API: the zero-gap equality under the weakened domain/relative-interior qualifications.

Layer target: `source-facing`.
-/

-- Proof sketch: in the polyhedral `g` case, replace the `g`-side relative interiors in the two
-- Fenchel qualification clauses by ordinary effective domains. The weakening is justified through
-- the Chapter 31 polyhedral separation owner, so the theorem must live on the same nondegenerate
-- finite-dimensional topological-module linear-pairing layer and carry the canonical
-- nondegeneracy owner.
/-- If `g` is polyhedral, the `g`-side relative-interior conditions in the main Fenchel duality
statement may be weakened to ordinary effective-domain conditions, and the closure requirement on
`g` in clause (b) is unnecessary, provided the Chapter 31 nondegenerate linear-pairing
assumptions used for the polyhedral weakening are available. -/
theorem iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_polyhedral_g_qualification
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_proper : g.IsProperConcave)
    (hg_poly : (-g).HasPolyhedralEpigraph)
    (hpair_nondegenerate : PairingNondegenerate)
    (hqual :
      primalPolyhedralGQualification ∨ dualPolyhedralGQualification) :
    primalValue = dualValue := sorry

-- Proof sketch: this is the symmetric polyhedral refinement of the previous theorem, replacing
-- the `f`-side relative interiors in the qualification clauses by ordinary effective domains and
-- then applying the same Chapter 31 polyhedral separation argument. Consequently the theorem
-- inherits the same finite-dimensional topological-module ambient and pairing nondegeneracy owner.
/-- If `f` is polyhedral, the `f`-side relative-interior conditions in the main Fenchel duality
statement may be weakened to ordinary effective-domain conditions, and the closure requirement on
`f` in clause (b) is unnecessary, again on the nondegenerate linear-pairing owner layer required
by the polyhedral separation theorem. -/
theorem iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_polyhedral_f_qualification
    (hf_proper : f.IsProper)
    (hg_concave : g.IsConcave 𝕜) (hg_proper : g.IsProperConcave)
    (hf_poly : f.HasPolyhedralEpigraph)
    (hpair_nondegenerate : PairingNondegenerate)
    (hqual :
      primalPolyhedralFQualification ∨ dualPolyhedralFQualification) :
    primalValue = dualValue := sorry

end
