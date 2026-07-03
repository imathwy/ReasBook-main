import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_30_1 (from Chap06) -/
noncomputable section

open Function
open scoped Rockafellar

universe u v u' v'

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.30.1 says that inconsistency of the dual program is equivalent to
  some primal slice `F u` being unbounded below, while inconsistency of the primal program is
  equivalent to some adjoint slice `F* x⋆` being unbounded above.
- `core/canonical`: the chapter owners already present are `IsConsistent`, `adjoint`,
  `perturbationFunction`, and `upperPerturbationFunction`.
- `bridge/view`: the textbook phrases “has no lower bound” and “has no upper bound” are rendered
  canonically by the extended-order slice values `perturbationFunction F u = ⊥` and
  `supᵇ(F⋆) x⋆ = ⊤`.

Domain-style sampling used here:
- `IsConsistent` from Definition 6.29.1;
- `adjoint` from Definition 6.30.14;
- `upperPerturbationFunction` from Definition 6.30.11;
- the two conjugacy identities from Theorem 6.30.15.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜` on pairing spaces
  `(U, UStar)` and `(X, XStar)`;
- canonical owners: primal consistency `IsConsistent F` and dual consistency
  `IsConsistent (adjoint F)`;
- derived source-facing conclusions: existence of a primal slice with infimum `⊥`, and existence
  of an adjoint slice with supremum `⊤`.

Layer target: `bridge/view`, stated directly on the canonical Chapter 6 owners without introducing
any separate package for primal or dual programs.
-/

section

variable {𝕜 : Type*}
variable [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

-- Proof sketch: dual inconsistency means the zero slice `objective (adjoint F)` is
-- everywhere `⊤`. Apply the first conjugacy identity from Theorem 6.30.15,
-- `concaveConjugate (- perturbationFunction F) = objective (adjoint F)`, and use the
-- defining infimum formula for the concave conjugate to identify this with existence of some
-- parameter `u` where `perturbationFunction F u = ⊥`.
/-- Corollary 6.30.1 (1): the dual program associated with `F` is inconsistent exactly when some
primal slice `F u` has no lower bound, rendered canonically by
`perturbationFunction F u = ⊥`. -/
theorem not_isConsistent_adjointFunction_iff_exists_perturbationFunction_eq_bot
    :
    ¬ IsConsistent ((F⋆) : XStar → UStar → WithBotTop 𝕜) ↔
      ∃ u : U, perturbationFunction F u = ⊥ := sorry

end

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [Neg UStar] [AddCommMonoid UStar] [Module 𝕜 UStar]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "IsClosedProperConvex[" 𝕜 "]" =>
  Function.IsClosedProperConvex (𝕜 := 𝕜)

-- Proof sketch: primal inconsistency means the zero slice `objective F` is everywhere `⊤`.
-- For a closed proper convex bifunction, Theorem 6.30.15 identifies `objective F` with the
-- Fenchel conjugate of `- supᵇ(F⋆)`. A Fenchel conjugate is
-- identically `⊤` exactly when the underlying function takes the value `⊥` somewhere, i.e. when
-- `supᵇ(F⋆)` takes the value `⊤` at some dual point.
/-- Corollary 6.30.1 (2): the primal program associated with a closed proper convex bifunction
`F` is inconsistent exactly when some adjoint slice `F* x⋆` has no upper bound, rendered
canonically by `supᵇ(F⋆) x⋆ = ⊤`. -/
theorem not_isConsistent_iff_exists_upperPerturbationFunction_adjoint_eq_top
    (hF : IsClosedProperConvex[𝕜] (uncurry F)) :
    ¬ IsConsistent F ↔
      ∃ xStar : XStar, supᵇ(((F⋆) : XStar → UStar → WithBotTop 𝕜)) xStar = ⊤ := sorry

end

end Bifunction

/-! ### Definition_6_30_1 (from Chap06) -/
universe u

section

variable {E : Type u}
variable {β : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 6.30.1 introduces the hypograph of a concave function and recalls
  its effective domain.
- `core/canonical`: the relevant owner abstractions are the raw hypograph set
  `{p : E × β | p.1 ∈ S ∧ p.2 ≤ g p.1}`, the Chapter 1 effective-domain owner `dom(·)`, and
  mathlib's concavity/hypograph API `ConcaveOn.convex_hypograph` and
  `concaveOn_iff_convex_hypograph`.
- `bridge/view`: the chapter owner `hypo` (with restricted notation `hypo[S] g`) is the
  source-facing hypograph layer. The effective-domain bridge
  `x ∈ dom(-g) ↔ ⊥ < g x` is part of the Chapter 1 `dom(·)` owner API and is reused downstream.

Domain-style sampling used here:
- `epigraph` and `mem_epi_restrict_iff` from Chapter 1;
- `effectiveDomain`, `dom(·)`, `mem_effectiveDomain`, `mem_dom_neg_iff`,
  and `dom_neg_eq_setOf_bot_lt` from Chapter 1;
- `ConcaveOn.convex_hypograph` and `concaveOn_iff_convex_hypograph` from mathlib.

Primitive data vs derived API:
- primitive new owner: `hypo g S`;
- reused owner for the domain clause: `dom(-g)`, with its canonical Chapter 1 bridge lemmas;
- derived API: the membership simplifications for `hypo`, plus bridge lemmas
  `ConcaveOn.convex_hypo` and `concaveOn_iff_convex_hypo` re-expressing mathlib's raw
  hypograph-set characterization on the chapter owner surface.

Layer target:
- `source-facing` for `hypo`;
- `bridge/view` for the effective-domain clause, which reuses `dom(-g)` from the owner file
  `Definition_4_4` rather than introducing a Chapter 6-local duplicate.

Notation evaluation:
- the book writes the hypograph as `exp g`, but that notation clashes with Lean's exponential API;
  this file therefore uses the chapter-parallel owner name `hypo`, matching `epi`.
-/

/-- Definition 6.30.1: the hypograph of an ordered-valued function on a subset is the set
of pairs `(x, μ)` with `x ∈ S` and `μ ≤ g x`. -/
def hypo [LE β] (g : E → β) (S : Set E := Set.univ) : Set (E × β) :=
  {p : E × β | p.1 ∈ S ∧ p.2 ≤ g p.1}

/-- Chapter-parallel notation for the hypograph of `g` restricted to `S`. -/
notation:max "hypo[" S "] " g => hypo g S

/-- The restricted hypograph owner `hypo[S] g` is the set of pairs with base point in `S` and
height below `g`. -/
theorem hypo_eq_setOf_mem_and_le [LE β] (g : E → β) (S : Set E) :
    (hypo[S] g) = {p : E × β | p.1 ∈ S ∧ p.2 ≤ g p.1} :=
  rfl

/-- Restricting the hypograph owner to `S` is equivalent to intersecting the global hypograph with
the first-coordinate preimage of `S`. -/
theorem hypo_restrict_eq_preimage_fst_inter [LE β] (g : E → β) (S : Set E) :
    (hypo[S] g) = (Prod.fst ⁻¹' S) ∩ hypo g := by
  ext p
  rcases p with ⟨x, μ⟩
  simp [hypo]

/-- Restricting the hypograph owner to `Set.univ` gives the global hypograph. -/
@[simp] theorem hypo_univ [LE β] (g : E → β) :
    (hypo[Set.univ] g) = hypo g :=
  rfl

/-- Membership in `hypo[S] g` is the intrinsic owner-level pair condition. -/
@[simp] theorem mem_hypo_restrict_iff [LE β]
    {S : Set E} {g : E → β} {p : E × β} :
    p ∈ (hypo[S] g) ↔ p.1 ∈ S ∧ p.2 ≤ g p.1 :=
  Iff.rfl

/-- Coordinate view of membership in `hypo[S] g`. -/
@[simp] theorem mk_mem_hypo_restrict_iff [LE β]
    {S : Set E} {g : E → β} {x : E} {μ : β} :
    (x, μ) ∈ (hypo[S] g) ↔ x ∈ S ∧ μ ≤ g x :=
  Iff.rfl

/-- Membership in the global hypograph `hypo g` is the intrinsic pair inequality. -/
@[simp] theorem mem_hypo_iff [LE β] {g : E → β} {p : E × β} :
    p ∈ hypo g ↔ p.2 ≤ g p.1 := by
  rcases p with ⟨x, μ⟩
  simp [hypo]

/-- Coordinate view of membership in the global hypograph `hypo g`. -/
@[simp] theorem mk_mem_hypo_iff [LE β] {g : E → β} {x : E} {μ : β} :
    (x, μ) ∈ hypo g ↔ μ ≤ g x :=
  mem_hypo_iff (g := g) (p := (x, μ))

/-- Monotonicity in the restriction set for the hypograph owner. -/
theorem hypo_mono [LE β] {S T : Set E} {g : E → β} (hST : S ⊆ T) :
    (hypo[S] g) ⊆ (hypo[T] g) := by
  intro p hp
  exact ⟨hST hp.1, hp.2⟩

/-- The global hypograph `hypo g` is the set `{(x, μ) | μ ≤ g x}`. -/
theorem hypo_univ_eq_setOf_le [LE β] (g : E → β) :
    (hypo g) = {p : E × β | p.2 ≤ g p.1} := by
  simpa [hypo_univ] using (hypo_eq_setOf_mem_and_le (g := g) (S := Set.univ))

section ConvexBridge

variable {𝕜 : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β]
variable [Module 𝕜 β] [PosSMulMono 𝕜 β]
variable {s : Set E} {g : E → β}

/-- Bridge to mathlib's concavity API: a concave map has convex restricted hypograph owner
`hypo[s] g`. -/
theorem ConcaveOn.convex_hypo (hg : ConcaveOn 𝕜 s g) :
    Convex 𝕜 (hypo[s] g) := by
  simpa [hypo] using hg.convex_hypograph

/-- Bridge to mathlib's canonical characterization: concavity on `s` is equivalent to convexity
of the restricted hypograph owner `hypo[s] g`. -/
theorem concaveOn_iff_convex_hypo :
    ConcaveOn 𝕜 s g ↔ Convex 𝕜 (hypo[s] g) := by
  simpa [hypo] using (concaveOn_iff_convex_hypograph (𝕜 := 𝕜) (s := s) (f := g))

end ConvexBridge

end

/-! ### Theorem_6_30_1 (from Chap06) -/
noncomputable section

universe u

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.1 identifies closedness of a concave function with the fixed-point
  equation `concaveClosure g = g`, equivalently `cl(-g) = -g` on the convex side.
- `core/canonical`: the chapter closure owner is `concaveClosure`, and convex-side closedness is
  the standard lower-semicontinuity/fixed-point API for `lowerSemicontinuousHull`, written `cl(·)`.
- `bridge/view`: negation converts the concave closure fixed-point equation into the convex closure
  fixed-point equation for `-g`.

Primary mathematical domain:
- closedness and closure operators for extended-real-valued concave functions on topological
  spaces.

Domain-style sampling used here:
- `concaveClosure`;
- `concaveClosure_eq_neg_lowerSemicontinuousHull_neg`;
- `lowerSemicontinuousHull_eq_self`;
- `lowerSemicontinuous_lowerSemicontinuousHull`.

Primitive data vs derived API:
- primitive owner: `concaveClosure g`;
- derived API: the source-facing fixed-point equivalence
  `concaveClosure g = g ↔ cl(-g) = -g`, and its thin lower-semicontinuity companion obtained from
  the Chapter 2 owner theorem for `cl(·)`.

Layer target: `source-facing` for the fixed-point theorem, with a `bridge/view` companion to
`LowerSemicontinuous (-g)`.
-/

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddGroup 𝕜]
variable {E : Type u} [TopologicalSpace E]

-- Proof sketch: unfold `concaveClosure g = - cl(-g)` pointwise and negate the resulting equality.
-- This turns the fixed-point equation for `concaveClosure` into the fixed-point equation
-- `cl(-g) = -g` for the convex-side closure of the negated function.
/-- Theorem 6.30.1: a concave extended-real-valued function is closed exactly when its concave
closure fixes it; equivalently, the convex-side closure of the negated function is already `-g`. -/
theorem concaveClosure_eq_self_iff_cl_neg_eq_neg
    (g : E → WithBotTop 𝕜) :
    concaveClosure g = g ↔ cl(-g) = -g := by
  rw [concaveClosure_eq_neg_lowerSemicontinuousHull_neg g]
  constructor
  · intro h
    ext x
    have hx : -(cl(-g) x) = g x := congrArg (fun f ↦ f x) h
    simpa using congrArg Neg.neg hx
  · intro h
    ext x
    have hx : cl(-g) x = -g x := congrArg (fun f ↦ f x) h
    simpa using congrArg Neg.neg hx

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddCommGroup 𝕜]
variable {E : Type u} [TopologicalSpace E]
variable [NoMinOrder 𝕜] [Nonempty 𝕜]
variable [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
variable [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜] [NoBotOrder 𝕜]

-- Proof sketch: combine the source-facing fixed-point equivalence above with the Chapter 2 owner
-- theorem `LowerSemicontinuous f ↔ cl(f) = f`, applied to `f := -g`.
/-- Companion bridge: the source-facing closedness equation from Theorem 6.30.1 is equivalent to
lower semicontinuity of the negated function. -/
theorem concaveClosure_eq_self_iff_lowerSemicontinuous_neg
    (g : E → WithBotTop 𝕜) :
    concaveClosure g = g ↔ LowerSemicontinuous (-g) := by
  rw [concaveClosure_eq_self_iff_cl_neg_eq_neg]
  constructor
  · intro hg
    simpa [hg] using lowerSemicontinuous_lowerSemicontinuousHull (-g)
  · intro hg
    exact lowerSemicontinuousHull_eq_self hg

/-- Symmetric bridge form of Theorem 6.30.1 used by downstream fixed-point proofs. -/
theorem lowerSemicontinuous_neg_iff_concaveClosure_eq_self
    (g : E → WithBotTop 𝕜) :
    LowerSemicontinuous (-g) ↔ concaveClosure g = g :=
  (concaveClosure_eq_self_iff_lowerSemicontinuous_neg g).symm

end

end

/-! ### Corollary_6_30_2 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v v'

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.30.2 evaluates at `0` the primal perturbation function `inf F`,
  the dual upper perturbation function `sup F*`, and the zero-slice objectives `F₀` and `F*₀`,
  concluding the primal-dual value inequality `inf F0 ≥ sup F*0`.
- `core/canonical`: the owner declarations already present in Chapter 6 are
  `perturbationFunction`, `upperPerturbationFunction`/`supᵇ(·)`, `objective`, `adjoint`,
  `concaveClosure`, and the convex closure `cl(·)`.
- `bridge/view`: the source writes `sup F*0` and `inf F0`; these are rendered canonically as
  `sSup (Set.range ((F⋆)₀))` and `sInf (Set.range ((F)₀))`.

Domain-style sampling used here:
- `perturbationFunction` and `objective` from Definitions 6.29.1 and 6.29.12;
- the scoped zero-slice notation `(·)₀` from Definition 6.29.12;
- `upperPerturbationFunction` / `supᵇ(·)` from Definition 6.30.11;
- `adjoint` from Definition 6.30.14;
- the conjugacy identities of Theorem 6.30.15.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owners already upstream: `perturbationFunction F`,
  `supᵇ(F⋆)`, `(F)₀`, and `(F⋆)₀`;
- derived API added here: the five value identities at `0` and the resulting primal-dual
  inequality.

Layer target: `source-facing`, stated directly on the established Chapter 6 owners with no extra
program package or wrapper for optimal values.
-/

section ClPrimalEqDualAtZero

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Zero XStar]
variable [HasLinearPairing U U 𝕜] [HasContinuousPairing U U 𝕜]
variable [HasPairing X XStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar U F

-- Proof sketch: apply the first closed-value identity from Theorem 6.30.15 to `F` and evaluate
-- the resulting concave-conjugate formula at `0`; at the origin, the concave conjugate rewrites
-- the dual zero-slice objective as the upper perturbation value
-- `supᵇ(F⋆) 0`.
/-- Corollary 6.30.2 (1): for a convex bifunction `F`, the closure of the primal perturbation
value at `0` equals the dual upper perturbation value at `0`, i.e.
`(cl (inf F))(0) = (sup F^*)(0)`. -/
theorem cl_perturbationFunction_zero_eq_upperPerturbationFunction_adjoint_zero
    (hF_convex : (Function.uncurry F).IsConvex 𝕜) :
    cl(perturbationFunction F) 0 =
      supᵇ(F⋆) 0 := sorry

end ClPrimalEqDualAtZero

-- Proof sketch: this is the owner theorem
-- `Bifunction.upperPerturbationFunction_zero_eq_sSup_range_objective` specialized to `F⋆`.
/- Corollary 6.30.2 (2): the dual upper perturbation value at `0` is the supremum of the dual
zero-slice objective `F^*_0`, i.e. `(sup F^*)(0) = sup F^*0`. -/
recall upperPerturbationFunction_zero_eq_sSup_range_objective

section ConcaveClosureDualEqPrimalAtZero

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
variable [TopologicalSpace X] [AddCommMonoid X] [Module 𝕜 X]
variable [TopologicalSpace XStar] [Zero XStar]
variable [HasLinearPairing U U 𝕜] [HasContinuousPairing U U 𝕜]
variable [HasPairing X XStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar U F

-- Proof sketch: combine the second closed-value identity from Theorem 6.30.15 with the
-- graph-function closedness of `F`, then evaluate the resulting conjugate-side equality at `0`.
/-- Corollary 6.30.2 (3): for a closed convex bifunction `F`, the concave closure of the dual
upper perturbation function at `0` equals the primal perturbation value at `0`. -/
theorem concaveClosure_upperPerturbationFunction_adjoint_zero_eq_perturbationFunction_zero
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F)) :
    concaveClosure (supᵇ(F⋆)) 0 =
      perturbationFunction F 0 := sorry

end ConcaveClosureDualEqPrimalAtZero

-- Proof sketch: unfold the perturbation function at `0`; by definition it is the infimum over
-- the `X`-slice `x ↦ F 0 x`, which is exactly the primal zero-slice objective `(F)₀`.
/- Corollary 6.30.2 (4) is already the canonical owner theorem
`Bifunction.perturbationFunction_zero_eq_sInf_range`. -/
recall perturbationFunction_zero_eq_sInf_range

section PrimalValueGeDualValue

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Zero XStar]
variable [HasPairing U U 𝕜] [HasPairing X XStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar U F

-- Proof sketch: combine clauses (1), (2), and the owner theorem
-- `perturbationFunction_zero_eq_sInf_range` with the basic inequality
-- `cl(perturbationFunction F) 0 ≤ perturbationFunction F 0`, then rewrite both sides through the
-- objective-range formulas.
/-- Corollary 6.30.2 (5): the primal optimal value dominates the dual optimal value,
`inf F0 ≥ sup F^*0`. -/
theorem sInf_range_objective_ge_sSup_range_objective_adjointFunction
    (hF_convex : (Function.uncurry F).IsConvex 𝕜) :
    sInf (Set.range ((F)₀)) ≥
      sSup (Set.range ((F⋆)₀)) := sorry

end PrimalValueGeDualValue

end Bifunction

/-! ### Definition_6_30_2 (from Chap06) -/
noncomputable section

universe u

open scoped Rockafellar

section

variable {𝕜 : Type*} [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜] [Neg 𝕜]
variable {E : Type u} [TopologicalSpace E]

/-- Definition 6.30.2: the concave closure is the sign-dual of the convex closure. -/
def concaveClosure (g : E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  fun x ↦ -(cl(-g) x)

/-- Owner equation for concave closure. -/
theorem concaveClosure_eq_neg_lowerSemicontinuousHull_neg (g : E → WithTopBot 𝕜) :
    concaveClosure g = fun x ↦ -(cl(-g) x) :=
  rfl

end

section

variable (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {α : Type*} [AddCommGroup α] [SMul 𝕜 α] [LE α]

namespace Function

/-- Concavity is encoded via convexity of the negated function. -/
abbrev IsConcave (g : E → WithTopBot α) : Prop :=
  (-g).IsConvex 𝕜

/-- Sign-dual bridge from concavity to convexity of the negated function. -/
theorem IsConcave.convex_neg {g : E → WithTopBot α} (hg : g.IsConcave 𝕜) :
    (-g).IsConvex 𝕜 :=
  hg

end Function

end

section

variable {E : Type u}
variable {α : Type*} [Neg α] [Preorder α]

namespace Function

/-- Proper concavity is encoded via properness of the negated function. -/
abbrev IsProperConcave (g : E → WithTopBot α) : Prop :=
  (-g).IsProper

/-- Definitional bridge between proper concavity and properness of `-g`. -/
theorem isProperConcave_iff (g : E → WithTopBot α) :
    g.IsProperConcave ↔ (-g).IsProper :=
  Iff.rfl

namespace IsProperConcave

/-- Proper concavity directly provides properness of `-g`. -/
theorem neg_isProper {g : E → WithTopBot α} (hg : g.IsProperConcave) :
    (-g).IsProper :=
  hg

end IsProperConcave

end Function

end

section

variable (𝕜 : Type*) [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [SMul 𝕜 E]
variable {α : Type*}
variable [TopologicalSpace (WithTopBot α)] [AddCommGroup α] [SMul 𝕜 α] [Preorder α]

namespace Function

/-- Closed-proper-concave owner on the Chapter 12 codomain layer, encoded as
closed-proper-convexity of the negated function. -/
abbrev IsClosedProperConcave (g : E → WithTopBot α) : Prop :=
  Function.IsClosedProperConvex (𝕜 := 𝕜) (-g)

local notation "IsClosedProperConcave[" 𝕜 "]" => Function.IsClosedProperConcave (𝕜 := 𝕜)
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-- Definitional bridge between closed proper concavity and closed proper convexity of `-g`. -/
theorem isClosedProperConcave_iff (g : E → WithTopBot α) :
    IsClosedProperConcave[𝕜] g ↔ IsClosedProperConvex[𝕜] (-g) :=
  Iff.rfl

namespace IsClosedProperConcave

/-- Closed proper concavity directly provides closed proper convexity of `-g`. -/
theorem neg_isClosedProperConvex {g : E → WithTopBot α}
    (hg : IsClosedProperConcave[𝕜] g) :
    IsClosedProperConvex[𝕜] (-g) :=
  hg

end IsClosedProperConcave

end Function

end

section

variable {𝕜 : Type*} [Ring 𝕜] [Preorder 𝕜]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

/-- Affine majorants of a `WithTopBot`-valued function. -/
abbrev AffineMajorant (g : E → WithTopBot 𝕜) :=
  {h : AffineMap 𝕜 E 𝕜 // g ≤ h.toWithBotTop}

instance {g : E → WithTopBot 𝕜} : CoeFun (AffineMajorant g) (fun _ ↦ E → 𝕜) where
  coe h := (h : AffineMap 𝕜 E 𝕜)

namespace AffineMajorant

/-- Coercion-free `WithTopBot`-valued view of an affine majorant. -/
abbrev toWithTopBot {g : E → WithTopBot 𝕜} (h : AffineMajorant g) : E → WithTopBot 𝕜 :=
  (h : AffineMap 𝕜 E 𝕜).toWithBotTop

@[simp] theorem toWithTopBot_apply {g : E → WithTopBot 𝕜} (h : AffineMajorant g) (x : E) :
    h.toWithTopBot x = ((h x : 𝕜) : WithTopBot 𝕜) :=
  rfl

end AffineMajorant

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [Ring 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

/-- Bridge form: once `cl(-g)` is identified as the pointwise supremum of affine minorants of
`-g`, the concave closure is the pointwise infimum of affine majorants of `g`. -/
theorem concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant
    (g : E → WithTopBot 𝕜) (x : E)
    (hcl : cl(-g) x = ⨆ h : AffineMinorant (-g), h.toWithBotTop x) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  have hneg_iSup :
      -(⨆ h : AffineMinorant (-g), h.toWithBotTop x) =
        ⨅ h : AffineMinorant (-g), -h.toWithBotTop x := by
    exact
      congrArg OrderDual.ofDual
        (WithTopBot.negOrderIso.map_iSup (fun h : AffineMinorant (-g) ↦ h.toWithBotTop x))
  have hle_majorants :
      -(⨆ h : AffineMinorant (-g), h.toWithBotTop x) ≤
        ⨅ h : AffineMajorant g, h.toWithTopBot x := by
    refine le_iInf ?_
    intro hMaj
    let hMin : AffineMinorant (-g) :=
      ⟨-hMaj.1, by
        intro y
        have hy : g y ≤ hMaj.toWithTopBot y := hMaj.property y
        simpa [AffineMajorant.toWithTopBot, AffineMinorant.toWithBotTop] using
          (WithTopBot.neg_le_neg_iff.2 hy)⟩
    have hMin_le :
        hMin.toWithBotTop x ≤ ⨆ h : AffineMinorant (-g), h.toWithBotTop x :=
      le_iSup_of_le hMin le_rfl
    have hneg_le : -(⨆ h : AffineMinorant (-g), h.toWithBotTop x) ≤ -hMin.toWithBotTop x :=
      (WithTopBot.neg_le_neg_iff.2 hMin_le)
    simpa [hMin, AffineMajorant.toWithTopBot, AffineMinorant.toWithBotTop] using hneg_le
  have hle_minorants :
      (⨅ h : AffineMajorant g, h.toWithTopBot x) ≤
        ⨅ h : AffineMinorant (-g), -h.toWithBotTop x := by
    refine le_iInf ?_
    intro hMin
    let hMaj : AffineMajorant g :=
      ⟨-hMin.1, by
        intro y
        have hy : hMin.toWithBotTop y ≤ (-g) y := hMin.property y
        simpa [AffineMajorant.toWithTopBot, AffineMinorant.toWithBotTop] using
          (WithTopBot.neg_le_neg_iff.2 hy)⟩
    have hMaj_le :
        (⨅ h : AffineMajorant g, h.toWithTopBot x) ≤ hMaj.toWithTopBot x :=
      iInf_le _ hMaj
    simpa [hMaj, AffineMajorant.toWithTopBot, AffineMinorant.toWithBotTop] using hMaj_le
  have hle_minorants_to_majorants :
      (⨅ h : AffineMinorant (-g), -h.toWithBotTop x) ≤
        ⨅ h : AffineMajorant g, h.toWithTopBot x := by
    simpa [hneg_iSup] using hle_majorants
  calc
    concaveClosure g x = -(cl(-g) x) := rfl
    _ = -(⨆ h : AffineMinorant (-g), h.toWithBotTop x) := by rw [hcl]
    _ = ⨅ h : AffineMinorant (-g), -h.toWithBotTop x := hneg_iSup
    _ = ⨅ h : AffineMajorant g, h.toWithTopBot x :=
      le_antisymm hle_minorants_to_majorants hle_minorants

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [Ring 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

namespace Function

/-- Generic bridge form: once `cl(-g)` is identified as the pointwise supremum of affine
minorants of `-g`, the concave closure is the pointwise infimum of affine majorants of `g`. -/
theorem concaveClosure_eq_iInf_affineMajorant
    {g : E → WithTopBot 𝕜} (x : E)
    (hcl : cl(-g) x = ⨆ h : AffineMinorant (-g), h.toWithBotTop x) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  exact concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant g x hcl

end Function

end

section

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [CommRing 𝕜]
variable [IsStrictOrderedRing 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable {Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasPairing Y E 𝕜] [HasPairingSwap E Y 𝕜]

namespace Function

/-- Primitive bridge form: if a dual-pairing biconjugate identity for `-g` is available and
affine minorants of `-g` admit the pairing normal form, then the concave closure of `g` is the
pointwise infimum of its affine majorants. -/
theorem concaveClosure_eq_iInf_affineMajorant_of_neg_eq_biconjugate
    {g : E → WithTopBot 𝕜} (x : E)
    (hg_biconj : (((-g)⋆ : Y → WithTopBot 𝕜)⋆ : E → WithTopBot 𝕜) = cl(-g))
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable (-g)) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  have hclCanon :
      cl(-g) x = ⨆ h : AffineMinorant (-g), h.toWithBotTop x := by
    calc
      cl(-g) x = (((-g)⋆ : Y → WithTopBot 𝕜)⋆ : E → WithTopBot 𝕜) x := by
        simpa using congrArg (fun f : E → WithTopBot 𝕜 ↦ f x) hg_biconj.symm
      _ = ⨆ h : AffineMinorant (-g), h.toWithBotTop x :=
        biconjugate_apply_eq_iSup_affineMinorant
          (-g) x h_affine
  exact concaveClosure_eq_iInf_affineMajorant x hclCanon

end Function

end

section

variable {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [Field 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [IsStrictOrderedRing 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasPairingSwap E E 𝕜]

namespace Function.IsConcave

/-- For a concave function `g`, the closure `ḡ` is the pointwise infimum of all affine majorants
of `g`, obtained by discharging the affine-minorant representation bridge from Theorem 12.1 on
the finite-dimensional scalar-field pairing layer. -/
theorem concaveClosure_eq_iInf_affineMajorant_of_pairingSubConstRepresentable
    {g : E → WithTopBot 𝕜} (hg : g.IsConcave 𝕜) (x : E)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable (-g)) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  exact Function.concaveClosure_eq_iInf_affineMajorant_of_neg_eq_biconjugate
    x hg.convex_neg.biconjugate_eq_lowerSemicontinuousHull h_affine

end Function.IsConcave

end

/-! ### Theorem_6_30_2 (from Chap06) -/
universe u

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.2 identifies the chapter concave-closure fixed-point equation
  `concaveClosure g = g` with upper semicontinuity of `g` and closedness of every real upper
  level set of `g`, and it asserts convexity of those upper level sets under concavity.
- `core/canonical`: the Chapter 6 owner `concaveClosure`, mathlib's `UpperSemicontinuous`, the
  Chapter 6 owner `Function.IsConcave`, and the Chapter 1 owner `Function.IsConvex`.
- `bridge/view`: negation turns upper level sets of `g` into sublevel sets of `-g`; the
  convex-side fixed-point equation `cl(-g) = -g` is used only as a proof bridge, matching the
  companion source-facing bridge isolated in Theorem 6.30.1.

Primary mathematical domain:
- upper semicontinuity and upper level sets of `WithBotTop α`-valued concave functions, with the
  textbook `EReal` / `ℝ` surface recovered by specialization.

Domain-style sampling used here:
- `concaveClosure`;
- `lowerSemicontinuousHull` / the notation `cl(·)`;
- `upperSemicontinuous_iff_isClosed_preimage`;
- `lowerSemicontinuous_iff_isClosed_sublevel`;
- `Function.IsConcave` and `Function.IsConcave.convex_neg`;
- `Function.IsConvex.convex_le`.

Primitive data vs. derived API:
- primitive owners for part (1): `concaveClosure g` and `UpperSemicontinuous g` on the canonical
  codomain layer `WithBotTop α`;
- source hypothesis used only for part (2): `g.IsConcave 𝕜`;
- derived API: the closed-scalar-upper-level-set characterization, the convex-side bridge
  `LowerSemicontinuous (-g)`, and the convexity of those upper level sets; the convexity of `-g`
  is used only internally via `hg.convex_neg`.

Layer target:
- part (1): `source-facing` on the textbook `EReal` specialization, obtained from a
  `bridge/view` theorem at the generic `WithBotTop α` owner layer;
- part (2): `bridge/view`, via the chapter owner `Function.IsConcave`.
-/

section

variable {α : Type*} [LinearOrder α]
variable {E : Type u} [TopologicalSpace E]

/-- Companion owner form: a `WithBotTop α`-valued function is upper semicontinuous exactly when
all of its scalar upper level sets are closed. -/
theorem upperSemicontinuous_iff_isClosed_upperLevelSets
    [NoMaxOrder α] [Nonempty α] (g : E → WithBotTop α) :
    UpperSemicontinuous g ↔ ∀ a : α, IsClosed (g ⁻¹' Set.Ici (a : WithBotTop α)) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  constructor
  · intro hg a
    simpa using hg (a : WithBotTop α)
  · intro h y
    change WithBot (WithTop α) at y
    induction y using WithBot.recBotCoe with
    | bot => simp
    | coe y =>
        induction y using WithTop.recTopCoe with
        | top =>
            have hpreimage_eq :
                g ⁻¹' Set.Ici (⊤ : WithBotTop α) = ⋂ a : α, g ⁻¹' Set.Ici (a : WithBotTop α) := by
              ext x
              simp only [Set.mem_preimage, Set.mem_iInter, Set.mem_Ici]
              constructor
              · intro hx a
                exact le_trans (by simp) hx
              · intro hx
                by_cases htop : g x = ⊤
                · simp [htop]
                · cases hgx : g x using WithBotTop.rec with
                  | bot =>
                      exfalso
                      let a : α := Classical.choice ‹Nonempty α›
                      have hxa : (a : WithBotTop α) ≤ g x := hx a
                      simp [hgx] at hxa
                  | coe b =>
                      exfalso
                      rcases exists_gt b with ⟨a, hba⟩
                      have hxa : (a : WithBotTop α) ≤ g x := hx a
                      rw [hgx] at hxa
                      exact (not_le_of_gt hba) (WithBotTop.coe_le_coe.mp hxa)
                  | top => exact (htop hgx).elim
            rw [show ((⊤ : WithTop α) : WithBot (WithTop α)) = (⊤ : WithBotTop α) by rfl]
            rw [hpreimage_eq]
            exact isClosed_iInter h
        | coe a =>
            simpa using h a

end

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [AddCommGroup 𝕜]
variable {E : Type u} [TopologicalSpace E]
variable [NoMinOrder 𝕜] [Nonempty 𝕜] [OrderTopology 𝕜]
variable [DenselyOrdered 𝕜] [NoMaxOrder 𝕜] [AddLeftMono 𝕜] [AddRightMono 𝕜] [ContinuousAdd 𝕜]
variable [NoBotOrder 𝕜] [IsOrderedAddMonoid 𝕜]

/-- Companion bridge: on the canonical `WithBotTop 𝕜` codomain layer, the Chapter 6
concave-closure fixed-point equation is equivalent to upper semicontinuity. -/
theorem concaveClosure_eq_self_iff_upperSemicontinuous
    (g : E → WithBotTop 𝕜) :
    concaveClosure g = g ↔ UpperSemicontinuous g := by
  rw [concaveClosure_eq_self_iff_lowerSemicontinuous_neg]
  rw [lowerSemicontinuous_iff_isClosed_sublevel_withBotTop,
    upperSemicontinuous_iff_isClosed_upperLevelSets]
  constructor
  · intro h a
    have hs :
        {x : E | (-g) x ≤ (((-a : 𝕜) : WithBotTop 𝕜))} =
          g ⁻¹' Set.Ici (a : WithBotTop 𝕜) := by
      ext x
      simpa [Set.mem_preimage] using
        (show -g x ≤ (((-a : 𝕜) : WithBotTop 𝕜)) ↔ (a : WithBotTop 𝕜) ≤ g x from
          WithBotTop.neg_le)
    simpa [hs] using h (-a)
  · intro h a
    have hs :
        {x : E | (-g) x ≤ (a : WithBotTop 𝕜)} =
          g ⁻¹' Set.Ici (-((a : 𝕜) : WithBotTop 𝕜)) := by
      ext x
      simpa [Set.mem_preimage] using
        (show -g x ≤ (a : WithBotTop 𝕜) ↔ (-((a : 𝕜) : WithBotTop 𝕜)) ≤ g x from
          WithBotTop.neg_le)
    simpa using hs.symm ▸ h (-a)

/-- Theorem 6.30.2 (1): the chapter concave-closure fixed-point equation,
upper semicontinuity, and closedness of all scalar upper level sets are equivalent.
Specializing `𝕜 = ℝ` recovers the textbook `EReal` statement. -/
theorem concaveClosure_eq_self_tfae_upperSemicontinuous_isClosed_upperLevelSets
    {g : E → WithBotTop 𝕜} :
    List.TFAE
      [concaveClosure g = g,
        UpperSemicontinuous g,
        ∀ a : 𝕜, IsClosed (g ⁻¹' Set.Ici (a : WithBotTop 𝕜))] := by
  tfae_have 1 ↔ 2 := by
    exact concaveClosure_eq_self_iff_upperSemicontinuous g
  tfae_have 2 ↔ 3 := by
    exact upperSemicontinuous_iff_isClosed_upperLevelSets g
  tfae_finish

end

section

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]
variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

namespace Function.IsConcave

/-- Owner form of Theorem 6.30.2 (2): every scalar upper level set of a concave
`WithBotTop α`-valued function is convex. The textbook `EReal` / `ℝ` statement is the
specialization `α = ℝ`. -/
theorem convex_upperLevelSet
    {g : E → WithBotTop α} (hg : g.IsConcave 𝕜) (a : α) :
    Convex 𝕜 (g ⁻¹' Set.Ici (a : WithBotTop α)) := by
  have hset :
      g ⁻¹' Set.Ici (a : WithBotTop α) =
        {x : E | (-g) x ≤ (((-a : α) : WithBotTop α))} := by
    ext x
    simpa [Set.mem_preimage] using
      (show (a : WithBotTop α) ≤ g x ↔ -g x ≤ (((-a : α) : WithBotTop α)) from
        WithBotTop.neg_le.symm)
  rw [hset]
  simpa using hg.convex_neg.convex_le (((-a : α) : WithBotTop α))

end Function.IsConcave

end

/-! ### Corollary_6_30_3 (from Chap06) -/
noncomputable section

open Filter
open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: the present corollary states that, except when both the primal and dual programs
  are inconsistent, the liminf at `0` of the primal perturbation function `inf F` equals the dual
  value `sup F* 0`, and the limsup at `0` of the dual perturbation function `sup F*` equals the
  primal value `inf F 0`.
- `core/canonical`: the relevant owner layer is already present as `perturbationFunction`,
  `upperPerturbationFunction`/`supᵇ(·)`, `adjoint`, `IsConsistent`, and the filter-side owners
  `liminf` and `limsup`.
- `bridge/view`: the source notations `inf F` and `sup F*` are rendered canonically by
  `perturbationFunction F` and `supᵇ(F⋆)`.

Domain-style sampling used here:
- `perturbationFunction` and `IsConsistent` from Definition 6.29.1;
- `upperPerturbationFunction` from Definition 6.30.11;
- `adjoint` from Definition 6.30.14;
- the zero-value identities from Corollary 6.30.2;
- the inconsistency criteria from Corollary 6.30.1.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜` on paired spaces
  `(U, UStar)` and `(X, XStar)`;
- primitive owners already upstream: `perturbationFunction F`,
  `supᵇ(F⋆)`, and the primal/dual consistency predicates;
- derived API added here: the two neighborhood-limit identities at the origin.

Layer target: `source-facing`, stated directly on the chapter's canonical owners without adding a
separate wrapper for the primal-dual program pair.
-/

section

variable {𝕜 : Type w}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

-- Proof sketch: apply the general identity
-- `(cl (perturbationFunction F)) 0 = liminf (perturbationFunction F) (nhds 0)` away from the
-- exceptional `⊥/⊤` case, then rewrite `(cl (perturbationFunction F)) 0` by Corollary 6.30.2.
-- Corollary 6.30.1 rules out the exceptional case as soon as either the primal or the dual
-- program is consistent.
/-- Corollary 6.30.3 (1): if either the primal or the dual generalized convex program attached to
`F` is consistent, then the liminf at `0` of the primal perturbation function equals the dual
upper perturbation value at `0`, i.e.
`liminf_{u → 0} (inf F)(u) = (sup F^*)(0)`. -/
theorem liminf_perturbationFunction_eq_upperPerturbationFunction_adjoint_zero_of_primal_or_dual_consistent
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hconsistent :
      IsConsistent F ∨ IsConsistent ((F⋆) : XStar → UStar → WithBotTop 𝕜)) :
    liminf (perturbationFunction F) (nhds (0 : U)) =
      supᵇ(((F⋆) : XStar → UStar → WithBotTop 𝕜)) (0 : XStar) := sorry

-- Proof sketch: apply the concave-side identity
-- `concaveClosure (upperPerturbationFunction (adjoint F)) 0 =
-- perturbationFunction F 0` from Corollary 6.30.2 together with the general formula expressing a
-- concave closure value as a limsup at the base point away from the exceptional `⊤/⊥` case.
-- The same consistency disjunction excludes that exceptional case via Corollary 6.30.1.
/-- Corollary 6.30.3 (2): if either the primal or the
dual generalized convex program attached to the closed convex bifunction `F` is consistent, then
the limsup at `0` of the dual upper perturbation function equals the primal perturbation value at
`0`, i.e. `limsup_{x^* → 0} (sup F^*)(x^*) = (inf F)(0)`. -/
theorem limsup_upperPerturbationFunction_adjoint_eq_perturbationFunction_zero_of_primal_or_dual_consistent
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hconsistent :
      IsConsistent F ∨ IsConsistent ((F⋆) : XStar → UStar → WithBotTop 𝕜)) :
    limsup (supᵇ(((F⋆) : XStar → UStar → WithBotTop 𝕜))) (nhds (0 : XStar)) =
      perturbationFunction F (0 : U) := sorry

end

end Bifunction

/-! ### Definition_6_30_3 (from Chap06) -/
noncomputable section
open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 6.30.3 gives the affine-majorant formula for the closure of a
  concave function.
- `core/canonical`: the closure owner already introduced in this chapter is `concaveClosure`.
- `bridge/view`: the formula is mediated upstream by
  `concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant`; this file keeps the main
  theorem surface at that generic owner layer (assuming the convex-side affine-minorant
  representation of `cl(-g)`), and then records the finite-dimensional scalar-field pairing and
  inner-product specializations as downstream bridges.

Primary mathematical domain:
- convex/concave duality for `WithTopBot`-valued functions on ordered scalar codomains.

Domain-style sampling used here:
- `concaveClosure`;
- `AffineMajorant`;
- `concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant`;
- `Function.IsConcave.concaveClosure_eq_iInf_affineMajorant_of_pairingSubConstRepresentable`;
- `AffineMap.exists_eq_inner_add_const` for the finite-dimensional inner-product bridge.

Primitive data vs derived API:
- primitive owner: `concaveClosure g`;
- primitive bridge input: the convex-side representation
  `cl(-g) x = ⨆ h : AffineMinorant (-g), h.toWithBotTop x`;
- derived bridge API: the source-facing affine-majorant formula expressing `concaveClosure g` as
  the pointwise infimum of affine majorants of `g`; the item then discharges the bridge input on
  the finite-dimensional scalar-field pairing layer and finally specializes to inner-product spaces
  through the affine-representation bridge.

Layer target: `bridge/view`. The item is a textbook specification of the already introduced owner
`concaveClosure`, so the main labeled entry is a direct recall of that canonical owner rather than
another wrapper definition.
-/

/- Definition 6.30.3 (1): the textbook closure `cl g` of a concave function is the canonical
Chapter 6 owner `concaveClosure g`. -/
recall concaveClosure

section

variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [Ring 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]

-- Proof sketch: apply the generic owner theorem from `Definition_6_30_2` pointwise.
/-- Definition 6.30.3 (2), canonical function-level bridge form: if the convex-side closure
`cl(-g)` is represented pointwise by the supremum of affine minorants of `-g`, then the concave
closure of `g` is the pointwise infimum of affine majorants of `g`. -/
theorem concaveClosure_eq_iInf_affineMajorant
    [IsOrderedAddMonoid 𝕜]
    (g : E → WithTopBot 𝕜)
    (hcl : cl(-g) = fun x ↦ ⨆ h : AffineMinorant (-g), h.toWithBotTop x) :
    concaveClosure g = fun x ↦ ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  funext x
  exact concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant g x
    (congrArg (fun f : E → WithTopBot 𝕜 ↦ f x) hcl)

/-- Definition 6.30.3 (2), canonical bridge form at a fixed point `x`. -/
theorem concaveClosure_apply_eq_iInf_affineMajorant
    [IsOrderedAddMonoid 𝕜]
    (g : E → WithTopBot 𝕜) (x : E)
    (hcl : cl(-g) x = ⨆ h : AffineMinorant (-g), h.toWithBotTop x) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  exact concaveClosure_eq_iInf_affineMajorant_of_eq_iSup_affineMinorant g x hcl

end

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜]
variable [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

-- Proof sketch: discharge Definition 6.30.3 directly by the pairing-level bridge theorem from
-- `Definition_6_30_2`.
/-- Finite-dimensional scalar-field pairing bridge for Definition 6.30.3 (2), in canonical
function-level form. -/
theorem concaveClosure_eq_iInf_affineMajorant_of_pairingSubConstRepresentable
    (g : E → WithTopBot 𝕜) (hg : g.IsConcave 𝕜)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable (-g)) :
    concaveClosure g = fun x ↦ ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  funext x
  exact hg.concaveClosure_eq_iInf_affineMajorant_of_pairingSubConstRepresentable x h_affine

/-- Finite-dimensional scalar-field pairing bridge for Definition 6.30.3 (2), evaluated at a
fixed point `x`. -/
theorem concaveClosure_apply_eq_iInf_affineMajorant_of_pairingSubConstRepresentable
    (g : E → WithTopBot 𝕜) (x : E) (hg : g.IsConcave 𝕜)
    (h_affine : AffineMinorant.IsPairingSubConstRepresentable (-g)) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  simpa using congrArg (fun f : E → WithTopBot 𝕜 ↦ f x)
    (concaveClosure_eq_iInf_affineMajorant_of_pairingSubConstRepresentable
      g hg h_affine)

end

section

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Definition 6.30.3 (2), Euclidean specialization: on a finite-dimensional real inner-product
space, and hence in particular on `ℝ^n`, the concave closure equals the pointwise infimum of all
affine majorants. -/
theorem concaveClosure_eq_iInf_affineMajorant_of_innerProduct
    (g : E → WithTopBot ℝ) (hg : g.IsConcave ℝ) :
    concaveClosure g = fun x ↦ ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  letI : HasLinearPairing E E ℝ := instHasLinearPairingInner E
  letI : HasContinuousPairing E E ℝ := instHasContinuousPairingInner E
  letI : HasPairingSwap E E ℝ := instHasPairingSwapInner E
  funext x
  have h_affine : AffineMinorant.IsPairingSubConstRepresentable (-g) := by
    intro h
    rcases AffineMap.exists_eq_inner_add_const (f := h.1) with ⟨y, α, hrepr⟩
    refine ⟨y, -α, ?_⟩
    ext z
    rw [pairingSubConstAffineMap_apply]
    have hreprz : (h.1 : E → ℝ) z = inner ℝ y z + α := by
      simpa using congrArg (fun f : E → ℝ ↦ f z) hrepr
    simpa [real_inner_comm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hreprz
  exact concaveClosure_apply_eq_iInf_affineMajorant_of_pairingSubConstRepresentable g x hg h_affine

/-- Definition 6.30.3 (2), Euclidean specialization evaluated at a fixed point `x`. -/
theorem concaveClosure_apply_eq_iInf_affineMajorant_of_innerProduct
    (g : E → WithTopBot ℝ) (x : E) (hg : g.IsConcave ℝ) :
    concaveClosure g x =
      ⨅ h : AffineMajorant g, h.toWithTopBot x := by
  simpa using congrArg (fun f : E → WithTopBot ℝ ↦ f x)
    (concaveClosure_eq_iInf_affineMajorant_of_innerProduct g hg)

end

/-! ### Theorem_6_30_3 (from Chap06) -/
noncomputable section

universe u

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.3 states Rockafellar's concave biconjugacy identity
  `g** = cl g` for a concave function.
- `core/canonical`: the relevant owners already present in the project are `concaveConjugate` for
  the concave conjugate and `concaveClosure` for the closure from Definition 6.30.2.
- `bridge/view`: the theorem is the sign-dual transport of convex biconjugacy for `-g`; it should
  therefore be stated directly as an equality between those two existing owners, not through a new
  wrapper.

Primary mathematical domain:
- convex/concave duality on `WithBotTop 𝕜`-valued functions over finite-dimensional paired spaces.

Domain-style sampling used here:
- `concaveConjugate`;
- `concaveClosure`;
- `Function.IsConcave.convex_neg`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`.

Primitive data vs derived API:
- primitive input: a concave function `g : E → WithBotTop 𝕜`;
- primitive owners already available: `concaveConjugate g` and `concaveClosure g`;
- derived API added here: the biconjugacy bridge identifying the concave biconjugate with the
  concave closure.

Layer target: `bridge/view`. The source theorem is not introducing a new owner; it relates the
existing Chapter 6 conjugate and closure owners. The source statement is lifted to the canonical
finite-dimensional scalar-parametric self-pairing layer already used by the convex-side
biconjugacy theorem.
-/

section

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

local notation:max g "∗∗" => (concaveConjugate (Y := E) g)∗

namespace Function.IsConcave

-- Proof sketch: apply the sign-duality formula from Theorem 6.30.4 twice to rewrite the concave
-- biconjugate of `g` as the negative of the convex biconjugate of `-g`. Since `hg` gives convexity
-- of `-g`, Theorem 12.2 identifies that convex biconjugate with `cl(-g)`, and unfolding
-- `concaveClosure` turns the result into the desired equality.
/-- Theorem 6.30.3: on a finite-dimensional space with a continuous linear self-pairing, the
concave biconjugate of a concave function equals its concave closure, at the finite-dimensional
scalar-parametric self-pairing layer. Here `concaveClosure g` is the closure from Definition 6.30.2,
namely the pointwise infimum of the affine majorants of `g`. -/
theorem biconjugate_eq_concaveClosure
    {g : E → WithBotTop 𝕜} (hg : g.IsConcave 𝕜) :
    g∗∗ = concaveClosure g := by
  ext x
  rw [concaveConjugate_eq_neg_convexConjugate_neg_apply
        (g := concaveConjugate (Y := E) g) (y := x)]
  have hneg_gStar :
      (-g∗) = fun y : E ↦ ((-g)⋆ : E → WithBotTop 𝕜) (-y) := by
    funext y
    simpa using
      congrArg Neg.neg (concaveConjugate_eq_neg_convexConjugate_neg_apply (g := g) (y := y))
  rw [hneg_gStar]
  have hpair_neg_left : ∀ y z : E, (⟪-y, z⟫ₚ : 𝕜) = -⟪y, z⟫ₚ := by
    intro y z
    change (HasLinearPairing.pairingLinear (-y)) z = -((HasLinearPairing.pairingLinear y) z)
    exact congrArg (fun φ : Module.Dual 𝕜 E => φ z)
      (LinearMap.map_neg (HasLinearPairing.pairingLinear : E →ₗ[𝕜] Module.Dual 𝕜 E) y)
  have hbiconj_neg :
      (((fun y : E ↦ ((-g)⋆ : E → WithBotTop 𝕜) (-y))⋆ : E → WithBotTop 𝕜) (-x)) =
        ((-g)⋆⋆ : E → WithBotTop 𝕜) x := by
    rw [convexConjugate_eq_iSup_pairing_sub, convexBiconjugate_eq_iSup_pairing_sub]
    calc
      (⨆ y : E, (⟪y, -x⟫ₚ : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) (-y)))
          = ⨆ y : E, (⟪-y, -x⟫ₚ : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) y) := by
              simpa using
                (Equiv.iSup_comp (e := Equiv.neg E)
                  (g := fun y : E ↦
                    (⟪-y, -x⟫ₚ : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) y)))
      _ = ⨆ y : E, (⟪y, x⟫ₚ : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) y) := by
            refine iSup_congr ?_
            intro y
            have hpair : (⟪-y, -x⟫ₚ : 𝕜) = ⟪y, x⟫ₚ := by
              calc
                (⟪-y, -x⟫ₚ : 𝕜) = -⟪-y, x⟫ₚ := HasPairingNegRight.pairing_neg_right (-y) x
                _ = -(-⟪y, x⟫ₚ) := by rw [hpair_neg_left y x]
                _ = ⟪y, x⟫ₚ := by simp
            change (((⟪-y, -x⟫ₚ : 𝕜) : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) y)) =
              (((⟪y, x⟫ₚ : 𝕜) : WithBotTop 𝕜) - (((-g)⋆ : E → WithBotTop 𝕜) y))
            rw [hpair]
  rw [hbiconj_neg]
  rw [hg.convex_neg.biconjugate_eq_lowerSemicontinuousHull]
  rfl

end Function.IsConcave

end

/-! ### Corollary_6_30_4 (from Chap06) -/
noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: this file records the verified owner-level part of Corollary 6.30.4 at a fixed
  pair `(xBar, uStarBar)`: zero-duality-gap with primal/dual attainment is equivalent to
  objective-value equality, and hence to the objective inequality under weak duality.
- `core/canonical`: the chapter owners are `perturbationFunction`, `upperPerturbationFunction`,
  `objective`, and `adjoint`.
- `bridge/view`: the public surface stays on those owners and avoids introducing a parallel
  wrapper.

Note on scope:
- the previous local statement included an explicit saddle-point clause but did not provide a
  proved bridge at this abstraction layer; this version keeps the proved owner-level equivalence.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type*} {XStar : Type*}
variable [AddGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [Zero U]
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "p" => perturbationFunction F
local notation "fStar" => ((adjoint XStar UStar F) : XStar → UStar → WithBotTop 𝕜)
local notation "q" => upperPerturbationFunction fStar
local notation "f₀" => (F)₀
local notation "f⋆₀" => ((fStar)₀ : UStar → WithBotTop 𝕜)

omit [AddGroup 𝕜] in
private theorem perturbationFunction_zero_eq_of_isMinOn
    {xBar : X} (hmin : IsMinOn f₀ Set.univ xBar) :
    p 0 = f₀ xBar := by
  have hmin' : ∀ x : X, f₀ xBar ≤ f₀ x := (isMinOn_univ_iff.mp hmin)
  refine le_antisymm ?_ ?_
  · simpa [perturbationFunction_apply] using (iInf_le (fun x : X ↦ f₀ x) xBar)
  · simpa [perturbationFunction_apply] using (le_iInf hmin')

omit [Zero U] in
private theorem upperPerturbationFunction_zero_eq_of_isMaxOn
    {uStarBar : UStar} (hmax : IsMaxOn f⋆₀ Set.univ uStarBar) :
    q 0 = f⋆₀ uStarBar := by
  have hmax' : ∀ uStar : UStar, f⋆₀ uStar ≤ f⋆₀ uStarBar := (isMaxOn_univ_iff.mp hmax)
  refine le_antisymm ?_ ?_
  · simpa [upperPerturbationFunction_apply] using (iSup_le hmax')
  · simpa [upperPerturbationFunction_apply] using
      (le_iSup (fun uStar : UStar ↦ f⋆₀ uStar) uStarBar)

/-- Corollary 6.30.4 owner-level form: for a fixed pair `(xBar, uStarBar)`, the conjunction
`p 0 = q 0` with primal/dual optimality is equivalent to objective equality. -/
theorem zeroDualityGap_primalDualOptimality_iff_objective_eq
    (hweak : ∀ x : X, ∀ uStar : UStar, f⋆₀ uStar ≤ f₀ x)
    (xBar : X) (uStarBar : UStar) :
    (p 0 = q 0 ∧ IsMinOn f₀ Set.univ xBar ∧ IsMaxOn f⋆₀ Set.univ uStarBar) ↔
      f₀ xBar = f⋆₀ uStarBar := by
  constructor
  · rintro ⟨hgap, hmin, hmax⟩
    have hp0 : p 0 = f₀ xBar := perturbationFunction_zero_eq_of_isMinOn (F := F) hmin
    have hq0 : q 0 = f⋆₀ uStarBar := upperPerturbationFunction_zero_eq_of_isMaxOn (F := F) hmax
    calc
      f₀ xBar = p 0 := hp0.symm
      _ = q 0 := hgap
      _ = f⋆₀ uStarBar := hq0
  · intro heq
    have hmin : IsMinOn f₀ Set.univ xBar := by
      rw [isMinOn_univ_iff]
      intro x
      calc
        f₀ xBar = f⋆₀ uStarBar := heq
        _ ≤ f₀ x := hweak x uStarBar
    have hmax : IsMaxOn f⋆₀ Set.univ uStarBar := by
      rw [isMaxOn_univ_iff]
      intro uStar
      calc
        f⋆₀ uStar ≤ f₀ xBar := hweak xBar uStar
        _ = f⋆₀ uStarBar := heq
    have hp0 : p 0 = f₀ xBar := perturbationFunction_zero_eq_of_isMinOn (F := F) hmin
    have hq0 : q 0 = f⋆₀ uStarBar := upperPerturbationFunction_zero_eq_of_isMaxOn (F := F) hmax
    refine ⟨?_, hmin, hmax⟩
    calc
      p 0 = f₀ xBar := hp0
      _ = f⋆₀ uStarBar := heq
      _ = q 0 := hq0.symm

/-- Under weak duality at `(xBar, uStarBar)`, objective equality is equivalent to objective
inequality. -/
theorem objective_eq_iff_objective_le_of_weakDuality
    (hweak : ∀ x : X, ∀ uStar : UStar, f⋆₀ uStar ≤ f₀ x)
    (xBar : X) (uStarBar : UStar) :
    f₀ xBar = f⋆₀ uStarBar ↔
      f₀ xBar ≤ f⋆₀ uStarBar := by
  constructor
  · intro heq
    exact le_of_eq heq
  · intro hle
    exact le_antisymm hle (hweak xBar uStarBar)

/-- Corollary 6.30.4 owner-level form: for a fixed pair `(xBar, uStarBar)`, the conjunction
`p 0 = q 0` with primal/dual optimality, objective equality, and objective inequality are
equivalent under weak duality. -/
theorem zeroDualityGap_primalDualOptimality_objective_eq_objective_le_tfae
    (hweak : ∀ x : X, ∀ uStar : UStar, f⋆₀ uStar ≤ f₀ x)
    (xBar : X) (uStarBar : UStar) :
    List.TFAE
      [p 0 = q 0 ∧ IsMinOn f₀ Set.univ xBar ∧ IsMaxOn f⋆₀ Set.univ uStarBar,
        f₀ xBar = f⋆₀ uStarBar,
        f₀ xBar ≤ f⋆₀ uStarBar] := by
  tfae_have 1 ↔ 2 := by
    exact zeroDualityGap_primalDualOptimality_iff_objective_eq
      (F := F) hweak xBar uStarBar
  tfae_have 2 ↔ 3 := by
    exact objective_eq_iff_objective_le_of_weakDuality
      (F := F) hweak xBar uStarBar
  tfae_finish

/-- Under weak duality, objective inequality at a pair implies objective equality at that pair. -/
theorem objective_eq_of_objective_le_of_weakDuality
    (hweak : ∀ x : X, ∀ uStar : UStar, f⋆₀ uStar ≤ f₀ x)
    (xBar : X) (uStarBar : UStar)
    (hle : f₀ xBar ≤ f⋆₀ uStarBar) :
    f₀ xBar = f⋆₀ uStarBar :=
  (objective_eq_iff_objective_le_of_weakDuality (F := F) hweak xBar uStarBar).2 hle

end

end Bifunction

/-! ### Definition_6_30_4 (from Chap06) -/
noncomputable section

universe u v w

open scoped Rockafellar

section

variable {X : Type u} {Y : Type v} {L : Type w}
variable [InfSet L] [Sub L] [HasPairing X Y L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.4 introduces the conjugate `g*` of a concave function `g` by
  the infimum formula `inf_x (pairing x y - g x)`.
- `core/canonical`: the actual owner abstraction is already Chapter 12's `convexConjugate`,
  applied on the order-dual codomain `OrderDual L`, since `InfSet L` is exactly `SupSet (OrderDual
  L)` and the source formula is the same conjugation operator viewed in the reversed order.
- `bridge/view`: this file keeps the source-facing Chapter 6 name `concaveConjugate` and notation
  `g∗`, but only as the thin order-dual view of that existing owner.

Domain-style sampling used here:
- the Chapter 12 pairing owner `convexConjugate`;
- an ambient codomain `L` carrying the primitive operations used by the source formula;
- indexed infima `⨅ x, ...` as the primitive source formula.

Primitive data vs derived API:
- primitive input: a function `g : X → L`;
- canonical owner upstream: `convexConjugate` on `OrderDual L`;
- source-facing bridge owner in this file: `concaveConjugate g : Y → L`;
- derived API in this file: only the immediate pointwise `⨅` restatement.

Layer target: `bridge/view`. The source genuinely introduces a concave-side conjugation formula,
but its canonical owner is already the Chapter 12 conjugate on the order-dual codomain, so this
file should expose only the source-facing view rather than a second primitive wheel.
-/

/-- Definition 6.30.4: the Chapter 6 concave-side conjugate owner, implemented as
the order-dual view of the Chapter 12 owner `convexConjugate`. -/
def concaveConjugate : (X → L) → (Y → L) :=
  (convexConjugate : (X → OrderDual L) → Y → OrderDual L)

-- Source-facing notation `g∗` is directly the Chapter 6 bridge owner.
-- Keeping the notation on the owner directly avoids fragile elaboration through local lambdas.
scoped[Rockafellar] postfix:max "∗" => concaveConjugate

/-- Owner-level bridge: the Chapter 6 concave conjugate is exactly the Chapter 12 Fenchel
conjugate on the order-dual codomain. -/
@[simp] theorem concaveConjugate_eq_convexConjugate (g : X → L) :
    g∗ = (g⋆ : Y → OrderDual L) :=
  rfl

/-- Evaluating the concave conjugate `g∗` at `y` gives the source infimum formula
`inf_x (pairing x y - g x)`. -/
theorem concaveConjugate_eq_iInf_pairing_sub
    (g : X → L) (y : Y) :
    g∗ y =
      ⨅ x : X, ⟪x, y⟫ₚ - g x :=
  rfl

end
