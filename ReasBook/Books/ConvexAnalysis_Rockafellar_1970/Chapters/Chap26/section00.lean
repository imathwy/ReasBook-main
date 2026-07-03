import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Set.Subsingleton
import Mathlib.Logic.Relator
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_26_0_1 (from Chap05) -/
open scoped SetRel

universe u v

section

variable {α : Type u} {β : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 26.0.1 introduces a multivalued mapping `ρ`, meaning a pointwise
  assignment `x ↦ ρ(x) ⊆ β`, and says that `ρ` is single-valued when each value set contains at
  most one point.
- `core/canonical`: mathlib's canonical owner for multivalued mappings is `SetRel α β`, i.e. a
  relation between `α` and `β`, together with its pointwise image operation `SetRel.image`.
- `bridge/view`: the source value set `ρ(x)` is the singleton-image `ρ[[x]] := ρ.image {x}`,
  with explicit relation-membership bridge `xStar ∈ ρ[[x]] ↔ x ~[ρ] xStar`, while the
  single-valuedness clause is the right-uniqueness predicate on the underlying relation.

Domain-style sampling used here:
- `SetRel` from `Mathlib/Data/Rel.lean`;
- `SetRel.image`;
- `SetRel.mem_image`;
- `Relator.RightUnique`;
- `Relator.LeftUnique`;
- `Relator.BiUnique`;
- `Set.Subsingleton`.

Primitive data vs derived API:
- primitive owner data: a relation `ρ : SetRel α β`;
- primitive owner predicates: `ρ.RightUnique`, `ρ.LeftUnique`, and `ρ.BiUnique`;
- derived/source-facing API: the equivalence between right-uniqueness of `ρ` and subsingleton
  singleton-image fibers.

Layer target: `core/canonical`, with the source-facing fiber characterization retained only as a
companion theorem.
-/

/- Definition 26.0.1: a multivalued mapping from `α` to `β` is the canonical relation type
`SetRel α β`, equivalently a set-valued assignment sending each `x : α` to a subset of `β`. -/
#check (SetRel α β)

/- Definition 26.0.1: single-valuedness of a multivalued mapping is the canonical relation
predicate `Relator.RightUnique`. -/
recall Relator.RightUnique
recall Relator.LeftUnique
recall Relator.BiUnique

-- Proof sketch: membership in `ρ[[x]]` is the same as relation membership
-- `x ~[ρ] xStar` by `SetRel.mem_image`, because the only point in `{x}` is `x` itself. The
-- right-uniqueness predicate for `ρ` is then exactly the statement that any two elements of the
-- singleton-image fiber over `x` coincide.
namespace SetRel

/-- Source-facing pointwise value-set notation for a multivalued mapping relation. -/
scoped notation:arg ρ "[[" x "]]" => SetRel.image ρ ({x} : Set _)

/-- Canonical owner on `SetRel` for single-valuedness of a multivalued mapping. -/
abbrev RightUnique (ρ : SetRel α β) : Prop :=
  Relator.RightUnique (· ~[ρ] ·)

/-- Canonical owner on `SetRel` for inverse single-valuedness (left-uniqueness). -/
abbrev LeftUnique (ρ : SetRel α β) : Prop :=
  Relator.LeftUnique (· ~[ρ] ·)

/-- Canonical owner on `SetRel` for one-to-one multivalued mappings. -/
abbrev BiUnique (ρ : SetRel α β) : Prop :=
  Relator.BiUnique (· ~[ρ] ·)

/-- Membership in the source-facing value set is exactly relation membership. -/
@[simp] theorem mem_image_singleton_iff (ρ : SetRel α β) {x : α} {xStar : β} :
    xStar ∈ ρ[[x]] ↔ x ~[ρ] xStar := by
  simp [Set.mem_singleton_iff]

/-- The singleton image of `x` under a relation is exactly its intrinsic relation fiber. -/
@[simp] theorem image_singleton_eq_fiber (ρ : SetRel α β) (x : α) :
    ρ[[x]] = {xStar : β | x ~[ρ] xStar} := by
  ext xStar
  exact mem_image_singleton_iff (ρ := ρ)

/-- Canonical intrinsic owner form: a relation is right-unique iff each relation fiber over `x`
is subsingleton. -/
@[simp] theorem rightUnique_iff_fiber_subsingleton (ρ : SetRel α β) :
    ρ.RightUnique ↔ ∀ x : α, ({xStar : β | x ~[ρ] xStar}).Subsingleton := by
  constructor
  · intro h x y hy z hz
    exact h hy hz
  · intro h x y z hxy hxz
    exact h x hxy hxz

/-- The source single-valuedness clause on a multivalued mapping is equivalent to every pointwise
value set containing at most one element. -/
@[simp] theorem rightUnique_iff_image_singleton_subsingleton (ρ : SetRel α β) :
    ρ.RightUnique ↔ ∀ x : α, (ρ[[x]]).Subsingleton := by
  simp [image_singleton_eq_fiber, rightUnique_iff_fiber_subsingleton]

end SetRel

end

/-! ### Text_26_0_1 (from Chap05) -/
noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar SetRel

universe u

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : E → WithTopBot 𝕜}

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "fStarDual" => (f⋆ : StrongDual 𝕜 E → WithTopBot 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.0.1 motivates the Legendre transformation for convex functions by
  pointing to two existing mathematical correspondences: Fenchel conjugacy `f ↦ f⋆` and the
  subdifferential multifunction `∂f`.
- `core/canonical`: the owner abstractions already present in the project are `convexConjugate`,
  `_root_.subdifferentialGraph`, the relation inverse `SetRel.inv`, the Chapter 26 one-to-one
  owner `SetRel.BiUnique`, and the Chapter 23 Fenchel-Young conjugacy owner theorem.
- `bridge/view`: the Euclidean self-dual graph view `Function.subdifferentialGraph` remains a
  Fréchet-Riesz bridge obtained after the intrinsic graph-inverse owner theorem below.

Domain-style sampling used here:
- `convexConjugate`;
- `_root_.subdifferentialGraph`;
- `Function.subdifferentialGraph`;
- `SetRel.inv`;
- `SetRel.BiUnique`;
- `Function.subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_
  conjugate_subdifferentialAt_of_closure_eq`.

Primitive data vs derived API:
- primitive data: a closed proper convex function `f`, its intrinsic subdifferential graph
  relation, and relation inversion;
- derived bridge API: the Euclidean same-carrier graph view
  `Function.subdifferentialGraph`, and the differentiable value identity
  `f⋆(∇f(x)) = ⟪x, ∇f(x)⟫ - f(x)` for the canonical extension off an open convex domain.

Layer target:
- `core/canonical`: the intrinsic graph-inverse theorem on `_root_.subdifferentialGraph`;
- `bridge/view`: the Euclidean same-carrier graph theorem used by the later Chapter 26
  one-to-one bridge.
-/

/-- Text 26.0.1, intrinsic graph-owner form: for a closed proper convex function, the
subdifferential graph of the Fenchel conjugate is the inverse relation of the original
subdifferential graph. This is the canonical pairing-owner statement behind Legendre
correspondence. -/
theorem subdifferentialGraph_convexConjugate_eq_inv
    (hf : IsClosedProperConvex[𝕜] f) :
    gph∂[E](fStarDual) = (gph∂(f)).inv := by
  ext p
  rcases p with ⟨xStar, x⟩
  constructor
  · intro hp
    have hsub : x ∈ ∂[E]fStarDual(xStar) :=
      _root_.mem_subdifferentialGraph.mp hp
    have hsub' : xStar ∈ ∂ f at x :=
      (Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff
        (f := f) (x := x) (xStar := xStar) hf).1 hsub
    exact
      (SetRel.mem_inv (R := gph∂(f)) (a := x) (b := xStar)).2
        (_root_.mem_subdifferentialGraph.mpr hsub')
  · intro hp
    have hgraph : (x, xStar) ∈ gph∂(f) :=
      (SetRel.mem_inv (R := gph∂(f)) (a := x) (b := xStar)).1 hp
    have hsub : xStar ∈ ∂ f at x :=
      _root_.mem_subdifferentialGraph.mp hgraph
    have hsub' : x ∈ ∂[E]fStarDual(xStar) :=
      (Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff
        (f := f) (x := x) (xStar := xStar) hf).2 hsub
    exact _root_.mem_subdifferentialGraph.mpr hsub'

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.0.1 motivates the Legendre transformation for convex functions by
  pointing to two existing mathematical correspondences: Fenchel conjugacy `f ↦ f⋆` and the
  subdifferential multifunction `∂f`.
- `core/canonical`: the owner abstractions already present in the project are `convexConjugate`,
  `_root_.subdifferentialGraph`, `Function.subdifferentialGraph`, the relation inverse
  `SetRel.inv`, the Chapter 26 one-to-one owner `SetRel.BiUnique`, and the Chapter 23
  Fenchel-Young conjugacy owner theorem.
- `bridge/view`: the declaration below records the Euclidean graph-inverse identity underlying the
  classical Legendre correspondence; projection-injectivity and one-to-one consequences are then
  derived from the existing `SetRel` owner API rather than introduced as a parallel root theorem.

Domain-style sampling used here:
- `convexConjugate`;
- `_root_.subdifferentialGraph`;
- `Function.subdifferentialGraph`;
- `SetRel.inv`;
- `SetRel.BiUnique`;
- `Function.subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_
  conjugate_subdifferentialAt_of_closure_eq`.

Primitive data vs derived API:
- primitive data: a closed proper convex function `f`, its intrinsic subdifferential graph
  relation, its Euclidean graph view `Function.subdifferentialGraph f`, and the inverse relation
  on that Euclidean graph;
- derived API: the one-to-one and projection-uniqueness consequences obtained from the graph
  inverse identity, and the differentiable value identity
  `f⋆(∇f(x)) = ⟪x, ∇f(x)⟫ - f(x)` for the canonical extension off an open convex domain.

Layer target: `bridge/view`. This introductory text does not own a new construction; it reuses the
chapter owners for conjugacy, subdifferentials, relation inversion, and multivalued-map
uniqueness.

Ambient refinement:
- the conjugacy side uses `f⋆` with the chapter's inner-product self-pairing on `E`, but the
  owner statement below is expressed on the same-carrier Euclidean graph view
  `Function.subdifferentialGraph`, where relation inversion has the correct type.
-/

/- Text 26.0.1 is organized around the chapter's Fenchel-conjugacy owner. -/
#check convexConjugate

/- Text 26.0.1 treats multivalued mappings through the canonical relation inverse. -/
#check SetRel.inv

/- Text 26.0.1 treats one-to-one multivalued mappings through the canonical relation owner. -/
#check SetRel.BiUnique

/- Text 26.0.1 treats subdifferential mappings through the intrinsic graph owner. -/
#check _root_.subdifferentialGraph

/- Text 26.0.1 treats the Euclidean self-dual graph view through `Function.subdifferentialGraph`. -/
#check Function.subdifferentialGraph
namespace Function

/-- Text 26.0.1, Euclidean graph-owner bridge: for a closed proper convex function, the
vector-valued subdifferential graph of the Fenchel conjugate is the inverse relation of the
vector-valued subdifferential graph of `f`. This is the same-carrier bridge statement from which
the chapter's projection-injectivity and one-to-one formulations are derived. -/
theorem subdifferentialGraph_convexConjugate_eq_inv
    {f : E → WithTopBot ℝ} (hf : f.IsClosedProperConvex) :
    subdifferentialGraph (f⋆ : E → WithTopBot ℝ) = (subdifferentialGraph f).inv := by
  ext p
  rcases p with ⟨x, xStar⟩
  have hcl : cl(f) xStar = f xStar := by
    simpa using congrFun (lowerSemicontinuousHull_eq_self hf.closed) xStar
  have hiff :
      xStar ∈ ∂ᵥ(f⋆ : E → WithTopBot ℝ)(x) ↔ x ∈ ∂ᵥf(xStar) :=
    (subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_conjugate_subdifferentialAt_of_closure_eq
      (f := f) (x := xStar) (xStar := x) hf.convex hf.proper hcl).out 4 0
  constructor
  · intro hx
    have hsub : x ∈ ∂ᵥf(xStar) := hiff.1 (Function.mem_subdifferentialGraph.mp hx)
    have hgraph : xStar ~[subdifferentialGraph f] x :=
      Function.mem_subdifferentialGraph.mpr hsub
    change (xStar, x) ∈ subdifferentialGraph f
    exact hgraph
  · intro hx
    have hgraph : xStar ~[subdifferentialGraph f] x := by
      change (xStar, x) ∈ subdifferentialGraph f at hx
      exact hx
    have hsub : x ∈ ∂ᵥf(xStar) :=
      Function.mem_subdifferentialGraph.mp hgraph
    exact Function.mem_subdifferentialGraph.mpr (hiff.2 hsub)

end Function

end

section

variable {𝕜 : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Function

variable {U : Set E} {f : E → 𝕜}

local notation "fExt" => Function.toWithTopBotOn f U

/-- Text 26.0.1, intrinsic owner-level differentiable value formula: at a relative-interior point
`x ∈ ri[𝕜](U)` of a convex branch, the Fenchel conjugate of the canonical extension
`Function.toWithTopBotOn f U`, evaluated at the Fréchet derivative owner `fderiv 𝕜 f x`, is the
affine defect `(fderiv 𝕜 f x) x - f x`. -/
theorem convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub
    (hf_convex : ConvexOn 𝕜 U f)
    {x : E} (hx : x ∈ ri[𝕜](U)) (hfdx : DifferentiableAt 𝕜 f x) :
    fExt⋆ (fderiv 𝕜 f x) = (((fderiv 𝕜 f x) x - f x : 𝕜) : WithTopBot 𝕜) := by
  have hsub : ∂ᵣf(x | U) = {fderiv 𝕜 f x} :=
    subdifferentialWithinAt_eq_singleton_fderiv
      (hf_convex := hf_convex) (x := x) (hx := hx)
      (hfdx := hfdx.hasFDerivAt)
  have hmem : fderiv 𝕜 f x ∈ ∂ᵣf(x | U) := by
    simp [hsub]
  have hvalue :=
    convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
      (f := f) (U := U) (x := x)
      (xStar := fderiv 𝕜 f x) (intrinsicInterior_subset hx) hmem
  have hpair : (⟪x, fderiv 𝕜 f x⟫ₚ : 𝕜) = (fderiv 𝕜 f x) x := rfl
  calc
    fExt⋆ (fderiv 𝕜 f x) = (((⟪x, fderiv 𝕜 f x⟫ₚ - f x : 𝕜)) : WithTopBot 𝕜) :=
      hvalue
    _ = (((fderiv 𝕜 f x) x - f x : 𝕜) : WithTopBot 𝕜) := by rw [hpair]

/-- Text 26.0.1, open-set bridge form: on an open convex set `U`, the same value identity as
`convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub` can be stated using `fderivWithin 𝕜 f U x`. -/
theorem convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub
    (hU_open : IsOpen U) (hf_convex : ConvexOn 𝕜 U f)
    {x : E} (hx : x ∈ U) (hfdx : DifferentiableAt 𝕜 f x) :
    fExt⋆ (fderivWithin 𝕜 f U x) = (((fderivWithin 𝕜 f U x) x - f x : 𝕜) : WithTopBot 𝕜) := by
  have hx_int : x ∈ interior U := mem_interior_iff_mem_nhds.2 (hU_open.mem_nhds hx)
  have hx_ri : x ∈ ri[𝕜](U) := interior_subset_intrinsicInterior (𝕜 := 𝕜) hx_int
  have hfd_within : fderivWithin 𝕜 f U x = fderiv 𝕜 f x :=
    fderivWithin_of_isOpen hU_open hx
  simpa [hfd_within] using
    (convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub
      (hf_convex := hf_convex) (x := x) (hx := hx_ri) (hfdx := hfdx))

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function

variable {U : Set E} {f : E → ℝ}

local notation "fExt" => Function.toWithTopBotOn f U

/-- Text 26.0.1, differentiable Legendre-value formula: on the differentiability locus of the
canonical extension `Function.toWithTopBotOn f U`, the Fenchel conjugate evaluated at the
gradient is the classical affine defect `⟪x, ∇ f x⟫ - f x`. This is the single-valued branch
of the subdifferential correspondence used in the Legendre transformation discussion, obtained by
the Fréchet-Riesz bridge from the derivative-owner theorem above. -/
theorem convexConjugate_toWithTopBotOn_gradient_eq_inner_sub
    (hf_convex : ConvexOn ℝ U f)
    {x : E} (hx : x ∈ ri[ℝ](U)) (hfdx : DifferentiableAt ℝ f x) :
    fExt⋆ (∇ f x) = ((⟪x, ∇ f x⟫ - f x : ℝ) : WithTopBot ℝ) := by
  have hgrad_mem_vec : ∇ f x ∈ ∂ᵥᵣf(x | U) := by
    have hsub : ∂ᵥᵣf(x | U) = {∇ f x} :=
      Function.subdifferentialWithinAt_eq_singleton_gradient
        (hf_convex := hf_convex) (x := x)
        (hx := hx) (hfdx := hfdx)
    simp [hsub]
  have hgrad_mem : ∇ f x ∈ ∂ᵣ[E]f(x | U) := by
    rw [_root_.mem_subdifferentialWithinAt_pairing]
    intro z
    change
      Function.toWithTopBotOn f U z ≥
        Function.toWithTopBotOn f U x + ((⟪z - x, ∇ f x⟫ₚ : ℝ) : WithTopBot ℝ)
    have hz :
        Function.toWithTopBotOn f U z ≥
          Function.toWithTopBotOn f U x + ((inner ℝ (∇ f x) (z - x) : ℝ) : WithTopBot ℝ) :=
      (Function.mem_subdifferentialWithinAt
        (f := f) (U := U) (x := x) (g := ∇ f x)).1 hgrad_mem_vec z
    have hswap_pair : (⟪∇ f x, z - x⟫ : ℝ) = (⟪z - x, ∇ f x⟫ₚ : ℝ) := by
      change inner ℝ (∇ f x) (z - x) = inner ℝ (z - x) (∇ f x)
      simp [real_inner_comm]
    simpa [hswap_pair] using hz
  simpa using
    (convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
      (f := f) (U := U) (x := x) (xStar := ∇ f x)
      (intrinsicInterior_subset hx) hgrad_mem)

end Function

end

/-! ### Definition_26_0_2 (from Chap05) -/
open scoped SetRel

universe u v

section

variable {α : Type u} {β : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 26.0.2 defines the inverse `ρ⁻¹` of a multivalued mapping `ρ` by
  the textbook membership condition `x ∈ ρ⁻¹(x*) ↔ x* ∈ ρ(x)`.
- `core/canonical`: mathlib's owner abstraction for multivalued mappings is `SetRel α β`, and the
  inverse mapping is the canonical relation inverse `SetRel.inv`.
- `bridge/view`: the source set-builder description is already the canonical theorem
  `SetRel.mem_inv`, on the chapter notation surface `ρ⁻¹`.

Domain-style sampling used here:
- `SetRel` from `Mathlib/Data/Rel.lean`;
- `SetRel.inv`;
- `SetRel.mem_inv`;
- the domain/codomain swap lemmas `SetRel.dom_inv` and `SetRel.cod_inv`, which confirm that this
  owner has the expected multivalued-mapping behavior.

Primitive data vs derived API:
- primitive input: a multivalued mapping `ρ`, represented canonically as a relation `SetRel α β`;
- primitive owner: `SetRel.inv`, written on the chapter surface as `ρ⁻¹`;
- derived/source-facing API: the textbook characterization
  `xStar ~[ρ⁻¹] x ↔ x ~[ρ] xStar`, already owned by `SetRel.mem_inv`.

Layer target: `bridge/view`.

This file keeps only direct canonical recall/use and chapter notation.
-/

namespace SetRel
scoped postfix:max "⁻¹" => SetRel.inv
end SetRel

variable (ρ : SetRel α β)

/- Definition 26.0.2: the inverse multivalued mapping is the canonical inverse relation
`SetRel.inv`, with the textbook Chapter 26 surface notation `ρ⁻¹`. -/
#check ρ⁻¹

/- Definition 26.0.2, source-facing membership formula on the canonical owner:
membership in the inverse multivalued mapping is equivalent to reversed membership in the
original mapping. This is exactly `SetRel.mem_inv`. -/
recall SetRel.mem_inv

namespace SetRel

/-- Source-facing value-set form of Definition 26.0.2: membership in the inverse value set is
equivalent to reversed membership in the original value set. -/
@[simp] theorem mem_image_singleton_inv_iff (ρ : SetRel α β) {x : α} {xStar : β} :
    x ∈ (ρ⁻¹)[[xStar]] ↔ xStar ∈ ρ[[x]] := by
  simp

end SetRel

/- Definition 26.0.2 companion owner facts: inverse swaps domain and codomain. -/
recall SetRel.dom_inv
recall SetRel.cod_inv

end

/-! ### Definition_26_0_3 (from Chap05) -/
open scoped SetRel

universe u v

section

variable {α : Type u} {β : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 26.0.3 says a multivalued mapping is one-to-one exactly when both
  the mapping and its inverse are single-valued.
- `core/canonical`: on the chapter owner `SetRel`, one-to-one-ness is the canonical relation
  owner `Relator.BiUnique (· ~[ρ] ·)`.
- `bridge/view`: the chapter's multivalued-mapping owner is `SetRel α β`, and inversion is the
  canonical `SetRel.inv`; the source inverse wording is therefore a thin bridge from
  `(ρ⁻¹).RightUnique` to the intrinsic owner `ρ.LeftUnique`.

Domain-style sampling used here:
- `SetRel` and `SetRel.inv` from `Mathlib/Data/Rel.lean`;
- `Relator.RightUnique`;
- `Relator.LeftUnique`;
- `Relator.BiUnique`.

Primitive data vs derived API:
- primitive owner data: the relation `ρ : SetRel α β`;
- primitive canonical owner surface on `SetRel`: the one-to-one owner `ρ.BiUnique`,
  aligned with `Relator.BiUnique (· ~[ρ] ·)`;
- primitive theorem-level decomposition: right- and left-uniqueness of `ρ` through
  `ρ.RightUnique` and `ρ.LeftUnique`;
- derived source-facing bridge API: single-valuedness of `ρ⁻¹`,
  i.e. `(ρ⁻¹).RightUnique`.

Layer target: `bridge/view`.
-/

/- Definition 26.0.3: the canonical owner of “one-to-one” for a multivalued mapping is the
relation predicate `Relator.BiUnique`. -/
recall Relator.BiUnique

namespace SetRel

-- `SetRel.LeftUnique` and `SetRel.BiUnique` are part of the base Chapter 26 owner layer in
-- `Definition_26_0_1`; this file provides source-facing inverse/order bridge theorems.

/-- Inverse single-valuedness is exactly the left-uniqueness clause on the original relation. -/
@[simp] theorem rightUnique_inv_iff_leftUnique (ρ : SetRel α β) :
    (ρ⁻¹).RightUnique ↔ ρ.LeftUnique := by
  constructor
  · intro h a b c hac hbc
    exact h (by simpa [SetRel.mem_inv] using hac) (by simpa [SetRel.mem_inv] using hbc)
  · intro h c a b hca hcb
    exact h (by simpa [SetRel.mem_inv] using hca) (by simpa [SetRel.mem_inv] using hcb)

/-! The inverse bridge is symmetric: inverse left-uniqueness is right-uniqueness of the original
relation, and one-to-one-ness is invariant under inversion. -/

/-- Inverse left-uniqueness is exactly the right-uniqueness clause on the original relation. -/
@[simp] theorem leftUnique_inv_iff_rightUnique (ρ : SetRel α β) :
    (ρ⁻¹).LeftUnique ↔ ρ.RightUnique := by
  constructor
  · intro h c a b hca hcb
    exact h (by simpa [SetRel.mem_inv] using hca) (by simpa [SetRel.mem_inv] using hcb)
  · intro h a b c hac hbc
    exact h (by simpa [SetRel.mem_inv] using hac) (by simpa [SetRel.mem_inv] using hbc)

/-! Definition 26.0.3 has intrinsic canonical decomposition in terms of left- and right-uniqueness
on `ρ`, with source-order and source-inverse phrasings kept as bridge theorems. -/

/-- Canonical owner decomposition: one-to-one means left- and right-uniqueness on `ρ`
itself, in the intrinsic owner order of `Relator.BiUnique`. -/
@[simp] theorem biUnique_iff_leftUnique_and_rightUnique (ρ : SetRel α β) :
    ρ.BiUnique ↔
      ρ.LeftUnique ∧ ρ.RightUnique := by
  rw [SetRel.BiUnique, SetRel.LeftUnique, SetRel.RightUnique, Relator.BiUnique]

/-- Source-order bridge of Definition 26.0.3: one-to-one means right- and left-uniqueness on
`ρ` itself. -/
theorem biUnique_iff_rightUnique_and_leftUnique (ρ : SetRel α β) :
    ρ.BiUnique ↔
      ρ.RightUnique ∧ ρ.LeftUnique := by
  rw [biUnique_iff_leftUnique_and_rightUnique, and_comm]

/-- Definition 26.0.3 in the source inverse wording: `ρ` is one-to-one exactly when both
`ρ` and `ρ⁻¹` are single-valued. -/
theorem biUnique_iff_rightUnique_and_inv_rightUnique (ρ : SetRel α β) :
    ρ.BiUnique ↔
      ρ.RightUnique ∧ (ρ⁻¹).RightUnique := by
  rw [biUnique_iff_rightUnique_and_leftUnique, rightUnique_inv_iff_leftUnique]

/-- One-to-one-ness of a multivalued mapping relation is invariant under inversion. -/
@[simp] theorem biUnique_inv_iff (ρ : SetRel α β) :
    (ρ⁻¹).BiUnique ↔ ρ.BiUnique := by
  rw [biUnique_iff_leftUnique_and_rightUnique (ρ := ρ⁻¹)]
  rw [leftUnique_inv_iff_rightUnique (ρ := ρ), rightUnique_inv_iff_leftUnique (ρ := ρ)]
  rw [and_comm]
  rw [biUnique_iff_leftUnique_and_rightUnique (ρ := ρ)]

end SetRel

end
