import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_12_2_1 (from Chap03) -/
noncomputable section

universe u v

open scoped Rockafellar

section

variable {𝕜 : Type v} {E : Type u}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsOrderedAddMonoid 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 12.2.1 says that Fenchel conjugation `f ↦ f*` is a symmetric
  one-to-one correspondence on the class of closed proper convex functions on finite-dimensional
  paired spaces.
- `core/canonical`: the project owners already present are `convexConjugate` for Fenchel
  conjugation and the owner predicate `f.IsClosedProperConvex` for the admissible class, both on
  arbitrary finite-dimensional scalar spaces equipped with a continuous linear self-pairing.
- `bridge/view`: the textbook phrase "symmetric one-to-one correspondence" is rendered by the
  canonical set-level notion `Set.BijOn`, together with the companion involution statement
  `convexConjugate (convexConjugate f) = f` on that class.

Domain-style sampling used here:
- the project owner `convexConjugate`;
- the chapter owner predicate `Function.IsClosedProperConvex`;
- Theorem 12.2 declarations `Function.IsConvex.convexConjugate_isProper_iff`,
  `Function.isConvex_convexConjugate`, and
  `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`;
- the closure owner theorem `lowerSemicontinuousHull_eq_self`.

Primitive data vs derived API:
- primitive input: a function `f : E → WithBotTop 𝕜` together with the owner hypothesis
  `f.IsClosedProperConvex`;
- derived API: stability under conjugation and the induced bijection of the class with itself.

Codomain/scalar layer note:
- this item is stated directly on the scalar-generic chapter layer `WithBotTop 𝕜` and does not
  keep a parallel codomain-specialized surface.

Layer target:
- `core/canonical` for the companion owner lemmas
  `Function.IsClosedProperConvex.convexConjugate` and
  `Function.IsClosedProperConvex.biconjugate_eq`;
- `source-facing` for the correspondence theorem, stated directly as a theorem about the canonical
  conjugacy operator on the canonical class of closed proper convex functions, with no surrogate
  package or subtype wrapper.
-/

-- Proof sketch: Theorem 12.2 shows that the conjugate of any function is lower semicontinuous and
-- convex, and that properness is preserved on convex functions. Thus `convexConjugate` maps the
-- class of functions satisfying `Function.IsClosedProperConvex` to itself. Theorem 12.2 also gives
-- `f** = lowerSemicontinuousHull f` for convex `f`; applying this to `f` and then to `f⋆` yields
-- `cl(f⋆) = f⋆`, so closedness of the conjugate is recovered intrinsically from biconjugacy and
-- closure identities. Hence conjugation is its own inverse on that class and defines a bijection
-- of it with itself.
namespace Function.IsClosedProperConvex

section

variable [HasPairingSwap E E 𝕜]

/-- The class of closed proper convex functions on a finite-dimensional scalar space with a
continuous linear self-pairing is stable under Fenchel conjugation. -/
theorem convexConjugate {f : E → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f) :
    IsClosedProperConvex[𝕜] (f⋆ : E → WithBotTop 𝕜) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (Function.isConvex_convexConjugate (𝕜 := 𝕜) (f := f))
  · exact (Function.IsConvex.convexConjugate_isProper_iff (𝕜 := 𝕜) (f := f) hf.convex).2 hf.proper
  · simpa using (lowerSemicontinuous_convexConjugate (𝕜 := 𝕜) (f := f))

end

section

variable [OrderTopology 𝕜]

/-- Closed proper convex functions agree with their Fenchel biconjugates. -/
theorem biconjugate_eq {f : E → WithBotTop 𝕜} (hf : IsClosedProperConvex[𝕜] f) :
    f⋆⋆ = f := by
  calc
    f⋆⋆ = cl(f) := Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull (𝕜 := 𝕜) hf.convex
    _ = f := lowerSemicontinuousHull_eq_self hf.closed

end

end Function.IsClosedProperConvex

variable [HasPairingSwap E E 𝕜] [OrderTopology 𝕜]

/-- Corollary 12.2.1: Fenchel conjugation induces a symmetric one-to-one correspondence on the
class of all closed proper convex functions on a finite-dimensional topological vector space with
continuous linear self-pairing, expressed here as a bijection of that class with itself. -/
theorem convexConjugate_bijOn_closedProperConvexFunctions :
    Set.BijOn
      (fun f : E → WithBotTop 𝕜 ↦ (f⋆ : E → WithBotTop 𝕜))
      {f : E → WithBotTop 𝕜 | IsClosedProperConvex[𝕜] f}
      {f : E → WithBotTop 𝕜 | IsClosedProperConvex[𝕜] f} := by
  let S : Set (E → WithBotTop 𝕜) := {f | IsClosedProperConvex[𝕜] f}
  have hmaps :
      Set.MapsTo
        (fun f : E → WithBotTop 𝕜 ↦ (f⋆ : E → WithBotTop 𝕜))
        S S := by
    intro f hf
    exact hf.convexConjugate
  have hinv :
      Set.InvOn
        (fun f : E → WithBotTop 𝕜 ↦ (f⋆ : E → WithBotTop 𝕜))
        (fun f : E → WithBotTop 𝕜 ↦ (f⋆ : E → WithBotTop 𝕜))
        S S := by
    constructor <;> intro f hf <;>
      exact Function.IsClosedProperConvex.biconjugate_eq hf
  simpa [S] using hinv.bijOn hmaps hmaps

end

/-! ### Text_12_2_1 (from Chap03) -/
universe u v w

section

open scoped Rockafellar

variable {X : Type u} {Y : Type v} {L : Type w}
variable [CompleteSemilatticeSup L] [Sub L] [HasPairing X Y L]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.1 states that if `f₁ ≤ f₂` pointwise, then the conjugates satisfy
  the reverse pointwise inequality `f₂⋆ ≤ f₁⋆`.
- `core/canonical`: the owner abstraction is the order-reversing conjugation operator
  `convexConjugate : (X → L) → Y → L`.
- `bridge/view`: the scoped postfix notation `f⋆` and the textbook two-function implication
  `f₁ ≤ f₂ → f₂⋆ ≤ f₁⋆` are direct specializations of that owner-level `Antitone` statement.

Domain-style sampling used here:
- `convexConjugate` and its scoped notation `f⋆`;
- the owner formula `convexConjugate_eq_iSup_pairing_sub`;
- `Antitone` for order-reversing owner maps;
- codomain-side subtraction antitonicity in the primitive form
  `∀ a : L, Antitone (fun b : L ↦ a - b)`, together with complete-sup order on `L`-valued
  functions.

Primitive data vs derived API:
- primitive owner data: the pairing-valued conjugation operator `convexConjugate`;
- derived API: the two-function order-reversal statement obtained by applying owner antitonicity
  once.

Layer target: `core/canonical`; Text 12.2.1 is completed by the owner theorem itself, and the
source-facing two-function inequality is recovered by applying it to a pointwise comparison.
-/

-- Proof sketch: the hypothesis `f₁ x ≤ f₂ x` implies
-- `⟪x, y⟫ₚ - f₂ x ≤ ⟪x, y⟫ₚ - f₁ x` for every `x`, and taking the supremum over `x`
-- preserves that pointwise order. This is exactly the antitonicity of Fenchel conjugation.
/-- Core owner form of Text 12.2.1: Fenchel conjugation is order reversing whenever subtraction is
antitone in its right argument. -/
theorem convexConjugate_antitone_of_subRightAntitone
    (hsub : ∀ a : L, Antitone (fun b : L ↦ a - b)) :
    Antitone (convexConjugate : (X → L) → Y → L) := by
  intro f₁ f₂ h y
  rw [convexConjugate_eq_iSup_pairing_sub, convexConjugate_eq_iSup_pairing_sub]
  change sSup (Set.range (fun x : X ↦ ⟪x, y⟫ₚ - f₂ x)) ≤
      sSup (Set.range (fun x : X ↦ ⟪x, y⟫ₚ - f₁ x))
  refine sSup_le ?_
  intro z hz
  rcases hz with ⟨x, rfl⟩
  exact (hsub (⟪x, y⟫ₚ)) (h x) |>.trans
    (le_sSup ⟨x, rfl⟩)

section WithBotTop

variable {α : Type w}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [HasPairing X Y α]

/-- Text 12.2.1: on the chapter-canonical codomain `WithBotTop α`, Fenchel conjugation is order
reversing: if `f₁ ≤ f₂`, then `f₂⋆ ≤ f₁⋆`. -/
theorem convexConjugate_antitone :
    Antitone (convexConjugate : (X → WithBotTop α) → Y → WithBotTop α) := by
  refine convexConjugate_antitone_of_subRightAntitone (X := X) (Y := Y)
      (L := WithBotTop α) ?_
  intro a b c hbc
  exact WithBotTop.sub_le_sub le_rfl hbc

/-- Text 12.2.1, source-facing two-function form on `WithBotTop α`: `f₁ ≤ f₂` implies
`f₂⋆ ≤ f₁⋆`. -/
theorem convexConjugate_le_convexConjugate_of_le
    {f₁ f₂ : X → WithBotTop α} (h : f₁ ≤ f₂) :
    f₂⋆ ≤ (f₁⋆ : Y → WithBotTop α) :=
  convexConjugate_antitone h

end WithBotTop

end

/-! ### Corollary_12_2_2 (from Chap03) -/
noncomputable section

universe u v w

open scoped Rockafellar

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
variable [TopologicalSpace (WithBotTop 𝕜)] [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 12.2.2 says that, for a convex function on a finite-dimensional
  normed primal space, the Fenchel supremum defining `f*` may be restricted from the ambient
  primal space to `ri (dom f)`.
- `core/canonical`: the owner abstraction is the project declaration `convexConjugate`.
- `bridge/view`: Rockafellar's `dom f` is represented by the chapter's effective-domain notation
  `dom(f)`, and `ri` is represented by `riDom[𝕜](f) = intrinsicInterior 𝕜 dom(f)`.

Domain-style sampling used here:
- the project owner `convexConjugate`;
- the paired-space closure-invariance theorem
  `convexConjugate_lowerSemicontinuousHull_eq_of_pairingSlices`;
- the primitive pairing-slice lower-semicontinuity hypothesis
  `LowerSemicontinuous (fun x ↦ (⟪x, y⟫ₚ : WithBotTop 𝕜))` at the selected dual point `y`;
- the closure-from-relative-interior theorem
  `cl_eq_of_riDom_eq_and_eqOn`;
- the idempotence theorem `ri_idem` for the relative interior bridge
  `riDom[𝕜](g) = riDom[𝕜](f)`.

Primitive data vs derived API:
- primitive inputs: a convex function `f : X → WithBotTop 𝕜` on a finite-dimensional normed
  `𝕜`-space, a dual point `y : Y`, and the pairing-slice lower-semicontinuity data
  `hpair : LowerSemicontinuous (fun x ↦ (⟪x, y⟫ₚ : WithBotTop 𝕜))`;
- derived API: the restriction of the conjugate supremum to the relative interior of the effective
  domain of `f`.

Codomain/scalar canonicalization note:
- both statement and proof are written directly on the scalar-generic owner layer
  `WithBotTop 𝕜`, with no codomain-specialization coercion bridge in the pairing-slice
  continuity step.

Layer target: `source-facing`; the corollary is stated directly as a conjugate formula in the
owner language, without introducing a restriction wrapper.
- Ambient refinement: the proof uses only the finite-dimensional normed geometry of
  `riDom[𝕜](f)` on the primal side together with the paired-space closure invariance of
  `convexConjugate` from Theorem 12.2, so coordinate-model wording is treated as a
  downstream specialization rather than as the owner abstraction.
-/

-- Proof sketch: let `g` agree with `f` on `intrinsicInterior 𝕜 {x : X | f x < ⊤}` and take the
-- value `⊤` outside that set. The restricted supremum is then `convexConjugate g y` by the
-- defining formula for conjugation. Corollary 7.3.4 gives
-- `cl(g) = cl(f)`, so Theorem 12.2 identifies
-- `convexConjugate g = convexConjugate f`.
namespace Function.IsConvex

/-- Corollary 12.2.2: for a convex function `f` on a finite-dimensional normed `𝕜`-space, the
supremum defining `f⋆ y` may be restricted to the relative interior `ri (dom f)`, represented
here by the subtype `riDom[𝕜](f)`.
The dual variable lives in an arbitrary paired space `Y`; the only extra owner input beyond the
primal geometry is lower semicontinuity of the selected pairing slice at `y`. -/
theorem convexConjugate_eq_iSup_pairing_sub_riDom
    {f : X → WithBotTop 𝕜} (hf : f.IsConvex 𝕜)
    (y : Y) (hpair : LowerSemicontinuous (fun x : X ↦ (⟪x, y⟫ₚ : WithBotTop 𝕜))) :
    f⋆ y = ⨆ x : riDom[𝕜](f), ⟪x, y⟫ₚ - f x := by
  classical
  let S : Set X := riDom[𝕜](f)
  let g : X → WithBotTop 𝕜 := S.piecewise f ⊤
  have hS_convex : Convex 𝕜 S := by
    simpa [S] using hf.convex_dom.intrinsicInterior
  have hS_idem : intrinsicInterior 𝕜 S = S := by
    change intrinsicInterior 𝕜 (intrinsicInterior 𝕜 dom(f)) = intrinsicInterior 𝕜 dom(f)
    exact ri_idem (𝕜 := 𝕜) (C := dom(f))
  have hg : g.IsConvex 𝕜 := by
    rw [Function.isConvex_iff_convex_epigraph]
    have hset :
        {p : X × 𝕜 | g p.1 ≤ p.2} =
          (S ×ˢ (Set.univ : Set 𝕜)) ∩ {p : X × 𝕜 | f p.1 ≤ p.2} := by
      ext p
      by_cases hp : p.1 ∈ S <;> simp [g, hp]
    change Convex 𝕜 ({p : X × 𝕜 | g p.1 ≤ (p.2 : WithBotTop 𝕜)})
    rw [hset]
    exact (hS_convex.prod convex_univ).inter hf.convex_epigraph
  have hdom : dom(g) = S := by
    ext x
    constructor
    · intro hxg
      by_contra hxS
      have hxg' : g x < ⊤ := by simpa [mem_effectiveDomain] using hxg
      have hgx : g x = ⊤ := by simp [g, hxS]
      exact (not_lt_of_ge le_rfl) (hgx ▸ hxg')
    · intro hx
      have hfx : f x < ⊤ := by
        simpa [S] using (intrinsicInterior_subset hx : x ∈ dom(f))
      simpa [mem_effectiveDomain, g, hx] using hfx
  have hri : riDom[𝕜](f) = riDom[𝕜](g) := by
    calc
      riDom[𝕜](f) = S := by simp [S]
      _ = intrinsicInterior 𝕜 S := hS_idem.symm
      _ = riDom[𝕜](g) := by simp [hdom]
  have hfg : Set.EqOn f g riDom[𝕜](f) := by
    intro x hx
    have hxS : x ∈ S := by simpa [S] using hx
    simp [g, hxS]
  have hcl : cl(f) = cl(g) :=
    hf.cl_eq_of_riDom_eq_and_eqOn hg hri hfg
  have hcl_conj_eval :
      ∀ h : X → WithBotTop 𝕜,
        (cl(h)⋆ : Y → WithBotTop 𝕜) y = h⋆ y := by
    intro h
    letI : HasPairing X Unit 𝕜 := ⟨fun x _ ↦ (⟪x, y⟫ₚ : 𝕜)⟩
    have hpair_unit :
        ∀ u : Unit, LowerSemicontinuous (fun x : X ↦ (⟪x, u⟫ₚ : WithBotTop 𝕜)) := by
      intro u
      cases u
      simpa using hpair
    have hconj_unit :
        (cl(h)⋆ : Unit → WithBotTop 𝕜) = (h⋆ : Unit → WithBotTop 𝕜) :=
      convexConjugate_lowerSemicontinuousHull_eq_of_pairingSlices h hpair_unit
    have hunit :
        (cl(h)⋆ : Unit → WithBotTop 𝕜) () =
          (h⋆ : Unit → WithBotTop 𝕜) () :=
      congrFun hconj_unit ()
    simpa [convexConjugate] using hunit
  have hconj : f⋆ y = g⋆ y := by
    calc
      f⋆ y = (cl(f)⋆ : Y → WithBotTop 𝕜) y := (hcl_conj_eval f).symm
      _ = (cl(g)⋆ : Y → WithBotTop 𝕜) y := by simp [hcl]
      _ = g⋆ y := hcl_conj_eval g
  have hg_formula :
      g⋆ y = ⨆ x : riDom[𝕜](f), ⟪x, y⟫ₚ - f x := by
    rw [convexConjugate_eq_iSup_pairing_sub]
    apply le_antisymm
    · refine iSup_le fun x ↦ ?_
      by_cases hx : x ∈ S
      · calc
          ⟪x, y⟫ₚ - g x = ⟪x, y⟫ₚ - f x := by
            simp [g, hx]
          _ ≤ ⨆ z : riDom[𝕜](f), ⟪z, y⟫ₚ - f z :=
            le_iSup_of_le ⟨x, by simpa [S] using hx⟩ le_rfl
      · simp [g, hx]
    · refine iSup_le fun x ↦ ?_
      have hx : (x : X) ∈ S := by
        change (x : X) ∈ riDom[𝕜](f)
        exact x.property
      calc
        ⟪x, y⟫ₚ - f x = ⟪x, y⟫ₚ - g x := by simp [g, hx]
        _ ≤ ⨆ z : X, ⟪z, y⟫ₚ - g z := le_iSup (fun z : X ↦ ⟪z, y⟫ₚ - g z) (x : X)
  calc
    f⋆ y = g⋆ y := hconj
    _ = ⨆ x : riDom[𝕜](f), ⟪x, y⟫ₚ - f x := hg_formula

end Function.IsConvex

end

/-! ### Text_12_2_2 (from Chap03) -/
universe u v w

noncomputable section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.2 studies pairs `(f, g)` of extended-valued functions,
  specialized in the source to `R^n`, satisfying the generalized Fenchel inequality and ordered
  pointwise by simultaneous tightening.
- `core/canonical`: the owner construction for conjugation is `convexConjugate`, and the ambient
  order is the canonical product order on `(X → L) × (Y → L)`, specialized below to
  `WithBotTop α` where conjugacy is used.
- `bridge/view`: the textbook set `𝒲` is rendered by the owner `fenchelAdmissiblePairs`
  (notation `𝒲`), while pointwise admissibility is rendered by `isFenchelPair`. Textbook
  minimality is rendered as `Minimal 𝒲` on function pairs. The owner-side comparison data is the
  pointwise inequality `f⋆ ≤ g`, with the converse recovered only under the exact no-`⊥`
  hypotheses forced by Fenchel admissibility.

Domain-style sampling used here:
- `convexConjugate`;
- `convexConjugate_antitone`;
- `fenchelAdmissiblePairs` (notation `𝒲`);
- `Minimal` for order-theoretic minimality in a partial order.

Primitive data vs derived API:
- primitive inputs: a pair of functions `f : X → L` and `g : Y → L`;
- primitive pairing data is the codomain-level owner `HasPairing X Y L`; in the conjugacy layer,
  `L = WithBotTop α` is supplied by the canonical lift from a scalar pairing;
- primitive owner relation introduced here: `isFenchelPair f g` at weak assumptions
  `[LE L] [Add L]`;
- product owner/set view: `fenchelAdmissiblePairs` with notation `𝒲`;
- derived API: symmetry of the admissibility relation under a swap-compatible pairing identity, the
  owner inequality `isFenchelPair f g → f⋆ ≤ g`, the atomic left/right no-`⊥` consequences under
  opposite-side nonemptiness, its converse under the sharp no-`⊥` side conditions, and the
  minimality criterion.

Layer target: `source-facing`; the item remains a direct theorem about admissible pairs and
mutual Fenchel conjugacy. The source writes this on `R^n`, while the canonical chapter codomain is
`WithBotTop α`; the declarations are therefore stated directly on paired spaces
`HasPairing X Y α` (with canonical codomain lift to `WithBotTop α`) rather than on a concrete
real self-model.
-/

section FenchelPairOwner

variable {L : Type v} [LE L] [Add L]
variable {X : Type u} {Y : Type w} [HasPairing X Y L]

/-- A Fenchel-admissible pair is a pair of `L`-valued functions on paired spaces, satisfying the
generalized Fenchel inequality `⟪x, y⟫ₚ ≤ f x + g y` for all `x` and `y`. -/
def isFenchelPair (f : X → L) (g : Y → L) : Prop :=
  ∀ x : X, ∀ y : Y, ⟪x, y⟫ₚ ≤ f x + g y

/-- The textbook Fenchel-admissible set `𝒲`, viewed as a predicate on pairs of functions. -/
def fenchelAdmissiblePairs : Set ((X → L) × (Y → L)) :=
  {fg | isFenchelPair fg.1 fg.2}

scoped[Rockafellar] notation "𝒲" => fenchelAdmissiblePairs

@[simp] theorem mem_fenchelAdmissiblePairs
    (f : X → L) (g : Y → L) :
    (f, g) ∈ 𝒲 ↔ isFenchelPair f g :=
  Iff.rfl

-- Proof sketch: swap `x` and `y` and use `HasPairingSwap.pairing_swap`.
/-- The generalized Fenchel inequality is symmetric in the two functions. -/
@[simp]
theorem isFenchelPair_comm
    [HasPairing Y X L] [HasPairingSwap X Y L]
    (f : X → L) (g : Y → L) :
    isFenchelPair f g ↔ isFenchelPair g f := sorry

end FenchelPairOwner

section ConjugacyLayer

variable {α : Type v} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
  [IsOrderedAddMonoid α]
variable {X : Type u} {Y : Type w} [HasPairing X Y α]

-- Proof sketch: rewrite `⟪x, y⟫ₚ ≤ f x + g y` as `⟪x, y⟫ₚ - f x ≤ g y` and take the supremum over
-- `x` to obtain `f⋆ y ≤ g y`.
/-- A Fenchel-admissible pair gives the owner-side conjugate inequality `f⋆ ≤ g`. -/
theorem convexConjugate_le_of_isFenchelPair
    (f : X → WithBotTop α) (g : Y → WithBotTop α) (hfg : isFenchelPair f g) :
    f⋆ ≤ g := sorry

-- Proof sketch: for fixed `x`, choose `y` from the nonempty right space. If
-- `⟪x, y⟫ₚ ≤ f x + g y` and `f x = ⊥`, then the right side is `⊥`, impossible because pairing
-- values lie in `α` and therefore are not `⊥`.
/-- If the right space is nonempty, a Fenchel-admissible pair has no `-∞` values in its left
component. -/
theorem isFenchelPair_left_ne_bot
    (f : X → WithBotTop α) (g : Y → WithBotTop α)
    (hy : Nonempty Y) (hfg : isFenchelPair f g) (x : X) :
    f x ≠ ⊥ := sorry

/-- If the left space is nonempty, a Fenchel-admissible pair has no `-∞` values in its right
component. -/
theorem isFenchelPair_right_ne_bot
    (f : X → WithBotTop α) (g : Y → WithBotTop α)
    (hx : Nonempty X) (hfg : isFenchelPair f g) (y : Y) :
    g y ≠ ⊥ := sorry

-- Proof sketch: from `f⋆ y ≤ g y`, each affine defect `⟪x, y⟫ₚ - f x` is bounded
-- above by `g y`. The hypotheses `f x ≠ ⊥` and `g y ≠ ⊥` are exactly the side conditions needed
-- for `sub_le_iff_le_add`, which converts this defect bound back to
-- `⟪x, y⟫ₚ ≤ f x + g y`.
/-- The owner inequality `f⋆ ≤ g` recovers the generalized Fenchel inequality once both functions
avoid the value `-∞`; with nonempty opposite-side spaces, admissibility forces exactly these
side conditions. -/
theorem isFenchelPair_of_convexConjugate_le_of_ne_bot
    (f : X → WithBotTop α) (g : Y → WithBotTop α)
    (hf : ∀ x : X, f x ≠ ⊥) (hg : ∀ y : Y, g y ≠ ⊥)
    (hfg : f⋆ ≤ g) :
    isFenchelPair f g := sorry

-- Proof sketch: combine the forward owner inequality with the converse under the no-`⊥`
-- hypotheses.
/-- Under the sharp no-`⊥` hypotheses, Fenchel admissibility is equivalent to the owner inequality
`f⋆ ≤ g`. -/
theorem isFenchelPair_iff_convexConjugate_le_of_ne_bot
    (f : X → WithBotTop α) (g : Y → WithBotTop α)
    (hf : ∀ x : X, f x ≠ ⊥) (hg : ∀ y : Y, g y ≠ ⊥) :
    isFenchelPair f g ↔ f⋆ ≤ g := sorry

-- Proof sketch: from minimality, first read off admissibility and then, using nonemptiness on
-- both sides, read off the no-`⊥` conditions from `isFenchelPair_left_ne_bot` and
-- `isFenchelPair_right_ne_bot`. The owner inequalities
-- `f⋆ ≤ g` and `g⋆ ≤ f` follow from
-- `convexConjugate_le_of_isFenchelPair` and symmetry. If `(f', g')` is an admissible smaller pair,
-- antitonicity of conjugation forces `g ≤ f'* ≤ g'` and `f ≤ g'* ≤ f'`, so minimality makes the
-- owner equalities sharp. Conversely, if `(f, g)` is admissible and mutually conjugate, then any
-- admissible smaller pair has the same owner inequalities, and the same antitonicity argument
-- forces equality.
/-- Text 12.2.2: a pair `(f, g)` is a minimal element among the Fenchel-admissible pairs, ordered
pointwise by simultaneous tightening, if and only if `f` and `g` are mutually conjugate:
`g = f⋆` and `f = g⋆`. Over arbitrary `WithBotTop α`-valued functions the admissibility clause is
not redundant, because mutual conjugacy alone does not rule out the `⊤`/`⊥` pathologies of the
extended codomain. -/
theorem minimal_fenchel_pair_iff_mutually_conjugate
    [HasPairing Y X α] [HasPairingSwap X Y α]
    (hx : Nonempty X) (hy : Nonempty Y)
    (f : X → WithBotTop α) (g : Y → WithBotTop α) :
    Minimal 𝒲 (f, g) ↔
      (f, g) ∈ 𝒲 ∧ g = f⋆ ∧ f = g⋆ := sorry

end ConjugacyLayer

/-! ### Theorem_12_2 (from Chap03) -/
noncomputable section

universe u v w

open scoped Rockafellar

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [TopologicalSpace Y] [Sub (WithTopBot 𝕜)] [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 12.2 records the basic duality properties of the conjugate of a convex
  function on `R^n`: closedness, convexity, properness equivalence, invariance under closure, and
  biconjugacy.
- `core/canonical`: the owner declarations already present in the project are
  `convexConjugate`, its scoped notation `f⋆`, `Function.IsConvex`, `Function.IsProper`, and
  `lowerSemicontinuousHull` with its scoped notation `cl(f)`, with
  `ConvexOn 𝕜 Set.univ` as the canonical convexity owner surface and
  `Function.IsConvex` retained as a bridge for downstream compatibility.
- `bridge/view`: Rockafellar's closure notation `cl(f)` is rendered by the project owner
  `lowerSemicontinuousHull f`, and the biconjugate `f**` is rendered by the owner notation `f⋆⋆`.

Domain-style sampling used here:
- the chapter owner `convexConjugate` from `Defn_12_2`;
- the chapter owner predicates `Function.IsConvex` and `Function.IsProper`;
- the chapter owner theorem `Function.IsConvex.iSup` for pointwise suprema from Theorem 5.5;
- the chapter owner theorem `Function.isConvex_supportFunction` from `Text_5_5_0`, which fixes the
  correct linear-pairing abstraction layer for dual-variable convexity statements;
- the project owner `lowerSemicontinuousHull` from `Text_7_0_4`;
- mathlib's canonical predicate `LowerSemicontinuous`.

Primitive data vs derived API:
- the primitive inputs for clauses `(1)` and `(4)` are a pairing
  `HasPairing X Y 𝕜`, the primal function `f : X → WithTopBot 𝕜`, and only the extra
  topological structure used by the corresponding owner theorem;
- the primitive input for clause `(2)` is the same primal function together with the canonical
  linear-pairing owner `HasLinearPairing X Y 𝕜`, since convexity in the dual variable uses the
  linearity of each slice `y ↦ ⟪x, y⟫ₚ`, and the codomain-general owner form now lives on
  `WithTopBot 𝕜`;
- the primitive input for clauses `(3)` and `(5)` is a function
  `f : E → WithTopBot 𝕜`, together with the source hypothesis
  `ConvexOn 𝕜 Set.univ f` plus a finite-dimensional scalar-field ambient carrying a continuous
  linear self-pairing;
- the derived API consists of the closedness, convexity, properness, closure-invariance, and
  biconjugacy statements for `f⋆`, with clauses `(1)` and `(4)` stated at the paired-space
  topological layer needed for lower semicontinuity of pairing slices, clause `(2)` stated at the
  canonical linear-pairing layer (including the codomain-general `WithTopBot 𝕜` owner form) needed
  for convexity via `ConvexOn 𝕜 Set.univ`, and clauses `(3)` and `(5)` stated on finite-dimensional
  scalar-field spaces through the pairing owner instead of an inner-product-space owner.

Layer target: `source-facing`; the theorem is stated directly in terms of the project owner
declarations rather than through an auxiliary package. The source's `R^n` wording is rendered on
the stronger reusable owner ambient of paired spaces for clauses `(1)` and `(4)`, on the
canonical linear-pairing owner for clause `(2)`, and on finite-dimensional scalar-field spaces with
continuous linear self-pairing for clauses `(3)` and `(5)`, so the file avoids a separate
Euclidean-model wrapper.
-/

-- Proof sketch: view `f⋆` as the pointwise supremum of the affine functions
-- `y ↦ ⟪y, x⟫ - f x`. Each such affine function is lower semicontinuous, and lower semicontinuity
-- is preserved under arbitrary pointwise suprema.
/-- Theorem 12.2 (1): the conjugate `f⋆` of any extended-codomain-valued function is closed,
expressed here as lower semicontinuity. The Euclidean source statement is lifted to the canonical
paired-space owner layer by assuming only lower semicontinuity of the pairing slices on the dual
side. -/
theorem lowerSemicontinuous_convexConjugate_of_pairingSlices
    (f : X → WithTopBot 𝕜)
    (hpair : ∀ x : X, LowerSemicontinuous (fun y : Y ↦ ((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜))) :
    LowerSemicontinuous (f⋆ : Y → WithTopBot 𝕜) := sorry

end

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

-- Proof sketch: rewrite `f⋆` as the pointwise supremum of the affine functions
-- `y ↦ ⟪x, y⟫ - f x`. The linear-pairing owner `HasLinearPairing X Y 𝕜` provides the linearity of
-- each dual-variable slice `y ↦ ⟪x, y⟫ₚ`, so each summand is convex and the supremum is convex.
/-- Theorem 12.2 (2), canonical owner form: the conjugate `f⋆` of any
`WithTopBot 𝕜`-valued function is convex on `Set.univ`. The canonical owner layer here is a linear
pairing, not a raw pairing, because convexity in the dual variable uses the linearity of the
pairing slices. -/
theorem Function.convexOn_univ_convexConjugate
    (f : X → WithTopBot 𝕜) :
    ConvexOn 𝕜 (Set.univ : Set Y) (f⋆ : Y → WithTopBot 𝕜) := sorry

/-- Bridge form of Theorem 12.2 (2) through the chapter owner alias `Function.IsConvex`. -/
theorem Function.isConvex_convexConjugate
    (f : X → WithTopBot 𝕜) :
    (f⋆ : Y → WithTopBot 𝕜).IsConvex 𝕜 := by
  rw [Function.isConvex_iff_convex_epigraph]
  simpa [convexOn_iff_convex_epigraph, Set.mem_univ] using
    (Function.convexOn_univ_convexConjugate (f := f))

end

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable [TopologicalSpace X] [Sub (WithTopBot 𝕜)] [HasPairing X Y 𝕜]

-- Proof sketch: `cl(f) ≤ f`, so monotonicity of conjugation gives one
-- inequality. For the reverse inequality, every affine minorant of `f` is lower semicontinuous,
-- hence also a minorant of `cl(f)`; taking the supremum over affine minorants
-- yields equality of conjugates.
/-- Theorem 12.2 (4): taking the conjugate commutes with Rockafellar's closure `cl(f)`. The
Euclidean source statement is lifted to the canonical paired-space owner layer by assuming only
lower semicontinuity of the primal pairing slices. -/
theorem convexConjugate_lowerSemicontinuousHull_eq_of_pairingSlices
    (f : X → WithTopBot 𝕜)
    (hpair : ∀ y : Y, LowerSemicontinuous (fun x : X ↦ ((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜))) :
    (cl(f)⋆ : Y → WithTopBot 𝕜) = (f⋆ : Y → WithTopBot 𝕜) := sorry

end

section

variable {E : Type u} {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [TopologicalSpace E]
variable [Sub (WithTopBot 𝕜)] [HasPairingSwap E E 𝕜] [HasContinuousPairing E E 𝕜]

/-- Continuity-and-symmetry bridge for Theorem 12.2 (1): on a self-paired space, continuity in
the first variable and pairing symmetry provide lower semicontinuity of the dual-variable slices,
hence lower semicontinuity of the conjugate. -/
private theorem lowerSemicontinuous_convexConjugate_of_continuousPairingSwap
    (f : E → WithTopBot 𝕜) :
    LowerSemicontinuous (f⋆ : E → WithTopBot 𝕜) := sorry

/-- Theorem 12.2 (1), self-pairing canonical owner form: on a self-paired space with pairing
continuity and swap compatibility, the conjugate is lower semicontinuous. -/
theorem lowerSemicontinuous_convexConjugate
    (f : E → WithTopBot 𝕜) :
    LowerSemicontinuous (f⋆ : E → WithTopBot 𝕜) := by
  simpa using lowerSemicontinuous_convexConjugate_of_continuousPairingSwap (f := f)

end

section

variable {E : Type u} {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace E] [Sub (WithTopBot 𝕜)] [HasContinuousPairing E E 𝕜]

/-- Continuity-layer bridge for Theorem 12.2 (4). -/
theorem convexConjugate_lowerSemicontinuousHull_eq
    (f : E → WithTopBot 𝕜) :
    (cl(f)⋆ : E → WithTopBot 𝕜) = (f⋆ : E → WithTopBot 𝕜) := sorry

end

section

variable {E : Type u} {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

namespace Function

-- Proof sketch: if `f` is proper and convex, the supporting-affine-minorant theorem gives a finite
-- affine minorant, which yields a finite point of `f⋆`; the definition of the
-- conjugate rules out the value `-∞`. Conversely, if `f⋆` is proper, apply the same
-- argument to `f⋆`, use biconjugacy below, and read properness back through `cl(f)`.
/-- Theorem 12.2 (3), canonical owner form: for a convex function on `Set.univ` in a
finite-dimensional scalar-field space equipped with a continuous linear self-pairing, the conjugate
`f⋆` is proper if and only if `f` is proper. -/
theorem convexConjugate_isProper_iff_of_convexOn_univ
    {f : E → WithTopBot 𝕜} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    (f⋆ : E → WithTopBot 𝕜).IsProper ↔ f.IsProper := sorry

-- Proof sketch: apply closure-invariance to replace `cl(f)⋆` by `f⋆`, then use the
-- closed-case biconjugacy statement on `cl(f)`.
/-- Theorem 12.2 (5), canonical owner form: for a convex function on `Set.univ` in a
finite-dimensional scalar-field space equipped with a continuous linear self-pairing, the
biconjugate `f⋆⋆` equals the closure `cl(f)`. -/
theorem biconjugate_eq_lowerSemicontinuousHull_of_convexOn_univ
    {f : E → WithTopBot 𝕜} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    f⋆⋆ = cl(f) := sorry

end Function

namespace Function.IsConvex

private theorem convexOn_univ {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) :
    ConvexOn 𝕜 (Set.univ : Set E) f := by
  rw [convexOn_iff_convex_epigraph]
  simpa [Function.isConvex_iff_convex_epigraph, Set.mem_univ] using hf

-- Proof sketch: if `f` is proper and convex, the supporting-affine-minorant theorem gives a finite
-- affine minorant, which yields a finite point of `f⋆`; the definition of the
-- conjugate rules out the value `-∞`. Conversely, if `f⋆` is proper, apply the same
-- argument to `f⋆`, use the biconjugacy theorem below, and read properness back
-- through `cl(f)`.
/-- Theorem 12.2 (3): for a convex function on a finite-dimensional scalar field space equipped
with a continuous linear self-pairing, the
conjugate `f⋆` is proper if and only if `f` is proper. -/
theorem convexConjugate_isProper_iff
    {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) :
    (f⋆ : E → WithTopBot 𝕜).IsProper ↔ f.IsProper := by
  exact Function.convexConjugate_isProper_iff_of_convexOn_univ
    (hf := hf.convexOn_univ)

-- Proof sketch: apply the preceding closure-invariance theorem to replace
-- `cl(f)⋆` by `f⋆`. Then apply the closed-case biconjugacy statement to the closed convex function
-- `cl(f)`.
/-- Theorem 12.2 (5): for a convex function on a finite-dimensional scalar field space equipped
with a continuous linear self-pairing, the
biconjugate `f⋆⋆` equals the closure `cl(f)`. -/
theorem biconjugate_eq_lowerSemicontinuousHull
    {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) :
    f⋆⋆ = cl(f) := by
  exact Function.biconjugate_eq_lowerSemicontinuousHull_of_convexOn_univ
    (hf := hf.convexOn_univ)

end Function.IsConvex

end

/-! ### Text_12_2_3 (from Chap03) -/
noncomputable section

universe u v

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.3 computes the Fenchel conjugate of the indicator of a linear
  subspace `L`, specialized in the source to a subspace of `R^n`, and identifies it with the
  indicator of the orthogonal complement `Lᗮ`.
- `core/canonical`: the owner declarations are the chapter indicator bridge `indicatorFunction`,
  the Fenchel conjugate owner `convexConjugate`, and the pairing-annihilator owner
  `Submodule.pairingOrthogonal`.
- `bridge/view`: the inner-product orthogonal-complement owner `Submodule.orthogonal` is retained
  as the textbook-facing specialization through
  `Submodule.pairingOrthogonal_eq_orthogonal_real`.

Primitive data vs derived API:
- primitive datum: a subspace `L : Submodule 𝕜 X` in paired modules `X` and `Y`;
- derived API: the indicator-conjugacy identity first at `Lᗮₚ : Submodule 𝕜 Y`, then the
  source-facing self-pairing specialization `Lᗮ`.

Layer target: owner-first at `Submodule.pairingOrthogonal`, with a thin bridge theorem for the
textbook orthogonal notation.

Ambient minimization note:
- the owner-side statement is kept at the pairing/scalar-generic Chapter 14 layer;
- the remaining `ℝ` / inner-product specialization is only the textbook bridge `Lᗮ`.
-/

namespace Submodule

section PairingOwner

variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type v} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

-- Proof sketch: apply the owner polar-cone conjugacy theorem to `K = L`, then rewrite
-- the polar cone of a submodule as its pairing annihilator.
/-- Text 12.2.3 at the canonical pairing-owner layer: the Fenchel conjugate of `δ(· | L)` is the
indicator of the pairing annihilator `Lᗮₚ`. -/
theorem convexConjugate_indicatorFunction_eq_indicatorFunction_pairingOrthogonal
    (L : Submodule 𝕜 X) :
    (δ[𝕜](· | L) : X → WithBotTop 𝕜)⋆ =
      (δ[𝕜](· | (Lᗮₚ : Set Y)) : Y → WithBotTop 𝕜) := by
  have hL_nonempty : (L : Set X).Nonempty := ⟨0, L.zero_mem⟩
  have hL_cone : Set.IsCone 𝕜 (L : Set X) := by
    intro c x _ hx
    exact L.smul_mem c hx
  have hpolar :
      (δ[𝕜](· | L) : X → WithBotTop 𝕜)⋆ =
        (δ[𝕜](· | (((L : Set X)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y)) : Y → WithBotTop 𝕜) := by
    simpa using
      (convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone
        (K := (L : Set X)) hL_nonempty hL_cone)
  have hset :
      (((L : Set X)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) = ((Lᗮₚ : Submodule 𝕜 Y) : Set Y) := by
    simpa using (Submodule.polarCone_set_eq_pairingOrthogonal (K := L))
  calc
    (δ[𝕜](· | L) : X → WithBotTop 𝕜)⋆
        = (δ[𝕜](· | (((L : Set X)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y)) : Y → WithBotTop 𝕜) := hpolar
    _ = (δ[𝕜](· | ((Lᗮₚ : Submodule 𝕜 Y) : Set Y)) : Y → WithBotTop 𝕜) := by
      simp [hset]

end PairingOwner

section RealInnerProductBridge

open scoped RealInnerProductSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Text 12.2.3 (source-facing inner-product specialization): the Fenchel conjugate of `δ(· | L)`
is the indicator of the orthogonal complement `Lᗮ`. -/
theorem convexConjugate_indicatorFunction_eq_indicatorFunction_orthogonal
    (L : Submodule ℝ E) :
    (δ[ℝ](· | L) : E → WithBotTop ℝ)⋆ =
      (δ[ℝ](· | (Lᗮ : Set E)) : E → WithBotTop ℝ) := by
  have hpair :
      (δ[ℝ](· | L) : E → WithBotTop ℝ)⋆ =
        (δ[ℝ](· | (Lᗮₚ : Set E)) : E → WithBotTop ℝ) :=
    convexConjugate_indicatorFunction_eq_indicatorFunction_pairingOrthogonal (L := L)
  have hset :
      (Lᗮₚ : Set E) = (Lᗮ : Set E) := by
    simpa using
      congrArg (fun K : Submodule ℝ E => (K : Set E))
        (Submodule.pairingOrthogonal_eq_orthogonal_real L)
  calc
    (δ[ℝ](· | L) : E → WithBotTop ℝ)⋆
        = (δ[ℝ](· | (Lᗮₚ : Set E)) : E → WithBotTop ℝ) := hpair
    _ = (δ[ℝ](· | (Lᗮ : Set E)) : E → WithBotTop ℝ) := by
      simp [hset]

end RealInnerProductBridge

end Submodule

end

/-! ### Text_12_2_4 (from Chap03) -/
noncomputable section

section

open scoped Rockafellar

local instance : HasPairing ℝ ℝ ℝ where
  pairing x y := x * y
local instance : HasPairing ℝ ℝ (WithBotTop ℝ) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item computes the Fenchel conjugate of the scalar exponential function
  `x ↦ exp x`.
- `core/canonical`: the owner is `convexConjugate` on the pairing-based layer from Defn 12.2,
  specialized here to `ℝ` with codomain `WithBotTop ℝ` via `Function.toWithBotTop`.
- `bridge/view`: the explicit branchwise target on `[0, ∞)` written by the canonical extension
  owner `Function.toWithBotTopOn`, together with the textbook scalar Fenchel-supremum formula.

Primitive data vs derived API:
- primitive source-facing data: `Real.exp : ℝ → ℝ`;
- owner theorem surface: `((Real.exp).toWithBotTop)⋆` on the chapter codomain `WithBotTop ℝ`,
  with explicit conjugate branch owner `Function.toWithBotTopOn`;
- derived specification view: the scalar `⨆` formula on `ℝ`.

Abstraction note:
- `ℝ` remains essential in this file because the statement and proof are built on the specific
  real-analytic primitives `Real.exp`, `Real.log`, and their order/derivative inequalities.
  The owner itself stays on the pairing-based abstraction layer (no `RealInnerProductSpace`
  scope on theorem surfaces).
-/

/-- For `a > 0`, the affine-defect function `x ↦ x * a - exp x` is bounded above by
`a * log a - a`. -/
private lemma exp_linear_sub_exp_le_conjugateValue {a x : ℝ} (ha : 0 < a) :
    x * a - Real.exp x ≤ a * Real.log a - a := by
  have h := Real.add_one_le_exp (x - Real.log a)
  have hmul :
      a * ((x - Real.log a) + 1) ≤ a * Real.exp (x - Real.log a) :=
    mul_le_mul_of_nonneg_left h (le_of_lt ha)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hrewrite : a * Real.exp (x - Real.log a) = Real.exp x := by
    calc
      a * Real.exp (x - Real.log a)
          = a * (Real.exp x / Real.exp (Real.log a)) := by simp [Real.exp_sub]
      _ = a * (Real.exp x / a) := by simp [Real.exp_log ha]
      _ = Real.exp x := by
        field_simp [ha0]
  have hmul' : a * ((x - Real.log a) + 1) ≤ Real.exp x := by simpa [hrewrite] using hmul
  have hadd : a * (x - Real.log a) + a ≤ Real.exp x := by
    simpa [mul_add, add_assoc] using hmul'
  have hsub : a * (x - Real.log a) ≤ Real.exp x - a :=
    (le_sub_iff_add_le).2 hadd
  have hsub' : a * x - a * Real.log a ≤ Real.exp x - a := by
    simpa [mul_sub] using hsub
  have hxle : a * x ≤ Real.exp x - a + a * Real.log a := by
    have := add_le_add_right hsub' (a * Real.log a)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have hxle' :
      a * x - Real.exp x ≤ (Real.exp x - a + a * Real.log a) - Real.exp x :=
    sub_le_sub_right hxle (Real.exp x)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_comm, mul_left_comm, mul_assoc] using hxle'

/-- If `a < 0`, the function `x ↦ x * a - exp x` is unbounded above. -/
private lemma exists_gt_linear_sub_exp_of_neg {a μ : ℝ} (ha : a < 0) :
    ∃ x : ℝ, μ < x * a - Real.exp x := by
  have hpos : 0 < -a := by linarith
  have hne : (-a) ≠ 0 := ne_of_gt hpos
  set t : ℝ := max ((μ + 1) / (-a)) 1
  have ht1 : 1 ≤ t := le_max_right _ _
  have htμ : (μ + 1) / (-a) ≤ t := le_max_left _ _
  have hneg : -t < 0 := by linarith
  have hexp : Real.exp (-t) < 1 := (Real.exp_lt_one_iff).2 hneg
  have hmul' : μ + 1 ≤ t * (-a) := by
    have := mul_le_mul_of_nonneg_right htμ (le_of_lt hpos)
    have hleft : ((μ + 1) / (-a)) * (-a) = μ + 1 := by
      calc
        (μ + 1) / (-a) * (-a) = (μ + 1) * (-a) / (-a) := by
          simpa using (div_mul_eq_mul_div (μ + 1) (-a) (-a))
        _ = μ + 1 := by
          simpa using (mul_div_cancel_right₀ (μ + 1) (b := -a) hne)
    simpa [hleft] using this
  refine ⟨-t, ?_⟩
  have hsub_le : μ + 1 - Real.exp (-t) ≤ t * (-a) - Real.exp (-t) :=
    sub_le_sub_right hmul' (Real.exp (-t))
  have hμlt : μ < μ + 1 - Real.exp (-t) := by
    have htmp : μ + 1 - 1 < μ + 1 - Real.exp (-t) := sub_lt_sub_left hexp (μ + 1)
    have hμ1 : μ + 1 - 1 = μ := by ring
    simpa [hμ1] using htmp
  have : μ < t * (-a) - Real.exp (-t) := lt_of_lt_of_le hμlt hsub_le
  have hta : (-t) * a = t * (-a) := by ring
  simpa [hta] using this

/-- For negative `μ`, one can force `-exp x` above `μ` by taking `x` sufficiently negative. -/
private lemma exists_gt_neg_exp_of_neg_mu {μ : ℝ} (hμ : μ < 0) :
    ∃ x : ℝ, μ < -Real.exp x := by
  have hpos : 0 < -μ / 2 := by linarith
  refine ⟨Real.log (-μ / 2), ?_⟩
  have : -Real.exp (Real.log (-μ / 2)) = μ / 2 := by
    simp [Real.exp_log hpos]
    ring
  nlinarith [this]

/-- The `xStar > 0` branch of the Fenchel conjugate formula for `x ↦ exp x`. -/
private lemma exp_convexConjugate_pos_case (xStar : ℝ) (hpos : 0 < xStar) :
    ((Real.exp).toWithBotTop)⋆ xStar =
      (((xStar * Real.log xStar - xStar : ℝ) : WithBotTop ℝ)) := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro x
    have hreal : x * xStar - Real.exp x ≤ xStar * Real.log xStar - xStar :=
      exp_linear_sub_exp_le_conjugateValue (a := xStar) (x := x) hpos
    have hE :
        (((x * xStar - Real.exp x : ℝ) : WithBotTop ℝ)) ≤
          (((xStar * Real.log xStar - xStar : ℝ) : WithBotTop ℝ)) := by
      simpa using hreal
    simpa [Function.toWithBotTop, sub_eq_add_neg, HasPairing.pairing, mul_comm] using hE
  · have hpair_logE :
        (⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) =
          (((xStar * Real.log xStar : ℝ) : WithBotTop ℝ)) := by
      change (((Real.log xStar * xStar : ℝ) : WithBotTop ℝ)) =
        (((xStar * Real.log xStar : ℝ) : WithBotTop ℝ))
      simp [mul_comm]
    have hsup :
        ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) -
            (Real.exp).toWithBotTop (Real.log xStar)) ≤
          (⨆ x : ℝ, ((⟪x, xStar⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) := by
      exact le_iSup (fun x : ℝ => ((⟪x, xStar⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x))
        (Real.log xStar)
    have hsub :
        (((xStar * Real.log xStar - xStar : ℝ) : WithBotTop ℝ)) =
          ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) +
            -((xStar : ℝ) : WithBotTop ℝ)) := by
      have hreal :
          xStar * Real.log xStar - xStar = xStar * Real.log xStar + -xStar := by ring
      calc
        (((xStar * Real.log xStar - xStar : ℝ) : WithBotTop ℝ))
            = (((xStar * Real.log xStar + -xStar : ℝ) : WithBotTop ℝ)) := by
                exact congrArg (fun t : ℝ => (t : WithBotTop ℝ)) hreal
        _ = (((xStar * Real.log xStar : ℝ) : WithBotTop ℝ) + (((-xStar : ℝ) : WithBotTop ℝ))) := by
              simp
        _ = (((xStar * Real.log xStar : ℝ) : WithBotTop ℝ) + -((xStar : ℝ) : WithBotTop ℝ)) := by
              exact congrArg
                (fun t : WithBotTop ℝ =>
                  (((xStar * Real.log xStar : ℝ) : WithBotTop ℝ) + t))
                (WithBotTop.coe_neg xStar)
        _ = ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) + -((xStar : ℝ) : WithBotTop ℝ)) := by
              exact congrArg
                (fun t : WithBotTop ℝ => t + -((xStar : ℝ) : WithBotTop ℝ))
                hpair_logE.symm
    have hlog :
        ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) + -((xStar : ℝ) : WithBotTop ℝ)) =
          ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) -
            (Real.exp).toWithBotTop (Real.log xStar)) := by
      rw [show (Real.exp).toWithBotTop (Real.log xStar) = ((xStar : ℝ) : WithBotTop ℝ) by
        simp [Function.toWithBotTop, Real.exp_log hpos]]
      rfl
    calc
      (((xStar * Real.log xStar - xStar : ℝ) : WithBotTop ℝ))
          = ((⟪Real.log xStar, xStar⟫ₚ : WithBotTop ℝ) -
              (Real.exp).toWithBotTop (Real.log xStar)) := by
              exact hsub.trans hlog
      _ ≤ (⨆ x : ℝ, ((⟪x, xStar⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) := hsup

/-- The `xStar = 0` branch of the Fenchel conjugate formula for `x ↦ exp x`. -/
private lemma exp_convexConjugate_zero_case :
    ((Real.exp).toWithBotTop)⋆ (0 : ℝ) = (0 : WithBotTop ℝ) := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro x
    have hpair0E : (⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) = 0 := by
      simp [HasPairing.pairing]
    have hreal : (0 : ℝ) - Real.exp x ≤ 0 := sub_nonpos.2 (le_of_lt (Real.exp_pos x))
    have hrealE :
        (((0 : ℝ) - Real.exp x : ℝ) : WithBotTop ℝ) ≤ (0 : WithBotTop ℝ) :=
      (WithBotTop.coe_le_coe).2 hreal
    have hE :
        ((⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x) ≤
          (0 : WithBotTop ℝ) := by
      calc
        ((⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)
            = (((0 : ℝ) - Real.exp x : ℝ) : WithBotTop ℝ) := by
                simp [Function.toWithBotTop, hpair0E]
        _ ≤ (0 : WithBotTop ℝ) := hrealE
    exact hE
  · refine (WithBotTop.le_of_forall_lt_iff_le (x := (0 : WithBotTop ℝ))
      (y := (⨆ x : ℝ,
        ((⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)))).2 ?_
    intro μ hμ
    have hμ' : ((μ : ℝ) : WithBotTop ℝ) < ((0 : ℝ) : WithBotTop ℝ) := by
      simpa using hμ
    have hμneg : μ < 0 := (WithBotTop.coe_lt_coe).1 hμ'
    rcases exists_gt_neg_exp_of_neg_mu (μ := μ) hμneg with ⟨x0, hx0⟩
    have hx0E :
        ((μ : ℝ) : WithBotTop ℝ) <
          ((⟪x0, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x0) := by
      have hpair0E : (⟪x0, (0 : ℝ)⟫ₚ : WithBotTop ℝ) = 0 := by
        simp [HasPairing.pairing]
      have hx0' : ((μ : ℝ) : WithBotTop ℝ) < (((-Real.exp x0 : ℝ) : WithBotTop ℝ)) :=
        (WithBotTop.coe_lt_coe).2 hx0
      calc
        ((μ : ℝ) : WithBotTop ℝ) < (((-Real.exp x0 : ℝ) : WithBotTop ℝ)) := hx0'
        _ = ((⟪x0, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x0) := by
          simp [Function.toWithBotTop, hpair0E]
    have hle0 :
        ((⟪x0, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x0) ≤
          (⨆ x : ℝ, ((⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) := by
      exact le_iSup (fun x : ℝ =>
        ((⟪x, (0 : ℝ)⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) x0
    exact lt_of_lt_of_le hx0E hle0

/-- The `xStar < 0` branch of the Fenchel conjugate formula for `x ↦ exp x`. -/
private lemma exp_convexConjugate_neg_case (xStar : ℝ) (hneg : xStar < 0) :
    ((Real.exp).toWithBotTop)⋆ xStar = (⊤ : WithBotTop ℝ) := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  refine (WithBotTop.eq_top_iff_forall_lt _).2 ?_
  intro μ
  rcases exists_gt_linear_sub_exp_of_neg (a := xStar) (μ := μ) hneg with ⟨x0, hx0⟩
  have hx0E : ((μ : ℝ) : WithBotTop ℝ) < (((x0 * xStar - Real.exp x0 : ℝ) : WithBotTop ℝ)) := by
    simpa using hx0
  have hle :
      (((x0 * xStar - Real.exp x0 : ℝ) : WithBotTop ℝ)) ≤
        (⨆ x : ℝ, ((⟪x, xStar⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) := by
    have := le_iSup (fun x : ℝ =>
      ((⟪x, xStar⟫ₚ : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) x0
    simpa [Function.toWithBotTop, sub_eq_add_neg, HasPairing.pairing, mul_comm] using this
  exact lt_of_lt_of_le hx0E hle

-- Proof sketch: split into the three cases `xStar < 0`, `xStar = 0`, and `0 < xStar`; then use
-- explicit branchwise computations of the scalar supremum `⨆ x, x * xStar - exp x`.
/-- Text 12.2.4: the Fenchel conjugate of the exponential function `x ↦ exp x` on `ℝ` is
`xStar * log xStar - xStar` for `xStar > 0`, equals `0` at `xStar = 0`, and is `+∞` for
`xStar < 0`. -/
theorem exp_fenchelConjugate_eq :
    ((Real.exp).toWithBotTop)⋆ =
      Function.toWithBotTopOn (fun xStar : ℝ ↦ xStar * Real.log xStar - xStar) (Set.Ici 0) := by
  funext xStar
  by_cases hnonneg : 0 ≤ xStar
  · rcases lt_or_eq_of_le hnonneg with hpos | hzero
    · simp [Function.toWithBotTopOn, Set.mem_Ici,
        hnonneg, hpos, exp_convexConjugate_pos_case]
    · subst hzero
      simp [Function.toWithBotTopOn, exp_convexConjugate_zero_case]
  · have hneg : xStar < 0 := lt_of_not_ge hnonneg
    simp [Function.toWithBotTopOn, Set.mem_Ici,
      hnonneg, hneg, exp_convexConjugate_neg_case]

/-- Pointwise form of `exp_fenchelConjugate_eq`. -/
theorem exp_fenchelConjugate_eq_apply (xStar : ℝ) :
    ((Real.exp).toWithBotTop)⋆ xStar =
      Function.toWithBotTopOn (fun y : ℝ ↦ y * Real.log y - y) (Set.Ici 0) xStar := by
  simpa using congrFun exp_fenchelConjugate_eq xStar

-- Proof sketch: rewrite the owner theorem by `convexConjugate_eq_iSup_pairing_sub`.
/-- Text 12.2.4 in owner `⨆` form: the same conjugate formula as
`exp_fenchelConjugate_eq`, written through the canonical pairing notation. -/
theorem exp_fenchelConjugate_eq_iSup (xStar : ℝ) :
    (⨆ x : ℝ, (⟪x, xStar⟫ₚ - (Real.exp).toWithBotTop x)) =
      Function.toWithBotTopOn (fun y : ℝ ↦ y * Real.log y - y) (Set.Ici 0) xStar := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    exp_fenchelConjugate_eq_apply xStar

-- Proof sketch: specialize the pairing notation to scalar multiplication on `ℝ`.
/-- Text 12.2.4 in textbook scalar-supremum form: the same conjugate formula as
`exp_fenchelConjugate_eq`, written directly as the scalar Fenchel supremum on `ℝ`. -/
theorem exp_fenchelConjugate_eq_iSup_mul (xStar : ℝ) :
    (⨆ x : ℝ, (((x * xStar : ℝ) : WithBotTop ℝ) - (Real.exp).toWithBotTop x)) =
      Function.toWithBotTopOn (fun y : ℝ ↦ y * Real.log y - y) (Set.Ici 0) xStar := by
  simpa [HasPairing.pairing, mul_comm] using exp_fenchelConjugate_eq_iSup xStar

end

/-! ### Text_12_2_5 (from Chap03) -/
noncomputable section

section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.5 computes the Fenchel conjugate of the scalar function
  `x ↦ (1 / p) * |x|^p` on `ℝ`.
- `core/canonical`: the chapter owner abstraction is `convexConjugate` on
  `WithBotTop ℝ`-valued functions at the pairing layer; this file uses the canonical real
  self-pairing owner provided by `HasLinearPairing`/`HasPairing`, together with its canonical
  codomain lift to `WithBotTop ℝ`.
- `bridge/view`: the scalar supremum formula and the Hölder-conjugate `q`-restatement are thin
  views of that owner theorem.

Domain-style sampling used here:
- `Function.toWithBotTop` from `Chap01.EOrder.Basic` as the canonical codomain-lift owner for
  real-valued primal functions;
- `instHasPairingWithBotTop` from `Chap01.HasPairing` as the canonical codomain lift of the
  underlying real pairing owner;
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from Defn 12.2;
- `Real.conjExponent` together with `Real.HolderConjugate.conjExponent_eq`;
- `Analysis.MeanInequalities.young_inequality` as the standard upper-bound mechanism for the
  Fenchel supremum.

Primitive data vs derived API:
- primitive inputs: the exponent `p : ℝ` with `1 < p`, and the source power function
  `absRpowDiv p`;
- owner-side primitive theorem surface: the conjugate identity for the canonical codomain lift
  `((absRpowDiv p).toWithBotTop)` stated directly on `ℝ`;
- derived API: the scalar `iSup` presentation and the explicit `q`-exponent restatement.

Layer target: `source-facing`; the public theorem is the scalar owner theorem on `ℝ`, stated
through the canonical codomain lift `Function.toWithBotTop` rather than a parallel local wrapper.
-/

/-- Source-facing power owner for Text 12.2.5: `x ↦ (1 / p) * |x|^p` on `ℝ`. -/
def absRpowDiv (p : ℝ) : ℝ → ℝ :=
  fun x ↦ (1 / p) * |x| ^ p

@[simp] private lemma pairing_real_eq_mul (x y : ℝ) :
    (⟪x, y⟫ₚ : ℝ) = x * y := by
  change inner ℝ x y = x * y
  calc
    inner ℝ x y = y * (starRingEnd ℝ) x := RCLike.inner_apply x y
    _ = y * x := by simp
    _ = x * y := by ring

@[simp] private lemma pairing_real_withBotTop_eq_mul (x y : ℝ) :
    (⟪x, y⟫ₚ : WithBotTop ℝ) = ((x * y : ℝ) : WithBotTop ℝ) :=
  congrArg (fun t : ℝ => (t : WithBotTop ℝ)) (pairing_real_eq_mul x y)

private lemma exists_eq_abs_rpow_div_fenchel_argmax
    {p xStar : ℝ} (hp : 1 < p) :
    ∃ x0 : ℝ,
      x0 * xStar - (1 / p) * |x0| ^ p =
        (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  have hqgt1 : 1 < Real.conjExponent p := hpq.symm.lt
  have hqminus_nonneg : 0 ≤ Real.conjExponent p - 1 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  have hp0 : p ≠ 0 := by linarith
  have hmul : (Real.conjExponent p - 1) * p = Real.conjExponent p := by
    rw [Real.conjExponent]
    field_simp [hp1]
    ring_nf
  have hone : 1 - 1 / p = 1 / Real.conjExponent p := by
    rw [Real.conjExponent]
    field_simp [hp1, hp0]
  by_cases hxs : 0 ≤ xStar
  · refine ⟨xStar ^ (Real.conjExponent p - 1), ?_⟩
    have hx0_nonneg : 0 ≤ xStar ^ (Real.conjExponent p - 1) :=
      Real.rpow_nonneg hxs _
    have hxmul :
        (xStar ^ (Real.conjExponent p - 1)) * xStar = xStar ^ (Real.conjExponent p) := by
      calc
        (xStar ^ (Real.conjExponent p - 1)) * xStar
            = (xStar ^ (Real.conjExponent p - 1)) * xStar ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = xStar ^ ((Real.conjExponent p - 1) + 1) := by
              symm
              exact Real.rpow_add_of_nonneg hxs hqminus_nonneg zero_le_one
        _ = xStar ^ (Real.conjExponent p) := by ring_nf
    have hxabs :
        |xStar ^ (Real.conjExponent p - 1)| ^ p = xStar ^ (Real.conjExponent p) := by
      calc
        |xStar ^ (Real.conjExponent p - 1)| ^ p
            = (xStar ^ (Real.conjExponent p - 1)) ^ p := by simp [abs_of_nonneg hx0_nonneg]
        _ = xStar ^ ((Real.conjExponent p - 1) * p) := by
              rw [← Real.rpow_mul hxs (Real.conjExponent p - 1) p]
        _ = xStar ^ (Real.conjExponent p) := by rw [hmul]
    calc
      (xStar ^ (Real.conjExponent p - 1)) * xStar
          - (1 / p) * |xStar ^ (Real.conjExponent p - 1)| ^ p
          = xStar ^ (Real.conjExponent p) - (1 / p) * xStar ^ (Real.conjExponent p) := by
              rw [hxmul, hxabs]
      _ = (1 - 1 / p) * xStar ^ (Real.conjExponent p) := by ring
      _ = (1 / Real.conjExponent p) * xStar ^ (Real.conjExponent p) := by rw [hone]
      _ = (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) := by
            simp [abs_of_nonneg hxs]
  · have hneg : xStar < 0 := lt_of_not_ge hxs
    set y : ℝ := -xStar
    have hy_nonneg : 0 ≤ y := by
      dsimp [y]
      linarith
    have hyPow_nonneg : 0 ≤ y ^ (Real.conjExponent p - 1) := Real.rpow_nonneg hy_nonneg _
    refine ⟨-(y ^ (Real.conjExponent p - 1)), ?_⟩
    have hy_mul : (y ^ (Real.conjExponent p - 1)) * y = y ^ (Real.conjExponent p) := by
      calc
        (y ^ (Real.conjExponent p - 1)) * y
            = (y ^ (Real.conjExponent p - 1)) * y ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = y ^ ((Real.conjExponent p - 1) + 1) := by
              symm
              exact Real.rpow_add_of_nonneg hy_nonneg hqminus_nonneg zero_le_one
        _ = y ^ (Real.conjExponent p) := by ring_nf
    have hxmul :
        (-(y ^ (Real.conjExponent p - 1))) * xStar = y ^ (Real.conjExponent p) := by
      calc
        (-(y ^ (Real.conjExponent p - 1))) * xStar
            = (-(y ^ (Real.conjExponent p - 1))) * (-y) := by simp [y]
        _ = (y ^ (Real.conjExponent p - 1)) * y := by ring
        _ = y ^ (Real.conjExponent p) := hy_mul
    have hxabs :
        |-(y ^ (Real.conjExponent p - 1))| ^ p = y ^ (Real.conjExponent p) := by
      calc
        |-(y ^ (Real.conjExponent p - 1))| ^ p
            = |y ^ (Real.conjExponent p - 1)| ^ p := by simp
        _ = (y ^ (Real.conjExponent p - 1)) ^ p := by
              simp [abs_of_nonneg hyPow_nonneg]
        _ = y ^ ((Real.conjExponent p - 1) * p) := by
              rw [← Real.rpow_mul hy_nonneg (Real.conjExponent p - 1) p]
        _ = y ^ (Real.conjExponent p) := by rw [hmul]
    calc
      (-(y ^ (Real.conjExponent p - 1))) * xStar - (1 / p) * |-(y ^ (Real.conjExponent p - 1))| ^ p
          = y ^ (Real.conjExponent p) - (1 / p) * |-(y ^ (Real.conjExponent p - 1))| ^ p := by
              rw [hxmul]
      _ = y ^ (Real.conjExponent p) - (1 / p) * y ^ (Real.conjExponent p) := by rw [hxabs]
      _ = (1 - 1 / p) * y ^ (Real.conjExponent p) := by ring
      _ = (1 / Real.conjExponent p) * y ^ (Real.conjExponent p) := by rw [hone]
      _ = (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) := by
            simp [y, abs_of_neg hneg]

private lemma abs_rpow_div_fenchel_iSup_eq
    {p : ℝ} (hp : 1 < p) (xStar : ℝ) :
    (⨆ x : ℝ,
        (⟪x, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x)) =
      (absRpowDiv (Real.conjExponent p)).toWithBotTop xStar := by
  have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    intro x
    have hreal :
        x * xStar - (1 / p) * |x| ^ p ≤
          (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) := by
      have hyoung := Real.young_inequality x xStar hpq
      have hyoung' :
          x * xStar ≤
            (1 / p) * |x| ^ p + (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) := by
        simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hyoung
      linarith
    have hE :
        (((x * xStar - (1 / p) * |x| ^ p : ℝ) : WithBotTop ℝ)) ≤
          (((1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) : ℝ) : WithBotTop ℝ) :=
      (WithBotTop.coe_le_coe).2 hreal
    simpa [absRpowDiv, Function.toWithBotTop, sub_eq_add_neg] using hE
  · rcases exists_eq_abs_rpow_div_fenchel_argmax (hp := hp) (xStar := xStar) with ⟨x0, hx0⟩
    have hx0E :
        (absRpowDiv (Real.conjExponent p)).toWithBotTop xStar ≤
          (⟪x0, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x0) := by
      have hreal :
          (1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) ≤
            x0 * xStar - (1 / p) * |x0| ^ p := le_of_eq hx0.symm
      have hE :
          (((1 / Real.conjExponent p) * |xStar| ^ (Real.conjExponent p) : ℝ) : WithBotTop ℝ) ≤
            (((x0 * xStar - (1 / p) * |x0| ^ p : ℝ) : WithBotTop ℝ)) :=
        (WithBotTop.coe_le_coe).2 hreal
      simpa [absRpowDiv, Function.toWithBotTop, sub_eq_add_neg] using hE
    have hx0Sup :
        (⟪x0, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x0) ≤
          (⨆ x : ℝ, (⟪x, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x)) :=
      le_iSup (fun x : ℝ ↦ (⟪x, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x)) x0
    exact le_trans hx0E hx0Sup

-- Proof sketch: identify the conjugate with the scalar Fenchel supremum by
-- `convexConjugate_eq_iSup_pairing_sub`. Young's inequality bounds each affine defect by
-- `(1 / q) * |xStar| ^ q`, where `q = Real.conjExponent p`, and equality is attained at the
-- standard optimizer `x = sign xStar * |xStar| ^ (q - 1)`.
/-- Text 12.2.5: for `1 < p`, the Fenchel conjugate of `x ↦ (1 / p) * |x|^p` on `ℝ` is the power
law with canonical dual exponent `Real.conjExponent p`. -/
theorem abs_rpow_div_fenchelConjugate_eq
    {p : ℝ} (hp : 1 < p) :
    ((absRpowDiv p).toWithBotTop)⋆ =
      (absRpowDiv (Real.conjExponent p)).toWithBotTop := by
  funext xStar
  simpa [absRpowDiv, Function.toWithBotTop, convexConjugate_eq_iSup_pairing_sub] using
    abs_rpow_div_fenchel_iSup_eq (hp := hp) xStar

-- Proof sketch: rewrite the owner theorem by `convexConjugate_eq_iSup_pairing_sub`. On `ℝ`, the
-- canonical pairing is multiplication, so the supremum becomes the textbook scalar Fenchel
-- supremum.
/-- Text 12.2.5 in textbook scalar-supremum form: the same conjugate formula as
`abs_rpow_div_fenchelConjugate_eq`, written directly as the scalar Fenchel supremum on `ℝ`. -/
theorem abs_rpow_div_fenchelConjugate_eq_iSup
    {p : ℝ} (hp : 1 < p) (xStar : ℝ) :
    (⨆ x : ℝ,
        (⟪x, xStar⟫ₚ - (absRpowDiv p).toWithBotTop x)) =
      (absRpowDiv (Real.conjExponent p)).toWithBotTop xStar := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    congrFun (abs_rpow_div_fenchelConjugate_eq (hp := hp)) xStar

-- Proof sketch: specialize the canonical dual-exponent owner theorem above to `hpq.lt : 1 < p`,
-- then rewrite `Real.conjExponent p` to `q` using the bridge `hpq.conjExponent_eq`.
/-- Source-facing restatement of Text 12.2.5: if `p` and `q` are Hölder-conjugate exponents, then
the Fenchel conjugate of `x ↦ (1 / p) * |x|^p` is `xStar ↦ (1 / q) * |xStar|^q`. -/
theorem abs_rpow_div_fenchelConjugate_eq_of_holderConjugate
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ((absRpowDiv p).toWithBotTop)⋆ =
      (absRpowDiv q).toWithBotTop := by
  simpa [absRpowDiv, hpq.conjExponent_eq] using abs_rpow_div_fenchelConjugate_eq hpq.lt

end

/-! ### Text_12_2_6 (from Chap03) -/
noncomputable section

section

open scoped Rockafellar

local instance : HasPairing ℝ ℝ ℝ where
  pairing x y := x * y
local instance : HasPairing ℝ ℝ (WithBotTop ℝ) := instHasPairingWithBotTop

variable (p : ℝ)

/-- Source scalar branch from Text 12.2.6: `x ↦ -(1 / p) * x^p`. -/
def negRpowDiv (p : ℝ) : ℝ → ℝ :=
  fun x ↦ (-(1 / p)) * x ^ p

/-- Conjugate-side scalar branch used in Text 12.2.6: `x ↦ -(1 / q) * |x|^q`. -/
def negAbsRpowDiv (q : ℝ) : ℝ → ℝ :=
  fun x ↦ (-(1 / q)) * |x| ^ q

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item defines the one-dimensional function
  `x ↦ -(1 / p) x^p` on `[0, ∞)`, extended by `+∞` to `(-∞, 0)`, for `0 < p < 1`.
- `core/canonical`: the chapter owner abstractions are the extension-by-`+∞` owner
  `Function.toWithBotTopOn f C` from Remark 4.4.5, the Fenchel conjugate `convexConjugate` on the
  scalar pairing layer over `ℝ`, and the canonical dual exponent owner `Real.conjExponent`.
- `bridge/view`: the piecewise branch formula follows by unfolding
  `Function.toWithBotTopOn`, while the scalar Fenchel-supremum formula and the textbook
  reciprocal relation `1 / p + 1 / q = 1` are companion restatement layers of the owner theorem.

Domain-style sampling used here:
- the Chapter 1 extension-by-`+∞` owner `Function.toWithBotTopOn f C` from Remark 4.4.5;
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from Defn 12.2;
- `Real.conjExponent` from mathlib as the owner dual exponent API;
- the neighboring owner-pattern `abs_rpow_div_fenchelConjugate_eq` from Text 12.2.5;
- the scalar-source-facing patterns `exp_fenchelConjugate_eq` from Text 12.2.4 and
  `neg_sqrt_sq_sub_sq_icc_fenchelConjugate_eq` from Text 12.2.7;
- `Real.rpow` for the fractional powers `x^p` and `|xStar|^q`;
- the `WithBotTop ℝ` conventions, with `⊤` standing for `+∞`.

Primitive data vs derived API:
- primitive source-facing data: the exponent `p` with `0 < p < 1` and the scalar function itself;
- owner-side primitive theorem surface: the conjugacy formula for
  `(Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0))⋆` stated directly on `ℝ`;
- derived API: the branchwise source formula for the canonical extension owner, the scalar
  Fenchel-supremum formula, and the two-branch closed form with exponent
  `Real.conjExponent p`, plus a thin `q`-based bridge restatement.

Layer target: `source-facing`; the scalar source function already lives on the canonical owner
ambient `ℝ`, and its extension by `+∞` outside `[0, ∞)` already has the chapter owner
`Function.toWithBotTopOn f C`, so the main conjugacy result is stated directly through that owner
and `f⋆`, with the raw scalar supremum retained only as a companion specification view.

Abstraction boundary: this item remains over `ℝ` because its source formula uses
`Real.rpow` with a real exponent parameter and the canonical dual-exponent API
`Real.conjExponent`; these owners are intrinsically real-valued in the current ecosystem.
-/

-- Proof sketch: unfold the canonical extension owner `Function.toWithBotTopOn` for the real
-- branch `x ↦ -(1 / p) x^p` on `[0, ∞) = Set.Ici 0`, then simplify the two piecewise branches.
/-- The canonical `WithBotTop ℝ` owner for `x ↦ -(1 / p) x^p` on `[0, ∞)` reproduces
the source branch formula `-(1 / p) x^p` on `x ≥ 0` and `+∞` on `x < 0`. -/
@[simp] theorem neg_rpow_div_ici_eq_piecewise (x : ℝ) :
    Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0) x =
      if 0 ≤ x then
        (negRpowDiv p).toWithBotTop x
      else
        ⊤ := by
  by_cases hx : 0 ≤ x
  · simp [Function.toWithBotTopOn, Set.mem_Ici, hx, negRpowDiv]
  · simp [Function.toWithBotTopOn, Set.mem_Ici, hx, negRpowDiv]

-- Proof sketch: write the Fenchel conjugate on `ℝ` as the supremum of
-- `x * xStar + (1 / p) * x^p` over `x ≥ 0`. If `xStar ≥ 0`, the affine term forces this supremum
-- to be `+∞` as `x → +∞`. If `xStar < 0`, maximize the concave one-variable function by solving
-- `xStar + x^(p - 1) = 0`, which gives the critical point `x = |xStar|^(1 / (p - 1))`; this
-- evaluates to the canonical dual-exponent formula with `Real.conjExponent p = p / (p - 1) < 0`.
/-- Text 12.2.6: if `0 < p < 1`, then the Fenchel conjugate of the function
`x ↦ -(1 / p) x^p` on `[0, ∞)` extended by `+∞` to `(-∞, 0)`, written on the canonical
`WithBotTop ℝ` owner surface as `Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0)`,
has Fenchel conjugate given
on the same owner layer by the extension-by-`+∞` operator on `Set.Iio 0` with canonical dual
exponent `Real.conjExponent p`. -/
theorem neg_rpow_div_ici_fenchelConjugate_eq
    (hp0 : 0 < p) (hp1 : p < 1) :
    (Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0))⋆ =
      Function.toWithBotTopOn (negAbsRpowDiv (Real.conjExponent p)) (Set.Iio 0) := by
  sorry

-- Proof sketch: the reciprocal relation `1 / p + 1 / q = 1` with `0 < p < 1` determines
-- `q = Real.conjExponent p`, so the source-facing `q`-formula is a direct restatement of the
-- canonical owner theorem above.
/-- Source-facing restatement of Text 12.2.6: if `0 < p < 1` and `q` satisfies
`1 / p + 1 / q = 1`, then the Fenchel conjugate formula may be written with `q` instead of the
canonical dual exponent `Real.conjExponent p`. -/
theorem neg_rpow_div_ici_fenchelConjugate_eq_of_reciprocal_relation
    (q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hpq : 1 / p + 1 / q = 1) :
    (Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0))⋆ =
      Function.toWithBotTopOn (negAbsRpowDiv q) (Set.Iio 0) := by
  sorry

-- Proof sketch: rewrite the owner theorem by `convexConjugate_eq_iSup_pairing_sub` at the pairing
-- layer. On `ℝ`, this recovers the textbook scalar Fenchel supremum.
/-- Text 12.2.6 in textbook supremum form: the same conjugate formula as
`neg_rpow_div_ici_fenchelConjugate_eq`, expressed directly by the scalar Fenchel
supremum on `ℝ`. -/
theorem neg_rpow_div_ici_fenchelConjugate_eq_iSup
    (hp0 : 0 < p) (hp1 : p < 1) (xStar : ℝ) :
    (⨆ x : ℝ,
        (⟪x, xStar⟫ₚ -
          Function.toWithBotTopOn (negRpowDiv p) (Set.Ici 0) x)) =
      Function.toWithBotTopOn (negAbsRpowDiv (Real.conjExponent p)) (Set.Iio 0) xStar := by
  simpa [convexConjugate_eq_iSup_pairing_sub] using
    congrFun (neg_rpow_div_ici_fenchelConjugate_eq p hp0 hp1) xStar

end
