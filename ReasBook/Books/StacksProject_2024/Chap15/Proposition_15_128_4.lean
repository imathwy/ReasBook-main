import Mathlib
import StacksProject_2024.Chap15.Situation_15_128_1

-- Declarations for this item will be appended below by the statement pipeline.

open Order Set TopologicalSpace
open scoped ClosedPointFiber

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain-style sampling:
- primary domain: fibrewise linear independence of section classes in the visible quotient `V(x)`
  at closed points, together with codimension control on irreducible closed subsets;
- inspected owner-style declarations:
  `closedPointFiberVisibleQuotient`,
  `closedPointFiberVisibleClass`,
  `selectedSections_splitAfterInverting_iff_linearIndependent_visibleClasses`,
  `IrreducibleCloseds`,
  `Order.coheight`;
- best owner abstraction: the chapter owner for the source-visible fibre data is
  `closedPointFiberVisibleQuotient` together with `closedPointFiberVisibleClass`; this file should
  build its bad-locus predicate from that owner rather than from the full fibre `M(x)`, and the
  codimension predicate should quantify directly over the canonical owner `IrreducibleCloseds Ω`
  rather than re-encoding irreducible closed subsets as raw sets;
- layer: `source-facing` for `section_dependence_locus sections`,
  `irreducible_components_codim_at_least k F`, and the proposition's existential conclusion;
  `core/canonical` for the visible quotient owner, `IrreducibleCloseds`, and `Order.coheight`;
- primitive data: `sections`, `k`, `F`, the prescribed visible classes, the added section `s`,
  and the auxiliary set `F'`;
- derived API: the proposition statement itself; the two local predicates are small owner-level
  definitions and do not need separate unfold-only public wrappers.
-/
local notation "Ω" => closedPoints (PrimeSpectrum R)
local notation "V(" x ")" => closedPointFiberVisibleQuotient M x

/-- The locus of closed points where a finite family of sections fails to be linearly independent
in the visible quotient `V(x)`. -/
def section_dependence_locus {h : ℕ} (sections : Fin h → M) : Set Ω :=
  {x | ¬ LinearIndependent (κ(x)) (closedPointFiberVisibleClass x ∘ sections)}

/-- A subset of `Ω` has irreducible components of codimension at least `k` if every maximal
irreducible closed subset contained in it has `coheight` at least `k`. -/
def irreducible_components_codim_at_least (k : ℕ) (F : Set Ω) : Prop :=
  ∀ Z : IrreducibleCloseds Ω,
    Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ F) Z →
      (k : ℕ∞) ≤ coheight Z

variable [Module.FinitePresentation R M]

-- Proof sketch: argue by induction on `k`. The case `k = 0` is Lemma `15.128.3`. For the
-- induction step, first apply the induction hypothesis to obtain a section `u` and an error set
-- `G`; choose one point on each irreducible component of `G \ F` together with a visible class
-- outside the span of the existing visible classes, enlarge the family `(s₁, …, s_h, u)`, and
-- use the Chinese remainder theorem to splice the resulting sections. These choices remove
-- irreducible components of codimension `< k`, leaving only components of codimension at least
-- `k`.
/-- Proposition 15.128.4: in the Noetherian closed-point space `Ω`, if a family of `h` sections is
already fibrewise independent in the visible quotient `V(x)` away from a closed subset `F`, if
one prescribes visible classes at finitely many pairwise distinct points of `F`, and if every
visible quotient `V(x)` has dimension at least `h + k`, then one can add one more section meeting
the prescribed visible classes so that the new dependence locus is contained in `F ∪ F'` for some
closed subset `F'` whose irreducible components all have codimension at least `k`. -/
theorem exists_section_with_prescribed_values_and_codim_controlled_dependence_locus
    [NoetherianSpace Ω] {h n k : ℕ} (sections : Fin h → M) {F : Set Ω} (hFclosed : IsClosed F)
    (hzero : section_dependence_locus sections ⊆ F)
    (pts : Fin n → Ω)
    (hpts : Pairwise fun i j ↦ pts i ≠ pts j)
    (hptsF : ∀ i, pts i ∈ F)
    (v : ∀ i, V((pts i)))
    (hdim : ∀ x : Ω, h + k ≤ Module.finrank (κ(x)) (V(x))) :
    ∃ s : M, ∃ F' : Set Ω,
      IsClosed F' ∧
      (∀ i, closedPointFiberVisibleClass (pts i) s = v i) ∧
      section_dependence_locus (Fin.snoc sections s) ⊆ F ∪ F' ∧
      irreducible_components_codim_at_least k F' := sorry

end
