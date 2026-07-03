import Mathlib
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_3 (from Chap01) -/
/-
Source/core/bridge triage:
`source-facing`: Definition 4.3 says that a function on `s` is affine exactly when it is both
  convex and concave on `s`; the textbook real-valued statement is a specialization of this
  canonical owner surface.
- `core/canonical`: use the existing mathlib owners `ConvexOn` and `ConcaveOn`, surfaced directly
  by the chapter notation `affOn[𝕜](f, s)`.
- `bridge/view`: the affine-combination equality view is exposed as a theorem-level bridge from
  `ConvexOn 𝕜 s f ∧ ConcaveOn 𝕜 s f`.
- Primitive data vs derived API: the primitive inputs are the scalar system `𝕜`, the set `s`, and
  the ambient function `f : E → β`; the affine-equality statement is derived bridge API.
- Domain-style sampling: `ConvexOn`, `ConcaveOn`, `convexOn_iff_forall_pos`,
  `concaveOn_iff_forall_pos`, and the chapter's generalized Jensen owner theorem in Theorem 4.3.
- Layer target: canonical existing owners + source-facing notation.
-/

section

variable {𝕜 E β : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

/- Definition 4.3 recalls the canonical convex-on predicate. -/
recall ConvexOn

/- Together with `ConvexOn`, `ConcaveOn` gives the source notion of an affine function on a set. -/
recall ConcaveOn

/-- Textbook notation for affine-on-set predicates from Definition 4.3, expressed directly by the
canonical `ConvexOn`/`ConcaveOn` conjunction. -/
scoped[Rockafellar] notation:max "affOn[" 𝕜 "](" f ", " s ")" =>
  ConvexOn 𝕜 s f ∧ ConcaveOn 𝕜 s f

open scoped Rockafellar

@[simp] theorem affOn_iff_convexOn_concaveOn {s : Set E} {f : E → β} :
    affOn[𝕜](f, s) ↔ (ConvexOn 𝕜 s f ∧ ConcaveOn 𝕜 s f) :=
  Iff.rfl

/-- Ordered-codomain bridge for Definition 4.3: convexity and concavity on the same set are
exactly the affine-combination equality condition. -/
@[simp] theorem affOn_iff_forall_eq_affineCombination {s : Set E} {f : E → β} :
    affOn[𝕜](f, s) ↔
      Convex 𝕜 s ∧
        ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
          f (a • x + b • y) = a • f x + b • f y := by
  constructor
  · rintro ⟨hconvex, hconcave⟩
    refine ⟨hconvex.1, ?_⟩
    intro x hx y hy a b ha hb hab
    exact le_antisymm (hconvex.2 hx hy ha hb hab) (hconcave.2 hx hy ha hb hab)
  · rintro ⟨hs, heq⟩
    refine
      ⟨⟨hs, fun x hx y hy a b ha hb hab => (heq hx hy ha hb hab).le⟩,
        ⟨hs, fun x hx y hy a b ha hb hab => (heq hx hy ha hb hab).ge⟩⟩

/-- Constructor in canonical owner language. -/
theorem affOn_of_convexOn_concaveOn {s : Set E} {f : E → β}
    (hconvex : ConvexOn 𝕜 s f) (hconcave : ConcaveOn 𝕜 s f) :
    affOn[𝕜](f, s) :=
  ⟨hconvex, hconcave⟩

/-- Extract the affine-combination equality view from the canonical owner pair. -/
theorem affOn_eq_affineCombination {s : Set E} {f : E → β} (hf : affOn[𝕜](f, s)) :
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) = a • f x + b • f y :=
  (affOn_iff_forall_eq_affineCombination (s := s) (f := f)).1 hf |>.2

end

/-! ### Theorem_4_3 (from Chap01) -/
open scoped BigOperators

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 4.3 states that a function is convex exactly when it satisfies Jensen's
  inequality for every finite convex combination of points; the textbook whole-space statement is
  recovered as the specialization `s = Set.univ` (and `𝕜 = ℝ` for `R^n`).
- `core/canonical`: the owner predicate is mathlib's `ConvexOn 𝕜 s f` on an arbitrary set `s`.
- `bridge/view`: `ConvexOn.map_sum_le` and `ConvexOn.map_centerMass_le` are the canonical finite
  Jensen APIs, and the reverse implication is recovered by specializing finite Jensen to a
  two-point family.
- Primitive data vs derived API: the reverse bridge from finite Jensen to convexity is proven from
  the primitive `ConvexOn` constructor at the semiring + `SMul` layer; the full finite Jensen
  equivalences use the stronger ordered-field Jensen API.
- Layer target: keep theorem surfaces on canonical `ConvexOn`; whole-space form is a thin
  specialization.
-/

universe u v

section

variable {𝕜 : Type*} {E : Type u} {β : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
variable {f : E → β}

/-- Reverse finite-Jensen bridge at the primitive semiring layer: if `s` is convex and `f`
satisfies the finite convex-combination Jensen inequality on `s`, then `f` is convex on `s`. -/
theorem convexOn_of_finset_jensen {s : Set E}
    (hs : Convex 𝕜 s)
    (h :
      ∀ ⦃ι : Type*⦄ (t : Finset ι) (w : ι → 𝕜) (x : ι → E),
        (∀ i ∈ t, 0 ≤ w i) →
        (∀ i ∈ t, x i ∈ s) →
        (∑ i ∈ t, w i = 1) →
        f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, w i • f (x i)) :
    ConvexOn 𝕜 s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hw2 : ∀ i : ULift (Fin 2), 0 ≤ (![a, b] i.down : 𝕜) := by
    intro i
    cases i using ULift.casesOn with
    | _ j =>
        fin_cases j
        · exact ha
        · exact hb
  let w2 : ULift (Fin 2) → 𝕜 := fun i ↦ ![a, b] i.down
  let x2 : ULift (Fin 2) → E := fun i ↦ ![x, y] i.down
  have hx2 : ∀ i : ULift (Fin 2), x2 i ∈ s := by
    intro i
    cases i using ULift.casesOn with
    | _ j =>
        fin_cases j
        · simpa [x2] using hx
        · simpa [x2] using hy
  have hs2 : ∑ i : ULift (Fin 2), w2 i • x2 i = a • x + b • y := by
    trans ∑ i : Fin 2, w2 (ULift.up i) • x2 (ULift.up i)
    · simpa using
        (Equiv.sum_comp Equiv.ulift fun i : Fin 2 ↦ w2 (ULift.up i) • x2 (ULift.up i))
    · simp [w2, x2, Fin.sum_univ_two]
  have hsf2 : ∑ i : ULift (Fin 2), w2 i • f (x2 i) = a • f x + b • f y := by
    trans ∑ i : Fin 2, w2 (ULift.up i) • f (x2 (ULift.up i))
    · simpa using
        (Equiv.sum_comp Equiv.ulift fun i : Fin 2 ↦ w2 (ULift.up i) • f (x2 (ULift.up i)))
    · simp [w2, x2, Fin.sum_univ_two]
  have h2 :=
    h (Finset.univ : Finset (ULift (Fin 2))) w2 x2
      (fun i _ ↦ by simpa [w2] using hw2 i)
      (fun i _ ↦ hx2 i)
      (by
        trans ∑ i : ULift (Fin 2), w2 i
        · simp
        · trans ∑ i : Fin 2, w2 (ULift.up i)
          · simpa using (Equiv.sum_comp Equiv.ulift fun i : Fin 2 ↦ w2 (ULift.up i))
          · simpa [w2, Fin.sum_univ_two] using hab)
  simpa [hs2, hsf2] using h2

end

section

variable {𝕜 : Type*} {E : Type u} {β : Type v}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β]
variable [IsStrictOrderedModule 𝕜 β]
variable {f : E → β}

/-- Canonical finite Jensen characterization on a set, in center-of-mass form: convexity on `s` is
equivalent to `s` being convex together with Jensen's inequality for every finite weighted center
of mass of points in `s`. -/
theorem convexOn_iff_finset_centerMass_jensen {s : Set E} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃ι : Type*⦄ (t : Finset ι) (w : ι → 𝕜) (x : ι → E),
          (∀ i ∈ t, 0 ≤ w i) →
          0 < ∑ i ∈ t, w i →
          (∀ i ∈ t, x i ∈ s) →
          f (t.centerMass w x) ≤ t.centerMass w (f ∘ x) := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro ι t w x hw hsum hx
    exact hf.map_centerMass_le hw hsum hx
  · rintro ⟨hs, h⟩
    refine convexOn_of_finset_jensen (f := f) hs ?_
    intro ι t w x hw hx hsum
    have hsum_pos : 0 < ∑ i ∈ t, w i := by simp [hsum]
    have hcenter := h t w x hw hsum_pos hx
    simpa only [Finset.centerMass, hsum, inv_one, one_smul] using hcenter

/-- Canonical finite Jensen characterization on a set: convexity on `s` is equivalent to
`s` being convex together with Jensen's inequality for every finite convex combination of points
in `s`. -/
-- Proof sketch: the forward implication is `ConvexOn.map_sum_le`; for the reverse implication,
-- recover the two-point inequality from a two-element finite family and apply
-- `convexOn_iff_forall_pos`.
theorem convexOn_iff_finset_jensen {s : Set E} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃ι : Type*⦄ (t : Finset ι) (w : ι → 𝕜) (x : ι → E),
          (∀ i ∈ t, 0 ≤ w i) →
          (∀ i ∈ t, x i ∈ s) →
          (∑ i ∈ t, w i = 1) →
          f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, w i • f (x i) := by
  constructor
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro ι t w x hw hx hsum
    exact hf.map_sum_le hw hsum hx
  · rintro ⟨hs, h⟩
    exact convexOn_of_finset_jensen (f := f) hs h

/-- Theorem 4.3, textbook-space specialization: finite Jensen on the whole space. -/
theorem convexOn_univ_iff_finset_jensen :
    ConvexOn 𝕜 Set.univ f ↔
      ∀ ⦃ι : Type*⦄ (t : Finset ι) (w : ι → 𝕜) (x : ι → E),
        (∀ i ∈ t, 0 ≤ w i) →
        (∑ i ∈ t, w i = 1) →
        f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, w i • f (x i) := by
  simpa [convex_univ] using
    (convexOn_iff_finset_jensen (s := Set.univ))

end
