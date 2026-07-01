import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
