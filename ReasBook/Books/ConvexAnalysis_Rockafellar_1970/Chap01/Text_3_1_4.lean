import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise

universe u v

section

variable {ι : Type u} {𝕜 : Type*}
variable [LE 𝕜] [AddCommMonoid 𝕜] [One 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.4 introduces a finite convex combination of sets with nonnegative
  coefficients summing to `1`.
- `core/canonical`: the coefficient owner was already fixed in Definition 2.2.10 as
  `StdSimplex 𝕜 ι`; the resulting weighted combination is the owner-side finite sum
  `w.sum` applied to the set-valued summands `fun i a ↦ a • C i`, with
  `Set.addCommMonoid` supplying the ambient pointwise additive structure on sets.
- `bridge/view`: the textbook coefficient conditions are exactly `w.nonneg` and `w.total`, and
  the source display `∑ i : ι, w.weights i • C i` (for finite `ι`) is a bridge view of that
  owner-side sum once the zero-coefficient branches contribute the additive identity in `Set E`.
  No separate weighted-set owner or wrapper is needed.
- Primitive data vs derived API: the primitive data are the family `C : ι → Set E` and simplex
  weights `w : StdSimplex 𝕜 ι`; a `Fintype` instance is only needed for the derived full-index
  display `∑ i, ...`, not for the owner-side sum.
- Domain-style sampling: this item aligns with `StdSimplex`, `Finsupp.sum_fintype`,
  and `Set.addCommMonoid`.
- Layer target: `source-facing`, expressed directly through the canonical owner operations rather
  than a parallel local alias.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: keep the coefficient owner at canonical `StdSimplex 𝕜 ι`; no concrete
  codomain such as `ℝ`/`EReal` appears in this item.
- Scalar/ambient-structure check: retain only the primitive simplex assumptions
  `[LE 𝕜] [AddCommMonoid 𝕜] [One 𝕜]`; set- and scalar-action assumptions are moved to the
  set-valued bridge specialization.
- Owner check: expose a generic owner-side bridge from `w.sum` to `Fintype` full-index sums for
  any additive codomain, then derive the set-valued textbook surface from it.
- Topology check: not applicable (item is algebraic, not topological).
- Notation/surface check: theorem surfaces keep textbook finite-sum notation `∑ i, ...` and
  simplex-owner notation `w.sum`.
-/

/- Text 3.1.4 uses the chapter's canonical owner for convex-combination coefficients. -/
recall StdSimplex

/- The finite convex combination of sets is then the ordinary finite sum in the additive
commutative monoid of sets. -/
recall Set.addCommMonoid

namespace StdSimplex

variable {β : Type*}

/-- Generic owner-side form: `StdSimplex.sum` is the support-indexed finite sum. -/
theorem sum_eq_sum_support [AddCommMonoid β]
    (w : StdSimplex 𝕜 ι) (f : ι → 𝕜 → β) :
    w.sum f = Finset.sum w.weights.support (fun i ↦ f i (w.weights i)) := by
  rfl

-- Bridge from support-indexed owner sums to full-index sums on finite index types.
theorem sum_eq_sum_weights [Fintype ι] [AddCommMonoid β]
    (w : StdSimplex 𝕜 ι) (f : ι → 𝕜 → β)
    (hzero : ∀ i : ι, f i 0 = 0) :
    w.sum f = ∑ i : ι, f i (w.weights i) := by
  classical
  simpa [Finsupp.sum_fintype] using
    (Finsupp.sum_fintype w.weights f hzero)

-- Canonical weighted-family owner surface (`z : ι → β`) over additive codomains.
theorem sum_smul_eq_sum_support [AddCommMonoid β] [SMul 𝕜 β]
    (w : StdSimplex 𝕜 ι) (z : ι → β) :
    w.sum (fun i a ↦ a • z i) =
      Finset.sum w.weights.support (fun i ↦ w.weights i • z i) := by
  simpa using (sum_eq_sum_support (w := w) (f := fun i a ↦ a • z i))

-- Finite-index bridge for weighted families; `hzero` discharges dropped zero-weight branches.
theorem sum_smul_eq_sum_weights [Fintype ι] [AddCommMonoid β] [SMul 𝕜 β]
    (w : StdSimplex 𝕜 ι) (z : ι → β)
    (hzero : ∀ i : ι, (0 : 𝕜) • z i = 0) :
    w.sum (fun i a ↦ a • z i) = ∑ i : ι, w.weights i • z i := by
  simpa using
    (sum_eq_sum_weights (w := w) (f := fun i a ↦ a • z i)
      (hzero := hzero))

section SetValued

variable {E : Type v} [AddCommMonoid E]

/-- The primitive owner-side form of Text 3.1.4 is the support-indexed simplex sum. -/
theorem sum_smul_set_eq_sum_support [SMul 𝕜 E]
    (w : StdSimplex 𝕜 ι) (C : ι → Set E) :
    w.sum (fun i a ↦ a • C i) =
      Finset.sum w.weights.support (fun i ↦ w.weights i • C i) := by
  simpa using (sum_smul_eq_sum_support (w := w) (z := C))

/-- Primitive finite-index bridge: the textbook full-index display follows once each
zero-coefficient branch is additive identity in `Set E`. -/
theorem sum_smul_set_eq_sum_weights [Fintype ι]
    [SMul 𝕜 E]
    (w : StdSimplex 𝕜 ι) (C : ι → Set E)
    (hzero : ∀ i : ι, (0 : 𝕜) • C i = 0) :
    w.sum (fun i a ↦ a • C i) = ∑ i : ι, w.weights i • C i := by
  simpa using
    (sum_smul_eq_sum_weights (w := w) (z := C)
      (hzero := hzero))

/-- Derived finite-index bridge for nonempty families, using `Set.zero_smul_set`. -/
theorem sum_smul_set_eq_sum_weights_of_nonempty [Fintype ι]
    [SMulWithZero 𝕜 E]
    (w : StdSimplex 𝕜 ι) (C : ι → Set E)
    (hnonempty : ∀ i : ι, (C i).Nonempty) :
    w.sum (fun i a ↦ a • C i) = ∑ i : ι, w.weights i • C i := by
  exact sum_smul_set_eq_sum_weights (w := w) (C := C)
    (hzero := fun i ↦ by simpa using Set.zero_smul_set (α := 𝕜) (hnonempty i))

end SetValued

end StdSimplex

variable {E : Type v}
variable [AddCommMonoid E]
variable [SMul 𝕜 E]
variable (C : ι → Set E) (w : StdSimplex 𝕜 ι)

/- Text 3.1.4: once the coefficient data are taken in the canonical owner `StdSimplex 𝕜 ι`, the
finite convex combination of the family `C` is the owner-side simplex sum
`w.sum (fun i a ↦ a • C i)`. -/
/- Owner-side finite convex-combination form from the simplex-owner sum operation. -/
#check (w.sum fun i a ↦ a • C i)

section

variable [Fintype ι]

/- Companion source-facing display form for finite index types. -/
#check ∑ i : ι, w.weights i • C i

end

end
