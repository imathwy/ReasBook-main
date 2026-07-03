import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_21_6_1 (from Chap04) -/
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

/-! ### Corollary_21_6_2 (from Chap04) -/
open scoped BigOperators Rockafellar

section

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {I : Type*} [Nonempty I]

namespace Finsupp

/-- A nonnegative nontrivial multiplier family whose weighted sum is pointwise nonnegative on
`C` with zero lower bound. -/
abbrev IsNonnegativeZeroBoundCertificateOn
    [Finite I]
    (weights : I →₀ 𝕜) (C : Set E) (f : I → E → WithBotTop 𝕜) : Prop :=
  by
    classical
    letI : Fintype I := Fintype.ofFinite I
    exact (weights : I → 𝕜).IsNonnegativeZeroBoundCertificateOn C f

end Finsupp

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 21.6.2 sharpens the source-facing alternatives of Theorems 21.1 and
  21.2 by sharpening their chapter-owner feasible-set alternatives: either the original owner
  feasible-set branch holds, or the multiplier branch can already be stated with at most
  `Module.finrank 𝕜 E + 1` nonzero multipliers on the strict side. Specializing to
  `𝕜 = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the textbook bound `n + 1`.
- `core/canonical`: the owner APIs are the source-facing `Xor'` alternatives from Theorems 21.1
  and 21.2 together with the canonical finitely supported owner `Finsupp` for support-bounded
  certificate data and its intrinsic weighted sum `w.sum`. On the mixed side the convex and affine
  multipliers are still best packaged as a single sum-indexed `Finsupp` on `ι ⊕ κ`.
  The strict branch now stays on the same scalar-generic owner layer as Theorem 21.1; the mixed
  branch remains on the finite-dimensional real layer inherited from Theorem 21.2. The stronger
  Chapter 21.3 predicate
  `Finsupp.IsNonnegativeMultiplierCertificateOn` is not the right owner here: it packages a
  uniform positive lower bound `ε > 0`, while Corollary 21.6.2 preserves the weaker Theorems 21.1
  and 21.2 certificate semantics with lower bound `0`.
- `bridge/view`: the source-pointwise and certificate-only extraction lemmas are companions. They
  are obtained by expanding the owner feasible-set side or by combining the sharpened `Xor'`
  alternatives with the original Theorems 21.1 and 21.2 to rule out the owner feasible-set branch
  once an old-style certificate is already given.

Domain-style sampling used here:
- `xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate`;
- `xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate`;
- `strict_convexInequalitySolutionSet_nonempty_iff`;
- `mixed_convexInequalitySolutionSet_nonempty_iff_affine`;
- `convexInequalitySolutionSet_nonempty_of_small_subsystems_feasible`;
- `Finsupp.sum`;
- `mixedSystem`.

Primitive data vs derived API:
- primitive source-facing data: the existing owner feasible-set branches and multiplier hypotheses from
  Theorems 21.1 and 21.2; for the strict-family branch this includes the nonempty finite index
  family required already by Theorem 21.1;
- primitive owner-side bounded-certificate data in this corollary: a single finitely supported
  multiplier family `w` together with its intrinsic sum `w.sum`;
- derived API: the source-pointwise bridge companions obtained by expanding the owner feasible-set
  side, and the certificate-only extraction companions obtained from the sharpened `Xor'`
  statements.

Layer target: `source-facing` for the two sharpened owner alternatives, with `bridge/view`
companions that expand the owner feasible-set side to the textbook pointwise wording and that
extract only the bounded certificate branch when an old-style certificate is already known.
-/

/-- Corollary 21.6.2 (1), owner form: under the hypotheses of Theorem 21.1, exactly one of the
following holds: either the strict Chapter 21 feasible set on `C` is nonempty, or there is a
nontrivial nonnegative finitely supported multiplier family `w` with
`w.support.card ≤ Module.finrank 𝕜 E + 1` whose weighted sum is nonnegative on `C`. Specializing
to `𝕜 = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the textbook bound `n + 1`. -/
theorem
    xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
    [Finite I]
    {C : Set E} (f : I → E → WithBotTop 𝕜) (hC : Convex 𝕜 C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i)) :
    Xor'
      ((C ∩ strictConvexInequalitySolutionSet f).Nonempty)
      (∃ w : I →₀ 𝕜,
        w.support.card ≤ Module.finrank 𝕜 E + 1 ∧
          w.IsNonnegativeZeroBoundCertificateOn C f) := sorry

/-- Corollary 21.6.2 (1), source-facing bridge: the owner feasible-set branch above is exactly the
existence of a point `x ∈ C` with `f i x < 0` for every `i`. -/
theorem xor_exists_strict_feasible_point_or_nonnegative_multiplier_certificate_with_support_card_le
    [Finite I]
    {C : Set E} (f : I → E → WithBotTop 𝕜) (hC : Convex 𝕜 C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i)) :
    Xor'
      (∃ x : E, x ∈ C ∧ ∀ i, f i x < 0)
      (∃ w : I →₀ 𝕜,
        w.support.card ≤ Module.finrank 𝕜 E + 1 ∧
          w.IsNonnegativeZeroBoundCertificateOn C f) := by
  simpa [strict_convexInequalitySolutionSet_nonempty_iff f] using
    xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
      f hC hf_convex hf_bot hdom

/-- Companion to Corollary 21.6.2 (1): once the old multiplier branch of Theorem 21.1 is known,
the sharpened alternative above forces a support-bounded certificate. -/
theorem exists_strict_convex_system_multiplier_certificate_with_support_card_le
    [Fintype I]
    {C : Set E} (f : I → E → WithBotTop 𝕜) (hC : Convex 𝕜 C)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i))
    (hcert : ∃ w : I → 𝕜, w.IsNonnegativeZeroBoundCertificateOn C f) :
    ∃ w : I →₀ 𝕜,
      w.support.card ≤ Module.finrank 𝕜 E + 1 ∧
        w.IsNonnegativeZeroBoundCertificateOn C f := by
  classical
  have hxor :=
    xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
      f hC hf_convex hf_bot hdom
  rcases hxor.or with hfeasible | hsmall
    · have horig :=
      xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate
        f hC hf_convex hf_bot hdom
    rcases horig with ⟨_, hnotcert⟩ | ⟨_, hnotfeasible⟩
    · exact False.elim (hnotcert hcert)
    · exact False.elim (hnotfeasible hfeasible)
  · exact hsmall

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

namespace Finsupp

/-- Mixed strict/weak multiplier certificate owner used in Corollary 21.6.2 (2). -/
abbrev IsNonnegativeZeroBoundMixedCertificateOn
    (weights : (ι ⊕ κ) →₀ ℝ) (C : Set E)
    (f : ι → E → WithBotTop ℝ) (g : κ → AffineMap ℝ E ℝ) : Prop :=
  (weights : ι ⊕ κ → ℝ).IsNonnegativeZeroBoundCertificateOn C (mixedSystem f g) ∧
    ∃ i : ι, weights (.inl i) ≠ 0

end Finsupp

/-- Corollary 21.6.2 (2), owner form: under the hypotheses of Theorem 21.2, exactly one of the
following holds: either the mixed Chapter 21 feasible set on `C` is nonempty, or there is a
nonnegative sum-indexed finitely supported multiplier family
`w : (ι ⊕ κ) →₀ ℝ` with `w.support.card ≤ Module.finrank ℝ E + 1` whose weighted mixed
sum is nonnegative on `C`, and whose convex-side coefficients are not all zero. Specializing
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook bound `n + 1`. -/
theorem
    xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
    {C : Set E} (hC : Convex ℝ C)
    (f : ι → E → WithBotTop ℝ) (g : κ → AffineMap ℝ E ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[ℝ](C) ⊆ dom(f i))
    (hfeas_affine : ∃ x, x ∈ ri[ℝ](C) ∧ ∀ j, g j x ≤ 0) :
    Xor'
      ((C ∩ mixedConvexInequalitySolutionSet f g).Nonempty)
      (∃ w : (ι ⊕ κ) →₀ ℝ,
        w.support.card ≤ Module.finrank ℝ E + 1 ∧
          w.IsNonnegativeZeroBoundMixedCertificateOn C f g) :=
  sorry

/-- Corollary 21.6.2 (2), source-facing bridge: the owner feasible-set branch above is exactly the
existence of a point `x ∈ C` satisfying the strict convex block and the weak affine block. -/
theorem xor_strict_feasible_or_nonnegative_multiplier_certificate_with_support_card_le
    {C : Set E} (hC : Convex ℝ C)
    (f : ι → E → WithBotTop ℝ) (g : κ → AffineMap ℝ E ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[ℝ](C) ⊆ dom(f i))
    (hfeas_affine : ∃ x, x ∈ ri[ℝ](C) ∧ ∀ j, g j x ≤ 0) :
    Xor'
      (∃ x : E, x ∈ C ∧ (∀ i : ι, f i x < 0) ∧ ∀ j : κ, g j x ≤ 0)
      (∃ w : (ι ⊕ κ) →₀ ℝ,
        w.support.card ≤ Module.finrank ℝ E + 1 ∧
          w.IsNonnegativeZeroBoundMixedCertificateOn C f g) := by
  have hiff :
      (C ∩ mixedConvexInequalitySolutionSet f g).Nonempty ↔
        ∃ x : E, x ∈ C ∧ (∀ i : ι, f i x < 0) ∧ ∀ j : κ, g j x ≤ 0 :=
    mixed_convexInequalitySolutionSet_nonempty_iff_affine f g
  rcases
      xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
        hC f g hf_convex hf_bot hdom hfeas_affine with
    hxor | hxor
  · exact Or.inl ⟨hiff.mp hxor.1, hxor.2⟩
  · exact Or.inr ⟨hxor.1, fun hfeasible ↦ hxor.2 (hiff.mpr hfeasible)⟩

/-- Companion to Corollary 21.6.2 (2): once the old multiplier branch of Theorem 21.2 is known,
the sharpened alternative above forces a support-bounded mixed certificate. -/
theorem exists_convex_affine_system_multiplier_certificate_with_support_card_le
    {C : Set E} (hC : Convex ℝ C)
    (f : ι → E → WithBotTop ℝ) (g : κ → AffineMap ℝ E ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ C (f i))
    (hf_bot : ∀ i x, ⊥ < f i x)
    (hdom : ∀ i, ri[ℝ](C) ⊆ dom(f i))
    (hfeas_affine : ∃ x, x ∈ ri[ℝ](C) ∧ ∀ j, g j x ≤ 0)
    (hcert : ∃ wf : ι → ℝ, ∃ wg : κ → ℝ,
      (∀ i : ι, 0 ≤ wf i) ∧
      (∀ j : κ, 0 ≤ wg j) ∧
      (∃ i : ι, wf i ≠ 0) ∧
      ∀ x : C,
        (0 : WithBotTop ℝ) ≤
          (∑ i, (wf i : WithBotTop ℝ) * f i x) +
            ∑ j, (wg j : WithBotTop ℝ) * Function.toWithBotTop (g j) x) :
    ∃ w : (ι ⊕ κ) →₀ ℝ,
      w.support.card ≤ Module.finrank ℝ E + 1 ∧
        w.IsNonnegativeZeroBoundMixedCertificateOn C f g := by
  have hxor :=
    xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_with_support_card_le
      hC f g hf_convex hf_bot hdom hfeas_affine
  rcases hxor.or with hfeasible | hsmall
  · have horig :=
      xor_strict_feasible_or_nonnegative_multiplier_certificate
        hC f g hf_convex hf_bot hdom hfeas_affine
    have hfeasible' :
        ∃ x : E, x ∈ C ∧ (∀ i : ι, f i x < 0) ∧ ∀ j : κ, g j x ≤ 0 :=
      (mixed_convexInequalitySolutionSet_nonempty_iff_affine f g).mp hfeasible
    rcases horig with horig | horig
    · exact False.elim (horig.2 hcert)
    · exact False.elim (horig.2 hfeasible')
  · exact hsmall

end

/-! ### Theorem_21_6 (from Chap04) -/
/- 
Source/core/bridge triage:
- `source-facing`: Theorem 21.6 is Helly's theorem for a finite collection of convex subsets of a
  finite-dimensional vector space with threshold `Module.finrank 𝕜 E + 1`.
- `core/canonical`: the owner declaration recalled here is the intrinsic finite-set surface
  `Convex.helly_theorem_set'` (subfamily cardinality form `≤`), which avoids index-family
  scaffolding on the theorem surface.
- `bridge/view`: this owner is obtained from the primitive indexed-family theorem
  `Convex.helly_theorem'`; the classical exact-cardinality surfaces
  (`Convex.helly_theorem`, `Convex.helly_theorem_set`) and concrete coordinate-model
  presentations are downstream specializations.

Domain-style sampling used here:
- `Convex.helly_theorem_set'`;
- `Convex.helly_theorem'`;
- `Convex.helly_theorem_set`.

Primitive data vs derived API:
- primitive upstream data: a finite index set `s : Finset ι`, a family `F : ι → Set E`,
  pointwise convexity on `s`, and nonempty intersections for all subfamilies of cardinality at
  most `Module.finrank 𝕜 E + 1` (`Convex.helly_theorem'`);
- source-facing owner here: the equivalent intrinsic finite-set statement
  (`Convex.helly_theorem_set'`) on `Finset (Set E)`;
- derived API: exact-cardinality-plus-lower-bound classical surfaces are downstream bridges.

Layer target: `core/canonical`. This item is a direct recall of the intrinsic finite-set owner
surface rather than a second public alias.

Abstraction checks for this item:
- Codomain/ambient layer: no ordered-extended-codomain owner is introduced; the statement is
  set-level Helly on `Set E`, so there is no codomain over-specialization to repair here.
- Scalar/ambient structure: the recalled owner already lives over the weaker canonical layer
  `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]` with
  `[FiniteDimensional 𝕜 E]`, so this file does not freeze to a concrete scalar/model.
- Owner model choice: this theorem-surface recall uses the intrinsic finite-set owner
  `Convex.helly_theorem_set'` instead of the more implementation-facing indexed-family scaffold.
- Ambient vs intrinsic topology: no ambient `closure`/`interior` formulation is introduced, so no
  intrinsic/relative-topology promotion is missing here.
- Owner naming surface: no long local owner name is introduced; the canonical upstream owner name
  is used verbatim.
- Notation surface: no new notation is needed because no new owner is introduced; direct recall
  keeps the theorem surface minimal.
-/

/- Theorem 21.6 is recalled at the intrinsic finite-set owner layer as
`Convex.helly_theorem_set'`; indexed-family and exact-cardinality surfaces are downstream bridge
views. -/
recall Convex.helly_theorem_set'
