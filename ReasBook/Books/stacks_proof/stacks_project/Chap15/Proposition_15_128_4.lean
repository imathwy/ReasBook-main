import Mathlib
import StacksProject_2024.Chap15.Situation_15_128_1
import StacksProject_2024.Chap15.Lemma_15_128_2
import StacksProject_2024.Chap15.Lemma_15_128_3

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

/-- Helper for Proposition 15.128.4: codimension at least `0` is automatic for every irreducible
component. -/
lemma irreducible_components_codim_at_least_zero (F : Set Ω) :
    irreducible_components_codim_at_least 0 F := by
  intro Z hZ
  -- `0` is the bottom element of `ℕ∞`, so no geometric input is needed here.
  exact bot_le

/-- Helper for Proposition 15.128.4: the case `k = 0` follows from the prescribed-values lemma by
taking `F'` to be the closure of the new dependence locus outside `F`. -/
lemma exists_section_with_prescribed_values_and_codim_controlled_dependence_locus_zero
    [Module.FinitePresentation R M] {h n : ℕ} (sections : Fin h → M) {F : Set Ω}
    (_hFclosed : IsClosed F)
    (_hzero : section_dependence_locus sections ⊆ F)
    (pts : Fin n → Ω)
    (hpts : Pairwise fun i j ↦ pts i ≠ pts j)
    (_hptsF : ∀ i, pts i ∈ F)
    (v : ∀ i, V((pts i)))
    (_hdim : ∀ x : Ω, h + 0 ≤ Module.finrank (κ(x)) (V(x))) :
    ∃ s : M, ∃ F' : Set Ω,
      IsClosed F' ∧
      (∀ i, closedPointFiberVisibleClass (pts i) s = v i) ∧
      section_dependence_locus (Fin.snoc sections s) ⊆ F ∪ F' ∧
      irreducible_components_codim_at_least 0 F' := by
  obtain ⟨s, hs⟩ :=
    exists_section_with_prescribed_values_at_pairwise_distinct_closed_points
      (M := M) pts hpts v
  refine ⟨s, closure (section_dependence_locus (Fin.snoc sections s) \ F), ?_⟩
  refine ⟨isClosed_closure, hs, ?_, irreducible_components_codim_at_least_zero _⟩
  intro x hx
  -- Outside `F`, every bad point lies in the chosen closure by construction.
  by_cases hxF : x ∈ F
  · exact Or.inl hxF
  · exact Or.inr <| subset_closure ⟨hx, hxF⟩

variable [Module.FinitePresentation R M]

/-- Helper for Proposition 15.128.4: fibrewise independence is an open condition on closed points,
witnessed by the same localization parameter `f`. -/
lemma independent_point_has_open_neighborhood {h : ℕ} (sections : Fin h → M) (x : Ω)
    (hx : x ∉ section_dependence_locus sections) :
    ∃ U : Set Ω, IsOpen U ∧ x ∈ U ∧ U ⊆ (section_dependence_locus sections)ᶜ := by
  -- Convert pointwise independence into a localization-away-from-`f` splitting at `x`.
  have hlin : LinearIndependent (κ(x)) (closedPointFiberVisibleClass x ∘ sections) := by
    simpa [section_dependence_locus] using hx
  have hsplit :=
    (selectedSections_splitAfterInverting_iff_linearIndependent_visibleClasses
      (M := M) x sections).2 hlin
  rcases hsplit with ⟨f, hfx, ρ, hρ⟩
  refine ⟨Subtype.val ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)), ?_, ?_, ?_⟩
  · -- The basic open `D(f)` in `Spec R` restricts to an open subset of the closed-point space.
    exact PrimeSpectrum.isOpen_basicOpen.preimage continuous_subtype_val
  · -- The chosen parameter `f` is nonzero at `x`, so `x` lies in that basic open.
    simpa [PrimeSpectrum.mem_basicOpen] using hfx
  · intro y hy
    -- The same localized left inverse works at every closed point avoiding `f`.
    have hyf : f ∉ (y : PrimeSpectrum R).asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using hy
    have hsplit_y : selectedSectionsSplitAfterInverting y sections := ⟨f, hyf, ρ, hρ⟩
    have hlin_y :
        LinearIndependent (κ(y)) (closedPointFiberVisibleClass y ∘ sections) :=
      (selectedSections_splitAfterInverting_iff_linearIndependent_visibleClasses
        (M := M) y sections).1 hsplit_y
    simpa [section_dependence_locus] using hlin_y

/-- Helper for Proposition 15.128.4: the dependence locus is closed because fibrewise
independence persists on an open neighborhood of every independent point. -/
lemma isClosed_section_dependence_locus {h : ℕ} (sections : Fin h → M) :
    IsClosed (section_dependence_locus (R := R) (M := M) sections) := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  -- Use the pointwise openness of the independence condition to open the complement.
  rcases independent_point_has_open_neighborhood (R := R) (M := M) sections x hx with
    ⟨U, hUopen, hxU, hUsub⟩
  exact Filter.mem_of_superset (hUopen.mem_nhds hxU) hUsub

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: normalizing the bad locus by taking the closure of its
outside-`F` part already captures every bad point not lying in `F`. -/
lemma section_dependence_locus_subset_union_closure_diff {h : ℕ} (sections : Fin h → M)
    (F : Set Ω) :
    section_dependence_locus sections ⊆ F ∪ closure (section_dependence_locus sections \ F) := by
  intro x hx
  -- Split according to whether the bad point is already absorbed by the base closed set `F`.
  by_cases hxF : x ∈ F
  · exact Or.inl hxF
  · exact Or.inr <| subset_closure ⟨hx, hxF⟩

/-- Helper for Proposition 15.128.4: the normalized bad locus attached to `B` relative to `F` is
the closure of the part of `B` lying outside `F`. -/
def normalized_bad_locus (B F : Set Ω) : Set Ω := closure (B \ F)

/-- Helper for Proposition 15.128.4: the predicate asserting that an irreducible closed subset is
contained in a fixed ambient closed set. -/
def irreducible_closed_subset_pred (C : Set Ω) : IrreducibleCloseds Ω → Prop :=
  fun Y ↦ (Y : Set Ω) ⊆ C

/-- Helper for Proposition 15.128.4: a point where the visible classes are already independent
cannot lie in the closure of the bad locus outside any base set `F`. -/
lemma point_not_mem_closure_diff_of_not_mem_section_dependence_locus
    {h : ℕ} (sections : Fin h → M) {F : Set Ω} {x : Ω}
    (hx : x ∉ section_dependence_locus sections) :
    x ∉ closure (section_dependence_locus sections \ F) := by
  rcases independent_point_has_open_neighborhood (R := R) (M := M) sections x hx with
    ⟨U, hUopen, hxU, hUsub⟩
  intro hxclosure
  -- Any neighborhood on which independence persists is disjoint from the bad locus outside `F`.
  rcases mem_closure_iff.1 hxclosure U hUopen hxU with ⟨y, hyU, hybad⟩
  exact hUsub hyU hybad.1

/-- Helper for Proposition 15.128.4: appending points from outside a base set to points inside
that base set preserves pairwise distinctness. -/
lemma pairwise_append_of_mem_base_and_outside_base {α : Type*} {D : Set α}
    {n m : ℕ} (xs : Fin n → α) (ys : Fin m → α)
    (hxs : Pairwise fun i j ↦ xs i ≠ xs j)
    (hys : Pairwise fun i j ↦ ys i ≠ ys j)
    (hxsD : ∀ i, xs i ∈ D)
    (hysD : ∀ j, ys j ∉ D) :
    Pairwise fun i j ↦ Fin.append xs ys i ≠ Fin.append xs ys j := by
  intro i j hij
  cases i using Fin.addCases with
  | left i =>
      cases j using Fin.addCases with
      | left j =>
          -- Two points in the left block stay distinct because the original family was pairwise.
          have hij' : i ≠ j := by
            intro h
            apply hij
            simpa [h]
          simpa [Fin.append] using hxs hij'
      | right j =>
          -- A point in the right block cannot equal one in the left block because it lies
          -- outside the base set `D`.
          intro hEq
          have hEq' : ys j = xs i := by
            simpa [Fin.append] using hEq.symm
          exact hysD j (hEq' ▸ hxsD i)
  | right i =>
      cases j using Fin.addCases with
      | left j =>
          -- This is the symmetric left/right case.
          intro hEq
          have hEq' : ys i = xs j := by
            simpa [Fin.append] using hEq
          exact hysD i (hEq' ▸ hxsD j)
      | right j =>
          -- Two points in the right block stay distinct because the original family was pairwise.
          have hij' : i ≠ j := by
            intro h
            apply hij
            simpa [h]
          simpa [Fin.append] using hys hij'

/-- Helper for Proposition 15.128.4: replacing the last vector in an independent `snoc` family by
that vector plus a scalar multiple of a further independent vector preserves linear independence. -/
lemma linearIndependent_snoc_add_smul
    {K : Type*} [DivisionRing K] {W : Type*} [AddCommGroup W] [Module K W]
    {h : ℕ} (sections : Fin h → W) (u t : W)
    (hli : LinearIndependent K (Fin.snoc (Fin.snoc sections u) t)) (c : K) :
    LinearIndependent K (Fin.snoc sections (u + c • t)) := by
  -- First peel the two `snoc` steps apart to isolate the span conditions on `u` and `t`.
  have hsu : LinearIndependent K (Fin.snoc sections u) := by
    simpa [Fin.init_snoc] using
      (linearIndependent_finSucc' (v := Fin.snoc (Fin.snoc sections u) t)).1 hli |>.1
  have hsections : LinearIndependent K sections := by
    simpa [Fin.init_snoc] using
      (linearIndependent_finSucc' (v := Fin.snoc sections u)).1 hsu |>.1
  have ht_not_mem :
      t ∉ Submodule.span K (Set.range (Fin.snoc sections u)) := by
    simpa [Fin.init_snoc] using
      (linearIndependent_finSucc' (v := Fin.snoc (Fin.snoc sections u) t)).1 hli |>.2
  have hu_not_mem :
      u ∉ Submodule.span K (Set.range sections) := by
    simpa [Fin.init_snoc] using
      (linearIndependent_finSucc' (v := Fin.snoc sections u)).1 hsu |>.2
  have hnew_not_mem :
      u + c • t ∉ Submodule.span K (Set.range sections) := by
    intro hmem
    by_cases hc : c = 0
    · -- When `c = 0`, the new vector is exactly `u`.
      have hu_mem : u ∈ Submodule.span K (Set.range sections) := by
        simpa [hc] using hmem
      exact hu_not_mem hu_mem
    · -- Otherwise, a span relation for `u + c • t` would force `t` into the old span.
      have hsections_subset :
          Set.range sections ⊆ Set.range (Fin.snoc sections u) := by
        rintro x ⟨i, rfl⟩
        refine ⟨i.castSucc, ?_⟩
        simp [Fin.snoc_castSucc]
      have hnew_mem :
          u + c • t ∈ Submodule.span K (Set.range (Fin.snoc sections u)) :=
        (Submodule.span_mono hsections_subset) hmem
      have hu_mem :
          u ∈ Submodule.span K (Set.range (Fin.snoc sections u)) := by
        exact Submodule.subset_span ⟨Fin.last h, Fin.snoc_last _ _⟩
      let S : Submodule K W := Submodule.span K (Set.range (Fin.snoc sections u))
      have hsub_mem : (u + c • t) - u ∈ S := sub_mem hnew_mem hu_mem
      have hdiff_mem : c • t ∈ S := by
        simpa [S, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub_mem
      have hscaled_mem : c⁻¹ • (c • t) ∈ S := by
        exact S.smul_mem _ hdiff_mem
      have ht_mem : t ∈ S := by
        have hEq : c⁻¹ • (c • t) = t := by
          rw [smul_smul]
          simp [hc]
        simpa [hEq] using hscaled_mem
      exact ht_not_mem <| by
        simpa [S] using ht_mem
  -- Reassemble the family by the finite-family criterion for appending one last vector.
  simpa [linearIndependent_finSucc', Fin.init_snoc] using ⟨hsections, hnew_not_mem⟩

/-- Helper for Proposition 15.128.4: if the correction term already lies outside the span of the
original family, then adding any vector from that span still gives an independent `snoc` family. -/
lemma linearIndependent_snoc_add_of_mem_span
    {K : Type*} [DivisionRing K] {W : Type*} [AddCommGroup W] [Module K W]
    {h : ℕ} (sections : Fin h → W) (u w : W)
    (hsections : LinearIndependent K sections)
    (hu : u ∈ Submodule.span K (Set.range sections))
    (hw : w ∉ Submodule.span K (Set.range sections)) :
    LinearIndependent K (Fin.snoc sections (u + w)) := by
  have hnew_not_mem : u + w ∉ Submodule.span K (Set.range sections) := by
    intro hmem
    have hw_mem : w ∈ Submodule.span K (Set.range sections) := by
      -- Subtract the known span element `u` from the hypothesized span relation for `u + w`.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using sub_mem hmem hu
    exact hw hw_mem
  -- Appending a vector outside the old span is exactly the `Fin.snoc` independence criterion.
  simpa [linearIndependent_finSucc', Fin.init_snoc] using ⟨hsections, hnew_not_mem⟩

/-- Helper for Proposition 15.128.4: replacing the last entry of a `snoc` family by an equal
vector preserves linear independence. -/
lemma linearIndependent_snoc_congr_last
    {K : Type*} [DivisionRing K] {W : Type*} [AddCommGroup W] [Module K W]
    {h : ℕ} (sections : Fin h → W) {u v : W}
    (huv : v = u)
    (hli : LinearIndependent K (Fin.snoc sections u)) :
    LinearIndependent K (Fin.snoc sections v) := by
  simpa [huv] using hli

/-- Helper for Proposition 15.128.4: rewriting `f ∘ Fin.snoc sections u` as two successive
`Fin.snoc` operations preserves linear independence after appending one more vector. -/
lemma linearIndependent_snoc_snoc_of_comp_snoc
    {K : Type*} [DivisionRing K] {W : Type*} [AddCommGroup W] [Module K W]
    {A : Type*} {h : ℕ} (f : A → W) (sections : Fin h → A) (u : A) (t : W)
    (hli : LinearIndependent K (Fin.snoc (f ∘ Fin.snoc sections u) t)) :
    LinearIndependent K (Fin.snoc (Fin.snoc (f ∘ sections) (f u)) t) := by
  have hfamily : f ∘ Fin.snoc sections u = Fin.snoc (f ∘ sections) (f u) := by
    funext j
    cases j using Fin.lastCases with
    | last =>
        simp [Function.comp_apply, Fin.snoc_last]
    | cast j =>
        simp [Function.comp_apply, Fin.snoc_castSucc]
  exact hfamily ▸ hli

/-- Helper for Proposition 15.128.4: if appending `u` destroys linear independence while the old
family is still independent, then `u` already lies in the span of the old family. -/
lemma snoc_last_mem_span_of_not_linearIndependent
    {K : Type*} [DivisionRing K] {W : Type*} [AddCommGroup W] [Module K W]
    {h : ℕ} (sections : Fin h → W) (u : W)
    (hsections : LinearIndependent K sections)
    (hnot : ¬ LinearIndependent K (Fin.snoc sections u)) :
    u ∈ Submodule.span K (Set.range sections) := by
  -- Route correction: turn failure of independence for the appended family directly into the
  -- finite-family span criterion, instead of unfolding the family by hand at each call site.
  by_contra hu
  exact hnot <| by
    simpa [linearIndependent_finSucc', Fin.init_snoc] using ⟨hsections, hu⟩

/-- Helper for Proposition 15.128.4: in a finite-dimensional vector space, an independent family of
`h` vectors cannot span the whole space once the ambient dimension is at least `h + 1`. -/
lemma exists_not_mem_span_of_succ_le_finrank
    {K : Type*} [DivisionRing K] {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {h : ℕ} (sections : Fin h → W)
    (hsections : LinearIndependent K sections)
    (hdim : h + 1 ≤ Module.finrank K W) :
    ∃ w : W, w ∉ Submodule.span K (Set.range sections) := by
  by_contra hnot
  have hspan_ge_top : ⊤ ≤ Submodule.span K (Set.range sections) := by
    intro w hwtop
    by_contra hw
    exact hnot ⟨w, hw⟩
  have hspan_top : Submodule.span K (Set.range sections) = ⊤ := top_le_iff.mp hspan_ge_top
  have hfinrank_eq : Module.finrank K W = h := by
    calc
      Module.finrank K W = Module.finrank K (⊤ : Submodule K W) := by simp
      _ = Module.finrank K (Submodule.span K (Set.range sections)) := by rw [← hspan_top]
      _ = h := by simpa using finrank_span_eq_card hsections
  have : h + 1 ≤ h := by simpa [hfinrank_eq] using hdim
  exact Nat.not_succ_le_self h this

/-- Helper for Proposition 15.128.4: in the regular `R`-module, the submodule `I • ⊤` is exactly
`I` itself. -/
lemma ideal_smul_top_eq_self_submodule (I : Ideal R) :
    ((I • (⊤ : Submodule R R)) : Submodule R R) = (I : Submodule R R) := by
  -- Normalize `I • ⊤` to the image of `I` under the identity algebra map on `R`.
  ext x
  constructor
  · intro hx
    rw [Ideal.smul_top_eq_map] at hx
    simpa using hx
  · intro hx
    rw [Ideal.smul_top_eq_map]
    simpa using hx

/-- Helper for Proposition 15.128.4: the source-facing fibre of `R` at a closed point is the same
`R`-module as the quotient ring `R ⧸ x`. -/
noncomputable abbrev closedPointFiber_ring_quotient_linear_equiv (x : Ω) :
    R﹙x﹚ ≃ₗ[R] (R ⧸ x.1.asIdeal) :=
  Submodule.quotEquivOfEq
    ((x.1.asIdeal • (⊤ : Submodule R R)) : Submodule R R)
    (x.1.asIdeal : Submodule R R)
    (ideal_smul_top_eq_self_submodule (R := R) x.1.asIdeal)

/-- Helper for Proposition 15.128.4: the fibre-to-quotient comparison sends a quotient generator
to the matching ideal-quotient class. -/
@[simp] lemma closedPointFiber_ring_quotient_linear_equiv_mk
    (x : Ω) (r : R) :
    closedPointFiber_ring_quotient_linear_equiv (R := R) x (Submodule.Quotient.mk r) =
      Ideal.Quotient.mk x.1.asIdeal r := by
  -- The quotient-model bridge is the canonical quotient equivalence, so it preserves generators.
  simpa [closedPointFiber_ring_quotient_linear_equiv, Ideal.Quotient.mk_eq_mk] using
    (Submodule.quotEquivOfEq_mk
      ((x.1.asIdeal • (⊤ : Submodule R R)) : Submodule R R)
      (x.1.asIdeal : Submodule R R)
      (ideal_smul_top_eq_self_submodule (R := R) x.1.asIdeal) r)

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: taking visible classes commutes with appending one last
section by `Fin.snoc`. -/
lemma closedPointFiberVisibleClass_snoc_family
    {h : ℕ} (y : Ω) (sections : Fin h → M) (u : M) :
    closedPointFiberVisibleClass y ∘ Fin.snoc sections u =
      Fin.snoc (closedPointFiberVisibleClass y ∘ sections)
        (closedPointFiberVisibleClass y u) := by
  -- Compare the two families entrywise, splitting into the old entries and the new last entry.
  funext j
  cases j using Fin.lastCases with
  | last =>
      simp [Function.comp_apply, Fin.snoc_last]
  | cast j =>
      simp [Function.comp_apply, Fin.snoc_castSucc]

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: membership in the dependence locus of an appended family is
exactly failure of linear independence for the corresponding visible `snoc` family. -/
lemma mem_section_dependence_locus_snoc_iff
    {h : ℕ} (x : Ω) (sections : Fin h → M) (u : M) :
    x ∈ section_dependence_locus (Fin.snoc sections u) ↔
      ¬ LinearIndependent (κ(x))
        (Fin.snoc (closedPointFiberVisibleClass x ∘ sections)
          (closedPointFiberVisibleClass x u)) := by
  -- Normalize the visible `snoc` family before unfolding the bad-locus predicate.
  simp [section_dependence_locus, closedPointFiberVisibleClass_snoc_family]

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: being outside the dependence locus of an appended family is
exactly linear independence for the corresponding visible `snoc` family. -/
lemma not_mem_section_dependence_locus_snoc_iff
    {h : ℕ} (x : Ω) (sections : Fin h → M) (u : M) :
    x ∉ section_dependence_locus (Fin.snoc sections u) ↔
      LinearIndependent (κ(x))
        (Fin.snoc (closedPointFiberVisibleClass x ∘ sections)
          (closedPointFiberVisibleClass x u)) := by
  -- This is just the complement form of the previous normalization lemma.
  simp [mem_section_dependence_locus_snoc_iff (R := R) (M := M) x sections u]

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: taking visible classes commutes with addition of sections. -/
@[simp] lemma closedPointFiberVisibleClass_add
    (x : Ω) (s t : M) :
    closedPointFiberVisibleClass x (s + t) =
      closedPointFiberVisibleClass x s + closedPointFiberVisibleClass x t := by
  -- Both the fibre map and the visible quotient projection are linear, so addition is preserved.
  simp [closedPointFiberVisibleClass]

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: taking visible classes commutes with scalar multiplication
by a global scalar. -/
@[simp] lemma closedPointFiberVisibleClass_smul
    (x : Ω) (r : R) (s : M) :
    closedPointFiberVisibleClass x (r • s) = r • closedPointFiberVisibleClass x s := by
  -- The quotient fibre and its visible quotient both carry the induced `R`-linear structure.
  simp [closedPointFiberVisibleClass]

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: scalar multiplication on the visible quotient depends only on
the residue class of the scalar at the chosen closed point. -/
lemma closedPointFiberVisibleClass_smul_eq_residue_scalar
    (x : Ω) (f : R) (t : M) :
    closedPointFiberVisibleClass x (f • t) =
      (closedPointFiberResidueFieldAlgEquiv (R := R) x
        (Ideal.Quotient.mk x.1.asIdeal f)) • closedPointFiberVisibleClass x t := by
  have hscalar :
      (algebraMap R (κ(x)) f : κ(x)) =
        closedPointFiberResidueFieldAlgEquiv (R := R) x
          (Ideal.Quotient.mk x.1.asIdeal f) := by
    -- The residue-field comparison is compatible with the original `R`-algebra structure.
    simpa [Ideal.Quotient.mk_eq_mk] using
      ((closedPointFiberResidueFieldAlgEquiv (R := R) x).commutes f).symm
  calc
    closedPointFiberVisibleClass x (f • t)
        = (algebraMap R (κ(x)) f : κ(x)) • closedPointFiberVisibleClass x t := by
            simpa using
              (IsScalarTower.algebraMap_smul (κ(x)) f (closedPointFiberVisibleClass x t)).symm
    _ = (closedPointFiberResidueFieldAlgEquiv (R := R) x
          (Ideal.Quotient.mk x.1.asIdeal f)) • closedPointFiberVisibleClass x t := by
            rw [hscalar]

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: evaluating the splice `u + f • t` at a closed point splits as
the old visible class plus the residue scalar times the correction visible class. -/
lemma closedPointFiberVisibleClass_splice_eq
    (x : Ω) (u t : M) (f : R) :
    closedPointFiberVisibleClass x (u + f • t) =
      closedPointFiberVisibleClass x u +
        (closedPointFiberResidueFieldAlgEquiv (R := R) x
          (Ideal.Quotient.mk x.1.asIdeal f)) • closedPointFiberVisibleClass x t := by
  -- Expand the splice by additivity and then move the scalar action to the residue field.
  calc
    closedPointFiberVisibleClass x (u + f • t)
        = closedPointFiberVisibleClass x u
            + closedPointFiberVisibleClass x (f • t) := by
              simp
    _ = closedPointFiberVisibleClass x u
          + (closedPointFiberResidueFieldAlgEquiv (R := R) x
              (Ideal.Quotient.mk x.1.asIdeal f)) •
              closedPointFiberVisibleClass x t := by
              rw [closedPointFiberVisibleClass_smul_eq_residue_scalar]

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: if the residue of `f` at `x` is zero, then the visible class
of the splice `u + f • t` agrees with the visible class of `u`. -/
lemma closedPointFiberVisibleClass_splice_eq_left_of_residue_zero
    (x : Ω) (u t : M) (f : R)
    (hzero :
      closedPointFiberResidueFieldAlgEquiv (R := R) x
        (Ideal.Quotient.mk x.1.asIdeal f) = 0) :
    closedPointFiberVisibleClass x (u + f • t) = closedPointFiberVisibleClass x u := by
  calc
    closedPointFiberVisibleClass x (u + f • t)
        = closedPointFiberVisibleClass x u +
            (closedPointFiberResidueFieldAlgEquiv (R := R) x
              (Ideal.Quotient.mk x.1.asIdeal f)) •
              closedPointFiberVisibleClass x t := by
                exact closedPointFiberVisibleClass_splice_eq
                  (R := R) (M := M) (x := x) (u := u) (t := t) (f := f)
    _ = closedPointFiberVisibleClass x u + 0 := by
          simp [hzero]
    _ = closedPointFiberVisibleClass x u := by
          simp

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: if the visible classes of `sections`, `u`, and `t` form an
independent two-step `snoc` family at `x`, then replacing the last entry by the visible class of
the splice `u + f • t` preserves linear independence. -/
lemma linearIndependent_snoc_visible_splice
    {h : ℕ} (x : Ω) (sections : Fin h → M) (u t : M) (f : R)
    (hli :
      LinearIndependent (κ(x))
        (Fin.snoc
          (Fin.snoc (closedPointFiberVisibleClass x ∘ sections)
            (closedPointFiberVisibleClass x u))
          (closedPointFiberVisibleClass x t))) :
    LinearIndependent (κ(x))
      (Fin.snoc (closedPointFiberVisibleClass x ∘ sections)
        (closedPointFiberVisibleClass x (u + f • t))) := by
  have hli_splice :
      LinearIndependent (κ(x))
        (Fin.snoc (closedPointFiberVisibleClass x ∘ sections)
          (closedPointFiberVisibleClass x u +
            (closedPointFiberResidueFieldAlgEquiv (R := R) x
              (Ideal.Quotient.mk x.1.asIdeal f)) •
              closedPointFiberVisibleClass x t)) := by
    exact linearIndependent_snoc_add_smul
      (sections := closedPointFiberVisibleClass x ∘ sections)
      (u := closedPointFiberVisibleClass x u)
      (t := closedPointFiberVisibleClass x t)
      hli _
  exact linearIndependent_snoc_congr_last
    (sections := closedPointFiberVisibleClass x ∘ sections)
    (closedPointFiberVisibleClass_splice_eq
      (R := R) (M := M) (x := x) (u := u) (t := t) (f := f))
    hli_splice

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: a visible-class prescription on an appended family evaluates
directly on the left block. -/
lemma append_visible_family_left
    {a b : ℕ} (xs : Fin a → Ω) (ys : Fin b → Ω) (s : M)
    (values : ∀ i : Fin (a + b), V((Fin.append xs ys i)))
    (hs : ∀ i, closedPointFiberVisibleClass (Fin.append xs ys i) s = values i)
    (i : Fin a) :
    closedPointFiberVisibleClass (Fin.append xs ys (Fin.castAdd b i)) s =
      values (Fin.castAdd b i) := by
  -- The left block is already one of the appended indices.
  exact hs (Fin.castAdd b i)

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: a visible-class prescription on an appended family evaluates
directly on the right block. -/
lemma append_visible_family_right
    {a b : ℕ} (xs : Fin a → Ω) (ys : Fin b → Ω) (s : M)
    (values : ∀ i : Fin (a + b), V((Fin.append xs ys i)))
    (hs : ∀ i, closedPointFiberVisibleClass (Fin.append xs ys i) s = values i)
    (j : Fin b) :
    closedPointFiberVisibleClass (Fin.append xs ys (Fin.natAdd a j)) s =
      values (Fin.natAdd a j) := by
  -- The right block is already one of the appended indices.
  exact hs (Fin.natAdd a j)

/-- Helper for Proposition 15.128.4: the visible quotient at a closed point is finite-dimensional
because it is a quotient of the finite-dimensional fibre. -/
noncomputable instance closedPointFiberVisibleQuotient_finiteDimensional (x : Ω) :
    FiniteDimensional κ(x) (V(x)) := by
  let _ : FiniteDimensional κ(x) (M﹙x﹚) :=
    closedPointFiber_finiteDimensional (R := R) (M := M) x
  infer_instance

/-- Helper for Proposition 15.128.4: Chinese remainder interpolation can prescribe arbitrary
residue-field values at finitely many pairwise distinct closed points. -/
lemma exists_scalar_with_prescribed_residue_values_at_pairwise_distinct_closed_points
    {n : ℕ} (pts : Fin n → Ω)
    (hpts : Pairwise fun i j ↦ pts i ≠ pts j)
    (a : ∀ i, κ((pts i))) :
    ∃ f : R, ∀ i,
      closedPointFiberResidueFieldAlgEquiv (R := R) (pts i)
        (Ideal.Quotient.mk ((pts i).1.asIdeal) f) = a i := by
  have hcoprime :
      Pairwise (fun i j ↦ IsCoprime ((pts i).1.asIdeal) ((pts j).1.asIdeal)) := by
    intro i j hij
    exact Ideal.isCoprime_of_isMaximal fun hEq ↦
      hpts hij <| Subtype.ext <| PrimeSpectrum.ext hEq
  let b : ∀ i, R﹙(pts i)﹚ := fun i ↦
    (closedPointFiber_ring_quotient_linear_equiv (R := R) (pts i)).symm
      ((closedPointFiberResidueFieldAlgEquiv (R := R) (pts i)).symm (a i))
  -- Pull the residue-field targets back to the quotient fibres and apply the same CRT lift as
  -- in Lemma 15.128.3 with `M = R`.
  obtain ⟨f, hf⟩ :=
    Ideal.pi_tensorProductMk_quotient_surjective R
      (fun i ↦ (pts i).1.asIdeal)
      hcoprime
      (fun i ↦ (TensorProduct.quotTensorEquivQuotSMul R ((pts i).1.asIdeal)).symm (b i))
  refine ⟨f, fun i ↦ ?_⟩
  have hf' : f⟮(pts i)⟯ = b i := by
    -- The tensor-product output already computes the fibre class of `f` at each chosen point.
    have hf'' :=
      congrArg (TensorProduct.quotTensorEquivQuotSMul R ((pts i).1.asIdeal)) (congrFun hf i)
    calc
      f⟮(pts i)⟯
        = (TensorProduct.quotTensorEquivQuotSMul R ((pts i).1.asIdeal)) (1 ⊗ₜ[R] f) := by
            simpa [closedPointFiber] using
              (TensorProduct.quotTensorEquivQuotSMul_mk_tmul
                (M := R) ((pts i).1.asIdeal) 1 f).symm
      _ = b i := by
            simpa [b] using hf''
  -- Push the lifted fibre class forward through the quotient bridge and the residue-field
  -- equivalence to recover the prescribed residue value.
  calc
    closedPointFiberResidueFieldAlgEquiv (R := R) (pts i)
        (Ideal.Quotient.mk ((pts i).1.asIdeal) f)
      = closedPointFiberResidueFieldAlgEquiv (R := R) (pts i)
          (closedPointFiber_ring_quotient_linear_equiv (R := R) (pts i) (f⟮(pts i)⟯)) := by
            rw [closedPointFiber_ring_quotient_linear_equiv_mk]
    _ = closedPointFiberResidueFieldAlgEquiv (R := R) (pts i)
          (closedPointFiber_ring_quotient_linear_equiv (R := R) (pts i) (b i)) := by
            rw [hf']
    _ = a i := by
            simp [b]

/-- Helper for Proposition 15.128.4: a residue-field prescription on an appended family evaluates
directly on the left block. -/
lemma append_residue_family_left
    {a b : ℕ} (xs : Fin a → Ω) (ys : Fin b → Ω)
    (values : ∀ i : Fin (a + b), κ((Fin.append xs ys i)))
    {f : R}
    (hf : ∀ i,
      closedPointFiberResidueFieldAlgEquiv (R := R) (Fin.append xs ys i)
        (Ideal.Quotient.mk ((Fin.append xs ys i).1.asIdeal) f) = values i)
    (i : Fin a) :
    closedPointFiberResidueFieldAlgEquiv (R := R) (Fin.append xs ys (Fin.castAdd b i))
      (Ideal.Quotient.mk ((Fin.append xs ys (Fin.castAdd b i)).1.asIdeal) f) =
        values (Fin.castAdd b i) := by
  -- The left block is already one of the appended indices.
  exact hf (Fin.castAdd b i)

/-- Helper for Proposition 15.128.4: a residue-field prescription on an appended family evaluates
directly on the right block. -/
lemma append_residue_family_right
    {a b : ℕ} (xs : Fin a → Ω) (ys : Fin b → Ω)
    (values : ∀ i : Fin (a + b), κ((Fin.append xs ys i)))
    {f : R}
    (hf : ∀ i,
      closedPointFiberResidueFieldAlgEquiv (R := R) (Fin.append xs ys i)
        (Ideal.Quotient.mk ((Fin.append xs ys i).1.asIdeal) f) = values i)
    (j : Fin b) :
    closedPointFiberResidueFieldAlgEquiv (R := R) (Fin.append xs ys (Fin.natAdd a j))
      (Ideal.Quotient.mk ((Fin.append xs ys (Fin.natAdd a j)).1.asIdeal) f) =
        values (Fin.natAdd a j) := by
  -- The right block is already one of the appended indices.
  exact hf (Fin.natAdd a j)

/-- Helper for Proposition 15.128.4: transporting a dependent family value along an index equality
agrees with evaluating the family at the rewritten index. -/
lemma dependent_family_transport_eq
    {α : Type*} {β : α → Sort*} (f : (a : α) → β a)
    {a b : α} (h : a = b) :
    Eq.mp (congrArg β h) (f a) = f b := by
  cases h
  rfl

/-- Helper for Proposition 15.128.4: an irreducible closed subset contained in a closed owner `B`
lies in some maximal irreducible closed subset of `Ω` still contained in `B`. -/
lemma exists_component_of_closed_set_containing_irreducible [NoetherianSpace Ω]
    {B : Set Ω} (hBclosed : IsClosed B) (Z : IrreducibleCloseds Ω) (hZB : (Z : Set Ω) ⊆ B) :
    ∃ W : IrreducibleCloseds Ω,
      Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ B) W ∧
        (Z : Set Ω) ⊆ W := by
  let ZB : Set B := Subtype.val ⁻¹' (Z : Set Ω)
  have hZB_irreducible : IsIrreducible ZB := by
    let f : Z → B := fun z ↦ ⟨z.1, hZB z.2⟩
    have hf_cont : Continuous f := by
      continuity
    have himage : f '' (Set.univ : Set Z) = ZB := by
      ext x
      constructor
      · rintro ⟨z, -, rfl⟩
        exact z.2
      · intro hx
        refine ⟨⟨x.1, hx⟩, mem_univ _, ?_⟩
        ext
        rfl
    letI : IrreducibleSpace Z := Subtype.irreducibleSpace Z.isIrreducible
    -- View `Z` inside the closed subspace `B`; irreducibility is preserved by the induced map.
    simpa [ZB, himage] using
      (IrreducibleSpace.isIrreducible_univ Z).image f hf_cont.continuousOn
  obtain ⟨W₀, hW₀, hZW₀⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible ZB hZB_irreducible
  let W : IrreducibleCloseds Ω :=
    ⟨Subtype.val '' W₀,
      hW₀.1.image (Subtype.val : B → Ω) continuous_subtype_val.continuousOn,
      hBclosed.isClosedEmbedding_subtypeVal.isClosedMap _ <|
        isClosed_of_mem_irreducibleComponents W₀ hW₀⟩
  refine ⟨W, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rintro x ⟨y, hy, rfl⟩
      exact y.2
    · intro T hT_sub_B hWT x hx
      have hTB_irreducible : IsIrreducible (Subtype.val ⁻¹' (T : Set Ω) : Set B) := by
        let g : T → B := fun t ↦ ⟨t.1, hT_sub_B t.2⟩
        have hg_cont : Continuous g := by
          continuity
        have himage : g '' (Set.univ : Set T) = (Subtype.val ⁻¹' (T : Set Ω) : Set B) := by
          ext y
          constructor
          · rintro ⟨t, -, rfl⟩
            exact t.2
          · intro hy
            refine ⟨⟨y.1, hy⟩, mem_univ _, ?_⟩
            ext
            rfl
        letI : IrreducibleSpace T := Subtype.irreducibleSpace T.isIrreducible
        -- The same closed-subspace transport turns any ambient irreducible closed subset of `B`
        -- into an irreducible subset of the owner space `B`.
        simpa [himage] using
          (IrreducibleSpace.isIrreducible_univ T).image g hg_cont.continuousOn
      have hW₀_subset_TB : W₀ ⊆ (Subtype.val ⁻¹' (T : Set Ω) : Set B) := by
        intro y hy
        exact hWT ⟨y, hy, rfl⟩
      have hTB_subset_W₀ : (Subtype.val ⁻¹' (T : Set Ω) : Set B) ⊆ W₀ :=
        hW₀.2 hTB_irreducible hW₀_subset_TB
      exact ⟨⟨x, hT_sub_B hx⟩, hTB_subset_W₀ hx, rfl⟩
  · intro x hx
    exact ⟨⟨x, hZB hx⟩, hZW₀ hx, rfl⟩

/-- Helper for Proposition 15.128.4: codimension bounds pass from a closed owner `B` to the
closure of any subset `A ⊆ B`. -/
lemma irreducible_components_codim_at_least_closure_of_subset [NoetherianSpace Ω]
    {k : ℕ} {A B : Set Ω} (hAB : A ⊆ B) (hBclosed : IsClosed B)
    (hcodimB : irreducible_components_codim_at_least k B) :
    irreducible_components_codim_at_least k (closure A) := by
  intro Z hZ
  have hclosureAB : closure A ⊆ B := closure_minimal hAB hBclosed
  obtain ⟨W, hWmax, hZW⟩ :=
    exists_component_of_closed_set_containing_irreducible
      (B := B) hBclosed Z (hZ.1.trans hclosureAB)
  -- Apply the codimension hypothesis to the owner component `W`, then move back down to `Z`.
  exact le_trans (hcodimB W hWmax) (coheight_anti hZW)

/-- Helper for Proposition 15.128.4: an ambient irreducible closed subset contained in an owner
remains irreducible after passing to the closed subspace. -/
lemma isIrreducible_preimage_subtype_of_subset
    {C : Set Ω} (Z : IrreducibleCloseds Ω) (hZC : (Z : Set Ω) ⊆ C) :
    IsIrreducible (Subtype.val ⁻¹' (Z : Set Ω) : Set C) := by
  let f : Z → C := fun z ↦ ⟨z.1, hZC z.2⟩
  have hf_cont : Continuous f := by
    continuity
  have himage : f '' (Set.univ : Set Z) = (Subtype.val ⁻¹' (Z : Set Ω) : Set C) := by
    ext x
    constructor
    · rintro ⟨z, -, rfl⟩
      exact z.2
    · intro hx
      refine ⟨⟨x.1, hx⟩, mem_univ _, ?_⟩
      ext
      rfl
  letI : IrreducibleSpace Z := Subtype.irreducibleSpace Z.isIrreducible
  -- View the ambient irreducible closed subset inside the owner by the induced subtype map.
  simpa [himage] using
    (IrreducibleSpace.isIrreducible_univ Z).image f hf_cont.continuousOn

/-- Helper for Proposition 15.128.4: ambientizing an irreducible component of a closed owner
produces a maximal ambient irreducible closed subset still contained in that owner. -/
lemma maximal_of_ambient_irreducible_component
    {C : Set Ω} (hCclosed : IsClosed C) (Z : irreducibleComponents C) :
    let W : IrreducibleCloseds Ω :=
      ⟨Subtype.val '' (Z : Set C),
        Z.2.1.image (Subtype.val : C → Ω) continuous_subtype_val.continuousOn,
        hCclosed.isClosedEmbedding_subtypeVal.isClosedMap _ <|
          isClosed_of_mem_irreducibleComponents (Z : Set C) Z.2⟩
    Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) W := by
  let W : IrreducibleCloseds Ω :=
    ⟨Subtype.val '' (Z : Set C),
      Z.2.1.image (Subtype.val : C → Ω) continuous_subtype_val.continuousOn,
      hCclosed.isClosedEmbedding_subtypeVal.isClosedMap _ <|
        isClosed_of_mem_irreducibleComponents (Z : Set C) Z.2⟩
  have hZmax :
      Maximal (fun T : Set C ↦ IsClosed T ∧ IsIrreducible T) (Z : Set C) := by
    simpa [irreducibleComponents_eq_maximals_closed] using Z.2
  dsimp [W]
  refine ⟨?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact y.2
  · intro Y hYC hWY
    have hYpre_closed : IsClosed (Subtype.val ⁻¹' (Y : Set Ω) : Set C) :=
      Y.isClosed.preimage continuous_subtype_val
    have hYpre_irreducible :
        IsIrreducible (Subtype.val ⁻¹' (Y : Set Ω) : Set C) :=
      isIrreducible_preimage_subtype_of_subset (C := C) Y hYC
    have hZYpre : (Z : Set C) ⊆ Subtype.val ⁻¹' (Y : Set Ω) := by
      intro x hx
      exact hWY ⟨x, hx, rfl⟩
    have hYpre_subset_Z : (Subtype.val ⁻¹' (Y : Set Ω) : Set C) ⊆ Z :=
      hZmax.2 ⟨hYpre_closed, hYpre_irreducible⟩ hZYpre
    intro x hx
    exact ⟨⟨x, hYC hx⟩, hYpre_subset_Z hx, rfl⟩

/-- Helper for Proposition 15.128.4: the maximal ambient irreducible closed subsets of a closed
owner that are not absorbed by `D` form a finite family. -/
lemma finite_maximal_components_not_subset [NoetherianSpace Ω]
    {C D : Set Ω} (hCclosed : IsClosed C) :
    ∃ S : Finset (IrreducibleCloseds Ω),
      ∀ Z : IrreducibleCloseds Ω,
        Z ∈ S ↔
          Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) Z ∧
            ¬ ((Z : Set Ω) ⊆ D) := by
  classical
  letI : Finite (irreducibleComponents C) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let ambient : irreducibleComponents C → IrreducibleCloseds Ω := fun Z ↦
    ⟨Subtype.val '' (Z : Set C),
      Z.2.1.image (Subtype.val : C → Ω) continuous_subtype_val.continuousOn,
      hCclosed.isClosedEmbedding_subtypeVal.isClosedMap _ <|
        isClosed_of_mem_irreducibleComponents (Z : Set C) Z.2⟩
  let T : Set (IrreducibleCloseds Ω) := {Z |
    Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) Z ∧
      ¬ ((Z : Set Ω) ⊆ D)}
  have hT_subset : T ⊆ Set.range ambient := by
    intro Z hZ
    let ZC : Set C := Subtype.val ⁻¹' (Z : Set Ω)
    have hZC_mem : ZC ∈ irreducibleComponents C := by
      rw [irreducibleComponents_eq_maximals_closed]
      refine ⟨⟨Z.isClosed.preimage continuous_subtype_val,
        isIrreducible_preimage_subtype_of_subset (C := C) Z hZ.1.1⟩, ?_⟩
      intro W hW hZCW
      let Y : IrreducibleCloseds Ω :=
        ⟨Subtype.val '' W,
          hW.2.image (Subtype.val : C → Ω) continuous_subtype_val.continuousOn,
          hCclosed.isClosedEmbedding_subtypeVal.isClosedMap _ hW.1⟩
      have hYC : (Y : Set Ω) ⊆ C := by
        rintro x ⟨y, hy, rfl⟩
        exact y.2
      have hZY : (Z : Set Ω) ⊆ Y := by
        intro x hx
        exact ⟨⟨x, hZ.1.1 hx⟩, hZCW hx, rfl⟩
      have hY_subset_Z : (Y : Set Ω) ⊆ Z := hZ.1.2 hYC hZY
      intro x hx
      exact hY_subset_Z ⟨x, hx, rfl⟩
    refine ⟨⟨ZC, hZC_mem⟩, ?_⟩
    apply IrreducibleCloseds.ext
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hZ.1.1 hx⟩, hx, rfl⟩
  have hRangeFinite : (Set.range ambient).Finite := by
    letI : Fintype (irreducibleComponents C) := Fintype.ofFinite (irreducibleComponents C)
    simpa [Set.image_univ] using (Set.toFinite (Set.univ : Set (irreducibleComponents C))).image ambient
  have hTfinite : T.Finite := hRangeFinite.subset hT_subset
  refine ⟨hTfinite.toFinset, ?_⟩
  intro Z
  simpa [T] using hTfinite.mem_toFinset Z

/-- Helper for Proposition 15.128.4: every point of the owner outside the base closed set lies on
one listed maximal owner component. -/
lemma mem_some_listed_component_of_mem_owner_diff_base [NoetherianSpace Ω]
    {C D : Set Ω} (hCclosed : IsClosed C)
    {S : Finset (IrreducibleCloseds Ω)}
    (hS : ∀ Z : IrreducibleCloseds Ω,
      Z ∈ S ↔
        Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) Z ∧
          ¬ ((Z : Set Ω) ⊆ D))
    {x : Ω} (hxC : x ∈ C) (hxD : x ∉ D) :
    ∃ Z : IrreducibleCloseds Ω, Z ∈ S ∧ x ∈ (Z : Set Ω) := by
  let xC : C := ⟨x, hxC⟩
  let ZC : irreducibleComponents C :=
    ⟨irreducibleComponent xC, irreducibleComponent_mem_irreducibleComponents xC⟩
  let Z : IrreducibleCloseds Ω :=
    ⟨Subtype.val '' (ZC : Set C),
      ZC.2.1.image (Subtype.val : C → Ω) continuous_subtype_val.continuousOn,
      hCclosed.isClosedEmbedding_subtypeVal.isClosedMap _ <|
        isClosed_of_mem_irreducibleComponents (ZC : Set C) ZC.2⟩
  have hZmax : Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) Z := by
    -- The component of the subtype point stays maximal after ambientizing it.
    simpa [Z, ZC] using maximal_of_ambient_irreducible_component (C := C) hCclosed ZC
  have hxZ : x ∈ (Z : Set Ω) := by
    exact ⟨xC, mem_irreducibleComponent, rfl⟩
  have hZnotD : ¬ ((Z : Set Ω) ⊆ D) := by
    intro hZD
    exact hxD (hZD hxZ)
  exact ⟨Z, (hS Z).2 ⟨hZmax, hZnotD⟩, hxZ⟩

/-- Helper for Proposition 15.128.4: among the listed maximal owner components, inclusion already
forces equality. -/
lemma listed_components_eq_of_subset [NoetherianSpace Ω]
    {C D : Set Ω} {S : Finset (IrreducibleCloseds Ω)}
    (hS : ∀ Z : IrreducibleCloseds Ω,
      Z ∈ S ↔
        Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) Z ∧
          ¬ ((Z : Set Ω) ⊆ D))
    {Y Z : IrreducibleCloseds Ω} (hY : Y ∈ S) (hZ : Z ∈ S)
    (hYZ : (Y : Set Ω) ⊆ Z) :
    Y = Z := by
  have hYmax :
      Maximal (fun T : IrreducibleCloseds Ω ↦ (T : Set Ω) ⊆ C) Y := (hS Y).1 hY |>.1
  have hZmax :
      Maximal (fun T : IrreducibleCloseds Ω ↦ (T : Set Ω) ⊆ C) Z := (hS Z).1 hZ |>.1
  -- Maximality of `Y` turns the assumed inclusion into the reverse inclusion.
  have hZY : (Z : Set Ω) ⊆ Y := hYmax.2 hZmax.1 hYZ
  apply IrreducibleCloseds.ext
  ext x
  exact ⟨fun hx ↦ hYZ hx, fun hx ↦ hZY hx⟩

/-- Helper for Proposition 15.128.4: the obstruction attached to a listed component is the base
closed set together with all the other listed owner components. -/
def listed_component_obstruction [DecidableEq (IrreducibleCloseds Ω)]
    {S : Finset (IrreducibleCloseds Ω)}
    (D : Set Ω) (Z : IrreducibleCloseds Ω) : Set Ω :=
  D ∪ ⋃ Y ∈ ((↑(S.erase Z) : Set (IrreducibleCloseds Ω))), ((Y : Set Ω) : Set Ω)

/-- Helper for Proposition 15.128.4: a listed component is not absorbed by the base closed set
plus the other listed components. -/
lemma listed_component_not_subset_base_union_others [NoetherianSpace Ω]
    [DecidableEq (IrreducibleCloseds Ω)] {C D : Set Ω} (hDclosed : IsClosed D)
    {S : Finset (IrreducibleCloseds Ω)}
    (hS : ∀ Z : IrreducibleCloseds Ω,
      Z ∈ S ↔
        Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) Z ∧
          ¬ ((Z : Set Ω) ⊆ D))
    {Z : IrreducibleCloseds Ω} (hZ : Z ∈ S) :
    ¬ ((Z : Set Ω) ⊆ listed_component_obstruction (S := S) D Z) := by
  classical
  let T : Finset (Set Ω) :=
    insert D ((S.erase Z).attach.image
      (fun Y : {Y // Y ∈ S.erase Z} ↦ ((Y.1 : IrreducibleCloseds Ω) : Set Ω)))
  intro hZO
  have hTclosed : ∀ W ∈ T, IsClosed W := by
    intro W hW
    rcases Finset.mem_insert.mp hW with rfl | hW
    · exact hDclosed
    · rcases Finset.mem_image.mp hW with ⟨Y, -, rfl⟩
      exact (Y.1 : IrreducibleCloseds Ω).isClosed
  -- Convert the obstruction cover into the finite-family form required by irreducibility.
  have hZT : (Z : Set Ω) ⊆ ⋃₀ (↑T : Set (Set Ω)) := by
    intro x hxZ
    have hxO : x ∈ listed_component_obstruction (S := S) D Z := hZO hxZ
    rcases hxO with hxD | hxOther
    · exact mem_sUnion.2 ⟨D, by simp [T], hxD⟩
    · rcases mem_iUnion₂.1 hxOther with ⟨Y, hY, hxY⟩
      have hYT : ((Y : Set Ω) : Set Ω) ∈ T := by
        refine Finset.mem_insert.mpr <| Or.inr ?_
        exact Finset.mem_image.mpr ⟨⟨Y, hY⟩, by simp⟩
      exact mem_sUnion.2 ⟨(Y : Set Ω), hYT, hxY⟩
  obtain ⟨W, hWT, hZW⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp Z.isIrreducible T hTclosed hZT
  rcases Finset.mem_insert.mp hWT with rfl | hWT
  · -- Landing in `D` contradicts the defining property of the listed component.
    exact ((hS Z).1 hZ).2 hZW
  · rcases Finset.mem_image.mp hWT with ⟨Y, hY, rfl⟩
    have hYS : (Y.1 : IrreducibleCloseds Ω) ∈ S := (Finset.mem_erase.mp Y.2).2
    -- If `Z` lies in another listed component, maximality forces equality.
    have hEq : Z = (Y.1 : IrreducibleCloseds Ω) :=
      listed_components_eq_of_subset (S := S) hS hZ hYS hZW
    exact (Finset.mem_erase.mp Y.2).1 hEq.symm

/-- Helper for Proposition 15.128.4: each listed owner component admits an ambient open trace in
`C \ D` which meets no other listed component. -/
lemma exists_component_pure_open_trace [NoetherianSpace Ω]
    {C D : Set Ω} (hCclosed : IsClosed C)
    (hDclosed : IsClosed D)
    {S : Finset (IrreducibleCloseds Ω)}
    (hS : ∀ Z : IrreducibleCloseds Ω,
      Z ∈ S ↔
        Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) Z ∧
          ¬ ((Z : Set Ω) ⊆ D))
    {Z : IrreducibleCloseds Ω} (hZ : Z ∈ S) :
    ∃ U : Set Ω, IsOpen U ∧ (U ∩ C).Nonempty ∧
      U ∩ C ⊆ ((Z : Set Ω) \ D) ∧
      ∀ Y : IrreducibleCloseds Ω, Y ∈ S → Y ≠ Z → U ∩ C ∩ (Y : Set Ω) = ∅ := by
  classical
  let O : Set Ω := listed_component_obstruction (S := S) D Z
  have hother_closed :
      IsClosed (⋃ Y ∈ ((↑(S.erase Z) : Set (IrreducibleCloseds Ω))), ((Y : Set Ω) : Set Ω)) := by
    simpa [Finset.mem_erase, and_comm, and_left_comm, and_assoc, eq_comm] using
      (isClosed_biUnion_finset
        (s := S.erase Z)
        (f := fun Y : IrreducibleCloseds Ω ↦ ((Y : Set Ω) : Set Ω))
        (fun Y _ ↦ Y.isClosed))
  have hOclosed : IsClosed O := by
    exact hDclosed.union hother_closed
  refine ⟨Oᶜ, hOclosed.isOpen_compl, ?_, ?_, ?_⟩
  · -- The obstruction is proper on `Z`, so some point of `Z` survives in the trace.
    have hZO : ¬ ((Z : Set Ω) ⊆ O) := by
      simpa [O] using
        listed_component_not_subset_base_union_others
          (C := C) (D := D) (S := S) hDclosed hS hZ
    have hpoint : ∃ x : Ω, x ∈ (Z : Set Ω) ∧ x ∉ O := by
      by_contra hpoint
      apply hZO
      intro x hxZ
      by_contra hxO
      exact hpoint ⟨x, hxZ, hxO⟩
    rcases hpoint with ⟨x, hxZ, hxO⟩
    have hxC : x ∈ C := ((hS Z).1 hZ).1.1 hxZ
    exact ⟨x, hxO, hxC⟩
  · intro x hx
    have hxO : x ∉ O := hx.1
    have hxC : x ∈ C := hx.2
    have hxD : x ∉ D := by
      intro hxD
      exact hxO (Or.inl hxD)
    obtain ⟨Y, hYS, hxY⟩ :=
      mem_some_listed_component_of_mem_owner_diff_base
        (C := C) (D := D) hCclosed hS hxC hxD
    -- Any surviving point of `Oᶜ ∩ C` cannot lie on one of the other listed components.
    have hYZ : Y = Z := by
      by_contra hYZ
      exact hxO <| Or.inr <| mem_iUnion₂.2 ⟨Y, Finset.mem_erase.mpr ⟨hYZ, hYS⟩, hxY⟩
    subst hYZ
    exact ⟨hxY, hxD⟩
  · intro Y hYS hYZ
    ext x
    constructor
    · intro hx
      exact False.elim <|
        hx.1.1 <| Or.inr <| mem_iUnion₂.2 ⟨Y, Finset.mem_erase.mpr ⟨hYZ, hYS⟩, hx.2⟩
    · intro hx
      exact False.elim hx

/-- Helper for Proposition 15.128.4: a nonempty open trace on the closure of the bad locus
contains an actual bad point. -/
lemma exists_bad_point_in_component_trace_of_closure_eq_owner
    {A C D U : Set Ω} {Z : IrreducibleCloseds Ω}
    (hclosure : closure A = C) (hUopen : IsOpen U) (hUC : (U ∩ C).Nonempty)
    (htrace : U ∩ C ⊆ ((Z : Set Ω) \ D)) :
    ∃ y : Ω, y ∈ A ∧ y ∈ U ∧ y ∈ (Z : Set Ω) ∧ y ∉ D := by
  rcases hUC with ⟨x, hxU, hxC⟩
  have hxclosure : x ∈ closure A := by
    simpa [hclosure] using hxC
  -- Density of `A` in `C` gives a genuine bad point inside the ambient open trace `U`.
  rcases mem_closure_iff.1 hxclosure U hUopen hxU with ⟨y, hyU, hyA⟩
  have hyC : y ∈ C := by
    simpa [hclosure] using subset_closure hyA
  have hytrace : y ∈ ((Z : Set Ω) \ D) := htrace ⟨hyU, hyC⟩
  exact ⟨y, hyA, hyU, hytrace.1, hytrace.2⟩

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: each listed owner component of the normalized bad locus
contains a genuine bad point which lies on no other listed component. -/
lemma exists_pure_bad_point_on_listed_component [NoetherianSpace Ω]
    {h : ℕ} (sections : Fin h → M)
    {C D : Set Ω} (hCclosed : IsClosed C) (hDclosed : IsClosed D)
    (hclosure : closure (section_dependence_locus sections \ D) = C)
    {S : Finset (IrreducibleCloseds Ω)}
    (hS : ∀ Z : IrreducibleCloseds Ω,
      Z ∈ S ↔
        Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) Z ∧
          ¬ ((Z : Set Ω) ⊆ D))
    {Z : IrreducibleCloseds Ω} (hZ : Z ∈ S) :
    ∃ y : Ω,
      y ∈ section_dependence_locus sections \ D ∧
      y ∈ (Z : Set Ω) ∧
      ∀ Y : IrreducibleCloseds Ω, Y ∈ S → Y ≠ Z → y ∉ (Y : Set Ω) := by
  classical
  obtain ⟨U, hUopen, hUnonempty, hUsub, hUdisj⟩ :=
    exists_component_pure_open_trace (C := C) (D := D) hCclosed hDclosed hS hZ
  obtain ⟨y, hybad, hyU, hyZ, hyD⟩ :=
    exists_bad_point_in_component_trace_of_closure_eq_owner
      (A := section_dependence_locus sections \ D) (C := C) (D := D) (U := U) (Z := Z)
      hclosure hUopen hUnonempty hUsub
  refine ⟨y, hybad, hyZ, ?_⟩
  intro Y hY hYZ hyY
  have hyC : y ∈ C := by
    simpa [hclosure] using subset_closure hybad
  have hEmpty := hUdisj Y hY hYZ
  have hyEmpty : y ∈ U ∩ C ∩ (Y : Set Ω) := ⟨⟨hyU, hyC⟩, hyY⟩
  exact by simpa [hEmpty] using hyEmpty

/-- Helper for Proposition 15.128.4: the listed maximal owner components admit pairwise distinct
points in `C \ D`, one on each listed component and on no other listed component. -/
lemma exists_pairwise_distinct_component_points_outside_base [NoetherianSpace Ω]
    {C D : Set Ω} (hCclosed : IsClosed C) (hDclosed : IsClosed D)
    {S : Finset (IrreducibleCloseds Ω)}
    (hS : ∀ Z : IrreducibleCloseds Ω,
      Z ∈ S ↔
        Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) Z ∧
          ¬ ((Z : Set Ω) ⊆ D)) :
    ∃ zs : {Z // Z ∈ S} → Ω,
      (∀ i, zs i ∈ C \ D) ∧
      (∀ i, zs i ∈ (i.1 : Set Ω)) ∧
      Pairwise fun i j ↦ zs i ≠ zs j := by
  classical
  have hpoint :
      ∀ i : {Z // Z ∈ S},
        ∃ z : Ω,
          z ∈ C \ D ∧
          z ∈ (i.1 : Set Ω) ∧
          ∀ Y : IrreducibleCloseds Ω, Y ∈ S → Y ≠ i.1 → z ∉ (Y : Set Ω) := by
    intro i
    obtain ⟨U, hUopen, hUnonempty, hUsub, hUdisj⟩ :=
      exists_component_pure_open_trace (C := C) (D := D) hCclosed hDclosed hS i.2
    rcases hUnonempty with ⟨z, hzU, hzC⟩
    have hztrace : z ∈ ((i.1 : Set Ω) \ D) := hUsub ⟨hzU, hzC⟩
    refine ⟨z, ⟨hzC, hztrace.2⟩, hztrace.1, ?_⟩
    intro Y hY hYi hzY
    have hEmpty := hUdisj Y hY hYi
    have hzEmpty : z ∈ U ∩ C ∩ (Y : Set Ω) := ⟨⟨hzU, hzC⟩, hzY⟩
    exact by simpa [hEmpty] using hzEmpty
  choose zs hzs_outside hzs_mem hzs_sep using hpoint
  refine ⟨zs, hzs_outside, hzs_mem, ?_⟩
  intro i j hij hEq
  have hij_carrier : j.1 ≠ i.1 := by
    intro hji
    apply hij
    cases i with
    | mk i hi =>
        cases j with
        | mk j hj =>
            cases hji
            simp
  have hzj : zs i ∈ (j.1 : Set Ω) := by
    simpa [hEq] using hzs_mem j
  exact hzs_sep i j.1 j.2 hij_carrier hzj

omit [Module.FinitePresentation R M] in
/-- Helper for Proposition 15.128.4: the listed owner components of the normalized bad locus admit
pairwise distinct bad points indexed by the listed components themselves. -/
lemma exists_pairwise_distinct_component_bad_points [NoetherianSpace Ω]
    {h : ℕ} (sections : Fin h → M)
    {C D : Set Ω} (hCclosed : IsClosed C) (hDclosed : IsClosed D)
    (hclosure : closure (section_dependence_locus sections \ D) = C)
    {S : Finset (IrreducibleCloseds Ω)}
    (hS : ∀ Z : IrreducibleCloseds Ω,
      Z ∈ S ↔
        Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ C) Z ∧
          ¬ ((Z : Set Ω) ⊆ D)) :
    ∃ ys : {Z // Z ∈ S} → Ω,
      (∀ i, ys i ∈ section_dependence_locus sections \ D) ∧
      (∀ i, ys i ∈ (i.1 : Set Ω)) ∧
      Pairwise fun i j ↦ ys i ≠ ys j := by
  classical
  have hpoint :
      ∀ i : {Z // Z ∈ S},
        ∃ y : Ω,
          y ∈ section_dependence_locus sections \ D ∧
          y ∈ (i.1 : Set Ω) ∧
          ∀ Y : IrreducibleCloseds Ω, Y ∈ S → Y ≠ i.1 → y ∉ (Y : Set Ω) := by
    intro i
    exact exists_pure_bad_point_on_listed_component
      (sections := sections) (C := C) (D := D) hCclosed hDclosed hclosure hS i.2
  choose ys hys_bad hys_mem hys_sep using hpoint
  refine ⟨ys, hys_bad, hys_mem, ?_⟩
  intro i j hij hEq
  have hij_carrier : j.1 ≠ i.1 := by
    intro hji
    apply hij
    cases i with
    | mk i hi =>
        cases j with
        | mk j hj =>
            cases hji
            simp
  have hyj : ys i ∈ (j.1 : Set Ω) := by
    simpa [hEq] using hys_mem j
  exact hys_sep i j.1 j.2 hij_carrier hyj

/-- Helper for Proposition 15.128.4: a strict inclusion of irreducible closed owners raises the
available codimension lower bound by one. -/
lemma succ_le_coheight_of_strictly_smaller_component
    {W Z : IrreducibleCloseds Ω} (hWZ : W < Z) {k : ℕ}
    (hk : (k : ℕ∞) ≤ coheight Z) :
    (((k + 1 : ℕ) : ℕ∞)) ≤ coheight W := by
  have hnot_le : ¬ coheight W ≤ (k : ℕ∞) := by
    intro hW
    have hZlt : coheight Z < (k : ℕ∞) :=
      (Order.coheight_le_coe_iff (x := W) (n := k)).1 hW Z hWZ
    exact not_lt_of_ge hk hZlt
  by_cases htop : coheight W = ⊤
  · simpa [htop]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
    have hklt : (k : ℕ∞) < n := by
      simpa [hn] using lt_of_not_ge hnot_le
    simpa [hn] using
      (ENat.coe_le_coe.mpr (Nat.succ_le_of_lt (ENat.coe_lt_coe.mp hklt)) :
        (((k + 1 : ℕ) : ℕ∞)) ≤ n)

/-- Helper for Proposition 15.128.4: a proper contained irreducible closed subset is strictly
smaller once one exhibits a point of the owner outside it. -/
lemma strict_lt_of_subset_and_point_not_mem
    {W Z : IrreducibleCloseds Ω} {y : Ω}
    (hWZ : (W : Set Ω) ⊆ Z) (hyZ : y ∈ (Z : Set Ω)) (hyW : y ∉ (W : Set Ω)) :
    W < Z := by
  refine lt_of_le_of_ne hWZ ?_
  intro hEq
  exact hyW <| by simpa [hEq] using hyZ

/-- Helper for Proposition 15.128.4: an irreducible closed subset contained in the union of two
closed sets is already contained in one of them. -/
lemma irreducible_subset_union_of_closed
    {A B : Set Ω} (hAclosed : IsClosed A) (hBclosed : IsClosed B)
    {Z : IrreducibleCloseds Ω} (hZAB : (Z : Set Ω) ⊆ A ∪ B) :
    (Z : Set Ω) ⊆ A ∨ (Z : Set Ω) ⊆ B := by
  classical
  let T : Finset (Set Ω) := {A, B}
  have hZT : (Z : Set Ω) ⊆ ⋃₀ (↑T : Set (Set Ω)) := by
    intro x hxZ
    rcases hZAB hxZ with hxA | hxB
    · exact mem_sUnion.2 ⟨A, by simp [T], hxA⟩
    · exact mem_sUnion.2 ⟨B, by simp [T], hxB⟩
  obtain ⟨Y, hYT, hZY⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp Z.isIrreducible T
      (by
        intro Y hY
        have hY' : Y = A ∨ Y = B := by
          simpa [T, Finset.mem_insert, Finset.mem_singleton] using hY
        rcases hY' with rfl | rfl
        · exact hAclosed
        · exact hBclosed)
      hZT
  have hY' : Y = A ∨ Y = B := by
    simpa [T, Finset.mem_insert, Finset.mem_singleton] using hYT
  rcases hY' with rfl | rfl
  · exact Or.inl hZY
  · exact Or.inr hZY

/-- Helper for Proposition 15.128.4: every maximal irreducible component of `closure A` meets the
source set `A`. -/
lemma maximal_component_of_closure_meets_source [NoetherianSpace Ω]
    {A : Set Ω} {W : IrreducibleCloseds Ω}
    (hW : Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ closure A) W) :
    ∃ x : Ω, x ∈ A ∧ x ∈ (W : Set Ω) := by
  classical
  obtain ⟨S, hS⟩ :=
    finite_maximal_components_not_subset
      (C := closure A) (D := (∅ : Set Ω)) isClosed_closure
  have hWnotempty : ¬ ((W : Set Ω) ⊆ (∅ : Set Ω)) := by
    intro hWempty
    rcases W.isIrreducible.nonempty with ⟨x, hxW⟩
    exact hWempty hxW
  have hWS : W ∈ S := (hS W).2 ⟨hW, hWnotempty⟩
  obtain ⟨U, hUopen, hUnonempty, hUsub, _⟩ :=
    exists_component_pure_open_trace
      (C := closure A) (D := (∅ : Set Ω))
      isClosed_closure isClosed_empty hS hWS
  -- The pure open trace on `W` contains an actual point of the dense source set `A`.
  obtain ⟨x, hxA, _, hxW, _⟩ :=
    exists_bad_point_in_component_trace_of_closure_eq_owner
      (A := A) (C := closure A) (D := (∅ : Set Ω)) (U := U) (Z := W)
      rfl hUopen hUnonempty hUsub
  exact ⟨x, hxA, hxW⟩

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
@[stacks 0GVB]
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
      irreducible_components_codim_at_least k F' := by
  induction k generalizing h n sections F pts with
  | zero =>
      -- The base case is exactly the prescribed-values construction plus the tautological closure.
      simpa using
        exists_section_with_prescribed_values_and_codim_controlled_dependence_locus_zero
          (R := R) (M := M) sections hFclosed hzero pts hpts hptsF v hdim
  | succ k ih =>
      -- Route correction: keep the source-proof induction on `k`, with the bad locus replaced by
      -- closures of the outside-`F` dependence loci, rather than switching to a different route.
      classical
      have hdim_prev : ∀ x : Ω, h + k ≤ Module.finrank (κ(x)) (V(x)) := by
        intro x
        exact le_trans (by simpa [Nat.add_assoc] using Nat.le_succ (h + k)) (hdim x)
      -- The first recursive call constructs the auxiliary section `u` and a codimension-`k`
      -- witness set controlling the enlarged dependence locus.
      obtain ⟨u, G, hGclosed, hupts, hdepG, hcodimG⟩ :=
        ih sections hFclosed hzero pts hpts hptsF v hdim_prev
      let G₀ : Set Ω := closure (section_dependence_locus (Fin.snoc sections u) \ F)
      have hbad_subset : section_dependence_locus (Fin.snoc sections u) \ F ⊆ G := by
        intro x hx
        rcases hdepG hx.1 with hxF | hxG
        · exact False.elim (hx.2 hxF)
        · exact hxG
      have hdepG₀ : section_dependence_locus (Fin.snoc sections u) ⊆ F ∪ G₀ := by
        -- The normalized owner `G₀` is the closure of the bad locus outside `F`.
        simpa [G₀] using
          section_dependence_locus_subset_union_closure_diff
            (sections := Fin.snoc sections u) F
      have hG₀closed : IsClosed G₀ := isClosed_closure
      have hG₀subset : G₀ ⊆ G := by
        exact closure_minimal hbad_subset hGclosed
      have hcodimG₀ : irreducible_components_codim_at_least k G₀ := by
        -- Normalize the first recursive error set without losing the codimension-`k` bound.
        exact irreducible_components_codim_at_least_closure_of_subset
          (A := section_dependence_locus (Fin.snoc sections u) \ F) (B := G)
          hbad_subset hGclosed hcodimG
      obtain ⟨S, hS⟩ :=
        finite_maximal_components_not_subset (C := G₀) (D := F) hG₀closed
      have hcover_owner_diff :
          ∀ ⦃x : Ω⦄, x ∈ G₀ → x ∉ F →
            ∃ Z : IrreducibleCloseds Ω, Z ∈ S ∧ x ∈ (Z : Set Ω) := by
        intro x hxG₀ hxF
        -- Every point of the normalized owner outside `F` lies on one listed owner component.
        exact mem_some_listed_component_of_mem_owner_diff_base
          (C := G₀) (D := F) hG₀closed hS hxG₀ hxF
      have hcomponent_trace :
          ∀ ⦃Z : IrreducibleCloseds Ω⦄, Z ∈ S →
            ∃ U : Set Ω, IsOpen U ∧ (U ∩ G₀).Nonempty ∧
              U ∩ G₀ ⊆ ((Z : Set Ω) \ F) ∧
              ∀ Y : IrreducibleCloseds Ω, Y ∈ S → Y ≠ Z → U ∩ G₀ ∩ (Y : Set Ω) = ∅ := by
        intro Z hZ
        -- Each listed owner component can be separated from the others by an ambient open trace.
        exact exists_component_pure_open_trace
          (C := G₀) (D := F) hG₀closed hFclosed hS hZ
      obtain ⟨ys, hys_bad, hys_mem, hys_pairwise⟩ :=
        exists_pairwise_distinct_component_bad_points
          (sections := Fin.snoc sections u) (C := G₀) (D := F) hG₀closed hFclosed rfl hS
      have hys_sections_indep :
          ∀ i : {Z // Z ∈ S},
            LinearIndependent (κ((ys i))) (closedPointFiberVisibleClass (ys i) ∘ sections) := by
        intro i
        have hy_not_dep : ys i ∉ section_dependence_locus sections := by
          intro hy_dep
          exact (hys_bad i).2 (hzero hy_dep)
        -- Each chosen point lies outside `F`, so the original sections stay independent there.
        simpa [section_dependence_locus] using hy_not_dep
      have hu_span_at_ys :
          ∀ i : {Z // Z ∈ S},
            closedPointFiberVisibleClass (ys i) u ∈
              Submodule.span (κ((ys i)))
                (Set.range (closedPointFiberVisibleClass (ys i) ∘ sections)) := by
        intro i
        have hys_bad_snoc :
            ¬ LinearIndependent (κ((ys i)))
              (Fin.snoc (closedPointFiberVisibleClass (ys i) ∘ sections)
                (closedPointFiberVisibleClass (ys i) u)) := by
          -- Rewrite the badness of `(sections, u)` at `ys i` into the explicit `Fin.snoc` family.
          exact
            (mem_section_dependence_locus_snoc_iff
              (R := R) (M := M) (ys i) sections u).1 (hys_bad i).1
        exact snoc_last_mem_span_of_not_linearIndependent
          (sections := closedPointFiberVisibleClass (ys i) ∘ sections)
          (u := closedPointFiberVisibleClass (ys i) u)
          (hsections := hys_sections_indep i)
          hys_bad_snoc
      have hys_dim :
          ∀ i : {Z // Z ∈ S},
            h + 1 ≤ Module.finrank (κ((ys i))) (V((ys i))) := by
        intro i
        exact le_trans
          (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le k)) h)
          (hdim (ys i))
      have hw_exists :
          ∀ i : {Z // Z ∈ S},
            ∃ w : V((ys i)),
              w ∉ Submodule.span (κ((ys i)))
                (Set.range (closedPointFiberVisibleClass (ys i) ∘ sections)) := by
        intro i
        -- The fibre-dimension bound leaves room for one visible class outside the old span.
        exact exists_not_mem_span_of_succ_le_finrank
          (sections := closedPointFiberVisibleClass (ys i) ∘ sections)
          (hsections := hys_sections_indep i)
          (hdim := hys_dim i)
      choose w hw_not_mem using hw_exists
      let m := Fintype.card {Z // Z ∈ S}
      let e : Fin m ≃ {Z // Z ∈ S} := (Fintype.equivFin {Z // Z ∈ S}).symm
      let ysFin : Fin m → Ω := fun j ↦ ys (e j)
      have hysFin_pairwise : Pairwise fun i j ↦ ysFin i ≠ ysFin j := by
        intro i j hij
        -- Reindex the component-marking family from the finite subtype to `Fin m`.
        simpa [ysFin, e] using hys_pairwise (fun h ↦ hij (e.injective h))
      have hysFin_not_memF : ∀ j, ysFin j ∉ F := by
        intro j
        exact (hys_bad (e j)).2
      have hysFin_memG₀ : ∀ j, ysFin j ∈ G₀ := by
        intro j
        have hy_dep : ysFin j ∈ section_dependence_locus (Fin.snoc sections u) := (hys_bad (e j)).1
        have hy_notF : ysFin j ∉ F := hysFin_not_memF j
        rcases hdepG₀ hy_dep with hyF | hyG₀
        · exact False.elim (hy_notF hyF)
        · exact hyG₀
      have happend_pairwise :
          Pairwise fun i j ↦ (Fin.append pts ysFin) i ≠ (Fin.append pts ysFin) j := by
        -- The prescribed points lie in `F`, while the new component points lie outside `F`.
        exact pairwise_append_of_mem_base_and_outside_base
          pts ysFin hpts hysFin_pairwise hptsF hysFin_not_memF
      let ptsAll : Fin (n + m) → Ω := Fin.append pts ysFin
      have hptsAll_pairwise : Pairwise fun i j ↦ ptsAll i ≠ ptsAll j := by
        simpa [ptsAll] using happend_pairwise
      have hptsAll_castAdd : ∀ i, ptsAll (Fin.castAdd m i) = pts i := by
        intro i
        simp [ptsAll, Fin.append_left]
      have hptsAll_natAdd : ∀ j, ptsAll (Fin.natAdd n j) = ysFin j := by
        intro j
        simp [ptsAll, Fin.append_right]
      let prescribed_right : (j : Fin m) → V((ptsAll (Fin.natAdd n j))) := by
        intro j
        simpa [ptsAll] using w (e j)
      let prescribed : ∀ i : Fin (n + m), V((ptsAll i)) :=
        Fin.addCases (fun _ ↦ 0) prescribed_right
      have hptsAll_mem : ∀ i : Fin (n + m), ptsAll i ∈ F ∪ G₀ := by
        intro i
        cases i using Fin.addCases with
        | left i =>
            simpa [ptsAll] using Or.inl (hptsF i)
        | right j =>
            simpa [ptsAll] using Or.inr (hysFin_memG₀ j)
      have hdim_snoc :
          ∀ x : Ω, (h + 1) + k ≤
            Module.finrank (κ(x)) (closedPointFiberVisibleQuotient M x) := by
        intro x
        -- Rewrite the original `h + (k + 1)` bound into the form expected by the second recursion.
        simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hdim x
      -- The second recursive call matches the source proof: enlarge the family by `u` and force
      -- the correction section to vanish on `pts` and hit the chosen `w_i` on the component points.
      obtain ⟨t, H, hHclosed, ht_prescribed, hdepH, hcodimH⟩ :=
        ih (sections := Fin.snoc sections u) (F := F ∪ G₀)
          (hFclosed.union hG₀closed) hdepG₀
          (pts := ptsAll) hptsAll_pairwise hptsAll_mem
          prescribed hdim_snoc
      have ht_pts_zero : ∀ i, closedPointFiberVisibleClass (pts i) t = 0 := by
        intro i
        have h :
            closedPointFiberVisibleClass (ptsAll (Fin.castAdd m i)) t = 0 := by
          simpa [prescribed] using ht_prescribed (Fin.castAdd m i)
        rw [hptsAll_castAdd i] at h
        exact h
      have ht_ys :
          ∀ j, closedPointFiberVisibleClass (ysFin j) t = w (e j) := by
        intro j
        have hcast :=
          congrArg
            (Eq.mp (by
              simp [ptsAll, Fin.append_right] :
                V(ptsAll (Fin.natAdd n j)) = V(ysFin j)))
            (ht_prescribed (Fin.natAdd n j))
        have hleft :
            Eq.mp (by
              simp [ptsAll, Fin.append_right] :
                V(ptsAll (Fin.natAdd n j)) = V(ysFin j))
              (closedPointFiberVisibleClass (ptsAll (Fin.natAdd n j)) t) =
                closedPointFiberVisibleClass (ysFin j) t := by
          simpa [ptsAll, Fin.append_right] using
            dependent_family_transport_eq
              (f := fun x ↦ closedPointFiberVisibleClass x t)
              (h := hptsAll_natAdd j)
        calc
          closedPointFiberVisibleClass (ysFin j) t
              = Eq.mp (by
                  simp [ptsAll, Fin.append_right] :
                    V(ptsAll (Fin.natAdd n j)) = V(ysFin j))
                  (closedPointFiberVisibleClass (ptsAll (Fin.natAdd n j)) t) := by
                    exact hleft.symm
          _ = w (e j) := by
                simpa [prescribed, prescribed_right, ptsAll, Fin.append_right] using hcast
      obtain ⟨T, hT⟩ :=
        finite_maximal_components_not_subset (C := H) (D := F ∪ G₀) hHclosed
      obtain ⟨zs, hzs_outside, hzs_mem, hzs_pairwise⟩ :=
        exists_pairwise_distinct_component_points_outside_base
          (C := H) (D := F ∪ G₀) hHclosed (hFclosed.union hG₀closed) hT
      let l := Fintype.card {Z // Z ∈ T}
      let eH : Fin l ≃ {Z // Z ∈ T} := (Fintype.equivFin {Z // Z ∈ T}).symm
      let zsFin : Fin l → Ω := fun r ↦ zs (eH r)
      have hzsFin_pairwise : Pairwise fun i j ↦ zsFin i ≠ zsFin j := by
        intro i j hij
        -- Reindex the `H`-component points from the finite subtype to `Fin l`.
        simpa [zsFin, eH] using hzs_pairwise (fun h ↦ hij (eH.injective h))
      have hzsFin_not_mem_base : ∀ r, zsFin r ∉ F ∪ G₀ := by
        intro r
        exact (hzs_outside (eH r)).2
      have hysFin_mem_base : ∀ j, ysFin j ∈ F ∪ G₀ := by
        intro j
        exact Or.inr (hysFin_memG₀ j)
      have happend_yszs_pairwise :
          Pairwise fun i j ↦ (Fin.append ysFin zsFin) i ≠ (Fin.append ysFin zsFin) j := by
        -- The `ys` points lie in the base owner `F ∪ G₀`, while the `zs` points lie outside it.
        exact pairwise_append_of_mem_base_and_outside_base
          (D := F ∪ G₀) ysFin zsFin hysFin_pairwise hzsFin_pairwise
          hysFin_mem_base hzsFin_not_mem_base
      let ptsBad : Fin (m + l) → Ω := Fin.addCases ysFin zsFin
      have hptsBad_pairwise : Pairwise fun i j ↦ ptsBad i ≠ ptsBad j := by
        simpa [ptsBad] using happend_yszs_pairwise
      have hptsBad_castAdd : ∀ j, ptsBad (Fin.castAdd l j) = ysFin j := by
        intro j
        simpa [ptsBad] using
          (Fin.addCases_left (left := ysFin) (right := zsFin) j)
      have hptsBad_natAdd : ∀ r, ptsBad (Fin.natAdd m r) = zsFin r := by
        intro r
        simpa [ptsBad] using
          (Fin.addCases_right (left := ysFin) (right := zsFin) r)
      let residueValues : ∀ i : Fin (m + l), κ((ptsBad i)) :=
        Fin.addCases (fun _ ↦ 1) (fun _ ↦ 0)
      obtain ⟨f, hf_residue⟩ :=
        exists_scalar_with_prescribed_residue_values_at_pairwise_distinct_closed_points
          (R := R) (pts := ptsBad) hptsBad_pairwise residueValues
      have hf_ys :
          ∀ j,
            closedPointFiberResidueFieldAlgEquiv (R := R) (ysFin j)
              (Ideal.Quotient.mk ((ysFin j).1.asIdeal) f) = 1 := by
        intro j
        have h :
            closedPointFiberResidueFieldAlgEquiv (R := R) (ptsBad (Fin.castAdd l j))
              (Ideal.Quotient.mk ((ptsBad (Fin.castAdd l j)).1.asIdeal) f) = 1 := by
          simpa [residueValues] using hf_residue (Fin.castAdd l j)
        rw [hptsBad_castAdd j] at h
        exact h
      have hf_zs :
          ∀ r,
            closedPointFiberResidueFieldAlgEquiv (R := R) (zsFin r)
              (Ideal.Quotient.mk ((zsFin r).1.asIdeal) f) = 0 := by
        intro r
        have h :
            closedPointFiberResidueFieldAlgEquiv (R := R) (ptsBad (Fin.natAdd m r))
              (Ideal.Quotient.mk ((ptsBad (Fin.natAdd m r)).1.asIdeal) f) = 0 := by
          simpa [residueValues] using hf_residue (Fin.natAdd m r)
        rw [hptsBad_natAdd r] at h
        exact h
      let s : M := u + f • t
      have hs_pts : ∀ i, closedPointFiberVisibleClass (pts i) s = v i := by
        intro i
        -- The splice keeps the original prescribed values because `t` vanishes at every `pts i`.
        calc
          closedPointFiberVisibleClass (pts i) s
              = closedPointFiberVisibleClass (pts i) u
                  + (closedPointFiberResidueFieldAlgEquiv (R := R) (pts i)
                      (Ideal.Quotient.mk (pts i).1.asIdeal f)) •
                      closedPointFiberVisibleClass (pts i) t := by
                  simpa [s] using
                    closedPointFiberVisibleClass_splice_eq
                      (R := R) (M := M) (x := pts i) (u := u) (t := t) (f := f)
          _ = v i
                + (closedPointFiberResidueFieldAlgEquiv (R := R) (pts i)
                    (Ideal.Quotient.mk (pts i).1.asIdeal f)) • 0 := by
                  rw [hupts, ht_pts_zero]
          _ = v i := by simp
      let _ := hcomponent_trace
      let _ := hys_mem
      let _ := hys_sections_indep
      let _ := hu_span_at_ys
      let _ := hw_not_mem
      let _ := hHclosed
      let _ := ht_prescribed
      let _ := hdepH
      let _ := hcodimH
      let _ := hT
      let _ := hzs_outside
      let _ := hzs_mem
      let _ := hzs_pairwise
      let _ := hzsFin_pairwise
      let _ := happend_yszs_pairwise
      let _ := ht_pts_zero
      let _ := ht_ys
      let _ := residueValues
      let _ := hf_residue
      let _ := hf_ys
      let _ := hf_zs
      let _ := hs_pts
      let B : Set Ω := section_dependence_locus (Fin.snoc sections s)
      have hysFin_not_dep : ∀ j : Fin m, ysFin j ∉ B := by
        intro j
        have hs_eval :
            closedPointFiberVisibleClass (ysFin j) s =
              closedPointFiberVisibleClass (ysFin j) u + w (e j) := by
          have hs_splice :
              closedPointFiberVisibleClass (ysFin j) s =
                closedPointFiberVisibleClass (ysFin j) u +
                  (closedPointFiberResidueFieldAlgEquiv (R := R) (ysFin j)
                    (Ideal.Quotient.mk (ysFin j).1.asIdeal f)) •
                    closedPointFiberVisibleClass (ysFin j) t := by
            simpa only [s] using
              closedPointFiberVisibleClass_splice_eq
                (R := R) (M := M) (x := ysFin j) (u := u) (t := t) (f := f)
          calc
            closedPointFiberVisibleClass (ysFin j) s
                = closedPointFiberVisibleClass (ysFin j) u +
                    (closedPointFiberResidueFieldAlgEquiv (R := R) (ysFin j)
                      (Ideal.Quotient.mk (ysFin j).1.asIdeal f)) •
                      closedPointFiberVisibleClass (ysFin j) t := hs_splice
            _ = closedPointFiberVisibleClass (ysFin j) u + 1 • w (e j) := by
                  simpa [hf_ys j, ht_ys j]
            _ = closedPointFiberVisibleClass (ysFin j) u + w (e j) := by
                  simp
        have hli :
            LinearIndependent (κ((ysFin j)))
              (Fin.snoc (closedPointFiberVisibleClass (ysFin j) ∘ sections)
                (closedPointFiberVisibleClass (ysFin j) s)) := by
          rw [hs_eval]
          exact linearIndependent_snoc_add_of_mem_span
              (sections := closedPointFiberVisibleClass (ysFin j) ∘ sections)
              (u := closedPointFiberVisibleClass (ysFin j) u)
              (w := w (e j))
              (hsections := hys_sections_indep (e j))
              (hu := hu_span_at_ys (e j))
              (hw := hw_not_mem (e j))
        exact
          (not_mem_section_dependence_locus_snoc_iff
            (R := R) (M := M) (ysFin j) sections s).2 hli
      have hys_not_dep :
          ∀ i : {Z // Z ∈ S}, ys i ∉ B := by
        intro i
        simpa [ysFin, e] using hysFin_not_dep (e.symm i)
      have hzsFin_not_dep : ∀ r : Fin l, zsFin r ∉ B := by
        intro r
        let z : Ω := zsFin r
        let c : κ(z) :=
          closedPointFiberResidueFieldAlgEquiv (R := R) z
            (Ideal.Quotient.mk z.1.asIdeal f)
        have hz_not_dep_u : z ∉ section_dependence_locus (Fin.snoc sections u) := by
          intro hz_dep
          exact (hzs_outside (eH r)).2 (hdepG₀ hz_dep)
        have hli_u :
            LinearIndependent (κ(z))
              (Fin.snoc (closedPointFiberVisibleClass z ∘ sections)
                (closedPointFiberVisibleClass z u)) :=
          (not_mem_section_dependence_locus_snoc_iff
            (R := R) (M := M) z sections u).1 hz_not_dep_u
        have hs_eval :
            closedPointFiberVisibleClass z s =
              closedPointFiberVisibleClass z u := by
          have hc : c = 0 := by
            simpa [z, c] using hf_zs r
          -- At the `zs`-points the prescribed scalar has zero residue, so the splice does not
          -- change the visible class.
          simpa only [s, c] using
            closedPointFiberVisibleClass_splice_eq_left_of_residue_zero
              (R := R) (M := M) (x := z) (u := u) (t := t) (f := f) hc
        have hli :
            LinearIndependent (κ(z))
              (Fin.snoc (closedPointFiberVisibleClass z ∘ sections)
                (closedPointFiberVisibleClass z s)) := by
          exact linearIndependent_snoc_congr_last
            (sections := closedPointFiberVisibleClass z ∘ sections) hs_eval hli_u
        simpa [B, z] using
          (not_mem_section_dependence_locus_snoc_iff
            (R := R) (M := M) z sections s).2 hli
      have hzs_not_dep :
          ∀ i : {Z // Z ∈ T}, zs i ∉ B := by
        intro i
        simpa [zsFin, eH] using hzsFin_not_dep (eH.symm i)
      have hdep_s_raw : section_dependence_locus (Fin.snoc sections s) ⊆ F ∪ G₀ ∪ H := by
        intro x hxB
        by_contra hx_out
        have hx_not_owner : x ∉ (F ∪ G₀) ∪ H := by
          simpa [Set.union_assoc] using hx_out
        have hx_not_dep_ut : x ∉ section_dependence_locus (Fin.snoc (Fin.snoc sections u) t) := by
          intro hx_dep_ut
          exact hx_not_owner (hdepH hx_dep_ut)
        have hli_ut' :
            LinearIndependent (κ(x))
              (Fin.snoc (closedPointFiberVisibleClass x ∘ Fin.snoc sections u)
                (closedPointFiberVisibleClass x t)) :=
          (not_mem_section_dependence_locus_snoc_iff
            (R := R) (M := M) (x := x) (sections := Fin.snoc sections u) (u := t)).1
            hx_not_dep_ut
        have hli_ut :
            LinearIndependent (κ(x))
              (Fin.snoc
                (Fin.snoc (closedPointFiberVisibleClass x ∘ sections)
                  (closedPointFiberVisibleClass x u))
                (closedPointFiberVisibleClass x t)) := by
          -- Rewrite the nested visible-class family through a fixed-map `Fin.snoc` helper.
          exact linearIndependent_snoc_snoc_of_comp_snoc
            (K := κ(x)) (f := closedPointFiberVisibleClass x) sections u
            (closedPointFiberVisibleClass x t) hli_ut'
        have hli :
            LinearIndependent (κ(x))
              (Fin.snoc (closedPointFiberVisibleClass x ∘ sections)
                (closedPointFiberVisibleClass x s)) := by
          have hli_splice :
              LinearIndependent (κ(x))
                (Fin.snoc (closedPointFiberVisibleClass x ∘ sections)
                  (closedPointFiberVisibleClass x (u + f • t))) := by
            exact
              linearIndependent_snoc_visible_splice
                (R := R) (M := M) (x := x) (sections := sections) (u := u) (t := t) (f := f)
                hli_ut
          exact linearIndependent_snoc_congr_last
            (sections := closedPointFiberVisibleClass x ∘ sections)
            (by
              rfl)
            hli_splice
        have hx_not_B :
            x ∉ section_dependence_locus (Fin.snoc sections s) := by
          exact
            (not_mem_section_dependence_locus_snoc_iff
              (R := R) (M := M) x sections s).2 hli
        exact hx_not_B hxB
      have hdep_s_subset : B ⊆ F ∪ G₀ ∪ H := by
        simpa [B] using hdep_s_raw
      let F' : Set Ω := normalized_bad_locus B F
      have hF'closed : IsClosed F' := by
        change IsClosed (closure (B \ F))
        exact isClosed_closure
      have hdep_final : B ⊆ F ∪ F' := by
        -- Normalize the final bad locus by taking the closure outside `F`.
        change section_dependence_locus (Fin.snoc sections s) ⊆
          F ∪ closure (section_dependence_locus (Fin.snoc sections s) \ F)
        exact
          section_dependence_locus_subset_union_closure_diff
            (sections := Fin.snoc sections s) F
      have hF'subset_owner : F' ⊆ G₀ ∪ H := by
        -- The final normalized bad locus is supported on the two auxiliary owners.
        refine closure_minimal ?_ (hG₀closed.union hHclosed)
        intro x hx
        have hx_owner : x ∈ (F ∪ G₀) ∪ H := by
          simpa [Set.union_assoc] using hdep_s_subset hx.1
        rcases hx_owner with hxFG | hxH
        · rcases hxFG with hxF | hxG₀
          · exact False.elim (hx.2 hxF)
          · exact Or.inl hxG₀
        · exact Or.inr hxH
      have hcodim_from_G₀ :
          ∀ {W : IrreducibleCloseds Ω},
            Maximal (irreducible_closed_subset_pred F') W →
            irreducible_closed_subset_pred G₀ W →
            (k + 1 : ℕ∞) ≤ coheight W := by
        intro W hWmax hWG₀
        have hWmax' : Maximal (fun Y : IrreducibleCloseds Ω ↦ (Y : Set Ω) ⊆ F') W := by
          simpa [irreducible_closed_subset_pred] using hWmax
        have hWG₀' : (W : Set Ω) ⊆ G₀ := by
          simpa [irreducible_closed_subset_pred] using hWG₀
        obtain ⟨xW, hxWbad, hxWW⟩ :=
          maximal_component_of_closure_meets_source
            (A := B \ F) (W := W) (by simpa [F', normalized_bad_locus] using hWmax')
        have hW_not_subset_F : ¬ ((W : Set Ω) ⊆ F) := by
          intro hWF
          exact hxWbad.2 (hWF hxWW)
        obtain ⟨Z, hZmax, hWZ⟩ :=
          exists_component_of_closed_set_containing_irreducible
            (B := G₀) hG₀closed W hWG₀'
        have hZnotF : ¬ ((Z : Set Ω) ⊆ F) := by
          intro hZF
          exact hW_not_subset_F (hWZ.trans hZF)
        have hZS : Z ∈ S := (hS Z).2 ⟨hZmax, hZnotF⟩
        let i : {Z // Z ∈ S} := ⟨Z, hZS⟩
        have hy_not_F' : ys i ∉ F' := by
          -- The component-marking point stays outside the final normalized bad locus.
          simpa [B, F', normalized_bad_locus] using
            point_not_mem_closure_diff_of_not_mem_section_dependence_locus
              (sections := Fin.snoc sections s) (F := F) (x := ys i) (hys_not_dep i)
        have hy_not_W : ys i ∉ (W : Set Ω) := by
          intro hyW
          exact hy_not_F' (hWmax.1 hyW)
        have hWltZ : W < Z := by
          -- The owner component `Z` contains `W`, but it also contains the surviving point `ys i`
          -- outside `W`, so the inclusion is strict.
          exact strict_lt_of_subset_and_point_not_mem hWZ (hys_mem i) hy_not_W
        exact succ_le_coheight_of_strictly_smaller_component hWltZ (hcodimG₀ Z hZmax)
      have hcodimF' : irreducible_components_codim_at_least (k + 1) F' := by
        intro W hWmax
        have hWmax_owner : Maximal (irreducible_closed_subset_pred F') W := by
          simpa [irreducible_closed_subset_pred] using hWmax
        have hW_owner : (W : Set Ω) ⊆ G₀ ∪ H := hWmax.1.trans hF'subset_owner
        have hsplit : (W : Set Ω) ⊆ G₀ ∨ (W : Set Ω) ⊆ H := by
          -- A maximal final component must already live on one of the two auxiliary owners.
          exact irreducible_subset_union_of_closed hG₀closed hHclosed hW_owner
        rcases hsplit with hWG₀ | hWH
        · exact hcodim_from_G₀ hWmax_owner <| by
            simpa [irreducible_closed_subset_pred] using hWG₀
        · obtain ⟨xW, hxWbad, hxWW⟩ :=
            maximal_component_of_closure_meets_source
              (A := B \ F) (W := W) (by simpa [F', normalized_bad_locus] using hWmax)
          have hW_not_subset_F : ¬ ((W : Set Ω) ⊆ F) := by
            intro hWF
            exact hxWbad.2 (hWF hxWW)
          obtain ⟨Z, hZmax, hWZ⟩ :=
            exists_component_of_closed_set_containing_irreducible
              (B := H) hHclosed W hWH
          by_cases hZbase : (Z : Set Ω) ⊆ F ∪ G₀
          · have hWbase : (W : Set Ω) ⊆ F ∪ G₀ := hWZ.trans hZbase
            have hWsplit' : (W : Set Ω) ⊆ F ∨ (W : Set Ω) ⊆ G₀ := by
              -- If the `H`-owner is absorbed by `F ∪ G₀`, irreducibility pushes `W` into one side.
              exact irreducible_subset_union_of_closed hFclosed hG₀closed hWbase
            rcases hWsplit' with hWF | hWG₀
            · exact False.elim (hW_not_subset_F hWF)
            · exact hcodim_from_G₀ hWmax_owner <| by
                simpa [irreducible_closed_subset_pred] using hWG₀
          · have hZT : Z ∈ T := (hT Z).2 ⟨hZmax, hZbase⟩
            let i : {Z // Z ∈ T} := ⟨Z, hZT⟩
            have hz_not_F' : zs i ∉ F' := by
              -- The `zs`-point survives outside the final normalized bad locus as well.
              simpa [B, F', normalized_bad_locus] using
                point_not_mem_closure_diff_of_not_mem_section_dependence_locus
                  (sections := Fin.snoc sections s) (F := F) (x := zs i) (hzs_not_dep i)
            have hz_not_W : zs i ∉ (W : Set Ω) := by
              intro hzW
              exact hz_not_F' (hWmax.1 hzW)
            have hWltZ : W < Z := by
              -- The owner component `Z` contains a marked point outside `W`, so `W` is a proper
              -- subcomponent of `Z`.
              exact strict_lt_of_subset_and_point_not_mem hWZ (hzs_mem i) hz_not_W
            exact succ_le_coheight_of_strictly_smaller_component hWltZ (hcodimH Z hZmax)
      refine ⟨s, F', ?_⟩
      -- The source-faithful splice is now complete: prescribed values hold, the final bad locus is
      -- supported on `F ∪ F'`, and every irreducible component of `F'` gains one codimension step.
      refine ⟨hF'closed, hs_pts, ?_, ?_⟩
      · simpa [B, F', normalized_bad_locus] using hdep_final
      · simpa [Nat.succ_eq_add_one] using hcodimF'
end
