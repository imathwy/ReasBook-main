import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap12.Corollary_12_31
import BauschkeLean.Chap13.GammaZeroConjugate
import BauschkeLean.Chap13.Proposition_13_48
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap15.Definition_15_24_1
import BauschkeLean.Chap15.Proposition_15_24
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap19.Theorem_19_1

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

open ContinuousLinearMap

-- Semantic recall note: `lean_leansearch` only surfaced generic adjoint lemmas here, not the
-- local Chapter 15/16/19 composite-duality owners. The verified project-facing surfaces used in
-- this file are `compositePrimalObjective`, `compositeDualObjective`, `f∗[hf]`, and
-- `adjointImageSubdifferential`.

section CompositeOptimality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Proposition 27.5 (1): every zero of `∂ f + L^* ∘ (∂ g) ∘ L`, realized as
`(∂ f) + adjointImageSubdifferential L g`, is a minimizer of the composite primal objective
`x ↦ f x + g (L x)`. -/
theorem zeros_subdifferential_sum_subset_argmin_compositePrimalObjective
    {f : H → Set.Ioi (⊥ : EReal)}
    {g : K → Set.Ioi (⊥ : EReal)}
    (L : H →L[ℝ] K) :
    ((∂ f) + adjointImageSubdifferential L g).zeros ⊆
      Argmin (compositePrimalObjective f g L) := by
  intro x hx
  have hxzero : x ∈ (∂ (f + g ∘ L)).zeros := by
    rw [SetValuedOperator.mem_zeros_iff] at hx ⊢
    exact subdifferential_add_adjoint_image_subset_subdifferential_add_comp f g L x hx
  have hxarg : x ∈ Argmin ((f + g ∘ L).asEReal) := by
    simpa [argmin_eq_zeros_subdifferential] using hxzero
  simpa [compositePrimalObjective] using hxarg

/-- Helper for Proposition 27.5: swapping `f` and `g` for the conjugate problem rewrites the
composite primal objective into the composite dual objective. -/
lemma compositeDualObjective_eq_swapped_conjugate_compositePrimalObjective
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) :
    compositePrimalObjective (g∗[hg]) (f∗[hf]) (-L.adjoint) = compositeDualObjective f g L := by
  -- Evaluate both owner objectives at a dual point and rewrite the packaged conjugates.
  funext v
  simp [compositePrimalObjective_apply, compositeDualObjective_apply, add_comm]

/-- Proposition 27.5 (2): every zero of `-L ∘ (∂ f^*) ∘ (-L^*) + ∂ g^*`, realized as
`(∂ (g∗[hg])) + adjointImageSubdifferential (-L.adjoint) (f∗[hf])`, is a minimizer of the
composite dual objective `v ↦ f^*(-L^* v) + g^*(v)`. -/
theorem zeros_conjugate_subdifferential_sum_subset_argmin_compositeDualObjective
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K) :
    ((∂ (g∗[hg])) + adjointImageSubdifferential (-L.adjoint) (f∗[hf])).zeros ⊆
      Argmin (compositeDualObjective f g L) := by
  -- Reuse the primal inclusion on the conjugate-swapped problem and then normalize the objective.
  simpa [compositeDualObjective_eq_swapped_conjugate_compositePrimalObjective (hf := hf)
    (hg := hg) (L := L)] using
    (zeros_subdifferential_sum_subset_argmin_compositePrimalObjective
      (f := g∗[hg]) (g := f∗[hf]) (-L.adjoint))

/-- The four textbook regularity alternatives used to identify the minimizers of
`compositePrimalObjective f g L` with the zeros of `∂ f + L^* ∘ (∂ g) ∘ L`. -/
inductive CompositePrimalObjectiveRegularity
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) : Prop where
  | zero_mem_sri
      (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
      CompositePrimalObjectiveRegularity f g L
  | finiteDimensional_ri
      (hfin : FiniteDimensional ℝ K)
      (hri : (ri (effectiveDomain g) ∩ ri (L '' effectiveDomain f)).Nonempty) :
      CompositePrimalObjectiveRegularity f g L
  | polyhedral_finiteDimensional_ri
      (hfin : FiniteDimensional ℝ K)
      (hpoly : Polyhedral g.asEReal)
      (hri : (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty) :
      CompositePrimalObjectiveRegularity f g L
  | polyhedral_finiteDimensional
      (hfinH : FiniteDimensional ℝ H)
      (hfinK : FiniteDimensional ℝ K)
      (hpolyf : Polyhedral f.asEReal)
      (hpolyg : Polyhedral g.asEReal)
      (hnonempty : (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) :
      CompositePrimalObjectiveRegularity f g L

private theorem CompositePrimalObjectiveRegularity.toSriOrPolyhedralRegularity
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    {L : H →L[ℝ] K}
    (hregular : CompositePrimalObjectiveRegularity f g L) :
    (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) ∨
      (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
        (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty) ∨
      (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
        FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
        (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty) := by
  cases hregular with
  | zero_mem_sri hsri =>
      exact Or.inl hsri
  | finiteDimensional_ri hfin hri =>
      have hregular15 : effectiveDomainSubImageStrongRelativeInteriorRegularity f g L := by
        rw [effectiveDomainSubImageStrongRelativeInteriorRegularity]
        exact
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
            Or.inl ⟨hfin, hri⟩
      exact
        Or.inl <|
          zero_mem_strongRelativeInterior_sub_image_effectiveDomain_of_regularity hf hg L hregular15
  | polyhedral_finiteDimensional_ri hfin hpoly hri =>
      exact Or.inr <| Or.inl ⟨hfin, hpoly, hri⟩
  | polyhedral_finiteDimensional hfinH hfinK hpolyf hpolyg hnonempty =>
      exact Or.inr <| Or.inr <| ⟨hfinK, hpolyg, hfinH, hpolyf, hnonempty⟩

/-- Every Chapter 27 regularity case supplies a point in
`L (effectiveDomain f) ∩ effectiveDomain g`. -/
theorem CompositePrimalObjectiveRegularity.image_inter_effectiveDomain_nonempty
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    {L : H →L[ℝ] K}
    (hregular : CompositePrimalObjectiveRegularity f g L) :
    (L '' effectiveDomain f ∩ effectiveDomain g).Nonempty := by
  rcases hregular.toSriOrPolyhedralRegularity hf hg with hsri | hpoly | hpoly
  · rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
    rcases Set.mem_sub.mp hzero with ⟨y, hy, z, hz, hyz⟩
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨L x, ⟨x, hx, rfl⟩, ?_⟩
    simpa [sub_eq_zero.mp hyz] using hy
  · rcases hpoly with ⟨_, _, ⟨y, hy, hyri⟩⟩
    exact ⟨y, (Set.mem_relativeInterior_iff.mp hyri).1, hy⟩
  · rcases hpoly with ⟨_, _, _, _, ⟨y, hy, hyImage⟩⟩
    exact ⟨y, hyImage, hy⟩

/-- Helper for Proposition 27.5: the same chapter regularity cases also give the range-based
intersection `Set.range L ∩ effectiveDomain g ≠ ∅` used by the Chapter 13/15 exactness owners. -/
theorem CompositePrimalObjectiveRegularity.range_inter_effectiveDomain_nonempty
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    {L : H →L[ℝ] K}
    (hregular : CompositePrimalObjectiveRegularity f g L) :
    (Set.range L ∩ effectiveDomain g).Nonempty := by
  -- First reuse the stronger image-based witness already extracted from the regularity split.
  rcases CompositePrimalObjectiveRegularity.image_inter_effectiveDomain_nonempty
      (hf := hf) (hg := hg) hregular with ⟨y, hyImage, hyg⟩
  rcases hyImage with ⟨x, _, rfl⟩
  -- Then forget the domain witness and package the same point as a range witness for `L`.
  exact ⟨L x, ⟨x, rfl⟩, hyg⟩

/-- Helper for Proposition 27.5: once the pointwise dual minimizer for `(f, g ∘ L)` is known and
the Chapter 13 composition-conjugation bridge is fixed, exactness of the adjoint infimal
postcomposition lifts that minimizing point to the composite dual problem. -/
theorem exists_mem_argmin_compositeDualObjective_of_mem_argmin_pointwiseDualObjective_and_exact_postcomposition_local
    {f : H → Set.Ioi (⊥ : EReal)}
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hcompconj : (g.asEReal ∘ L)∗ = L.adjoint ▷ g.asEReal∗)
    (hexact : infimalPostcomposition.Exact L.adjoint (g∗[hg]))
    {u : H}
    (huDom : u ∈ dom ((g.asEReal ∘ L)∗))
    (huArg :
      u ∈ Argmin (fun z : H ↦ f.asEReal∗ (-z) + ((g.asEReal ∘ L)∗ z)))
    (hvalue :
      compositePrimalOptimalValue f g L =
        -(f.asEReal∗ (-u) + ((g.asEReal ∘ L)∗ u))) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := by
  let pointwiseDualObjective : H → EReal :=
    fun z ↦ f.asEReal∗ (-z) + ((g.asEReal ∘ L)∗ z)
  have huDom' : u ∈ dom (L.adjoint ▷ g.asEReal∗) := by
    -- Rewrite the composite conjugate once so the exactness hypothesis applies to the same owner.
    simpa [hcompconj] using huDom
  have huExact : infimalPostcomposition.ExactAt L.adjoint (g∗[hg]) u := hexact huDom'
  rcases (infimalPostcomposition.exactAt_iff_exists_eq L.adjoint (g∗[hg]) u).1 huExact with
    ⟨_, v, hLv, hvExact⟩
  have hvPost :
      ((g.asEReal ∘ L)∗ u) = g.asEReal∗ v := by
    -- Exactness identifies the composite conjugate value with the chosen dual fiber value.
    calc
      ((g.asEReal ∘ L)∗ u) = (L.adjoint ▷ g.asEReal∗) u := by
        rw [hcompconj]
      _ = g.asEReal∗ v := by
        simpa [gammaZeroConjugate_apply] using hvExact
  have hvPointwise :
      pointwiseDualObjective u = compositeDualObjective f g L v := by
    -- The exact postcomposition witness turns the pointwise objective into the composite dual one.
    calc
      pointwiseDualObjective u = f.asEReal∗ (-u) + ((g.asEReal ∘ L)∗ u) := rfl
      _ = f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v := by rw [hLv, hvPost]
      _ = compositeDualObjective f g L v := by
        rw [compositeDualObjective_apply]
  have hvArg : v ∈ Argmin (compositeDualObjective f g L) := by
    rw [mem_argmin_iff, isMinOn_univ_iff]
    intro w
    have hwFiber :
        (L.adjoint ▷ g.asEReal∗) (L.adjoint w) ≤ g.asEReal∗ w := by
      -- The comparison point `w` belongs to the adjoint fiber over `L.adjoint w`.
      change
        sInf (g.asEReal∗ '' ((L.adjoint) ⁻¹' ({L.adjoint w} : Set H))) ≤ g.asEReal∗ w
      exact sInf_le ⟨w, by simp, rfl⟩
    have hwPost :
        ((g.asEReal ∘ L)∗ (L.adjoint w)) ≤ g.asEReal∗ w := by
      -- Push the fiber inequality back through the composition-conjugation identity.
      rw [hcompconj]
      exact hwFiber
    have huMin : ∀ z : H, pointwiseDualObjective u ≤ pointwiseDualObjective z := by
      exact isMinOn_univ_iff.mp ((mem_argmin_iff).1 huArg)
    have huw :
        pointwiseDualObjective u ≤ pointwiseDualObjective (L.adjoint w) :=
      huMin (L.adjoint w)
    calc
      compositeDualObjective f g L v = pointwiseDualObjective u := hvPointwise.symm
      _ ≤ pointwiseDualObjective (L.adjoint w) := huw
      _ = f.asEReal∗ (-(L.adjoint w)) + ((g.asEReal ∘ L)∗ (L.adjoint w)) := rfl
      _ ≤ f.asEReal∗ (-(L.adjoint w)) + g.asEReal∗ w := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hwPost (f.asEReal∗ (-(L.adjoint w)))
      _ = compositeDualObjective f g L w := by
        rw [compositeDualObjective_apply]
  refine ⟨v, hvArg, ?_⟩
  -- Replace the minimizing pointwise value by the attained composite dual value.
  calc
    compositePrimalOptimalValue f g L =
        -(f.asEReal∗ (-u) + ((g.asEReal ∘ L)∗ u)) := hvalue
    _ = -(compositeDualObjective f g L v) := by rw [← hvPointwise]

/-- Helper for Proposition 27.5: the range-domain hypothesis should identify the conjugate of
`g ∘ L` with the adjoint infimal postcomposition `L.adjoint ▷ g∗`. -/
lemma conjugate_comp_eq_adjointInfimalPostcomposition_of_range_inter_effectiveDomain_nonempty_local
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hdom : (Set.range L ∩ effectiveDomain g).Nonempty) :
    (g.asEReal ∘ L)∗ = L.adjoint ▷ g.asEReal∗ := by
  let _ := hg
  let _ := hdom
  -- TODO: port the missing public owner `conjugate_comp_eq_adjointInfimalPostcomposition`.
  -- Direct reuse from downstream Chapter 15/16 files is blocked in this checkout because the
  -- required `.olean` chain is incomplete.
  sorry

/-- Helper for Proposition 27.5: a minimizing dual point evaluates the composite dual objective
at the canonical dual optimal value. -/
lemma compositeDualObjective_eq_compositeDualOptimalValue_of_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)}
    {g : K → Set.Ioi (⊥ : EReal)}
    {L : H →L[ℝ] K}
    {v : K}
    (hvArg : v ∈ Argmin (compositeDualObjective f g L)) :
    compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
  -- `Argmin` rewrites the attained dual value to the owner infimum by definition.
  simpa [compositeDualOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hvArg)

/-- Helper for Proposition 27.5: the source polyhedral regularity split should force exactness of
the adjoint infimal postcomposition attached to `g`. -/
lemma exact_adjointInfimalPostcomposition_of_polyhedralRegularity_local
    {f : H → Set.Ioi (⊥ : EReal)}
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    [FiniteDimensional ℝ K] (hgPoly : Polyhedral g.asEReal)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    infimalPostcomposition.Exact L.adjoint (g∗[hg]) := by
  let _ := hg
  let _ := hgPoly
  let _ := hregular
  -- TODO: replace this local placeholder with a direct call to
  -- `infimalPostcomposition_adjoint_conjugate_exact_of_regular` once the Chapter 15
  -- `Theorem_15_27`/`Corollary_15_28` owner chain is available in this checkout.
  sorry

/-- Helper for Proposition 27.5: the source polyhedral regularity split should first attain the
ordinary dual problem for the pair `(f, g ∘ L)`. -/
lemma exists_mem_argmin_pointwiseDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedralRegularity_local
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    [FiniteDimensional ℝ K] (hgPoly : Polyhedral g.asEReal)
    (hregular :
      (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty ∨
        (FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
          (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    ∃ u, u ∈ dom ((g.asEReal ∘ L)∗) ∧
      u ∈ Argmin (fun z : H ↦ f.asEReal∗ (-z) + ((g.asEReal ∘ L)∗ z)) ∧
        compositePrimalOptimalValue f g L =
          -(f.asEReal∗ (-u) + ((g.asEReal ∘ L)∗ u)) := by
  let _ := hf
  let _ := hg
  let _ := hgPoly
  let _ := hregular
  -- TODO: replace this local placeholder with the public Chapter 15 attainment theorem for the
  -- ordinary dual problem once the corresponding owner `.olean` chain is buildable.
  sorry

/-- Helper for Proposition 27.5: the polyhedral regularity alternatives yield a dual minimizer
with the strong-duality identity needed by Theorem 19.1. -/
lemma exists_mem_argmin_compositeDualObjective_and_strongDuality_of_polyhedralRegularity
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    {L : H →L[ℝ] K}
    (hregular :
      (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
        (effectiveDomain g ∩ ri (L '' effectiveDomain f)).Nonempty) ∨
      (FiniteDimensional ℝ K ∧ Polyhedral g.asEReal ∧
        FiniteDimensional ℝ H ∧ Polyhedral f.asEReal ∧
        (effectiveDomain g ∩ L '' effectiveDomain f).Nonempty)) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
  -- Route correction: the intended proof is a thin wrapper around the public Chapter 15
  -- dual-attainment theorem, but that owner import currently fails to build in this checkout, so
  -- the remaining frontier stays localized in the exactness/ordinary-dual helper placeholders.
  rcases hregular with hri | hpoly
  · rcases hri with ⟨hfinK, hgPoly, hnonempty⟩
    letI : FiniteDimensional ℝ K := hfinK
    have hchapterRegularity : CompositePrimalObjectiveRegularity f g L :=
      .polyhedral_finiteDimensional_ri hfinK hgPoly hnonempty
    have hrange :
        (Set.range L ∩ effectiveDomain g).Nonempty :=
      CompositePrimalObjectiveRegularity.range_inter_effectiveDomain_nonempty
        (hf := hf) (hg := hg) hchapterRegularity
    have hcompconj :
        (g.asEReal ∘ L)∗ = L.adjoint ▷ g.asEReal∗ :=
      conjugate_comp_eq_adjointInfimalPostcomposition_of_range_inter_effectiveDomain_nonempty_local
        (hg := hg) (L := L) hrange
    have hexact :
        infimalPostcomposition.Exact L.adjoint (g∗[hg]) :=
      exact_adjointInfimalPostcomposition_of_polyhedralRegularity_local
        (hg := hg) (L := L) (hgPoly := hgPoly) (hregular := Or.inl hnonempty)
    obtain ⟨u, huDom, huArg, huValue⟩ :=
      exists_mem_argmin_pointwiseDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedralRegularity_local
        (hf := hf) (hg := hg) (L := L) (hgPoly := hgPoly) (hregular := Or.inl hnonempty)
    obtain ⟨v, hvArg, hvValue⟩ :=
      exists_mem_argmin_compositeDualObjective_of_mem_argmin_pointwiseDualObjective_and_exact_postcomposition_local
        (hg := hg) (L := L) hcompconj hexact huDom huArg huValue
    have hvOptimal :
        compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
      -- The minimizing dual point rewrites its attained value to the owner dual optimum.
      exact compositeDualObjective_eq_compositeDualOptimalValue_of_mem_argmin hvArg
    refine ⟨v, hvArg, ?_⟩
    calc
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := hvValue
      _ = -compositeDualOptimalValue f g L := by rw [hvOptimal]
  · rcases hpoly with ⟨hfinK, hgPoly, hfinH, hfPoly, hnonempty⟩
    letI : FiniteDimensional ℝ K := hfinK
    letI : FiniteDimensional ℝ H := hfinH
    have hchapterRegularity : CompositePrimalObjectiveRegularity f g L :=
      .polyhedral_finiteDimensional hfinH hfinK hfPoly hgPoly hnonempty
    have hrange :
        (Set.range L ∩ effectiveDomain g).Nonempty :=
      CompositePrimalObjectiveRegularity.range_inter_effectiveDomain_nonempty
        (hf := hf) (hg := hg) hchapterRegularity
    have hcompconj :
        (g.asEReal ∘ L)∗ = L.adjoint ▷ g.asEReal∗ :=
      conjugate_comp_eq_adjointInfimalPostcomposition_of_range_inter_effectiveDomain_nonempty_local
        (hg := hg) (L := L) hrange
    have hexact :
        infimalPostcomposition.Exact L.adjoint (g∗[hg]) :=
      exact_adjointInfimalPostcomposition_of_polyhedralRegularity_local
        (hg := hg) (L := L) (hgPoly := hgPoly)
        (hregular := Or.inr ⟨hfinH, hfPoly, hnonempty⟩)
    obtain ⟨u, huDom, huArg, huValue⟩ :=
      exists_mem_argmin_pointwiseDualObjective_eq_neg_compositePrimalOptimalValue_of_polyhedralRegularity_local
        (hf := hf) (hg := hg) (L := L) (hgPoly := hgPoly)
        (hregular := Or.inr ⟨hfinH, hfPoly, hnonempty⟩)
    obtain ⟨v, hvArg, hvValue⟩ :=
      exists_mem_argmin_compositeDualObjective_of_mem_argmin_pointwiseDualObjective_and_exact_postcomposition_local
        (hg := hg) (L := L) hcompconj hexact huDom huArg huValue
    have hvOptimal :
        compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
      -- The minimizing dual point rewrites its attained value to the owner dual optimum.
      exact compositeDualObjective_eq_compositeDualOptimalValue_of_mem_argmin hvArg
    refine ⟨v, hvArg, ?_⟩
    calc
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := hvValue
      _ = -compositeDualOptimalValue f g L := by rw [hvOptimal]

/-- Helper for Proposition 27.5: the `sri` regularity branch already provides a dual minimizer
and the strong-duality identity needed by Theorem 19.1. -/
lemma exists_mem_argmin_compositeDualObjective_and_strongDuality_of_zero_mem_sri_sub_image_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
  let _ := hf
  let _ := hg
  let _ := hsri
  -- TODO: replace this local placeholder with a direct call to
  -- `exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain`
  -- once the Chapter 15 `Theorem_15_23` owner compiles in this workspace.
  sorry

/-- Helper for Proposition 27.5: every chapter regularity branch produces the same dual
certificate shape for the composite primal problem. -/
lemma exists_mem_argmin_compositeDualObjective_and_strongDuality_of_regular
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hregular : CompositePrimalObjectiveRegularity f g L) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
  -- Split the wrapper once, then normalize each branch to the same certificate output.
  rcases hregular.toSriOrPolyhedralRegularity hf hg with hsri | hpoly | hpoly
  · exact
      exists_mem_argmin_compositeDualObjective_and_strongDuality_of_zero_mem_sri_sub_image_effectiveDomain
        (hf := hf) (hg := hg) (L := L) hsri
  · exact
      exists_mem_argmin_compositeDualObjective_and_strongDuality_of_polyhedralRegularity
        (hf := hf) (hg := hg) (hregular := Or.inl hpoly)
  · exact
      exists_mem_argmin_compositeDualObjective_and_strongDuality_of_polyhedralRegularity
        (hf := hf) (hg := hg) (hregular := Or.inr hpoly)

/-- Helper for Proposition 27.5: a primal minimizer is already a zero of
`(∂ f) + adjointImageSubdifferential L g` once a dual minimizer realizes strong duality. -/
lemma mem_zeros_subdifferential_sum_of_mem_argmin_compositePrimalObjective_of_dual_certificate
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    {v : K}
    (hvArg : v ∈ Argmin (compositeDualObjective f g L))
    (hstrong : compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L)
    {x : H}
    (hx : x ∈ Argmin (compositePrimalObjective f g L)) :
    x ∈ ((∂ f) + adjointImageSubdifferential L g).zeros := by
  have hxValue :
      compositePrimalObjective f g L x = compositePrimalOptimalValue f g L := by
    simpa [compositePrimalOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hx)
  have hvValue :
      compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
    -- The dual certificate attains the canonical dual optimal value.
    exact compositeDualObjective_eq_compositeDualOptimalValue_of_mem_argmin hvArg
  have hcontact :
      compositePrimalObjective f g L x = -compositeDualObjective f g L v := by
    calc
      compositePrimalObjective f g L x = compositePrimalOptimalValue f g L := hxValue
      _ = -compositeDualOptimalValue f g L := hstrong
      _ = -compositeDualObjective f g L v := by rw [hvValue]
  have hzeroGap :
      ((f x : EReal) + (g (L x) : EReal)) +
          (f.asEReal∗ (-(L.adjoint v)) + g.asEReal∗ v) = 0 := by
    exact (composite_contact_eq_iff_zero_gap hf hg L x v).mp hcontact
  have hsubgrad :
      -L.adjoint v ∈ (∂ f) x ∧
        v ∈ (∂ g) (L x) := by
    exact (composite_fenchel_young_zero_iff_subgradient_pair hf hg L x v).mp hzeroGap
  rw [SetValuedOperator.mem_zeros_iff]
  -- The dual witness gives opposite subgradients for the two summands, so they sum to zero.
  refine ⟨-L.adjoint v, hsubgrad.1, L.adjoint v, ?_, by simp⟩
  rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
  exact ⟨v, hsubgrad.2, rfl⟩

/-- Helper for Proposition 27.5: under the chapter regularity wrapper, every primal minimizer is
already a zero of `(∂ f) + adjointImageSubdifferential L g`. -/
lemma mem_zeros_subdifferential_sum_of_mem_argmin_compositePrimalObjective_of_regular
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hregular : CompositePrimalObjectiveRegularity f g L)
    {x : H}
    (hx : x ∈ Argmin (compositePrimalObjective f g L)) :
    x ∈ ((∂ f) + adjointImageSubdifferential L g).zeros := by
  obtain ⟨v, hvArg, hstrong⟩ :=
    exists_mem_argmin_compositeDualObjective_and_strongDuality_of_regular
      (hf := hf) (hg := hg) (L := L) hregular
  -- Every regularity branch now closes through the same Chapter 19 primal-dual optimality bridge.
  exact
    mem_zeros_subdifferential_sum_of_mem_argmin_compositePrimalObjective_of_dual_certificate
      (hf := hf) (hg := hg) (L := L) hvArg hstrong hx

/-- Proposition 27.5 (3): under any of the source regularity hypotheses `(1)` through `(4)`, the
primal minimizer set equals the zero set of `∂ f + L^* ∘ (∂ g) ∘ L`. A separate nonemptiness
assumption then yields the common-set nonemptiness companion below. -/
theorem argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_regular
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hregular : CompositePrimalObjectiveRegularity f g L) :
    Argmin (compositePrimalObjective f g L) =
      ((∂ f) + adjointImageSubdifferential L g).zeros := by
  apply Set.Subset.antisymm
  · intro x hx
    exact
      mem_zeros_subdifferential_sum_of_mem_argmin_compositePrimalObjective_of_regular
        (hf := hf) (hg := hg) (L := L) hregular hx
  · exact
      zeros_subdifferential_sum_subset_argmin_compositePrimalObjective
        (f := f) (g := g) L

/-- Helper for Proposition 27.5: a common minimizer of `f` and `g ∘ L` is a zero of
`(∂ f) + adjointImageSubdifferential L g`. -/
lemma mem_zeros_subdifferential_sum_of_mem_argmin_inter_preimage_argmin
    {f : H → Set.Ioi (⊥ : EReal)}
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - Set.range L))
    {x : H}
    (hx : x ∈ Argmin f.asEReal ∩ L ⁻¹' Argmin g.asEReal) :
    x ∈ ((∂ f) + adjointImageSubdifferential L g).zeros := by
  let _ := hg
  let _ := hsri
  rw [SetValuedOperator.mem_zeros_iff]
  rcases hx with ⟨hxf, hxg⟩
  have hxzero_f : (0 : H) ∈ (∂ f) x := by
    simpa [argmin_eq_zeros_subdifferential f, SetValuedOperator.mem_zeros_iff] using hxf
  have hxzero_g : (0 : K) ∈ (∂ g) (L x) := by
    simpa [argmin_eq_zeros_subdifferential g, SetValuedOperator.mem_zeros_iff] using hxg
  -- A zero subgradient for both terms gives a zero element in their Minkowski sum.
  refine ⟨0, hxzero_f, 0, ?_, by simp⟩
  rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
  exact ⟨0, hxzero_g, by simp⟩

/-- Under the hypotheses of Proposition 27.5 (3), the zero set of
`(∂ f) + adjointImageSubdifferential L g` is nonempty. -/
theorem zeros_subdifferential_sum_nonempty_of_nonempty_argmin_and_regular
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hargmin : (Argmin (compositePrimalObjective f g L)).Nonempty)
    (hregular : CompositePrimalObjectiveRegularity f g L) :
    (((∂ f) + adjointImageSubdifferential L g).zeros).Nonempty := by
  rw [← argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_regular
    hf hg L hregular]
  exact hargmin

/-- Proposition 27.5 (4): if every primal minimizer is simultaneously a minimizer of `f` and of
`g ∘ L`, if such simultaneous minimizers exist, and if `0 ∈ sri (dom g - ran L)`, then the
primal minimizer set equals the zero set of `∂ f + L^* ∘ (∂ g) ∘ L` and is nonempty. -/
theorem argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_separate_minimizers
    {f : H → Set.Ioi (⊥ : EReal)} (_hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsubset :
      Argmin (compositePrimalObjective f g L) ⊆
        Argmin f.asEReal ∩ L ⁻¹' (Argmin g.asEReal))
    (hnonempty :
      (Argmin f.asEReal ∩ L ⁻¹' (Argmin g.asEReal)).Nonempty)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - Set.range L)) :
    Argmin (compositePrimalObjective f g L) =
        ((∂ f) + adjointImageSubdifferential L g).zeros ∧
      (Argmin (compositePrimalObjective f g L)).Nonempty := by
  have hforward :
      Argmin (compositePrimalObjective f g L) ⊆
        ((∂ f) + adjointImageSubdifferential L g).zeros := by
    intro x hx
    -- The assumed common-minimizer inclusion reduces the forward direction to the local helper.
    exact
      mem_zeros_subdifferential_sum_of_mem_argmin_inter_preimage_argmin
        (hg := hg) (L := L) hsri (hsubset hx)
  have hbackward :
      ((∂ f) + adjointImageSubdifferential L g).zeros ⊆
        Argmin (compositePrimalObjective f g L) :=
    zeros_subdifferential_sum_subset_argmin_compositePrimalObjective (f := f) (g := g) L
  have heq :
      Argmin (compositePrimalObjective f g L) =
        ((∂ f) + adjointImageSubdifferential L g).zeros :=
    Set.Subset.antisymm hforward hbackward
  have hzeros_nonempty :
      (((∂ f) + adjointImageSubdifferential L g).zeros).Nonempty := by
    rcases hnonempty with ⟨x, hx⟩
    exact ⟨x, mem_zeros_subdifferential_sum_of_mem_argmin_inter_preimage_argmin
      (hg := hg) (L := L) hsri hx⟩
  -- Equality with the zero set transfers nonemptiness back to the primal argmin set.
  refine ⟨heq, ?_⟩
  simpa [heq] using hzeros_nonempty

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Proposition 27.5: the indicator composite objective is exactly the indicator of the
feasible set `C ∩ L ⁻¹' D`. -/
lemma compositePrimalObjective_indicator_indicator_eq_indicator_feasibleSet
    (C : Set H) (D : Set K) (L : H →L[ℝ] K) :
    compositePrimalObjective (ι[C]) (ι[D]) L = (ι[C ∩ L ⁻¹' D]).asEReal := by
  -- Split on feasibility and rewrite both indicators pointwise.
  funext x
  by_cases hxC : x ∈ C
  · by_cases hxD : L x ∈ D
    · simp [compositePrimalObjective_apply, indicator_apply, hxC, hxD]
    · simp [compositePrimalObjective_apply, indicator_apply, hxC, hxD]
  · have hleft : compositePrimalObjective (ι[C]) (ι[D]) L x = ⊤ := by
      have hxTop : ((ι[C]) x : EReal) = ⊤ := by
        simp [indicator_apply, hxC]
      rw [compositePrimalObjective_apply, hxTop, EReal.top_add_of_ne_bot]
      exact ne_of_gt (((ι[D]) (L x)).2)
    have hright : ((ι[C ∩ L ⁻¹' D]).asEReal x) = ⊤ := by
      simp [indicator_apply, hxC]
    rw [hleft, hright]

/-- Helper for Proposition 27.5: the minimizers of a nonempty indicator are exactly the underlying
set. -/
lemma argmin_indicator_eq_set_of_nonempty
    {X : Type*} (S : Set X) (hS : S.Nonempty) :
    Argmin ((ι[S]).asEReal) = S := by
  ext x
  constructor
  · intro hx
    rw [mem_argmin_iff, isMinOn_univ_iff] at hx
    -- Comparing with a feasible witness excludes the case `x ∉ S`.
    by_contra hxS
    rcases hS with ⟨y, hy⟩
    simpa [indicator_apply, hxS, hy] using hx y
  · intro hxS
    rw [mem_argmin_iff, isMinOn_univ_iff]
    -- On feasible points the indicator is `0`, and every other value is at least `0`.
    intro y
    by_cases hy : y ∈ S <;> simp [indicator_apply, hxS, hy]

/-- Proposition 27.5 (5): if `C ⊆ H` and `D ⊆ K` are closed convex sets with
`C ∩ L⁻¹(D) ≠ ∅` and `0 ∈ sri (D - ran L)`, then for the indicator specialization
`f = ι[C]` and `g = ι[D]` the primal minimizer set equals the zero set of
`∂ (ι[C]) + L^* ∘ (∂ (ι[D])) ∘ L` and is nonempty. -/
theorem argmin_compositeIndicatorObjective_eq_zeros_subdifferential_sum_of_feasibility
    (C : Set H) (D : Set K)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (L : H →L[ℝ] K)
    (hfeasible : (C ∩ L ⁻¹' D).Nonempty)
    (hsri : (0 : K) ∈ sri (D - Set.range L)) :
    Argmin (compositePrimalObjective (ι[C]) (ι[D]) L) =
        ((∂ (ι[C])) + adjointImageSubdifferential L (ι[D])).zeros ∧
      (Argmin (compositePrimalObjective (ι[C]) (ι[D]) L)).Nonempty := by
  rcases hfeasible with ⟨x, hxC, hxD⟩
  have hC_nonempty : C.Nonempty := ⟨x, hxC⟩
  have hD_nonempty : D.Nonempty := ⟨L x, hxD⟩
  have hC_gamma : (ι[C]) ∈ Γ₀(H) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  have hD_gamma : (ι[D]) ∈ Γ₀(K) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hD_nonempty hD_closed hD_convex
  have hargminC : Argmin ((ι[C]).asEReal) = C :=
    argmin_indicator_eq_set_of_nonempty C hC_nonempty
  have hargminD : Argmin ((ι[D]).asEReal) = D :=
    argmin_indicator_eq_set_of_nonempty D hD_nonempty
  have hargminFeasible :
      Argmin (compositePrimalObjective (ι[C]) (ι[D]) L) = C ∩ L ⁻¹' D := by
    -- Rewrite the composite indicator objective as the feasible-set indicator.
    rw [compositePrimalObjective_indicator_indicator_eq_indicator_feasibleSet]
    exact argmin_indicator_eq_set_of_nonempty (C ∩ L ⁻¹' D) ⟨x, hxC, hxD⟩
  have hsubset :
      Argmin (compositePrimalObjective (ι[C]) (ι[D]) L) ⊆
        Argmin (ι[C]).asEReal ∩ L ⁻¹' Argmin (ι[D]).asEReal := by
    intro y hy
    have hyFeasible : y ∈ C ∩ L ⁻¹' D := by
      simpa [hargminFeasible] using hy
    refine ⟨?_, ?_⟩
    · simpa [hargminC] using hyFeasible.1
    · simpa [hargminD] using hyFeasible.2
  have hnonempty :
      (Argmin (ι[C]).asEReal ∩ L ⁻¹' Argmin (ι[D]).asEReal).Nonempty := by
    refine ⟨x, ?_, ?_⟩
    · simpa [hargminC] using hxC
    · simpa [hargminD] using hxD
  have hsri_indicator : (0 : K) ∈ sri (effectiveDomain (ι[D]) - Set.range L) := by
    simpa [effectiveDomain_indicator] using hsri
  -- Apply the separate-minimizer branch to the indicator specialization.
  simpa [effectiveDomain_indicator] using
    (argmin_compositePrimalObjective_eq_zeros_subdifferential_sum_of_separate_minimizers
      (f := ι[C]) (_hf := hC_gamma) (g := ι[D]) (hg := hD_gamma)
      (L := L) hsubset hnonempty hsri_indicator)

end CompositeOptimality

end ERealFunction
