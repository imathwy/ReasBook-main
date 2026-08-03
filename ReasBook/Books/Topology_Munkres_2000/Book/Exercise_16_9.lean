module

public import Topology_Munkres_2000.Book.Exercise_8_99_4.Instances
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Instances.Real.Lemmas

public section

open Prod.Lex

namespace RealPlaneTopology

/-- The dictionary order topology on the real plane, transported to `ℝ × ℝ`. -/
@[reducible] def dictionary : TopologicalSpace (ℝ × ℝ) :=
  TopologicalSpace.induced toLex realProdLexTopologicalSpace

/-- The product of the discrete topology on the first real factor and the standard topology on
the second. -/
@[reducible] def discreteProduct : TopologicalSpace (ℝ × ℝ) :=
  TopologicalSpace.induced Prod.fst ⊥ ⊓
    TopologicalSpace.induced Prod.snd inferInstance

/-- Helper for Exercise 16.9: a lexicographic interval around a point contains an interval
whose endpoints lie in the same vertical fiber. -/
lemma exists_sameFiber_Ioo_subset {p : ℝ × ℝ} {lower upper : ℝ ×ₗ ℝ}
    (hlower : lower < toLex p) (hupper : toLex p < upper) :
    ∃ a b : ℝ, a < p.2 ∧ p.2 < b ∧
      lower < toLex (p.1, a) ∧ toLex (p.1, b) < upper := by
  -- Split each lexicographic comparison according to the first coordinate.
  rw [← toLex_ofLex lower] at hlower
  rw [← toLex_ofLex upper] at hupper
  rcases Prod.Lex.toLex_lt_toLex.mp hlower with hfirst | ⟨hfirst, hsecond⟩
  · obtain ⟨a, ha⟩ := exists_lt p.2
    have hlower' : toLex (ofLex lower) < toLex (p.1, a) := by
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hfirst)
    rcases Prod.Lex.toLex_lt_toLex.mp hupper with hupperFirst | ⟨hupperFirst, hupperSecond⟩
    · obtain ⟨b, hb⟩ := exists_gt p.2
      have hupper' : toLex (p.1, b) < toLex (ofLex upper) := by
        exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hupperFirst)
      exact ⟨a, b, ha, hb, hlower', hupper'⟩
    · obtain ⟨b, hb, hbUpper⟩ := exists_between hupperSecond
      have hupper' : toLex (p.1, b) < toLex (ofLex upper) := by
        exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hupperFirst, hbUpper⟩)
      exact ⟨a, b, ha, hb, hlower', hupper'⟩
  · obtain ⟨a, hlowerSecond, ha⟩ := exists_between hsecond
    have hlower' : toLex (ofLex lower) < toLex (p.1, a) := by
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hfirst, hlowerSecond⟩)
    rcases Prod.Lex.toLex_lt_toLex.mp hupper with hupperFirst | ⟨hupperFirst, hupperSecond⟩
    · obtain ⟨b, hb⟩ := exists_gt p.2
      have hupper' : toLex (p.1, b) < toLex (ofLex upper) := by
        exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hupperFirst)
      exact ⟨a, b, ha, hb, hlower', hupper'⟩
    · obtain ⟨b, hb, hbUpper⟩ := exists_between hupperSecond
      have hupper' : toLex (p.1, b) < toLex (ofLex upper) := by
        exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hupperFirst, hbUpper⟩)
      exact ⟨a, b, ha, hb, hlower', hupper'⟩

/-- Helper for Exercise 16.9: a same-fiber lexicographic interval pulls back to a vertical
open interval. -/
lemma preimage_lexIoo_same_fst (x a b : ℝ) :
    toLex ⁻¹' Set.Ioo (toLex (x, a)) (toLex (x, b)) = ({x} ×ˢ Set.Ioo a b) := by
  -- Expand lexicographic inequalities and rule out incompatible first coordinates.
  ext p
  simp only [Set.mem_preimage, Set.mem_Ioo, Set.mem_prod, Set.mem_singleton_iff,
    Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro ⟨ha, hb⟩
    rcases ha with ha | ⟨hx, ha⟩
    · rcases hb with hb | ⟨hx', hb⟩
      · exact (lt_asymm ha hb).elim
      · rw [hx'] at ha
        exact (lt_irrefl x ha).elim
    · rcases hb with hb | ⟨hx', hb⟩
      · rw [← hx] at hb
        exact (lt_irrefl x hb).elim
      · exact ⟨hx.symm, ha, hb⟩
  · rintro ⟨rfl, ha, hb⟩
    exact ⟨Or.inr ⟨rfl, ha⟩, Or.inr ⟨rfl, hb⟩⟩

/-- Helper for Exercise 16.9: vertical open intervals form a neighborhood basis for the
dictionary topology. -/
lemma dictionary_nhds_basis_verticalIntervals (p : ℝ × ℝ) :
    (@nhds _ dictionary p).HasBasis
      (fun ab : ℝ × ℝ ↦ ab.1 < p.2 ∧ p.2 < ab.2)
      (fun ab ↦ {p.1} ×ˢ Set.Ioo ab.1 ab.2) := by
  -- Pull back the order-topology basis and refine it to same-fiber intervals.
  letI : OrderTopology (ℝ ×ₗ ℝ) := ⟨rfl⟩
  rw [dictionary, nhds_induced]
  refine ((nhds_basis_Ioo (toLex p)).comap toLex).to_hasBasis ?_ ?_
  · rintro ⟨lower, upper⟩ ⟨hlower, hupper⟩
    obtain ⟨a, b, ha, hb, hlower', hupper'⟩ :=
      exists_sameFiber_Ioo_subset hlower hupper
    refine ⟨(a, b), ⟨ha, hb⟩, ?_⟩
    rw [← preimage_lexIoo_same_fst p.1 a b]
    exact Set.preimage_mono (Set.Ioo_subset_Ioo hlower'.le hupper'.le)
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    refine ⟨(toLex (p.1, a), toLex (p.1, b)), ?_, ?_⟩
    · exact ⟨Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, ha⟩),
        Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hb⟩)⟩
    · rw [preimage_lexIoo_same_fst]

/-- Helper for Exercise 16.9: vertical open intervals form a neighborhood basis for the product
with a discrete first factor. -/
lemma discreteProduct_nhds_basis_verticalIntervals (p : ℝ × ℝ) :
    (@nhds _ discreteProduct p).HasBasis
      (fun ab : ℝ × ℝ ↦ ab.1 < p.2 ∧ p.2 < ab.2)
      (fun ab ↦ {p.1} ×ˢ Set.Ioo ab.1 ab.2) := by
  -- Compute the infimum neighborhood filter from the two induced factors.
  change (@nhds _ (TopologicalSpace.induced Prod.fst ⊥ ⊓
    TopologicalSpace.induced Prod.snd inferInstance) p).HasBasis _ _
  rw [@nhds_inf _ (TopologicalSpace.induced Prod.fst ⊥)
    (TopologicalSpace.induced Prod.snd inferInstance) p]
  rw [@nhds_induced ℝ (ℝ × ℝ) ⊥ Prod.fst p]
  rw [@nhds_induced ℝ (ℝ × ℝ) inferInstance Prod.snd p]
  rw [@nhds_discrete ℝ ⊥ (discreteTopology_bot ℝ)]
  refine (((Filter.hasBasis_pure p.1).comap Prod.fst).inf
    ((nhds_basis_Ioo p.2).comap Prod.snd)).to_hasBasis ?_ ?_
  · rintro ⟨x, ⟨a, b⟩⟩ ⟨-, ha, hb⟩
    refine ⟨(a, b), ⟨ha, hb⟩, ?_⟩
    intro q hq
    exact ⟨hq.1, hq.2⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    refine ⟨((), (a, b)), ⟨trivial, ha, hb⟩, ?_⟩
    intro q hq
    exact ⟨hq.1, hq.2⟩

/-- Helper for Exercise 16.9: a vertical fiber is open in `discreteProduct` but not in the
standard product topology. -/
lemma verticalFiber_open_discreteProduct_not_open_standard :
    @IsOpen _ discreteProduct ({(0 : ℝ)} ×ˢ Set.univ) ∧
      ¬ @IsOpen _ (inferInstance : TopologicalSpace (ℝ × ℝ)) ({(0 : ℝ)} ×ˢ Set.univ) := by
  -- The discrete first-coordinate topology makes the fiber open.
  constructor
  · apply TopologicalSpace.le_def.mp inf_le_left
    have hopen : @IsOpen _ (TopologicalSpace.induced Prod.fst ⊥)
        (Prod.fst ⁻¹' ({(0 : ℝ)} : Set ℝ)) :=
      @isOpen_induced (ℝ × ℝ) ℝ ⊥ Prod.fst {(0 : ℝ)}
        (@isOpen_discrete ℝ ⊥ (discreteTopology_bot ℝ) {(0 : ℝ)})
    have hset : (@Prod.fst ℝ ℝ) ⁻¹' ({(0 : ℝ)} : Set ℝ) =
        ({(0 : ℝ)} ×ˢ Set.univ) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_univ, and_true]
    rwa [hset] at hopen
  · intro hopen
    -- Standard product openness would force the real singleton to be open.
    rcases (isOpen_prod_iff'.mp hopen) with hopenFactors | hempty
    · exact not_isOpen_singleton (0 : ℝ) hopenFactors.1
    · rcases hempty with hsingleton | huniv
      · exact Set.singleton_ne_empty 0 hsingleton
      · exact Set.univ_nonempty.ne_empty huniv

/-- Exercise 16.9 (1): The dictionary order topology on `ℝ × ℝ` is the
product of the discrete topology on the first factor and the standard topology on the second
factor. -/
theorem dictionary_eq_discreteProduct : dictionary = discreteProduct := by
  -- The two topologies coincide because their neighborhood filters have the same basis.
  apply TopologicalSpace.ext_nhds
  intro p
  exact (dictionary_nhds_basis_verticalIntervals p).eq_of_same_basis
    (discreteProduct_nhds_basis_verticalIntervals p)

/-- Exercise 16.9 (2): The dictionary order topology on `ℝ × ℝ` is
strictly finer than the standard product topology on `ℝ × ℝ`. -/
theorem dictionary_lt_standardProduct :
    dictionary < (inferInstance : TopologicalSpace (ℝ × ℝ)) := by
  -- Compare after replacing the dictionary topology by the explicit mixed product.
  rw [dictionary_eq_discreteProduct]
  refine lt_of_le_of_ne ?_ ?_
  · exact inf_le_inf (induced_mono bot_le) le_rfl
  · intro heq
    have hopenStandard : @IsOpen _ (inferInstance : TopologicalSpace (ℝ × ℝ))
        ({(0 : ℝ)} ×ˢ Set.univ) := heq ▸ verticalFiber_open_discreteProduct_not_open_standard.1
    exact verticalFiber_open_discreteProduct_not_open_standard.2 hopenStandard


end RealPlaneTopology
