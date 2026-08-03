module

public import Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
import all Topology_Munkres_2000.Book.Lemma_55_1.Inclusions
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Topology_Munkres_2000.Book.Theorem_70_1

public section

universe u

/-- The least normal subgroup of `π₁(U, x₀)` containing the image under the left
intersection inclusion of the kernel of the right intersection inclusion. -/
noncomputable abbrev intersectionKernelNormalClosure {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    Subgroup (FundamentalGroup U ⟨x₀, hx₀.1⟩) :=
  let i₁ : FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩ →*
      FundamentalGroup U ⟨x₀, hx₀.1⟩ :=
    FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩
  let i₂ : FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩ →*
      FundamentalGroup V ⟨x₀, hx₀.2⟩ :=
    FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩
  Subgroup.normalClosure ((i₂.ker.map i₁ : Subgroup _) : Set _)

/-- Helper for Exercise 70.2: inclusion through a subspace induces the same
fundamental-group homomorphism as direct inclusion into the ambient space. -/
private lemma FundamentalGroup.mapOfSubtype_comp_mapOfSubset
    {X : Type u} [TopologicalSpace X] {A U : Set X}
    (hAU : A ⊆ U) (a : A) :
    (FundamentalGroup.mapOfSubtype U ⟨a, hAU a.property⟩).comp
        (FundamentalGroup.mapOfSubset hAU a) =
      FundamentalGroup.mapOfSubtype A a := by
  -- Expose the two inclusion maps, then use functoriality on each loop class.
  ext q
  simp only [MonoidHom.comp_apply]
  rw [FundamentalGroup.mapOfSubset_eq_map_inclusion]
  unfold FundamentalGroup.mapOfSubtype
  rw [FundamentalGroup.map_apply]
  exact (Path.Homotopic.Quotient.map_comp
    (p := q) (f := ContinuousMap.inclusion hAU)
    (g := (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))).symm

/-- The normal closure of the image of the right inclusion kernel is killed by the
inclusion-induced map from `π₁(U, x₀)` to `π₁(X, x₀)`. -/
theorem intersectionKernelNormalClosure_le_inclusionKer
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    intersectionKernelNormalClosure U V x₀ hx₀ ≤
      (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩).ker := by
  -- It suffices to show that every mapped kernel generator is killed in `X`.
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨g, hg, rfl⟩
  apply MonoidHom.mem_ker.mpr
  -- Both routes from the intersection to `X` are the direct inclusion map.
  have hleft := FundamentalGroup.mapOfSubtype_comp_mapOfSubset
    Set.inter_subset_left ⟨x₀, hx₀⟩
  have hright := FundamentalGroup.mapOfSubtype_comp_mapOfSubset
    Set.inter_subset_right ⟨x₀, hx₀⟩
  have hcommutes := DFunLike.congr_fun (hleft.trans hright.symm) g
  have hrightValue :
      FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩ g = 1 :=
    MonoidHom.mem_ker.mp hg
  simpa only [MonoidHom.comp_apply, hrightValue, map_one] using hcommutes

/-- Surjectivity of the right intersection inclusion implies surjectivity of the
inclusion-induced map from `π₁(U, x₀)` to `π₁(X, x₀)`. -/
theorem fundamentalGroupInclusion_surjective {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (hi₂ : Function.Surjective
      (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩)) :
    Function.Surjective (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩) := by
  let i₁ := FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩
  let i₂ := FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩
  let j₁ := FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩
  let j₂ := FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩
  have hi₂' : Function.Surjective i₂ := by
    simpa only [i₂] using hi₂
  have hleft : j₁.comp i₁ =
      FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ := by
    simpa only [i₁, j₁] using
      FundamentalGroup.mapOfSubtype_comp_mapOfSubset
        Set.inter_subset_left ⟨x₀, hx₀⟩
  have hright : j₂.comp i₂ =
      FundamentalGroup.mapOfSubtype (U ∩ V) ⟨x₀, hx₀⟩ := by
    simpa only [i₂, j₂] using
      FundamentalGroup.mapOfSubtype_comp_mapOfSubset
        Set.inter_subset_right ⟨x₀, hx₀⟩
  -- Surjectivity of `i₂` places the entire range of `j₂` inside that of `j₁`.
  have hrightRange : MonoidHom.range j₂ ≤ MonoidHom.range j₁ := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨g, rfl⟩ := hi₂' v
    refine ⟨i₁ g, ?_⟩
    have hleftValue := DFunLike.congr_fun hleft g
    have hrightValue := DFunLike.congr_fun hright g
    simpa only [MonoidHom.comp_apply] using hleftValue.trans hrightValue.symm
  -- The open-cover generation theorem now collapses to `range j₁ = ⊤`.
  have hj₁Range : MonoidHom.range j₁ = ⊤ := by
    rw [← fundamentalGroupMap_range_sup_range_eq_top U V x₀ hx₀ hU hV hcover]
    simpa only [j₁, j₂] using (sup_eq_left.mpr hrightRange).symm
  exact MonoidHom.range_eq_top.mp hj₁Range

/-- The homomorphism induced by inclusion from the quotient of `π₁(U, x₀)` by the
normal closure of the image of the right intersection inclusion kernel. -/
noncomputable def fundamentalGroupQuotientInclusion
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V) :
    FundamentalGroup U ⟨x₀, hx₀.1⟩ ⧸ intersectionKernelNormalClosure U V x₀ hx₀ →*
      FundamentalGroup X x₀ :=
  QuotientGroup.lift (intersectionKernelNormalClosure U V x₀ hx₀)
    (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩)
    (intersectionKernelNormalClosure_le_inclusionKer U V x₀ hx₀)

/-- The quotient homomorphism agrees with the inclusion-induced homomorphism on
representatives. -/
@[simp] theorem fundamentalGroupQuotientInclusion_mk
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (g : FundamentalGroup U ⟨x₀, hx₀.1⟩) :
    fundamentalGroupQuotientInclusion U V x₀ hx₀ g =
      FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩ g :=
  by
    simp [fundamentalGroupQuotientInclusion]

/-- Helper for Exercise 70.2(a): If the right intersection inclusion is surjective on fundamental
groups, then the quotient homomorphism induced by the inclusion of `U` into `X` is
surjective. -/
theorem fundamentalGroupQuotientInclusion_surjective
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (hi₂ : Function.Surjective
      (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩)) :
    Function.Surjective
      (fundamentalGroupQuotientInclusion U V x₀ hx₀) := by
  -- Surjectivity of the inclusion map descends through its canonical quotient lift.
  simpa only [fundamentalGroupQuotientInclusion] using
    QuotientGroup.lift_surjective_of_surjective
      (intersectionKernelNormalClosure U V x₀ hx₀)
      (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩)
      (fundamentalGroupInclusion_surjective U V x₀ hx₀ hU hV hcover hi₂)
      (intersectionKernelNormalClosure_le_inclusionKer U V x₀ hx₀)

/-- Under the surjectivity hypothesis, the kernel of the inclusion-induced map from
`π₁(U, x₀)` is exactly the specified normal closure. -/
theorem fundamentalGroupInclusion_ker {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (hi₂ : Function.Surjective
      (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩)) :
    (FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩).ker =
      intersectionKernelNormalClosure U V x₀ hx₀ := by
  let i₁ := FundamentalGroup.mapOfSubset Set.inter_subset_left ⟨x₀, hx₀⟩
  let i₂ := FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩
  let j₁ := FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩
  let M := intersectionKernelNormalClosure U V x₀ hx₀
  let q := QuotientGroup.mk' M
  have hi₂' : Function.Surjective i₂ := by
    simpa only [i₂] using hi₂
  -- The quotient projection kills `i₁(ker i₂)` by the definition of `M`.
  have hker : i₂.ker ≤ (q.comp i₁).ker := by
    intro g hg
    have hmem : i₁ g ∈ M := Subgroup.subset_normalClosure ⟨g, hg, rfl⟩
    apply MonoidHom.mem_ker.mpr
    simpa only [MonoidHom.comp_apply, q, QuotientGroup.mk'_apply] using
      (QuotientGroup.eq_one_iff (i₁ g)).mpr hmem
  let φ₂ := i₂.liftOfSurjective hi₂' ⟨q.comp i₁, hker⟩
  -- The descended map on `V` has exactly the compatibility required by van Kampen.
  have hfactor : φ₂.comp i₂ = q.comp i₁ := by
    simpa only [φ₂, MonoidHom.liftOfSurjective] using
      i₂.liftOfRightInverse_comp (Function.surjInv hi₂')
        (Function.rightInverse_surjInv hi₂') ⟨q.comp i₁, hker⟩
  have hcompat : q.comp i₁ = φ₂.comp i₂ := hfactor.symm
  obtain ⟨Φ, hΦ, _⟩ :=
    seifertVanKampen U V x₀ hx₀ hU hV hcover q φ₂ hcompat
  -- The global extension sends every element of `ker j₁` to the trivial quotient class.
  have hkerLe : j₁.ker ≤ M := by
    intro g hg
    apply (QuotientGroup.eq_one_iff g).mp
    have hj₁Value : j₁ g = 1 := MonoidHom.mem_ker.mp hg
    have hΦValue := DFunLike.congr_fun hΦ.1 g
    calc
      (g : FundamentalGroup U ⟨x₀, hx₀.1⟩ ⧸ M) = q g :=
        (QuotientGroup.mk'_apply M g).symm
      _ = Φ (j₁ g) := hΦValue.symm
      _ = Φ 1 := congrArg Φ hj₁Value
      _ = 1 := map_one Φ
  -- Combine the extension argument with the generator containment proved above.
  apply le_antisymm
  · simpa only [j₁, M] using hkerLe
  · exact intersectionKernelNormalClosure_le_inclusionKer U V x₀ hx₀

/-- Exercise 70.2(b): The homomorphism from the quotient of `π₁(U, x₀)` by the least
normal subgroup containing the image of `ker i₂` to `π₁(X, x₀)` is an isomorphism. -/
theorem fundamentalGroupQuotientInclusion_bijective
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (U ∩ V : Set X)]
    (hi₂ : Function.Surjective
      (FundamentalGroup.mapOfSubset Set.inter_subset_right ⟨x₀, hx₀⟩)) :
    Function.Bijective
      (fundamentalGroupQuotientInclusion U V x₀ hx₀) := by
  constructor
  · -- The kernel equality is precisely the injectivity criterion for a quotient lift.
    rw [fundamentalGroupQuotientInclusion, QuotientGroup.injective_lift_iff]
    exact (fundamentalGroupInclusion_ker U V x₀ hx₀ hU hV hcover hi₂).symm
  · -- Part (a) supplies surjectivity of the same canonical lift.
    exact fundamentalGroupQuotientInclusion_surjective
      U V x₀ hx₀ hU hV hcover hi₂
