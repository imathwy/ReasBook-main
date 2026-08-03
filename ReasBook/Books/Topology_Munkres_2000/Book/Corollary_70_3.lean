module

public import Topology_Munkres_2000.Book.Theorem_70_2
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import all Topology_Munkres_2000.Book.Theorem_70_2.Presentation

public section

universe u

/-- Helper for Corollary 70.3: the van Kampen relations normally generate the trivial
subgroup when the intersection fundamental group is subsingleton. -/
private lemma vanKampenNormalClosure_eq_bot_of_subsingleton
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [Subsingleton (FundamentalGroup (U ∩ V : Set X) ⟨x₀, hx₀⟩)] :
    FundamentalGroup.vanKampenNormalClosure U V x₀ hx₀ = ⊥ := by
  -- The presentation equations reduce the normal closure to its generating relations.
  rw [FundamentalGroup.vanKampenNormalClosure.eq_def,
    FundamentalGroup.vanKampenRelations.eq_def, Subgroup.normalClosure_eq_bot_iff]
  rintro _ ⟨g, rfl⟩
  rw [Subsingleton.elim g 1]
  simp only [FundamentalGroup.vanKampenRelation.eq_def, map_one, inv_one, one_mul,
    Set.mem_singleton_iff]

/-- The canonical Seifert–van Kampen homomorphism is bijective when the intersection
`U ∩ V` is simply connected. -/
theorem vanKampenMap_bijective_of_simplyConnected
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    Function.Bijective (FundamentalGroup.vanKampenMap U V x₀ hx₀) := by
  -- Theorem 70.2 supplies surjectivity and identifies the kernel with the relation closure.
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_,
    vanKampenMap_surjective U V x₀ hx₀ hU hV hcover⟩
  rw [vanKampenMap_ker U V x₀ hx₀ hU hV hcover,
    vanKampenNormalClosure_eq_bot_of_subsingleton]

/-- Corollary 70.3. Under the Seifert–van Kampen hypotheses, if `U ∩ V` is simply
connected, the canonical homomorphism from the free product of `π₁(U, x₀)` and
`π₁(V, x₀)` to `π₁(X, x₀)` underlies a multiplicative equivalence. -/
theorem exists_vanKampenMulEquiv
    {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)] :
    ∃ k : Monoid.Coprod (FundamentalGroup U ⟨x₀, hx₀.1⟩)
        (FundamentalGroup V ⟨x₀, hx₀.2⟩) ≃* FundamentalGroup X x₀,
      k.toMonoidHom = FundamentalGroup.vanKampenMap U V x₀ hx₀ := by
  refine ⟨MulEquiv.ofBijective _
    (vanKampenMap_bijective_of_simplyConnected U V x₀ hx₀ hU hV hcover), ?_⟩
  rfl
