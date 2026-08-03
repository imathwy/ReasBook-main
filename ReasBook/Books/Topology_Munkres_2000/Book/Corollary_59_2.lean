module

import Topology_Munkres_2000.Book.Theorem_59_1
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

public section

universe u

/-- Helper for Corollary 59.2: trivial fundamental groups on two members of an open
cover force the fundamental group at a common basepoint to be trivial. -/
private lemma fundamentalGroupSubsingletonOfOpenCover {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [PathConnectedSpace (U ∩ V : Set X)]
    [Subsingleton (FundamentalGroup U ⟨x₀, hx₀.1⟩)]
    [Subsingleton (FundamentalGroup V ⟨x₀, hx₀.2⟩)] :
    Subsingleton (FundamentalGroup X x₀) := by
  -- Each inclusion homomorphism is the unique map out of its subsingleton source.
  have hUmap : FundamentalGroup.mapOfSubtype U ⟨x₀, hx₀.1⟩ = 1 :=
    Subsingleton.elim _ _
  have hVmap : FundamentalGroup.mapOfSubtype V ⟨x₀, hx₀.2⟩ = 1 :=
    Subsingleton.elim _ _
  -- Theorem 59.1 then identifies the bottom and top ambient subgroups.
  have hgenerated :=
    fundamentalGroupMap_range_sup_range_eq_top U V x₀ hx₀ hU hV hcover
  have hbotTop : (⊥ : Subgroup (FundamentalGroup X x₀)) = ⊤ := by
    simpa only [hUmap, hVmap, MonoidHom.range_one, sup_idem] using hgenerated
  -- A group is subsingleton exactly when its subgroup lattice is subsingleton.
  exact Subgroup.subsingleton_iff.mp (subsingleton_iff_bot_eq_top.mp hbotTop)

/-- Corollary 59.2: If a space is covered by two open simply connected subsets whose
intersection is path connected, then the space is simply connected. -/
theorem SimplyConnectedSpace.of_isOpen_cover {X : Type u} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (hUV : IsPathConnected (U ∩ V))
    (hUsc : IsSimplyConnected U) (hVsc : IsSimplyConnected V) :
    SimplyConnectedSpace X := by
  -- Choose the common basepoint and expose the hypotheses as the instances used below.
  obtain ⟨x₀, hx₀⟩ := hUV.nonempty
  letI : PathConnectedSpace (U ∩ V : Set X) :=
    isPathConnected_iff_pathConnectedSpace.mp hUV
  letI : SimplyConnectedSpace U := hUsc.simplyConnectedSpace
  letI : SimplyConnectedSpace V := hVsc.simplyConnectedSpace
  -- The two path-connected cover members meet, so their union, hence all of `X`, is path connected.
  have hXPathConnected : IsPathConnected (Set.univ : Set X) := by
    rw [← hcover]
    exact hUsc.isPathConnected.union hVsc.isPathConnected hUV.nonempty
  letI : PathConnectedSpace X := pathConnectedSpace_iff_univ.mpr hXPathConnected
  -- Van Kampen trivializes the fundamental group at the chosen common basepoint.
  letI : Subsingleton (FundamentalGroup X x₀) :=
    fundamentalGroupSubsingletonOfOpenCover U V x₀ hx₀ hU hV hcover
  -- Transport triviality to every basepoint and translate equality of loop classes to homotopy.
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro y γ
  have hy : Subsingleton (FundamentalGroup X y) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x₀ y).toEquiv.symm.subsingleton
  exact Quotient.eq.mp
    (@Subsingleton.elim (FundamentalGroup X y) hy ⟦γ⟧ ⟦Path.refl y⟧)
