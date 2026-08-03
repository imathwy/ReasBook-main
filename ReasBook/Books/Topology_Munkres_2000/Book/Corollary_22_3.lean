module

public import Topology_Munkres_2000.Book.Theorem_22_2
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Separation.Hausdorff

public section

namespace Setoid

universe u v

variable {X : Type u} {Z : Type v}

/-- Helper for Corollary 22.3: the equivalence induced by a surjection agrees
with the original map after the kernel-quotient projection. -/
lemma quotientKerEquivOfSurjective_comp_mk (g : X → Z)
    (hg_surj : Function.Surjective g) :
    (quotientKerEquivOfSurjective g hg_surj : Quotient (ker g) → Z) ∘
        Quotient.mk'' = g := by
  -- Evaluate the induced equivalence on representatives of the quotient.
  funext x
  exact kerLift_mk g x

variable [TopologicalSpace X] [TopologicalSpace Z]

/-- Corollary 22.3 (1): A surjective continuous map induces a continuous
equivalence from its kernel quotient to its codomain. -/
theorem quotientKerEquivOfSurjective_continuous (g : X → Z)
    (hg_surj : Function.Surjective g) (hg_cont : Continuous g) :
    Continuous (quotientKerEquivOfSurjective g hg_surj) := by
  -- Descend continuity through the canonical quotient projection.
  rw [Topology.IsQuotientMap.continuous_iff_of_comp_eq
    isQuotientMap_quotient_mk'
    (quotientKerEquivOfSurjective_comp_mk g hg_surj)]
  exact hg_cont

/-- Corollary 22.3 (2): The induced equivalence from the kernel quotient is a
homeomorphism exactly when the original map is a quotient map. -/
theorem quotientKerEquivOfSurjective_isHomeomorph_iff (g : X → Z)
    (hg_surj : Function.Surjective g) :
    IsHomeomorph (quotientKerEquivOfSurjective g hg_surj) ↔
      Topology.IsQuotientMap g := by
  -- A bijection is a homeomorphism precisely when it is a quotient map.
  rw [isHomeomorph_iff_isQuotientMap_injective]
  rw [Topology.IsQuotientMap.isQuotientMap_iff_of_comp_eq
    isQuotientMap_quotient_mk'
    (quotientKerEquivOfSurjective_comp_mk g hg_surj)]
  simp only [Equiv.injective, and_true]

/-- Corollary 22.3 (3): If the codomain of a surjective continuous map is
Hausdorff, then its kernel quotient is Hausdorff. -/
theorem t2Space_quotientKer [T2Space Z] (g : X → Z)
    (hg_surj : Function.Surjective g) (hg_cont : Continuous g) :
    T2Space (Quotient (ker g)) := by
  -- Transfer Hausdorff separation along the continuous induced injection.
  exact T2Space.of_injective_continuous
    (quotientKerEquivOfSurjective g hg_surj).injective
    (quotientKerEquivOfSurjective_continuous g hg_surj hg_cont)

end Setoid
