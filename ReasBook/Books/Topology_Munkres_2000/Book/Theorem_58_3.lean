module

public import Topology_Munkres_2000.Book.Proposition_58_2.HomotopyEquiv
public import Topology_Munkres_2000.Book.Notation_52_3.InducedMap
public import Topology_Munkres_2000.Book.Theorem_58_3.HomotopyEquiv

public section

universe u

namespace Set.IsDeformationRetract

open FundamentalGroup.LeftToRight

/-- Helper for Theorem 58.3: taking the opposite of a bijective monoid homomorphism
preserves bijectivity. -/
private lemma monoidHomOp_bijective {M N : Type*} [MulOneClass M] [MulOneClass N]
    (f : M →* N) (hf : Function.Bijective f) :
    Function.Bijective (MonoidHom.op f) := by
  -- The opposite homomorphism is `unop`, followed by `f`, followed by `op`.
  exact MulOpposite.op_bijective.comp (hf.comp MulOpposite.unop_bijective)

/-- Theorem 58.3. If `A` is a deformation retract of `X`, then the inclusion
`A ↪ X` induces a bijective homomorphism on fundamental groups at `x₀`. -/
theorem fundamentalGroupMap_bijective {X : Type u} [TopologicalSpace X]
    {A : Set X} (hA : IsDeformationRetract A) (x₀ : A) :
    Function.Bijective
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))₍x₀₎)₊ := by
  -- Use the public characterization to recover the opaque deformation-retraction data.
  obtain ⟨r, ⟨H⟩⟩ := (Set.isDeformationRetract_iff A).1 hA
  let D : Set.DeformationRetraction A :=
    Set.DeformationRetraction.ofHomotopyRel r H
  have hForward : D.toHomotopyEquiv.toFun =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) := by
    -- The owner API identifies the opaque equivalence's forward map pointwise.
    ext a
    exact D.toHomotopyEquiv_apply a
  have hCanonical : Function.Bijective
      (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) x₀) := by
    -- Homotopy equivalences induce bijections on the canonical fundamental groups.
    rw [← hForward]
    exact D.toHomotopyEquiv.fundamentalGroupMap_bijective x₀
  -- Passing to opposite groups converts the canonical map to Munkres's convention.
  exact monoidHomOp_bijective _ hCanonical

end Set.IsDeformationRetract

end
