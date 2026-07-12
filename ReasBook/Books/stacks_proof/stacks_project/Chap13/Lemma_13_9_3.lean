import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Limits

universe v u

namespace CochainComplex

open HomComplex

/- Domain-style sampling for Lemma 13.9.3:
- primary domain: homological algebra of cochain complexes, null-homotopies, and the
  mapping-cone / mapping-cocone factorization owners;
- inspected owner declarations:
  `HomologicalComplex.homotopyCofiber.desc`,
  `HomologicalComplex.homotopyCofiber.descEquiv`,
  `CochainComplex.mappingCone.desc`,
  `CochainComplex.mappingCocone.lift`;
- best owner abstraction: the canonical homotopy-cofiber factorization API, specialized in the
  cochain-complex model by `mappingCone.desc` and `mappingCocone.lift`;
- primitive data: a chosen null-homotopy `H : Homotopy (f ≫ g) 0`;
- derived API: direct use of the canonical factorization constructors
  `mappingCone.desc` and `mappingCocone.lift`, together with the source-facing existential
  consequences below.

Source/core/bridge triage:
- `source-facing`: the two existential factorization statements below, matching the textbook lemma;
- `core/canonical`: `homotopyCofiber.desc`, `homotopyCofiber.descEquiv`, `mappingCone.desc`, and
  `mappingCocone.lift`;
- `bridge/view`: the direct specialization of `mappingCone.desc` and `mappingCocone.lift` to a
  null-homotopy of `f ≫ g`, producing maps with source/target the textbook objects `C(f)^•` and
  `C(g)^•[-1]`.
-/

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
variable {K L M : CochainComplex C ℤ}

/-- Lemma 13.9.3 (1): if the composite `f ≫ g` is homotopic to zero, then `g` factors through a
morphism from the mapping cone `C(f)^• = CochainComplex.mappingCone f` to `M^•`. -/
@[stacks 08RI]
theorem comp_homotopic_to_zero_factors_through_mapping_cone
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    ∃ γ : mappingCone f ⟶ M, mappingCone.inr f ≫ γ = g := by
  refine ⟨mappingCone.desc f (Cochain.ofHomotopy H) g (by simp [δ_ofHomotopy H]), by simp⟩

/-- Lemma 13.9.3 (2): if the composite `f ≫ g` is homotopic to zero, then `f` factors through a
morphism `K^• ⟶ C(g)^•[-1]`, expressed canonically as a morphism to
`CochainComplex.mappingCocone g = (CochainComplex.mappingCone g)⟦(-1 : ℤ)⟧`. -/
@[stacks 08RI]
theorem comp_homotopic_to_zero_factors_through_mapping_cocone
    (f : K ⟶ L) (g : L ⟶ M) (H : Homotopy (f ≫ g) 0) :
    ∃ γ : K ⟶ mappingCocone g, γ ≫ mappingCocone.fst g = f := by
  refine ⟨mappingCocone.lift g f (Cochain.ofHomotopy H.symm) (by
    rw [δ_ofHomotopy H.symm]
    simp), by simp⟩

end

end CochainComplex
