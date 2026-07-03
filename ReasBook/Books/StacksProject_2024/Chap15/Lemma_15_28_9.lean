import Mathlib
import StacksProject_2024.Chap12.Definition_12_14_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v u

open CategoryTheory HomologicalComplex

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
- primary domain: mapping-cone / homotopy-cofiber constructions in the homotopy category of chain
  complexes;
- owner declarations inspected: `HomologicalComplex.homotopyCofiber`,
  `HomotopyEquiv`, `HomologicalComplex.homotopyEquivalences`, and the chapter recall
  `Definition_12_13_2`;
- best owner abstraction: the canonical cone object `homotopyCofiber` together with the canonical
  homotopy-equivalence owner/bridge pair `HomotopyEquiv` and `homotopyEquivalences`.

Primitive data are only the chain complex `A` and the scalar endomorphisms `f • 𝟙 A`,
`g • 𝟙 A`, and `(f * g) • 𝟙 A`. The morphism
`(homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧ ⟶ homotopyCofiber (g • 𝟙 A)` is source-facing bridge data,
and the resulting morphism from `homotopyCofiber ((f * g) • 𝟙 A)` to the cone of that morphism
being a homotopy equivalence is derived API, not primitive owner data.

Layer triage:
- `core/canonical`: `homotopyCofiber` and `HomotopyEquiv`;
- `bridge/view`: the source-facing assertion that there exists some comparison morphism whose cone
  is homotopy equivalent to the cone of multiplication by `f * g`.
-/

-- Proof sketch: first treat the two-term complex `R ⟶ R`, where there is an explicit morphism
-- from the shifted cone of multiplication by `f` to the cone of multiplication by `g` whose cone
-- is homotopy equivalent to the cone of multiplication by `f * g`. Then tensor that explicit
-- two-term construction with `A` and pass to the total complex, using compatibility of
-- totalization with cones and homotopies.
/-- Lemma 15.28.9: for a chain complex `A_•` of `R`-modules and scalars `f, g : R`, the cone of
multiplication by `f * g` on `A_•` is homotopy equivalent to the cone of some morphism from the
degree-one shift of the cone of multiplication by `f` to the cone of multiplication by `g`. -/
theorem homotopyCofiber_smul_mul_exists_homotopyEquiv_homotopyCofiber
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    ∃ α : (homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧ ⟶ homotopyCofiber (g • 𝟙 A),
      Nonempty (HomotopyEquiv (homotopyCofiber ((f * g) • 𝟙 A)) (homotopyCofiber α)) := sorry
