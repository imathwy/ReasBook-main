import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Ideal
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 11.4.5:
- primary domain: Morita-theoretic and ring-theoretic invariants of full matrix rings, with the
  chapter convention that an `A`-module means a right `A`-module, modeled as a left module over
  `Aᵐᵒᵖ`;
- sampled owner declarations:
  `ModuleCat.matrixEquivalence`,
  `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`,
  `TwoSidedIdeal.equivMatrix`,
  `Matrix.subringCenter_eq_scalar_map`;
- best owner abstractions:
  `ModuleCat.matrixEquivalence` for the underlying Morita equivalence, transported to right
  modules by `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` along the canonical matrix-opposite
  ring equivalence `RingEquiv.mopMatrix`,
  `TwoSidedIdeal.equivMatrix` for the source-facing ideal correspondence,
  `Matrix.subringCenter_eq_scalar_map` for the center computation;
- primitive data: only the ring `R`, the size `n`, and a witness of `Fin n` when nonemptiness is
  needed to instantiate the Morita inverse and ideal correspondence;
- derived API: the textbook statements are direct views of those owner declarations and their
  canonical bridge, so this file should stay at the recall/bridge layer rather than introducing
  local wrappers.

Source/core/bridge triage:
- `source-facing`: the three textbook properties of full matrix rings listed in Lemma 11.4.5,
  where part (1) is a statement about right modules;
- `core/canonical`: `ModuleCat.matrixEquivalence`, `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`,
  `TwoSidedIdeal.equivMatrix`, and `Matrix.subringCenter_eq_scalar_map`;
- `bridge/view`: `RingEquiv.mopMatrix`, which identifies modules over
  `Matrix (Fin n) (Fin n) Rᵐᵒᵖ` with right modules over `Matrix (Fin n) (Fin n) R`, and the
  `#check` lines below exhibiting the source statements as direct uses of those owners. -/

section RightModuleEquivalence

open CategoryTheory

variable (R : Type*) [Ring R] (n : ℕ) (hn : 1 ≤ n)

/- Owner recall for Lemma 11.4.5 (1): the canonical owner abstraction is the Morita equivalence
for left modules over `Rᵐᵒᵖ`, namely `ModuleCat.matrixEquivalence`, together with the canonical
change-of-rings equivalence induced by `RingEquiv.mopMatrix`. -/
recall ModuleCat.matrixEquivalence
recall ModuleCat.restrictScalarsEquivalenceOfRingEquiv
recall RingEquiv.mopMatrix

/- Lemma 11.4.5 (1): for a possibly noncommutative ring `R` and `n ≥ 1`, the equivalence between
right `R`-modules and right `M_n(R)`-modules is obtained by applying
`ModuleCat.matrixEquivalence` to `Rᵐᵒᵖ` and then transporting across the canonical identification
`Matrix (Fin n) (Fin n) Rᵐᵒᵖ ≃+* (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ`. -/
#check
  ((ModuleCat.matrixEquivalence Rᵐᵒᵖ (⟨0, Nat.succ_le_iff.mp hn⟩ : Fin n)).trans
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      RingEquiv.mopMatrix).symm :
      ModuleCat Rᵐᵒᵖ ≌ ModuleCat (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ)

end RightModuleEquivalence

section TwoSidedIdeals

variable (R : Type*) [Ring R] (n : ℕ) (hn : 1 ≤ n)

/- Owner recall for Lemma 11.4.5 (2): the ideal correspondence lives canonically in
`TwoSidedIdeal.equivMatrix`. -/
recall TwoSidedIdeal.equivMatrix

/- Lemma 11.4.5 (2): the correspondence between two-sided ideals of `R` and of the matrix ring
`Matrix (Fin n) (Fin n) R` is the canonical equivalence `TwoSidedIdeal.equivMatrix`; the
textbook existence statement is its surjectivity. -/
#check
  (let _ : Nonempty (Fin n) := ⟨⟨0, Nat.succ_le_iff.mp hn⟩⟩
   TwoSidedIdeal.equivMatrix :
     TwoSidedIdeal R ≃ TwoSidedIdeal (Matrix (Fin n) (Fin n) R))

end TwoSidedIdeals

section Center

variable (R : Type*) [Ring R] (n : ℕ)

/- Owner recall for Lemma 11.4.5 (3): the center statement is exactly the matrix-center owner
theorem `Matrix.subringCenter_eq_scalar_map`. -/
recall Matrix.subringCenter_eq_scalar_map

/- Lemma 11.4.5 (3): the center of `Matrix (Fin n) (Fin n) R` is the image of the center of
`R` under the scalar-matrix embedding, which is the precise Lean form of saying that the center
of `Rₙ` equals the center of `R`. -/
#check
  (Matrix.subringCenter_eq_scalar_map R :
    Subring.center (Matrix (Fin n) (Fin n) R) = (Subring.center R).map (Matrix.scalar (Fin n)))

end Center
