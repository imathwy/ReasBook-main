import Mathlib
import stacks_project.Chap15.Definition_15_28_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open CategoryTheory ComplexShape HomologicalComplex

/- Domain-style sampling:
- primary domain: degree shifts of `ℕ`-indexed chain complexes, expressed canonically through the
  cochain-complex shift on `ℤ` together with complex-shape embeddings;
- sampled owner declarations:
  `HomologicalComplex.extend`,
  `HomologicalComplex.restriction`,
  `ComplexShape.embeddingDownNat`,
  `CategoryTheory.shiftFunctor` on `CochainComplex C ℤ`;
- best owner abstraction: for an `ℕ`-indexed chain complex `K`, the source-facing degree-one
  shifted complex is the bridge/view
  `((K.extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`;
- primitive data: the chain complex `K` and the canonical embedding `embeddingDownNat`;
- derived API: any `ℕ`-indexed reformulation of that shifted complex.

Source/core/bridge triage:
- `source-facing`: the existence statement for the Koszul complexes in Lemma 15.28.10;
- `core/canonical`: `extend`, `restriction`, `embeddingDownNat`, and the canonical cochain shift;
- `bridge/view`: the `ℕ`-indexed shifted-chain source object obtained by extending to `ℤ`,
  shifting by `-1`, and restricting back. This file should therefore use that owner expression
  directly rather than keep a parallel local shift definition. -/

section

variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]

-- Proof sketch: identify the three Koszul complexes attached to
-- `koszulCoprodScalarLinearMap φ f`, `koszulCoprodScalarLinearMap φ g`, and
-- `koszulCoprodScalarLinearMap φ (f * g)` with the corresponding homotopy cofibers from
-- Lemma 15.28.7; interpret the degree-one shift of the first complex via the canonical bridge
-- `((K.extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`; then apply
-- `homotopyCofiber_smul_mul_exists_homotopyEquiv_homotopyCofiber` to the scalar endomorphisms
-- of `koszulComplex φ`.
/-- Lemma 15.28.10: if `φ'_f`, `φ'_g`, and `φ'_{fg}` are the linear forms on `E ⊕ R`, realized in
Lean as `E × R`, obtained from `φ` by adjoining multiplication by `f`, `g`, and `f * g` on the
`R`-summand, then the Koszul complex of `φ'_{fg}` is homotopy equivalent to the cone of a map
from the canonical degree-one shift
`((K(φ'_f).extend embeddingDownNat)⟦(-1 : ℤ)⟧).restriction embeddingDownNat`
to `K(φ'_g)`. -/
theorem koszulComplex_coprod_scalar_mul_exists_homotopyEquiv_homotopyCofiber
    (φ : E →ₗ[R] R) (f g : R) :
    ∃ α :
        (((koszulComplex (koszulCoprodScalarLinearMap φ f)).extend embeddingDownNat)⟦
          (-1 : ℤ)⟧).restriction embeddingDownNat ⟶
          koszulComplex (koszulCoprodScalarLinearMap φ g),
      Nonempty
        (HomotopyEquiv
          (koszulComplex (koszulCoprodScalarLinearMap φ (f * g)))
          (homotopyCofiber α)) := sorry

end
