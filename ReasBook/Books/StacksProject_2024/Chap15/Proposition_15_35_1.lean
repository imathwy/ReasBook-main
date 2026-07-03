import Mathlib
import stacks_project.Chap10.Definition_10_110_7
import stacks_project.Chap10.Lemma_10_44_2
import stacks_project.Chap10.Lemma_10_166_5

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open scoped TensorProduct
open TensorProduct.AlgebraTensorModule

noncomputable section

universe u v w

/- Domain triage:
* primary domain: geometric regularity of local `k`-algebras in characteristic `p`, together with
  the cotangent-theoretic criteria for the local map `k → A`;
* sampled owner declarations:
  - `Algebra.IsGeometricallyRegular`,
  - `onePthRootExtension`,
  - `Algebra.H1Cotangent.map`,
  - `_root_.KaehlerDifferential.mapBaseChange`,
  - `_root_.LinearMap.liftBaseChange`;
* best owner abstraction: the proposition should keep the source-facing finite test
  `k ⊂ k' ⊂ k^{1/p}` through the chapter-local owner `onePthRootExtension`, and use
  `IsGeometricallyRegular`, `H1Cotangent.map`, and `KaehlerDifferential.mapBaseChange` only as the
  canonical bridge/core layer;
* layer triage:
  - `source-facing`: Proposition `15.35.1`, the four-way equivalence;
  - `core/canonical`: `IsGeometricallyRegular`, `onePthRootExtension`,
    `H1Cotangent.map`, and `KaehlerDifferential.mapBaseChange`;
  - `bridge/view`: the named residue-field comparison
    `KaehlerDifferential.residueFieldComparison`, obtained from
    `KaehlerDifferential.mapBaseChange` by tensoring to `κ(A)`.

Primitive data are the canonical owner maps themselves. The conjunction clauses in the `TFAE`
statement are derived API, so the only extracted bridge is the reusable residue-field comparison
map needed by both this proposition and Theorem `15.40.1`.
-/

namespace KaehlerDifferential

section

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S]
variable (A : Type w) [CommRing A] [Algebra R S] [Algebra S A] [Algebra R A]
variable [IsScalarTower R S A] [IsLocalRing A]

/-- The canonical comparison map
`κ(A) ⊗[S] Ω[S⁄R] → κ(A) ⊗[A] Ω[A⁄R]` induced by
`KaehlerDifferential.mapBaseChange R S A` and residue-field base change. -/
noncomputable abbrev residueFieldComparison :
    ResidueField A ⊗[S] Ω[S⁄R] →ₗ[ResidueField A] ResidueField A ⊗[A] Ω[A⁄R] :=
  lTensor (ResidueField A) (ResidueField A) (KaehlerDifferential.mapBaseChange R S A) ∘ₗ
    (cancelBaseChange S A (ResidueField A) (ResidueField A) Ω[S⁄R]).symm.toLinearMap

end

end KaehlerDifferential

namespace Algebra

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [IsLocalRing A] [Algebra k A]
variable {p : ℕ} [Fact p.Prime]
variable [CharP k p] [IsNoetherianRing A]

-- Proof sketch: use the source-facing finite `k ⊂ k' ⊂ k^{1/p}` test as a bridge to geometric
-- regularity, then combine the cotangent-homology and differential criteria for the residue
-- field. The third
-- clause uses the canonical Jacobi-Zariski map
-- `H1Cotangent.map k A κ(A) κ(A)`, which corresponds to `H_1(L_{κ(A)/k}) → 𝔪/𝔪²`.
/-- Proposition 15.35.1: for a Noetherian local `k`-algebra `A` in characteristic `p > 0`, the
following are equivalent: `A` is geometrically regular over `k`; for every finite intermediate
field `k ⊂ k' ⊂ k^{1/p}`, realized through the chosen chapter-local model
`onePthRootExtension k p`, the tensor base change `k' ⊗[k] A` is regular; `A` is regular local and
the canonical map `H_1(L_{κ(A)/k}) → 𝔪_A / 𝔪_A^2` is injective, expressed in the library-facing
form `Function.Injective (H1Cotangent.map k A κ(A) κ(A))`; and `A` is regular local and
`KaehlerDifferential.residueFieldComparison (ZMod p) k A` is injective. -/
theorem geometricallyRegularLocalRing_tfae_of_charP :
    by
      letI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
      letI : Algebra (ZMod p) k := ZMod.algebra k p
      letI : Algebra (ZMod p) A := ZMod.algebra A p
      letI : IsScalarTower (ZMod p) k A := by infer_instance
      exact
        List.TFAE [
          IsGeometricallyRegular k A,
          ∀ (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K],
            K ≤ onePthRootExtension k p →
              IsRegularRing (K ⊗[k] A),
          IsRegularLocalRing A ∧
            Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)),
          IsRegularLocalRing A ∧
            Function.Injective (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
        ] := sorry

end

end Algebra
