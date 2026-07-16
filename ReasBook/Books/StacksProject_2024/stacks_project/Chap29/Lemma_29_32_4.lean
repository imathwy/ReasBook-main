import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_10
import StacksProject_2024.stacks_project.Chap29.Lemma_29_33_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open AlgebraicGeometry
open RingedSpace.Hom
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {R A : CommRingCat.{u}}

-- Semantic recall: `Der[ψ ; ℱ]` is the canonical sheaf-level owner for relative derivations, and
-- the affine comparison on global sections should reuse the canonical affine-global-sections
-- algebra/module tower from `Lemma_29_33_1`. The source-facing affine statement is therefore an
-- existence-and-uniqueness comparison between a sheaf relative derivation and an ordinary
-- derivation on affine global sections, with the explicit `ΓSpecIso` computation written directly
-- in the statement rather than wrapped in a separate predicate.

/-- Relative derivations on the affine global sections of an `\mathcal O_{Spec(A)}`-module over
the ring map `R ⟶ A`. -/
abbrev affineGlobalSectionsDerivations
    (φ : R ⟶ A) (ℱ : (Spec A).Modules) :=
  (ModuleCat.of A (Γ(ℱ, ⊤))).Derivation φ

/-- Lemma 29.32.4: let `φ : R ⟶ A`, let `X = Spec(A)`, `S = Spec(R)`, and let `ℱ` be an
`\mathcal O_X`-module. Then every `R`-derivation on the affine global sections `Γ(X, ℱ)` lifts
uniquely to an `S`-derivation on `ℱ`. Equivalently, sending an `S`-derivation on `ℱ` to its
action on global sections yields a bijection between `S`-derivations of `ℱ` and `R`-derivations
on `Γ(X, ℱ)`. -/
theorem existsUnique_affineRelativeDerivation_of_globalSections
    (φ : R ⟶ A) (ℱ : (Spec A).Modules) (D : affineGlobalSectionsDerivations φ ℱ) :
    ∃! Dsheaf : Der[inverseImageStructureSheafHomComm (Spec.map φ).toShHom ; ℱ],
      ∀ a : A,
        ((Dsheaf.app (op ⊤)).d ((Scheme.ΓSpecIso A).inv.hom a)) = D.d a := by
  sorry

end

end AlgebraicGeometry
