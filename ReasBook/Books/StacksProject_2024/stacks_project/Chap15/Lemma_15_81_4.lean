import Mathlib
import StacksProject_2024.Chap15.Definition_15_81_2
import StacksProject_2024.Chap15.Lemma_15_81_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped TensorProduct

local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: relative finite presentation of modules under localization;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.FinitePresentation`,
  `Module.finitePresentation_of_finitePresentationRelativeTo`,
  `LocalizedModule.Away`,
  `IsLocalization.Away.finitePresentation`;
- best owner abstraction: the source-facing predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: one surjective polynomial presentation of the ambient algebra together with
  finite presentation of the induced module over that polynomial ring;
- derived API: localization statements and ordinary finite presentation over the target algebra.

Source/core/bridge triage:
- `source-facing`: the localization theorem below for relative finite presentation;
- `core/canonical`: `Module.FinitePresentation`;
- `bridge/view`: passage from the localized source-facing owner over `Localization.Away f` to the
  localized target owner over `R`.

The raw existential in the original statement is exactly the primitive data already owned by
`Module.FinitePresentationRelativeTo`, so the theorem should use that owner directly rather than
repeat the witness package locally. -/

variable {R : Type u} [CommRing R]
variable {f : R}
variable {A : Type v} [CommRing A] [Algebra R A] [Algebra (Localization.Away f) A]
variable [IsScalarTower R (Localization.Away f) A]
variable {g : A}
variable {M : Type w} [AddCommGroup M] [Module A M]

-- Proof sketch: choose a polynomial presentation of `A` over `Localization.Away f`, rewrite
-- `Localization.Away f` as an `R`-algebra obtained by adjoining an inverse to `f`, then localize
-- the presentation further at `g` by adjoining an inverse to `g`; this gives a polynomial
-- presentation of `LocalizedModule.Away g M` over `R`.
/-- Lemma 15.81.4: if `M` is finitely presented relative to the localized base
`Localization.Away f` as an `A`-module, then the localized module `Away g M` is
finitely presented relative to `R` as a `Localization.Away g`-module. -/
theorem Module.finitePresentationRelativeTo_localizationAway_from_localizedBase
    (hM : Module.FinitePresentationRelativeTo (Localization.Away f) A M) :
    Module.FinitePresentationRelativeTo R (Localization.Away g) (Away g M) := by
  have hTensor :
      Module.FinitePresentationRelativeTo (Localization.Away f) (Localization.Away g)
        ((Localization.Away g) ⊗[A] M) :=
    Module.finitePresentationRelativeTo_baseChange_of_finitePresentation
      (R := Localization.Away f) (A := A) (A' := Localization.Away g) (M := M) hM
  rcases hTensor with ⟨n, α, hα, hTensor⟩
  let eTensor : Away g M ≃ₗ[Localization.Away g] (Localization.Away g) ⊗[A] M :=
    LocalizedModule.equivTensorProduct (Submonoid.powers g) M
  let P := MvPolynomial (Fin n) (Localization.Away f)
  letI : Module P ((Localization.Away g) ⊗[A] M) := Module.compHom _ α.toRingHom
  letI : Module P (Away g M) := Module.compHom (Away g M) α.toRingHom
  letI : Module.FinitePresentation P ((Localization.Away g) ⊗[A] M) := by
    simpa [P] using hTensor
  have hmap_smul :
      ∀ c : P, ∀ x : (Localization.Away g) ⊗[A] M,
        eTensor.symm ((α c) • x) = (α c) • eTensor.symm x := by
    intro c x
    exact eTensor.symm.map_smul (α c) x
  have hAwayP : Module.FinitePresentation P (Away g M) := by
    let eP : ((Localization.Away g) ⊗[A] M) ≃ₗ[P] Away g M :=
      { toFun := eTensor.symm
        invFun := eTensor
        left_inv := eTensor.symm.left_inv
        right_inv := eTensor.symm.right_inv
        map_add' := eTensor.symm.map_add
        map_smul' := hmap_smul }
    exact Module.FinitePresentation.of_equiv eP
  letI : Algebra.FinitePresentation R (Localization.Away f) :=
    IsLocalization.Away.finitePresentation f
  have hP : Algebra.FinitePresentation R P := by
    simpa [P] using
      (Algebra.FinitePresentation.mvPolynomial_of_finitePresentation
        (R := R) (A := Localization.Away f) (Fin n))
  letI : Algebra.FinitePresentation R P := hP
  obtain ⟨m, β, hβ, hkerβ⟩ := (inferInstance : Algebra.FinitePresentation R P).out
  let Q := MvPolynomial (Fin m) R
  letI : Algebra Q P := β.toRingHom.toAlgebra
  letI : Module Q P := Module.compHom P β.toRingHom
  have hQP : Module.FinitePresentation Q P := by
    refine Module.finitePresentation_of_surjective (Algebra.linearMap Q P) hβ ?_
    simpa using hkerβ
  letI : Module.FinitePresentation Q P := hQP
  letI : Module Q (Away g M) := Module.compHom (Away g M) ((α.restrictScalars R).comp β).toRingHom
  letI : IsScalarTower Q P (Away g M) := IsScalarTower.of_compHom Q P (Away g M)
  have hαR : Function.Surjective (α.restrictScalars R) := by
    simpa using hα
  have hcomp : Function.Surjective ((α.restrictScalars R).comp β) := by
    intro x
    rcases hαR x with ⟨y, rfl⟩
    rcases hβ y with ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  refine ⟨m, (α.restrictScalars R).comp β, hcomp, ?_⟩
  exact (Module.FinitePresentation.trans Q (Away g M) P :
    Module.FinitePresentation Q (Away g M))

end
