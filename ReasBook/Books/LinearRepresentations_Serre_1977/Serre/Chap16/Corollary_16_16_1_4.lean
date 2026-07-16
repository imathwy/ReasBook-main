import LinearRepresentations_Serre_1977.Serre.Chap16.Theorem_16_16_1_2

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation

universe u

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local notation "k" => IsLocalRing.ResidueField A

/- Domain-style sampling for Corollary 16-16.1-4:
* primary domain: scalar extension of finite projective `A[G]`-modules and the induced
  Grothendieck-group maps `P₀[k](G) → R₀[K](G)`;
* relevant owner declarations inspected in this domain:
  `projectiveGrothendieckScalarExtensionHom`,
  `projectiveGrothendieckReductionEquiv`,
  `finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso`;
* best owner abstraction: the canonical owner category
  `FiniteProjectiveGroupAlgebraModule A G`, together with the canonical Grothendieck-group maps
  built from it;
* source/core/bridge triage:
  source-facing: equality of scalar-extension classes forces isomorphism of the original finite
    projective `A[G]`-modules;
  core/canonical: Serre's map `projectiveGrothendieckScalarExtensionHom A K` and the reduction
    equivalence `projectiveGrothendieckReductionEquiv A G`;
  bridge/view: Chapter `14`'s classification theorem from equality in `P₀[A](G)` to an isomorphism
    in the owner category.
* primitive data: equality of the scalar-extension classes in `R₀[K](G)`;
* derived API: injectivity of `projectiveGrothendieckScalarExtensionHom A K`, transported
  equality in `P₀[A](G)`, and the resulting owner isomorphism.
The theorem should therefore conclude with the canonical owner-level isomorphism `P ≅ P'`, rather
than keeping a parallel module-level bridge as its main public surface.
-/

-- Proof sketch: the source proof uses injectivity of Serre's map `e` directly, so the right Lean
-- skeleton is to reflect equality of scalar-extension classes back along the base-change
-- homomorphism `P₀[A](G) → R₀[K](G)` and then finish with the Chapter `14` class-equality
-- criterion. The only remaining blocker is the earlier public injectivity bridge for that
-- base-change homomorphism on the present `[IsLocalRing A] [IsFractionRing A K]` surface.
/-- Helper for Corollary 16-16.1-4: the base-change homomorphism on projective Grothendieck
classes is injective on the present Henselian-local surface. -/
private theorem projective_baseChange_injective
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K] [PerfectField (IsLocalRing.ResidueField A)] :
    Function.Injective (projectiveGrothendieckBaseChangeHom (A := A) (G := G) K) := by
  -- Reflect equality of base-change classes through the split injectivity of Serre's map and
  -- then transport back across the reduction equivalence.
  obtain ⟨s, hs⟩ :=
    projectiveGrothendieckScalarExtensionHom_split_injective
      (A := A) (K := K) (G := G)
  intro x y hxy
  have hred :
      projectiveGrothendieckReductionEquiv (A := A) (G := G) x =
        projectiveGrothendieckReductionEquiv (A := A) (G := G) y := by
    apply hs.injective
    -- Rewrite Serre's scalar-extension map on both sides to the source-facing base-change map.
    simpa [projectiveGrothendieckScalarExtensionHom_apply] using hxy
  exact (projectiveGrothendieckReductionEquiv (A := A) (G := G)).injective hred

/-- Helper for Corollary 16-16.1-4: equality of scalar-extension classes reflects to equality of
projective Grothendieck classes over `A[G]`. -/
private theorem projective_class_eq_of_scalarExtensionClass_eq
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K] [PerfectField (IsLocalRing.ResidueField A)]
    (P P' : FiniteProjectiveGroupAlgebraModule A G)
    (hclass : [P.scalarExtension K]₀ = [P'.scalarExtension K]₀) :
    [P]ₚ₀ = [P']ₚ₀ := by
  -- Reflect the equality of generic-fiber classes through the injective base-change map.
  apply projective_baseChange_injective (A := A) (K := K) (G := G)
  -- On projective generators, the source-facing base-change map is scalar extension.
  simpa [projectiveGrothendieckBaseChangeHom_projectiveClass_eq] using hclass

/-- Corollary 16-16.1-4: if two finite projective `A[G]`-modules have the same scalar-extension
class in `R₀[K](G)`, then they are already isomorphic in the canonical owner category of finite
projective `A[G]`-modules. -/
theorem finiteProjectiveGroupAlgebraModule_iso_of_scalarExtensionClass_eq
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharZero K] [PerfectField (IsLocalRing.ResidueField A)]
    (P P' : FiniteProjectiveGroupAlgebraModule A G)
    (hclass : [P.scalarExtension K]₀ = [P'.scalarExtension K]₀) :
    Nonempty (P ≅ P') := by
  -- First reflect the equality of generic-fiber classes back to `P₀[A](G)`.
  have hprojective : [P]ₚ₀ = [P']ₚ₀ :=
    projective_class_eq_of_scalarExtensionClass_eq (A := A) (K := K) (G := G) P P' hclass
  -- Then apply the Chapter 14 criterion identifying class equality with isomorphism.
  exact (finiteProjectiveGroupAlgebraGrothendieckClass_eq_iff_nonempty_iso P P').mp hprojective

end

end Representation
