import Mathlib
import StacksProject_2024.Chap13.Definition_13_19_1
import StacksProject_2024.Chap15.Lemma_15_72_1
import StacksProject_2024.Chap15.Definition_15_59_1
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_74_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "ProjMinus" => CochainComplex.ProjectiveMinus (ModuleCat R)

open scoped DerivedInternalHom
open scoped ModuleComplexInternalHom

/- Domain-style sampling for Lemma 15.99.4:
- primary domain: the canonical Hom complex of cochain complexes of `R`-modules and its comparison
  with the chosen derived internal Hom on `D(R)`, for bounded-above termwise-projective source
  complexes;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.HomComplex`,
  `module_complex_internal_hom`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective`,
  `CochainComplex.IsBoundedFiniteProjective`,
  `DerivedCategory.IsPerfect`,
  the source-facing notation `RHom[H](K, L)`;
- best owner abstraction:
  `source-facing`: the K-flatness upgrade for `⟪P, K⟫` when `P : ProjectiveMinus` represents a
  perfect object and `K` is K-flat;
  `core/canonical`: the chapter owner `module_complex_internal_hom` from `Lemma_15_72_1` together
  with the source-side owner `CochainComplex.ProjectiveMinus` from Chapter 13 and the chosen
  monoidal-closed owner `H : MonoidalClosed DMod`;
  `bridge/view`: the resulting isomorphism
  `DerivedCategory.Q.obj ⟪P, K⟫ ≅ RHom[H](Q.obj P, Q.obj K)` for `P : ProjectiveMinus`;
- primitive data vs. derived API: the primitive source-side data here are exactly the owner datum
  `P : ProjectiveMinus`. Perfectness is derived additional structure used only for the K-flatness
  upgrade, not for the representation theorem itself. The Hom complex is already primitive
  upstream, so the local degreewise/differential reconstruction was duplicate derived API and
  should be deleted.
-/

-- Proof sketch: bounded-above termwise-projective complexes are K-projective, so the canonical
-- Hom complex already computes `RHom(P^•, K^•)` in the derived category without any perfectness
-- or K-flatness hypothesis on the target complex.
/-- The canonical comparison between the Hom complex `\mathrm{Hom}^\bullet(P^•, K^•)` and the
chosen derived internal Hom `R\mathrm{Hom}_R(P^•, K^•)` when `P^•` is bounded above and
termwise projective. This is the direct theorem-level representation layer; the perfectness
hypothesis is only needed later for the K-flatness upgrade. -/
theorem module_complex_internal_hom_represents_derivedInternalHom_of_boundedAbove_projective
    (H : RHomPkg)
    (P : ProjMinus) (K : Cpx) :
    IsIsomorphic
      (DerivedCategory.Q.obj ⟪P, K⟫)
      (RHom[H](DerivedCategory.Q.obj (P : Cpx), DerivedCategory.Q.obj K)) := sorry

-- Proof sketch: use the direct representation theorem above for the derived-Hom clause. For the
-- K-flatness clause, replace `P^•` in the derived category by a bounded finite-projective complex
-- using perfectness, compare the two Hom complexes via the bounded-above projective invariance,
-- and then apply the K-flatness results from Section `15.59`.
/-- Lemma 15.99.4: if `P^•` is a bounded-above cochain complex of projective `R`-modules, `K^•`
is K-flat, and `P^•` represents a perfect object of `D(R)`, then the module-valued internal-Hom
complex `\mathrm{Hom}^\bullet(P^•, K^•)` is K-flat, and the canonical comparison with
`R\mathrm{Hom}_R(P^•, K^•)` is an isomorphism in the derived category. -/
theorem module_complex_internal_hom_isKFlat_and_represents_derivedInternalHom_of_isPerfect
    (H : RHomPkg)
    (P : ProjMinus) (K : Cpx)
    (hK : K.IsKFlat)
    (hperfect : DerivedCategory.IsPerfect (DerivedCategory.Q.obj (P : Cpx))) :
    (⟪P, K⟫).IsKFlat ∧
      IsIsomorphic
        (DerivedCategory.Q.obj ⟪P, K⟫)
        (RHom[H](DerivedCategory.Q.obj (P : Cpx), DerivedCategory.Q.obj K)) := sorry

-- Proof sketch: apply the main theorem and project to its first conjunct.
/-- The Hom complex against a K-flat complex is K-flat when the source complex is bounded above,
termwise projective, and perfect in the derived category. -/
theorem module_complex_internal_hom_isKFlat_of_isPerfect
    (P : ProjMinus) (K : Cpx)
    (hK : K.IsKFlat)
    (hperfect : DerivedCategory.IsPerfect (DerivedCategory.Q.obj (P : Cpx))) :
    (⟪P, K⟫).IsKFlat := sorry

end

end CategoryTheory
