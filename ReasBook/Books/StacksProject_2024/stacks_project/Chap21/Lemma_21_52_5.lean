import StacksProject_2024.Chap13.Definition_13_37_1
import StacksProject_2024.Chap18.«18_19_2_1»
import StacksProject_2024.Chap21.Lemma_21_12_2
import StacksProject_2024.Chap21.Lemma_21_20_7_core
import StacksProject_2024.Chap21.Lemma_21_52_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite
open scoped SheafOfModules.RingedSite.LocalizedStructureModuleExtensionByZero

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

variable [Abelian (SheafOfModules (ringSheaf J 𝒪))]

/- Domain-style sampling for Lemma 21.52.5:
- primary domain: compactness of the standard generators `((single0).obj (j![𝒪, U]))` in the derived
  category of sheaves of modules on a ringed site;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `CategoryTheory.Sheaf.H'`,
  `SheafOfModules.toSheaf`,
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor`,
  `SheafOfModules.cohomologyAtObject_isomorphic`,
  `DerivedCategory.singleFunctor`;
- best owner abstraction: the source-facing owner is the canonical degree-zero derived object
  `((single0).obj (j![𝒪, U]))`, and the hypothesis layer is best expressed through the canonical
  pointwise cohomology owner `F.H' p U`, realized functorially by
  `SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙ Sheaf.cohomologyPresheafFunctor J p` and compared to
  the module-valued derived functor through `SheafOfModules.cohomologyAtObject_isomorphic`;
- primitive data: the vanishing bound and direct-sum preservation for the ordinary site
  cohomology functors on `𝒪`-modules over the fixed object `U`;
- derived API: compactness of `((single0).obj (j![𝒪, U]))`.

Source/core/bridge triage:
- `source-facing`: the compactness criterion in Lemma `21.52.5`;
- `core/canonical`: `CategoryTheory.IsCompactObject` applied to
  `((single0).obj (j![𝒪, U]))`, viewed through the canonical
  `((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).H' p U`;
- `bridge/view`: the comparison isomorphism
  `SheafOfModules.cohomologyAtObject_isomorphic` from the module-valued derived functor to the
  canonical owner `((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).H' p U`.
-/

local notation "Mod𝒪" => SheafOfModules (ringSheaf J 𝒪)
local notation "single0" => DerivedCategory.singleFunctor Mod𝒪 (0 : ℤ)

/- Proof sketch: identify
`Hom (((single0).obj (j![𝒪, U])), K)` with `RΓ(U, K)`. The uniform bound on `H^p(U, ℱ)` gives
finite cohomological dimension for `Γ(U,-)`, and the direct-sum hypothesis makes direct sums of
injective resolutions acyclic for this functor. One then computes `RΓ(U, ⨁ i, K_i)` termwise on
K-injective representatives and obtains compatibility with arbitrary direct sums, which is exactly
compactness of `j![𝒪, U]` in degree zero. -/

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] [Abelian Mod𝒪] in
/-- The source-side cohomological-dimension hypothesis transfers directly to the project owner
`cohomologyAtObjectFunctor` above the same bound. -/
private lemma cohomologyAtObjectFunctor_obj_isZero_of_gt_bound
    (U : C) {d : ℤ}
    (hvanish :
      ∀ (p : ℕ) (_hp : d < p) (ℱ : Mod𝒪),
        IsZero (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).H' p U))
    (p : ℕ) (hp : d < p) (ℱ : Mod𝒪) :
    IsZero ((SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U).obj ℱ) := by
  -- Move from the source's `H^p(U, -)` owner to the project owner's right-derived functor.
  rcases SheafOfModules.cohomologyAtObject_isomorphic (ringSheaf J 𝒪) ℱ p U with ⟨e⟩
  exact e.isZero_iff.2 (hvanish p hp ℱ)

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] [Abelian Mod𝒪] in
/-- Positive objectwise cohomology over `U` vanishes on injective `𝒪`-modules in every strictly
positive degree. This is the source-facing form used when checking termwise acyclicity of chosen
injective complexes. -/
private lemma cohomologyAtObjectFunctor_obj_isZero_of_injective_pos
    (U : C) (p : ℕ) (hp : 0 < p) (ℱ : Mod𝒪) [Injective ℱ] :
    IsZero ((SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U).obj ℱ) := by
  -- Rewrite a positive degree as `n + 1` and apply the previously established successor case.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hp
  simpa [Nat.add_comm] using
    SheafOfModules.RingedSite.cohomologyAtObjectFunctor_obj_isZero_of_injective_succ
      J 𝒪 U n ℱ

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] [Abelian Mod𝒪] in
/-- If all objectwise cohomology functors commute with direct sums, then every direct sum of
injective `𝒪`-modules is acyclic for positive objectwise cohomology over `U`. This is the
source-facing package needed later for the coproduct of chosen K-injective representatives. -/
private lemma cohomologyAtObjectFunctor_obj_isZero_of_coproduct_of_injective_pos
    (U : C) {ι : Type (u + 1)} (A : ι → Mod𝒪) [HasCoproduct A]
    (hcomm :
      ∀ (p : ℕ) (κ : Type (u + 1)),
        PreservesColimitsOfShape (Discrete κ)
          (SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U))
    [∀ i, Injective (A i)]
    (p : ℕ) (hp : 0 < p) :
    IsZero ((SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U).obj (∐ A)) := by
  -- Rewrite the positive degree as `n + 1` so the direct-sum vanishing lemma applies.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hp
  simpa [Nat.add_comm] using
    SheafOfModules.RingedSite.cohomologyAtObjectFunctor_obj_isZero_of_coproduct_of_injective_succ
      J 𝒪 U n A (hcomm (n + 1) ι)

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] [Abelian Mod𝒪] in
 /-- Bridge API for Lemma 21.52.5: after forgetting the module-valued cohomology presheaf and
 evaluating at `U`, the project owner `cohomologyAtObjectFunctor` agrees with the source-side
 additive functor `ℱ ↦ H^p(U, ℱ)` on the underlying abelian sheaf. -/
theorem cohomologyAtObjectFunctor_underlyingAbelian_isomorphic
    (U : C) (p : ℕ) :
    IsIsomorphic
      (SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U)
      (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
        Sheaf.cohomologyPresheafFunctor J p ⋙
          (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) := by
  rcases SheafOfModules.cohomologyPresheafFunctor_toPresheaf_isomorphic (ringSheaf J 𝒪) p with
    ⟨e⟩
  exact ⟨by
    simpa [SheafOfModules.cohomologyAtObjectFunctor] using
      Functor.isoWhiskerRight e
        ((CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))⟩

omit [HasBinaryProducts C] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})] [Abelian Mod𝒪] in
/-- The source-side direct-sum hypothesis on the canonical owner `ℱ ↦ H^p(U, ℱ)` transports to
the project owner `cohomologyAtObjectFunctor`, so the proof may use the module-valued right
derived functor internally without changing the public statement. -/
theorem cohomologyAtObjectFunctor_preservesColimitsOfShape_of_source
    (U : C) (p : ℕ) (ι : Type w)
    (hcomm :
      PreservesColimitsOfShape (Discrete ι)
        (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
          Sheaf.cohomologyPresheafFunctor J p ⋙
            (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))) :
    PreservesColimitsOfShape (Discrete ι)
      (SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U) := by
  have hIso :
      IsIsomorphic
        (SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U)
        (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
          Sheaf.cohomologyPresheafFunctor J p ⋙
            (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) :=
    cohomologyAtObjectFunctor_underlyingAbelian_isomorphic U p
  rcases hIso with ⟨e⟩
  let _ :
      PreservesColimitsOfShape (Discrete ι)
        (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
          Sheaf.cohomologyPresheafFunctor J p ⋙
            (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) := hcomm
  exact CategoryTheory.Limits.preservesColimitsOfShape_of_natIso e.symm

/-- Lemma 21.52.5: if there is an integer `d` such that `H^p(U, ℱ) = 0` for all `p > d` and all
sheaves `ℱ` of `𝒪`-modules, and if each functor `ℱ ↦ H^p(U, ℱ)` commutes with arbitrary direct
sums, then the degree-zero derived object `((single0).obj (j![𝒪, U]))` is compact in
`DerivedCategory Mod𝒪`. -/
@[stacks 094D]
theorem localizedStructureModuleExtensionByZeroDegreeZero_isCompactObject_of_finiteCohomologicalDimension_and_directSumCompatibility
    (U : C)
    (hvanish :
      ∃ d : ℤ, ∀ (p : ℕ) (hp : d < p) (ℱ : Mod𝒪),
        IsZero (((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).H' p U))
    (hcomm :
      ∀ (p : ℕ) (ι : Type (u + 1)),
        PreservesColimitsOfShape (Discrete ι)
          (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
            Sheaf.cohomologyPresheafFunctor J p ⋙
              (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))) :
    IsCompactObject ((single0).obj (j![𝒪, U])) := by
  obtain ⟨d, hvanishSource⟩ := hvanish
  have hvanishFunctor :
      ∀ (p : ℕ) (_hp : d < p) (ℱ : Mod𝒪),
        IsZero ((SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U).obj ℱ) := by
    intro p hp ℱ
    exact cohomologyAtObjectFunctor_obj_isZero_of_gt_bound U hvanishSource p hp ℱ
  have hcommFunctor :
      ∀ (p : ℕ) (ι : Type (u + 1)),
        PreservesColimitsOfShape (Discrete ι)
          (SheafOfModules.cohomologyAtObjectFunctor (ringSheaf J 𝒪) p U) := by
    intro p ι
    exact cohomologyAtObjectFunctor_preservesColimitsOfShape_of_source U p ι (hcomm p ι)
  sorry

end

end SheafOfModules.RingedSite
