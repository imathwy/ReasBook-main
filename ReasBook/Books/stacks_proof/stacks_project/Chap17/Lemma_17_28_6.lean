import Mathlib
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import stacks_proof.stacks_project.Chap17.Definition_17_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open PresheafOfModules.DifferentialsConstruction
open scoped RelativeDerivation

noncomputable section

universe u

namespace TopCat.Sheaf

/- Domain-style sampling for Lemma 17.28.6:
- primary domain: inverse image compatibility for sheaves of relative differentials;
- sampled owner declarations:
  `TopCat.Sheaf.relativeDifferentials`,
  `TopCat.Sheaf.relativeDifferentials_def`,
  `TopCat.Sheaf.pullback`,
  `SheafOfModules.pullback`,
  `SheafOfModules.sheafificationCompPullback`;
- best owner abstraction: the source-facing owner `TopCat.Sheaf.relativeDifferentials`, with the
  inverse-image comparison expressed by the actual module pullback and the transported
  pulled-back owner over the raw `RingCat`-valued structure sheaf;
- primitive data: the owner `relativeDifferentials`, the actual pullback functor
  `SheafOfModules.pullback`, and the canonical restrict-scalars transport along
  `pullbackRingSheafIso`;
- derived API: the ring-sheaf comparison bridge `pullbackRingSheafIso`, the direct comparison
  isomorphism `inverseImage_relativeDifferentialsIso`, its compatibility property on universal
  derivations, and the theorem-level `IsIsomorphic` companion.

Source/core/bridge triage:
- `core/canonical`: `TopCat.Sheaf.relativeDifferentials`;
- `bridge/view`: this lemma compares the actual inverse image of `Ω(φ)` with the same owner
  applied to the pulled-back morphism, then transported across the canonical ring-sheaf
  comparison;
- the public API should therefore expose that transport by a direct comparison isomorphism, rather
  than by a public `Classical.choice` witness extracted from an existence theorem. -/

/-- Helper for Chap17 Lemma 17 28 6: forgetting commutativity preserves sheafification on the
opens site of a topological space. -/
private theorem opensPreservesSheafificationForgetToRingCat
    (Y : TopCat.{u}) :
    (Opens.grothendieckTopology Y).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u}) := by
  -- Proof comment: isolate the generic preservation instance in its own declaration so the
  -- expensive typeclass search runs under a fresh elaboration budget.
  -- TODO: force the concrete `PreservesSheafification` owner instance for
  -- `forget₂ CommRingCat RingCat` without triggering the local typeclass timeout.
  sorry

/-- Helper for Lemma 17.28.6: the canonical ring-sheaf comparison between pulling back before or
after forgetting commutativity. -/
noncomputable abbrev pullbackRingSheafIso
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    (O : X.Sheaf CommRingCat.{u}) :
    ringSheaf ((pullback CommRingCat.{u} f).obj O) ≅
      (pullback RingCat.{u} f).obj (ringSheaf O) :=
  letI :
      (Opens.grothendieckTopology Y).PreservesSheafification
        (forget₂ CommRingCat RingCat.{u}) :=
    opensPreservesSheafificationForgetToRingCat Y
  let P : (Opens Y)ᵒᵖ ⥤ CommRingCat.{u} :=
    (TopCat.Presheaf.pullback CommRingCat.{u} f).obj O.1
  let h₁ :
      (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).obj
          ((presheafToSheaf (Opens.grothendieckTopology Y) CommRingCat.{u}).obj P) ≅
        (presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).obj
          (P ⋙ forget₂ CommRingCat RingCat.{u}) :=
    ((CategoryTheory.sheafComposeNatIso
        (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat.{u})
        (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology Y) CommRingCat.{u})
        (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology Y) RingCat.{u})).app
      P).symm
  let h₂ :
      (presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).obj
          (P ⋙ forget₂ CommRingCat RingCat.{u}) ≅
        (forget RingCat.{u} X ⋙ TopCat.Presheaf.pullback RingCat.{u} f ⋙
            presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).obj
          (ringSheaf O) := by
    let hP :
        P ⋙ forget₂ CommRingCat RingCat.{u} ≅
          (TopCat.Presheaf.pullback RingCat.{u} f).obj (ringSheaf O).1 := by
      -- Normalize the forgotten commutative-ring pullback to the raw ring-valued pullback.
      simpa [P, ringSheaf, TopCat.Presheaf.pullback] using
        ((Functor.lanCompIsoOfPreserves
          (L := (Opens.map f).op)
          (G := forget₂ CommRingCat RingCat.{u})).app O.1)
    exact (presheafToSheaf (Opens.grothendieckTopology Y) RingCat.{u}).mapIso hP
  -- Compare the two pullback constructions by inserting the sheafification/forgetful bridge.
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).mapIso
      ((TopCat.Sheaf.pullbackIso CommRingCat.{u} f).app O) ≪≫
    h₁ ≪≫
    h₂ ≪≫
    ((TopCat.Sheaf.pullbackIso RingCat.{u} f).app (ringSheaf O)).symm

/-- The canonical inverse-image comparison for relative differentials. -/
noncomputable abbrev inverseImage_relativeDifferentialsIso
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    (SheafOfModules.pullback
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).obj
      Ω(φ) ≅
      (SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
        Ω((pullback CommRingCat.{u} f).map φ) :=
  -- Route correction: the local construction reduces to the direct inverse-image comparison iso,
  -- but its proof currently still depends on the missing opens-site pullback presentation.
  -- TODO: construct the comparison by descending the pulled-back universal derivation and prove
  -- it is an isomorphism by representer uniqueness for the two derivation functors.
  sorry

/-- The source-facing compatibility property saying that, after adjunction, a morphism from the
inverse image of `Ω(φ)` to the pulled-back cotangent sheaf carries the universal derivation
`d(t)` to the pulled-back universal derivation `d(f^\sharp t)` on every local section `t`. -/
def inverseImage_relativeDifferentialsComparisonProperty
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    (τ :
      (SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).obj
        Ω(φ) ⟶
        (SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
          Ω((pullback CommRingCat.{u} f).map φ)) : Prop :=
  ∀ {U : (Opens X)ᵒᵖ} (t : O₂.obj.obj U),
    let U' := (Opens.map f).op.obj U
    let fSharpU := ((pullbackPushforwardAdjunction CommRingCat.{u} f).unit.app O₂).hom.app U
    ((((SheafOfModules.pullbackPushforwardAdjunction
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).homEquiv _ _)
      τ).val.app U)
      (((relativeDifferential φ).app U).d t) =
        ((relativeDifferential ((pullback CommRingCat.{u} f).map φ)).app U').d (fSharpU t)

/-- The canonical inverse-image comparison isomorphism is characterized by compatibility with the
pulled-back universal derivation. -/
theorem inverseImage_relativeDifferentialsIso_characterizing
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    inverseImage_relativeDifferentialsComparisonProperty f φ
      (inverseImage_relativeDifferentialsIso f φ).hom := by
  -- TODO: once the local comparison iso is reconstructed, prove the generator formula by
  -- reducing to the sectionwise pulled-back universal derivation.
  -- The intended closing step is `relativeDifferentialDesc_fac` for the forward comparison map
  -- obtained from the pullback-pushforward adjunction.
  sorry

/-- Helper for Chap17 Lemma 17 28 6: the fixed pullback-pushforward adjunction detects equality
of comparison morphisms after transposition. -/
private theorem inverseImageRelativeDifferentialsAdjunction_injective
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    {τ₁ τ₂ :
      (SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).obj
        Ω(φ) ⟶
        (SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
          Ω((pullback CommRingCat.{u} f).map φ)}
    (h :
      (((SheafOfModules.pullbackPushforwardAdjunction
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).homEquiv
            _ _) τ₁) =
        (((SheafOfModules.pullbackPushforwardAdjunction
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).homEquiv
            _ _) τ₂)) :
    τ₁ = τ₂ := by
  -- Proof comment: package the adjunction-side injectivity once so the uniqueness proof can
  -- focus on the universal-derivation argument rather than the repeated hom-equivalence term.
  exact
    ((SheafOfModules.pullbackPushforwardAdjunction
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).homEquiv
      _ _).injective h

/-- A morphism from the inverse image of `Ω(φ)` to the pulled-back cotangent sheaf is the
canonical one once its adjoint sends `d(t)` to the pulled-back universal differential on every
open set. -/
theorem inverseImage_relativeDifferentialsIso_unique
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    (τ :
      (SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).obj
        Ω(φ) ⟶
        (SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
          Ω((pullback CommRingCat.{u} f).map φ))
    (hτ : inverseImage_relativeDifferentialsComparisonProperty f φ τ) :
    τ = (inverseImage_relativeDifferentialsIso f φ).hom := by
  -- Compare adjoints under the pullback-pushforward adjunction and then use that `Ω(φ)` is
  -- generated by the universal derivation.
  apply inverseImageRelativeDifferentialsAdjunction_injective (f := f) (φ := φ)
  apply TopCat.Sheaf.relativeDifferential_postcomp_injective φ
  ext U t
  change ((((SheafOfModules.pullbackPushforwardAdjunction
      ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).homEquiv
        _ _) τ).val.app U)
      (((relativeDifferential φ).app U).d t) =
    ((((SheafOfModules.pullbackPushforwardAdjunction
        ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).homEquiv
          _ _)
        (inverseImage_relativeDifferentialsIso f φ).hom).val.app U)
      (((relativeDifferential φ).app U).d t)
  exact Eq.trans (hτ (U := U) t)
    ((inverseImage_relativeDifferentialsIso_characterizing f φ (U := U) t).symm)

/-- Lemma 17.28.6: there exists a unique morphism from the inverse image of `Ω(φ)` to the
relative differentials of the pulled-back morphism whose adjoint carries `d(t)` to the pulled-back
universal derivation. The canonical isomorphism above is its unique witness. -/
@[stacks 08RR]
theorem existsUnique_inverseImage_relativeDifferentialsComparison
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    ∃! τ :
        (SheafOfModules.pullback
            ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).obj
          Ω(φ) ⟶
          (SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
            Ω((pullback CommRingCat.{u} f).map φ),
      inverseImage_relativeDifferentialsComparisonProperty f φ τ := by
  refine ⟨(inverseImage_relativeDifferentialsIso f φ).hom, ?_, ?_⟩
  · exact inverseImage_relativeDifferentialsIso_characterizing f φ
  · intro τ hτ
    exact inverseImage_relativeDifferentialsIso_unique f φ τ hτ

/-- The inverse image of `Ω(φ)` is canonically identified with the relative differentials of the
pulled-back morphism, expressed over the canonical pulled-back `RingCat`-valued structure sheaf. -/
theorem inverseImage_relativeDifferentials_isIsomorphic
    {X Y : TopCat.{u}} (f : Y ⟶ X)
    {O₁ O₂ : X.Sheaf CommRingCat.{u}} (φ : O₁ ⟶ O₂) :
    IsIsomorphic
      ((SheafOfModules.pullback
          ((pullbackPushforwardAdjunction RingCat.{u} f).unit.app (ringSheaf O₂))).obj
        Ω(φ))
      ((SheafOfModules.restrictScalars (pullbackRingSheafIso f O₂).inv).obj
        Ω((pullback CommRingCat.{u} f).map φ)) := by
  exact ⟨inverseImage_relativeDifferentialsIso f φ⟩

end TopCat.Sheaf
