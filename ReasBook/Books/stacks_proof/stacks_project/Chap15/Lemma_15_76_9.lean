import Mathlib
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Lemma_15_3_2
import StacksProject_2024.Chap15.Lemma_15_3_3
import StacksProject_2024.Chap15.Lemma_15_3_5
import StacksProject_2024.Chap15.Lemma_15_13_1
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_76_2

noncomputable section

open CategoryTheory
open ComplexShape
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]

local notation "ModR" => ModuleCat R
local notation "ModRI" => ModuleCat (R ⧸ I)
local notation "DModR" => DerivedCategory ModR
local notation "CpxR" => CochainComplex ModR ℤ
local notation "CpxRI" => CochainComplex ModRI ℤ
local notation "FiniteProjectiveClass" => finiteProjectiveModuleProperty R
local notation "FiniteProjectiveClassModI" => finiteProjectiveModuleProperty (R ⧸ I)
local notation "ReduceModI" => ModuleCat.extendScalars (Ideal.Quotient.mk I)
local notation "ReduceCpx" =>
  (Functor.mapHomologicalComplex (ModuleCat.extendScalars (Ideal.Quotient.mk I)) (up ℤ))

/- Domain-style sampling:
- primary domain: lifting bounded-above finite-projective derived representatives across reduction
  modulo a henselian ideal;
- sampled owner declarations:
  `finiteProjectiveModuleProperty`,
  `exists_finiteProjective_lift_of_henselianRing`,
  `CochainComplex.MinusWithTermsIn`,
  `DerivedCategory.IsPseudoCoherent`,
  `ModuleCat.extendScalars`;
- best owner abstraction: the chosen representative should remain a bounded-above owner complex
  `P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass`, while the quotient-side input should
  use the canonical owner `CochainComplex.MinusWithTermsIn FiniteProjectiveClassModI`; the bridge
  from quotient-side finite projectives to reduction data for `Lemma 15.76.2` is proof-only, via
  `exists_finiteProjective_lift_of_henselianRing`; pseudo-coherence remains on the derived object
  `K`;
- primitive data: the quotient-side bounded-above finite-projective complex `E`, the lifted
  bounded-above finite-projective representative `P`, and the comparison data in `D(R)` and after
  reduction modulo `I`;
- derived API: the existence of such representatives, recorded by the explicit comparison
  isomorphisms supplied by the owner theorem
  `exists_boundedAbove_representative_lifting_derivedReduction`; since those isomorphisms are
  genuine data rather than propositions, the source-facing statement below exposes them as
  explicit existential binders together with the termwise freeness consequence.

Source/core/bridge triage:
- `source-facing`: the lifting-existence statement of Lemma `15.76.9`;
- `core/canonical`: `finiteProjectiveModuleProperty`, `CochainComplex.MinusWithTermsIn`, and
  `K.IsPseudoCoherent`;
- `bridge/view`: the explicit comparison isomorphisms
  `K ≅ DerivedCategory.Q.obj (P : CpxR)` and
  `(ReduceCpx).obj (P : CpxR) ≅ (E : CpxRI)`. -/

-- Proof sketch: apply Lemma `15.76.2` with `PClass` equal to the class of finite projective
-- `R`-modules. The henselian-pair hypothesis and Lemma `15.13.1` lift each finite projective
-- `R/I`-term of `E`, Nakayama's lemma supplies the surjectivity condition via Lemma `15.3.5`, and
-- pseudo-coherence gives a bounded-above finite-projective representative of `K` directly from the
-- defining witness.
/-- Helper for Lemma 15.76.9: a termwise finite free complex is termwise finite projective after
forgetting freeness. -/
lemma finite_projective_of_termwise_finite_free
    {E : CpxR} (hE : E.IsTermwiseFiniteFree) (i : ℤ) :
    FiniteProjectiveClass (E.X i) := by
  -- Proof comment: unpack the finite/free package and keep only the finite/projective part.
  rcases hE.out i with ⟨hfree, hfinite⟩
  let _ : Module.Free R (E.X i) := hfree
  exact ⟨hfinite, inferInstance⟩

/-- Helper for Lemma 15.76.9: a pseudo-coherent derived object admits a bounded-above finite
projective representative. -/
lemma pseudoCoherent_exists_boundedAbove_finiteProjective_model
    (K : DModR) (hK : K.IsPseudoCoherent) :
    ∃ P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass,
      K ≅ DerivedCategory.Q.obj (P : CpxR) := by
  rcases hK with ⟨E, ⟨b, hEb⟩, hE, α, hα⟩
  -- Proof comment: repackage the bounded-above finite free witness from pseudo-coherence as a
  -- bounded-above finite projective complex degreewise.
  let P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hEb⟩⟩,
      finite_projective_of_termwise_finite_free (R := R) hE⟩
  let _ : IsIso α := hα
  exact ⟨P, (asIso α).symm⟩

/-- Helper for Lemma 15.76.9: a finite projective `R/I`-module lies in the reduction image of a
finite projective `R`-module over a henselian pair. -/
lemma finiteProjectiveClass_map_of_henselian_lift
    {M : ModRI} (hM : FiniteProjectiveClassModI M) :
    (FiniteProjectiveClass.map ReduceModI) M := by
  let Mbar : FiniteProjectiveModuleCat (R ⧸ I) := ⟨M, hM⟩
  obtain ⟨P, hP⟩ :=
    exists_finiteProjective_lift_of_henselianRing (R := R) (I := I) Mbar
  refine ⟨P.obj, P.2, ?_⟩
  -- Proof comment: forget the chosen lift in the finite-projective full subcategory back to the
  -- mapped object-property witness.
  simpa [Mbar, finiteProjectiveReductionFunctor] using hP

/-- Helper for Lemma 15.76.9: finite projective modules are closed under binary coproducts. -/
local instance finiteProjectiveClass_isClosedUnderBinaryCoproducts :
    CategoryTheory.ObjectProperty.IsClosedUnderBinaryCoproducts FiniteProjectiveClass := by
  refine CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro Z ⟨F, hF⟩
  let A := F.obj ⟨WalkingPair.left⟩
  let B := F.obj ⟨WalkingPair.right⟩
  have hA : FiniteProjectiveClass A := by
    simpa [A] using hF ⟨WalkingPair.left⟩
  have hB : FiniteProjectiveClass B := by
    simpa [B] using hF ⟨WalkingPair.right⟩
  let _ : Module.Finite R A := hA.1
  let _ : Module.Projective R A := hA.2
  let _ : Module.Finite R B := hB.1
  let _ : Module.Projective R B := hB.2
  have hBiprod : FiniteProjectiveClass (A ⊞ B : ModR) := by
    constructor
    · -- Proof comment: transport finite generation across the standard biproduct-product
      -- comparison.
      exact Module.Finite.of_equiv (ModuleCat.biprodIsoProd A B).toLinearEquiv
    · -- Proof comment: the same comparison transports projectivity from the product module.
      exact Module.Projective.of_equiv (ModuleCat.biprodIsoProd A B).toLinearEquiv
  have hCoprod : FiniteProjectiveClass (A ⨿ B : ModR) := by
    exact CategoryTheory.ObjectProperty.prop_of_iso
      (P := FiniteProjectiveClass) (biprod.isoCoprod A B) hBiprod
  -- Proof comment: every binary coproduct is canonically isomorphic to the coproduct of the
  -- underlying walking-pair diagram.
  exact CategoryTheory.ObjectProperty.prop_of_iso (P := FiniteProjectiveClass)
    (HasColimit.isoOfNatIso (diagramIsoPair F)).symm hCoprod

/-- Helper for Lemma 15.76.9: finite projective modules are stable under retracts. -/
local instance finiteProjectiveClass_isStableUnderRetracts :
    CategoryTheory.ObjectProperty.IsStableUnderRetracts FiniteProjectiveClass where
  of_retract r hY := by
    let _ : Module.Finite R r.Y := hY.1
    let _ : Module.Projective R r.Y := hY.2
    constructor
    · -- Proof comment: the retraction map is surjective because the section composes back to the
      -- identity on the retract.
      exact Module.Finite.of_surjective r.r.hom
        (fun x ↦ ⟨r.i.hom x, LinearMap.congr_fun (congrArg ModuleCat.Hom.hom r.retract) x⟩)
    · -- Proof comment: the same split identity exhibits the retract as a direct summand of a
      -- projective module.
      exact Module.Projective.of_split r.i.hom r.r.hom (by
        ext x
        exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom r.retract) x)

/-- Helper for Lemma 15.76.9: surjectivity after reduction modulo `I` upgrades to actual
surjectivity on finite projective modules once `I` lies in the Jacobson radical. -/
lemma finiteProjective_surjective_of_reduceModI_surjective
    (hI : I ≤ Ring.jacobson R)
    {P₁ P₂ : ModR} (f : P₁ ⟶ P₂)
    (hP₁ : FiniteProjectiveClass P₁) (hP₂ : FiniteProjectiveClass P₂)
    (hsurj : Function.Surjective ((ReduceModI.map f).hom)) :
    Function.Surjective f.hom := by
  have hquot : Function.Surjective (f.hom.quotientMapByIdeal I) := by
    exact (surjective_reduceModI_map_iff_quotientMapByIdeal (I := I) f).1 hsurj
  let _ : Module.Finite R P₂ := hP₂.1
  -- Proof comment: identify the reduced map with the concrete quotient map, then invoke the
  -- Jacobson-radical Nakayama criterion.
  exact surjective_of_quotientMap_surjective_of_le_ring_jacobson
    (I := I) f.hom hquot hI

/-- Helper for Lemma 15.76.9: a finite projective `R`-module is free when its reduction modulo
`I` is free over `R/I`. -/
lemma free_of_finiteProjective_of_free_reduction
    (hI : I ≤ Ring.jacobson R)
    {M : ModR} (hM : FiniteProjectiveClass M)
    (hred : Module.Free (R ⧸ I) (ReduceModI.obj M)) :
    Module.Free R M := by
  let _ : Module.Finite R M := hM.1
  let _ : Module.Projective R M := hM.2
  let _ : Module.Free (R ⧸ I) (ReduceModI.obj M) := hred
  have hReduceFinite : Module.Finite (R ⧸ I) (ReduceModI.obj M) := by
    simpa using (Module.Finite.base_change (R := R) (A := R ⧸ I) (M := M))
  let _ : Module.Finite (R ⧸ I) (ReduceModI.obj M) := hReduceFinite
  have hquot :
      Module.Free (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := by
    -- Proof comment: normalize reduction modulo `I` to the concrete quotient module model once.
    exact Module.Free.of_equiv
      ((reduceModI_obj_iso_quotient (I := I) M).symm.toLinearEquiv)
  let _ : Module.Free (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) := hquot
  let _ : Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
    Module.Finite.of_equiv (reduceModI_obj_iso_quotient (I := I) M).symm.toLinearEquiv
  obtain ⟨n, ⟨eQuot⟩⟩ :=
    CategoryTheory.ShortComplex.finite_free_linearEquiv_fin
      (R := R ⧸ I) (F := M ⧸ (I • (⊤ : Submodule R M)))
  let eTarget :
      (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I]
        ((Fin n → R) ⧸ (I • (⊤ : Submodule R (Fin n → R)))) :=
    eQuot.trans (free_pi_quotient_equiv (R := R) (I := I) n).symm
  -- Proof comment: lift the chosen quotient linear equivalence to an actual linear equivalence
  -- with the free module `R^n`.
  obtain ⟨eLift, -⟩ :=
    exists_lift_of_quotient_equiv_of_finite_projective
      (R := R) (I := I) (P := M) (P' := Fin n → R) hI eTarget
  exact Module.Free.of_equiv eLift

/-- Lemma 15.76.9: let `R` be a commutative ring, let `I ⊆ R` be an ideal, let `E^•` be a
bounded-above cochain complex of finite projective `R/I`-modules, and let `K` be an object of
`D(R)`. Assume `K \otimes_R^{\mathbf L} R/I` is represented by `E^•`, `K` is pseudo-coherent, and
`(R, I)` is a henselian pair. Then there exists a bounded-above cochain complex of finite
projective `R`-modules representing `K` whose reduction modulo `I` is isomorphic to `E^•`;
moreover, if `E^i` is free, then the lifted term `P^i` is free. -/
@[stacks 0BCE]
theorem exists_boundedAbove_finiteProjective_representative_lifting_derivedReduction
    (K : DModR)
    (E : CochainComplex.MinusWithTermsIn FiniteProjectiveClassModI)
    (hErep : Nonempty ((K ⊗[R]^L[(R ⧸ I)]) ≅ DerivedCategory.Q.obj (E : CpxRI)))
    (hK : K.IsPseudoCoherent) :
    ∃ P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass,
      ∃ eK : K ≅ DerivedCategory.Q.obj (P : CpxR),
        ∃ eE : (ReduceCpx).obj (P : CpxR) ≅ (E : CpxRI),
        ∀ i : ℤ, Module.Free (R ⧸ I) ((E : CpxRI).X i) → Module.Free R ((P : CpxR).X i) := by
  have hprojective : ∀ ⦃P : ModR⦄, FiniteProjectiveClass P → Projective P := by
    intro P hP
    let _ : Module.Projective R P := hP.2
    infer_instance
  have hsurj :
      ∀ ⦃P₁ P₂ : ModR⦄ (f : P₁ ⟶ P₂),
        FiniteProjectiveClass P₁ → FiniteProjectiveClass P₂ →
          Function.Surjective ((ReduceModI.map f).hom) →
            Function.Surjective f.hom := by
    intro P₁ P₂ f hP₁ hP₂ hf
    exact finiteProjective_surjective_of_reduceModI_surjective
      (R := R) (I := I) (Ideal.le_ring_jacobson_of_henselianRing (A := R) (I := I))
      f hP₁ hP₂ hf
  let E' : CochainComplex.MinusWithTermsIn (FiniteProjectiveClass.map ReduceModI) :=
    ⟨(E : CochainComplex.MinusWithTermsIn FiniteProjectiveClassModI),
      fun i ↦ finiteProjectiveClass_map_of_henselian_lift (R := R) (I := I) (E.term_mem i)⟩
  obtain ⟨P₀, eK₀⟩ :=
    pseudoCoherent_exists_boundedAbove_finiteProjective_model (R := R) (I := I) K hK
  -- Proof comment: specialize Lemma `15.76.2` to the finite-projective object property, with
  -- the quotient complex re-owned through henselian termwise lifting.
  obtain ⟨P, eK, eE₀⟩ :=
    exists_boundedAbove_representative_lifting_derivedReduction
      (I := I) (PClass := FiniteProjectiveClass) hprojective hsurj
      K E' hErep ⟨P₀, eK₀⟩
  have eE : (ReduceCpx).obj (P : CpxR) ≅ (E : CpxRI) := by
    simpa [E'] using eE₀
  refine ⟨P, eK, eE, ?_⟩
  intro i hEiFree
  let eX : ((ReduceCpx).obj (P : CpxR)).X i ≅ (E : CpxRI).X i :=
    { hom := eE.hom.f i
      inv := eE.inv.f i
      hom_inv_id := by
        ext x
        exact LinearMap.congr_fun
          (congrArg ModuleCat.Hom.hom (congrArg (fun f ↦ f.f i) eE.hom_inv_id)) x
      inv_hom_id := by
        ext x
        exact LinearMap.congr_fun
          (congrArg ModuleCat.Hom.hom (congrArg (fun f ↦ f.f i) eE.inv_hom_id)) x }
  have hReducedFree : Module.Free (R ⧸ I) (((ReduceCpx).obj (P : CpxR)).X i) := by
    let _ : Module.Free (R ⧸ I) ((E : CpxRI).X i) := hEiFree
    -- Proof comment: transfer freeness across the degree-`i` component of the reduction
    -- comparison isomorphism.
    exact Module.Free.of_equiv eX.toLinearEquiv
  have hTerm : FiniteProjectiveClass ((P : CpxR).X i) := by
    simpa using P.term_mem i
  -- Proof comment: rewrite the reduced term as scalar extension of the lifted finite-projective
  -- term, then apply the module-level free lifting theorem.
  exact free_of_finiteProjective_of_free_reduction
    (R := R) (I := I) (Ideal.le_ring_jacobson_of_henselianRing (A := R) (I := I))
    hTerm (by
      simpa [ReduceCpx, CategoryTheory.Functor.mapHomologicalComplex_obj_X] using hReducedFree)

end

end CategoryTheory
