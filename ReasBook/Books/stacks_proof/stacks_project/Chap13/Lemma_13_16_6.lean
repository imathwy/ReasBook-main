import Mathlib
import StacksProject_2024.Chap12.Definition_12_12_1
import StacksProject_2024.Chap12.Lemma_12_12_4
import StacksProject_2024.Chap13.Lemma_13_4_21
import StacksProject_2024.Chap13.Lemma_13_4_22
import StacksProject_2024.Chap13.Lemma_13_16_3
import StacksProject_2024.Chap13.Lemma_13_16_4

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section BoundedBelow

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable [RF.CommShift ℤ] [RF.IsTriangulated]

/- Domain-style sampling for Lemma 13.16.6:
- primary domain: bounded-below right derived functors of additive functors between abelian
  categories, expressed through the canonical triangulated-to-cohomological `δ`-functor pipeline;
- sampled owner declarations:
  `ShortComplex.ShortExact.singleδ`,
  `DeltaFunctor.postcomposeExactFunctor`,
  `DeltaFunctor.toCohomologicalDeltaFunctor`,
  `Functor.boundedBelowRightDerived`,
  `single0ToDplus`;
- best owner abstraction: the public source-facing object is the canonical bounded-below
  cohomological `δ`-functor whose degree-`n` term is `RF.boundedBelowRightDerived n`, obtained by
  first building the bounded-below `DeltaFunctor` on degree-zero objects and then applying the
  owner construction `DeltaFunctor.toCohomologicalDeltaFunctor`;
- primitive data: the explicit bounded-below degree-zero `DeltaFunctor` and the exact functor
  `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`;
- derived API: the named cohomological `δ`-functor `boundedBelowRightDerivedDeltaFunctor RF`, its
  degreewise identification with `RF.boundedBelowRightDerived n`, and the universality criterion
  once objects embed into bounded-below right-acyclic objects.

Source/core/bridge triage:
- `source-facing`: the bounded-below right-derived cohomological `δ`-functor and its universality.
- `core/canonical`: `DeltaFunctor`, `DeltaFunctor.postcomposeExactFunctor`,
  `DeltaFunctor.toCohomologicalDeltaFunctor`, and `CohomologicalDeltaFunctor.IsUniversal`.
- `bridge/view`: the bounded-below degree-zero `DeltaFunctor` on `single0ToDplus 𝒜`, plus the
  later unbounded comparison with `Functor.rightDerived`.

This file should therefore expose the source-facing cohomological `δ`-functor by direct reuse of
the chapter’s `DeltaFunctor` owners, not by existentially packaging the connecting maps. -/

local notation "plusιA" => ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜)))
local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ)))
local notation "H" => DerivedCategory.homologyFunctor ℬ

private noncomputable def single0ToDerivedIso :
    single0ToDplus 𝒜 ⋙ plusιA ≅ DerivedCategory.singleFunctor 𝒜 0 :=
  (𝟭 𝒜).single0PlusToSingleFunctorIso ≪≫ Functor.leftUnitor _

/-- Helper for Lemma 13.16.6: the short exact sequence triangle on degree-zero objects in
`D⁺(\mathcal A)` is obtained by transporting the usual single-complex triangle in `D(\mathcal A)`.
-/
private noncomputable def single0ToDplusTriangle {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    Triangle (D⁺(𝒜)) :=
  Triangle.mk
    ((single0ToDplus 𝒜).map S.f)
    ((single0ToDplus 𝒜).map S.g)
    (plusιA.preimage
      ((single0ToDerivedIso.hom.app S.X₃) ≫ hS.singleδ ≫
        ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁)))

/-- Helper for Lemma 13.16.6: the transported degree-zero triangle attached to a short exact
sequence is distinguished in `D⁺(\mathcal A)`. -/
private theorem single0ToDplus_triangle_distinguished {S : ShortComplex 𝒜}
    (hS : S.ShortExact) :
    single0ToDplusTriangle (𝒜 := 𝒜) hS ∈ distTriang (D⁺(𝒜)) := by
  -- Compare the transported bounded-below triangle with the standard single-object triangle in
  -- the ambient derived category.
  rw [← plusιA.map_distinguished_iff]
  change
    Triangle.mk
        (plusιA.map ((single0ToDplus 𝒜).map S.f))
        (plusιA.map ((single0ToDplus 𝒜).map S.g))
        (plusιA.map
            (plusιA.preimage
              ((single0ToDerivedIso.hom.app S.X₃) ≫ hS.singleδ ≫
                ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
                  (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁))) ≫
          (plusιA.commShiftIso (1 : ℤ)).hom.app ((single0ToDplus 𝒜).obj S.X₁)) ∈
      distTriang (D(𝒜))
  rw [plusιA.map_preimage]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _
    (single0ToDerivedIso.app S.X₁)
    (single0ToDerivedIso.app S.X₂)
    (single0ToDerivedIso.app S.X₃)
    ?_ ?_ ?_
  · -- The first edge is just naturality of the comparison `A[0] ↦ A[0]`.
    simpa using single0ToDerivedIso.hom.naturality S.f
  · -- The second edge is identical for `S.g`.
    simpa using single0ToDerivedIso.hom.naturality S.g
  · -- After cancelling the shift-commutation isomorphisms, the third edge is `hS.singleδ`.
    have hshift :
        (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
            (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁) =
          𝟙 (((DerivedCategory.singleFunctor 𝒜 0).obj S.X₁)⟦(1 : ℤ)⟧) := by
      simpa using
        congrArg
          (fun k ↦ (shiftFunctor (D(𝒜)) (1 : ℤ)).map k)
          (single0ToDerivedIso.inv_hom_id_app S.X₁)
    have hthird :
        single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                (Functor.commShiftIso plusιA (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                  (Functor.commShiftIso plusιA (1 : ℤ)).hom.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁) =
          single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
      calc
        single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                (Functor.commShiftIso plusιA (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                  (Functor.commShiftIso plusιA (1 : ℤ)).hom.app ((single0ToDplus 𝒜).obj S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁)
            =
          single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁) := by
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫
                hS.singleδ ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                    k ≫
                      (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁))
              ((Functor.commShiftIso plusιA (1 : ℤ)).inv_hom_id_app ((single0ToDplus 𝒜).obj S.X₁))
        _ = single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
          calc
            single0ToDerivedIso.hom.app S.X₃ ≫
                hS.singleδ ≫
                  (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.inv.app S.X₁) ≫
                    (shiftFunctor (D(𝒜)) (1 : ℤ)).map (single0ToDerivedIso.hom.app S.X₁)
                =
              single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫
                𝟙 (((DerivedCategory.singleFunctor 𝒜 0).obj S.X₁)⟦(1 : ℤ)⟧) := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫ k) hshift
            _ = single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ := by
              simp
    simpa [single0ToDplusTriangle, ShortComplex.ShortExact.singleTriangle, Category.assoc] using
      hthird

/-- Helper for Lemma 13.16.6: the transported connecting morphisms on degree-zero objects are
natural in morphisms of short exact sequences. -/
private theorem single0ToDplus_delta_naturality {S T : ShortComplex 𝒜}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) :
    CommSq
      ((single0ToDplus 𝒜).map φ.τ₃)
      (plusιA.preimage
        ((single0ToDerivedIso.hom.app S.X₃) ≫ hS.singleδ ≫
          ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁)))
      (plusιA.preimage
        ((single0ToDerivedIso.hom.app T.X₃) ≫ hT.singleδ ≫
          ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj T.X₁)))
      (((single0ToDplus 𝒜).map φ.τ₁)⟦(1 : ℤ)⟧') := by
  -- Apply the fully faithful inclusion `D⁺(𝒜) ⥤ D(𝒜)` and reduce to naturality of `singleδ`.
  apply CommSq.mk
  apply plusιA.map_injective
  have hsingleδ :
      (DerivedCategory.singleFunctor 𝒜 0).map φ.τ₃ ≫ hT.singleδ =
        hS.singleδ ≫ ((DerivedCategory.singleFunctor 𝒜 0).map φ.τ₁)⟦(1 : ℤ)⟧' := by
    simpa using
      (ShortComplex.ShortExact.singleTriangle.map (h₁ := hS) (h₂ := hT) φ).comm₃
  have hinv :
      ((DerivedCategory.singleFunctor 𝒜 0).map φ.τ₁)⟦(1 : ℤ)⟧' ≫
          ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') =
        ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          (plusιA.map ((single0ToDplus 𝒜).map φ.τ₁))⟦(1 : ℤ)⟧' := by
    simpa using
      congrArg
        (fun k ↦ (shiftFunctor (D(𝒜)) (1 : ℤ)).map k)
        (single0ToDerivedIso.inv.naturality φ.τ₁)
  -- Rewrite the left and right transports separately, then insert the naturality square for
  -- `singleδ`.
  calc
    plusιA.map ((single0ToDplus 𝒜).map φ.τ₃) ≫
        (single0ToDerivedIso.hom.app T.X₃) ≫
          hT.singleδ ≫
            ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj T.X₁)
        =
      single0ToDerivedIso.hom.app S.X₃ ≫
        (DerivedCategory.singleFunctor 𝒜 0).map φ.τ₃ ≫
          hT.singleδ ≫
            ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj T.X₁) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ hT.singleδ ≫
            ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj T.X₁))
          (single0ToDerivedIso.hom.naturality φ.τ₃)
    _ =
      single0ToDerivedIso.hom.app S.X₃ ≫
        hS.singleδ ≫
          ((DerivedCategory.singleFunctor 𝒜 0).map φ.τ₁)⟦(1 : ℤ)⟧' ≫
            ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj T.X₁) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫
            k ≫
              ((single0ToDerivedIso.inv.app T.X₁)⟦(1 : ℤ)⟧') ≫
                (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj T.X₁))
          hsingleδ
    _ =
      single0ToDerivedIso.hom.app S.X₃ ≫
        hS.singleδ ≫
          ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.map ((single0ToDplus 𝒜).map φ.τ₁))⟦(1 : ℤ)⟧' ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj T.X₁) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫ hS.singleδ ≫
            k ≫
              (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj T.X₁))
          hinv
    _ =
      single0ToDerivedIso.hom.app S.X₃ ≫
        hS.singleδ ≫
          ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
            (plusιA.commShiftIso (1 : ℤ)).inv.app ((single0ToDplus 𝒜).obj S.X₁) ≫
              plusιA.map (((single0ToDplus 𝒜).map φ.τ₁)⟦(1 : ℤ)⟧') := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ single0ToDerivedIso.hom.app S.X₃ ≫
            hS.singleδ ≫
              ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
                k)
          (plusιA.commShiftIso_inv_naturality ((single0ToDplus 𝒜).map φ.τ₁) (1 : ℤ))

-- Proof sketch: transport the canonical connecting morphism `hS.singleδ` for short exact
-- sequences in `𝒜` into the bounded-below derived category `D⁺(𝒜)` via the explicit
-- degree-zero comparison `single0PlusToDerivedIso`. The distinguished-triangle and naturality
-- fields are the corresponding transported versions of `hS.singleTriangle_distinguished` and the
-- naturality of `singleδ`.
/-- The canonical `δ`-functor on degree-zero objects
`single0ToDplus 𝒜 : 𝒜 ⥤ D^+(\mathcal A)`. -/
noncomputable def single0ToDplusDeltaFunctor :
    DeltaFunctor 𝒜 D⁺(𝒜) where
  toFunctor := single0ToDplus 𝒜
  additive := inferInstance
  δ := fun {S} hS ↦
    ObjectProperty.homMk
      ((single0ToDerivedIso.hom.app S.X₃) ≫ hS.singleδ ≫
        ((single0ToDerivedIso.inv.app S.X₁)⟦(1 : ℤ)⟧') ≫
          ((Functor.commShiftIso plusιA (1 : ℤ)).inv.app
            ((single0ToDplus 𝒜).obj S.X₁)))
  map_distinguished := fun {S} hS ↦ single0ToDplus_triangle_distinguished (𝒜 := 𝒜) hS
  δ_naturality := fun {S T} hS hT φ ↦
    single0ToDplus_delta_naturality (𝒜 := 𝒜) hS hT φ

/-- The underlying functor of `single0ToDplusDeltaFunctor` is the canonical degree-zero embedding
`𝒜 ⥤ D^+(\mathcal A)`. -/
@[simp] theorem single0ToDplusDeltaFunctor_toFunctor :
    (single0ToDplusDeltaFunctor : DeltaFunctor 𝒜 D⁺(𝒜)).toFunctor = single0ToDplus 𝒜 :=
  rfl

private noncomputable def boundedBelowRightDerivedDeltaOwner :
    DeltaFunctor 𝒜 (D(ℬ)) :=
  (single0ToDplusDeltaFunctor.postcomposeExactFunctor RF).postcomposeExactFunctor plusι

private theorem boundedBelowRightDerivedDeltaOwner_hneg (X : 𝒜) :
    IsZero (((H 0).shift (-1)).obj
      ((boundedBelowRightDerivedDeltaOwner RF).toFunctor.obj X)) := by
  -- Normalize the owner to the degree `-1` bounded-below right derived functor and then use the
  -- negative-degree vanishing theorem.
  have hzero : IsZero (RF.boundedBelowRightDerived (-1 : ℤ)) :=
    boundedBelowRightDerived_isZero_of_neg (RF := RF) (-1) (by omega)
  rw [Functor.isZero_iff] at hzero
  simpa [boundedBelowRightDerivedDeltaOwner, Functor.boundedBelowRightDerived,
    DeltaFunctor.postcomposeExactFunctor_toFunctor, DerivedCategory.shift_homologyFunctor] using
    hzero X

/-- Lemma 13.16.6 (1): for an exact bounded-below right derived functor
`RF : D^+(\mathcal A) ⥤ D^+(\mathcal B)`, the functors
`RF.boundedBelowRightDerived n`, i.e. `A ↦ H^n((RF(A[0])) : D(\mathcal B))`, carry canonical
connecting morphisms making them into a cohomological `δ`-functor. -/
@[stacks 05TE]
noncomputable def boundedBelowRightDerivedDeltaFunctor :
    CohomologicalDeltaFunctor 𝒜 ℬ :=
  DeltaFunctor.toCohomologicalDeltaFunctor
    (boundedBelowRightDerivedDeltaOwner RF) (H 0)
    (boundedBelowRightDerivedDeltaOwner_hneg RF)

/-- The degree-`n` branch of `boundedBelowRightDerivedDeltaFunctor RF` is the canonical functor
`A ↦ H^n((RF(A[0])) : D(\mathcal B))`. -/
@[simp] theorem boundedBelowRightDerivedDeltaFunctor_obj (n : ℕ) :
    ((boundedBelowRightDerivedDeltaFunctor RF n).obj) = RF.boundedBelowRightDerived n := by
  -- This is just the owner normalization from `toCohomologicalDeltaFunctor` plus the standard
  -- identification `(H^0).shift n = H^n`.
  simp [boundedBelowRightDerivedDeltaFunctor, boundedBelowRightDerivedDeltaOwner,
    Functor.boundedBelowRightDerived, DeltaFunctor.postcomposeExactFunctor_toFunctor,
    DerivedCategory.shift_homologyFunctor]

end BoundedBelow

section Universal

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

variable (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F]
variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]
variable [RF.CommShift ℤ] [RF.IsTriangulated]

/-- Helper for Lemma 13.16.6: positive degrees of the bounded-below right-derived
cohomological `δ`-functor are weakly effaceable under monomorphisms into bounded-below
right-acyclic objects. -/
private theorem boundedBelowRightDerived_higherDegreesWeaklyEffaceable
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      IsBoundedBelowRightAcyclicForAdditiveFunctor F Y)
    (n : ℕ) (hn : 0 < n) (X : 𝒜) :
    ∃ (Y : 𝒜) (u : X ⟶ Y), Mono u ∧ ((boundedBelowRightDerivedDeltaFunctor RF n).obj.map u) = 0 := by
  rcases hacyclic X with ⟨Y, u, hu, hY⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  -- Translate bounded-below acyclicity of `Y` into vanishing of the higher right derived functors.
  have hvanish :
      IsZero ((RF.boundedBelowRightDerived (m + 1)).obj Y) :=
    (isBoundedBelowRightAcyclicForAdditiveFunctor_iff_boundedBelowHigherRightDerivedVanishes
      (F := F) (RF := RF) (α := α) Y).1 hY m
  refine ⟨Y, u, hu, ?_⟩
  -- A morphism into a zero target vanishes.
  simpa [boundedBelowRightDerivedDeltaFunctor_obj (RF := RF) (m + 1)] using
    hvanish.eq_of_tgt (((RF.boundedBelowRightDerived (m + 1)).obj).map u) 0

-- Proof sketch: if every object embeds into a bounded-below right-acyclic object, then Lemma
-- `13.16.4` turns that acyclicity into vanishing of all positive functors
-- `RF.boundedBelowRightDerived (n + 1)` on the chosen target object. Hence every positive degree
-- of `T` is weakly effaceable, and Lemma
-- `12.12.4` gives universality.
/-- Lemma 13.16.6 (2): if `F` is left exact and every object of `𝒜` is a subobject of an object
right acyclic for the bounded-below right derived functor of `F`, then the canonical bounded-
below right-derived cohomological `δ`-functor is universal. -/
@[stacks 05TE]
theorem boundedBelowRightDerivedDeltaFunctor_isUniversal
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      IsBoundedBelowRightAcyclicForAdditiveFunctor F Y) :
    CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF) := by
  -- Chapter 12 reduces universality to weak effaceability of all positive degrees.
  refine CohomologicalDeltaFunctor.isUniversal_of_higherDegreesWeaklyEffaceable
    (boundedBelowRightDerivedDeltaFunctor RF) ?_
  intro n hn X
  exact boundedBelowRightDerived_higherDegreesWeaklyEffaceable
    (F := F) (RF := RF) (α := α) hacyclic n hn X

end Universal

section UnboundedCompanion

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} ℬ]

variable (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F] [HasInjectiveResolutions 𝒜]
variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(ℬ))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]
variable [RF.CommShift ℤ] [RF.IsTriangulated]

-- Proof sketch: specialize the bounded-below universality theorem to the stronger hypothesis
-- that the bounded-below degrees agree with the canonical unbounded `Functor.rightDerived`
-- functors and that every object embeds into an unbounded right-acyclic object.
/-- Stronger-assumption companion: under injective resolutions, if the bounded-below family
`A ↦ H^n((RF(A[0])) : D(\mathcal B))` is degreewise isomorphic to the canonical unbounded right
derived functors `F.rightDerived n`, then the canonical bounded-below right-derived
cohomological `δ`-functor is universal. -/
theorem boundedBelowRightDerivedDeltaFunctor_isUniversal_of_rightDerivedComparison
    (hcompare : ∀ n : ℕ, IsIsomorphic (RF.boundedBelowRightDerived n) (F.rightDerived n))
    (hacyclic : ∀ X : 𝒜, ∃ (Y : 𝒜) (i : X ⟶ Y), Mono i ∧
      IsRightAcyclicForAdditiveFunctor F Y) :
    CohomologicalDeltaFunctor.IsUniversal (boundedBelowRightDerivedDeltaFunctor RF) := by
  -- Convert unbounded right acyclicity into bounded-below acyclicity via the comparison
  -- isomorphisms, then reuse the bounded-below universality theorem.
  refine boundedBelowRightDerivedDeltaFunctor_isUniversal (F := F) (RF := RF) (α := α) ?_
  intro X
  rcases hacyclic X with ⟨Y, i, hi, hY⟩
  refine ⟨Y, i, hi, ?_⟩
  have hvanishRight : F.higherRightDerivedVanishes Y :=
    (isRightAcyclicForAdditiveFunctor_iff_higherRightDerivedVanishes (F := F) Y).1 hY
  have hvanishBounded : RF.boundedBelowHigherRightDerivedVanishes Y := by
    intro n
    rcases hcompare (n + 1) with ⟨e⟩
    exact (e.app Y).isZero_iff.2 (hvanishRight n)
  exact
    (isBoundedBelowRightAcyclicForAdditiveFunctor_iff_boundedBelowHigherRightDerivedVanishes
      (F := F) (RF := RF) (α := α) Y).2 hvanishBounded

end UnboundedCompanion

end CategoryTheory
