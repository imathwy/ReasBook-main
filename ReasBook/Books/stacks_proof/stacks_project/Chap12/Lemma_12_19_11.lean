import StacksProject_2024.Chap12.Lemma_12_19_2
import StacksProject_2024.Chap12.Lemma_12_19_4
import StacksProject_2024.Chap12.Lemma_12_19_7
import StacksProject_2024.Chap12.Lemma_12_19_8
import Mathlib.Tactic.StacksAttribute

open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

open FilteredObject.Hom

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.11:
- source-facing: existence of a filtered pullback square with strict projection to `C`
- core/canonical owner: `IsPullback g' f' f g`, together with the chosen `HasPullback f g`
- primitive data: the canonical comparison morphism `B ⊞ C ⟶ A`
  induced by `(f, -g)`
- bridge/view: the kernel model of that comparison morphism inside `B ⊞ C`,
  together with the derived projections to `B` and `C`
-/

/-- Helper for Lemma 12.19.11: the ambient biproduct object on the underlying objects of `B`
and `C`. -/
private abbrev ambientBiprod : 𝒜 := B.obj ⊞ C.obj

/-- Helper for Lemma 12.19.11: the ambient left projection from the underlying biproduct object
of `B ⊞ C`. -/
private abbrev ambientBiprodFst : ambientBiprod (B := B) (C := C) ⟶ B.obj := biprod.fst

/-- Helper for Lemma 12.19.11: the ambient right projection from the underlying biproduct object
of `B ⊞ C`. -/
private abbrev ambientBiprodSnd : ambientBiprod (B := B) (C := C) ⟶ C.obj := biprod.snd

/-- Helper for Lemma 12.19.11: the ambient biproduct lift with codomain fixed to the underlying
object of `B ⊞ C`. -/
private abbrev ambientBiprodLift {T : 𝒜} (a : T ⟶ B.obj) (b : T ⟶ C.obj) :
    T ⟶ ambientBiprod (B := B) (C := C) := biprod.lift a b

/-- Helper for Lemma 12.19.11: the ambient biproduct desc with domain fixed to the underlying
object of `B ⊞ C`. -/
private abbrev ambientBiprodDesc (f : B.obj ⟶ A.obj) (g : C.obj ⟶ A.obj) :
    ambientBiprod (B := B) (C := C) ⟶ A.obj := biprod.desc f g

/-- Helper for Lemma 12.19.11: the explicit ambient filtered biproduct on `B.obj ⊞ C.obj` with
the stagewise biproduct filtration. -/
private abbrev ambientFilteredBiprod : FilteredObject 𝒜 where
  obj := ambientBiprod (B := B) (C := C)
  filtration := DecreasingFiltration.biprod B.filtration C.filtration

/-- Helper for Lemma 12.19.11: the first projection from the explicit ambient filtered biproduct.
-/
private theorem ambientFilteredBiprodFst_preserves (i : ℤ) :
    (B.filtration i).Factors
      (((ambientFilteredBiprod (B := B) (C := C)).filtration i).arrow ≫ ambientBiprodFst (B := B) (C := C)) := by
  let stageArrow :
      ((B.filtration i : 𝒜) ⊞ (C.filtration i : 𝒜)) ⟶ ambientBiprod (B := B) (C := C) :=
    biprod.map (B.filtration i).arrow (C.filtration i).arrow
  change (B.filtration i).Factors ((Subobject.mk stageArrow).arrow ≫ ambientBiprodFst (B := B) (C := C))
  refine (Subobject.factors_iff _ _).2 ?_
  refine ⟨(Subobject.underlyingIso stageArrow).hom ≫ biprod.fst, ?_⟩
  calc
    ((Subobject.underlyingIso stageArrow).hom ≫ biprod.fst) ≫ (B.filtration i).arrow
        = (Subobject.underlyingIso stageArrow).hom ≫ (biprod.fst ≫ (B.filtration i).arrow) := by
            simp [Category.assoc]
    _ = (Subobject.underlyingIso stageArrow).hom ≫ (stageArrow ≫ biprod.fst) := by
          simp [stageArrow]
    _ = (Subobject.mk stageArrow).arrow ≫ ambientBiprodFst (B := B) (C := C) := by
          simp [ambientBiprodFst]

/-- Helper for Lemma 12.19.11: the second projection from the explicit ambient filtered biproduct.
-/
private theorem ambientFilteredBiprodSnd_preserves (i : ℤ) :
    (C.filtration i).Factors
      (((ambientFilteredBiprod (B := B) (C := C)).filtration i).arrow ≫ ambientBiprodSnd (B := B) (C := C)) := by
  let stageArrow :
      ((B.filtration i : 𝒜) ⊞ (C.filtration i : 𝒜)) ⟶ ambientBiprod (B := B) (C := C) :=
    biprod.map (B.filtration i).arrow (C.filtration i).arrow
  change (C.filtration i).Factors ((Subobject.mk stageArrow).arrow ≫ ambientBiprodSnd (B := B) (C := C))
  refine (Subobject.factors_iff _ _).2 ?_
  refine ⟨(Subobject.underlyingIso stageArrow).hom ≫ biprod.snd, ?_⟩
  calc
    ((Subobject.underlyingIso stageArrow).hom ≫ biprod.snd) ≫ (C.filtration i).arrow
        = (Subobject.underlyingIso stageArrow).hom ≫ (biprod.snd ≫ (C.filtration i).arrow) := by
            simp [Category.assoc]
    _ = (Subobject.underlyingIso stageArrow).hom ≫ (stageArrow ≫ biprod.snd) := by
          simp [stageArrow]
    _ = (Subobject.mk stageArrow).arrow ≫ ambientBiprodSnd (B := B) (C := C) := by
          simp [ambientBiprodSnd]

/-- Helper for Lemma 12.19.11: the biproduct lift into the explicit ambient filtered biproduct
preserves filtrations. -/
private theorem ambientFilteredBiprodLift_preserves {P : FilteredObject 𝒜}
    (a : P ⟶ B) (b : P ⟶ C) (i : ℤ) :
    ((ambientFilteredBiprod (B := B) (C := C)).filtration i).Factors
      ((P.filtration i).arrow ≫ ambientBiprodLift a.hom b.hom) := by
  let stageArrow :
      ((B.filtration i : 𝒜) ⊞ (C.filtration i : 𝒜)) ⟶ ambientBiprod (B := B) (C := C) :=
    biprod.map (B.filtration i).arrow (C.filtration i).arrow
  change (Subobject.mk stageArrow).Factors ((P.filtration i).arrow ≫ ambientBiprodLift a.hom b.hom)
  rw [Subobject.mk_factors_iff]
  refine ⟨biprod.lift (stageMap a i) (stageMap b i), ?_⟩
  apply biprod.hom_ext <;>
    simp [stageArrow, Category.assoc]

/-- Helper for Lemma 12.19.11: the biproduct desc from the explicit ambient filtered biproduct
preserves filtrations. -/
private theorem ambientFilteredBiprodDesc_preserves {Z : FilteredObject 𝒜}
    (f : B ⟶ Z) (g : C ⟶ Z) (i : ℤ) :
    (Z.filtration i).Factors
      (((ambientFilteredBiprod (B := B) (C := C)).filtration i).arrow ≫ ambientBiprodDesc f.hom g.hom) := by
  let stageArrow :
      ((B.filtration i : 𝒜) ⊞ (C.filtration i : 𝒜)) ⟶ ambientBiprod (B := B) (C := C) :=
    biprod.map (B.filtration i).arrow (C.filtration i).arrow
  change (Z.filtration i).Factors ((Subobject.mk stageArrow).arrow ≫ ambientBiprodDesc f.hom g.hom)
  refine (Subobject.factors_iff _ _).2 ?_
  refine
    ⟨(Subobject.underlyingIso stageArrow).hom ≫
        biprod.desc (stageMap f i) (stageMap g i), ?_⟩
  calc
    ((Subobject.underlyingIso stageArrow).hom ≫ biprod.desc (stageMap f i) (stageMap g i)) ≫
        (Z.filtration i).arrow
        =
          (Subobject.underlyingIso stageArrow).hom ≫
            (biprod.desc (stageMap f i) (stageMap g i) ≫ (Z.filtration i).arrow) := by
              simp [Category.assoc]
    _ =
          (Subobject.underlyingIso stageArrow).hom ≫
            (stageArrow ≫ ambientBiprodDesc f.hom g.hom) := by
              congr 1
              apply biprod.hom_ext' <;>
                simp [stageArrow]
    _ = (Subobject.mk stageArrow).arrow ≫ ambientBiprodDesc f.hom g.hom := by
          simp

/-- Helper for Lemma 12.19.11: the first projection from the explicit ambient filtered biproduct.
-/
private abbrev ambientFilteredBiprodFst :
    ambientFilteredBiprod (B := B) (C := C) ⟶ B where
  hom := ambientBiprodFst (B := B) (C := C)
  preserves := ambientFilteredBiprodFst_preserves (B := B) (C := C)

/-- Helper for Lemma 12.19.11: the second projection from the explicit ambient filtered biproduct.
-/
private abbrev ambientFilteredBiprodSnd :
    ambientFilteredBiprod (B := B) (C := C) ⟶ C where
  hom := ambientBiprodSnd (B := B) (C := C)
  preserves := ambientFilteredBiprodSnd_preserves (B := B) (C := C)

/-- Helper for Lemma 12.19.11: the canonical lift into the explicit ambient filtered biproduct. -/
private abbrev ambientFilteredBiprodLift {P : FilteredObject 𝒜}
    (a : P ⟶ B) (b : P ⟶ C) :
    P ⟶ ambientFilteredBiprod (B := B) (C := C) where
  hom := ambientBiprodLift a.hom b.hom
  preserves := ambientFilteredBiprodLift_preserves (B := B) (C := C) a b

/-- Helper for Lemma 12.19.11: the canonical desc from the explicit ambient filtered biproduct. -/
private abbrev ambientFilteredBiprodDesc {Z : FilteredObject 𝒜}
    (f : B ⟶ Z) (g : C ⟶ Z) :
    ambientFilteredBiprod (B := B) (C := C) ⟶ Z where
  hom := ambientBiprodDesc f.hom g.hom
  preserves := ambientFilteredBiprodDesc_preserves (B := B) (C := C) f g

private abbrev pullbackDifference (f : B ⟶ A) (g : C ⟶ A) :
    ambientFilteredBiprod (B := B) (C := C) ⟶ A :=
  ambientFilteredBiprodDesc f (show C ⟶ A from -g)

private abbrev kernelPullback (f : B ⟶ A) (g : C ⟶ A) : FilteredObject 𝒜 :=
  (ambientFilteredBiprod (B := B) (C := C)).subobjectFilteredObject
    (kernelSubobject (pullbackDifference f g).hom)

private abbrev kernelPullbackι (f : B ⟶ A) (g : C ⟶ A) :
    kernelPullback f g ⟶ ambientFilteredBiprod (B := B) (C := C) :=
  (ambientFilteredBiprod (B := B) (C := C)).subobjectInclusion
    (kernelSubobject (pullbackDifference f g).hom)

private abbrev kernelPullbackFst (f : B ⟶ A) (g : C ⟶ A) : kernelPullback f g ⟶ B :=
  kernelPullbackι f g ≫ ambientFilteredBiprodFst

private abbrev kernelPullbackSnd (f : B ⟶ A) (g : C ⟶ A) : kernelPullback f g ⟶ C :=
  kernelPullbackι f g ≫ ambientFilteredBiprodSnd

/-- Helper for Lemma 12.19.11: the ambient biproduct lift attached to a commutative square
`a ≫ f = b ≫ g` lands in the kernel of `(f, -g)`. -/
private theorem kernelPullbackLift_hom_zero {P : FilteredObject 𝒜}
    (f : B ⟶ A) (g : C ⟶ A) (a : P ⟶ B) (b : P ⟶ C) (h : a ≫ f = b ≫ g) :
    (ambientFilteredBiprodLift (B := B) (C := C) a b).hom ≫ (pullbackDifference f g).hom = 0 := by
  -- Proof comment: expand the biproduct comparison map `(f, -g)` and use the commutativity
  -- hypothesis to cancel the resulting difference.
  have hh : a.hom ≫ f.hom = b.hom ≫ g.hom := congrArg FilteredObject.Hom.hom h
  calc
    (ambientFilteredBiprodLift (B := B) (C := C) a b).hom ≫ (pullbackDifference f g).hom
        = a.hom ≫ f.hom - b.hom ≫ g.hom := by
            simpa [ambientFilteredBiprodLift, ambientFilteredBiprodDesc, sub_eq_add_neg] using
              (biprod.lift_desc : ambientBiprodLift a.hom b.hom ≫ ambientBiprodDesc f.hom (-g.hom) =
                a.hom ≫ f.hom + b.hom ≫ (-g.hom))
    _ = 0 := by
          rw [hh, sub_self]

/-- Helper for Lemma 12.19.11: the ambient kernel factor of `biprod.lift a b` preserves the
filtered structures, so it defines a filtered morphism into the canonical kernel-model pullback.
-/
private theorem kernelPullbackLift_preserves {P : FilteredObject 𝒜}
    (f : B ⟶ A) (g : C ⟶ A) (a : P ⟶ B) (b : P ⟶ C) (h : a ≫ f = b ≫ g) :
    ∀ i : ℤ,
      ((kernelPullback f g).filtration i).Factors
        ((P.filtration i).arrow ≫
          factorThruKernelSubobject
            (pullbackDifference f g).hom
            (ambientFilteredBiprodLift (B := B) (C := C) a b).hom
            (kernelPullbackLift_hom_zero f g a b h)) := by
  intro i
  -- Proof comment: the kernel-model filtration is induced from the ambient biproduct filtration,
  -- so it is enough to show that the ambient stage map factors through the kernel arrow.
  rw [show ((kernelPullback f g).filtration i) =
      (Subobject.pullback (kernelSubobject (pullbackDifference f g).hom).arrow).obj
        ((ambientFilteredBiprod (B := B) (C := C)).filtration i) by
    rfl]
  have hcomp :
      (((P.filtration i).arrow ≫
        factorThruKernelSubobject
          (pullbackDifference f g).hom
          (ambientFilteredBiprodLift (B := B) (C := C) a b).hom
          (kernelPullbackLift_hom_zero f g a b h)) ≫
        (kernelSubobject (pullbackDifference f g).hom).arrow) =
      (P.filtration i).arrow ≫ (ambientFilteredBiprodLift (B := B) (C := C) a b).hom := by
    simp [Category.assoc, factorThruKernelSubobject_comp_arrow]
  have hstage :
      ((ambientFilteredBiprod (B := B) (C := C)).filtration i).Factors
        (((P.filtration i).arrow ≫
          factorThruKernelSubobject
            (pullbackDifference f g).hom
            (ambientFilteredBiprodLift (B := B) (C := C) a b).hom
            (kernelPullbackLift_hom_zero f g a b h)) ≫
          (kernelSubobject (pullbackDifference f g).hom).arrow) := by
    rw [hcomp]
    simpa using (ambientFilteredBiprodLift (B := B) (C := C) a b).preserves i
  exact
      (pullback_factors_iff
      (f := (kernelSubobject (pullbackDifference f g).hom).arrow)
      (y := ((ambientFilteredBiprod (B := B) (C := C)).filtration i))
      (h := (P.filtration i).arrow ≫
        factorThruKernelSubobject
          (pullbackDifference f g).hom
          (ambientFilteredBiprodLift (B := B) (C := C) a b).hom
          (kernelPullbackLift_hom_zero f g a b h))).2 hstage

/-- Helper for Lemma 12.19.11: the ambient biproduct lift of a commutative square factors through
the canonical kernel-model pullback as a filtered morphism. -/
private abbrev kernelPullbackLift {P : FilteredObject 𝒜}
    (f : B ⟶ A) (g : C ⟶ A) (a : P ⟶ B) (b : P ⟶ C) (h : a ≫ f = b ≫ g) :
    P ⟶ kernelPullback f g where
  hom :=
    factorThruKernelSubobject
      (pullbackDifference f g).hom
      (ambientFilteredBiprodLift (B := B) (C := C) a b).hom
      (kernelPullbackLift_hom_zero f g a b h)
  preserves := kernelPullbackLift_preserves f g a b h

/-- Helper for Lemma 12.19.11: the filtered kernel lift composed with the canonical kernel-model
inclusion recovers the original biproduct lift. -/
private theorem kernelPullbackLift_comp_kernelPullbackι {P : FilteredObject 𝒜}
    (f : B ⟶ A) (g : C ⟶ A) (a : P ⟶ B) (b : P ⟶ C) (h : a ≫ f = b ≫ g) :
    kernelPullbackLift f g a b h ≫ kernelPullbackι f g =
      ambientFilteredBiprodLift (B := B) (C := C) a b := by
  -- Proof comment: the filtered kernel lift is defined by the ambient kernel factorization, whose
  -- composite with the kernel inclusion is the original ambient lift into `B ⊞ C`.
  apply FilteredObject.forget.map_injective
  change
    factorThruKernelSubobject
        (pullbackDifference f g).hom
        (ambientFilteredBiprodLift (B := B) (C := C) a b).hom
        (kernelPullbackLift_hom_zero f g a b h) ≫
      (kernelSubobject (pullbackDifference f g).hom).arrow =
        (ambientFilteredBiprodLift (B := B) (C := C) a b).hom
  exact factorThruKernelSubobject_comp_arrow
    (f := (pullbackDifference f g).hom)
    ((ambientFilteredBiprodLift (B := B) (C := C) a b).hom)
    (kernelPullbackLift_hom_zero f g a b h)

/-- Helper for Lemma 12.19.11: the kernel-model inclusion into `B ⊞ C` is annihilated by the
comparison map `(f, -g)`. -/
private theorem kernelPullbackι_comp_pullbackDifference (f : B ⟶ A) (g : C ⟶ A) :
    (kernelPullbackι f g).hom ≫ (pullbackDifference f g).hom = 0 := by
  -- Proof comment: `kernelPullbackι` is the inclusion of the kernel subobject of
  -- `pullbackDifference f g`, so its composite with that map is the defining zero composite.
  change (kernelSubobject (pullbackDifference f g).hom).arrow ≫
      (pullbackDifference f g).hom = 0
  exact kernelSubobject_arrow_comp (pullbackDifference f g).hom

private theorem kernelPullback_isPullback (f : B ⟶ A) (g : C ⟶ A) :
    IsPullback (kernelPullbackFst f g) (kernelPullbackSnd f g) f g := by
  -- Route correction: use the explicit kernel-factor lift already built above, so the proof stays
  -- in the filtered category and avoids further rewriting of the ambient biproduct carrier.
  refine IsPullback.mk' ?_ ?_ ?_
  · -- Proof comment: the kernel inclusion is annihilated by `(f, -g)`, so the two projections
    -- have equal composites to `A`.
    have hsum :
        kernelPullbackFst f g ≫ f + kernelPullbackSnd f g ≫ (-g) = 0 := by
      have hι :
          kernelPullbackι f g =
            ambientFilteredBiprodLift
              (B := B) (C := C) (kernelPullbackFst f g) (kernelPullbackSnd f g) := by
        apply FilteredObject.forget.map_injective
        apply biprod.hom_ext
        · change (kernelPullbackι f g).hom ≫ biprod.fst =
            ambientBiprodLift ((kernelPullbackFst f g).hom) ((kernelPullbackSnd f g).hom) ≫ biprod.fst
          simp [kernelPullbackFst, ambientFilteredBiprodFst]
        · change (kernelPullbackι f g).hom ≫ biprod.snd =
            ambientBiprodLift ((kernelPullbackFst f g).hom) ((kernelPullbackSnd f g).hom) ≫ biprod.snd
          simp [kernelPullbackSnd, ambientFilteredBiprodSnd]
      calc
        kernelPullbackFst f g ≫ f + kernelPullbackSnd f g ≫ (-g)
            =
              ambientFilteredBiprodLift
                  (B := B) (C := C) (kernelPullbackFst f g) (kernelPullbackSnd f g) ≫
                ambientFilteredBiprodDesc f (-g) := by
                  apply FilteredObject.forget.map_injective
                  change
                    (kernelPullbackFst f g ≫ f + kernelPullbackSnd f g ≫ (-g)).hom =
                      (ambientBiprodLift ((kernelPullbackFst f g).hom) ((kernelPullbackSnd f g).hom) ≫
                        ambientBiprodDesc f.hom (-g.hom))
                  simp [kernelPullbackFst, kernelPullbackSnd, ambientFilteredBiprodFst,
                    ambientFilteredBiprodSnd, Category.assoc]
        _ = kernelPullbackι f g ≫ pullbackDifference f g := by
              rw [hι]
        _ = 0 := by
              apply FilteredObject.forget.map_injective
              exact kernelPullbackι_comp_pullbackDifference f g
    have hsub :
        kernelPullbackFst f g ≫ f - kernelPullbackSnd f g ≫ g = 0 := by
      simpa [sub_eq_add_neg] using hsum
    exact sub_eq_zero.mp hsub
  · intro P φ ψ hfst hsnd
    -- Proof comment: compare the two candidate lifts after the mono kernel inclusion and recover
    -- equality there from the biproduct projections.
    letI : Mono (kernelPullbackι f g) :=
      FilteredObject.forget.mono_of_mono_map <| by
        change Mono (kernelSubobject (pullbackDifference f g).hom).arrow
        infer_instance
    apply (cancel_mono (kernelPullbackι f g)).1
    apply FilteredObject.forget.map_injective
    change
      (φ.hom ≫ (kernelPullbackι f g).hom : P.obj ⟶ ambientBiprod (B := B) (C := C)) =
        ψ.hom ≫ (kernelPullbackι f g).hom
    apply biprod.hom_ext
    · simpa [kernelPullbackFst, Category.assoc] using
        congrArg FilteredObject.Hom.hom hfst
    · simpa [kernelPullbackSnd, Category.assoc] using
        congrArg FilteredObject.Hom.hom hsnd
  · intro P a b h
    -- Proof comment: the previously constructed filtered kernel lift is the desired universal
    -- arrow, and its two composites are read off from the biproduct lift formulas.
    refine ⟨kernelPullbackLift f g a b h, ?_, ?_⟩
    · calc
        kernelPullbackLift f g a b h ≫ kernelPullbackFst f g
            =
              kernelPullbackLift f g a b h ≫ kernelPullbackι f g ≫
                ambientFilteredBiprodFst (B := B) (C := C) := by
                simp [kernelPullbackFst]
        _ =
              ambientFilteredBiprodLift (B := B) (C := C) a b ≫
                ambientFilteredBiprodFst (B := B) (C := C) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k : P ⟶ ambientFilteredBiprod (B := B) (C := C) ↦
                    k ≫ ambientFilteredBiprodFst (B := B) (C := C))
                  (kernelPullbackLift_comp_kernelPullbackι f g a b h)
        _ = a := by
              apply FilteredObject.forget.map_injective
              change ambientBiprodLift a.hom b.hom ≫ biprod.fst = a.hom
              simp [ambientBiprodLift]
    · calc
        kernelPullbackLift f g a b h ≫ kernelPullbackSnd f g
            =
              kernelPullbackLift f g a b h ≫ kernelPullbackι f g ≫
                ambientFilteredBiprodSnd (B := B) (C := C) := by
                simp [kernelPullbackSnd]
        _ =
              ambientFilteredBiprodLift (B := B) (C := C) a b ≫
                ambientFilteredBiprodSnd (B := B) (C := C) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k : P ⟶ ambientFilteredBiprod (B := B) (C := C) ↦
                    k ≫ ambientFilteredBiprodSnd (B := B) (C := C))
                  (kernelPullbackLift_comp_kernelPullbackι f g a b h)
        _ = b := by
              apply FilteredObject.forget.map_injective
              change ambientBiprodLift a.hom b.hom ≫ biprod.snd = b.hom
              simp [ambientBiprodLift]

noncomputable instance hasPullback (f : B ⟶ A) (g : C ⟶ A) : HasPullback f g :=
  (kernelPullback_isPullback f g).hasPullback

/-- Helper for Lemma 12.19.11: the underlying ambient maps of the kernel-model pullback form a
pullback square in `𝒜`. -/
private theorem kernelPullback_hom_isPullback (f : B ⟶ A) (g : C ⟶ A) :
    IsPullback (kernelPullbackFst f g).hom (kernelPullbackSnd f g).hom f.hom g.hom := by
  -- Proof comment: reuse the same kernel model on underlying objects, where the universal arrow is
  -- the factorization of the ambient biproduct lift through the kernel subobject.
  refine IsPullback.mk' ?_ ?_ ?_
  · exact congrArg FilteredObject.Hom.hom (kernelPullback_isPullback f g).w
  · intro P φ ψ hfst hsnd
    letI : Mono (kernelPullbackι f g).hom := by
      change Mono (kernelSubobject (pullbackDifference f g).hom).arrow
      infer_instance
    apply (cancel_mono (kernelPullbackι f g).hom).1
    change
      (φ ≫ (kernelSubobject (pullbackDifference f g).hom).arrow : P ⟶ ambientBiprod (B := B) (C := C)) =
        (ψ ≫ (kernelSubobject (pullbackDifference f g).hom).arrow : P ⟶ ambientBiprod (B := B) (C := C))
    apply biprod.hom_ext
    · simpa [kernelPullbackFst, Category.assoc] using hfst
    · simpa [kernelPullbackSnd, Category.assoc] using hsnd
  · intro P a b h
    let ab : P ⟶ ambientBiprod (B := B) (C := C) := ambientBiprodLift a b
    have hab :
        ab ≫ (pullbackDifference f g).hom = 0 := by
      change ambientBiprodLift a b ≫ ambientBiprodDesc f.hom (-g.hom) = 0
      calc
        ambientBiprodLift a b ≫ ambientBiprodDesc f.hom (-g.hom)
            = a ≫ f.hom - b ≫ g.hom := by
                simpa [sub_eq_add_neg] using
                  (biprod.lift_desc :
                    ambientBiprodLift a b ≫ ambientBiprodDesc f.hom (-g.hom) =
                      a ≫ f.hom + b ≫ (-g.hom))
        _ = 0 := by rw [h, sub_self]
    refine
      ⟨factorThruKernelSubobject (pullbackDifference f g).hom ab hab, ?_, ?_⟩
    · calc
        factorThruKernelSubobject (pullbackDifference f g).hom ab hab ≫
            (kernelPullbackFst f g).hom
            =
              factorThruKernelSubobject (pullbackDifference f g).hom ab hab ≫
                ((kernelSubobject (pullbackDifference f g).hom).arrow ≫ ambientBiprodFst) := by
                  change
                    factorThruKernelSubobject (pullbackDifference f g).hom ab hab ≫
                      ((kernelSubobject (pullbackDifference f g).hom).arrow ≫ ambientBiprodFst) =
                    factorThruKernelSubobject (pullbackDifference f g).hom ab hab ≫
                      ((kernelSubobject (pullbackDifference f g).hom).arrow ≫ ambientBiprodFst)
                  rfl
        _ = ab ≫ ambientBiprodFst := by
              rw [← Category.assoc, factorThruKernelSubobject_comp_arrow]
        _ = a := by simpa [ab]
    · calc
        factorThruKernelSubobject (pullbackDifference f g).hom ab hab ≫
            (kernelPullbackSnd f g).hom
            =
              factorThruKernelSubobject (pullbackDifference f g).hom ab hab ≫
                ((kernelSubobject (pullbackDifference f g).hom).arrow ≫ ambientBiprodSnd) := by
                  change
                    factorThruKernelSubobject (pullbackDifference f g).hom ab hab ≫
                      ((kernelSubobject (pullbackDifference f g).hom).arrow ≫ ambientBiprodSnd) =
                    factorThruKernelSubobject (pullbackDifference f g).hom ab hab ≫
                      ((kernelSubobject (pullbackDifference f g).hom).arrow ≫ ambientBiprodSnd)
                  rfl
        _ = ab ≫ ambientBiprodSnd := by
              rw [← Category.assoc, factorThruKernelSubobject_comp_arrow]
        _ = b := by simpa [ab]

/-- Helper for Lemma 12.19.11: stage maps commute with composition of filtered morphisms. -/
private theorem stageMap_comp {C : Type u} [Category.{v} C]
    {X Y Z : FilteredObject C} (u : X ⟶ Y) (v : Y ⟶ Z) (i : ℤ) :
    stageMap (u ≫ v) i = stageMap u i ≫ stageMap v i := by
  -- Proof comment: both composites agree after postcomposing with the mono stage inclusion of
  -- `Z`, so they are equal.
  exact (cancel_mono (Z.filtration.obj i).arrow).1 (by
    calc
      stageMap (u ≫ v) i ≫ (Z.filtration.obj i).arrow
          = (X.filtration.obj i).arrow ≫ (u ≫ v).hom := by
              rw [stageMap_comm]
      _ = ((X.filtration.obj i).arrow ≫ u.hom) ≫ v.hom := by
            simp [Category.assoc]
      _ = (stageMap u i ≫ (Y.filtration.obj i).arrow) ≫ v.hom := by
            rw [stageMap_comm]
      _ = stageMap u i ≫ (stageMap v i ≫ (Z.filtration.obj i).arrow) := by
            rw [stageMap_comm]
            simp [Category.assoc]
      _ = (stageMap u i ≫ stageMap v i) ≫ (Z.filtration.obj i).arrow := by
            simp [Category.assoc])

/-- Helper for Lemma 12.19.11: postcomposing an epimorphism does not change the image subobject.
-/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : 𝒜}
    (u : X ⟶ Y) [Epi u] (v : Y ⟶ Z) :
    imageSubobject (u ≫ v) = imageSubobject v := by
  -- Proof comment: rewrite through the restriction to `im(u)` and identify `im(u)` with `⊤`
  -- because `u` is epi.
  calc
    imageSubobject (u ≫ v) = imageSubobject ((imageSubobject u).arrow ≫ v) := by
      rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction u v]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ v) := by
          simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ v))
            (Limits.imageSubobject_eq_top_of_epi u)
    _ = imageSubobject v := by
          simpa using Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) v

/-- Helper for Lemma 12.19.11: mapping the image of a composite through a monomorphism agrees
with the image of the composite inside the target. -/
private theorem imageSubobject_comp_eq_map_of_mono {X Y Z : 𝒜}
    (u : X ⟶ Y) (v : Y ⟶ Z) [Mono v] :
    imageSubobject (u ≫ v) = (Subobject.map v).obj (imageSubobject u) := by
  -- Proof comment: rewrite the composite image through the restriction to `im(u)`, then use that
  -- the image of a mono is the mono itself.
  calc
    imageSubobject (u ≫ v) = imageSubobject ((imageSubobject u).arrow ≫ v) := by
      rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction u v]
    _ = Subobject.mk ((imageSubobject u).arrow ≫ v) := by
          simpa using (Limits.imageSubobject_mono ((imageSubobject u).arrow ≫ v))
    _ = (Subobject.map v).obj (Subobject.mk (imageSubobject u).arrow) := by
          rw [Subobject.map_mk]
    _ = (Subobject.map v).obj (imageSubobject u) := by
          rw [Subobject.mk_arrow]

/-- Helper for Lemma 12.19.11: pushing forward a pullback subobject along an epimorphism
recovers the original subobject. -/
private theorem exists_pullback_eq_of_epi {X Y : 𝒜} (u : X ⟶ Y) [Epi u] (P : Subobject Y) :
    (Subobject.exists u).obj ((Subobject.pullback u).obj P) = P := by
  have hImage : imageSubobject (((Subobject.pullback u).obj P).arrow ≫ u) = P := by
    -- Proof comment: the pullback projection is epi, so its image agrees with the original
    -- subobject.
    rw [← (Subobject.isPullback u P).w]
    haveI : Epi (Subobject.pullbackπ u P) :=
      Abelian.epi_fst_of_isLimit P.arrow u (Subobject.isPullback u P).isLimit
    have hle :
        imageSubobject (Subobject.pullbackπ u P ≫ P.arrow) ≤ imageSubobject P.arrow :=
      imageSubobject_comp_le (Subobject.pullbackπ u P) P.arrow
    haveI : Epi (Subobject.ofLE _ _ hle) :=
      imageSubobject_comp_le_epi_of_epi (Subobject.pullbackπ u P) P.arrow
    haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
    have hEq :
        imageSubobject (Subobject.pullbackπ u P ≫ P.arrow) = imageSubobject P.arrow :=
      Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by simp)
    simpa [imageSubobject_mono] using hEq
  -- Proof comment: compare the pushed-forward pullback with the original subobject by their
  -- arrows into `Y`.
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage u ((Subobject.pullback u).obj P) ≪≫
      (imageSubobjectIso _).symm ≪≫
      Subobject.isoOfEq _ _ hImage)
  calc
    ((Subobject.existsIsoImage u ((Subobject.pullback u).obj P)).hom ≫
        (imageSubobjectIso (((Subobject.pullback u).obj P).arrow ≫ u)).inv ≫
        (Subobject.isoOfEq _ _ hImage).hom) ≫
        P.arrow
        = (Subobject.existsIsoImage u ((Subobject.pullback u).obj P)).hom ≫
            image.ι (((Subobject.pullback u).obj P).arrow ≫ u) := by
              simp [Category.assoc]
    _ = ((Subobject.exists u).obj ((Subobject.pullback u).obj P)).arrow := by
          simpa [Subobject.existsIsoImage] using
            (Over.w ((Subobject.existsCompRepresentativeIso u).app
              ((Subobject.pullback u).obj P)).hom.hom)

/-- Helper for Lemma 12.19.11: the `i`-th stage of the kernel-model pullback is a pullback of the
stage maps of `f` and `g`. -/
private theorem stageMap_kernelPullback_hom_ext
    (f : B ⟶ A) (g : C ⟶ A) (i : ℤ) {T : 𝒜}
    {φ ψ : T ⟶ (kernelPullback f g).filtration i}
    (hfst : φ ≫ stageMap (kernelPullbackFst f g) i =
      ψ ≫ stageMap (kernelPullbackFst f g) i)
    (hsnd : φ ≫ stageMap (kernelPullbackSnd f g) i =
      ψ ≫ stageMap (kernelPullbackSnd f g) i) :
    φ = ψ := by
  -- Proof comment: compare `φ` and `ψ` after the mono stage inclusion into `kernelPullback f g`,
  -- where the ambient pullback square gives extensionality from the two projections.
  apply (cancel_mono ((kernelPullback f g).filtration i).arrow).1
  have hfst' :
      φ ≫ ((kernelPullback f g).filtration i).arrow ≫ (kernelPullbackFst f g).hom =
        ψ ≫ ((kernelPullback f g).filtration i).arrow ≫ (kernelPullbackFst f g).hom := by
    have hfst_arrow :=
      congrArg (fun k : T ⟶ B.filtration i ↦ k ≫ (B.filtration i).arrow) hfst
    simpa [Category.assoc, stageMap_comm] using hfst_arrow
  have hsnd' :
      φ ≫ ((kernelPullback f g).filtration i).arrow ≫ (kernelPullbackSnd f g).hom =
        ψ ≫ ((kernelPullback f g).filtration i).arrow ≫ (kernelPullbackSnd f g).hom := by
    have hsnd_arrow :=
      congrArg (fun k : T ⟶ C.filtration i ↦ k ≫ (C.filtration i).arrow) hsnd
    simpa [Category.assoc, stageMap_comm] using hsnd_arrow
  have hfst'' :
      (φ ≫ ((kernelPullback f g).filtration i).arrow) ≫ (kernelPullbackFst f g).hom =
        (ψ ≫ ((kernelPullback f g).filtration i).arrow) ≫ (kernelPullbackFst f g).hom := by
    simpa [Category.assoc] using hfst'
  have hsnd'' :
      (φ ≫ ((kernelPullback f g).filtration i).arrow) ≫ (kernelPullbackSnd f g).hom =
        (ψ ≫ ((kernelPullback f g).filtration i).arrow) ≫ (kernelPullbackSnd f g).hom := by
    simpa [Category.assoc] using hsnd'
  simpa [Category.assoc] using (kernelPullback_hom_isPullback f g).hom_ext hfst'' hsnd''

/-- Helper for Lemma 12.19.11: a commutative square on the `i`-th stages factors through the
`i`-th stage of the kernel-model pullback. -/
private theorem stageMap_kernelPullback_exists_lift
    (f : B ⟶ A) (g : C ⟶ A) (i : ℤ) {T : 𝒜}
    (a : T ⟶ B.filtration i) (b : T ⟶ C.filtration i)
    (h : a ≫ stageMap f i = b ≫ stageMap g i) :
    ∃ l : T ⟶ (kernelPullback f g).filtration i,
      l ≫ stageMap (kernelPullbackFst f g) i = a ∧
      l ≫ stageMap (kernelPullbackSnd f g) i = b := by
  -- Proof comment: first build the ambient lift into the kernel-model pullback, then show that
  -- its composite with `kernelPullbackι` already lands in the `i`-th biproduct stage.
  let a₀ : T ⟶ B.obj := a ≫ (B.filtration i).arrow
  let b₀ : T ⟶ C.obj := b ≫ (C.filtration i).arrow
  have h₀ : a₀ ≫ f.hom = b₀ ≫ g.hom := by
    have h_arrow :=
      congrArg (fun k : T ⟶ A.filtration i ↦ k ≫ (A.filtration i).arrow) h
    simpa [a₀, b₀, Category.assoc, stageMap_comm] using h_arrow
  let ambientLift : T ⟶ ambientBiprod (B := B) (C := C) := ambientBiprodLift a₀ b₀
  let l₀ : T ⟶ (kernelPullback f g).obj := (kernelPullback_hom_isPullback f g).lift a₀ b₀ h₀
  have hl₀_ι :
      l₀ ≫ (kernelPullbackι f g).hom = ambientLift := by
    -- Proof comment: the ambient lift agrees with the biproduct lift because both maps have the
    -- same first and second projections.
    change l₀ ≫ (kernelSubobject (pullbackDifference f g).hom).arrow = ambientBiprodLift a₀ b₀
    change
      (l₀ ≫ (kernelSubobject (pullbackDifference f g).hom).arrow : T ⟶ ambientBiprod (B := B) (C := C)) =
        ambientBiprodLift a₀ b₀
    apply biprod.hom_ext
    · calc
        (l₀ ≫ (kernelSubobject (pullbackDifference f g).hom).arrow) ≫ ambientBiprodFst
            = l₀ ≫ (kernelPullbackFst f g).hom := by
                simpa [kernelPullbackFst, kernelPullbackι, FilteredObject.subobjectInclusion,
                  Category.assoc]
        _ = a₀ := by
              simpa [l₀] using (kernelPullback_hom_isPullback f g).lift_fst a₀ b₀ h₀
        _ = ambientBiprodLift a₀ b₀ ≫ ambientBiprodFst := by
              simp
    · calc
        (l₀ ≫ (kernelSubobject (pullbackDifference f g).hom).arrow) ≫ ambientBiprodSnd
            = l₀ ≫ (kernelPullbackSnd f g).hom := by
                simpa [kernelPullbackSnd, kernelPullbackι, FilteredObject.subobjectInclusion,
                  Category.assoc]
        _ = b₀ := by
              simpa [l₀] using (kernelPullback_hom_isPullback f g).lift_snd a₀ b₀ h₀
        _ = ambientBiprodLift a₀ b₀ ≫ ambientBiprodSnd := by
              simp
  have hBiprodStage :
      ((ambientFilteredBiprod (B := B) (C := C)).filtration i).Factors ambientLift := by
    -- Proof comment: the ambient biproduct lift factors through the stagewise biproduct by the
    -- literal `biprod.lift a b` map on the stage objects.
    let stageArrow :
        ((B.filtration i : 𝒜) ⊞ (C.filtration i : 𝒜)) ⟶ ambientBiprod (B := B) (C := C) :=
      biprod.map (B.filtration i).arrow (C.filtration i).arrow
    change (Subobject.mk stageArrow).Factors (ambientBiprodLift a₀ b₀)
    rw [Subobject.mk_factors_iff]
    refine ⟨biprod.lift a b, ?_⟩
    apply biprod.hom_ext <;>
      simp [stageArrow, a₀, b₀, Category.assoc]
  have hStage :
      ((kernelPullback f g).filtration i).Factors l₀ := by
    -- Proof comment: the filtration on `kernelPullback f g` is induced from the ambient
    -- biproduct filtration along the kernel inclusion.
    rw [show ((kernelPullback f g).filtration i) =
      (Subobject.pullback (kernelSubobject (pullbackDifference f g).hom).arrow).obj
        ((ambientFilteredBiprod (B := B) (C := C)).filtration i) by
      rfl]
    refine
      (pullback_factors_iff
        (f := (kernelSubobject (pullbackDifference f g).hom).arrow)
        (y := ((ambientFilteredBiprod (B := B) (C := C)).filtration i))
        (h := l₀)).2 ?_
    simpa [kernelPullbackι] using hl₀_ι ▸ hBiprodStage
  let l : T ⟶ (kernelPullback f g).filtration i :=
    ((kernelPullback f g).filtration i).factorThru l₀ hStage
  refine ⟨l, ?_, ?_⟩
  · -- Proof comment: cancel the stage inclusion of `B` after rewriting through the ambient lift.
    have hl_arrow : l ≫ ((kernelPullback f g).filtration i).arrow = l₀ := by
      simpa [l] using ((kernelPullback f g).filtration i).factorThru_arrow l₀ hStage
    apply (cancel_mono (B.filtration i).arrow).1
    calc
      (l ≫ stageMap (kernelPullbackFst f g) i) ≫ (B.filtration i).arrow
          = l ≫ ((kernelPullback f g).filtration i).arrow ≫ (kernelPullbackFst f g).hom := by
              simpa [Category.assoc, stageMap_comm]
      _ = l₀ ≫ (kernelPullbackFst f g).hom := by
            simpa [Category.assoc] using
              congrArg (fun k : T ⟶ (kernelPullback f g).obj ↦ k ≫ (kernelPullbackFst f g).hom)
                hl_arrow
      _ = a₀ := by
            simpa [l₀] using (kernelPullback_hom_isPullback f g).lift_fst a₀ b₀ h₀
      _ = a ≫ (B.filtration i).arrow := by
            simp [a₀]
  · -- Proof comment: the same ambient comparison with the right projection recovers `b`.
    have hl_arrow : l ≫ ((kernelPullback f g).filtration i).arrow = l₀ := by
      simpa [l] using ((kernelPullback f g).filtration i).factorThru_arrow l₀ hStage
    apply (cancel_mono (C.filtration i).arrow).1
    calc
      (l ≫ stageMap (kernelPullbackSnd f g) i) ≫ (C.filtration i).arrow
          = l ≫ ((kernelPullback f g).filtration i).arrow ≫ (kernelPullbackSnd f g).hom := by
              simpa [Category.assoc, stageMap_comm]
      _ = l₀ ≫ (kernelPullbackSnd f g).hom := by
            simpa [Category.assoc] using
              congrArg (fun k : T ⟶ (kernelPullback f g).obj ↦ k ≫ (kernelPullbackSnd f g).hom)
                hl_arrow
      _ = b₀ := by
            simpa [l₀] using (kernelPullback_hom_isPullback f g).lift_snd a₀ b₀ h₀
      _ = b ≫ (C.filtration i).arrow := by
            simp [b₀]

/-- Helper for Lemma 12.19.11: the `i`-th stage of the kernel-model pullback is a pullback of the
stage maps of `f` and `g`. -/
private theorem stageMap_kernelPullback_isPullback
    (f : B ⟶ A) (g : C ⟶ A) (i : ℤ) :
    IsPullback (stageMap (kernelPullbackFst f g) i) (stageMap (kernelPullbackSnd f g) i)
      (stageMap f i) (stageMap g i) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · -- Proof comment: stage maps respect composition, so the ambient pullback commutativity
    -- immediately descends to the `i`-th stage square.
    calc
      stageMap (kernelPullbackFst f g) i ≫ stageMap f i
          = stageMap (kernelPullbackFst f g ≫ f) i := by
              rw [← stageMap_comp]
      _ = stageMap (kernelPullbackSnd f g ≫ g) i := by
            simpa using congrArg (fun k : kernelPullback f g ⟶ A ↦ stageMap k i)
              (kernelPullback_isPullback f g).w
      _ = stageMap (kernelPullbackSnd f g) i ≫ stageMap g i := by
            rw [stageMap_comp]
  · intro T φ ψ hfst hsnd
    exact stageMap_kernelPullback_hom_ext f g i hfst hsnd
  · intro T a b h
    exact stageMap_kernelPullback_exists_lift f g i a b h

/-- Helper for Lemma 12.19.11: in any pullback square, the image of the right leg is the
pullback of the image of the left-bottom map along the bottom-right map. -/
private theorem imageSubobject_snd_eq_pullback_image_of_isPullback
    {P X Y Z : 𝒜} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (sq : IsPullback fst snd f g) :
    imageSubobject snd = (Subobject.pullback g).obj (imageSubobject f) := by
  -- Proof comment: factor `snd` through the pullback of `imageSubobject f` along `g`; this new
  -- map is a pullback of the epimorphism `factorThruImageSubobject f`, so pushing its image
  -- forward recovers the pullback subobject.
  have hComm :
      (fst ≫ factorThruImageSubobject f) ≫ (imageSubobject f).arrow = snd ≫ g := by
    simpa [Category.assoc] using sq.w
  let R : Subobject Y := (Subobject.pullback g).obj (imageSubobject f)
  let c : P ⟶ R :=
    (Subobject.isPullback g (imageSubobject f)).lift
      (fst ≫ factorThruImageSubobject f)
      snd
      hComm
  have hc_snd : c ≫ R.arrow = snd := by
    simpa [R, c] using
      (Subobject.isPullback g (imageSubobject f)).lift_snd
        (fst ≫ factorThruImageSubobject f)
        snd
        hComm
  have hc_pullbackπ :
      c ≫ Subobject.pullbackπ g (imageSubobject f) =
        fst ≫ factorThruImageSubobject f := by
    simpa [R, c] using
      (Subobject.isPullback g (imageSubobject f)).lift_fst
        (fst ≫ factorThruImageSubobject f)
        snd
        hComm
  have hc_isPullback :
      IsPullback fst c (factorThruImageSubobject f) (Subobject.pullbackπ g (imageSubobject f)) := by
    have hRight :
        IsPullback R.arrow (Subobject.pullbackπ g (imageSubobject f)) g
          (imageSubobject f).arrow := by
      simpa [R] using (Subobject.isPullback g (imageSubobject f)).flip
    refine ((IsPullback.paste_horiz_iff hRight hc_pullbackπ).1 ?_).flip
    simpa [hc_snd, Category.assoc] using (sq.flip : IsPullback snd fst g f)
  letI : Epi (factorThruImageSubobject f) := by infer_instance
  letI : Epi c := Abelian.epi_snd_of_isLimit
    (f := factorThruImageSubobject f)
    (g := Subobject.pullbackπ g (imageSubobject f))
    hc_isPullback.isLimit
  calc
    imageSubobject snd = imageSubobject (c ≫ R.arrow) := by rw [hc_snd]
    _ = imageSubobject R.arrow := by
          rw [imageSubobject_comp_eq_of_epi c R.arrow]
    _ = imageSubobject (((Subobject.pullback g).obj (imageSubobject f)).arrow) := by
          rfl
    _ = R := by
          simpa [R] using (Limits.imageSubobject_mono R.arrow)

/-- Helper for Lemma 12.19.11: the stage image of the canonical right pullback leg is the pullback
of the stage image of `f` along the stage map of `g`. -/
private theorem kernelPullbackSnd_stageImage_eq_pullback_stageImage
    (f : B ⟶ A) (g : C ⟶ A) (i : ℤ) :
    imageSubobject (stageMap (kernelPullbackSnd f g) i) =
      (Subobject.pullback (stageMap g i)).obj (imageSubobject (stageMap f i)) := by
  -- Proof comment: the stage square is itself a pullback square, so the generic image formula
  -- applies immediately.
  simpa using
    imageSubobject_snd_eq_pullback_image_of_isPullback
      (stageMap (kernelPullbackFst f g) i)
      (stageMap (kernelPullbackSnd f g) i)
      (stageMap f i)
      (stageMap g i)
      (stageMap_kernelPullback_isPullback f g i)

/-- Helper for Lemma 12.19.11: strictness of `f` rewrites the stage image of `stageMap f i` as
the pullback of the ambient image of `f.hom` along the stage inclusion of `A`. -/
private theorem stageImage_eq_pullback_image_of_strict
    (f : B ⟶ A) (hf : Strict f) (i : ℤ) :
    imageSubobject (stageMap f i) =
      (Subobject.pullback ((A.filtration i).arrow)).obj (imageSubobject f.hom) := by
  have hi :
      (Subobject.map ((A.filtration i).arrow)).obj (imageSubobject (stageMap f i)) =
        (Subobject.map ((A.filtration i).arrow)).obj
          ((Subobject.pullback ((A.filtration i).arrow)).obj (imageSubobject f.hom)) := by
    -- Proof comment: compare both subobjects after mapping them into `A.obj`, where strictness
    -- of `f` gives the standard `image ∩ stage` formula.
    calc
      (Subobject.map ((A.filtration i).arrow)).obj (imageSubobject (stageMap f i))
          = imageSubobject (stageMap f i ≫ (A.filtration i).arrow) := by
              rw [← imageSubobject_comp_eq_map_of_mono (stageMap f i) ((A.filtration i).arrow)]
      _ = imageSubobject ((B.filtration i).arrow ≫ f.hom) := by
            rw [stageMap_comm]
      _ = B.filtration.quotient f.hom i := by
            rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
      _ = imageSubobject f.hom ⊓ A.filtration i := by
            exact (strict_iff_quotient_eq_inf f).1 hf i
      _ = (Subobject.map ((A.filtration i).arrow)).obj
            ((Subobject.pullback ((A.filtration i).arrow)).obj (imageSubobject f.hom)) := by
            simpa [inf_comm] using
              (Subobject.inf_eq_map_pullback (A.filtration i) (imageSubobject f.hom))
  have hpull := congrArg ((Subobject.pullback ((A.filtration i).arrow)).obj) hi
  -- Proof comment: pulling back along the mono stage inclusion inverts the forward map on
  -- subobjects of `A.filtration i`.
  simpa [Subobject.pullback_self] using hpull

/-- Helper for Lemma 12.19.11: the ambient image of the canonical right pullback leg is the
pullback of the image of `f.hom` along `g.hom`. -/
private theorem kernelPullbackSnd_image_eq_pullback_image
    (f : B ⟶ A) (g : C ⟶ A) :
    imageSubobject (kernelPullbackSnd f g).hom =
      (Subobject.pullback g.hom).obj (imageSubobject f.hom) := by
  -- Proof comment: this is the ambient pullback square version of the same generic image
  -- computation.
  simpa using
    imageSubobject_snd_eq_pullback_image_of_isPullback
      (kernelPullbackFst f g).hom
      (kernelPullbackSnd f g).hom
      f.hom
      g.hom
      (kernelPullback_hom_isPullback f g)

/-- Helper for Lemma 12.19.11: pulling back `imageSubobject f.hom` first along the stage inclusion
of `A` and then along `stageMap g i` agrees with pulling back first along `g.hom` and then along
the stage inclusion of `C`. -/
private theorem stagePullback_pullback_image_eq
    (f : B ⟶ A) (g : C ⟶ A) (i : ℤ) :
    (Subobject.pullback (stageMap g i)).obj
        ((Subobject.pullback ((A.filtration i).arrow)).obj (imageSubobject f.hom)) =
      (Subobject.pullback ((C.filtration i).arrow)).obj
        ((Subobject.pullback g.hom).obj (imageSubobject f.hom)) := by
  -- Proof comment: both iterated pullbacks are pullbacks of `imageSubobject f.hom` along the
  -- same composite `C.filtration i ⟶ A.obj`.
  calc
    (Subobject.pullback (stageMap g i)).obj
        ((Subobject.pullback ((A.filtration i).arrow)).obj (imageSubobject f.hom))
        =
          (Subobject.pullback (stageMap g i ≫ (A.filtration i).arrow)).obj
            (imageSubobject f.hom) := by
              symm
              exact Subobject.pullback_comp
                (stageMap g i) ((A.filtration i).arrow) (imageSubobject f.hom)
    _ = (Subobject.pullback ((C.filtration i).arrow ≫ g.hom)).obj (imageSubobject f.hom) := by
          rw [stageMap_comm]
    _ = (Subobject.pullback ((C.filtration i).arrow)).obj
          ((Subobject.pullback g.hom).obj (imageSubobject f.hom)) := by
            exact Subobject.pullback_comp
              ((C.filtration i).arrow) g.hom (imageSubobject f.hom)

/-- Helper for Lemma 12.19.11: mapping a pullback subobject along the stage inclusion of `C`
recovers the intersection with the corresponding stage. -/
private theorem map_stageArrow_pullback_eq_inf
    (f : B ⟶ A) (g : C ⟶ A) (i : ℤ) :
    (Subobject.map ((C.filtration i).arrow)).obj
        ((Subobject.pullback ((C.filtration i).arrow)).obj
          ((Subobject.pullback g.hom).obj (imageSubobject f.hom))) =
      (Subobject.pullback g.hom).obj (imageSubobject f.hom) ⊓ C.filtration i := by
  -- Proof comment: mapping a pullback along the stage inclusion yields the ambient intersection
  -- with that stage.
  simpa [inf_comm] using
    (Subobject.inf_eq_map_pullback
      (C.filtration i)
      ((Subobject.pullback g.hom).obj (imageSubobject f.hom))).symm

/-- Helper for Lemma 12.19.11: a filtered isomorphism is strict. -/
private theorem strict_iso_hom {X Y : FilteredObject 𝒜} (e : X ≅ Y) :
    Strict e.hom := by
  letI : IsIso e.hom.hom := Functor.map_isIso (FilteredObject.forget (C := 𝒜)) e.hom
  letI : Mono e.hom.hom := by infer_instance
  -- Proof comment: the induced filtration for an isomorphism is the pullback filtration, and the
  -- inverse returns every pulled-back stage to the original one.
  refine (strict_iff_induced_filtration_of_mono e.hom).2 ?_
  refine OrderHom.ext _ _ ?_
  funext i
  refine le_antisymm ?_ ?_
  · -- Proof comment: filtration preservation of `e.hom` gives the easy inclusion into the
    -- pullback filtration.
    simpa using pullback_preserves e.hom i
  · -- Proof comment: factor the pullback stage into `Y.filtration i`, then compose with the
    -- inverse isomorphism and cancel `e.hom ≫ e.inv = 𝟙`.
    let P : Subobject X.obj := (Subobject.pullback e.hom.hom).obj (Y.filtration i)
    have hP :
        (Y.filtration i).Factors (P.arrow ≫ e.hom.hom) := by
      exact
        (pullback_factors_iff (f := e.hom.hom) (y := Y.filtration i) (h := P.arrow)).1 <| by
          simpa [P] using (Subobject.factors_self P)
    let u : (P : 𝒜) ⟶ Y.filtration i :=
      (Y.filtration i).factorThru (P.arrow ≫ e.hom.hom) hP
    let v : (Y.filtration i : 𝒜) ⟶ X.filtration i :=
      (X.filtration i).factorThru ((Y.filtration i).arrow ≫ e.inv.hom) (e.inv.preserves i)
    have hFactors : (X.filtration i).Factors P.arrow := by
      rw [Subobject.factors_iff]
      change ∃ t : (P : 𝒜) ⟶ X.filtration i, t ≫ (X.filtration i).arrow = P.arrow
      refine ⟨u ≫ v, ?_⟩
      calc
        (u ≫ v) ≫ (X.filtration i).arrow
            = u ≫ (Y.filtration i).arrow ≫ e.inv.hom := by
                simp [v]
        _ = P.arrow ≫ e.hom.hom ≫ e.inv.hom := by
              simp [u, Category.assoc]
        _ = P.arrow := by
              have hInv : e.hom.hom ≫ e.inv.hom = 𝟙 X.obj := by
                exact congrArg FilteredObject.Hom.hom e.hom_inv_id
              simpa [Category.assoc] using
                congrArg (fun k : X.obj ⟶ X.obj ↦ P.arrow ≫ k) hInv
    exact Subobject.le_of_factors hFactors

/-- Helper for Lemma 12.19.11: if `f` is strict, then the stage quotient of the canonical right
pullback leg identifies with the expected pullback-image intersection inside `C.obj`. -/
private theorem kernelPullbackSnd_stageQuotient_eq_pullbackImage_inf_of_strict
    (f : B ⟶ A) (g : C ⟶ A) (hf : Strict f) (i : ℤ) :
    (kernelPullback f g).filtration.quotient (kernelPullbackSnd f g).hom i =
      (Subobject.pullback g.hom).obj (imageSubobject f.hom) ⊓ C.filtration i := by
  -- Proof comment: rewrite the quotient stage as an image, replace that image by the stagewise
  -- pullback of `imageSubobject f.hom`, then push the stage inclusion back to an intersection.
  calc
    (kernelPullback f g).filtration.quotient (kernelPullbackSnd f g).hom i
        = imageSubobject
            (((kernelPullback f g).filtration i).arrow ≫ (kernelPullbackSnd f g).hom) := by
              rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = imageSubobject
          (stageMap (kernelPullbackSnd f g) i ≫ (C.filtration i).arrow) := by
            rw [stageMap_comm]
    _ = (Subobject.map ((C.filtration i).arrow)).obj
          (imageSubobject (stageMap (kernelPullbackSnd f g) i)) := by
            rw [imageSubobject_comp_eq_map_of_mono
              (stageMap (kernelPullbackSnd f g) i) ((C.filtration i).arrow)]
    _ = (Subobject.map ((C.filtration i).arrow)).obj
          ((Subobject.pullback (stageMap g i)).obj (imageSubobject (stageMap f i))) := by
            rw [kernelPullbackSnd_stageImage_eq_pullback_stageImage]
    _ = (Subobject.map ((C.filtration i).arrow)).obj
          ((Subobject.pullback (stageMap g i)).obj
            ((Subobject.pullback ((A.filtration i).arrow)).obj (imageSubobject f.hom))) := by
            rw [stageImage_eq_pullback_image_of_strict f hf]
    _ = (Subobject.map ((C.filtration i).arrow)).obj
          ((Subobject.pullback ((C.filtration i).arrow)).obj
            ((Subobject.pullback g.hom).obj (imageSubobject f.hom))) := by
            rw [stagePullback_pullback_image_eq]
    _ = (Subobject.pullback g.hom).obj (imageSubobject f.hom) ⊓ C.filtration i := by
          rw [map_stageArrow_pullback_eq_inf]

/-- Helper for Lemma 12.19.11: in the canonical kernel-model pullback, strictness of `f`
forces strictness of the projection to `C`. -/
private theorem strict_kernelPullbackSnd_of_strict (f : B ⟶ A) (g : C ⟶ A) (hf : Strict f) :
    Strict (kernelPullbackSnd f g) := by
  refine (strict_iff_quotient_eq_inf (kernelPullbackSnd f g)).2 ?_
  intro i
  rw [kernelPullbackSnd_stageQuotient_eq_pullbackImage_inf_of_strict f g hf i]
  rw [kernelPullbackSnd_image_eq_pullback_image]

/-- Helper for Lemma 12.19.11: transport strictness from the canonical kernel-model pullback to
the owner-level `pullback f g`. -/
private theorem strict_pullback_snd_of_strict_aux
    (f : B ⟶ A) (g : C ⟶ A) (hf : Strict f) :
    Strict (pullback.snd f g : pullback f g ⟶ C) := by
  -- Proof comment: transport strictness from the canonical kernel-model pullback along the
  -- pullback isomorphism supplied by the universal property.
  let e : kernelPullback f g ≅ pullback f g := (kernelPullback_isPullback f g).isoPullback
  letI : IsIso e.symm.hom.hom :=
    Functor.map_isIso (FilteredObject.forget (C := 𝒜)) e.symm.hom
  letI : Epi e.symm.hom.hom := by infer_instance
  have he : Strict e.symm.hom := strict_iso_hom e.symm
  have hkernel : Strict (kernelPullbackSnd f g) := strict_kernelPullbackSnd_of_strict f g hf
  simpa [e, kernelPullbackSnd] using
    (strict_comp_of_epi e.symm.hom (kernelPullbackSnd f g) he hkernel)

/-- In a pullback square of filtered objects, strictness of the left map forces strictness of the
right map. -/
theorem strict_snd_of_isPullback_of_strict
    (f : B ⟶ A) (g : C ⟶ A) {P : FilteredObject 𝒜} {g' : P ⟶ B} {f' : P ⟶ C}
    (sq : IsPullback g' f' f g) (hf : Strict f) :
    Strict f' := by
  -- Proof comment: compare the given pullback square with the owner-level pullback, then compose
  -- the strict owner-level projection with the strict pullback isomorphism from `sq`.
  let e : P ≅ pullback f g := sq.isoPullback
  letI : IsIso e.hom.hom := Functor.map_isIso (FilteredObject.forget (C := 𝒜)) e.hom
  letI : Epi e.hom.hom := by infer_instance
  have he : Strict e.hom := strict_iso_hom e
  have hpull : Strict (pullback.snd f g : pullback f g ⟶ C) :=
    strict_pullback_snd_of_strict_aux f g hf
  simpa [e] using
    (strict_comp_of_epi e.hom (pullback.snd f g : pullback f g ⟶ C) he hpull)

/-- In the canonical pullback square of filtered objects, strictness of the left map forces
strictness of the induced projection to the right factor. -/
theorem strict_pullback_snd_of_strict (f : B ⟶ A) (g : C ⟶ A) (hf : Strict f) :
    Strict (pullback.snd f g : pullback f g ⟶ C) := by
  exact strict_snd_of_isPullback_of_strict f g (IsPullback.of_hasPullback f g) hf

end FilteredObject.Hom

-- Proof sketch: realize the pullback in `FilteredObject` via the owner-level `HasPullback f g`
-- instance coming from the kernel presentation inside `B ⊞ C`; then package
-- the canonical pullback object and projections. The strictness clause is the square-level theorem
-- `strict_snd_of_isPullback_of_strict` applied to the canonical pullback square.
/-- Lemma 12.19.11: for morphisms `f : B ⟶ A` and `g : C ⟶ A` of filtered objects in an abelian
category, there exists a fibre product square in the filtered category, and if `f` is strict, then
the induced morphism `f' : B ×[A] C ⟶ C` is strict. -/
@[stacks 05SN]
theorem exists_filtered_pullback_preserving_strictness
    {A B C : FilteredObject 𝒜} (f : B ⟶ A) (g : C ⟶ A) :
    ∃ (P : FilteredObject 𝒜) (g' : P ⟶ B) (f' : P ⟶ C),
      IsPullback g' f' f g ∧ (Strict f → Strict f') := by
  refine ⟨pullback f g, pullback.fst f g, pullback.snd f g, IsPullback.of_hasPullback f g, ?_⟩
  exact strict_pullback_snd_of_strict f g

end CategoryTheory
