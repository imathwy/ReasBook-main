import Mathlib
import StacksProject_2024.Chap15.Lemma_15_65_2
import StacksProject_2024.Chap15.Lemma_15_65_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

private abbrev ModCat := ModuleCat.{u} R
local notation "DMod" => DerivedCategory (ModCat (R := R))
local notation "Cpx" => CochainComplex (ModCat (R := R)) ℤ

/-- Helper for Lemma 15.65.6: the zero cochain complex over `ModuleCat R`. -/
private abbrev zeroCpx : Cpx := 0

/- Domain-style sampling for Lemma 15.65.6:
- primary domain: pseudo-coherent object properties in the derived category `D(R)` and their
  closure under distinguished triangles;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.IsMPseudoCoherent`,
  `isMPseudoCoherent_obj₃_of_distinguishedTriangle`,
  `ObjectProperty.IsTriangulated`;
- best owner abstraction: the reusable owner statement is that the object property
  `fun K : DMod ↦ K.IsPseudoCoherent` is triangulated; the three numbered textbook statements are
  its source-facing `obj₁`/`obj₂`/`obj₃` consequences;
- primitive vs. derived:
  primitive data are the absolute notions `DerivedCategory.IsMPseudoCoherent` and
  `DerivedCategory.IsPseudoCoherent` from Definition `15.65.1`;
  the distinguished-triangle closure of `m`-pseudo-coherence from Lemma `15.65.2` is derived API,
  and this file upgrades it to pseudo-coherence;
- source/core/bridge triage:
  `source-facing`: the three numbered two-out-of-three statements below;
  `core/canonical`: `ObjectProperty.IsTriangulated (fun K : DMod ↦ K.IsPseudoCoherent)`;
  `bridge/view`: deriving the three source-facing consequences from that owner theorem.
- layer: this file keeps the source-facing statements but factors them through the canonical
  triangulated-object-property owner. -/

-- Proof sketch: choose any representative cochain complex of `K` in the derived category. Lemma
-- `15.65.5` characterizes pseudo-coherence of that representative by `m`-pseudo-coherence for all
-- integers `m`, and transport across the chosen isomorphism shows that this depends only on the
-- derived object `K`.
/-- Helper for Lemma 15.65.6: pseudo-coherence is invariant under isomorphism in `D(R)`. -/
private theorem isPseudoCoherent_of_iso {K L : DMod} (e : K ≅ L)
    (hK : K.IsPseudoCoherent) :
    L.IsPseudoCoherent := by
  rcases hK with ⟨E, hEbounded, hEfree, α, hα⟩
  -- Compose the chosen bounded-above finite-free model with the target isomorphism.
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Companion bridge for Lemma 15.65.6: a derived `R`-complex is pseudo-coherent exactly when it
is `m`-pseudo-coherent for every integer `m`. -/
theorem isPseudoCoherent_iff_forall_isMPseudoCoherent
    (K : DMod) :
    K.IsPseudoCoherent ↔ ∀ m : ℤ, K.IsMPseudoCoherent m := by
  let E : CochainComplex (ModuleCat R) ℤ := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj E ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hTFAE := cochainComplex_pseudoCoherent_tfae (R := R) E
  have hiffE : E.IsPseudoCoherent ↔ ∀ m : ℤ, E.IsMPseudoCoherent m :=
    hTFAE.out 0 1
  constructor
  · intro hK m
    -- Move to a chosen cochain representative where Lemma `15.65.5` applies verbatim.
    have hE : (DerivedCategory.Q.obj E).IsPseudoCoherent :=
      isPseudoCoherent_of_iso e.symm hK
    have hEm : (DerivedCategory.Q.obj E).IsMPseudoCoherent m :=
      (hiffE.mp hE) m
    -- Transport the fixed-degree conclusion back to `K`.
    exact isMPseudoCoherent_of_iso e m hEm
  · intro hK
    -- Pull the degreewise hypothesis back to the chosen representative.
    have hEall : ∀ m : ℤ, (DerivedCategory.Q.obj E).IsMPseudoCoherent m := fun m ↦
      isMPseudoCoherent_of_iso e.symm m (hK m)
    have hE : (DerivedCategory.Q.obj E).IsPseudoCoherent :=
      hiffE.mpr hEall
    -- Push the bounded-above finite-free model forward along the comparison isomorphism.
    exact isPseudoCoherent_of_iso e hE

instance isPseudoCoherent_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : DMod ↦ K.IsPseudoCoherent) where
  of_iso {X Y} e hK := by
    apply (isPseudoCoherent_iff_forall_isMPseudoCoherent (R := R) Y).2
    intro m
    let P : ObjectProperty DMod := fun K ↦ K.IsMPseudoCoherent m
    exact P.prop_of_iso e ((isPseudoCoherent_iff_forall_isMPseudoCoherent (R := R) X).1 hK m)

-- Proof sketch: combine Lemma `15.65.5`, which upgrades pseudo-coherence to
-- `m`-pseudo-coherence in every degree, with Lemma `15.65.2`, which gives the corresponding
-- two-out-of-three property for distinguished triangles degreewise in `m`. The resulting object
-- property is closed under isomorphisms by the previous instance, and the zero/shift axioms are
-- handled directly from the definition.
/-- Helper for Lemma 15.65.6: the zero cochain complex is termwise finite free. -/
private instance zero_isTermwiseFiniteFree :
    (zeroCpx (R := R)).IsTermwiseFiniteFree where
  out i := by
    let E0 : Cpx := zeroCpx (R := R)
    change Module.Free R ↥(E0.X i) ∧ Module.Finite R ↥(E0.X i)
    -- Each degree of the chosen zero complex is a zero module, hence free by subsingleton.
    let hzero : IsZero (E0.X i) := by
      simpa [E0] using
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i).map_isZero
          (isZero_zero Cpx : IsZero (zeroCpx (R := R)))
    letI : Subsingleton ↥(E0.X i) :=
      ModuleCat.subsingleton_of_isZero hzero
    -- Finite generation is transported from the one-point free module along a zero-object
    -- identification.
    have hfree : Module.Free R (E0.X i) :=
      Module.Free.of_subsingleton (R := R) (N := ↥(E0.X i))
    have hfinite : Module.Finite R (E0.X i) :=
      let e : ModuleCat.of R PUnit ≅ E0.X i :=
        (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)).isoZero ≪≫ hzero.isoZero.symm
      Module.Finite.equiv e.toLinearEquiv
    exact And.intro hfree hfinite

/-- Helper for Lemma 15.65.6: the image of the zero cochain complex in `D(R)` is
pseudo-coherent. -/
private theorem q_obj_zero_isPseudoCoherent :
    (DerivedCategory.Q.obj (zeroCpx (R := R))).IsPseudoCoherent := by
  change (zeroCpx (R := R)).IsPseudoCoherent
  have hId : IsIso (𝟙 (DerivedCategory.Q.obj (zeroCpx (R := R)))) := by
    infer_instance
  refine ⟨zeroCpx (R := R), ?_, inferInstance, 𝟙 _, hId⟩
  -- The zero complex is bounded above by every cutoff.
  · exact ⟨(0 : ℤ), inferInstance⟩

/-- Helper for Lemma 15.65.6: the zero object of `D(R)` is pseudo-coherent. -/
private theorem isPseudoCoherent_zero : (0 : DMod).IsPseudoCoherent := by
  let hsrc : Limits.IsZero (DerivedCategory.Q.obj (zeroCpx (R := R))) :=
    (DerivedCategory.Q).map_isZero (Limits.isZero_zero Cpx : Limits.IsZero (zeroCpx (R := R)))
  let e : DerivedCategory.Q.obj (zeroCpx (R := R)) ≅ (0 : DMod) :=
    hsrc.iso (Limits.isZero_zero DMod)
  -- Transport the explicit zero-complex model along the canonical zero-object isomorphism.
  exact isPseudoCoherent_of_iso (R := R) e q_obj_zero_isPseudoCoherent

/-- Canonical owner form of Lemma 15.65.6: pseudo-coherent objects of `D(R)` form a triangulated
object property. -/
instance isPseudoCoherent_isTriangulated :
    ObjectProperty.IsTriangulated (fun K : DMod ↦ K.IsPseudoCoherent) := by
  refine
    { exists_zero := ?_
      toIsStableUnderShift := ?_
      toIsTriangulatedClosed₂ := ?_ }
  · -- Use the explicit bounded-above finite-free zero model.
    exact ⟨(0 : DMod), Limits.isZero_zero DMod, isPseudoCoherent_zero (R := R)⟩
  · refine
      { isStableUnderShiftBy := fun n ↦ IsStableUnderShiftBy.mk <| by
          intro K hK
          -- Rewrite pseudo-coherence into the degreewise criterion from Lemma `15.65.5`.
          rw [prop_shift_iff]
          have hshift :
              K⟦n⟧.IsPseudoCoherent ↔ ∀ m : ℤ, K⟦n⟧.IsMPseudoCoherent m :=
            isPseudoCoherent_iff_forall_isMPseudoCoherent (K⟦n⟧)
          apply hshift.2
          intro m
          simpa using
            (isMPseudoCoherent_shift_iff K n (m + n)).2
              ((isPseudoCoherent_iff_forall_isMPseudoCoherent K).1 hK (m + n)) }
  · refine .mk' <| by
      intro T hT h₁ h₃
      -- Apply the degreewise two-out-of-three statement from Lemma `15.65.2`.
      have hmid :
          T.obj₂.IsPseudoCoherent ↔ ∀ m : ℤ, T.obj₂.IsMPseudoCoherent m :=
        isPseudoCoherent_iff_forall_isMPseudoCoherent T.obj₂
      apply hmid.2
      intro m
      exact
        isMPseudoCoherent_obj₂_of_distinguishedTriangle T hT
          ((isPseudoCoherent_iff_forall_isMPseudoCoherent T.obj₁).1 h₁ m)
          ((isPseudoCoherent_iff_forall_isMPseudoCoherent T.obj₃).1 h₃ m)

-- Proof sketch: this is the `obj₁`-`obj₂` to `obj₃` closure consequence of the triangulated
-- object property instance on pseudo-coherent objects.
/-- Lemma 15.65.6 (1): in a distinguished triangle in `D(R)`, if the first and second terms are
pseudo-coherent, then the third term is pseudo-coherent. -/
theorem isPseudoCoherent_obj₃_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsPseudoCoherent) (h₂ : T.obj₂.IsPseudoCoherent) :
    T.obj₃.IsPseudoCoherent := by
  let P : ObjectProperty DMod := fun K ↦ K.IsPseudoCoherent
  exact P.ext_of_isTriangulatedClosed₃ T hT h₁ h₂

-- Proof sketch: this is the `obj₁`-`obj₃` to `obj₂` closure consequence of the triangulated
-- object property instance on pseudo-coherent objects.
/-- Lemma 15.65.6 (2): in a distinguished triangle in `D(R)`, if the first and third terms are
pseudo-coherent, then the second term is pseudo-coherent. -/
theorem isPseudoCoherent_obj₂_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsPseudoCoherent) (h₃ : T.obj₃.IsPseudoCoherent) :
    T.obj₂.IsPseudoCoherent := by
  let P : ObjectProperty DMod := fun K ↦ K.IsPseudoCoherent
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

-- Proof sketch: this is the `obj₂`-`obj₃` to `obj₁` closure consequence of the triangulated
-- object property instance on pseudo-coherent objects.
/-- Lemma 15.65.6 (3): in a distinguished triangle in `D(R)`, if the second and third terms are
pseudo-coherent, then the first term is pseudo-coherent. -/
theorem isPseudoCoherent_obj₁_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : T.obj₂.IsPseudoCoherent) (h₃ : T.obj₃.IsPseudoCoherent) :
    T.obj₁.IsPseudoCoherent := by
  let P : ObjectProperty DMod := fun K ↦ K.IsPseudoCoherent
  exact P.ext_of_isTriangulatedClosed₁ T hT h₂ h₃

end

end CategoryTheory
