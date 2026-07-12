import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra CategoryTheory Limits
open scoped TensorProduct

universe u w

section

variable {J : Type u} [Category.{u} J] [IsFiltered J]

/-- Helper for Lemma 10.138.15: the canonical ring hom from `ULift ℤ` to a commutative ring. -/
def ulift_int_hom (A : Type u) [CommRing A] : ULift.{u} ℤ →+* A :=
  (Int.castRingHom A).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom

omit [IsFiltered J] in
/-- Helper for Lemma 10.138.15: every morphism in a diagram of commutative rings commutes with the
canonical `ULift ℤ`-algebra maps. -/
lemma ulift_integers_to_ring_diagram_naturality
    (F : J ⥤ CommRingCat.{u}) {i j : J} (f : i ⟶ j) :
    ((Functor.const J).obj (CommRingCat.of (ULift.{u} ℤ))).map f ≫
        CommRingCat.ofHom (ulift_int_hom (A := F.obj j)) =
      CommRingCat.ofHom (ulift_int_hom (A := F.obj i)) ≫ F.map f := by
  -- Proof comment: ring morphisms preserve the canonical map from the initial commutative ring
  -- object `ULift ℤ`.
  apply CommRingCat.hom_ext
  ext n
  cases n with
  | up n =>
      change ((Int.castRingHom (F.obj j)) n) = (F.map f).hom ((Int.castRingHom (F.obj i)) n)
      simpa using (map_intCast ((F.map f).hom) n).symm

omit [IsFiltered J] in
/-- Helper for Lemma 10.138.15: a diagram of commutative rings carries the canonical natural
transformation from the constant `ULift ℤ`-diagram. -/
def ulift_integers_to_ring_diagram
    (F : J ⥤ CommRingCat.{u}) :
    (Functor.const J).obj (CommRingCat.of (ULift.{u} ℤ)) ⟶ F :=
  { app := fun j => CommRingCat.ofHom (ulift_int_hom (A := F.obj j))
    naturality := fun {_ _} f => ulift_integers_to_ring_diagram_naturality (F := F) f }

/- Domain-style sampling:
* primary domain: smooth commutative algebras and filtered-colimit descent of finitely presented
  algebra data;
* sampled owner declarations:
  `Algebra.Smooth.exists_finiteType`,
  `Algebra.FinitePresentation.of_finiteType`,
  `RingHom.FinitePresentation.comp`,
  `finitelyPresented_algebra_is_baseChange_of_stage`;
* best owner abstraction: `Smooth`, with finite-presentation descent treated as derived bridge API;
* layer triage:
  - `source-facing`: the filtered-colimit descent theorem for a smooth algebra over `c.pt`;
  - `core/canonical`: the owner predicate `Smooth`;
  - `bridge/view`: factoring the finite-type model through a stage and recovering `B` by tensor
    base change;
* primitive data: the filtered diagram `F`, its colimit cocone `c`, and the smooth `c.pt`-algebra
  `B`;
* derived API: the finite-type model from `Algebra.Smooth.exists_finiteType`, the finite
  presentation of that model, and the stagewise base-change recovery.
-/

-- Proof sketch: first apply `Algebra.Smooth.exists_finiteType` to descend the smooth algebra over
-- the colimit ring to a smooth algebra over a finite-type intermediate ring. Since a finite-type
-- algebra is finitely presented, Lemma `10.127.3` factors the structure map of that intermediate
-- ring through some stage of the filtered diagram. This yields a stage algebra whose primary
-- owner-level property is smoothness; base changing that smooth model along the stage map then
-- recovers `B` as companion bridge data.
/-- Lemma 10.138.15: if `c` is a filtered colimit cocone of commutative rings and `B` is smooth
over the colimit ring `c.pt`, then `B` is obtained by base change from a smooth algebra over some
stage of the diagram. The descended stage algebra naturally lives in the universe of the diagram
stages, and the tensor-product equivalence back to `B` is companion bridge data. -/
@[stacks 0CAQ]
theorem smooth_is_baseChange_of_stage_of_isColimit
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c)
    (B : Type w) [CommRing B] [Algebra c.pt B] [Smooth c.pt B] :
    ∃ (j : J) (B_j : Type u) (_ : CommRing B_j) (_ : Algebra (F.obj j) B_j),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Smooth (F.obj j) B_j ∧ Nonempty (B ≃ₐ[c.pt] c.pt ⊗[F.obj j] B_j) := by
  let α := ulift_integers_to_ring_diagram (F := F)
  -- Proof comment: first descend the smooth `c.pt`-algebra to a smooth model over a finitely
  -- generated `ℤ`-subalgebra of `c.pt`.
  obtain ⟨A₀, B₀, _instB₀, _instAlgB₀, hA₀fg, _instSmoothB₀, hB⟩ :=
    Algebra.Smooth.exists_subalgebra_fg (R := ℤ) (A := c.pt) (B := B)
  haveI : Algebra.FinitePresentation ℤ A₀ := by
    -- Proof comment: finite generation over `ℤ` upgrades to finite presentation because `ℤ` is
    -- noetherian.
    have hfiniteType : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀fg
    exact (Algebra.FinitePresentation.of_finiteType (R := ℤ) (A := A₀)).mp hfiniteType
  have hA₀fpZ : (algebraMap ℤ A₀).FinitePresentation := by
    -- Proof comment: reinterpret the algebra-level finite-presentation instance as the ring-hom
    -- predicate required by the filtered-colimit factorization theorem.
    simpa [RingHom.finitePresentation_algebraMap] using
      (show Algebra.FinitePresentation ℤ A₀ from inferInstance)
  have hA₀fp : (ulift_int_hom (A := A₀)).FinitePresentation := by
    -- Proof comment: the category-level theorem is universe-polymorphic in the base ring, so we
    -- transfer finite presentation along `ULift.ringEquiv : ULift ℤ ≃+* ℤ`.
    rw [show ulift_int_hom (A := A₀) =
        (algebraMap ℤ A₀).comp (ULift.ringEquiv.{0, u} (R := ℤ)).toRingHom by rfl]
    exact RingHom.FinitePresentation.comp hA₀fpZ
      (RingHom.FinitePresentation.of_bijective
        (ULift.ringEquiv.{0, u} (R := ℤ)).bijective)
  have hcompat :
      ∀ i,
        CommRingCat.ofHom (ulift_int_hom (A := A₀)) ≫ CommRingCat.ofHom A₀.val =
          α.app i ≫ c.ι.app i := by
    intro i
    -- Proof comment: both composites are the canonical map `ULift ℤ → c.pt`.
    apply CommRingCat.hom_ext
    ext n
    simpa [ulift_int_hom, CommRingCat.hom_comp] using
      (map_intCast ((c.ι.app i).hom) n.down).symm
  -- Proof comment: finite presentation of the intermediate `ℤ`-algebra lets its structure map
  -- factor through some stage of the filtered system.
  obtain ⟨j, φj, hφj_alg, hφj_factor⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (R := CommRingCat.of (ULift.{u} ℤ)) (F := F) (α := α)
      (S := CommRingCat.of A₀) (f := CommRingCat.ofHom (ulift_int_hom (A := A₀)))
      (c := c) (hc := _hc) hA₀fp (CommRingCat.ofHom A₀.val) hcompat
  letI : Algebra A₀ (F.obj j) := φj.hom.toAlgebra
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  let _ := hφj_alg
  have hstage_eq :
      algebraMap A₀ c.pt = (algebraMap (F.obj j) c.pt).comp (algebraMap A₀ (F.obj j)) := by
    -- Proof comment: the factorization identity is exactly the compatibility needed for the
    -- scalar tower `A₀ → F.obj j → c.pt`.
    ext a
    simpa [CommRingCat.hom_comp, RingHom.algebraMap_toAlgebra] using
      congrArg (fun k : CommRingCat.of A₀ ⟶ c.pt => k.hom a) hφj_factor
  haveI : IsScalarTower A₀ (F.obj j) c.pt := IsScalarTower.of_algebraMap_eq' hstage_eq
  let B_j : Type u := (F.obj j) ⊗[A₀] B₀
  refine ⟨j, B_j, inferInstance, inferInstance, ?_⟩
  -- Proof comment: smoothness base-changes from `A₀ → B₀` to the stage `F.obj j`, and
  -- `cancelBaseChange` identifies the resulting tensor model with the original smooth algebra.
  constructor
  · infer_instance
  · refine ⟨hB.some.trans ?_⟩
    exact (Algebra.TensorProduct.cancelBaseChange A₀ (F.obj j) c.pt c.pt B₀).symm

end
