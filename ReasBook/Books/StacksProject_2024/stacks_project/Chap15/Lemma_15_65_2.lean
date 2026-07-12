import StacksProject_2024.Chap13.Definition_13_19_1
import StacksProject_2024.Chap13.Lemma_13_4_7
import StacksProject_2024.Chap13.Lemma_13_9_2
import StacksProject_2024.Chap13.Lemma_13_19_8
import StacksProject_2024.Chap13.Lemma_13_19_11
import StacksProject_2024.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory ObjectProperty Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/- Domain-style sampling for Lemma 15.65.2:
- primary domain: `m`-pseudo-coherent objects of `D(R)` and their behavior in distinguished
  triangles;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `ObjectProperty.IsTriangulatedClosed₂`,
  `Triangle.rotate`,
  `Triangle.invRotate`,
  `rot_of_distTriang`,
  `inv_rot_of_distTriang`;
- best owner abstraction: the source-facing owner is the canonical predicate
  `DerivedCategory.IsMPseudoCoherent` on objects of `D(R)`; for a fixed `m`, the exact
  two-out-of-three owner already present in mathlib is the object property
  `(fun K : DMod ↦ K.IsMPseudoCoherent m)`;
- primitive vs. derived:
  primitive data are the owner predicate `IsMPseudoCoherent`, the shift behavior of that owner,
  and the distinguished triangle;
  derived API is clause `(1)` together with the fixed-`m` canonical
  `ObjectProperty.IsTriangulatedClosed₂` instance below; the source-facing clauses `(2)` and `(3)`
  are then recovered from that owner property and the canonical triangle rotations;
- source/core/bridge triage:
  `source-facing`: the three numbered closure statements of Lemma `15.65.2`;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherent` and the fixed-`m`
    object property `(fun K : DMod ↦ K.IsMPseudoCoherent m)` on `D(R)`;
  `bridge/view`: the shift equivalence below and the use of `Triangle.rotate` / `Triangle.invRotate`
    to move between clause `(1)` and the source-facing clauses `(2)` and `(3)`.
-/

-- Proof sketch: shift a bounded finite-free approximation of `K` termwise; the cohomology
-- comparison conditions in degrees `> m` and `= m` translate by the standard homology shift
-- isomorphisms.
/-- Helper for Lemma 15.65.2: shifting a termwise finite free complex preserves termwise finite
freeness. -/
instance isTermwiseFiniteFree_shift (E : Cpx)
    [E.IsTermwiseFiniteFree] (n : ℤ) :
    (E⟦n⟧).IsTermwiseFiniteFree where
  out i := by
    -- Identify the shifted term with the unshifted degree `i + n` term and transport the owners.
    let e : ((E⟦n⟧).X i) ≅ E.X (i + n) :=
      E.shiftFunctorObjXIso n i (i + n) rfl
    exact
      ⟨Module.Free.of_equiv e.symm.toLinearEquiv,
        Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.surjective⟩

/-- Helper for Lemma 15.65.2: `m`-pseudo-coherence is invariant under isomorphism. -/
theorem isMPseudoCoherent_of_iso {K L : DMod} (e : K ≅ L) (m : ℤ)
    (hK : K.IsMPseudoCoherent m) :
    L.IsMPseudoCoherent m := by
  rcases hK with ⟨E, hbounds, hfree, α, hαgt, hαm⟩
  -- Compose the chosen approximation with the target isomorphism.
  refine ⟨E, hbounds, hfree, α ≫ e.hom, ?_, ?_⟩
  · intro i hi
    simpa using hαgt i hi
  · simpa [Functor.map_comp] using
      (show Epi ((H m).map α ≫ (H m).map e.hom) by infer_instance)

/-- Helper for Lemma 15.65.2: shifting a derived object by `n` shifts its degree-`i` homology to
degree `i + n`. -/
noncomputable def homology_shift_iso (K : DMod) (i n : ℤ) :
    (H i).obj (K⟦n⟧) ≅ (H (i + n)).obj K :=
  ((H 0).shiftIso n i (i + n) (add_comm n i)).app K

/-- Helper for Lemma 15.65.2: if `f ≫ e.hom` is an epimorphism and `e` is an isomorphism, then
`f` is already an epimorphism. -/
private theorem epi_of_epi_comp_iso
    {X Y Z : ModuleCat R} (f : X ⟶ Y) (e : Y ≅ Z) [Epi (f ≫ e.hom)] :
    Epi f := by
  rw [CategoryTheory.epi_iff_forall_injective]
  intro W
  let hcomp :=
    (CategoryTheory.epi_iff_forall_injective (f ≫ e.hom)).1
      (show Epi (f ≫ e.hom) by infer_instance) W
  intro u v huv
  have huv' : (f ≫ e.hom) ≫ (e.inv ≫ u) = (f ≫ e.hom) ≫ (e.inv ≫ v) := by
    simpa [Category.assoc] using huv
  have heq : e.inv ≫ u = e.inv ≫ v := hcomp huv'
  exact (cancel_epi e.inv).1 heq

/-- Helper for Lemma 15.65.2: conjugating a `Qh`-image along `quotientCompQhIso` recovers the
corresponding `Q`-image. -/
private theorem quotientCompQhIso_homCongr_map
    {K L : Cpx}
    (f : K ⟶ L) :
    (Iso.homCongr
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L))
      (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f)) =
        DerivedCategory.Q.map f := by
  -- This is the naturality square for the comparison isomorphism `quotient ⋙ Qh ≅ Q`.
  change
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
        DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
      DerivedCategory.Q.map f
  have hnat :
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
        (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K ≫
          DerivedCategory.Q.map f := by
    simpa [Functor.comp_map] using
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.naturality f
  calc
    (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
        DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f) ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app L =
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app K ≫
          DerivedCategory.Q.map f) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app K ≫ k)
                hnat
    _ = DerivedCategory.Q.map f := by
          simpa using
            (Iso.inv_hom_id_assoc
              ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
              (DerivedCategory.Q.map f))

/-- Helper for Lemma 15.65.2: shifting an `m`-pseudo-coherent object by `n` lowers the
pseudo-coherence index by `n`. -/
theorem isMPseudoCoherent_shift (K : DMod) (n m : ℤ)
    (hK : K.IsMPseudoCoherent m) :
    (K⟦n⟧).IsMPseudoCoherent (m - n) := by
  rcases hK with ⟨E, ⟨a, b, hEa, hEb⟩, hEfree, α, hαgt, hαm⟩
  letI : E.IsStrictlyGE a := hEa
  letI : E.IsStrictlyLE b := hEb
  have hEshiftGE : (E⟦n⟧).IsStrictlyGE (a - n) := by
    -- Shift the lower support bound by the same amount as the complex.
    simpa using E.isStrictlyGE_shift a n (a - n) (by omega)
  have hEshiftLE : (E⟦n⟧).IsStrictlyLE (b - n) := by
    -- Shift the upper support bound in the same way.
    simpa using E.isStrictlyLE_shift b n (b - n) (by omega)
  let αn : DerivedCategory.Q.obj (E⟦n⟧) ⟶ K⟦n⟧ :=
    ((DerivedCategory.Q.commShiftIso n).app E).hom ≫ α⟦n⟧'
  refine ⟨E⟦n⟧, ⟨a - n, b - n, hEshiftGE, hEshiftLE⟩, inferInstance, αn, ?_, ?_⟩
  · intro i hi
    have hi' : m < i + n := by
      omega
    let eSource :
        (H i).obj (DerivedCategory.Q.obj (E⟦n⟧)) ≅
          (H (i + n)).obj (DerivedCategory.Q.obj E) :=
      (H i).mapIso ((DerivedCategory.Q.commShiftIso n).app E) ≪≫
        homology_shift_iso (DerivedCategory.Q.obj E) i n
    let eTarget : (H i).obj (K⟦n⟧) ≅ (H (i + n)).obj K :=
      homology_shift_iso K i n
    have hshiftNat :
        (H i).map (α⟦n⟧') ≫ eTarget.hom =
          (homology_shift_iso (DerivedCategory.Q.obj E) i n).hom ≫
            (H (i + n)).map α := by
      -- Naturality of the homology shift comparison turns the shifted map on `α` into the
      -- unshifted map in degree `i + n`.
      exact (H 0).shiftIso_hom_naturality n i (i + n) (add_comm n i) α
    have hcomm :
        (H i).map αn ≫ eTarget.hom = eSource.hom ≫ (H (i + n)).map α := by
      -- First pass through `Q.commShiftIso`, then use naturality of `shiftIso`.
      have hmid :
          (H i).map αn ≫ eTarget.hom =
            (H i).map ((DerivedCategory.Q.commShiftIso n).app E).hom ≫
              (homology_shift_iso (DerivedCategory.Q.obj E) i n).hom ≫
                (H (i + n)).map α := by
        calc
          (H i).map αn ≫ eTarget.hom =
              (H i).map ((DerivedCategory.Q.commShiftIso n).app E).hom ≫
                ((H i).map (α⟦n⟧') ≫ eTarget.hom) := by
                  simp [αn, Functor.map_comp, Category.assoc]
          _ = (H i).map ((DerivedCategory.Q.commShiftIso n).app E).hom ≫
                (homology_shift_iso (DerivedCategory.Q.obj E) i n).hom ≫
                  (H (i + n)).map α := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun k ↦ (H i).map ((DerivedCategory.Q.commShiftIso n).app E).hom ≫ k)
                        hshiftNat
      simpa [eSource, Category.assoc] using hmid
    haveI : IsIso eSource.hom := by infer_instance
    haveI : IsIso ((H (i + n)).map α) := hαgt (i + n) hi'
    have hcompIso : IsIso ((H i).map αn ≫ eTarget.hom) := by
      rw [hcomm]
      infer_instance
    exact (isIso_comp_right_iff ((H i).map αn) eTarget.hom).1 hcompIso
  · let i := m - n
    have hi : i + n = m := by
      omega
    have hni : n + i = m := by
      simpa [add_comm] using hi
    let eSource :
        (H i).obj (DerivedCategory.Q.obj (E⟦n⟧)) ≅
          (H m).obj (DerivedCategory.Q.obj E) :=
      (H i).mapIso ((DerivedCategory.Q.commShiftIso n).app E) ≪≫
        ((H 0).shiftIso n i m hni).app (DerivedCategory.Q.obj E)
    let eTarget : (H i).obj (K⟦n⟧) ≅ (H m).obj K :=
      ((H 0).shiftIso n i m hni).app K
    have hshiftNat :
        (H i).map (α⟦n⟧') ≫ eTarget.hom =
          (((H 0).shiftIso n i m hni).app (DerivedCategory.Q.obj E)).hom ≫
            (H m).map α := by
      -- At the boundary degree, the same naturality square transports the surjectivity claim.
      exact (H 0).shiftIso_hom_naturality n i m hni α
    have hcomm :
        (H i).map αn ≫ eTarget.hom = eSource.hom ≫ (H m).map α := by
      -- The shifted witness map is the `Q.commShiftIso` comparison followed by `α⟦n⟧'`.
      have hmid :
          (H i).map αn ≫ eTarget.hom =
            (H i).map ((DerivedCategory.Q.commShiftIso n).app E).hom ≫
              (((H 0).shiftIso n i m hni).app (DerivedCategory.Q.obj E)).hom ≫
                (H m).map α := by
        calc
          (H i).map αn ≫ eTarget.hom =
              (H i).map ((DerivedCategory.Q.commShiftIso n).app E).hom ≫
                ((H i).map (α⟦n⟧') ≫ eTarget.hom) := by
                  simp [αn, Functor.map_comp, Category.assoc]
          _ = (H i).map ((DerivedCategory.Q.commShiftIso n).app E).hom ≫
                (((H 0).shiftIso n i m hni).app (DerivedCategory.Q.obj E)).hom ≫
                  (H m).map α := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun k ↦ (H i).map ((DerivedCategory.Q.commShiftIso n).app E).hom ≫ k)
                        hshiftNat
      simpa [eSource, Category.assoc] using hmid
    haveI : IsIso eSource.hom := by infer_instance
    have hcompEpi : Epi ((H i).map αn ≫ eTarget.hom) := by
      rw [hcomm]
      infer_instance
    exact epi_of_epi_comp_iso ((H i).map αn) eTarget

/-- Shifting an object of `D(R)` by `n` translates the `m`-pseudo-coherence bound by the same
amount. -/
theorem isMPseudoCoherent_shift_iff (K : DMod) (n m : ℤ) :
    (K⟦n⟧).IsMPseudoCoherent (m - n) ↔ K.IsMPseudoCoherent m := by
  constructor
  · intro hshift
    have hback : (K⟦n⟧⟦-n⟧).IsMPseudoCoherent m := by
      -- Shift back by `-n`; the index arithmetic simplifies to the original bound `m`.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        isMPseudoCoherent_shift (K⟦n⟧) (-n) (m - n) hshift
    -- The shift equivalence identifies `K⟦n⟧⟦-n⟧` with `K`.
    exact isMPseudoCoherent_of_iso (shiftShiftNeg K n) m hback
  · intro hK
    -- The reverse implication is exactly the shift-transport statement above.
    exact isMPseudoCoherent_shift K n m hK

instance isMPseudoCoherent_isClosedUnderIsomorphisms (m : ℤ) :
    IsClosedUnderIsomorphisms (fun K : DMod ↦ K.IsMPseudoCoherent m) where
  of_iso e hK := by
    -- Reuse the explicit isomorphism-transport lemma proved above.
    exact isMPseudoCoherent_of_iso e m hK

/-- Helper for Lemma 15.65.2: the degree-`i` derived homology map of `Q.map β` is the cochain
homology map of `β`, conjugated by the standard comparison isomorphisms
`homologyFunctorFactors.app`. -/
private theorem homologyFunctor_map_Q_eq_conjugate_homologyMap
    {E L : Cpx} (β : E ⟶ L) (i : ℤ) :
    (H i).map (DerivedCategory.Q.map β) =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E).hom ≫
        HomologicalComplex.homologyMap β i ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L).inv := by
  let eE := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E
  let eL := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L
  have hnat :
      (H i).map (DerivedCategory.Q.map β) ≫ eL.hom =
        eE.hom ≫ HomologicalComplex.homologyMap β i := by
    -- Naturality is exactly the comparison between derived and cochain homology maps.
    simpa using
      (DerivedCategory.homologyFunctorFactors_hom_naturality (C := ModuleCat R) β i)
  have hpost :
      ((H i).map (DerivedCategory.Q.map β) ≫ eL.hom) ≫ eL.inv =
        eE.hom ≫ HomologicalComplex.homologyMap β i ≫ eL.inv := by
    -- Postcompose the naturality square by the inverse comparison isomorphism.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eL.inv) hnat
  -- The left-hand composite collapses because `eL.hom ≫ eL.inv = 𝟙`.
  simpa [Category.assoc] using hpost

/-- Helper for Lemma 15.65.2: conversely, the cochain-level homology map is the derived homology
map of `Q.map β`, conjugated by the inverse comparison isomorphisms. -/
private theorem homologyMap_eq_conjugate_homologyFunctor_map_Q
    {E L : Cpx} (β : E ⟶ L) (i : ℤ) :
    HomologicalComplex.homologyMap β i =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E).inv ≫
        (H i).map (DerivedCategory.Q.map β) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L).hom := by
  let eE := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E
  let eL := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L
  have hnat :
      (H i).map (DerivedCategory.Q.map β) ≫ eL.hom =
        eE.hom ≫ HomologicalComplex.homologyMap β i := by
    -- The same naturality square can be solved for the cochain-level map.
    simpa using
      (DerivedCategory.homologyFunctorFactors_hom_naturality (C := ModuleCat R) β i)
  have hpre :
      eE.inv ≫ (eE.hom ≫ HomologicalComplex.homologyMap β i) =
        eE.inv ≫ ((H i).map (DerivedCategory.Q.map β) ≫ eL.hom) := by
    -- Precompose the naturality square by the inverse source comparison.
    simpa [Category.assoc] using congrArg (fun k ↦ eE.inv ≫ k) hnat.symm
  -- The left-hand composite collapses because `eE.inv ≫ eE.hom = 𝟙`.
  simpa [Category.assoc] using hpre

/-- Helper for Lemma 15.65.2: the cochain-level homology map of `β` is an isomorphism exactly
when the degree-`i` derived homology map of `Q.map β` is. -/
theorem homologyMap_isIso_iff_homologyFunctor_map_Q_isIso
    {E L : Cpx} (β : E ⟶ L) (i : ℤ) :
    IsIso (HomologicalComplex.homologyMap β i) ↔
      IsIso ((H i).map (DerivedCategory.Q.map β)) := by
  constructor
  · intro hβ
    letI : IsIso (HomologicalComplex.homologyMap β i) := hβ
    let eE := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E
    let eL := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L
    -- Rewrite the derived map as an isomorphic conjugate of the cochain homology map.
    rw [homologyFunctor_map_Q_eq_conjugate_homologyMap (R := R) β i]
    have hmid : IsIso (eE.hom ≫ HomologicalComplex.homologyMap β i) := by
      exact (isIso_comp_left_iff eE.hom (HomologicalComplex.homologyMap β i)).2 hβ
    exact (isIso_comp_right_iff (eE.hom ≫ HomologicalComplex.homologyMap β i) eL.inv).2 hmid
  · intro hβ
    letI : IsIso ((H i).map (DerivedCategory.Q.map β)) := hβ
    let eE := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E
    let eL := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L
    -- Rewrite back in the opposite direction to transport invertibility to the cochain model.
    rw [homologyMap_eq_conjugate_homologyFunctor_map_Q (R := R) β i]
    have hmid : IsIso (eE.inv ≫ (H i).map (DerivedCategory.Q.map β)) := by
      exact (isIso_comp_left_iff eE.inv ((H i).map (DerivedCategory.Q.map β))).2 hβ
    exact (isIso_comp_right_iff (eE.inv ≫ (H i).map (DerivedCategory.Q.map β)) eL.hom).2 hmid

/-- Helper for Lemma 15.65.2: the cochain-level homology map of `β` is epi exactly when the
degree-`i` derived homology map of `Q.map β` is epi. -/
theorem homologyMap_epi_iff_homologyFunctor_map_Q_epi
    {E L : Cpx} (β : E ⟶ L) (i : ℤ) :
    Epi (HomologicalComplex.homologyMap β i) ↔
      Epi ((H i).map (DerivedCategory.Q.map β)) := by
  constructor
  · intro hβ
    let eE := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E
    let eL := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L
    -- Rewrite the derived map as the cochain homology map conjugated by comparison isomorphisms.
    rw [homologyFunctor_map_Q_eq_conjugate_homologyMap (R := R) β i]
    rw [CategoryTheory.epi_iff_forall_injective]
    intro W u v huv
    have htmp :
        eE.hom ≫ (HomologicalComplex.homologyMap β i ≫ (eL.inv ≫ u)) =
          eE.hom ≫ (HomologicalComplex.homologyMap β i ≫ (eL.inv ≫ v)) := by
      exact huv
    have hcomp :
        HomologicalComplex.homologyMap β i ≫ (eL.inv ≫ u) =
          HomologicalComplex.homologyMap β i ≫ (eL.inv ≫ v) :=
      (cancel_epi eE.hom).1 htmp
    have heq :
        eL.inv ≫ u = eL.inv ≫ v :=
      (CategoryTheory.epi_iff_forall_injective (HomologicalComplex.homologyMap β i)).1 hβ W hcomp
    exact (cancel_epi eL.inv).1 heq
  · intro hβ
    let eE := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E
    let eL := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L
    -- Rewrite back to the cochain model; epimorphy is preserved under composition by isomorphisms.
    rw [homologyMap_eq_conjugate_homologyFunctor_map_Q (R := R) β i]
    rw [CategoryTheory.epi_iff_forall_injective]
    intro W u v huv
    have htmp :
        eE.inv ≫ (((H i).map (DerivedCategory.Q.map β)) ≫ (eL.hom ≫ u)) =
          eE.inv ≫ (((H i).map (DerivedCategory.Q.map β)) ≫ (eL.hom ≫ v)) := by
      exact huv
    have hcomp :
        (H i).map (DerivedCategory.Q.map β) ≫ (eL.hom ≫ u) =
          (H i).map (DerivedCategory.Q.map β) ≫ (eL.hom ≫ v) :=
      (cancel_epi eE.inv).1 htmp
    have heq :
        eL.hom ≫ u = eL.hom ≫ v :=
      (CategoryTheory.epi_iff_forall_injective
        ((H i).map (DerivedCategory.Q.map β))).1 hβ W hcomp
    exact (cancel_epi eL.hom).1 heq

/-- Helper for Lemma 15.65.2: transporting a distinguished triangle along the canonical
`Q.objPreimage` isomorphisms on the first two vertices keeps it distinguished. -/
private theorem transported_objPreimage_triangle_distinguished
    (T : Triangle DMod) (hT : T ∈ distTriang DMod) :
    Triangle.mk
        ((DerivedCategory.Q.objObjPreimageIso T.obj₁).hom ≫ T.mor₁ ≫
          (DerivedCategory.Q.objObjPreimageIso T.obj₂).inv)
        ((DerivedCategory.Q.objObjPreimageIso T.obj₂).hom ≫ T.mor₂)
        (T.mor₃ ≫ (DerivedCategory.Q.objObjPreimageIso T.obj₁).inv⟦(1 : ℤ)⟧') ∈
      distTriang DMod := by
  -- Transport the first two vertices to the chosen `Q.objPreimage` models and keep the third
  -- vertex fixed; distinguishedness is invariant under triangle isomorphism.
  refine isomorphic_distinguished _ hT _ ?_
  refine Triangle.isoMk _ _
    (DerivedCategory.Q.objObjPreimageIso T.obj₁)
    (DerivedCategory.Q.objObjPreimageIso T.obj₂)
    (Iso.refl _) ?_ ?_ ?_
  · simp [Category.assoc]
  · simp
  · simp [Category.assoc]

/-- Helper for Lemma 15.65.2: a derived composite out of a bounded-above projective source can be
represented by a literal cochain map. -/
private theorem exists_projective_minus_representative_of_composite
    (P : CochainComplex.ProjectiveMinus (ModuleCat R))
    {K L : Cpx} (ξ : (P : Cpx) ⟶ K)
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ β : (P : Cpx) ⟶ L, DerivedCategory.Q.map β = DerivedCategory.Q.map ξ ≫ α := by
  let Ho := HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
  let eP := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app (P : Cpx)
  let eL := (DerivedCategory.quotientCompQhIso (ModuleCat R)).app L
  let δ : DerivedCategory.Qh.obj (Ho.obj P) ⟶ DerivedCategory.Qh.obj (Ho.obj L) :=
    eP.hom ≫ DerivedCategory.Q.map ξ ≫ α ≫ eL.inv
  obtain ⟨βh, hβh⟩ :=
    (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective P L).surjective
      δ
  obtain ⟨β, hβ⟩ := Ho.map_surjective βh
  refine ⟨β, ?_⟩
  have hQh :
      DerivedCategory.Qh.map (Ho.map β) = δ := by
    simpa [hβ] using hβh
  -- Conjugate the `Qh`-identity back along `quotientCompQhIso` to recover the desired `Q`-map.
  calc
    DerivedCategory.Q.map β =
      (Iso.homCongr eP eL) (DerivedCategory.Qh.map (Ho.map β)) := by
        simpa using (quotientCompQhIso_homCongr_map (R := R) β).symm
    _ = (Iso.homCongr eP eL) δ := by simpa [hQh]
    _ = DerivedCategory.Q.map ξ ≫ α := by
      change eP.inv ≫ (eP.hom ≫ DerivedCategory.Q.map ξ ≫ α ≫ eL.inv) ≫ eL.hom =
        DerivedCategory.Q.map ξ ≫ α
      simp [Category.assoc]

/-- Helper for Lemma 15.65.2: once the first two vertices are transported to `Q.objPreimage`
models, a cochain representative of the first morphism extends to a morphism from its mapping-cone
triangle to the transported distinguished triangle. -/
private theorem exists_mappingCone_comparison_to_transported_triangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    {P : Cpx}
    (ξ : P ⟶ DerivedCategory.Q.objPreimage T.obj₁)
    (β : P ⟶ DerivedCategory.Q.objPreimage T.obj₂)
    (hβ :
      DerivedCategory.Q.map β =
        DerivedCategory.Q.map ξ ≫
          ((DerivedCategory.Q.objObjPreimageIso T.obj₁).hom ≫ T.mor₁ ≫
            (DerivedCategory.Q.objObjPreimageIso T.obj₂).inv)) :
    ∃ φ :
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β) ⟶
        Triangle.mk
          ((DerivedCategory.Q.objObjPreimageIso T.obj₁).hom ≫ T.mor₁ ≫
            (DerivedCategory.Q.objObjPreimageIso T.obj₂).inv)
          ((DerivedCategory.Q.objObjPreimageIso T.obj₂).hom ≫ T.mor₂)
          (T.mor₃ ≫ (DerivedCategory.Q.objObjPreimageIso T.obj₁).inv⟦(1 : ℤ)⟧'),
      φ.hom₁ = DerivedCategory.Q.map ξ ∧ φ.hom₂ = 𝟙 _ := by
  let T' : Triangle DMod :=
    Triangle.mk
      ((DerivedCategory.Q.objObjPreimageIso T.obj₁).hom ≫ T.mor₁ ≫
        (DerivedCategory.Q.objObjPreimageIso T.obj₂).inv)
      ((DerivedCategory.Q.objObjPreimageIso T.obj₂).hom ≫ T.mor₂)
      (T.mor₃ ≫ (DerivedCategory.Q.objObjPreimageIso T.obj₁).inv⟦(1 : ℤ)⟧')
  have hT' : T' ∈ distTriang DMod := by
    -- This is precisely the transported triangle from the previous helper.
    simpa [T'] using transported_objPreimage_triangle_distinguished (R := R) T hT
  have hCone :
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β) ∈ distTriang DMod := by
    -- Mapping-cone triangles are distinguished in the derived category.
    simpa using DerivedCategory.mappingCone_triangle_distinguished β
  obtain ⟨c, hc₂, hc₃⟩ :=
    complete_distinguished_triangle_morphism
      (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle β))
      T'
      hCone hT'
      (DerivedCategory.Q.map ξ) (𝟙 _)
      (by simpa [T'] using hβ)
  -- Package the TR3 completion as an explicit triangle morphism so the main theorem can reuse it.
  refine ⟨
    { hom₁ := DerivedCategory.Q.map ξ
      hom₂ := 𝟙 _
      hom₃ := c
      comm₁ := by simpa [T'] using hβ
      comm₂ := hc₂
      comm₃ := hc₃ },
    rfl, rfl⟩

/-- Helper for Lemma 15.65.2: if `c ≤ i`, then the retained degree `i` lies in the image of the
embedding `n ↦ c + n`. -/
private theorem embeddingUpIntGE_toNat_sub_eq
    (c i : ℤ) (hci : c ≤ i) :
    (ComplexShape.embeddingUpIntGE c).f (Int.toNat (i - c)) = i := by
  -- The difference `i - c` is nonnegative exactly on the retained side of the truncation.
  dsimp [ComplexShape.embeddingUpIntGE]
  rw [Int.toNat_of_nonneg]
  · omega
  · omega

/-- Helper for Lemma 15.65.2: in a retained degree, the lower brutal truncation term is
canonically the original term. -/
private noncomputable def lower_stupid_truncation_x_iso
    (E : Cpx) (c i : ℤ) (hci : c ≤ i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i ≅ E.X i :=
  E.stupidTruncXIso (ComplexShape.embeddingUpIntGE c)
    (embeddingUpIntGE_toNat_sub_eq c i hci)

/-- Helper for Lemma 15.65.2: the chosen proof `c ≤ i` does not affect the degreewise
lower-truncation identification morphism. -/
private theorem lower_stupid_truncation_x_iso_hom_eq
    (E : Cpx) (c i : ℤ) {h h' : c ≤ i} :
    (lower_stupid_truncation_x_iso E c i h).hom =
      (lower_stupid_truncation_x_iso E c i h').hom := by
  cases Subsingleton.elim h h'
  rfl

/-- Helper for Lemma 15.65.2: after transporting along the retained-degree identifications, the
differential of the lower brutal truncation is the original differential. -/
private theorem lower_stupid_truncation_d_via_x_iso
    (E : Cpx) (c : ℤ) {i j : ℤ}
    (hci : c ≤ i) (hcj : c ≤ j) :
    (lower_stupid_truncation_x_iso E c i hci).inv ≫
      (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
      (lower_stupid_truncation_x_iso E c j hcj).hom =
        E.d i j := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
    ComplexShape.embeddingUpIntGE c
  let i₀ : ℕ := Int.toNat (i - c)
  let j₀ : ℕ := Int.toNat (j - c)
  have hi₀ : e.f i₀ = i := embeddingUpIntGE_toNat_sub_eq c i hci
  have hj₀ : e.f j₀ = j := embeddingUpIntGE_toNat_sub_eq c j hcj
  -- First peel off the `extend` differential, then the `restriction` differential.
  change (lower_stupid_truncation_x_iso E c i hci).inv ≫
      ((E.restriction e).extend e).d i j ≫
      (lower_stupid_truncation_x_iso E c j hcj).hom =
        E.d i j
  rw [HomologicalComplex.extend_d_eq (K := E.restriction e) (e := e) hi₀ hj₀]
  rw [HomologicalComplex.restriction_d_eq (K := E) (e := e) hi₀ hj₀]
  simp [lower_stupid_truncation_x_iso, HomologicalComplex.stupidTrunc,
    HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso,
    e, i₀, j₀]

/-- Helper for Lemma 15.65.2: the component maps of the canonical lower-truncation inclusion. -/
private noncomputable def lower_stupid_truncation_inclusion_f
    (E : Cpx) (c i : ℤ) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i ⟶ E.X i :=
  if hci : c ≤ i then
    (lower_stupid_truncation_x_iso E c i hci).hom
  else
    0

/-- Helper for Lemma 15.65.2: in retained degrees, the canonical lower-truncation inclusion is the
transported identity map. -/
private theorem lower_stupid_truncation_inclusion_f_of_ge
    (E : Cpx) (c : ℤ) {i : ℤ} (hci : c ≤ i) :
    lower_stupid_truncation_inclusion_f E c i =
      (lower_stupid_truncation_x_iso E c i hci).hom := by
  -- Unfold the inclusion component and keep only the retained-degree branch.
  simp [lower_stupid_truncation_inclusion_f, hci]

/-- Helper for Lemma 15.65.2: in retained degrees, the canonical lower-truncation inclusion is an
isomorphism on components. -/
private theorem lower_stupid_truncation_inclusion_f_isIso_of_ge
    (E : Cpx) (c : ℤ) {i : ℤ} (hci : c ≤ i) :
    IsIso (lower_stupid_truncation_inclusion_f E c i) := by
  -- The retained component is literally one of the chosen degreewise identifications.
  rw [lower_stupid_truncation_inclusion_f_of_ge E c hci]
  infer_instance

/-- Helper for Lemma 15.65.2: the canonical componentwise map from the lower brutal truncation to
the original complex is a chain map. -/
private theorem lower_stupid_truncation_inclusion_comm
    (E : Cpx) (c : ℤ) :
    ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      lower_stupid_truncation_inclusion_f E c i ≫ E.d i j =
        (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
          lower_stupid_truncation_inclusion_f E c j := by
  intro i j hij
  by_cases hci : c ≤ i
  · have hcj : c ≤ j := by
      have hij' : j = i + 1 := by
        simpa [ComplexShape.up, eq_comm] using hij
      omega
    -- On retained degrees, the inclusion is the identity after transporting through the
    -- canonical truncation term identifications.
    rw [lower_stupid_truncation_inclusion_f_of_ge E c hci,
      lower_stupid_truncation_inclusion_f_of_ge E c hcj]
    calc
      (lower_stupid_truncation_x_iso E c i hci).hom ≫ E.d i j =
          (lower_stupid_truncation_x_iso E c i hci).hom ≫
            ((lower_stupid_truncation_x_iso E c i hci).inv ≫
              (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
                (lower_stupid_truncation_x_iso E c j hcj).hom) := by
              rw [lower_stupid_truncation_d_via_x_iso E c hci hcj]
      _ = (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j ≫
            (lower_stupid_truncation_x_iso E c j hcj).hom := by
              simp [Category.assoc]
  · have hzero :
        Limits.IsZero ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i) := by
      -- Below the cutoff, the source term of the truncation is zero.
      exact E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i
        (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hci)
    by_cases hcj : c ≤ j
    · -- Even when the target degree is retained, the source side already vanished.
      have hsrczero :
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j = 0 :=
        hzero.eq_of_src ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i j) 0
      simp [lower_stupid_truncation_inclusion_f, hci, hcj, hsrczero]
    · -- If both degrees are discarded, both components of the square are zero.
      simp [lower_stupid_truncation_inclusion_f, hci, hcj]

/-- Helper for Lemma 15.65.2: the lower brutal truncation has a canonical inclusion into the
original complex. -/
private noncomputable def lower_stupid_truncation_inclusion
    (E : Cpx) (c : ℤ) :
    E.stupidTrunc (ComplexShape.embeddingUpIntGE c) ⟶ E :=
  { f := fun i ↦ lower_stupid_truncation_inclusion_f E c i
    comm' := lower_stupid_truncation_inclusion_comm E c }

/-- Helper for Lemma 15.65.2: above the cutoff, the left differential of the lower brutal
truncation short complex agrees with the original differential after transport. -/
private theorem lower_stupid_truncation_sc_left_comm_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d (i - 1) i ≫
        (lower_stupid_truncation_x_iso E c i (by omega)).hom =
      (lower_stupid_truncation_x_iso E c (i - 1) (by omega)).hom ≫ E.d (i - 1) i := by
  have hi_prev : c ≤ i - 1 := by omega
  have hi_mid : c ≤ i := by omega
  -- Transport the left differential through the retained-degree identifications.
  calc
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d (i - 1) i ≫
        (lower_stupid_truncation_x_iso E c i hi_mid).hom =
      (lower_stupid_truncation_x_iso E c (i - 1) hi_prev).hom ≫
        ((lower_stupid_truncation_x_iso E c (i - 1) hi_prev).inv ≫
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d (i - 1) i ≫
            (lower_stupid_truncation_x_iso E c i hi_mid).hom) := by
              simp [Category.assoc]
    _ = (lower_stupid_truncation_x_iso E c (i - 1) hi_prev).hom ≫ E.d (i - 1) i := by
          rw [lower_stupid_truncation_d_via_x_iso E c hi_prev hi_mid]

/-- Helper for Lemma 15.65.2: above the cutoff, the right differential of the lower brutal
truncation short complex agrees with the original differential after transport. -/
private theorem lower_stupid_truncation_sc_right_comm_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i (i + 1) ≫
        (lower_stupid_truncation_x_iso E c (i + 1) (by omega)).hom =
      (lower_stupid_truncation_x_iso E c i (by omega)).hom ≫ E.d i (i + 1) := by
  have hi_mid : c ≤ i := by omega
  have hi_next : c ≤ i + 1 := by omega
  -- Transport the right differential through the retained-degree identifications.
  calc
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i (i + 1) ≫
        (lower_stupid_truncation_x_iso E c (i + 1) hi_next).hom =
      (lower_stupid_truncation_x_iso E c i hi_mid).hom ≫
        ((lower_stupid_truncation_x_iso E c i hi_mid).inv ≫
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i (i + 1) ≫
            (lower_stupid_truncation_x_iso E c (i + 1) hi_next).hom) := by
              simp [Category.assoc]
    _ = (lower_stupid_truncation_x_iso E c i hi_mid).hom ≫ E.d i (i + 1) := by
          rw [lower_stupid_truncation_d_via_x_iso E c hi_mid hi_next]

/-- Helper for Lemma 15.65.2: the predecessor in the cochain shape is `i - 1`. -/
private theorem cochain_prev_eq (i : ℤ) :
    (ComplexShape.up ℤ).prev i = i - 1 :=
  ComplexShape.prev_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.65.2: above the cutoff, the first object of the lower brutal truncation
short complex identifies with the original first object. -/
private noncomputable def lower_stupid_truncation_sc_X₁_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).X₁ ≅ (E.sc i).X₁ :=
  lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i)
    (by
      have hi_prev : c ≤ i - 1 := by omega
      simpa [cochain_prev_eq i] using hi_prev)

/-- Helper for Lemma 15.65.2: the first component of the lower-truncation short-complex
identification is the retained-degree isomorphism at `prev i`. -/
private theorem lower_stupid_truncation_sc_X₁_hom_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (lower_stupid_truncation_sc_X₁_iso_of_gt E c i hci).hom =
      (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i)
        (by
          have hi_prev : c ≤ i - 1 := by omega
          simpa [cochain_prev_eq i] using hi_prev)).hom := by
  rfl

/-- Helper for Lemma 15.65.2: above the cutoff, the middle object of the lower brutal truncation
short complex identifies with the original middle object. -/
private noncomputable def lower_stupid_truncation_sc_X₂_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).X₂ ≅ (E.sc i).X₂ := by
  simpa [HomologicalComplex.sc] using
    (lower_stupid_truncation_x_iso E c i (by omega))

/-- Helper for Lemma 15.65.2: the middle component of the lower-truncation short-complex
identification is the retained-degree isomorphism at `i`. -/
private theorem lower_stupid_truncation_sc_X₂_hom_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom =
      (lower_stupid_truncation_x_iso E c i (by omega)).hom := by
  rfl

/-- Helper for Lemma 15.65.2: the central degree identification in the lower-truncation short
complex cancels with its inverse. -/
private theorem lower_stupid_truncation_sc_X₂_inv_hom_id_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).inv ≫
      (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom = 𝟙 _ := by
  -- This is the standard inverse-hom cancellation for the middle degree isomorphism.
  simp

/-- Helper for Lemma 15.65.2: the successor in the cochain shape is `i + 1`. -/
private theorem cochain_next_eq (i : ℤ) :
    (ComplexShape.up ℤ).next i = i + 1 :=
  ComplexShape.next_eq' (ComplexShape.up ℤ) (by simp [ComplexShape.up, ComplexShape.up'])

/-- Helper for Lemma 15.65.2: above the cutoff, the third object of the lower brutal truncation
short complex identifies with the original third object. -/
private noncomputable def lower_stupid_truncation_sc_X₃_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).X₃ ≅ (E.sc i).X₃ :=
  lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i)
    (by
      have hi_next : c ≤ i + 1 := by omega
      simpa [cochain_next_eq i] using hi_next)

/-- Helper for Lemma 15.65.2: the third component of the lower-truncation short-complex
identification is the retained-degree isomorphism at `next i`. -/
private theorem lower_stupid_truncation_sc_X₃_hom_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (lower_stupid_truncation_sc_X₃_iso_of_gt E c i hci).hom =
      (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i)
        (by
          have hi_next : c ≤ i + 1 := by omega
          simpa [cochain_next_eq i] using hi_next)).hom := by
  rfl

/-- Helper for Lemma 15.65.2: above the cutoff, the first square of the short-complex
identification commutes. -/
private theorem lower_stupid_truncation_sc_left_comm_prev_language_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d ((ComplexShape.up ℤ).prev i) i ≫
        (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom =
      (lower_stupid_truncation_sc_X₁_iso_of_gt E c i hci).hom ≫
        E.d ((ComplexShape.up ℤ).prev i) i := by
  -- Read the already proved arithmetic identity in the exact `prev` language used by `sc`.
  rw [lower_stupid_truncation_sc_X₁_hom_of_gt, lower_stupid_truncation_sc_X₂_hom_of_gt]
  have hi_prev : c ≤ (ComplexShape.up ℤ).prev i := by
    rw [cochain_prev_eq i]
    omega
  have hi_mid : c ≤ i := by
    omega
  have hX₁ :
      (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i)
        (by
          have hi_prev' : c ≤ i - 1 := by omega
          simpa [cochain_prev_eq i] using hi_prev')).hom =
        (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).hom :=
    lower_stupid_truncation_x_iso_hom_eq E c ((ComplexShape.up ℤ).prev i)
  have hX₂ :
      (lower_stupid_truncation_x_iso E c i (by omega)).hom =
        (lower_stupid_truncation_x_iso E c i hi_mid).hom :=
    lower_stupid_truncation_x_iso_hom_eq E c i
  rw [hX₁, hX₂]
  calc
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d ((ComplexShape.up ℤ).prev i) i ≫
        (lower_stupid_truncation_x_iso E c i hi_mid).hom =
      (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).hom ≫
        ((lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).inv ≫
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d ((ComplexShape.up ℤ).prev i) i ≫
            (lower_stupid_truncation_x_iso E c i hi_mid).hom) := by
              simp
    _ = (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).prev i) hi_prev).hom ≫
          E.d ((ComplexShape.up ℤ).prev i) i := by
            rw [lower_stupid_truncation_d_via_x_iso E c hi_prev hi_mid]

/-- Helper for Lemma 15.65.2: above the cutoff, the second square of the short-complex
identification can be read directly in `next` language. -/
private theorem lower_stupid_truncation_sc_right_comm_next_language_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i ((ComplexShape.up ℤ).next i) ≫
        (lower_stupid_truncation_sc_X₃_iso_of_gt E c i hci).hom =
      (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom ≫
        E.d i ((ComplexShape.up ℤ).next i) := by
  -- Read the arithmetic identity in the exact `next` language used by `sc`.
  rw [lower_stupid_truncation_sc_X₂_hom_of_gt, lower_stupid_truncation_sc_X₃_hom_of_gt]
  have hi_mid : c ≤ i := by
    omega
  have hi_next : c ≤ (ComplexShape.up ℤ).next i := by
    rw [cochain_next_eq i]
    omega
  have hX₂ :
      (lower_stupid_truncation_x_iso E c i (by omega)).hom =
        (lower_stupid_truncation_x_iso E c i hi_mid).hom :=
    lower_stupid_truncation_x_iso_hom_eq E c i
  have hX₃ :
      (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i)
        (by
          have hi_next' : c ≤ i + 1 := by omega
          simpa [cochain_next_eq i] using hi_next')).hom =
        (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i) hi_next).hom :=
    lower_stupid_truncation_x_iso_hom_eq E c ((ComplexShape.up ℤ).next i)
  rw [hX₂, hX₃]
  calc
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i ((ComplexShape.up ℤ).next i) ≫
        (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i) hi_next).hom =
      (lower_stupid_truncation_x_iso E c i hi_mid).hom ≫
        ((lower_stupid_truncation_x_iso E c i hi_mid).inv ≫
          (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).d i ((ComplexShape.up ℤ).next i) ≫
            (lower_stupid_truncation_x_iso E c ((ComplexShape.up ℤ).next i) hi_next).hom) := by
              simp
    _ = (lower_stupid_truncation_x_iso E c i hi_mid).hom ≫
          E.d i ((ComplexShape.up ℤ).next i) := by
            rw [lower_stupid_truncation_d_via_x_iso E c hi_mid hi_next]

/-- Helper for Lemma 15.65.2: above the cutoff, the first square of the short-complex
identification commutes. -/
private theorem lower_stupid_truncation_sc_f_comm_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (lower_stupid_truncation_sc_X₁_iso_of_gt E c i hci).hom ≫ (E.sc i).f =
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).f ≫
        (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom := by
  -- Once the `prev`-language transport lemma is isolated, the `sc` square is just one unfolding.
  simpa only [HomologicalComplex.sc, lower_stupid_truncation_sc_X₁_hom_of_gt,
    lower_stupid_truncation_sc_X₂_hom_of_gt] using
    (lower_stupid_truncation_sc_left_comm_prev_language_of_gt E c i hci).symm

/-- Helper for Lemma 15.65.2: above the cutoff, the second square of the short-complex
identification commutes. -/
private theorem lower_stupid_truncation_sc_g_comm_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci).hom ≫ (E.sc i).g =
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i).g ≫
        (lower_stupid_truncation_sc_X₃_iso_of_gt E c i hci).hom := by
  -- The right square reduces in the same way once the `next`-language transport is isolated.
  simpa only [HomologicalComplex.sc, lower_stupid_truncation_sc_X₂_hom_of_gt,
    lower_stupid_truncation_sc_X₃_hom_of_gt] using
    (lower_stupid_truncation_sc_right_comm_next_language_of_gt E c i hci).symm

/-- Helper for Lemma 15.65.2: above the cutoff, the degree-`i` short complex of the lower brutal
truncation is canonically the same short complex as the degree-`i` short complex of `E`. -/
private noncomputable def lower_stupid_truncation_sc_iso_of_gt
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i ≅ E.sc i :=
  ShortComplex.isoMk
    (lower_stupid_truncation_sc_X₁_iso_of_gt E c i hci)
    (lower_stupid_truncation_sc_X₂_iso_of_gt E c i hci)
    (lower_stupid_truncation_sc_X₃_iso_of_gt E c i hci)
    (lower_stupid_truncation_sc_f_comm_of_gt E c i hci)
    (lower_stupid_truncation_sc_g_comm_of_gt E c i hci)

/-- Helper for Lemma 15.65.2: above the cutoff, the canonical inclusion from the lower brutal
truncation induces an isomorphism on homology. -/
private theorem homologyMap_lower_stupid_truncation_inclusion_isIso_above
    (E : Cpx) (c i : ℤ) (hci : c < i) :
    IsIso (HomologicalComplex.homologyMap (lower_stupid_truncation_inclusion E c) i) := by
  let φ :
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc i) ⟶ E.sc i :=
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) i).map
      (lower_stupid_truncation_inclusion E c))
  have hi_prev : c ≤ i - 1 := by omega
  have hi_mid : c ≤ i := by omega
  have hi_next : c ≤ i + 1 := by omega
  have hφ : φ = (lower_stupid_truncation_sc_iso_of_gt E c i hci).hom := by
    -- All three components of the mapped short-complex morphism are the retained-degree
    -- inclusion maps, so the whole morphism is the canonical short-complex isomorphism.
    ext
    · simp [φ, lower_stupid_truncation_sc_iso_of_gt, lower_stupid_truncation_sc_X₁_iso_of_gt,
        HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
        lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge,
        hi_prev]
    · simp [φ, lower_stupid_truncation_sc_iso_of_gt, lower_stupid_truncation_sc_X₂_iso_of_gt,
        HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
        lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge,
        hi_mid]
    · simp [φ, lower_stupid_truncation_sc_iso_of_gt, lower_stupid_truncation_sc_X₃_iso_of_gt,
        HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
        lower_stupid_truncation_inclusion, lower_stupid_truncation_inclusion_f_of_ge,
        hi_next]
  -- Identify the induced short-complex map with the hom of the canonical degree-`i`
  -- short-complex isomorphism, then transport invertibility to homology.
  change IsIso (CategoryTheory.ShortComplex.homologyMap φ)
  rw [hφ]
  exact
    (show IsIso
      (CategoryTheory.ShortComplex.homologyMap
        (lower_stupid_truncation_sc_iso_of_gt E c i hci).hom) by
          infer_instance)

/-- Helper for Lemma 15.65.2: at the cutoff degree, the canonical inclusion from the lower brutal
truncation induces an epimorphism on cycles. -/
private theorem lower_stupid_truncation_cyclesMap_epi_at_cutoff
    (E : Cpx) (c : ℤ) :
    Epi (HomologicalComplex.cyclesMap (lower_stupid_truncation_inclusion E c) c) := by
  -- At degree `c`, the cycles object only sees the degree-`c` and degree-`c + 1` terms, and the
  -- lower truncation inclusion is already an isomorphism on both retained components.
  change Epi
    (ShortComplex.cyclesMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
        (lower_stupid_truncation_inclusion E c)))
  let φ :
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).sc c) ⟶ E.sc c :=
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
      (lower_stupid_truncation_inclusion E c))
  have hτ₂ : IsIso φ.τ₂ := by
    -- The middle component is the retained degree-`c` inclusion.
    simpa [φ, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor', lower_stupid_truncation_inclusion,
      lower_stupid_truncation_inclusion_f_of_ge] using
      (lower_stupid_truncation_inclusion_f_isIso_of_ge E c (show c ≤ c by simp))
  have hτ₃ : IsIso φ.τ₃ := by
    -- The right component is the retained degree-`c + 1` inclusion.
    have hnext : (ComplexShape.up ℤ).next c = c + 1 := by
      simpa using
        (ComplexShape.next_eq' (ComplexShape.up ℤ)
          (ComplexShape.up_mk c (c + 1) rfl))
    have hcnext : c ≤ (ComplexShape.up ℤ).next c := by
      rw [hnext]
      omega
    simpa [φ, HomologicalComplex.sc, HomologicalComplex.shortComplexFunctor,
      HomologicalComplex.shortComplexFunctor', lower_stupid_truncation_inclusion,
      lower_stupid_truncation_inclusion_f_of_ge, ComplexShape.up] using
      (lower_stupid_truncation_inclusion_f_isIso_of_ge E c hcnext)
  letI : IsIso φ.τ₂ := hτ₂
  letI : IsIso φ.τ₃ := hτ₃
  letI : Mono φ.τ₃ := by infer_instance
  letI : IsIso (ShortComplex.cyclesMap φ) := by infer_instance
  infer_instance

/-- Helper for Lemma 15.65.2: at the cutoff degree, the canonical inclusion from the lower brutal
truncation induces an epimorphism on homology. -/
private theorem homologyMap_lower_stupid_truncation_inclusion_epi_at_cutoff
    (E : Cpx) (c : ℤ) :
    Epi (HomologicalComplex.homologyMap (lower_stupid_truncation_inclusion E c) c) := by
  -- Reduce to the short-complex homology map and descend the cutoff cycles epimorphism through
  -- the standard short-complex homology quotient.
  simpa [HomologicalComplex.homologyMap, HomologicalComplex.cyclesMap] using
    (ShortComplex.epi_homologyMap_of_epi_cyclesMap'
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
        (lower_stupid_truncation_inclusion E c))
      (show Epi
        (ShortComplex.cyclesMap
          ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (ComplexShape.up ℤ) c).map
            (lower_stupid_truncation_inclusion E c))) by
          simpa [HomologicalComplex.cyclesMap] using
            lower_stupid_truncation_cyclesMap_epi_at_cutoff (R := R) E c))

/-- Helper for Lemma 15.65.2: the lower brutal truncation is supported in degrees `≥ c`. -/
private theorem lower_stupid_truncation_isStrictlyGE
    (E : Cpx) (c : ℤ) :
    CochainComplex.IsStrictlyGE ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c) : Cpx)) c := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i ?_
  simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hi

/-- Helper for Lemma 15.65.2: a lower brutal truncation inherits any upper support bound from the
ambient complex. -/
private theorem lower_stupid_truncation_isStrictlyLE
    (E : Cpx) (c b : ℤ) [E.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c) : Cpx)) b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_cases hci : c ≤ i
  · let e := lower_stupid_truncation_x_iso E c i hci
    have hzero : Limits.IsZero (E.X i) := by
      simpa using E.isZero_of_isStrictlyLE b i hi
    exact hzero.of_iso e
  · have hzero :
        Limits.IsZero ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i) := by
      refine E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i ?_
      simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hci
    exact hzero

/-- Helper for Lemma 15.65.2: lower brutal truncation preserves termwise finite freeness. -/
private theorem isTermwiseFiniteFree_lower_stupid_truncation
    (E : Cpx) (c : ℤ) [E.IsTermwiseFiniteFree] :
    CochainComplex.IsTermwiseFiniteFree
      ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c) : Cpx)) := by
  refine ⟨fun i ↦ ?_⟩
  by_cases hci : c ≤ i
  · -- Retained degrees are canonically identified with the original terms of `E`.
    let e := lower_stupid_truncation_x_iso E c i hci
    rcases CochainComplex.IsTermwiseFiniteFree.out (E := E) i with ⟨hFree, hFinite⟩
    exact
      ⟨Module.Free.of_equiv e.toLinearEquiv.symm,
        Module.Finite.of_surjective e.toLinearEquiv.symm.toLinearMap
          e.toLinearEquiv.symm.surjective⟩
  · have hzero : Limits.IsZero ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i) := by
      -- Discarded degrees become zero terms in the truncation.
      refine E.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE c) i ?_
      simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hci
    let _ :
        Subsingleton (((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i : ModuleCat R)) :=
      ModuleCat.subsingleton_of_isZero hzero
    let eZero :
        (((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i : ModuleCat R)) ≃ₗ[R]
          (Fin 0 → R) :=
      LinearEquiv.ofSubsingleton _ _
    have hFreeZero :
        Module.Free R ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i : ModuleCat R) :=
      Module.Free.of_equiv eZero.symm
    have hFiniteZero :
        Module.Finite R ((E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i : ModuleCat R) :=
      Module.Finite.of_surjective
        (0 : (Fin 0 → R) →ₗ[R] (E.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X i) <| by
          intro x
          refine ⟨0, ?_⟩
          exact Subsingleton.elim _ _
    exact ⟨hFreeZero, hFiniteZero⟩

/-- Helper for Lemma 15.65.2: after lower brutal truncation at `m + 1`, the comparison with the
original witness still has the expected homology window. -/
private theorem homology_window_of_lower_truncation_comparison
    {E K : Cpx} (m : ℤ) (a : E ⟶ K)
    (ha_gt : ∀ i : ℤ, m + 1 < i → IsIso (HomologicalComplex.homologyMap a i))
    (ha_cutoff : Epi (HomologicalComplex.homologyMap a (m + 1))) :
    (∀ i : ℤ,
      m + 1 < i →
        IsIso
          (HomologicalComplex.homologyMap
            (lower_stupid_truncation_inclusion E (m + 1) ≫ a) i)) ∧
      Epi
        (HomologicalComplex.homologyMap
          (lower_stupid_truncation_inclusion E (m + 1) ≫ a) (m + 1)) := by
  constructor
  · intro i hi
    -- Above the cutoff, both the truncation inclusion and the original comparison are
    -- isomorphisms on homology, so their composite is as well.
    rw [HomologicalComplex.homologyMap_comp]
    letI :
        IsIso
          (HomologicalComplex.homologyMap
            (lower_stupid_truncation_inclusion E (m + 1)) i) :=
      homologyMap_lower_stupid_truncation_inclusion_isIso_above E (m + 1) i hi
    letI : IsIso (HomologicalComplex.homologyMap a i) := ha_gt i hi
    infer_instance
  · -- At the cutoff, both factors are epimorphisms on homology, so the composite remains epi.
    rw [HomologicalComplex.homologyMap_comp]
    letI :
        Epi
          (HomologicalComplex.homologyMap
            (lower_stupid_truncation_inclusion E (m + 1)) (m + 1)) :=
      homologyMap_lower_stupid_truncation_inclusion_epi_at_cutoff E (m + 1)
    letI : Epi (HomologicalComplex.homologyMap a (m + 1)) := ha_cutoff
    infer_instance

/-- Helper for Lemma 15.65.2: a termwise finite free cochain complex with an upper support bound
is a `ProjectiveMinus` complex. -/
private theorem minus_of_isStrictlyLE
    (E : Cpx) {b : ℤ} (hE : E.IsStrictlyLE b) :
    CochainComplex.minus (ModuleCat R) E :=
  (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hE⟩

-- Proof sketch: compare finite-free approximations of `T.obj₁` and `T.obj₂` by a morphism of
-- complexes and use the cone triangle together with the long exact cohomology sequence to produce
-- the required approximation of `T.obj₃`.
/-- Lemma 15.65.2 (1): in a distinguished triangle in `D(R)`, if the first term is
`(m + 1)`-pseudo-coherent and the second term is `m`-pseudo-coherent, then the third term is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₃_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsMPseudoCoherent (m + 1)) (h₂ : T.obj₂.IsMPseudoCoherent m) :
    T.obj₃.IsMPseudoCoherent m := by
  -- Route correction: keep the source truncation-and-cone argument, but only strictify the
  -- bounded-projective-source composite into the second vertex instead of the whole triangle.
  let T' : Triangle DMod :=
    Triangle.mk
      ((DerivedCategory.Q.objObjPreimageIso T.obj₁).hom ≫ T.mor₁ ≫
        (DerivedCategory.Q.objObjPreimageIso T.obj₂).inv)
      ((DerivedCategory.Q.objObjPreimageIso T.obj₂).hom ≫ T.mor₂)
      (T.mor₃ ≫ (DerivedCategory.Q.objObjPreimageIso T.obj₁).inv⟦(1 : ℤ)⟧')
  have h₁' :
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage T.obj₁)).IsMPseudoCoherent (m + 1) :=
    isMPseudoCoherent_of_iso (DerivedCategory.Q.objObjPreimageIso T.obj₁).symm (m + 1) h₁
  have h₂' :
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage T.obj₂)).IsMPseudoCoherent m :=
    isMPseudoCoherent_of_iso (DerivedCategory.Q.objObjPreimageIso T.obj₂).symm m h₂
  rcases h₁' with ⟨E₁, ⟨_, b₁, _, hE₁le⟩, hE₁free, α₁, hα₁gt, hα₁m⟩
  rcases h₂' with ⟨E₂, ⟨_, b₂, _, hE₂le⟩, hE₂free, α₂, hα₂gt, hα₂m⟩
  letI : E₁.IsStrictlyLE b₁ := hE₁le
  letI : E₂.IsStrictlyLE b₂ := hE₂le
  letI : E₁.IsTermwiseFiniteFree := hE₁free
  letI : E₂.IsTermwiseFiniteFree := hE₂free
  let P₁ : Cpx := E₁.stupidTrunc (ComplexShape.embeddingUpIntGE (m + 1))
  have hP₁ge : P₁.IsStrictlyGE m := by
    -- The lower brutal truncation vanishes below `m + 1`, hence in particular below `m`.
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    refine E₁.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE (m + 1)) i ?_
    simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using (show i < m + 1 by omega)
  have hP₁le : P₁.IsStrictlyLE b₁ := by
    -- The truncation keeps the same upper support bound as `E₁`.
    simpa [P₁] using lower_stupid_truncation_isStrictlyLE E₁ (m + 1) b₁
  have hP₁free : P₁.IsTermwiseFiniteFree := by
    -- Lower brutal truncation preserves the finite-free terms needed for the source witness.
    simpa [P₁] using isTermwiseFiniteFree_lower_stupid_truncation E₁ (m + 1)
  letI : P₁.IsTermwiseFiniteFree := hP₁free
  have hP₁minus : CochainComplex.minus (ModuleCat R) P₁ := by
    -- The extracted helper packages the bounded-above truncation as a minus complex.
    exact minus_of_isStrictlyLE P₁ hP₁le
  let P₁proj : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨P₁, hP₁minus⟩, fun i ↦ by infer_instance⟩
  have hα₁roof := DerivedCategory.right_fac α₁
  have hα₂roof := DerivedCategory.right_fac α₂
  let _ := T'
  let _ := hP₁ge
  let _ := P₁proj
  let _ := hα₁gt
  let _ := hα₁m
  let _ := hα₂gt
  let _ := hα₂m
  let _ := hα₁roof
  let _ := hα₂roof
  -- TODO: replace the unavailable direct chain representatives of `α₁` and `α₂` by a
  -- source-faithful use of `DerivedCategory.right_fac`/`left_fac`, then apply the new projective
  -- representative and cone-comparison helpers to finish the truncation-and-cone argument.
  sorry

/-- For fixed `m`, `m`-pseudo-coherent objects of `D(R)` satisfy the canonical
`ObjectProperty.IsTriangulatedClosed₂` two-out-of-three axiom. -/
instance isMPseudoCoherent_isTriangulatedClosed₂ (m : ℤ) :
    IsTriangulatedClosed₂ (fun K : DMod ↦ K.IsMPseudoCoherent m) :=
  .mk' fun T hT h₁ h₃ ↦ by
    have h₃' : (T.obj₃⟦-1⟧).IsMPseudoCoherent (m + 1) := by
      simpa using (isMPseudoCoherent_shift_iff T.obj₃ (-1) m).2 h₃
    exact isMPseudoCoherent_obj₃_of_distinguishedTriangle T.invRotate
      (inv_rot_of_distTriang T hT) h₃' h₁

-- Proof sketch: rotate the distinguished triangle once and reduce to part `(1)`.
/-- Lemma 15.65.2 (2): in a distinguished triangle in `D(R)`, if the first and third terms are
`m`-pseudo-coherent, then the second term is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₂_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : T.obj₁.IsMPseudoCoherent m) (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₂.IsMPseudoCoherent m := by
  let P : ObjectProperty DMod := fun K ↦ K.IsMPseudoCoherent m
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

-- Proof sketch: rotate the distinguished triangle once so that `T.obj₁⟦1⟧` becomes the third
-- vertex, apply part `(1)`, and shift back.
/-- Lemma 15.65.2 (3): in a distinguished triangle in `D(R)`, if the second term is
`(m + 1)`-pseudo-coherent and the third term is `m`-pseudo-coherent, then the first term is
`(m + 1)`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₁_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : T.obj₂.IsMPseudoCoherent (m + 1)) (h₃ : T.obj₃.IsMPseudoCoherent m) :
    T.obj₁.IsMPseudoCoherent (m + 1) := by
  have hshift : (T.obj₁⟦(1 : ℤ)⟧).IsMPseudoCoherent m :=
    isMPseudoCoherent_obj₃_of_distinguishedTriangle T.rotate
      (rot_of_distTriang T hT) h₂ h₃
  have hshift' : (T.obj₁⟦(1 : ℤ)⟧).IsMPseudoCoherent ((m + 1) - 1) := by
    simpa using hshift
  exact (isMPseudoCoherent_shift_iff T.obj₁ 1 (m + 1)).1 hshift'

end

end CategoryTheory
