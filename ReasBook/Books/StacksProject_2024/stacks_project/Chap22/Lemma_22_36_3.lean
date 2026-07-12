import StacksProject_2024.Chap22.CompactDGModule
import StacksProject_2024.Chap22.PropertyPDGModule
import StacksProject_2024.Chap22.Lemma_22_28_5
import StacksProject_2024.Chap13.Lemma_13_33_7
import StacksProject_2024.Chap13.Proposition_13_37_6

open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory
open scoped DirectSum

noncomputable section

universe u

namespace CochainComplex

open CochainComplex.PropertyPFiltration

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "Q" => (DerivedCategory.Q : DGMod ⥤ DMod)

/-- A finite cell filtration is the finite-length specialization of the Chapter 22 property `(P)`
filtration. It extends `PropertyPFiltration` with the finite-stage data needed for
Lemma 22.36.3 and Proposition 22.36.4. -/
structure FiniteCellFiltration (P : DGMod) extends PropertyPFiltration P where
  /-- The last stage at which new cells occur. -/
  length : ℕ
  /-- The filtration reaches the ambient differential graded module at stage `length`. -/
  topIso : stage length ≅ P
  /-- The successive quotients before the terminal stage are finite direct sums of shifted free
  differential graded modules. -/
  pieceFintype : ∀ i : Fin length, Fintype (pieceIndex i)
  /-- No new summands occur after the terminal stage. -/
  pieceIsEmpty : ∀ n : ℕ, length ≤ n → IsEmpty (pieceIndex n)

namespace FiniteCellFiltration

/-- The quotient index type at each nontrivial stage of a finite cell filtration is finite. -/
instance instPieceIndexFintype {P : DGMod}
    (F : FiniteCellFiltration P) (i : Fin F.length) :
    Fintype (F.pieceIndex i) :=
  F.pieceFintype i

/-- The stage maps of a finite cell filtration are monomorphisms. -/
instance instMonoInclusion {P : DGMod}
    (F : FiniteCellFiltration P) (n : ℕ) :
    Mono (F.inclusion n) :=
  F.mono n

/-- A finite cell filtration is, in particular, a property `(P)` filtration. -/
theorem hasPropertyP {P : DGMod}
    (F : FiniteCellFiltration P) :
    HasPropertyP P :=
  F.toPropertyPFiltration.hasPropertyP

end FiniteCellFiltration

/-- A finite-support subfiltration of a Chapter 22 property `(P)` filtration. The chosen
subobject carries a finite cell filtration, and each of its nontrivial quotient pieces is indexed
by a finite subset of the corresponding ambient quotient index type. -/
structure FiniteSummandSubfiltration
    {P : DGMod} (F : PropertyPFiltration P) where
  /-- The resulting differential graded submodule of `P`. -/
  subobject : Subobject P
  /-- The induced finite cell filtration on the chosen submodule. -/
  filtration : FiniteCellFiltration (Subobject.underlying.obj subobject)
  /-- The stagewise comparison into the ambient property `(P)` filtration. -/
  stageMap (n : ℕ) : filtration.stage n ⟶ F.stage n
  /-- The stagewise comparison maps form commutative squares with the filtration inclusions. -/
  stageMap_comm (n : ℕ) :
    CommSq
      (filtration.inclusion n)
      (stageMap n)
      (stageMap (n + 1))
      (F.inclusion n)
  /-- The top comparison lands in the ambient object through the cocone map of the property `(P)`
  filtration. -/
  stageMap_top :
    filtration.topIso.hom ≫ subobject.arrow =
      stageMap filtration.length ≫ F.coconeApp filtration.length
  /-- The induced map from a quotient of the finite subfiltration to the corresponding ambient
  quotient. -/
  quotientMap (i : Fin filtration.length) :
    cokernel (filtration.inclusion i.1) ⟶ cokernel (F.inclusion i.1)
  /-- `quotientMap` is induced by the comparison map on the next filtration stage. -/
  quotientMap_comm (i : Fin filtration.length) :
    CommSq
      (stageMap (i.1 + 1))
      (cokernel.π (filtration.inclusion i.1))
      (cokernel.π (F.inclusion i.1))
      (quotientMap i)
  /-- The retained summands at each nontrivial stage form an actual subset of the ambient
  summand family. -/
  pieceSubset (i : Fin filtration.length) : Set (F.pieceIndex i)
  /-- The retained quotient summands are indexed by the chosen subset. -/
  pieceIndexEquiv (i : Fin filtration.length) : filtration.pieceIndex i ≃ pieceSubset i
  /-- The finite subfiltration uses the same shift degrees as the ambient summands it retains. -/
  pieceDegree_eq (i : Fin filtration.length) (j : filtration.pieceIndex i) :
    filtration.pieceDegree i j = F.pieceDegree i (pieceIndexEquiv i j)

namespace FiniteSummandSubfiltration

/-- The underlying differential graded module of the chosen finite-support subfiltration. -/
abbrev obj {P : DGMod} {F : PropertyPFiltration P} (F' : FiniteSummandSubfiltration F) : DGMod :=
  Subobject.underlying.obj F'.subobject

instance instPieceSubsetFintype
    {P : DGMod} {F : PropertyPFiltration P} (F' : FiniteSummandSubfiltration F)
    (i : Fin F'.filtration.length) :
    Fintype (F'.pieceSubset i) :=
  Fintype.ofEquiv (F'.filtration.pieceIndex i) (F'.pieceIndexEquiv i)

end FiniteSummandSubfiltration

/-- Helper for Lemma 22.36.3: the ambient cocone map at stage `n` is the colimit structure map
followed by the inverse of the chosen colimit comparison. -/
theorem coconeApp_eq_colimitι_comp_colimitIso_inv
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    F.coconeApp n =
      colimit.ι (Functor.ofSequence F.inclusion) n ≫ F.colimitIso.inv :=
  rfl

/-- Helper for Lemma 22.36.3: compactness first cuts any map into `P` down to one finite stage of
the chosen property `(P)` filtration. -/
theorem compactFactorsThroughFiltrationStage
    (E : DMod)
    (hE : derivedCompactObject E)
    {P : DGMod} (F : PropertyPFiltration P) (f : E ⟶ Q.obj P) :
    ∃ n : ℕ, ∃ ψ : E ⟶ Q.obj (F.stage n), ψ ≫ Q.map (F.coconeApp n) = f := by
  let S : ℕ ⥤ DGMod := Functor.ofSequence F.inclusion
  have hCompact : IsCompactObject E := by
    simpa [derivedCompactObject, CategoryTheory.isCompactObject_iff] using hE
  let fColim : E ⟶ Q.obj (colimit S) :=
    f ≫ Q.map F.colimitIso.hom
  -- Proof comment: apply the Chapter 13 homotopy-colimit factorization theorem to the sequential
  -- stage diagram underlying the filtration.
  obtain ⟨n, ψ, hψ⟩ :=
    compact_map_factors_through_hocolim_stage
      (K := E) hCompact F.inclusion
      (fun n ↦ Q.map (colimit.ι S n))
      (termwise_colimit_presentation_connecting (𝒜 := ModuleCat A) S)
      (termwise_colimit_presentation_distinguished (𝒜 := ModuleCat A) S)
      fColim
  refine ⟨n, ψ, ?_⟩
  -- Proof comment: rewrite the ambient cocone leg through the colimit comparison and cancel the
  -- colimit isomorphism produced in the previous step.
  calc
    ψ ≫ Q.map (F.coconeApp n) =
      ψ ≫ Q.map (colimit.ι S n) ≫ Q.map F.colimitIso.inv := by
        rw [coconeApp_eq_colimitι_comp_colimitIso_inv]
        rw [Functor.map_comp]
        simp [Category.assoc, S]
    _ = f ≫ Q.map F.colimitIso.hom ≫ Q.map F.colimitIso.inv := by
        rw [hψ]
        simp [Category.assoc, fColim]
    _ = f := by
        rw [← Functor.map_comp]
        simp [Category.assoc]

/-- Helper for Lemma 22.36.3: the `0 ⟶ Y ⟶ Y ⟶ ⋯` tail filtration stage family. -/
private def zeroThenIdentityTailStage (Y : DGMod) : ℕ → DGMod
  | 0 => ⊥_ DGMod
  | _ + 1 => Y

/-- Helper for Lemma 22.36.3: the transition maps in the `0 ⟶ Y ⟶ Y ⟶ ⋯` tail filtration. -/
private def zeroThenIdentityTailInclusion (Y : DGMod) :
    ∀ n : ℕ, zeroThenIdentityTailStage Y n ⟶ zeroThenIdentityTailStage Y (n + 1)
  | 0 => 0
  | _ + 1 => 𝟙 Y

/-- Helper for Lemma 22.36.3: the sequential diagram underlying the `0 ⟶ Y ⟶ Y ⟶ ⋯` tail
filtration. -/
private abbrev zeroThenIdentityTailDiagram (Y : DGMod) : ℕ ⥤ DGMod :=
  Functor.ofSequence (zeroThenIdentityTailInclusion Y)

/-- Helper for Lemma 22.36.3: every map out of stage `1` in the constant tail is the identity. -/
private theorem zeroThenIdentityTail_map_from_one (Y : DGMod) (k : ℕ) :
    (zeroThenIdentityTailDiagram Y).map
        (homOfLE (Nat.succ_le_succ (Nat.zero_le k))) =
      𝟙 Y := by
  induction k with
  | zero =>
      -- Proof comment: the first tail map is the identity because stage `1` already lies in the
      -- constant `Y`-tail.
      simpa [zeroThenIdentityTailDiagram, zeroThenIdentityTailStage] using
        (CategoryTheory.Functor.OfSequence.map_id (zeroThenIdentityTailInclusion Y) 1)
  | succ k hk =>
      -- Proof comment: factor the longer tail map through the previous tail stage and use the
      -- induction hypothesis together with the identity tail step.
      rw [show homOfLE (Nat.succ_le_succ (Nat.zero_le (k + 1))) =
            homOfLE (Nat.succ_le_succ (Nat.zero_le k)) ≫ homOfLE (Nat.le_succ (k + 1)) by
              apply Subsingleton.elim]
      rw [Functor.map_comp, hk]
      exact congrArg (fun t ↦ 𝟙 Y ≫ t)
        (CategoryTheory.Functor.OfSequence.map_le_succ
          (zeroThenIdentityTailInclusion Y) (k + 1))

/-- Helper for Lemma 22.36.3: the colimit of `0 ⟶ Y ⟶ Y ⟶ ⋯` is already reached at stage `1`. -/
private theorem colimitIsoOfZeroThenIdentityTail (Y : DGMod) :
    Y ≅ colimit (zeroThenIdentityTailDiagram Y) := by
  let h : (zeroThenIdentityTailDiagram Y).IsEventuallyConstantFrom 1 := by
    intro j f
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (CategoryTheory.leOfHom f)
    have hf : f = homOfLE (Nat.succ_le_succ (Nat.zero_le k)) := Subsingleton.elim _ _
    subst hf
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (show IsIso
        ((zeroThenIdentityTailDiagram Y).map
          (homOfLE (Nat.succ_le_succ (Nat.zero_le k)))) by
            rw [zeroThenIdentityTail_map_from_one Y k]
            infer_instance)
  -- Proof comment: apply the eventually-constant colimit API instead of rebuilding a cocone by
  -- hand for the constant tail.
  exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h.isColimitCocone).symm

/-- Helper for Lemma 22.36.3: the first zero map into a differential graded module is an
admissible monomorphism after forgetting the differential. -/
private theorem isAdmissibleMono_zeroFromInitial (Y : DGMod) :
    IsAdmissibleMono dgModuleUnderlyingGradedHomSystem (0 : (⊥_ DGMod) ⟶ Y) := by
  -- Proof comment: the underlying graded map splits through the unique map back to the initial
  -- graded object.
  rw [isAdmissibleMono_iff_exists_retraction]
  refine ⟨0, ?_⟩
  ext n x
  simpa using (Subsingleton.elim x 0)

/-- Helper for Lemma 22.36.3: the first zero map into a differential graded module is
monomorphic. -/
private theorem mono_zeroFromInitial (Y : DGMod) :
    Mono (0 : (⊥_ DGMod) ⟶ Y) := by
  exact initialIsInitial.isZero.mono (0 : (⊥_ DGMod) ⟶ Y)

/-- Helper for Lemma 22.36.3: the empty coproduct of shifted free differential graded modules is a
zero object. -/
private theorem isZero_emptyShiftedFreeCoproduct (degree : PEmpty → ℤ) :
    IsZero (∐ fun i : PEmpty ↦ shiftedFreeDGModule A (degree i)) := by
  let G : Discrete PEmpty ⥤ DGMod :=
    Discrete.functor (fun i : PEmpty ↦ shiftedFreeDGModule A (degree i))
  -- Proof comment: identify the empty coproduct with a colimit of the constant initial diagram.
  refine (IsInitial.ofIso initialIsInitial ?_).isZero
  let e : G ≅ (Functor.const (Discrete PEmpty)).obj (⊥_ DGMod) :=
    NatIso.ofComponents (fun i ↦ PEmpty.elim i.as)
  exact colimitConstInitial.symm ≪≫ (HasColimit.isoOfNatIso e).symm

/-- Helper for Lemma 22.36.3: the cokernel of the zero map out of the initial differential graded
module is canonically the target. -/
private noncomputable def cokernelZeroFromZeroIso (Y : DGMod) :
    cokernel (0 : (⊥_ DGMod) ⟶ Y) ≅ Y := by
  let c :
      IsColimit
        (CokernelCofork.ofπ (𝟙 Y) (by simp :
          (0 : (⊥_ DGMod) ⟶ Y) ≫ 𝟙 Y = 0)) := by
    refine CokernelCofork.IsColimit.ofπ' (𝟙 Y) (by simp) ?_
    intro Z s hs
    exact ⟨s, by simpa using hs⟩
  -- Proof comment: compare the explicit cokernel cofork with the chosen categorical cokernel.
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (0 : (⊥_ DGMod) ⟶ Y)) c

/-- Helper for Lemma 22.36.3: the underlying differential graded module of the bottom subobject is
a zero object. -/
private theorem botUnderlyingIsZero {P : DGMod} :
    IsZero (Subobject.underlying.obj (⊥ : Subobject P)) :=
  (isZero_zero DGMod).of_iso Subobject.botCoeIsoZero

/-- Helper for Lemma 22.36.3: project the telescope coproduct onto the prefix ending at stage
`k`, sending later summands to zero. -/
private noncomputable def stagePrefixProjection
    {P : DGMod} (F : PropertyPFiltration P) (k : ℕ) :
    F.toFiltration.telescopeShortComplex.X₂ ⟶ F.stage k :=
  Limits.Sigma.desc fun i : ℕ ↦
    if h : i ≤ k then F.toFiltration.diagram.map (homOfLE h) else 0

/-- Helper for Lemma 22.36.3: on a retained summand, `stagePrefixProjection` is the expected
iterated filtration inclusion. -/
private theorem sigma_ι_stagePrefixProjection
    {P : DGMod} (F : PropertyPFiltration P) {i k : ℕ} (h : i ≤ k) :
    Limits.Sigma.ι F.toFiltration.diagram.obj i ≫ stagePrefixProjection F k =
      F.toFiltration.diagram.map (homOfLE h) := by
  -- Proof comment: the telescope coproduct projection is defined by `Sigma.desc`, so the `i`-th
  -- component reduces immediately to the chosen branch of the prefix family.
  simp [stagePrefixProjection, h, Limits.Sigma.ι_desc]

/-- Helper for Lemma 22.36.3: later summands are killed by `stagePrefixProjection`. -/
private theorem sigma_ι_stagePrefixProjection_eq_zero
    {P : DGMod} (F : PropertyPFiltration P) {i k : ℕ} (h : ¬ i ≤ k) :
    Limits.Sigma.ι F.toFiltration.diagram.obj i ≫ stagePrefixProjection F k = 0 := by
  -- Proof comment: by definition the prefix projection sends summands past stage `k` to zero.
  simp [stagePrefixProjection, h, Limits.Sigma.ι_desc]

/-- Helper for Lemma 22.36.3: the current stage summand is sent to the identity under the matching
prefix projection. -/
private theorem sigma_ι_stagePrefixProjection_self
    {P : DGMod} (F : PropertyPFiltration P) (k : ℕ) :
    Limits.Sigma.ι F.toFiltration.diagram.obj k ≫ stagePrefixProjection F k = 𝟙 (F.stage k) := by
  -- Proof comment: the `k`-th summand lies in the retained prefix by reflexivity.
  simpa using sigma_ι_stagePrefixProjection F (Nat.le_refl k)

/-- Helper for Lemma 22.36.3: the recursive telescope stage lift followed by a later prefix
projection is the expected iterated filtration inclusion. -/
private theorem telescopeDegreewiseStageLift_comp_stagePrefixProjection_of_le
    {P : DGMod} (F : PropertyPFiltration P) (n : ℤ) :
    ∀ {k m : ℕ} (hkm : k ≤ m),
      telescopeDegreewiseStageLift F n k ≫ (stagePrefixProjection F m).f n =
        ((F.toFiltration.diagram ⋙ HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n).map
          (homOfLE hkm)) := by
  intro k
  induction k with
  | zero =>
      intro m h0m
      have hzero : IsZero ((F.stage 0).X n) := by
        -- Proof comment: evaluation preserves the zero initial filtration stage.
        simpa using
          (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n).map_isZero F.stageZero
      -- Proof comment: both maps out of the degree-`n` zero stage are equal.
      exact hzero.eq_of_src _ _
  | succ k ih =>
      intro m hkm
      let D :=
        F.toFiltration.diagram ⋙ HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n
      have hkm' : k ≤ m := Nat.le_trans (Nat.le_succ k) hkm
      have hprev :
          telescopeDegreewiseStageLift F n k ≫ (stagePrefixProjection F m).f n =
            D.map (homOfLE hkm') :=
        ih hkm'
      have hsigma :
          ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n) ≫
              (stagePrefixProjection F m).f n =
            D.map (homOfLE hkm) := by
        -- Proof comment: once the `(k + 1)`-st summand lies in the retained prefix, the prefix
        -- projection is exactly the iterated inclusion into stage `m`.
        simpa [D] using
          congrArg (fun t ↦ t.f n) (sigma_ι_stagePrefixProjection (F := F) hkm)
      have hstep :
          D.map (homOfLE hkm') =
            (F.inclusion k).f n ≫ D.map (homOfLE hkm) := by
        have hhom :
            homOfLE hkm' = homOfLE (Nat.le_succ k) ≫ homOfLE hkm :=
          Subsingleton.elim _ _
        -- Proof comment: the iterated map from stage `k` to stage `m` factors through the
        -- successor stage `k + 1`.
        calc
          D.map (homOfLE hkm') = D.map (homOfLE (Nat.le_succ k) ≫ homOfLE hkm) := by
            rw [hhom]
          _ = D.map (homOfLE (Nat.le_succ k)) ≫ D.map (homOfLE hkm) := by
            rw [Functor.map_comp]
          _ = (F.inclusion k).f n ≫ D.map (homOfLE hkm) := by
            simpa [D, _root_.PropertyPFiltration.diagram,
              Functor.ofSequence_map_homOfLE_succ]
      -- Proof comment: expand the recursive lift once; the old-prefix term and the correction
      -- term together recombine to the desired stage map into `m`.
      calc
        telescopeDegreewiseStageLift F n (k + 1) ≫ (stagePrefixProjection F m).f n =
          (stepTermwiseRetraction F k n ≫ telescopeDegreewiseStageLift F n k +
              (𝟙 _ - stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n)) ≫
            (stagePrefixProjection F m).f n := by
              rfl
        _ =
          stepTermwiseRetraction F k n ≫
              (telescopeDegreewiseStageLift F n k ≫ (stagePrefixProjection F m).f n) +
            ((𝟙 _ - stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
                ((Limits.Sigma.ι F.toFiltration.diagram.obj (k + 1)).f n ≫
                  (stagePrefixProjection F m).f n)) := by
              simp only [Preadditive.add_comp, Category.assoc]
        _ =
          stepTermwiseRetraction F k n ≫ D.map (homOfLE hkm') +
            (𝟙 _ - stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
              D.map (homOfLE hkm) := by
              rw [hprev, hsigma]
        _ =
          stepTermwiseRetraction F k n ≫ ((F.inclusion k).f n ≫ D.map (homOfLE hkm)) +
            (𝟙 _ - stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) ≫
              D.map (homOfLE hkm) := by
              rw [hstep]
        _ =
          ((stepTermwiseRetraction F k n ≫ (F.inclusion k).f n) +
              (𝟙 _ - stepTermwiseRetraction F k n ≫ (F.inclusion k).f n)) ≫
            D.map (homOfLE hkm) := by
              rw [Category.assoc]
              rw [← Preadditive.add_comp]
        _ = D.map (homOfLE hkm) := by
              simp

/-- Helper for Lemma 22.36.3: the recursive telescope stage lift followed by the prefix projection
to the same stage is the identity. -/
private theorem telescopeDegreewiseStageLift_comp_stagePrefixProjection
    {P : DGMod} (F : PropertyPFiltration P) (n : ℤ) :
    ∀ k : ℕ,
      telescopeDegreewiseStageLift F n k ≫ (stagePrefixProjection F k).f n =
        𝟙 ((F.stage k).X n) := by
  intro k
  -- Proof comment: the same-stage identity is the diagonal specialization of the stronger
  -- later-stage compatibility lemma.
  simpa using
    telescopeDegreewiseStageLift_comp_stagePrefixProjection_of_le (F := F) (n := n)
      (Nat.le_refl k)

/-- Helper for Lemma 22.36.3: every cocone leg of the ambient property `(P)` filtration is
monomorphic. -/
private theorem mono_coconeApp
    {P : DGMod} (F : PropertyPFiltration P) (k : ℕ) :
    Mono (F.coconeApp k) := by
  -- Proof comment: degreewise, the telescope section followed by the matching prefix projection
  -- is a retraction of the stage-to-ambient map.
  refine HomologicalComplex.mono_of_mono_f _ ?_
  intro n
  let s : P.X n ⟶ (F.stage k).X n :=
    telescopeDegreewiseSection F n ≫ (stagePrefixProjection F k).f n
  have hs :
      (F.coconeApp k).f n ≫ s = 𝟙 ((F.stage k).X n) := by
    calc
      (F.coconeApp k).f n ≫ s =
        ((F.coconeApp k).f n ≫ telescopeDegreewiseSection F n) ≫
          (stagePrefixProjection F k).f n := by
            simp [s, Category.assoc]
      _ = telescopeDegreewiseStageLift F n k ≫ (stagePrefixProjection F k).f n := by
            simpa [Category.assoc, s] using
              congrArg
                (fun t ↦ t ≫ (stagePrefixProjection F k).f n)
                (telescopeDegreewiseSection_fac F n k)
      _ = 𝟙 ((F.stage k).X n) :=
            telescopeDegreewiseStageLift_comp_stagePrefixProjection F n k
  letI : IsSplitMono ((F.coconeApp k).f n) := IsSplitMono.mk' ⟨s, hs⟩
  infer_instance

/-- Helper for Lemma 22.36.3: the `n`-th filtration stage viewed as a subobject of the ambient
differential graded module. -/
private noncomputable abbrev stageSubobject
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) : Subobject P :=
  Subobject.mk (F.coconeApp n)

/-- Helper for Lemma 22.36.3: the underlying object of `stageSubobject F n` is canonically the
original stage `F.stage n`. -/
private noncomputable abbrev stageSubobjectIso
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    Subobject.underlying.obj (stageSubobject F n) ≅ F.stage n :=
  Subobject.underlyingIso (F.coconeApp n)

/-- Helper for Lemma 22.36.3: rewriting the packaged stage subobject arrow through the canonical
underlying isomorphism recovers the original cocone leg. -/
private theorem stageSubobjectIso_inv_arrow
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    (stageSubobjectIso F n).inv ≫ (stageSubobject F n).arrow = F.coconeApp n := by
  -- Proof comment: `stageSubobject F n` is defined by `Subobject.mk (F.coconeApp n)`, so the
  -- generic `Subobject.underlyingIso_arrow` lemma normalizes the packaged arrow immediately.
  simpa [stageSubobject, stageSubobjectIso] using
    (Subobject.underlyingIso_arrow (F.coconeApp n))

/-- Helper for Lemma 22.36.3: the forward direction of `stageSubobjectIso` also rewrites the
ambient arrow to the packaged `Subobject.mk` map. -/
private theorem stageSubobjectIso_hom_comp_coconeApp
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    (stageSubobjectIso F n).hom ≫ F.coconeApp n = (stageSubobject F n).arrow := by
  -- Proof comment: this is the arrow-level normalization used when comparing successive stage
  -- subobjects inside the ambient object `P`.
  simpa [stageSubobject, stageSubobjectIso] using
    (Subobject.underlyingIso_hom_comp_eq_mk (F.coconeApp n))

/-- Helper for Lemma 22.36.3: the ambient subobject of stage `n` lies in the ambient subobject of
stage `n + 1`. -/
private theorem stageSubobject_le_succ
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    stageSubobject F n ≤ stageSubobject F (n + 1) := by
  refine Subobject.mk_le_of_comm
    ((stageSubobjectIso F n).hom ≫ F.inclusion n ≫ (stageSubobjectIso F (n + 1)).inv)
    ?_
  -- Proof comment: rewrite both packaged subobject arrows back to the raw cocone maps and then
  -- use the cocone compatibility of the filtration.
  calc
    ((stageSubobjectIso F n).hom ≫ F.inclusion n ≫ (stageSubobjectIso F (n + 1)).inv) ≫
        (stageSubobject F (n + 1)).arrow =
      (stageSubobjectIso F n).hom ≫ F.inclusion n ≫
        ((stageSubobjectIso F (n + 1)).inv ≫ (stageSubobject F (n + 1)).arrow) := by
          simp [Category.assoc]
    _ = (stageSubobjectIso F n).hom ≫ F.inclusion n ≫ F.coconeApp (n + 1) := by
          rw [stageSubobjectIso_inv_arrow]
    _ = (stageSubobjectIso F n).hom ≫ F.coconeApp n := by
          simpa [_root_.PropertyPFiltration.diagram, Functor.ofSequence_map_homOfLE_succ] using
            F.toFiltration.toCocone.naturality (homOfLE (Nat.le_succ n))
    _ = (stageSubobject F n).arrow := by
          rw [stageSubobjectIso_hom_comp_coconeApp]

/-- Helper for Lemma 22.36.3: the `Subobject.ofLE` comparison between two successive ambient
stage subobjects has the expected arrow equation. -/
private theorem stageSubobject_ofLE_arrow
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    Subobject.ofLE (stageSubobject F n) (stageSubobject F (n + 1))
        (stageSubobject_le_succ F n) ≫ (stageSubobject F (n + 1)).arrow =
      (stageSubobject F n).arrow := by
  -- Proof comment: this is the defining factorization identity packaged by `Subobject.ofLE`.
  exact Subobject.ofLE_arrow (stageSubobject_le_succ F n)

/-- Helper for Lemma 22.36.3: after identifying the packaged ambient stage subobjects with the
raw stages, the comparison `stageSubobject F n ⟶ stageSubobject F (n + 1)` is exactly the
original filtration inclusion. -/
private theorem stageSubobjectIso_inv_comp_ofLE
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    (stageSubobjectIso F n).inv ≫
        Subobject.ofLE (stageSubobject F n) (stageSubobject F (n + 1))
          (stageSubobject_le_succ F n) =
      F.inclusion n ≫ (stageSubobjectIso F (n + 1)).inv := by
  apply (cancel_mono ((stageSubobject F (n + 1)).arrow)).1
  -- Proof comment: postcompose with the ambient arrow of `stageSubobject F (n + 1)` and rewrite
  -- both sides back to the raw cocone maps of the original filtration.
  calc
    ((stageSubobjectIso F n).inv ≫
        Subobject.ofLE (stageSubobject F n) (stageSubobject F (n + 1))
          (stageSubobject_le_succ F n)) ≫
        (stageSubobject F (n + 1)).arrow =
      (stageSubobjectIso F n).inv ≫ (stageSubobject F n).arrow := by
        rw [Category.assoc, stageSubobject_ofLE_arrow]
    _ = F.coconeApp n := by
        rw [stageSubobjectIso_inv_arrow]
    _ = F.inclusion n ≫ F.coconeApp (n + 1) := by
        simpa [_root_.PropertyPFiltration.diagram, Functor.ofSequence_map_homOfLE_succ] using
          (F.toFiltration.toCocone.naturality (homOfLE (Nat.le_succ n))).symm
    _ = (F.inclusion n ≫ (stageSubobjectIso F (n + 1)).inv) ≫
          (stageSubobject F (n + 1)).arrow := by
        rw [Category.assoc, stageSubobjectIso_inv_arrow]

/-- Helper for Lemma 22.36.3: the quotient map from the packaged ambient stage
`stageSubobject F (n + 1)` to the next filtration quotient is obtained by transporting the raw
quotient projection across `stageSubobjectIso`. -/
private noncomputable def stageQuotientMap
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    Subobject.underlying.obj (stageSubobject F (n + 1)) ⟶ cokernel (F.inclusion n) :=
  (stageSubobjectIso F (n + 1)).hom ≫ cokernel.π (F.inclusion n)

/-- Helper for Lemma 22.36.3: transporting `stageQuotientMap` back along
`stageSubobjectIso F (n + 1)` recovers the raw cokernel projection. -/
private theorem stageSubobjectIso_inv_comp_stageQuotientMap
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    (stageSubobjectIso F (n + 1)).inv ≫ stageQuotientMap F n =
      cokernel.π (F.inclusion n) := by
  -- Proof comment: this is immediate from the definition of `stageQuotientMap`.
  simp [stageQuotientMap, Category.assoc]

/-- Helper for Lemma 22.36.3: the previous stage subobject maps to zero in the packaged quotient
`stageQuotientMap F n`, exactly as the raw stage `F.stage n` maps to zero in
`cokernel (F.inclusion n)`. -/
private theorem stageSubobject_ofLE_comp_stageQuotientMap_eq_zero
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ) :
    Subobject.ofLE (stageSubobject F n) (stageSubobject F (n + 1))
        (stageSubobject_le_succ F n) ≫
      stageQuotientMap F n = 0 := by
  apply (cancel_mono ((stageSubobjectIso F n).inv)).1
  -- Proof comment: after rewriting the packaged inclusion and quotient map through the stage
  -- isomorphisms, the claim becomes the standard cokernel relation for `F.inclusion n`.
  calc
    (stageSubobjectIso F n).inv ≫
        (Subobject.ofLE (stageSubobject F n) (stageSubobject F (n + 1))
            (stageSubobject_le_succ F n) ≫
          stageQuotientMap F n) =
      (F.inclusion n ≫ (stageSubobjectIso F (n + 1)).inv) ≫
        stageQuotientMap F n := by
          rw [Category.assoc, Category.assoc, stageSubobjectIso_inv_comp_ofLE]
    _ = F.inclusion n ≫ cokernel.π (F.inclusion n) := by
          rw [Category.assoc, stageSubobjectIso_inv_comp_stageQuotientMap]
    _ = 0 := cokernel.condition (F.inclusion n)

/-- Helper for Lemma 22.36.3: once the map lands in one finite stage of the filtration, it should
factor through a finite-support subfiltration of the ambient property `(P)` filtration. -/
theorem factorThroughFiniteSummandSubfiltrationOfStage
    (E : DMod)
    (hE : derivedCompactObject E)
    {P : DGMod} (F : PropertyPFiltration P) (n : ℕ)
    (f : E ⟶ Q.obj (F.stage n)) :
    ∃ (F' : FiniteSummandSubfiltration F)
      (g : E ⟶ Q.obj F'.obj),
      g ≫ Q.map F'.subobject.arrow = f ≫ Q.map (F.coconeApp n) := by
  -- Route correction: the remaining source-faithful work is the finite-prefix recursion inside
  -- `F.stage n`, not the initial compactness reduction to one filtration stage.
  cases n with
  | zero =>
      let pieceDegree : ∀ _ : ℕ, PEmpty → ℤ := fun _ i ↦ PEmpty.elim i
      let Y := Subobject.underlying.obj (⊥ : Subobject P)
      let hY : IsZero Y := botUnderlyingIsZero
      let F₀ : FiniteCellFiltration Y :=
        {
          toPropertyPFiltration :=
            {
              stage := zeroThenIdentityTailStage Y
              stageZero := by
                simpa [zeroThenIdentityTailStage] using (isZero_zero DGMod)
              inclusion := zeroThenIdentityTailInclusion Y
              mono := by
                intro m
                cases m with
                | zero =>
                    simpa [zeroThenIdentityTailInclusion] using mono_zeroFromInitial Y
                | succ m =>
                    simpa [zeroThenIdentityTailInclusion]
              admissible := by
                intro m
                cases m with
                | zero =>
                    simpa [zeroThenIdentityTailInclusion] using
                      isAdmissibleMono_zeroFromInitial Y
                | succ m =>
                    simpa [zeroThenIdentityTailInclusion]
              hasColimit := inferInstance
              colimitIso := colimitIsoOfZeroThenIdentityTail Y
              pieceIndex := fun _ ↦ PEmpty
              pieceDegree := pieceDegree
              pieceHasCoproduct := by
                intro m
                infer_instance
              pieceIso := by
                intro m
                cases m with
                | zero =>
                    -- Proof comment: the only visible quotient is the cokernel of the initial
                    -- zero map, and both its target and the chosen empty coproduct are zero.
                    simpa [pieceDegree, zeroThenIdentityTailInclusion] using
                      (cokernelZeroFromZeroIso Y) ≪≫
                        hY.isoZero ≪≫
                          (isZero_emptyShiftedFreeCoproduct (pieceDegree 0)).isoZero.symm
                | succ m =>
                    -- Proof comment: every later quotient is the cokernel of an identity on the
                    -- zero object, so it again identifies with the empty shifted-free coproduct.
                    simpa [pieceDegree, zeroThenIdentityTailInclusion] using
                      (cokernel.ofEpi (𝟙 Y)) ≪≫
                        (isZero_emptyShiftedFreeCoproduct (pieceDegree (m + 1))).isoZero.symm
            }
          length := 1
          topIso := Iso.refl Y
          pieceFintype := by
            intro i
            have hi : i = 0 := Fin.eq_zero i
            subst hi
            infer_instance
          pieceIsEmpty := by
            intro m hm
            infer_instance
        }
      let F' : FiniteSummandSubfiltration F :=
        {
          subobject := ⊥
          filtration := F₀
          stageMap := fun _ ↦ 0
          stageMap_comm := by
            intro m
            cases m with
            | zero =>
                refine ⟨?_⟩
                exact (isZero_zero DGMod).eq_of_src _ _
            | succ m =>
                refine ⟨?_⟩
                exact hY.eq_of_src _ _
          stageMap_top := by
            exact hY.eq_of_src _ _
          quotientMap := fun _ ↦ 0
          quotientMap_comm := by
            intro i
            have hi : i = 0 := Fin.eq_zero i
            subst hi
            refine ⟨?_⟩
            exact hY.eq_of_src _ _
          pieceSubset := fun _ ↦ ∅
          pieceIndexEquiv := by
            intro i
            have hi : i = 0 := Fin.eq_zero i
            subst hi
            refine
              {
                toFun := fun j ↦ PEmpty.elim j
                invFun := fun j ↦ False.elim j.2
                left_inv := by
                  intro j
                  cases j
                right_inv := by
                  intro j
                  exact False.elim j.2
              }
          pieceDegree_eq := by
            intro i j
            cases j
        }
      have hstage0 : IsZero (Q.obj (F.stage 0)) := Q.map_isZero F.stageZero
      have hf : f = 0 := hstage0.eq_of_tgt _ _
      refine ⟨F', 0, ?_⟩
      -- Proof comment: both sides are zero because the stage-zero source and the chosen bottom
      -- subobject are zero objects.
      simp [FiniteSummandSubfiltration.obj, F', hf]
  | succ n =>
      -- TODO: the remaining source-faithful blocker is the one-step ambient pruning lemma on
      -- `stageSubobject F n ≤ stageSubobject F (n + 1)`. The compactness cut to finite support
      -- should happen on `cokernel (F.inclusion n)`, after which the factorization must descend
      -- through the pullback subobject between these two ambient stages.
      sorry

/-- Lemma 22.36.3: let `E` be a compact object of `D(A, d)` and let `P` admit a property `(P)`
filtration. Then every map `E ⟶ P` factors through a differential graded submodule carrying a
finite cell filtration whose nontrivial quotient pieces are indexed by finite subsets of the
ambient filtration summands. In the current Chapter 22 API, compactness is recorded by
`derivedCompactObject`, the ambient filtration by `PropertyPFiltration`, and the finite-support
conclusion by `FiniteSummandSubfiltration`. -/
@[stacks 09R2]
theorem exists_factorization_through_finiteSummandSubfiltration
    (E : DMod)
    (hE : derivedCompactObject E)
    {P : DGMod} (F : PropertyPFiltration P) (f : E ⟶ Q.obj P) :
    ∃ (F' : FiniteSummandSubfiltration F)
      (g : E ⟶ Q.obj F'.obj),
      g ≫ Q.map F'.subobject.arrow = f := by
  rcases compactFactorsThroughFiltrationStage E hE F f with ⟨n, ψ, hψ⟩
  rcases factorThroughFiniteSummandSubfiltrationOfStage E hE F n ψ with ⟨F', g, hg⟩
  refine ⟨F', g, ?_⟩
  -- Proof comment: compose the stage-level factorization with the compactness reduction already
  -- proved above.
  calc
    g ≫ Q.map F'.subobject.arrow = ψ ≫ Q.map (F.coconeApp n) := hg
    _ = f := hψ

end

end CochainComplex
