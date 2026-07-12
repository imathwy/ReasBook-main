import Mathlib
import StacksProject_2024.Chap05.Example_5_8_12
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap06.Definition_6_27_1
import StacksProject_2024.Chap17.Definition_17_10_1
import StacksProject_2024.Chap17.Lemma_17_10_2
import StacksProject_2024.Chap17.Example_17_10_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits TopCat TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

private abbrev witnessCarrier :=
  FiniteClosedAwayFromPoint (none : Option ℕ)

private abbrev witnessSpace : TopCat :=
  TopCat.of witnessCarrier

/-- Helper for Remark 17.10.3: the chosen generic point in the Example 5.8.12 witness space. -/
private abbrev witnessGenericPoint : witnessSpace :=
  (none : Option ℕ)

/-- Helper for Remark 17.10.3: the closed points indexed by natural numbers in the witness space. -/
private abbrev witnessClosedPoint (n : ℕ) : witnessSpace :=
  some n

/-- Helper for Remark 17.10.3: the witness structure sheaf is the skyscraper ring sheaf at the
generic point, so every nonempty open carries the same ring. -/
private noncomputable def witnessStructureSheaf : TopCat.Sheaf CommRingCat witnessSpace :=
  skyscraperSheaf witnessGenericPoint (CommRingCat.of ℤ)

/-- Helper for Remark 17.10.3: the concrete ringed-space witness built from Example 5.8.12 with
the skyscraper structure sheaf at the generic point. -/
private noncomputable def witnessRingedSpace : RingedSpace :=
  { carrier := witnessSpace
    presheaf := witnessStructureSheaf.obj
    IsSheaf := witnessStructureSheaf.property }

/-- Helper for Remark 17.10.3: the module placed at the closed point `some n` is the regular
module over the stalk ring at that point. -/
private noncomputable def witnessClosedPointModule (n : ℕ) :
    ModuleCat (RingCat.of (witnessRingedSpace.presheaf.stalk (witnessClosedPoint n))) :=
  ModuleCat.of (RingCat.of (witnessRingedSpace.presheaf.stalk (witnessClosedPoint n)))
    (witnessRingedSpace.presheaf.stalk (witnessClosedPoint n))

/-- Helper for Remark 17.10.3: the candidate summands are the skyscraper module sheaves supported
at the closed points `some n`. -/
private noncomputable def witnessFamily : ℕ → RingedSpace.Modules witnessRingedSpace :=
  fun n ↦ skyscraperModuleSheaf (X := witnessRingedSpace) (witnessClosedPoint n)
    (witnessClosedPointModule n)

/-- Helper for Remark 17.10.3: the closed subsets of the witness space are either all of the
space or finite subsets away from the generic point. -/
private theorem witnessClosed_description {s : Set witnessSpace} (hs : IsClosed s) :
    s = Set.univ ∨ s.Finite ∧ s ⊆ ({witnessGenericPoint} : Set witnessSpace)ᶜ := by
  -- Proof comment: this is exactly the public closed-set classification from Example 5.8.12.
  simpa [witnessCarrier, witnessGenericPoint] using
    (FiniteClosedAwayFromPoint.isClosed_iff (z := (none : Option ℕ)) (s := s)).1 hs

/-- Helper for Remark 17.10.3: every proper closed subset of the witness space misses the generic
point. -/
private theorem witnessClosed_subset_generic_compl {s : Set witnessSpace} (hs : IsClosed s)
    (hproper : s ≠ Set.univ) :
    s ⊆ ({witnessGenericPoint} : Set witnessSpace)ᶜ := by
  -- Proof comment: Example 5.8.12 says the only closed set that can contain the generic point is
  -- `univ`, so the proper case is automatically away from that point.
  rcases witnessClosed_description hs with htop | ⟨_, hsubset⟩
  · exact (hproper htop).elim
  · exact hsubset

/-- Helper for Remark 17.10.3: every nonempty open subset of the witness space contains the
generic point. -/
private theorem witnessGenericPoint_mem_of_nonempty_open (U : Opens witnessSpace)
    (hU : Set.Nonempty (U : Set witnessSpace)) :
    witnessGenericPoint ∈ U := by
  -- Proof comment: the complement of a nonempty open is a proper closed subset, hence it misses
  -- the generic point.
  by_contra hz
  have hsubset :
      ((U : Set witnessSpace)ᶜ) ⊆ ({witnessGenericPoint} : Set witnessSpace)ᶜ := by
    apply witnessClosed_subset_generic_compl
    · exact U.isOpen.isClosed_compl
    · intro htop
      rcases hU with ⟨x, hx⟩
      have : x ∈ ((U : Set witnessSpace)ᶜ) := by
        simpa [htop]
      exact this hx
  have hgeneric : witnessGenericPoint ∈ ({witnessGenericPoint} : Set witnessSpace)ᶜ := hsubset hz
  simpa using hgeneric

/-- Helper for Remark 17.10.3: every nonempty open subset of the witness space contains at least
one closed point `some n`. -/
private theorem witnessNonemptyOpen_containsClosedPoint (U : Opens witnessSpace)
    (hU : Set.Nonempty (U : Set witnessSpace)) :
    ∃ n : ℕ, witnessClosedPoint n ∈ U := by
  -- Proof comment: the complement of a nonempty open is finite away from the generic point, so a
  -- natural-number point survives outside that finite exceptional set.
  have hclosed : IsClosed ((U : Set witnessSpace)ᶜ) := U.isOpen.isClosed_compl
  have hproper : ((U : Set witnessSpace)ᶜ) ≠ Set.univ := by
    intro htop
    rcases hU with ⟨x, hx⟩
    have : x ∈ ((U : Set witnessSpace)ᶜ) := by
      simpa [htop]
    exact this hx
  rcases witnessClosed_description hclosed with htop | ⟨hfinite, _⟩
  · exact (hproper htop).elim
  ·
    have hpreimageFinite :
        Set.Finite (Option.some ⁻¹' ((U : Set witnessSpace)ᶜ)) := by
      simpa using hfinite.preimage (show Function.Injective (@Option.some ℕ) from Option.some_injective)
    let exceptional : Finset ℕ := hpreimageFinite.toFinset
    let n : ℕ := exceptional.sup id + 1
    refine ⟨n, ?_⟩
    have hnotMem :
        witnessClosedPoint n ∉ ((U : Set witnessSpace)ᶜ) := by
      intro hnU
      have hnExceptional : n ∈ exceptional := by
        simpa [exceptional, witnessClosedPoint] using hnU
      have hle : n ≤ exceptional.sup id := Finset.le_sup hnExceptional
      exact Nat.not_succ_le_self (exceptional.sup id) (by simpa [n] using hle)
    simpa using hnotMem

/-- Helper for Remark 17.10.3: the generic point is dense in the witness space. -/
private theorem witnessClosure_genericPoint_eq_univ :
    closure ({witnessGenericPoint} : Set witnessSpace) = Set.univ := by
  -- Proof comment: a closed subset containing the generic point must already be all of
  -- `witnessSpace`.
  rcases witnessClosed_description
      (s := closure ({witnessGenericPoint} : Set witnessSpace)) isClosed_closure with
    htop | ⟨_, hsubset⟩
  · exact htop
  ·
    exfalso
    have hmem :
        witnessGenericPoint ∈ closure ({witnessGenericPoint} : Set witnessSpace) :=
      subset_closure (by simp)
    have : witnessGenericPoint ∈ ({witnessGenericPoint} : Set witnessSpace)ᶜ := hsubset hmem
    simpa using this

/-- Helper for Remark 17.10.3: every closed point lies in the closure of the generic point. -/
private theorem witnessClosedPoint_mem_closure_generic (n : ℕ) :
    witnessClosedPoint n ∈ closure ({witnessGenericPoint} : Set witnessSpace) := by
  -- Proof comment: this is the pointwise form of the density statement above.
  simpa [witnessClosure_genericPoint_eq_univ]

/-- Helper for Remark 17.10.3: each closed-point singleton is closed in the witness space. -/
private theorem witnessClosedPoint_singleton_isClosed (n : ℕ) :
    IsClosed ({witnessClosedPoint n} : Set witnessSpace) := by
  -- Proof comment: Example 5.8.12 classifies proper closed sets as finite sets away from the
  -- generic point, and a singleton closed point is such a set.
  rw [FiniteClosedAwayFromPoint.isClosed_iff (z := (none : Option ℕ))]
  right
  refine ⟨Set.finite_singleton _, ?_⟩
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
  simpa [hx, witnessGenericPoint, witnessClosedPoint]

/-- Helper for Remark 17.10.3: the generic point is not in the closure of any closed point. -/
private theorem witnessGenericPoint_not_mem_closure_closedPoint (n : ℕ) :
    witnessGenericPoint ∉ closure ({witnessClosedPoint n} : Set witnessSpace) := by
  -- Proof comment: the closure of a closed-point singleton stays equal to that singleton.
  rw [witnessClosedPoint_singleton_isClosed n |>.closure_eq]
  simp [witnessGenericPoint, witnessClosedPoint]

/-- Helper for Remark 17.10.3: the identity on a free sheaf is the cokernel of the zero relation
map. -/
private theorem freePresentation_zero_comp_id
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    (I : Type u) :
    (0 :
      SheafOfModules.free.{u} (ULift.{u} (Fin 0)) ⟶
        (SheafOfModules.free.{u} I : SheafOfModules R)) ≫
      𝟙 (SheafOfModules.free.{u} I : SheafOfModules R) = 0 := by
  -- Proof comment: the zero relation map obviously composes trivially with the identity.
  simp

/-- Helper for Remark 17.10.3: the identity on a free sheaf is a cokernel presentation. -/
private noncomputable def freePresentation_id_isColimit
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    (I : Type u) :
    IsColimit
      (CokernelCofork.ofπ
        (𝟙 (SheafOfModules.free.{u} I : SheafOfModules R))
        (freePresentation_zero_comp_id (R := R) I)) := by
  -- Proof comment: the identity realizes a free sheaf as the cokernel of the zero map.
  exact
    CokernelCofork.IsColimit.ofId
      (0 :
        SheafOfModules.free.{u} (ULift.{u} (Fin 0)) ⟶
          (SheafOfModules.free.{u} I : SheafOfModules R))
      rfl

/-- Helper for Remark 17.10.3: every free sheaf has its tautological global presentation. -/
private noncomputable def freePresentation
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    (I : Type u) :
    (SheafOfModules.free.{u} I : SheafOfModules R).Presentation :=
  SheafOfModules.presentationOfIsCokernelFree
    (0 :
      SheafOfModules.free.{u} (ULift.{u} (Fin 0)) ⟶
        (SheafOfModules.free.{u} I : SheafOfModules R))
    (𝟙 (SheafOfModules.free.{u} I : SheafOfModules R))
    (freePresentation_zero_comp_id (R := R) I)
    (freePresentation_id_isColimit (R := R) I)

/-- Helper for Remark 17.10.3: the unit sheaf is the free sheaf on a singleton basis. -/
private noncomputable def unitIsoFreeSingleton
    {C : Type u} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    {ι : Type u} [Unique ι] :
    SheafOfModules.unit R ≅ (SheafOfModules.free.{u} ι : SheafOfModules R) := by
  let c : Cofan (fun _ : ι ↦ SheafOfModules.unit R) :=
    Cofan.mk (P := SheafOfModules.unit R) (fun _ ↦ 𝟙 _)
  let hc : IsColimit c :=
    mkCofanColimit c
      (fun t ↦ t.inj (default : ι))
      (fun t j ↦ by simpa [c, Subsingleton.elim j (default : ι)])
      (fun t m hm ↦ by simpa using hm (default : ι))
  -- Proof comment: both cocones exhibit the coproduct of a singleton family of copies of the unit
  -- sheaf.
  exact IsColimit.coconePointUniqueUpToIso hc (SheafOfModules.isColimitFreeCofan (R := R) ι)

/-- Helper for Remark 17.10.3: the unit module on any ringed space is quasi-coherent. -/
private theorem ringedSpaceModuleUnit_isQuasicoherent
    (X : RingedSpace.{u}) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := by
  let topOpen : Opens X := ⟨Set.univ, isOpen_univ⟩
  let q :
      (SheafOfModules.unit X.ringCatSheaf : X.Modules).QuasicoherentData :=
    { I := PUnit
      X := fun _ ↦ topOpen
      coversTop := by
        intro U x hx
        -- Proof comment: the singleton cover `⊤` refines every neighborhood.
        refine ⟨U, homOfLE le_rfl, ?_, ?_⟩
        · exact ⟨PUnit.unit, ⟨homOfLE (by
            intro y hy
            trivial)⟩⟩
        · exact hx
      presentation := fun _ ↦
        let e :
            ((SheafOfModules.unit X.ringCatSheaf : X.Modules).over topOpen) ≅
              (SheafOfModules.free.{u} PUnit :
                SheafOfModules (X.ringCatSheaf.over topOpen)) :=
          unitIsoFreeSingleton (R := X.ringCatSheaf.over topOpen)
        -- Proof comment: transport the standard free presentation across the singleton-basis iso.
        (freePresentation (R := X.ringCatSheaf.over topOpen) PUnit).of_isIso e.inv }
  -- Proof comment: one global free presentation on `⊤` already witnesses quasi-coherence.
  exact q.isQuasicoherent

/-- Helper for Remark 17.10.3: the coproduct of a constant family of unit modules is the
corresponding free module sheaf. -/
private noncomputable def coproductUnitsIsoFree
    (X : RingedSpace.{u}) (I : Type u) :
    (∐ fun _ : I ↦ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) ≅
      (SheafOfModules.free.{u} I : X.Modules) := by
  let F : Discrete I ⥤ X.Modules :=
    Discrete.functor (fun _ : I ↦ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
  let hc :
      IsColimit (SheafOfModules.freeCofan (R := X.ringCatSheaf) I) :=
    SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I
  -- Proof comment: the canonical coproduct object and the free-sheaf cofan are colimits of the
  -- same discrete diagram.
  exact (hc.coconePointUniqueUpToIso (colimit.isColimit F)).symm

/-- Helper for Remark 17.10.3: the quotient map defining the glued real line is open. -/
private theorem gluedRealLine_isOpenMap_quotientMk :
    IsOpenMap (Quotient.mk'' : ℕ × ℝ → gluedRealLine) := by
  intro s hs
  let q : ℕ × ℝ → gluedRealLine := Quotient.mk''
  let A : Set ℝ := {x | ∃ n : ℕ, (n, x) ∈ s}
  have hA : IsOpen A := by
    -- Proof comment: the set of real coordinates that occur in the open set `s` is the union of
    -- its open branchwise slices.
    change IsOpen (⋃ n : ℕ, {x : ℝ | (n, x) ∈ s})
    refine isOpen_iUnion fun n ↦ ?_
    simpa [Set.preimage, Prod.mk.eta] using
      hs.preimage (continuous_const.prod_mk continuous_id)
  have hpreimage :
      q ⁻¹' (q '' s) = s ∪ Prod.snd ⁻¹' (A \ ({0} : Set ℝ)) := by
    ext p
    constructor
    · intro hp
      rcases hp with ⟨y, hy, hqy⟩
      have hyrel : gluedRealLineSetoid.r y p := Quotient.eq''.mp hqy
      rcases hyrel with ⟨hcoord, horigin⟩
      by_cases hp0 : p.2 = 0
      · -- Proof comment: at the origin the branch index is remembered, so quotient equality forces
        -- the representative itself to lie in `s`.
        have hy0 : y.2 = 0 := by simpa [hcoord] using hp0
        have hbranch : y.1 = p.1 := horigin hy0
        left
        cases y
        cases p
        simp_all
      · -- Proof comment: away from the origin the quotient forgets the branch index, so only the
        -- real coordinate matters.
        right
        refine ⟨?_, by simpa [Set.mem_singleton_iff] using hp0⟩
        refine ⟨y.1, ?_⟩
        simpa [A, hcoord] using hy
    · intro hp
      rcases hp with hp | hp
      · exact ⟨p, hp, rfl⟩
      · rcases hp with ⟨⟨n, hn⟩, hp0⟩
        have hp0' : p.2 ≠ 0 := by
          simpa [Set.mem_singleton_iff] using hp0
        refine ⟨(n, p.2), hn, ?_⟩
        apply Quotient.eq''.2
        refine ⟨rfl, ?_⟩
        intro hzero
        exact (hp0' hzero).elim
  have hopenPreimage : IsOpen (q ⁻¹' (q '' s)) := by
    rw [hpreimage]
    refine hs.union ?_
    -- Proof comment: after replacing the quotient saturation by a preimage along `Prod.snd`, the
    -- remaining set is open because `A \ {0}` is an open subset of `ℝ`.
    have hA0 : IsOpen (A \ ({0} : Set ℝ)) := hA.diff isClosed_singleton
    simpa [A, Set.preimage] using hA0.preimage continuous_snd
  exact (((isQuotientMap_quotient_mk' :
      IsQuotientMap (Quotient.mk'' : ℕ × ℝ → gluedRealLine))).1.isOpen_preimage).1
    hopenPreimage

/-- Helper for Remark 17.10.3: the glued real line inherits local compactness from the open
quotient map `(ℕ × ℝ) → gluedRealLine`. -/
private instance gluedRealLine_locallyCompactSpace : LocallyCompactSpace gluedRealLine := by
  -- Proof comment: products of locally compact spaces are locally compact, and open quotient maps
  -- preserve local compactness.
  let q : ℕ × ℝ → gluedRealLine := Quotient.mk''
  let hq : IsOpenQuotientMap q :=
    IsOpenQuotientMap.of_isOpenMap_isQuotientMap
      gluedRealLine_isOpenMap_quotientMk isQuotientMap_quotient_mk'
  exact hq.locallyCompactSpace

/-- Helper for Remark 17.10.3: the glued origin has a neighborhood basis of compact subsets. -/
private theorem gluedRealLinePoint_hasCompactNeighborhoodBasis :
    (𝓝 gluedRealLinePoint).HasBasis
      (fun K : Set gluedRealLineRingedSpace ↦ K ∈ 𝓝 gluedRealLinePoint ∧ IsCompact K) id := by
  -- Proof comment: once local compactness is available on the glued real line, the standard
  -- compact-neighborhood basis theorem applies directly at the chosen point.
  simpa using compact_basis_nhds gluedRealLinePoint

/-- Helper for Remark 17.10.3: the free sheaf from Example 17.10.9 on the glued real line is not
quasi-coherent. -/
private theorem gluedRealLineFree_not_isQuasicoherent :
    ¬ ((SheafOfModules.free.{u} (ULift (ℕ × ℕ)) :
      gluedRealLineRingedSpace.Modules).IsQuasicoherent) := by
  obtain ⟨φ, hφ⟩ :=
    gluedRealLine_exists_free_module_sheaf_morphism_not_locally_induced_by_globalSectionsModuleMap
  intro hfree
  letI :
      (SheafOfModules.free.{u} (ULift (ℕ × ℕ)) :
        gluedRealLineRingedSpace.Modules).IsQuasicoherent := hfree
  have hloc : LocallyIsInducedByGlobalSectionsModuleMapAt gluedRealLinePoint φ := by
    -- Route correction: the public/private bridge now lives upstream in Example 17.10.9, where
    -- the restricted free-sheaf constructor is visible.
    exact
      gluedRealLine_locallyIsInducedByGlobalSectionsModuleMapAt_of_isQuasicoherent_freeTarget φ
  -- Proof comment: the bad morphism from Example 17.10.9 contradicts any local-induction witness.
  exact hφ hloc

/-- Helper for Remark 17.10.3: the coproduct of the constant unit family on the glued real line is
not quasi-coherent. -/
private theorem coproductUnitFamily_not_isQuasicoherent :
    ¬ (∐ fun _ : ULift (ℕ × ℕ) ↦
        (SheafOfModules.unit gluedRealLineRingedSpace.ringCatSheaf :
          gluedRealLineRingedSpace.Modules)).IsQuasicoherent := by
  intro hcoprod
  let e :
      (∐ fun _ : ULift (ℕ × ℕ) ↦
          (SheafOfModules.unit gluedRealLineRingedSpace.ringCatSheaf :
            gluedRealLineRingedSpace.Modules)) ≅
        (SheafOfModules.free.{u} (ULift (ℕ × ℕ)) :
          gluedRealLineRingedSpace.Modules) :=
    coproductUnitsIsoFree gluedRealLineRingedSpace (ULift (ℕ × ℕ))
  letI :
      (∐ fun _ : ULift (ℕ × ℕ) ↦
          (SheafOfModules.unit gluedRealLineRingedSpace.ringCatSheaf :
            gluedRealLineRingedSpace.Modules)).IsQuasicoherent := hcoprod
  -- Proof comment: transport quasi-coherence across the canonical coproduct/free comparison.
  exact gluedRealLineFree_not_isQuasicoherent
    (SheafOfModules.isQuasicoherent_of_iso e)

/- Domain-style sampling for Remark 17.10.3:
- primary domain: quasi-coherent `\mathcal O_X`-modules on ringed spaces and arbitrary direct
  sums/coproducts;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.isQuasicoherent`,
  `ringedSpaceModule_sigmaComparison_isIso_of_isCompact`;
- best owner abstraction: the ambient owner is `(RingedSpace.Modules X)` with the owner predicate
  `SheafOfModules.IsQuasicoherent`; the direct sum from the source is the categorical coproduct
  `∐ ℱ`;
- primitive data: a ringed space `X`, an index type `I`, and a family
  `ℱ : I → RingedSpace.Modules X`;
- derived API: the source-facing existence statement that even when every `ℱ i` is
  quasi-coherent, the coproduct `∐ ℱ` need not be.

Layer triage:
- `source-facing`: the warning that infinite direct sums of quasi-coherent modules need not remain
  quasi-coherent;
- `core/canonical`: `RingedSpace.Modules` and `SheafOfModules.IsQuasicoherent`;
- `bridge/view`: the categorical coproduct `∐ ℱ`, viewed as the direct sum from the source.
-/

-- Proof sketch: the source gives this as a warning rather than a construction. The canonical Lean
-- shape is therefore an existence statement over the owner category `(RingedSpace.Modules X)` and
-- its coproducts.
/-- Remark 17.10.3: in general, an infinite direct sum of quasi-coherent
`\mathcal O_X`-modules need not be quasi-coherent. -/
theorem exists_infinite_directSum_of_quasicoherent_not_quasicoherent :
    ∃ (X : RingedSpace.{u}) (I : Type u) (_ : Infinite I) (ℱ : I → RingedSpace.Modules X),
      (∀ i, (ℱ i).IsQuasicoherent) ∧ ¬ (∐ ℱ).IsQuasicoherent := by
  classical
  -- Route correction: the earlier closed-point skyscraper witness appears to need a false
  -- quasi-coherence claim, so switch to the glued-real-line free-sheaf counterexample from
  -- Example 17.10.9.
  let X : RingedSpace.{u} := gluedRealLineRingedSpace
  let I : Type u := ULift (ℕ × ℕ)
  let ℱ : I → X.Modules := fun _ ↦ (SheafOfModules.unit X.ringCatSheaf : X.Modules)
  refine ⟨X, I, inferInstance, ℱ, ?_, ?_⟩
  · intro i
    -- Proof comment: every summand is the unit module, which is quasi-coherent by the singleton
    -- free presentation above.
    exact ringedSpaceModuleUnit_isQuasicoherent X
  · -- Proof comment: the negative example is now isolated in the glued-real-line free sheaf, and
    -- the direct sum statement follows by the canonical coproduct/free comparison.
    exact coproductUnitFamily_not_isQuasicoherent

end AlgebraicGeometry
