import Mathlib
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_60_3
import StacksProject_2024.Chap15.Lemma_15_76_4
import StacksProject_2024.Chap15.Lemma_15_88_5_TowerBridge

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CommRingCat
open Opposite
open DerivedModuleTower
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {F : ℕᵒᵖ ⥤ CommRingCat.{u}}

section

local notation "DModA" => DerivedCategory (ModuleCat (inverseLimitRing F))

namespace DerivedModuleTower

/-- A stagewise property on a derived module tower either holds at every stage, or it holds at one
stage after which all transition kernels are nilpotent. -/
def StagewiseOrEventuallyNilpotent
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (P : ℕ → Prop) : Prop :=
  (∀ n : ℕ, P n) ∨
    ∃ n₀ : ℕ, P n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → IsNilpotent (RingHom.ker (stageTransitionRingHom F n))

/-- Monotonicity of the stagewise/eventually-nilpotent hypothesis with respect to the stagewise
property. -/
theorem stagewiseOrEventuallyNilpotent_mono
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (P Q : ℕ → Prop) (hPQ : ∀ n : ℕ, P n → Q n)
    (hP : StagewiseOrEventuallyNilpotent F P) :
    StagewiseOrEventuallyNilpotent F Q := by
  rcases hP with hP | ⟨n₀, hPn₀, hnil⟩
  · exact Or.inl (fun n ↦ hPQ n (hP n))
  · exact Or.inr ⟨n₀, hPQ n₀ hPn₀, hnil⟩

/-- The canonical stagewise derived base-change comparison induced by the tower map
`T.stepMap n : K_{n + 1} ⟶ K_n` viewed over `A_{n + 1}`. -/
abbrev stageDerivedBaseChangeComparison
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    stageDerivedBaseChange F T n ⟶ T.obj n :=
  ((derivedTensorWithAlgebraAdjunction).homEquiv (T.obj (n + 1)) (T.obj n)).symm (T.stepMap n)

/-- The derived-limit base-change comparison attached to a chosen stage comparison
`c : K ⟶ K_n|_A`. -/
abbrev inverseLimitBaseChangeComparison
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F))
    (K : DModA) (n : ℕ) (c : K ⟶ (stageRestrictionToLimitTower F T).obj (op n)) :
    inverseLimitBaseChange F K n ⟶ T.obj n :=
  ((derivedTensorWithAlgebraAdjunction).homEquiv K (T.obj n)).symm c

end DerivedModuleTower

namespace CategoryTheory.SequentialProObjectMorphismRep

section

variable {C : Type*} [Category C] {X : SequentialInverseSystem C}

/-- Helper for Lemma 15.98.1: the common refinement of the identity representative and the
double-shift representative lands at stage `c + (c + n)`. -/
private theorem self_shift_refinement_le (n c : ℕ) :
    n ≤ c + (c + n) := by
  -- Proof comment: first shift from `n` to `c + n`, then shift once more by `c`.
  exact (Nat.le_add_left n c).trans (Nat.le_add_left (c + n) c)

/-- Helper for Lemma 15.98.1: a shift representative is a pro-isomorphism when its self-composite
already agrees with the canonical transition map after passing to the common refinement
`n ↦ c + (c + n)`. -/
theorem ofShiftNatTrans_isProIsomorphism_of_self_composite_transition
    (c : ℕ) (α : SequentialInverseSystem.shift X c ⟶ X)
    (hα : ∀ n : ℕ,
      α.app (op (c + n)) ≫ α.app (op n) =
        SequentialInverseSystem.transitionMap X (self_shift_refinement_le n c)) :
    (ofShiftNatTrans c α).IsProIsomorphism := by
  let shiftComp := compRep (ofShiftNatTrans c α) (ofShiftNatTrans c α)
  have hEq : Equivalent shiftComp (idRep X) := by
    -- Proof comment: both representatives refine to the common stage `c + (c + n)`, where the
    -- self-composite is exactly the ordinary transition map by hypothesis.
    refine ⟨shiftComp.reindex, fun n ↦ le_rfl, fun n ↦ self_shift_refinement_le n c, ?_⟩
    intro n
    simpa [shiftComp, SequentialProObjectMorphismRep.compRep,
      SequentialProObjectMorphismRep.ofShiftNatTrans, SequentialProObjectMorphismRep.idRep,
      SequentialInverseSystem.transitionMap] using hα n
  -- Proof comment: the same shift representative serves as a two-sided inverse up to
  -- representative equivalence.
  exact ⟨ofShiftNatTrans c α, hEq, hEq⟩

end

end CategoryTheory.SequentialProObjectMorphismRep

namespace CategoryTheory.SequentialProObjectMorphismRep

section

variable {C : Type*} [Category C] {X Y : ℕᵒᵖ ⥤ C}

/-- Helper for Lemma 15.98.1: a natural isomorphism of sequential inverse systems is already a
pro-isomorphism in the Chapter 4 representative calculus. -/
theorem natIso_isProIsomorphism_ofNatTrans
    (e : X ≅ Y) :
    (SequentialProObjectMorphismRep.ofNatTrans e.hom).IsProIsomorphism := by
  -- Proof comment: use the inverse natural isomorphism as the reverse representative; with
  -- identity reindexing on both sides, the common-refinement equations reduce to the component
  -- identities of `e`.
  refine ⟨SequentialProObjectMorphismRep.ofNatTrans e.inv, ?_, ?_⟩
  · refine ⟨OrderHom.id, fun n ↦ le_rfl, fun n ↦ le_rfl, ?_⟩
    intro n
    change
      X.map (homOfLE (le_rfl : n ≤ n)).op ≫
          (e.hom.app (Opposite.op n) ≫ e.inv.app (Opposite.op n)) =
        X.map (homOfLE (le_rfl : n ≤ n)).op ≫ 𝟙 (X.obj (Opposite.op n))
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ X.map (homOfLE (le_rfl : n ≤ n)).op ≫ t)
        (e.hom_inv_id_app (Opposite.op n))
  · refine ⟨OrderHom.id, fun n ↦ le_rfl, fun n ↦ le_rfl, ?_⟩
    intro n
    change
      Y.map (homOfLE (le_rfl : n ≤ n)).op ≫
          (e.inv.app (Opposite.op n) ≫ e.hom.app (Opposite.op n)) =
        Y.map (homOfLE (le_rfl : n ≤ n)).op ≫ 𝟙 (Y.obj (Opposite.op n))
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ Y.map (homOfLE (le_rfl : n ≤ n)).op ≫ t)
        (e.inv_hom_id_app (Opposite.op n))

/-- Helper for Lemma 15.98.1: a pro-isomorphism representative induces an isomorphism of the
associated sequential pro-objects. -/
theorem toProObjectHom_isIso_of_isProIsomorphism
    (a : SequentialProObjectMorphismRep X Y)
    (ha : a.IsProIsomorphism) :
    IsIso a.toProObjectHom := by
  -- Proof comment: evaluate on every test object and use the Chapter 4 bridge from
  -- pro-isomorphisms to bijectivity of the represented Hom-colimit map.
  letI : ∀ Z : C, IsIso (a.toProObjectHom.app Z) := fun Z ↦
    (CategoryTheory.isIso_iff_bijective (a.toProObjectHom.app Z)).2
      (SequentialProObjectMorphismRep.isProIsomorphism_toProObjectHom_app_bijective ha Z)
  exact NatIso.isIso_of_isIso_app a.toProObjectHom

end

end CategoryTheory.SequentialProObjectMorphismRep

/- Domain-style sampling for Lemma 15.98.1:
- primary domain: derived inverse limits for towers of derived module objects over a sequential
  inverse system of commutative rings, together with pseudo-coherence and derived base change;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `CategoryTheory.IsDerivedLimit`,
  `DerivedModuleTower.stageRestrictionToLimitTower`,
  `DerivedModuleTower.stageDerivedBaseChangeComparison`,
  `CategoryTheory.HasMilnorTriangle.WithMap`;
- best owner abstraction: the chapter bridge owner
  `DerivedModuleTower (stageRing F) (stageTransitionRingHom F)` together with its canonical
  fixed-base inverse system `DerivedModuleTower.stageRestrictionToLimitTower T`, the canonical
  stagewise adjoint comparison
  `DerivedModuleTower.stageDerivedBaseChangeComparison F T n`, and the canonical
  derived-category owners `K.IsPseudoCoherent`, `CategoryTheory.IsDerivedLimit`, and the
  chosen-Milnor-map bridge `CategoryTheory.HasMilnorTriangle.WithMap`;
- primitive vs. derived:
  primitive data are the tower `T`, the chosen derived limit `K` of the canonical fixed-base
  tower `stageRestrictionToLimitTower T`, and the stagewise pseudo-coherence / nilpotence
  hypotheses;
  derived API is the pseudo-coherence conclusion for `K` and the inverse-limit base-change
  comparison induced by a derived-limit stage map.

Source/core/bridge triage:
- `source-facing`: the pseudo-coherence and base-change conclusion for the chosen derived limit;
- `core/canonical`: `K.IsPseudoCoherent` and `CategoryTheory.IsDerivedLimit`;
- `bridge/view`: `stageRestrictionToLimitTower`, `stageDerivedBaseChangeComparison`, and
  `inverseLimitBaseChangeComparison`, together with `HasMilnorTriangle.WithMap`. -/

-- Proof sketch: represent the tower by bounded-above finite-free complexes compatible under
-- reduction along the surjective transition maps, form the termwise inverse limit complex over
-- `A = lim A_n`, and use the Milnor description of `R lim` together with stagewise derived
-- tensor compatibility to identify pseudo-coherence of the limit object.
/-
Lemma 15.98.1: let `A = \varprojlim_n A_n` be a sequential inverse limit of commutative
rings, let `T` encode the compatible system `K_n ∈ D(A_n)`, and let `K` be a chosen derived
limit of the canonical fixed-base tower `stageRestrictionToLimitTower T` in `D(A)`. Assume the
transition maps `A_{n + 1} → A_n` are surjective with locally nilpotent kernels, that either every
`K_n` is pseudo-coherent or some stage `K_{n₀}` is pseudo-coherent and all later kernels are
nilpotent, and that the canonical stagewise derived base-change comparisons
`K_{n + 1} \otimes_{A_{n + 1}}^{\mathbf L} A_n → K_n` induced by `T.stepMap` are isomorphisms.
Then `K` is pseudo-coherent over `A`.
-/
variable
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F))
    (K : DModA)
    (h_surj : ∀ n : ℕ, Function.Surjective (stageTransitionRingHom F n))
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (stageTransitionRingHom F n) ≤ nilradical (stageRing F (n + 1)))
    (hpc : StagewiseOrEventuallyNilpotent F (fun n ↦ (T.obj n).IsPseudoCoherent))
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n))

/-- Helper for Lemma 15.98.1: pseudo-coherence is invariant under isomorphism in the relevant
derived category. -/
lemma isPseudoCoherent_of_iso
    {R : Type u} [CommRing R]
    {L M : DerivedCategory (ModuleCat R)} (e : L ≅ M)
    (hL : L.IsPseudoCoherent) :
    M.IsPseudoCoherent := by
  rcases hL with ⟨E, hEbounded, hEfree, α, hα⟩
  -- Proof comment: keep the same bounded-above finite-free model and postcompose its comparison
  -- with the chosen isomorphism.
  refine ⟨E, hEbounded, hEfree, α ≫ e.hom, ?_⟩
  simpa using (show IsIso (α ≫ e.hom) by infer_instance)

/-- Helper for Lemma 15.98.1: pseudo-coherence ascends across a surjective nilpotent thickening
once the derived base change is identified with a pseudo-coherent object. -/
lemma pseudoCoherent_of_surjective_of_nilpotent_baseChange_iso
    {R' R : Type u} [CommRing R'] [CommRing R] [Algebra R' R]
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    {K' : DerivedCategory (ModuleCat R')} {K : DerivedCategory (ModuleCat R)}
    (e : (K' ⊗[R']^L[R]) ≅ K)
    (hK : K.IsPseudoCoherent) :
    K'.IsPseudoCoherent := by
  -- Proof comment: first move pseudo-coherence across the chosen derived base-change isomorphism,
  -- then invoke the canonical nilpotent-thickening equivalence from Lemma `15.76.4`.
  have hBase : (K' ⊗[R']^L[R]).IsPseudoCoherent :=
    isPseudoCoherent_of_iso e.symm hK
  exact
    (CategoryTheory.isPseudoCoherent_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
      (R' := R') (R := R) hsurj hker K').mp hBase

/-- Helper for Lemma 15.98.1: the eventual branch of the hypothesis provides a stage `c` after
which every stage is pseudo-coherent. -/
lemma eventual_pseudoCoherent_tail
    (h_surj : ∀ n : ℕ, Function.Surjective (stageTransitionRingHom F n))
    (hpc : StagewiseOrEventuallyNilpotent F (fun n ↦ (T.obj n).IsPseudoCoherent))
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n)) :
    ∃ c : ℕ, ∀ n : ℕ, (T.obj (c + n)).IsPseudoCoherent := by
  rcases hpc with hpc_all | ⟨n₀, hn₀, hnil⟩
  · refine ⟨0, ?_⟩
    intro n
    simpa [Nat.zero_add] using hpc_all (0 + n)
  · refine ⟨n₀, ?_⟩
    intro n
    induction n with
    | zero =>
        simpa using hn₀
    | succ n ih =>
        -- Proof comment: the stage `(n₀ + n + 1)` base changes to the already pseudo-coherent
        -- stage `(n₀ + n)`, so pseudo-coherence ascends through the nilpotent surjection.
        have hker :
            IsNilpotent (RingHom.ker (stageTransitionRingHom F (n₀ + n))) :=
          hnil (n₀ + n) (Nat.le_add_right n₀ n)
        letI :
            IsIso (stageDerivedBaseChangeComparison (F := F) (T := T) (n₀ + n)) :=
          hstageBaseChange (n₀ + n)
        let e :
            stageDerivedBaseChange (F := F) T (n₀ + n) ≅ T.obj (n₀ + n) :=
          asIso (stageDerivedBaseChangeComparison (F := F) (T := T) (n₀ + n))
        exact
          pseudoCoherent_of_surjective_of_nilpotent_baseChange_iso
            (hsurj := h_surj (n₀ + n))
            (hker := hker)
            (e := e)
            ih

/-- Helper for Lemma 15.98.1: an isomorphism of fixed-base towers induces the canonical product
isomorphism on their stage families. -/
private noncomputable def tower_product_iso
    {Ksys Lsys : SequentialInverseSystem DModA}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (∏ᶜ inverseSystemFamily Ksys) ≅ ∏ᶜ inverseSystemFamily Lsys := by
  -- Proof comment: transport the discrete product diagram along the stagewise natural
  -- isomorphism of towers.
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (op n.as)
  exact HasLimit.isoOfNatIso eFamily

/-- Helper for Lemma 15.98.1: the product isomorphism attached to a tower isomorphism preserves
the projection to each stage. -/
private theorem tower_product_iso_hom_comp_π
    {Ksys Lsys : SequentialInverseSystem DModA}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) (n : ℕ) :
    (tower_product_iso e).hom ≫ Pi.π (inverseSystemFamily Lsys) n =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (op n)).hom := by
  -- Proof comment: this is the defining projection formula for `HasLimit.isoOfNatIso`.
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun m : Discrete ℕ ↦ e.app (op m.as)
  simpa [tower_product_iso, eFamily] using
    limMap_π (α := eFamily.hom) (j := Discrete.mk n)

/-- Helper for Lemma 15.98.1: the product isomorphism attached to a tower isomorphism intertwines
the Milnor difference maps. -/
private theorem tower_product_iso_hom_comm_difference
    {Ksys Lsys : SequentialInverseSystem DModA}
    [HasProduct (inverseSystemFamily Ksys)] [HasProduct (inverseSystemFamily Lsys)]
    (e : Ksys ≅ Lsys) :
    (tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys =
      derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom := by
  apply Pi.hom_ext
  intro n
  -- Proof comment: compare both Milnor endomorphisms after the `n`th projection and reduce to
  -- naturality of the stagewise comparison `e`.
  calc
    ((tower_product_iso e).hom ≫ derivedLimitDifferenceMap Lsys) ≫
        Pi.π (inverseSystemFamily Lsys) n =
      (tower_product_iso e).hom ≫
        (Pi.π (inverseSystemFamily Lsys) n -
          Pi.π (inverseSystemFamily Lsys) (n + 1) ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Category.assoc, derivedLimitDifferenceMap_comp_π]
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          (e.app (Opposite.op (n + 1))).hom ≫
            Lsys.transitionMap (Nat.le_succ n)) := by
          rw [Preadditive.comp_sub]
          rw [tower_product_iso_hom_comp_π]
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ t ≫ Lsys.transitionMap (Nat.le_succ n))
              (tower_product_iso_hom_comp_π e (n + 1))
    _ =
      Pi.π (inverseSystemFamily Ksys) n ≫ (e.app (Opposite.op n)).hom -
        (Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n) ≫
            (e.app (Opposite.op n)).hom) := by
          -- Naturality identifies the successor-transition contribution.
          congr 1
          simpa [Category.assoc] using
            congrArg
              (fun t ↦ Pi.π (inverseSystemFamily Ksys) (n + 1) ≫ t)
              (e.hom.naturality ((homOfLE (Nat.le_succ n)).op)).symm
    _ =
      (Pi.π (inverseSystemFamily Ksys) n -
        Pi.π (inverseSystemFamily Ksys) (n + 1) ≫
          Ksys.transitionMap (Nat.le_succ n)) ≫
        (e.app (Opposite.op n)).hom := by
          rw [Preadditive.sub_comp]
          simp [Category.assoc]
    _ =
      derivedLimitDifferenceMap Ksys ≫ Pi.π (inverseSystemFamily Ksys) n ≫
        (e.app (Opposite.op n)).hom := by
          rw [← derivedLimitDifferenceMap_comp_π_assoc]
    _ =
      ((derivedLimitDifferenceMap Ksys ≫ (tower_product_iso e).hom) ≫
        Pi.π (inverseSystemFamily Lsys) n) := by
          rw [Category.assoc, ← tower_product_iso_hom_comp_π, ← Category.assoc]

/-- Helper for Lemma 15.98.1: a derived-limit witness transports across an isomorphism of towers
when the limiting object is kept fixed. -/
private theorem isDerivedLimit_of_tower_iso
    {Ksys Lsys : SequentialInverseSystem DModA} {L : DModA}
    (e : Ksys ≅ Lsys)
    (hL : IsDerivedLimit Ksys L) :
    IsDerivedLimit Lsys L := by
  rcases hL with ⟨hP, hMilnor⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  let eFamily :
      Discrete.functor (inverseSystemFamily Ksys) ≅
        Discrete.functor (inverseSystemFamily Lsys) :=
    Discrete.natIso fun n : Discrete ℕ ↦ e.app (op n.as)
  let hQ : HasProduct (inverseSystemFamily Lsys) := by
    exact hasLimit_of_iso eFamily
  letI : HasProduct (inverseSystemFamily Lsys) := hQ
  rcases hMilnor with ⟨ι, δ, hδ⟩
  let Tmilnor : Triangle DModA :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let Ttransported : Triangle DModA :=
    Triangle.mk (ι ≫ (tower_product_iso e).hom) (derivedLimitDifferenceMap Lsys)
      ((tower_product_iso e).inv ≫ δ)
  have hIso : Tmilnor ≅ Ttransported := by
    -- Proof comment: repackage the original Milnor triangle through the product comparison
    -- isomorphism.
    refine Triangle.isoMk _ _ (Iso.refl _) (tower_product_iso e) (tower_product_iso e) ?_ ?_ ?_
    · simp [Tmilnor, Ttransported]
    · simpa [Tmilnor, Ttransported] using (tower_product_iso_hom_comm_difference e).symm
    · simp [Tmilnor, Ttransported]
  have hTtransported : Ttransported ∈ distTriang DModA := by
    -- Proof comment: distinguished triangles are stable under isomorphism.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact ⟨hQ, ⟨ι ≫ (tower_product_iso e).hom, (tower_product_iso e).inv ≫ δ, hTtransported⟩⟩

/-- Helper for Lemma 15.98.1: once a Milnor triangle is fixed for a tower, the limiting object
may be replaced by any isomorphic object. -/
private theorem isDerivedLimit_of_object_iso
    {Ksys : SequentialInverseSystem DModA} {L M : DModA}
    (e : L ≅ M)
    (hL : IsDerivedLimit Ksys L) :
    IsDerivedLimit Ksys M := by
  rcases hL with ⟨hP, hMilnor⟩
  letI : HasProduct (inverseSystemFamily Ksys) := hP
  rcases hMilnor with ⟨ι, δ, hδ⟩
  let Tmilnor : Triangle DModA :=
    Triangle.mk ι (derivedLimitDifferenceMap Ksys) δ
  let Ttransported : Triangle DModA :=
    Triangle.mk (e.inv ≫ ι) (derivedLimitDifferenceMap Ksys)
      (δ ≫ (shiftFunctor DModA (1 : ℤ)).map e.hom)
  have hIso : Tmilnor ≅ Ttransported := by
    -- Proof comment: only the first vertex changes, so the comparison triangle is induced by the
    -- chosen isomorphism of limiting objects.
    refine Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp [Tmilnor, Ttransported]
    · simp [Tmilnor, Ttransported]
    · simp [Tmilnor, Ttransported]
  have hTtransported : Ttransported ∈ distTriang DModA := by
    -- Proof comment: distinguished triangles are stable under isomorphism, so the transported
    -- Milnor triangle remains distinguished.
    exact isomorphic_distinguished _ hδ _ hIso.symm
  exact
    ⟨hP, ⟨e.inv ≫ ι, δ ≫ (shiftFunctor DModA (1 : ℤ)).map e.hom, hTtransported⟩⟩

/-- Helper for Lemma 15.98.1: a chosen Milnor product map presents its source as a derived limit
of the fixed-base tower. -/
lemma isDerivedLimit_of_withMap
    [HasProduct (inverseSystemFamily (stageRestrictionToLimitTower F T))]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily (stageRestrictionToLimitTower F T)}
    (hι : HasMilnorTriangle.WithMap (stageRestrictionToLimitTower F T) ι) :
    IsDerivedLimit (stageRestrictionToLimitTower F T) K :=
  -- Proof comment: `IsDerivedLimit` is exactly the packaged product plus Milnor-triangle data.
  ⟨inferInstance, hι.hasMilnorTriangle (stageRestrictionToLimitTower F T)⟩

/-- Helper for Lemma 15.98.1: the `n`th object of the reindexed tail of the fixed-base tower
starting at stage `c`. -/
private abbrev stageRestrictionToLimitTailObj
    (c n : ℕ) :
    DModA :=
  (stageRestrictionToLimitTower F T).obj (op (c + n))

/-- Helper for Lemma 15.98.1: the successor map in the explicit tail tower starting at stage
`c`. -/
private abbrev stageRestrictionToLimitTailStep
    (c n : ℕ) :
    stageRestrictionToLimitTailObj (F := F) (T := T) c (n + 1) ⟶
      stageRestrictionToLimitTailObj (F := F) (T := T) c n :=
  (stageRestrictionToLimitTower F T).map ((homOfLE (Nat.le_succ (c + n))).op)

/-- Helper for Lemma 15.98.1: the fixed-base tower obtained by forgetting the first `c` stages of
`stageRestrictionToLimitTower F T` and reindexing the remainder by `n ↦ c + n`. -/
private abbrev stageRestrictionToLimitTailTower
    (c : ℕ) :
    SequentialInverseSystem DModA :=
  Functor.ofOpSequence (stageRestrictionToLimitTailStep (F := F) (T := T) c)

/-- Helper for Lemma 15.98.1: after shifting the fixed-base tower by `c`, the successor map is
exactly the successor map of the explicit reindexed tail tower. -/
private theorem stageRestrictionToLimitTower_shift_tail_step
    (c n : ℕ) :
    (SequentialInverseSystem.shift (stageRestrictionToLimitTower F T) c).map
        (homOfLE (Nat.le_succ n)).op =
      (stageRestrictionToLimitTailTower (F := F) (T := T) c).map
        (homOfLE (Nat.le_succ n)).op := by
  -- Proof comment: both tower descriptions use the same object in degree `n`, and their
  -- successor maps are the same transition map of `stageRestrictionToLimitTower` after
  -- reindexing by `c`.
  change
    (stageRestrictionToLimitTower F T).map ((homOfLE (Nat.le_succ (c + n))).op) =
      (stageRestrictionToLimitTailTower (F := F) (T := T) c).map
        (homOfLE (Nat.le_succ n)).op
  simp [stageRestrictionToLimitTower, stageRestrictionToBaseTower,
    stageRestrictionToLimitTailTower, stageRestrictionToLimitTailStep,
    Functor.ofOpSequence_map_homOfLE_succ]

/-- Helper for Lemma 15.98.1: the common refinement used when comparing the identity
representative with the double-shift representative lands at stage `c + (c + n)`. -/
private theorem shiftComparison_le (n c : ℕ) :
    n ≤ c + (c + n) := by
  -- Proof comment: refine the identity representative first to stage `c + n`, then once more to
  -- stage `c + (c + n)`.
  exact (Nat.le_add_left n c).trans (Nat.le_add_left (c + n) c)

/-- Helper for Lemma 15.98.1: the canonical transition maps from the shifted tower back to the
original tower assemble into a natural transformation. -/
private noncomputable def stageRestrictionToLimitTower_shift_comparison
    (c : ℕ) :
    SequentialInverseSystem.shift (stageRestrictionToLimitTower F T) c ⟶
      stageRestrictionToLimitTower F T :=
  NatTrans.ofOpSequence
    (fun n ↦ (stageRestrictionToLimitTower F T).map ((homOfLE (Nat.le_add_left n c)).op))
    (fun n ↦ by
      -- Proof comment: both composites are the same transition morphism of
      -- `stageRestrictionToLimitTower F T`, written with two different parenthesizations of the
      -- unique morphism in `ℕᵒᵖ`.
      change
        (stageRestrictionToLimitTower F T).map
            ((homOfLE (Nat.add_le_add_left (Nat.le_succ n) c)).op) ≫
          (stageRestrictionToLimitTower F T).map ((homOfLE (Nat.le_add_left n c)).op) =
            (stageRestrictionToLimitTower F T).map
              ((homOfLE (Nat.le_add_left (n + 1) c)).op) ≫
              (stageRestrictionToLimitTower F T).map ((homOfLE (Nat.le_succ n)).op)
      rw [← Functor.map_comp, ← Functor.map_comp]
      subsingleton)

/-- Helper for Lemma 15.98.1: composing the shift comparison with itself is the ordinary
transition map from stage `c + (c + n)` down to stage `n`. -/
private theorem stageRestrictionToLimitTower_shift_comparison_comp
    (c n : ℕ) :
    ((stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c).app
        (op (c + n))) ≫
      (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c).app (op n) =
        SequentialInverseSystem.transitionMap (stageRestrictionToLimitTower F T)
          (shiftComparison_le n c) := by
  -- Proof comment: the two displayed transition maps are the same morphism in the index
  -- category, so functoriality identifies their images in the fixed-base tower.
  change
    (stageRestrictionToLimitTower F T).map ((homOfLE (Nat.le_add_left (c + n) c)).op) ≫
      (stageRestrictionToLimitTower F T).map ((homOfLE (Nat.le_add_left n c)).op) =
        (stageRestrictionToLimitTower F T).map ((homOfLE (shiftComparison_le n c)).op)
      rw [← Functor.map_comp]
      subsingleton

/-- Helper for Lemma 15.98.1: the `n`th component of the shift comparison is the obvious
transition map from stage `c + n` down to stage `n` in the original fixed-base tower. -/
private theorem stageRestrictionToLimitTower_shift_comparison_app
    (c n : ℕ) :
    (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c).app (op n) =
      SequentialInverseSystem.transitionMap (stageRestrictionToLimitTower F T)
        (Nat.le_add_left n c) := by
  -- Proof comment: the shift comparison was defined by these very transition maps.
  rfl

/-- Helper for Lemma 15.98.1: viewed on the shifted tower, the `c`-step transition is exactly the
`(c + n)`th component of the shift comparison. -/
private theorem stageRestrictionToLimitTower_shift_transition_app
    (c n : ℕ) :
    SequentialInverseSystem.transitionMap
        (SequentialInverseSystem.shift (stageRestrictionToLimitTower F T) c)
        (Nat.le_add_left n c) =
      (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c).app (op (c + n)) := by
  -- Proof comment: shifting only reindexes the original tower, so the relevant transition map is
  -- the same underlying morphism.
  rfl

/-- Helper for Lemma 15.98.1: the shift representative of the fixed-base tower is a
pro-isomorphism, expressing finite-prefix insensitivity of `R lim`. -/
private theorem stageRestrictionToLimitTower_shift_comparison_isProIsomorphism
    (c : ℕ) :
    (SequentialProObjectMorphismRep.ofShiftNatTrans c
      (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c)).IsProIsomorphism := by
  -- Proof comment: apply the generic self-shift criterion to the fixed-base tower; the required
  -- component identity is exactly `stageRestrictionToLimitTower_shift_comparison_comp`.
  exact
    SequentialProObjectMorphismRep.ofShiftNatTrans_isProIsomorphism_of_self_composite_transition
      (X := stageRestrictionToLimitTower F T) c
      (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c)
      (stageRestrictionToLimitTower_shift_comparison_comp (F := F) (T := T) c)

/-- Helper for Lemma 15.98.1: the owner-level pro-object morphism represented by the shift
comparison is an isomorphism. -/
private theorem stageRestrictionToLimitTower_shift_comparison_toProObjectHom_isIso
    (c : ℕ) :
    IsIso
      ((SequentialProObjectMorphismRep.ofShiftNatTrans c
        (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c)).toProObjectHom) := by
  -- Proof comment: the representative-level finite-prefix comparison is already a pro-isomorphism,
  -- so the associated owner-level pro-object morphism is invertible.
  exact
    SequentialProObjectMorphismRep.toProObjectHom_isIso_of_isProIsomorphism
      (a := SequentialProObjectMorphismRep.ofShiftNatTrans c
        (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c))
      (stageRestrictionToLimitTower_shift_comparison_isProIsomorphism (F := F) (T := T) c)

/-- Helper for Lemma 15.98.1: the literal natural transformation from the shifted fixed-base
tower to the original tower already gives a pro-isomorphism. -/
private theorem stageRestrictionToLimitTower_shift_comparison_ofNatTrans_isProIsomorphism
    (c : ℕ) :
    (SequentialProObjectMorphismRep.ofNatTrans
      (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c)).IsProIsomorphism := by
  let shifted : SequentialInverseSystem DModA :=
    SequentialInverseSystem.shift (stageRestrictionToLimitTower F T) c
  let backward :
      SequentialProObjectMorphismRep (stageRestrictionToLimitTower F T) shifted :=
    SequentialProObjectMorphismRep.ofShiftNatTrans c (𝟙 shifted)
  let forward :
      SequentialProObjectMorphismRep shifted (stageRestrictionToLimitTower F T) :=
    SequentialProObjectMorphismRep.ofNatTrans
      (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c)
  refine ⟨backward, ?_, ?_⟩
  · let shiftedComp := SequentialProObjectMorphismRep.compRep forward backward
    refine ⟨shiftedComp.reindex, fun n ↦ le_rfl, fun n ↦ ?_, ?_⟩
    · -- Proof comment: both the shifted identity representative and the composite refine to the
      -- source stage `c + n`.
      change n ≤ shiftedComp.reindex n
      simp [shiftedComp, forward, backward, SequentialProObjectMorphismRep.compRep,
        SequentialProObjectMorphismRep.ofShiftNatTrans,
        SequentialProObjectMorphismRep.ofNatTrans]
      exact Nat.le_add_left n c
    · intro n
      -- Proof comment: the composite level map is exactly the `c`-step transition of the shifted
      -- tower.
      simpa [shiftedComp, forward, backward, SequentialInverseSystem.transitionMap] using
        stageRestrictionToLimitTower_shift_transition_app (F := F) (T := T) c n
  · let originalComp := SequentialProObjectMorphismRep.compRep backward forward
    refine ⟨originalComp.reindex, fun n ↦ le_rfl, fun n ↦ ?_, ?_⟩
    · -- Proof comment: on the original tower, the same refinement again lands at stage `c + n`.
      change n ≤ originalComp.reindex n
      simp [originalComp, forward, backward, SequentialProObjectMorphismRep.compRep,
        SequentialProObjectMorphismRep.ofShiftNatTrans,
        SequentialProObjectMorphismRep.ofNatTrans]
      exact Nat.le_add_left n c
    · intro n
      -- Proof comment: the composite map from stage `c + n` to stage `n` is precisely the
      -- canonical transition in the original tower.
      simpa [originalComp, forward, backward, SequentialInverseSystem.transitionMap] using
        stageRestrictionToLimitTower_shift_comparison_app (F := F) (T := T) c n

/-- Helper for Lemma 15.98.1: the literal shift comparison induces an isomorphism of the
associated sequential pro-objects. -/
private theorem stageRestrictionToLimitTower_shift_comparison_ofNatTrans_toProObjectHom_isIso
    (c : ℕ) :
    IsIso
      ((SequentialProObjectMorphismRep.ofNatTrans
        (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c)).toProObjectHom) := by
  -- Proof comment: once the natural transformation is recognized as a pro-isomorphism, the
  -- owner-level pro-object morphism is invertible.
  exact
    SequentialProObjectMorphismRep.toProObjectHom_isIso_of_isProIsomorphism
      (a := SequentialProObjectMorphismRep.ofNatTrans
        (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c))
      (stageRestrictionToLimitTower_shift_comparison_ofNatTrans_isProIsomorphism
        (F := F) (T := T) c)

/-- Helper for Lemma 15.98.1: the canonical shift of the fixed-base tower is literally the
explicit reindexed tail tower. -/
private noncomputable def stageRestrictionToLimitTower_shift_tail_iso
    (c : ℕ) :
    SequentialInverseSystem.shift (stageRestrictionToLimitTower F T) c ≅
      stageRestrictionToLimitTailTower (F := F) (T := T) c where
  hom :=
    NatTrans.ofOpSequence
      (fun n ↦ 𝟙 _)
      (fun n ↦ by
        -- Proof comment: the shift and the explicit tail have the same successor map after
        -- reindexing by `c`.
        simpa using stageRestrictionToLimitTower_shift_tail_step (F := F) (T := T) c n)
  inv :=
    NatTrans.ofOpSequence
      (fun n ↦ 𝟙 _)
      (fun n ↦ by
        -- Proof comment: the inverse natural transformation uses the same objectwise identity,
        -- with the successor-map equality read in the opposite direction.
        simpa using (stageRestrictionToLimitTower_shift_tail_step (F := F) (T := T) c n).symm)
  hom_inv_id := by
    ext n
    simp
  inv_hom_id := by
    ext n
    simp

/-- Helper for Lemma 15.98.1: the literal shift-tail tower isomorphism induces an isomorphism of
the associated sequential pro-objects. -/
private theorem stageRestrictionToLimitTower_shift_tail_toProObjectHom_isIso
    (c : ℕ) :
    IsIso
      ((SequentialProObjectMorphismRep.ofNatTrans
        (stageRestrictionToLimitTower_shift_tail_iso (F := F) (T := T) c).hom).toProObjectHom) :=
    by
  have hpro :
      (SequentialProObjectMorphismRep.ofNatTrans
        (stageRestrictionToLimitTower_shift_tail_iso (F := F) (T := T) c).hom).IsProIsomorphism :=
      SequentialProObjectMorphismRep.natIso_isProIsomorphism_ofNatTrans
        (stageRestrictionToLimitTower_shift_tail_iso (F := F) (T := T) c)
  -- Proof comment: levelwise tower isomorphisms are already pro-isomorphisms, so they become
  -- owner-level isomorphisms on sequential pro-objects.
  exact
    SequentialProObjectMorphismRep.toProObjectHom_isIso_of_isProIsomorphism
      (a := SequentialProObjectMorphismRep.ofNatTrans
        (stageRestrictionToLimitTower_shift_tail_iso (F := F) (T := T) c).hom)
      hpro

/-- Helper for Lemma 15.98.1: a derived-limit witness for the explicit tail tower transports to
the shifted fixed-base tower. -/
private theorem isDerivedLimit_of_shift_tail_iso
    {L : DModA} (c : ℕ)
    (hL : IsDerivedLimit (stageRestrictionToLimitTailTower (F := F) (T := T) c) L) :
    IsDerivedLimit (SequentialInverseSystem.shift (stageRestrictionToLimitTower F T) c) L := by
  -- Proof comment: the explicit tail tower is literally the shifted fixed-base tower, so we only
  -- transport the Milnor witness across the tower isomorphism.
  exact
    isDerivedLimit_of_tower_iso
      (stageRestrictionToLimitTower_shift_tail_iso (F := F) (T := T) c).symm
      hL

/-- Helper for Lemma 15.98.1: a derived limit of the explicit tail tower is canonically
isomorphic to any chosen derived limit of the original fixed-base tower. -/
private theorem exists_isIso_hom_of_tail_derivedLimit
    {L : DModA} (c : ℕ)
    (hL : IsDerivedLimit (stageRestrictionToLimitTailTower (F := F) (T := T) c) L)
    (hK : IsDerivedLimit (stageRestrictionToLimitTower F T) K) :
    ∃ f : L ⟶ K, IsIso f := by
  have hShift :
      IsDerivedLimit
        (SequentialInverseSystem.shift (stageRestrictionToLimitTower F T) c) L :=
    isDerivedLimit_of_shift_tail_iso (F := F) (T := T) c hL
  let η :
      colimit (((stageRestrictionToLimitTower F T).op) ⋙ uliftCoyoneda.{0}) ⟶
        proSystemHomColimitFunctor
            (SequentialInverseSystem.shift (stageRestrictionToLimitTower F T) c) ⋙
          uliftFunctor.{0} :=
    (SequentialProObjectMorphismRep.ofNatTrans
      (stageRestrictionToLimitTower_shift_comparison (F := F) (T := T) c)).toProObjectHom
  letI : IsIso η :=
    stageRestrictionToLimitTower_shift_comparison_ofNatTrans_toProObjectHom_isIso
      (F := F) (T := T) c
  -- Proof comment: finite-prefix insensitivity is already packaged as an isomorphism of
  -- sequential pro-objects, so uniqueness of derived limits upgrades it to an isomorphism of the
  -- chosen limiting objects.
  exact
    CategoryTheory.exists_isIso_hom_of_proIsomorphism_of_isDerivedLimit
      (Ksys := SequentialInverseSystem.shift (stageRestrictionToLimitTower F T) c)
      (Msys := stageRestrictionToLimitTower F T)
      hShift hK η

/-- Helper for Lemma 15.98.1: once the explicit tail tower has a pseudo-coherent derived limit,
the original chosen derived limit is pseudo-coherent as well. -/
private theorem isPseudoCoherent_of_tail_derivedLimit
    {L : DModA} (c : ℕ)
    (hL : IsDerivedLimit (stageRestrictionToLimitTailTower (F := F) (T := T) c) L)
    (hLp : L.IsPseudoCoherent)
    (hK : IsDerivedLimit (stageRestrictionToLimitTower F T) K) :
    K.IsPseudoCoherent := by
  obtain ⟨f, hf⟩ :=
    exists_isIso_hom_of_tail_derivedLimit (F := F) (T := T) (K := K) c hL hK
  -- Proof comment: pseudo-coherence is invariant under isomorphism, so the tail model transfers
  -- directly across the uniqueness isomorphism.
  exact isPseudoCoherent_of_iso (asIso f) hLp

/-- Helper for Lemma 15.98.1: both public conclusions reduce to the single missing explicit
strict-tail realization package. -/
private theorem explicit_tail_limit_package
    [HasProduct (inverseSystemFamily (stageRestrictionToLimitTower F T))]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily (stageRestrictionToLimitTower F T)}
    (h_surj_tail : ∀ n : ℕ, Function.Surjective (stageTransitionRingHom F n))
    (h_locnil_tail :
      ∀ n : ℕ, RingHom.ker (stageTransitionRingHom F n) ≤ nilradical (stageRing F (n + 1)))
    (hstageBaseChange_tail : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n))
    (hι : HasMilnorTriangle.WithMap (stageRestrictionToLimitTower F T) ι)
    (htail : ∃ c : ℕ, ∀ n : ℕ, (T.obj (c + n)).IsPseudoCoherent) :
    K.IsPseudoCoherent ∧
      ∀ n : ℕ,
        IsIso
          (inverseLimitBaseChangeComparison T K n
            (ι ≫ Pi.π (inverseSystemFamily (stageRestrictionToLimitTower F T)) n)) := by
  -- Route correction: the duplicate pseudo-coherence and base-change `sorry`s are now merged into
  -- one source-faithful owner statement. The shift/tail transport layer is complete, so the only
  -- remaining work is to construct the strict finite-free tail model and compare its ordinary
  -- inverse limit with the chosen Milnor object.
  -- TODO: starting from `htail`, build the strict finite-free tail realization promised by the
  -- textbook using Lemma `15.76.5`, package it into one `SeqRingMod` cochain complex over
  -- `A = lim A_n`, identify its ordinary inverse-limit complex with a derived limit of the tail
  -- tower by `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`, and then transport
  -- that tail model back to the original tower via
  -- `exists_isIso_hom_of_tail_derivedLimit`. The same explicit model should then compute the
  -- comparison map induced by `hι` after projecting to each stage.
  sorry

/-- Helper for Lemma 15.98.1: once a pseudo-coherent tail is chosen, the remaining source proof is
to replace the tower by that tail and run the strict finite-free realization argument there. -/
theorem derivedLimit_isPseudoCoherent_of_pseudoCoherent_tail
    (h_surj_tail : ∀ n : ℕ, Function.Surjective (stageTransitionRingHom F n))
    (h_locnil_tail :
      ∀ n : ℕ, RingHom.ker (stageTransitionRingHom F n) ≤ nilradical (stageRing F (n + 1)))
    (hstageBaseChange_tail : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n))
    (htail : ∃ c : ℕ, ∀ n : ℕ, (T.obj (c + n)).IsPseudoCoherent)
    (hKlim : IsDerivedLimit (stageRestrictionToLimitTower F T) K) :
    K.IsPseudoCoherent := by
  rcases hKlim with ⟨hP, ⟨ι, δ, hδ⟩⟩
  letI : HasProduct (inverseSystemFamily (stageRestrictionToLimitTower F T)) := hP
  let hι : HasMilnorTriangle.WithMap (stageRestrictionToLimitTower F T) ι := ⟨δ, hδ⟩
  -- Proof comment: the public pseudo-coherence statement is the first projection of the shared
  -- explicit-tail package specialized to the Milnor map extracted from `hKlim`.
  exact
    (explicit_tail_limit_package (F := F) (T := T) (K := K) (ι := ι)
      h_surj_tail h_locnil_tail hstageBaseChange_tail hι htail).1

/-- Helper for Lemma 15.98.1: after shifting to a pseudo-coherent tail and strictifying it, the
chosen Milnor comparison map identifies derived base change of `K` with each stage. -/
theorem inverseLimitBaseChangeComparison_isIso_of_pseudoCoherent_tail
    [HasProduct (inverseSystemFamily (stageRestrictionToLimitTower F T))]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily (stageRestrictionToLimitTower F T)} {n : ℕ}
    (h_surj_tail : ∀ m : ℕ, Function.Surjective (stageTransitionRingHom F m))
    (h_locnil_tail :
      ∀ m : ℕ, RingHom.ker (stageTransitionRingHom F m) ≤ nilradical (stageRing F (m + 1)))
    (hstageBaseChange_tail : ∀ m : ℕ, IsIso (stageDerivedBaseChangeComparison T m))
    (hι : HasMilnorTriangle.WithMap (stageRestrictionToLimitTower F T) ι)
    (htail : ∃ c : ℕ, ∀ m : ℕ, (T.obj (c + m)).IsPseudoCoherent) :
    IsIso
      (inverseLimitBaseChangeComparison T K n
        (ι ≫ Pi.π (inverseSystemFamily (stageRestrictionToLimitTower F T)) n)) := by
  -- Proof comment: the public base-change statement is the second projection of the shared
  -- explicit-tail package for the same chosen Milnor map.
  exact
    (explicit_tail_limit_package (F := F) (T := T) (K := K) (ι := ι)
      h_surj_tail h_locnil_tail hstageBaseChange_tail hι htail).2 n

include h_surj h_locnil hpc hstageBaseChange

theorem derivedLimit_isPseudoCoherent_of_stagewisePseudoCoherent_or_eventuallyNilpotent
    (hKlim : IsDerivedLimit (stageRestrictionToLimitTower F T) K) :
    K.IsPseudoCoherent := by
  -- Proof comment: first isolate the tail where pseudo-coherence is known, then reduce the
  -- source proof to the tail realization step.
  have htail : ∃ c : ℕ, ∀ n : ℕ, (T.obj (c + n)).IsPseudoCoherent :=
    eventual_pseudoCoherent_tail
      (F := F) (T := T) h_surj hpc hstageBaseChange
  exact
    derivedLimit_isPseudoCoherent_of_pseudoCoherent_tail
      (F := F) (T := T) (K := K)
      h_surj h_locnil hstageBaseChange
      htail hKlim

-- Proof sketch: apply Lemma `15.98.1` to the canonical fixed-base tower
-- `stageRestrictionToLimitTower T`; any chosen Milnor map
-- `ι : K ⟶ ∏ stageRestrictionToLimitTower(T)_n` then yields the stage comparison
-- `ι ≫ π_n : K ⟶ K_n|_A`, which transposes under the derived extension/restriction adjunction to
-- the canonical base-change morphism `K ⊗_A^{\mathbf L} A_n ⟶ K_n`.
/-- Under the hypotheses of Lemma 15.98.1, the `n`th component of any chosen Milnor product map
from the derived limit `K` to the fixed-base tower `stageRestrictionToLimitTower T` induces an
isomorphism on derived base change `K ⊗_A^{\mathbf L} A_n → K_n`. -/
theorem inverseLimitBaseChangeComparison_isIso_of_stagewisePseudoCoherent_or_eventuallyNilpotent
    [HasProduct (inverseSystemFamily (stageRestrictionToLimitTower F T))]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily (stageRestrictionToLimitTower F T)} {n : ℕ}
    (hι : HasMilnorTriangle.WithMap (stageRestrictionToLimitTower F T) ι) :
    IsIso
      (inverseLimitBaseChangeComparison T K n
        (ι ≫ Pi.π (inverseSystemFamily (stageRestrictionToLimitTower F T)) n)) := by
  -- Proof comment: the same tail normalization reduces the base-change statement to the shifted
  -- explicit-model computation.
  have htail : ∃ c : ℕ, ∀ m : ℕ, (T.obj (c + m)).IsPseudoCoherent :=
    eventual_pseudoCoherent_tail
      (F := F) (T := T) h_surj hpc hstageBaseChange
  exact
    inverseLimitBaseChangeComparison_isIso_of_pseudoCoherent_tail
      (F := F) (T := T) (K := K)
      h_surj h_locnil hstageBaseChange
      hι htail

omit h_surj h_locnil hpc hstageBaseChange

end

end
