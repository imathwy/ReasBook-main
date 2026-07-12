import StacksProject_2024.Chap15.Lemma_15_96_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]

/-- Helper for Lemma 15.96.3: any morphism between zero objects of `ModuleCat A` is an
isomorphism. -/
private theorem isIso_of_isZero_of_isZero
    {X Y : ModuleCat A} (f : X ⟶ Y) (hX : Limits.IsZero X) (hY : Limits.IsZero Y) :
    IsIso f := by
  -- Proof comment: the zero morphism is automatically a two-sided inverse because both source and
  -- target have at most one morphism.
  refine ⟨⟨0, ?_, ?_⟩⟩
  · exact hX.eq_of_tgt _ _
  · exact hY.eq_of_tgt _ _

/-- Helper for Lemma 15.96.3: if the middle term of the degree-`i` short complex vanishes, then
the degree-`i` homology vanishes as well. -/
private theorem isZero_homology_of_isZero_term
    (K : ModuleComplex A) (i : ℤ) (hX : Limits.IsZero (K.X i)) :
    Limits.IsZero (K.homology i) := by
  -- Proof comment: the homology of `K` at `i` is the homology of the short complex `K.sc i`, and
  -- that short complex has zero middle object.
  simpa using
    (CategoryTheory.ShortComplex.isZero_homology_of_isZero_X₂
      (S := K.sc i)
      (by simpa [HomologicalComplex.sc] using hX))

/-- Helper for Lemma 15.96.3: linear maps send `f`-torsion elements to `f`-torsion elements. -/
private theorem linearMap_maps_torsionBy
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (g : M →ₗ[A] N) (f : A) :
    (Submodule.torsionBy A M f).map g ≤ Submodule.torsionBy A N f := by
  -- Proof comment: the defining equation `f • x = 0` is preserved by linearity of `g`.
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact
    (Submodule.mem_torsionBy_iff f (g x)).2 <|
      by
        have hx' : f • x = 0 := (Submodule.mem_torsionBy_iff f x).1 hx
        simpa using congrArg g hx'

/-- Helper for Lemma 15.96.3: the `f`-torsion submodule lies in the preimage of the target
`f`-torsion submodule under any linear map. -/
private theorem torsionBy_le_comap_of_linearMap
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (g : M →ₗ[A] N) (f : A) :
    Submodule.torsionBy A M f ≤ Submodule.comap g (Submodule.torsionBy A N f) := by
  -- Proof comment: this is the preimage reformulation of `linearMap_maps_torsionBy`.
  intro x hx
  exact (linearMap_maps_torsionBy g f) ⟨x, hx, rfl⟩

/-- Helper for Lemma 15.96.3: a linear equivalence transports quotient modules once the source
submodule maps exactly onto the target submodule. -/
private noncomputable def quotientLinearEquiv_of_submodule_map_eq
    {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) (S : Submodule A V) (T : Submodule A W)
    (hST : S.map e.toLinearMap = T) :
    (V ⧸ S) ≃ₗ[A] (W ⧸ T) := by
  let hForward : S ≤ Submodule.comap e.toLinearMap T := by
    intro x hx
    change e x ∈ T
    rw [← hST]
    exact ⟨x, hx, rfl⟩
  let hBackward : T ≤ Submodule.comap e.symm.toLinearMap S := by
    intro y hy
    change e.symm y ∈ S
    have hy' : y ∈ S.map e.toLinearMap := by
      simpa [hST] using hy
    rcases hy' with ⟨x, hx, rfl⟩
    simpa using hx
  let fQ : (V ⧸ S) →ₗ[A] (W ⧸ T) := Submodule.mapQ S T e.toLinearMap hForward
  let gQ : (W ⧸ T) →ₗ[A] (V ⧸ S) := Submodule.mapQ T S e.symm.toLinearMap hBackward
  -- Proof comment: both composites are checked on quotient representatives and reduce to the
  -- identities `e.symm (e x) = x` and `e (e.symm y) = y`.
  exact
    LinearEquiv.ofLinear fQ gQ
      (by
        apply LinearMap.ext
        intro q
        refine Quotient.inductionOn' q ?_
        intro x
        change fQ (gQ (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
        have hgQ :
            gQ (Submodule.Quotient.mk x) =
              (Submodule.Quotient.mk (e.symm x) : V ⧸ S) := by
          simpa [gQ] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ T S e.symm.toLinearMap) x
        rw [hgQ]
        have hfQ :
            fQ (Submodule.Quotient.mk (e.symm x)) =
              (Submodule.Quotient.mk (e (e.symm x)) : W ⧸ T) := by
          simpa [fQ] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ S T e.toLinearMap) (e.symm x)
        rw [hfQ]
        simp)
      (by
        apply LinearMap.ext
        intro q
        refine Quotient.inductionOn' q ?_
        intro x
        change gQ (fQ (Submodule.Quotient.mk x)) = Submodule.Quotient.mk x
        have hfQ :
            fQ (Submodule.Quotient.mk x) =
              (Submodule.Quotient.mk (e x) : W ⧸ T) := by
          simpa [fQ] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ S T e.toLinearMap) x
        rw [hfQ]
        have hgQ :
            gQ (Submodule.Quotient.mk (e x)) =
              (Submodule.Quotient.mk (e.symm (e x)) : V ⧸ S) := by
          simpa [gQ] using
            DFunLike.congr_fun (Submodule.mapQ_mkQ T S e.symm.toLinearMap) (e x)
        rw [hgQ]
        simp)

/-- Helper for Lemma 15.96.3: a linear equivalence identifies the `f`-torsion submodules of its
source and target. -/
private theorem torsionBy_map_eq_of_linearEquiv
    {V W : Type*} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (e : V ≃ₗ[A] W) (f : A) :
    (Submodule.torsionBy A V f).map e.toLinearMap = Submodule.torsionBy A W f := by
  -- Proof comment: the equation `f • x = 0` is preserved in both directions by the linear
  -- equivalence.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [Submodule.mem_torsionBy_iff] using congrArg e hx
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    simpa [Submodule.mem_torsionBy_iff] using congrArg e.symm hy

/-- Helper for Lemma 15.96.3: extending a quasi-isomorphism of nonnegative cochain complexes to a
bounded-below `ℤ`-indexed complex preserves the quasi-isomorphism property. -/
private theorem extendMap_quasiIso
    {M N : NatModuleCochainComplex A} (φ : M ⟶ N) (hφ : QuasiIso φ) :
    QuasiIso (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : 0 ≤ i
  · let n : ℕ := Int.toNat i
    have hni : ((n : ℕ) : ℤ) = i := by
      simpa [n] using Int.toNat_of_nonneg hi
    have hφi : IsIso (HomologicalComplex.homologyMap φ n) := by
      have hφn : QuasiIsoAt φ n := ((_root_.quasiIso_iff φ).1 hφ) n
      exact (quasiIsoAt_iff_isIso_homologyMap φ n).mp hφn
    let eM := M.extendHomologyIso ComplexShape.embeddingUpNat hni
    let eN := N.extendHomologyIso ComplexShape.embeddingUpNat hni
    have hnat :
        HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) i ≫ eN.hom =
          eM.hom ≫ HomologicalComplex.homologyMap φ n :=
      HomologicalComplex.extendHomologyIso_hom_naturality
        φ ComplexShape.embeddingUpNat hni
    have hrewrite :
        HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) i =
          eM.hom ≫ HomologicalComplex.homologyMap φ n ≫ eN.inv := by
      calc
        HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) i =
              (HomologicalComplex.homologyMap
                (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) i ≫
                  eN.hom) ≫ eN.inv := by
                    simp [Category.assoc]
        _ = eM.hom ≫ HomologicalComplex.homologyMap φ n ≫ eN.inv := by
              rw [hnat]
              simp
    rw [hrewrite]
    infer_instance
  · have hXiM :
        Limits.IsZero ((M.extend ComplexShape.embeddingUpNat).X i) := by
      let K' : ModuleComplex A := M.extend ComplexShape.embeddingUpNat
      exact CochainComplex.isZero_of_isStrictlyGE K' 0 i (by omega)
    have hXiN :
        Limits.IsZero ((N.extend ComplexShape.embeddingUpNat).X i) := by
      let K' : ModuleComplex A := N.extend ComplexShape.embeddingUpNat
      exact CochainComplex.isZero_of_isStrictlyGE K' 0 i (by omega)
    have hHiM :
        Limits.IsZero ((M.extend ComplexShape.embeddingUpNat).homology i) :=
      isZero_homology_of_isZero_term (M.extend ComplexShape.embeddingUpNat) i hXiM
    have hHiN :
        Limits.IsZero ((N.extend ComplexShape.embeddingUpNat).homology i) :=
      isZero_homology_of_isZero_term (N.extend ComplexShape.embeddingUpNat) i hXiN
    exact
      isIso_of_isZero_of_isZero
        (HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) i)
        hHiM hHiN

/-
Domain-style sampling:
- primary domain: Berthelot-Ogus `η_f` on cochain complexes of `A`-modules and preservation of
  quasi-isomorphisms;
- sampled chapter/project owner declarations in this domain:
  `BerthelotOgusInt.complex`,
  `BerthelotOgusInt.map`,
  `NatModuleCochainComplex`,
  `etaFMap`;
- best owner abstraction:
  `source-facing`: Lemma `15.96.3` for arbitrary `ℤ`-indexed complexes of `f`-torsion-free
    `A`-modules;
  `core/canonical`: the Berthelot-Ogus owner layer `BerthelotOgusInt.complex` and
    `BerthelotOgusInt.map` on `ModuleComplex A`;
  `bridge/view`: the bounded-below transport `etaFMap` on `NatModuleCochainComplex A`;
- primitive data vs derived API: the primitive data are only the complexes, the morphism, the
  nonzerodivisor hypothesis, and the termwise `f`-torsion-free hypotheses. The bounded-below
  `ℕ`-indexed statement is derived by transporting the owner morphism across
  `etaFExtendRestrictionIso`, so it should remain a bridge corollary rather than the main owner.
-/

namespace BerthelotOgusInt

/-- Helper for Lemma 15.96.3: the cocycle-level Berthelot-Ogus comparison commutes with a
morphism of bounded-below owner complexes. -/
private theorem cyclesToEtaXLinear_natural
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) :
    K.cyclesMap φ i ≫ ModuleCat.ofHom (cyclesToEtaXLinear f L i) =
      ModuleCat.ofHom (cyclesToEtaXLinear f K i) ≫ (map f φ).f i := by
  -- Compare both morphisms on a cycle representative after forgetting the target subtype.
  apply ModuleCat.hom_ext
  ext x
  have hcycles :
      (L.iCycles i).hom ((K.cyclesMap φ i).hom x) =
        (φ.f i).hom ((K.iCycles i).hom x) := by
    exact
      LinearMap.congr_fun
        (ModuleCat.hom_ext_iff.mp (HomologicalComplex.cyclesMap_i φ i)) x
  -- Route correction: the source proof works at the ambient degree-`i` module first, and only
  -- then remembers that the result lies in the Berthelot-Ogus submodule.
  change
    f ^ Int.toNat i • (L.iCycles i).hom ((K.cyclesMap φ i).hom x) =
      (φ.f i).hom (f ^ Int.toNat i • (K.iCycles i).hom x)
  rw [hcycles, _root_.map_smul]

/-- Helper for Lemma 15.96.3: after including into Berthelot-Ogus cycles, the cocycle comparison
is still the visibly scaled ambient cycle representative. -/
private theorem cyclesToEtaCycles_iCycles
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    cyclesToEtaCycles f K i ≫ (η[f] K).iCycles i =
      ModuleCat.ofHom (cyclesToEtaXLinear f K i) := by
  -- The defining property of `liftCycles'` identifies the lifted map after composing with the
  -- cycles inclusion.
  apply (cancel_mono ((η[f] K).iCycles i)).2
  simp [cyclesToEtaCycles, Category.assoc]

/-- Helper for Lemma 15.96.3: the cocycle comparison commutes with passing to Berthelot-Ogus
cycles under a morphism of complexes. -/
private theorem cyclesToEtaCycles_natural
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) :
    K.cyclesMap φ i ≫ cyclesToEtaCycles f L i =
      cyclesToEtaCycles f K i ≫ (η[f] K).cyclesMap (map f φ) i := by
  -- Compare the two cycles morphisms after composing with the ambient cycles inclusion.
  apply (cancel_mono ((η[f] L).iCycles i)).2
  calc
    K.cyclesMap φ i ≫ cyclesToEtaCycles f L i ≫ (η[f] L).iCycles i =
        K.cyclesMap φ i ≫ ModuleCat.ofHom (cyclesToEtaXLinear f L i) := by
          rw [Category.assoc, cyclesToEtaCycles_iCycles]
    _ = ModuleCat.ofHom (cyclesToEtaXLinear f K i) ≫ (map f φ).f i := by
          rw [cyclesToEtaXLinear_natural]
    _ = cyclesToEtaCycles f K i ≫ (η[f] K).iCycles i ≫ (map f φ).f i := by
          rw [cyclesToEtaCycles_iCycles]
    _ = cyclesToEtaCycles f K i ≫ ((η[f] K).iCycles i ≫ (map f φ).f i) := by
          simp [Category.assoc]
    _ =
        cyclesToEtaCycles f K i ≫
          ((η[f] K).cyclesMap (map f φ) i ≫ (η[f] L).iCycles i) := by
          rw [HomologicalComplex.cyclesMap_i]
    _ =
        (cyclesToEtaCycles f K i ≫ (η[f] K).cyclesMap (map f φ) i) ≫
          (η[f] L).iCycles i := by
            simp [Category.assoc]

/-- Helper for Lemma 15.96.3: the cocycle comparison descends naturally to homology. -/
private theorem cyclesToEtaHomology_natural
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) :
    K.cyclesMap φ i ≫ cyclesToEtaHomology f L i =
      cyclesToEtaHomology f K i ≫ HomologicalComplex.homologyMap (map f φ) i := by
  -- First commute on cycles, then use homology naturality for the Berthelot-Ogus map.
  calc
    K.cyclesMap φ i ≫ cyclesToEtaHomology f L i =
      K.cyclesMap φ i ≫ cyclesToEtaCycles f L i ≫ (η[f] L).homologyπ i := by
        simp [cyclesToEtaHomology, Category.assoc]
    _ =
      (cyclesToEtaCycles f K i ≫ (η[f] K).cyclesMap (map f φ) i) ≫
        (η[f] L).homologyπ i := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ (η[f] L).homologyπ i) (cyclesToEtaCycles_natural f φ i)
    _ =
      cyclesToEtaCycles f K i ≫
        ((η[f] K).cyclesMap (map f φ) i ≫ (η[f] L).homologyπ i) := by
        simp [Category.assoc]
    _ =
      cyclesToEtaCycles f K i ≫
        ((η[f] K).homologyπ i ≫ HomologicalComplex.homologyMap (map f φ) i) := by
        rw [HomologicalComplex.homologyπ_naturality]
    _ =
      cyclesToEtaHomology f K i ≫ HomologicalComplex.homologyMap (map f φ) i := by
        simp [cyclesToEtaHomology, Category.assoc]

/-- Helper for Lemma 15.96.3: the descended homology comparison map commutes with the canonical
projection from cycles to homology. -/
private theorem homologyToEtaHomology_homologyπ
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    K.homologyπ i ≫ homologyToEtaHomology f K i =
      cyclesToEtaHomology f K i := by
  -- This is the defining `descHomology` computation for the short complex `K.sc i`.
  change
    (K.sc i).homologyπ ≫
        (K.sc i).descHomology
          (cyclesToEtaHomology f K i)
          (toCycles_comp_cyclesToEtaHomology_eq_zero f K i) =
      cyclesToEtaHomology f K i
  exact
    ShortComplex.π_descHomology (S := K.sc i)
      (k := cyclesToEtaHomology f K i)
      (hk := toCycles_comp_cyclesToEtaHomology_eq_zero f K i)

/-- Helper for Lemma 15.96.3: the homology-level Berthelot-Ogus comparison is natural before
passing to the quotient by `f`-torsion. -/
private theorem homologyToEtaHomology_natural
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ) :
    HomologicalComplex.homologyMap φ i ≫ homologyToEtaHomology f L i =
      homologyToEtaHomology f K i ≫ HomologicalComplex.homologyMap (map f φ) i := by
  -- Cancel the canonical epimorphism from cycles to homology and reduce to cocycle naturality.
  apply (cancel_epi (K.homologyπ i)).1
  calc
    K.homologyπ i ≫ HomologicalComplex.homologyMap φ i ≫ homologyToEtaHomology f L i =
      K.cyclesMap φ i ≫ (L.homologyπ i ≫ homologyToEtaHomology f L i) := by
        rw [← Category.assoc, HomologicalComplex.homologyπ_naturality]
        simp [Category.assoc]
    _ =
      K.cyclesMap φ i ≫ cyclesToEtaHomology f L i := by
        rw [homologyToEtaHomology_homologyπ]
    _ =
      cyclesToEtaHomology f K i ≫ HomologicalComplex.homologyMap (map f φ) i := by
        rw [cyclesToEtaHomology_natural]
    _ =
      K.homologyπ i ≫ homologyToEtaHomology f K i ≫
        HomologicalComplex.homologyMap (map f φ) i := by
        rw [← Category.assoc, homologyToEtaHomology_homologyπ]
    _ =
      K.homologyπ i ≫
        (homologyToEtaHomology f K i ≫ HomologicalComplex.homologyMap (map f φ) i) := by
        simp [Category.assoc]

/-- Helper for Lemma 15.96.3: on the bounded-below regular branch, the quotient comparison map is
natural with respect to morphisms of complexes. -/
private theorem homologyComparisonOfRegular_natural
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L) (i : ℤ)
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0]
    (hK : IsTermwiseFTorsionFree f K) (hL : IsTermwiseFTorsionFree f L) :
    ModuleCat.ofHom
      (Submodule.mapQ
        (Submodule.torsionBy A (K.homology i) f)
        (Submodule.torsionBy A (L.homology i) f)
        (HomologicalComplex.homologyMap φ i).hom
        (torsionBy_le_comap_of_linearMap (HomologicalComplex.homologyMap φ i).hom f)) ≫
      ModuleCat.ofHom (homologyComparisonOfRegular f L i hL) =
        ModuleCat.ofHom (homologyComparisonOfRegular f K i hK) ≫
          HomologicalComplex.homologyMap (map f φ) i := by
  -- Unwind both quotient maps on representatives and invoke the homology-level naturality square.
  apply ModuleCat.hom_ext
  ext q
  refine Quotient.inductionOn' q ?_
  intro x
  -- Proof comment: both quotient maps are the canonical representative maps, so the claim
  -- reduces directly to `homologyToEtaHomology_natural` on `x`.
  simpa [homologyComparisonOfRegular, Category.assoc] using
    LinearMap.congr_fun
      (ModuleCat.hom_ext_iff.mp (homologyToEtaHomology_natural f φ i)) x

/-- Helper for Lemma 15.96.3: the owner-level quasi-isomorphism statement is already proved on
the bounded-below branch where Lemma `15.96.2` supplies comparison equivalences. -/
private theorem map_quasiIso_of_isStrictlyGE_zero
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L)
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0]
    (hf : f ∈ nonZeroDivisors A) (hφ : QuasiIso φ)
    (hK : IsTermwiseFTorsionFree f K) (hL : IsTermwiseFTorsionFree f L) :
    QuasiIso (map f φ) := by
  -- Route correction: the source proof factors through the quotient comparison equivalences from
  -- Lemma `15.96.2`, so we first identify the Berthelot-Ogus homology map with the induced
  -- quotient map on `H^i(-) / H^i(-)[f]`.
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hφi : IsIso (HomologicalComplex.homologyMap φ i) := by
    have hAt : QuasiIsoAt φ i := ((_root_.quasiIso_iff φ).1 hφ) i
    exact (quasiIsoAt_iff_isIso_homologyMap φ i).1 hAt
  let eφ : K.homology i ≅ L.homology i := asIso (HomologicalComplex.homologyMap φ i)
  let eQ :
      ((K.homology i) ⧸ Submodule.torsionBy A (K.homology i) f) ≃ₗ[A]
        ((L.homology i) ⧸ Submodule.torsionBy A (L.homology i) f) :=
    quotientLinearEquiv_of_submodule_map_eq
      eφ.toLinearEquiv
      (Submodule.torsionBy A (K.homology i) f)
      (Submodule.torsionBy A (L.homology i) f)
      (torsionBy_map_eq_of_linearEquiv eφ.toLinearEquiv f)
  let eK :
      ((K.homology i) ⧸ Submodule.torsionBy A (K.homology i) f) ≅ (η[f] K).homology i :=
    (homologyComparisonEquiv f K i hf hK).toModuleIso
  let eL :
      ((L.homology i) ⧸ Submodule.torsionBy A (L.homology i) f) ≅ (η[f] L).homology i :=
    (homologyComparisonEquiv f L i hf hL).toModuleIso
  have hq :
      ModuleCat.ofHom
        (Submodule.mapQ
          (Submodule.torsionBy A (K.homology i) f)
          (Submodule.torsionBy A (L.homology i) f)
          (HomologicalComplex.homologyMap φ i).hom
          (torsionBy_le_comap_of_linearMap (HomologicalComplex.homologyMap φ i).hom f)) =
        eQ.toModuleIso.hom := by
    rfl
  have hcompK :
      ModuleCat.ofHom (homologyComparisonOfRegular f K i hK) = eK.hom := by
    ext q
    simp [eK, homologyComparisonEquiv, homologyComparison, hK]
  have hcompL :
      ModuleCat.ofHom (homologyComparisonOfRegular f L i hL) = eL.hom := by
    ext q
    simp [eL, homologyComparisonEquiv, homologyComparison, hL]
  have hnat :
      eQ.toModuleIso.hom ≫ eL.hom =
        eK.hom ≫ HomologicalComplex.homologyMap (map f φ) i := by
    simpa [hq, hcompK, hcompL] using
      homologyComparisonOfRegular_natural f φ i hK hL
  have hrewrite :
      HomologicalComplex.homologyMap (map f φ) i =
        eK.inv ≫ eQ.toModuleIso.hom ≫ eL.hom := by
    calc
      HomologicalComplex.homologyMap (map f φ) i =
          eK.inv ≫ (eK.hom ≫ HomologicalComplex.homologyMap (map f φ) i) := by
            simp [Category.assoc]
      _ = eK.inv ≫ (eQ.toModuleIso.hom ≫ eL.hom) := by
            rw [hnat]
      _ = eK.inv ≫ eQ.toModuleIso.hom ≫ eL.hom := by
            simp [Category.assoc]
  rw [hrewrite]
  infer_instance

-- Proof sketch: identify the homology of `η[f] K` and `η[f] L` with the quotients
-- `H^i(K) / H^i(K)[f]` and `H^i(L) / H^i(L)[f]` by the Berthelot-Ogus comparison, observe that
-- the induced map on these quotients is an isomorphism because `φ` is a quasi-isomorphism, and
-- use naturality of the comparison maps to conclude that `map f φ` induces isomorphisms on every
-- cohomology group.
/-- Lemma 15.96.3, owner-level form: if `f` is a nonzerodivisor in `A`,
`φ : K^\bullet ⟶ L^\bullet` is a quasi-isomorphism, and both complexes are termwise
`f`-torsion free, then the induced map `η_f K^\bullet ⟶ η_f L^\bullet` is again a
quasi-isomorphism. -/
@[stacks 0F7Q]
theorem map_quasiIso
    (f : A) {K L : ModuleComplex A} (φ : K ⟶ L)
    (hf : f ∈ nonZeroDivisors A) (hφ : QuasiIso φ)
    (hK : IsTermwiseFTorsionFree f K) (hL : IsTermwiseFTorsionFree f L) :
    QuasiIso (map f φ) := by
  -- Route correction: the quotient-by-`f` comparison from Lemma `15.96.2` is only public on the
  -- bounded-below owner branch, so the unrestricted `ℤ`-indexed theorem still needs a canonical
  -- transport from arbitrary degree `i` to that branch before the naturality square can close.
  -- TODO: for each degree, transport the homology comparison through a source-faithful bounded
  -- below truncation/shift bridge, then conjugate `HomologicalComplex.homologyMap (map f φ) i`
  -- by the resulting quotient comparison equivalences.
  sorry

end BerthelotOgusInt

/-- Helper for Lemma 15.96.3: in degree `0`, restricting a bounded-below `ℤ`-indexed complex to
nonnegative degrees does not change the cycles object. -/
private noncomputable def restriction_cycles_iso_nat_zero
    (K : ModuleComplex A) [K.IsStrictlyGE 0] :
    (K.restriction (ComplexShape.embeddingUpIntGE 0)).cycles 0 ≅ K.cycles (0 : ℤ) := by
  let Kr := K.restriction (ComplexShape.embeddingUpIntGE 0)
  let Sr : ShortComplex (ModuleCat A) := Kr.sc' 0 0 1
  let Sf : ShortComplex (ModuleCat A) := K.sc' (-1) 0 1
  let e0 : Kr.X 0 ≅ K.X (0 : ℤ) :=
    K.restrictionXIso (ComplexShape.embeddingUpIntGE 0) (by simp)
  let e1 : Kr.X 1 ≅ K.X (1 : ℤ) :=
    K.restrictionXIso (ComplexShape.embeddingUpIntGE 0) (by simp)
  have hprevKr : (ComplexShape.up ℕ).prev 0 = 0 := by
    simp [CochainComplex.prev]
  have hnextKr : (ComplexShape.up ℕ).next 0 = 1 := by
    simpa using (CochainComplex.next ℕ 0)
  have hprevK : (ComplexShape.up ℤ).prev (0 : ℤ) = (-1 : ℤ) := by
    simpa using (CochainComplex.prev ℤ (0 : ℤ))
  have hnextK : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
    simpa using (CochainComplex.next ℤ (0 : ℤ))
  have hd :
      Kr.d 0 1 ≫ e1.hom = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
    -- Proof comment: restricting in degree `0` only inserts the standard `restrictionXIso`
    -- identifications into the outgoing differential.
    rw [HomologicalComplex.restriction_d_eq
      (K := K) (e := ComplexShape.embeddingUpIntGE 0)
      (i' := (0 : ℤ)) (j' := (1 : ℤ)) (by simp) (by simp)]
    calc
      ((e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ e1.inv) ≫ e1.hom) =
          e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) ≫ (e1.inv ≫ e1.hom) := by
            simp [Category.assoc]
      _ = e0.hom ≫ K.d (0 : ℤ) (1 : ℤ) := by
            simp
  -- Proof comment: compare both cycles objects as kernels of the same degree-`1` differential.
  exact
    (Kr.cyclesIsoSc' 0 0 1 hprevKr hnextKr) ≪≫
      Sr.cyclesIsoKernel ≪≫
      CategoryTheory.Limits.kernel.mapIso (Kr.d 0 1) (K.d (0 : ℤ) (1 : ℤ)) e0 e1 hd ≪≫
      Sf.cyclesIsoKernel.symm ≪≫
      (K.cyclesIsoSc' (-1) 0 1 hprevK hnextK).symm

/-- Helper for Lemma 15.96.3: in a bounded-below `ℤ`-indexed complex, restricting to
nonnegative degrees preserves homology in every degree. -/
private noncomputable def restriction_homology_iso_nat_of_isStrictlyGE
    (K : ModuleComplex A) [K.IsStrictlyGE 0] (n : ℕ) :
    (K.restriction (ComplexShape.embeddingUpIntGE 0)).homology n ≅ K.homology (n : ℤ) := by
  cases n with
  | zero =>
      let Kr := K.restriction (ComplexShape.embeddingUpIntGE 0)
      let eCycles := restriction_cycles_iso_nat_zero (A := A) K
      let eπr : Kr.homology 0 ≅ Kr.cycles 0 := (CochainComplex.isoHomologyπ₀ Kr).symm
      have hzero_prev : K.d (-1) 0 = 0 := by
        -- Proof comment: the predecessor term vanishes below the cutoff, so the incoming
        -- differential into degree `0` is zero.
        exact (K.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _
      let eπf : K.cycles (0 : ℤ) ≅ K.homology (0 : ℤ) :=
        K.isoHomologyπ (-1) 0 (by simp) hzero_prev
      -- Proof comment: degree `0` is the only place where we replace homology by cycles first.
      exact eπr ≪≫ eCycles ≪≫ eπf
  | succ n =>
      -- Proof comment: in positive degree, predecessor and successor both remain in the retained
      -- range, so the standard restriction-homology comparison applies directly.
      simpa using
        (HomologicalComplex.restrictionHomologyIso
          K (ComplexShape.embeddingUpIntGE 0) n (n + 1) (n + 2)
          (by simp) (by simp)
          (by simp : (ComplexShape.embeddingUpIntGE 0).f n = (n : ℤ))
          (by simp : (ComplexShape.embeddingUpIntGE 0).f (n + 1) = ((n + 1 : ℕ) : ℤ))
          (by norm_num : (ComplexShape.embeddingUpIntGE 0).f (n + 2) = ((n + 2 : ℕ) : ℤ))
          (by simp)
          (by
            calc
              (ComplexShape.up ℤ).next (((n + 1 : ℕ) : ℤ)) = (((n + 1 : ℕ) : ℤ) + 1) := by
                simpa using (CochainComplex.next ℤ (((n + 1 : ℕ) : ℤ)))
              _ = ((n + 2 : ℕ) : ℤ) := by omega))

/-- Helper for Lemma 15.96.3: the restriction-homology comparison is natural in the map of
bounded-below complexes. -/
private theorem restriction_homology_iso_nat_of_isStrictlyGE_natural
    {K L : ModuleComplex A} (ψ : K ⟶ L)
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] (n : ℕ) :
    HomologicalComplex.homologyMap
        (restrictionMap ψ (ComplexShape.embeddingUpIntGE 0)) n ≫
      (restriction_homology_iso_nat_of_isStrictlyGE (K := L) n).hom =
        (restriction_homology_iso_nat_of_isStrictlyGE (K := K) n).hom ≫
          HomologicalComplex.homologyMap ψ (n : ℤ) := by
  -- TODO: the remaining restriction transport blocker is the naturality square for the repaired
  -- degree-`0` comparison and its successor-degree specialization. Once that square is named, the
  -- restriction quasi-isomorphism package and `etaFMap_quasiIso` close by conjugation.
  sorry

/-- Helper for Lemma 15.96.3: restricting a quasi-isomorphism between bounded-below owner
complexes to nonnegative degrees preserves the quasi-isomorphism property. -/
private theorem restrictionMap_quasiIso_of_isStrictlyGE_zero
    {K L : ModuleComplex A} (ψ : K ⟶ L)
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] (hψ : QuasiIso ψ) :
    QuasiIso (restrictionMap ψ (ComplexShape.embeddingUpIntGE 0)) := by
  -- TODO: conjugate `homologyMap (restrictionMap ψ)` by
  -- `restriction_homology_iso_nat_of_isStrictlyGE`; the only missing ingredient is the naturality
  -- square isolated in `restriction_homology_iso_nat_of_isStrictlyGE_natural`.
  sorry

/-- Helper for Lemma 15.96.3: after transporting `etaFMap` across the extension-restriction
comparison isomorphisms, one recovers the restricted owner-level Berthelot-Ogus map. -/
private theorem etaFMap_conjugation
    (f : A) {M N : NatModuleCochainComplex A} (φ : M ⟶ N) :
    (etaFExtendRestrictionIso f M).hom ≫ etaFMap f φ ≫
        (etaFExtendRestrictionIso f N).inv =
      restrictionMap
        (BerthelotOgusInt.map f (extendMap φ ComplexShape.embeddingUpNat))
        (ComplexShape.embeddingUpIntGE 0) := by
  -- Proof comment: unfold `etaFMap` once and cancel the transport isomorphisms on both sides.
  rw [etaFMap]
  simp [Category.assoc]

-- Proof sketch: transport the owner-level quasi-isomorphism theorem
-- `BerthelotOgusInt.map_quasiIso` from `M.extend ComplexShape.embeddingUpNat` and
-- `N.extend ComplexShape.embeddingUpNat` across the canonical restriction isomorphisms
-- `etaFExtendRestrictionIso`.
/-- Lemma 15.96.3, bounded-below bridge/view: if `f` is a nonzerodivisor in `A`,
`φ : M^\bullet ⟶ N^\bullet` is a quasi-isomorphism, and both nonnegative complexes are termwise
`f`-torsion free, then the induced map `η_f M^\bullet ⟶ η_f N^\bullet` is again a
quasi-isomorphism. -/
@[stacks 0F7Q]
theorem etaFMap_quasiIso
    (f : A) {M N : NatModuleCochainComplex A} (φ : M ⟶ N)
    (hf : f ∈ nonZeroDivisors A) (hφ : QuasiIso φ)
    (hM : IsTermwiseFTorsionFree f M) (hN : IsTermwiseFTorsionFree f N) :
    QuasiIso (etaFMap f φ) := by
  -- Proof comment: first lift `φ` to the bounded-below owner complexes where `extendMap`
  -- preserves quasi-isomorphisms.
  have hExtend :
      QuasiIso (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat) :=
    extendMap_quasiIso φ hφ
  -- Proof comment: the owner-level Berthelot-Ogus map is a quasi-isomorphism once the remaining
  -- unrestricted owner theorem is available.
  have hEtaExtend :
      QuasiIso
        (BerthelotOgusInt.map
          f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) :=
    BerthelotOgusInt.map_quasiIso_of_isStrictlyGE_zero
      f
      (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)
      hf hExtend hM.toIsTermwiseFTorsionFree hN.toIsTermwiseFTorsionFree
  have hRestriction :
      QuasiIso
        (restrictionMap
          (BerthelotOgusInt.map
            f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
          (ComplexShape.embeddingUpIntGE 0)) :=
    restrictionMap_quasiIso_of_isStrictlyGE_zero
      (BerthelotOgusInt.map
        f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
      hEtaExtend
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hRestriction_n :
      IsIso
        (HomologicalComplex.homologyMap
          (restrictionMap
            (BerthelotOgusInt.map
              f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
            (ComplexShape.embeddingUpIntGE 0)) n) := by
    have hAt :
        QuasiIsoAt
          (restrictionMap
            (BerthelotOgusInt.map
              f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
            (ComplexShape.embeddingUpIntGE 0)) n :=
      ((_root_.quasiIso_iff
        (restrictionMap
          (BerthelotOgusInt.map
            f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
          (ComplexShape.embeddingUpIntGE 0))).1 hRestriction) n
    exact
      (quasiIsoAt_iff_isIso_homologyMap
        (restrictionMap
          (BerthelotOgusInt.map
            f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
          (ComplexShape.embeddingUpIntGE 0)) n).mp hAt
  let eM := HomologicalComplex.homologyMapIso (etaFExtendRestrictionIso f M) n
  let eN := HomologicalComplex.homologyMapIso (etaFExtendRestrictionIso f N) n
  have hconj :
      eM.hom ≫ HomologicalComplex.homologyMap (etaFMap f φ) n ≫ eN.inv =
        HomologicalComplex.homologyMap
          (restrictionMap
            (BerthelotOgusInt.map
              f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
            (ComplexShape.embeddingUpIntGE 0)) n := by
    -- Proof comment: apply homology to the chain-level conjugation identity and expand functoriality.
    simpa [eM, eN, HomologicalComplex.homologyMap_comp, Category.assoc] using
      congrArg (fun χ ↦ HomologicalComplex.homologyMap χ n) (etaFMap_conjugation f φ)
  have hrewrite :
      HomologicalComplex.homologyMap (etaFMap f φ) n =
        eM.inv ≫
          HomologicalComplex.homologyMap
            (restrictionMap
              (BerthelotOgusInt.map
                f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
              (ComplexShape.embeddingUpIntGE 0)) n ≫
            eN.hom := by
    calc
      HomologicalComplex.homologyMap (etaFMap f φ) n =
        eM.inv ≫ (eM.hom ≫ HomologicalComplex.homologyMap (etaFMap f φ) n) := by
          simp [Category.assoc]
      _ = eM.inv ≫
          ((eM.hom ≫ HomologicalComplex.homologyMap (etaFMap f φ) n ≫ eN.inv) ≫ eN.hom) := by
            simp [Category.assoc]
      _ = eM.inv ≫
          (HomologicalComplex.homologyMap
            (restrictionMap
              (BerthelotOgusInt.map
                f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
              (ComplexShape.embeddingUpIntGE 0)) n ≫
            eN.hom) := by
              rw [hconj]
      _ = eM.inv ≫
          HomologicalComplex.homologyMap
            (restrictionMap
              (BerthelotOgusInt.map
                f (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat))
              (ComplexShape.embeddingUpIntGE 0)) n ≫
            eN.hom := by
              simp [Category.assoc]
  rw [hrewrite]
  infer_instance

end
