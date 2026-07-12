import Mathlib
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import StacksProject_2024.Chap12.Definition_12_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace CategoryTheory

namespace SequentialInverseSystem

/-- Local abbreviation for sequential inverse systems of abelian groups. -/
abbrev AbSeq := SequentialInverseSystem AddCommGrpCat.{0}

noncomputable section

/-- Helper for Lemma 15.87.15: transition maps compose along chains of indices. -/
private theorem transitionMap_comp
    (F : AbSeq) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (Nat.le_trans hij hjk) = F.transitionMap hjk ≫ F.transitionMap hij := by
  have hcomp :
      (homOfLE (Nat.le_trans hij hjk)).op = (homOfLE hjk).op ≫ (homOfLE hij).op := by
    exact Subsingleton.elim _ _
  simpa [SequentialInverseSystem.transitionMap, hcomp] using
    (Functor.map_comp F ((homOfLE hjk).op) ((homOfLE hij).op)).symm

/-- Helper for Lemma 15.87.15: evaluating a short exact sequence of sequential inverse systems at a
stage gives a short exact sequence of abelian groups. -/
private theorem shortExact_eval {S : ShortComplex AbSeq} {n : ℕ} (hS : S.ShortExact) :
    (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n))).ShortExact := by
  let ev := (evaluation ℕᵒᵖ AddCommGrpCat).obj (op n)
  have hExactMono : (S.map ev).Exact ∧ Mono (S.map ev).f := by
    simpa using
      (S.map ev).exact_and_mono_f_iff_f_is_kernel.2
        ⟨KernelFork.mapIsLimit _ hS.fIsKernel ev⟩
  refine ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 ?_
  exact (NatTrans.epi_iff_epi_app S.g).1 hS.epi_g (op n)

/-- Helper for Lemma 15.87.15: stagewise short exactness gives exactness of the underlying group
homomorphisms. -/
private theorem shortExact_eval_function_exact {S : ShortComplex AbSeq} {n : ℕ}
    (hS : S.ShortExact) :
    Function.Exact (S.f.app (op n)).hom (S.g.app (op n)).hom := by
  let T : ShortComplex AddCommGrpCat := S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj (op n))
  have hT : T.ShortExact := by
    simpa [T] using shortExact_eval (S := S) hS
  refine Function.Exact.of_comp_of_mem_range ?_ ?_
  · funext x
    have hzero := congrArg (fun t ↦ t.hom x) T.zero
    simpa [T] using hzero
  · intro b hb
    let φ : AddCommGrpCat.of ℤ ⟶ T.X₂ := AddCommGrpCat.ofHom ((zmultiplesHom T.X₂) b)
    have hφzero : φ ≫ T.g = 0 := by
      apply AddCommGrpCat.int_hom_ext
      change (AddCommGrpCat.Hom.hom T.g) (((zmultiplesHom T.X₂) b) 1) = 0
      rw [zmultiplesHom_apply, one_zsmul]
      simpa [T] using hb
    let ψ : AddCommGrpCat.of ℤ ⟶ T.X₁ := hT.fIsKernel.lift (KernelFork.ofι φ hφzero)
    have hψ : ψ ≫ T.f = φ := by
      simpa [ψ] using hT.fIsKernel.fac (KernelFork.ofι φ hφzero) WalkingParallelPair.zero
    have hφ_app_one : φ.hom 1 = b := by
      change ((zmultiplesHom T.X₂) b) 1 = b
      rw [zmultiplesHom_apply, one_zsmul]
    refine ⟨ψ.hom 1, ?_⟩
    change T.f.hom (ψ.hom 1) = b
    have hψ1 := congrArg (fun t ↦ t.hom 1) hψ
    simpa [hφ_app_one] using hψ1

/-- Helper for Lemma 15.87.15: the concrete range inclusion in `AddCommGrpCat` is a monomorphism.
-/
private instance rangeSubtype_mono {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    Mono (AddCommGrpCat.ofHom f.hom.range.subtype) :=
  ConcreteCategory.mono_of_injective _ Subtype.val_injective

/-- Helper for Lemma 15.87.15: the image-subobject comparison with the concrete range subgroup
commutes with the image arrow in `AddCommGrpCat`. -/
private theorem imageSubobject_to_range_arrow {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    ((imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom) ≫
      AddCommGrpCat.ofHom f.hom.range.subtype = (imageSubobject f).arrow := by
  rw [Category.assoc]
  change (imageSubobjectIso f).hom ≫ (AddCommGrpCat.imageIsoRange f).hom ≫
      AddCommGrpCat.image.ι f = (imageSubobject f).arrow
  have hrange :
      (AddCommGrpCat.imageIsoRange f).hom ≫ AddCommGrpCat.image.ι f = image.ι f := by
    simpa [AddCommGrpCat.imageIsoRange] using
      (IsImage.isoExt_hom_m (hF := Image.isImage f) (hF' := AddCommGrpCat.isImage f))
  rw [hrange]
  simp

/-- Helper for Lemma 15.87.15: inclusion of image subobjects implies inclusion of the underlying
set-theoretic ranges in `AddCommGrpCat`. -/
private theorem range_subset_of_imageSubobject_le
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : imageSubobject f ≤ imageSubobject g) :
    Set.range f.hom ⊆ Set.range g.hom := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  let φ : X₁ ⟶ AddCommGrpCat.of g.hom.range :=
    factorThruImageSubobject f ≫
      Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
        (imageSubobjectIso g).hom ≫ (AddCommGrpCat.imageIsoRange g).hom
  have hφmor : φ ≫ AddCommGrpCat.ofHom g.hom.range.subtype = f := by
    calc
      φ ≫ AddCommGrpCat.ofHom g.hom.range.subtype
          = factorThruImageSubobject f ≫
              Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
                (((imageSubobjectIso g).hom ≫ (AddCommGrpCat.imageIsoRange g).hom) ≫
                  AddCommGrpCat.ofHom g.hom.range.subtype) := by
              simp [φ, Category.assoc]
      _ = factorThruImageSubobject f ≫
            Subobject.ofLE (imageSubobject f) (imageSubobject g) h ≫
              (imageSubobject g).arrow := by
            rw [imageSubobject_to_range_arrow]
      _ = factorThruImageSubobject f ≫ (imageSubobject f).arrow := by
            rw [Subobject.ofLE_arrow]
      _ = f := by
            rw [imageSubobject_arrow_comp]
  refine ⟨(φ.hom x).2.choose, ?_⟩
  have hφ := congrArg (fun u ↦ u.hom x) hφmor
  exact ((φ.hom x).2.choose_spec).trans hφ

/-- Helper for Lemma 15.87.15: equality of image subobjects gives equality of concrete ranges in
`AddCommGrpCat`. -/
private theorem range_eq_of_imageSubobject_eq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : imageSubobject f = imageSubobject g) :
    Set.range f.hom = Set.range g.hom := by
  refine Set.Subset.antisymm ?_ ?_
  · exact range_subset_of_imageSubobject_le h.le
  · exact range_subset_of_imageSubobject_le h.symm.le

/-- Helper for Lemma 15.87.15: in `AddCommGrpCat`, the image subobject is the concrete range
subgroup viewed as a subobject. -/
private theorem imageSubobject_eq_range_mk {X Y : AddCommGrpCat.{0}} (f : X ⟶ Y) :
    imageSubobject f = Subobject.mk (AddCommGrpCat.ofHom f.hom.range.subtype) := by
  exact CategoryTheory.Subobject.eq_mk_of_comm
    (AddCommGrpCat.ofHom f.hom.range.subtype)
    ((imageSubobjectIso f).trans (AddCommGrpCat.imageIsoRange f))
    (imageSubobject_to_range_arrow f)

/-- Helper for Lemma 15.87.15: equality of concrete ranges induces an additive equivalence between
the corresponding range subgroups. -/
private noncomputable def range_subgroup_add_equiv_of_range_eq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : Set.range f.hom = Set.range g.hom) :
    f.hom.range ≃+ g.hom.range := by
  refine
    { toFun := fun x ↦ by
        refine ⟨x.1, ?_⟩
        change x.1 ∈ Set.range g.hom
        exact h ▸ x.2
      invFun := fun y ↦ by
        refine ⟨y.1, ?_⟩
        change y.1 ∈ Set.range f.hom
        exact h.symm ▸ y.2
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro y
        ext
        rfl
      map_add' := by
        intro x y
        ext
        rfl }

/-- Helper for Lemma 15.87.15: equality of concrete ranges induces an isomorphism between the
corresponding range subgroups. -/
private noncomputable def range_subgroup_iso_of_range_eq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : Set.range f.hom = Set.range g.hom) :
    AddCommGrpCat.of f.hom.range ≅ AddCommGrpCat.of g.hom.range :=
  (range_subgroup_add_equiv_of_range_eq h).toAddCommGrpIso

/-- Helper for Lemma 15.87.15: equality of concrete ranges can be pushed back to equality of
image subobjects in `AddCommGrpCat`. -/
private theorem imageSubobject_eq_of_range_eq
    {X₁ X₂ Y : AddCommGrpCat.{0}} {f : X₁ ⟶ Y} {g : X₂ ⟶ Y}
    (h : Set.range f.hom = Set.range g.hom) :
    imageSubobject f = imageSubobject g := by
  let e : AddCommGrpCat.of f.hom.range ≅ AddCommGrpCat.of g.hom.range :=
    range_subgroup_iso_of_range_eq h
  have he :
      e.hom ≫ AddCommGrpCat.ofHom g.hom.range.subtype =
        AddCommGrpCat.ofHom f.hom.range.subtype := by
    ext x
    change ((range_subgroup_add_equiv_of_range_eq h) x).1 = x.1
    rfl
  calc
    imageSubobject f = Subobject.mk (AddCommGrpCat.ofHom f.hom.range.subtype) :=
      imageSubobject_eq_range_mk f
    _ = Subobject.mk (AddCommGrpCat.ofHom g.hom.range.subtype) :=
      CategoryTheory.Subobject.mk_eq_mk_of_comm
        (AddCommGrpCat.ofHom f.hom.range.subtype)
        (AddCommGrpCat.ofHom g.hom.range.subtype)
        e
        he
    _ = imageSubobject g := (imageSubobject_eq_range_mk g).symm

/-- Lemma 15.87.15: for a short exact sequence `0 ⟶ (A_i) ⟶ (B_i) ⟶ (C_i) ⟶ 0` of inverse
systems of abelian groups, if `(A_i)` and `(C_i)` are Mittag-Leffler, then `(B_i)` is
Mittag-Leffler. -/
theorem isMittagLeffler_middle_of_shortExact
    (S : ShortComplex AbSeq)
    (hS : S.ShortExact)
    (hA : S.X₁.IsMittagLeffler)
    (hC : S.X₃.IsMittagLeffler) :
    S.X₂.IsMittagLeffler := by
  intro i
  obtain ⟨cA, hicA, hAstable⟩ := hA i
  obtain ⟨c, hcA, hCstable⟩ := hC cA
  let hic : i ≤ c := Nat.le_trans hicA hcA
  refine ⟨c, hic, ?_⟩
  intro k hck
  apply imageSubobject_eq_of_range_eq
  refine Set.Subset.antisymm ?_ ?_
  · intro b hb
    rcases hb with ⟨bk, rfl⟩
    refine ⟨(S.X₂.transitionMap hck).hom bk, ?_⟩
    have hcomp := congrArg
      (fun t ↦ t.hom bk)
      (transitionMap_comp S.X₂ hic hck)
    simpa [hic] using hcomp.symm
  · intro b hb
    rcases hb with ⟨bc, rfl⟩
    have hkA : cA ≤ k := Nat.le_trans hcA hck
    have hCrange :
        Set.range ((S.X₃.transitionMap (Nat.le_trans hcA hck)).hom) =
          Set.range ((S.X₃.transitionMap hcA).hom) := by
      exact range_eq_of_imageSubobject_eq (hCstable hck)
    let zcA : S.X₃.obj (op cA) := (S.X₃.transitionMap hcA).hom ((S.g.app (op c)).hom bc)
    have hz_mem :
        zcA ∈ Set.range ((S.X₃.transitionMap (Nat.le_trans hcA hck)).hom) := by
      rw [hCrange]
      exact ⟨(S.g.app (op c)).hom bc, rfl⟩
    obtain ⟨zk, hzk⟩ := hz_mem
    have hsurj_gk :
        Function.Surjective (S.g.app (op k)).hom := by
      exact (AddCommGrpCat.epi_iff_surjective (S.g.app (op k))).1
        ((shortExact_eval (S := S) (n := k) hS).epi_g)
    obtain ⟨bk', hbk'⟩ := hsurj_gk zk
    let diff : S.X₂.obj (op cA) :=
      (S.X₂.transitionMap hcA).hom bc - (S.X₂.transitionMap (Nat.le_trans hcA hck)).hom bk'
    have hnat_c_mor :
        S.X₂.transitionMap hcA ≫ S.g.app (op cA) =
          S.g.app (op c) ≫ S.X₃.transitionMap hcA := by
      simpa [SequentialInverseSystem.transitionMap] using
        S.g.naturality ((homOfLE hcA).op)
    have hnat_c := congrArg
      (fun t ↦ (ConcreteCategory.hom t) bc)
      hnat_c_mor
    have hnat_k_mor :
        S.X₂.transitionMap (Nat.le_trans hcA hck) ≫ S.g.app (op cA) =
          S.g.app (op k) ≫ S.X₃.transitionMap (Nat.le_trans hcA hck) := by
      simpa [SequentialInverseSystem.transitionMap] using
        S.g.naturality ((homOfLE (Nat.le_trans hcA hck)).op)
    have hnat_k := congrArg
      (fun t ↦ (ConcreteCategory.hom t) bk')
      hnat_k_mor
    have hzero_diff : (S.g.app (op cA)).hom diff = 0 := by
      have hnat_c' :
          (S.g.app (op cA)).hom ((S.X₂.transitionMap hcA).hom bc) = zcA := by
        simpa [zcA, Category.assoc] using hnat_c
      have hnat_k' :
          (S.g.app (op cA)).hom ((S.X₂.transitionMap (Nat.le_trans hcA hck)).hom bk') = zcA := by
        simpa [zcA, hbk', hzk, Category.assoc] using hnat_k
      simp [diff, map_sub, hnat_c', hnat_k']
    have hExact_cA : Function.Exact (S.f.app (op cA)).hom (S.g.app (op cA)).hom :=
      shortExact_eval_function_exact (S := S) (n := cA) hS
    have hdiff_mem :
        diff ∈ Set.range (S.f.app (op cA)).hom := (hExact_cA diff).1 hzero_diff
    obtain ⟨acA, hacA⟩ := hdiff_mem
    have hA_mem :
        (S.X₁.transitionMap hicA).hom acA ∈
          Set.range ((S.X₁.transitionMap (Nat.le_trans hicA hkA)).hom) := by
      have hArange :
          Set.range ((S.X₁.transitionMap (Nat.le_trans hicA hkA)).hom) =
            Set.range ((S.X₁.transitionMap hicA).hom) := by
        exact range_eq_of_imageSubobject_eq (hAstable hkA)
      rw [hArange]
      exact ⟨acA, rfl⟩
    obtain ⟨ak, hak⟩ := hA_mem
    have hnat_f_cA_mor :
        S.X₁.transitionMap hicA ≫ S.f.app (op i) =
          S.f.app (op cA) ≫ S.X₂.transitionMap hicA := by
      simpa [SequentialInverseSystem.transitionMap] using
        S.f.naturality ((homOfLE hicA).op)
    have hnat_f_cA := congrArg
      (fun t ↦ (ConcreteCategory.hom t) acA)
      hnat_f_cA_mor
    have hEq1 :
        (S.f.app (op i)).hom ((S.X₁.transitionMap hicA).hom acA) =
          (S.X₂.transitionMap hic).hom bc -
            (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' := by
      calc
        (S.f.app (op i)).hom ((S.X₁.transitionMap hicA).hom acA)
            = (S.X₂.transitionMap hicA).hom ((S.f.app (op cA)).hom acA) := by
                simpa [Category.assoc] using hnat_f_cA
        _ = (S.X₂.transitionMap hicA).hom diff := by
              rw [hacA]
        _ = (S.X₂.transitionMap hicA).hom ((S.X₂.transitionMap hcA).hom bc) -
              (S.X₂.transitionMap hicA).hom
                ((S.X₂.transitionMap (Nat.le_trans hcA hck)).hom bk') := by
              simp [diff, map_sub]
        _ = (S.X₂.transitionMap hic).hom bc -
              (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' := by
              have hcomp_c :
                  (S.X₂.transitionMap hicA).hom ((S.X₂.transitionMap hcA).hom bc) =
                    (S.X₂.transitionMap hic).hom bc := by
                have hcomp := congrArg
                  (fun t ↦ t.hom bc)
                  (transitionMap_comp S.X₂ hicA hcA)
                simpa [hic, Category.assoc] using hcomp.symm
              have hcomp_k :
                  (S.X₂.transitionMap hicA).hom
                      ((S.X₂.transitionMap (Nat.le_trans hcA hck)).hom bk') =
                    (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' := by
                have hcomp := congrArg
                  (fun t ↦ t.hom bk')
                  (transitionMap_comp S.X₂ hicA (Nat.le_trans hcA hck))
                simpa [hic, Category.assoc] using hcomp.symm
              rw [hcomp_c, hcomp_k]
    have hsum :
        (S.X₂.transitionMap hic).hom bc =
          (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' +
            (S.f.app (op i)).hom ((S.X₁.transitionMap hicA).hom acA) := by
      rw [eq_sub_iff_add_eq] at hEq1
      simpa [add_comm, add_left_comm, add_assoc] using hEq1.symm
    have hnat_f_k_mor :
        S.X₁.transitionMap (Nat.le_trans hic hck) ≫ S.f.app (op i) =
          S.f.app (op k) ≫ S.X₂.transitionMap (Nat.le_trans hic hck) := by
      simpa [SequentialInverseSystem.transitionMap] using
        S.f.naturality ((homOfLE (Nat.le_trans hic hck)).op)
    have hnat_f_k := congrArg
      (fun t ↦ (ConcreteCategory.hom t) ak)
      hnat_f_k_mor
    have hmap_ak :
        (S.X₂.transitionMap (Nat.le_trans hic hck)).hom ((S.f.app (op k)).hom ak) =
          (S.f.app (op i)).hom ((S.X₁.transitionMap hicA).hom acA) := by
      have hmap_ak' :
          (S.f.app (op i)).hom ((S.X₁.transitionMap (Nat.le_trans hic hck)).hom ak) =
            (S.X₂.transitionMap (Nat.le_trans hic hck)).hom ((S.f.app (op k)).hom ak) := by
        simpa [Category.assoc] using hnat_f_k
      simpa [hak, hic] using hmap_ak'.symm
    refine ⟨bk' + (S.f.app (op k)).hom ak, ?_⟩
    calc
      (S.X₂.transitionMap (Nat.le_trans hic hck)).hom (bk' + (S.f.app (op k)).hom ak)
          = (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' +
              (S.X₂.transitionMap (Nat.le_trans hic hck)).hom ((S.f.app (op k)).hom ak) := by
                simp
      _ = (S.X₂.transitionMap (Nat.le_trans hic hck)).hom bk' +
            (S.f.app (op i)).hom ((S.X₁.transitionMap hicA).hom acA) := by
              rw [hmap_ak]
      _ = (S.X₂.transitionMap hic).hom bc := by
              simpa [add_comm, add_left_comm, add_assoc] using hsum.symm

end

end SequentialInverseSystem

end CategoryTheory
