import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe w u v

/-
Domain-style sampling for Lemma 17.10.2:
- primary domain: quasi-coherent sheaves of modules and their binary direct sums/biproducts;
- inspected owner declarations:
  `SheafOfModules.isQuasicoherent`,
  `SheafOfModules.IsQuasicoherent`,
  `CategoryTheory.ObjectProperty.IsClosedUnderBinaryProducts`,
  `CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan`,
  `CategoryTheory.Limits.BinaryBiproduct.isLimit`,
  `CategoryTheory.HasBinaryBiproduct.of_hasBinaryProduct`;
- best owner abstraction: the canonical object property `SheafOfModules.isQuasicoherent R`;
- primitive data: two quasi-coherent sheaves of modules `M` and `N`;
- derived API: the owner-level binary-product closure instance for
  `SheafOfModules.isQuasicoherent R`, and the source-facing direct-sum statement deduced from it.

Source/core/bridge triage:
- `source-facing`: the binary direct sum of two quasi-coherent modules is quasi-coherent;
- `core/canonical`: the owner predicate `SheafOfModules.isQuasicoherent R` together with its
  binary-product closure instance;
- `bridge/view`: `BinaryBiproduct.isLimit M N`, used only inside the owner-level closure proof.
-/

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ X, HasSheafify (J.over X) AddCommGrpCat.{w}]
variable [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Helper for Lemma 17.10.2: quasi-coherence is preserved by isomorphisms of sheaves of
modules. -/
lemma isQuasicoherent_of_iso
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{w}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M N : SheafOfModules.{w} R} (e : M ≅ N) [M.IsQuasicoherent] :
    N.IsQuasicoherent := by
  rcases IsQuasicoherent.nonempty_quasicoherentData (M := M) with ⟨q⟩
  refine ⟨⟨{
    I := q.I
    X := q.X
    coversTop := q.coversTop
    presentation := ?_
  }⟩⟩
  intro i
  -- Restriction is functorial, so we transport each local presentation across the restricted iso.
  let f : M.over (q.X i) ⟶ N.over (q.X i) :=
    (SheafOfModules.pushforward (𝟙 (R.over (q.X i)))).map e.hom
  exact (q.presentation i).of_isIso f

/-- Helper for Lemma 17.10.2: restriction along a slice object preserves the chosen binary
biproduct. -/
noncomputable def overBiprodIso
    {M N : SheafOfModules.{w} R} [HasBinaryBiproduct M N] (U : C) :
    (M ⊞ N).over U ≅ (M.over U) ⊞ (N.over U) := by
  let F := SheafOfModules.pushforward (R := R) (𝟙 (R.over U))
  letI : F.PreservesZeroMorphisms where
    map_zero X Y := by
      apply SheafOfModules.hom_ext
      ext V x
      rfl
  letI : F.IsLeftAdjoint := inferInstance
  letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  -- Proof comment: the restriction functor is additive and preserves the existing binary
  -- biproduct, so the restricted direct sum is the biproduct of the restricted summands.
  simpa [F] using Functor.mapBiprod F M N

namespace Presentation

/-- Helper for Chap17 Lemma 17 10 2: a morphism that kills the full block-diagonal relation also
kills the left relation block after restricting to the left summand. -/
private lemma leftBlockComp_eq_zero
    {ιA ιB κA κB : Type*} {Z : SheafOfModules.{w} R}
    (fA : free ιA ⟶ free κA) (fB : free ιB ⟶ free κB)
    (k : free (κA ⊕ κB) ⟶ Z)
    (hk :
      ((freeSumIso (R := R) ιA ιB).inv ≫ coprod.map fA fB ≫
          (freeSumIso (R := R) κA κB).hom) ≫ k = 0) :
    fA ≫ freeMap Sum.inl ≫ k = 0 := by
  -- Proof comment: precomposing the assembled relation by the left coproduct inclusion isolates
  -- the left block.
  calc
    fA ≫ freeMap Sum.inl ≫ k = coprod.inl ≫ (freeSumIso (R := R) ιA ιB).hom ≫
        ((freeSumIso (R := R) ιA ιB).inv ≫ coprod.map fA fB ≫
          (freeSumIso (R := R) κA κB).hom) ≫ k := by
          simp [Category.assoc]
    _ = 0 := by simp [hk]

/-- Helper for Chap17 Lemma 17 10 2: a morphism that kills the full block-diagonal relation also
kills the right relation block after restricting to the right summand. -/
private lemma rightBlockComp_eq_zero
    {ιA ιB κA κB : Type*} {Z : SheafOfModules.{w} R}
    (fA : free ιA ⟶ free κA) (fB : free ιB ⟶ free κB)
    (k : free (κA ⊕ κB) ⟶ Z)
    (hk :
      ((freeSumIso (R := R) ιA ιB).inv ≫ coprod.map fA fB ≫
          (freeSumIso (R := R) κA κB).hom) ≫ k = 0) :
    fB ≫ freeMap Sum.inr ≫ k = 0 := by
  -- Proof comment: the same normalization with the right coproduct inclusion isolates the right
  -- block.
  calc
    fB ≫ freeMap Sum.inr ≫ k = coprod.inr ≫ (freeSumIso (R := R) ιA ιB).hom ≫
        ((freeSumIso (R := R) ιA ιB).inv ≫ coprod.map fA fB ≫
          (freeSumIso (R := R) κA κB).hom) ≫ k := by
          simp [Category.assoc]
    _ = 0 := by simp [hk]

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Chap17 Lemma 17 10 2: biproducts of globally presented sheaves of modules are
quasi-coherent. -/
lemma isQuasicoherent_biprod
    {A B : SheafOfModules.{w} R} [HasBinaryBiproduct A B]
    (P : A.Presentation) (Q : B.Presentation) :
    (A ⊞ B).IsQuasicoherent := by
  let fA : free P.relations.I ⟶ free P.generators.I :=
    (freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π
  let fB : free Q.relations.I ⟶ free Q.generators.I :=
    (freeHomEquiv _).symm Q.relations.s ≫ kernel.ι Q.generators.π
  let f :
      free (P.relations.I ⊕ Q.relations.I) ⟶ free (P.generators.I ⊕ Q.generators.I) :=
    (freeSumIso (R := R) P.relations.I Q.relations.I).inv ≫
      coprod.map fA fB ≫
      (freeSumIso (R := R) P.generators.I Q.generators.I).hom
  let g : free (P.generators.I ⊕ Q.generators.I) ⟶ A ⊞ B :=
    (freeSumIso (R := R) P.generators.I Q.generators.I).inv ≫
      coprod.desc (P.generators.π ≫ biprod.inl) (Q.generators.π ≫ biprod.inr)
  have hfg : f ≫ g = 0 := by
    -- Proof comment: after rewriting through `freeSumIso`, the block-diagonal relation map
    -- vanishes on each summand by the two kernel conditions.
    apply (cancel_epi (freeSumIso (R := R) P.relations.I Q.relations.I).hom).1
    apply coprod.hom_ext
    · simp [f, g, fA, Category.assoc]
    · simp [f, g, fB, Category.assoc]
  have hCokernel : IsColimit (CokernelCofork.ofπ g hfg) := by
    -- Proof comment: the descended map is assembled from the two original cokernel descents,
    -- while uniqueness is reduced to the two original cokernel universal properties.
    refine CokernelCofork.IsColimit.ofπ g hfg
      (fun {Z} k hk ↦ by
        let πA : free P.generators.I ⟶ Z := freeMap Sum.inl ≫ k
        let πB : free Q.generators.I ⟶ Z := freeMap Sum.inr ≫ k
        have hπA : fA ≫ πA = 0 := by
          -- Proof comment: the left descent condition is the left-block specialization of `hk`.
          simpa [πA, f] using
            leftBlockComp_eq_zero (R := R) (fA := fA) (fB := fB) (k := k) hk
        have hπB : fB ≫ πB = 0 := by
          -- Proof comment: the right descent condition is the symmetric right-block computation.
          simpa [πB, f] using
            rightBlockComp_eq_zero (R := R) (fA := fA) (fB := fB) (k := k) hk
        exact biprod.desc
          (P.isColimit.desc (CokernelCofork.ofπ πA hπA))
          (Q.isColimit.desc (CokernelCofork.ofπ πB hπB)))
      (fun {Z} k hk ↦ by
        let πA : free P.generators.I ⟶ Z := freeMap Sum.inl ≫ k
        let πB : free Q.generators.I ⟶ Z := freeMap Sum.inr ≫ k
        have hπA : fA ≫ πA = 0 := by
          -- Proof comment: the same left-block normalization supplies the factorization witness.
          simpa [πA, f] using
            leftBlockComp_eq_zero (R := R) (fA := fA) (fB := fB) (k := k) hk
        have hπB : fB ≫ πB = 0 := by
          -- Proof comment: the symmetric right-block normalization gives the second witness.
          simpa [πB, f] using
            rightBlockComp_eq_zero (R := R) (fA := fA) (fB := fB) (k := k) hk
        -- Proof comment: checking the factorization is easiest after precomposing with the two
        -- coproduct injections into the free sum.
        apply (cancel_epi (freeSumIso (R := R) P.generators.I Q.generators.I).hom).1
        apply coprod.hom_ext
        · simpa [g, Category.assoc] using
            (P.isColimit.π_desc (t := CokernelCofork.ofπ πA hπA))
        · simpa [g, Category.assoc] using
            (Q.isColimit.π_desc (t := CokernelCofork.ofπ πB hπB)))
      (fun {Z} k hk m hm ↦ by
        let πA : free P.generators.I ⟶ Z := freeMap Sum.inl ≫ k
        let πB : free Q.generators.I ⟶ Z := freeMap Sum.inr ≫ k
        have hπA : fA ≫ πA = 0 := by
          -- Proof comment: uniqueness again reduces to the left-block specialization of `hk`.
          simpa [πA, f] using
            leftBlockComp_eq_zero (R := R) (fA := fA) (fB := fB) (k := k) hk
        have hπB : fB ≫ πB = 0 := by
          -- Proof comment: the right uniqueness witness is the same symmetric specialization.
          simpa [πB, f] using
            rightBlockComp_eq_zero (R := R) (fA := fA) (fB := fB) (k := k) hk
        apply biprod.hom_ext'
        · apply Cofork.IsColimit.hom_ext P.isColimit
          refine (by
            simpa [g, Category.assoc] using congrArg (fun t => freeMap Sum.inl ≫ t) hm).trans ?_
          simpa [πA] using
            (P.isColimit.π_desc (t := CokernelCofork.ofπ πA hπA)).symm
        · apply Cofork.IsColimit.hom_ext Q.isColimit
          refine (by
            simpa [g, Category.assoc] using congrArg (fun t => freeMap Sum.inr ≫ t) hm).trans ?_
          simpa [πB] using
            (Q.isColimit.π_desc (t := CokernelCofork.ofπ πB hπB)).symm)
  let Psum : (A ⊞ B).Presentation :=
    presentationOfIsCokernelFree f g hfg hCokernel
  -- Proof comment: the block-diagonal cokernel presentation gives quasi-coherence on the trivial
  -- cover.
  exact Psum.isQuasicoherent

end Presentation

/-- Helper for Lemma 17.10.2: if the left summand has a fixed presentation and the right summand
is quasi-coherent, then their biproduct is quasi-coherent. -/
lemma biprod_isQuasicoherent_ofPresentationLeft
    {C : Type u} [Category.{v} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{w}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {A B : SheafOfModules.{w} R} [HasBinaryBiproduct A B]
    (P : A.Presentation) [B.IsQuasicoherent] :
    (A ⊞ B).IsQuasicoherent := by
  letI (X : C) (Y : Over X) : ((J.over X).over Y).HasSheafCompose
      (forget₂ RingCat.{w} AddCommGrpCat.{w}) :=
    hasSheafComposeEssentiallySmallSite ((J.over X).over Y) RingCat.{w} AddCommGrpCat.{w}
      (forget₂ RingCat.{w} AddCommGrpCat.{w})
  letI (X : C) (Y : Over X) : HasSheafify ((J.over X).over Y) AddCommGrpCat.{w} :=
    hasSheafifyEssentiallySmallSite ((J.over X).over Y) AddCommGrpCat.{w}
  letI (X : C) (Y : Over X) :
      ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{w} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let qB := (IsQuasicoherent.nonempty_quasicoherentData (M := B)).some.shrink
  refine IsQuasicoherent.of_coversTop (M := A ⊞ B) qB.X qB.coversTop
  intro i
  let PA : (A.over (qB.X i)).Presentation :=
    P.map (pushforward (𝟙 (R.over (qB.X i)))) (by rfl)
  let e := overBiprodIso (R := R) (M := A) (N := B) (qB.X i)
  have hlocal : ((A.over (qB.X i)) ⊞ (B.over (qB.X i))).IsQuasicoherent :=
    Presentation.isQuasicoherent_biprod (R := R.over (qB.X i)) PA (qB.presentation i)
  -- Proof comment: each chart carries the direct sum of two explicit presentations, and the
  -- restriction of the ambient biproduct is canonically that chartwise biproduct.
  letI : ((A.over (qB.X i)) ⊞ (B.over (qB.X i))).IsQuasicoherent := hlocal
  exact isQuasicoherent_of_iso e.symm

/-- Helper for Lemma 17.10.2: the biproduct of two quasi-coherent sheaves of modules is
quasi-coherent. -/
lemma biprod_isQuasicoherent
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{w}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M N : SheafOfModules.{w} R} [HasBinaryBiproduct M N]
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent := by
  letI (X : C) (Y : Over X) : ((J.over X).over Y).HasSheafCompose
      (forget₂ RingCat.{w} AddCommGrpCat.{w}) :=
    hasSheafComposeEssentiallySmallSite ((J.over X).over Y) RingCat.{w} AddCommGrpCat.{w}
      (forget₂ RingCat.{w} AddCommGrpCat.{w})
  letI (X : C) (Y : Over X) : HasSheafify ((J.over X).over Y) AddCommGrpCat.{w} :=
    hasSheafifyEssentiallySmallSite ((J.over X).over Y) AddCommGrpCat.{w}
  letI (X : C) (Y : Over X) :
      ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{w} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let qM := (IsQuasicoherent.nonempty_quasicoherentData (M := M)).some.shrink
  refine IsQuasicoherent.of_coversTop (M := M ⊞ N) qM.X qM.coversTop
  intro i
  letI : (N.over (qM.X i)).IsQuasicoherent := inferInstance
  let e := overBiprodIso (R := R) (M := M) (N := N) (qM.X i)
  -- Route correction: the previous `infer_instance` route was circular through the later owner
  -- instance, so we first pass to a fixed quasi-coherent cover of `M`.
  have hlocal : ((M.over (qM.X i)) ⊞ (N.over (qM.X i))).IsQuasicoherent :=
    biprod_isQuasicoherent_ofPresentationLeft
      (C := Over (qM.X i)) (J := J.over (qM.X i)) (R := R.over (qM.X i))
      (A := M.over (qM.X i)) (B := N.over (qM.X i)) (P := qM.presentation i)
  -- Proof comment: transport the chartwise direct-sum presentation back to the restriction of the
  -- ambient biproduct by the canonical restriction/biproduct isomorphism.
  letI : ((M.over (qM.X i)) ⊞ (N.over (qM.X i))).IsQuasicoherent := hlocal
  exact isQuasicoherent_of_iso e.symm

/- Lemma 17.10.2: the direct sum of two quasi-coherent `\mathcal O_X`-modules is
quasi-coherent. -/
omit [HasBinaryProducts C] [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
lemma isQuasicoherent_biprod
    {M N : SheafOfModules.{w} R} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent := by
  simpa using biprod_isQuasicoherent (M := M) (N := N)

omit [HasBinaryProducts C] [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
instance instIsQuasicoherentBiprod
    {M N : SheafOfModules.{w} R} [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent :=
  isQuasicoherent_biprod

end SheafOfModules
