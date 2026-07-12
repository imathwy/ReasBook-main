import Mathlib
import StacksProject_2024.Chap12.Definition_12_14_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v u

open CategoryTheory HomologicalComplex
open HomologicalComplex.homotopyCofiber

variable {R : Type u} [CommRing R]

/- Domain-style sampling:
- primary domain: mapping-cone / homotopy-cofiber constructions in the homotopy category of chain
  complexes;
- owner declarations inspected: `HomologicalComplex.homotopyCofiber`,
  `HomotopyEquiv`, `HomologicalComplex.homotopyEquivalences`, and the chapter recall
  `Definition_12_13_2`;
- best owner abstraction: the canonical cone object `homotopyCofiber` together with the canonical
  homotopy-equivalence owner/bridge pair `HomotopyEquiv` and `homotopyEquivalences`.

Primitive data are only the chain complex `A` and the scalar endomorphisms `f • 𝟙 A`,
`g • 𝟙 A`, and `(f * g) • 𝟙 A`. The morphism
`(homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧ ⟶ homotopyCofiber (g • 𝟙 A)` is source-facing bridge data,
and the resulting morphism from `homotopyCofiber ((f * g) • 𝟙 A)` to the cone of that morphism
being a homotopy equivalence is derived API, not primitive owner data.

Layer triage:
- `core/canonical`: `homotopyCofiber` and `HomotopyEquiv`;
- `bridge/view`: the source-facing assertion that there exists some comparison morphism whose cone
  is homotopy equivalent to the cone of multiplication by `f * g`.
-/

-- Proof sketch: first treat the two-term complex `R ⟶ R`, where there is an explicit morphism
-- from the shifted cone of multiplication by `f` to the cone of multiplication by `g` whose cone
-- is homotopy equivalent to the cone of multiplication by `f * g`. Then tensor that explicit
-- two-term construction with `A` and pass to the total complex, using compatibility of
-- totalization with cones and homotopies.
/-- Helper for Lemma 15.28.9: the predecessor relation in `ComplexShape.down ℤ` needed for
textbook cone coordinates. -/
private lemma cone_downRel (n : ℤ) : (ComplexShape.down ℤ).Rel n (n - 1) :=
  ComplexShape.down_mk n (n - 1) (sub_add_cancel n 1)

/-- Helper for Lemma 15.28.9: `ComplexShape.down` chooses the expected predecessor `n - 1`. -/
private lemma cone_down_next (n : ℤ) : (ComplexShape.down ℤ).next n = n - 1 := by
  -- Every degree has the predecessor `n - 1`, and `ComplexShape.next_eq` makes that predecessor
  -- unique in the `down` shape.
  rw [ComplexShape.next, dif_pos ⟨n - 1, cone_downRel n⟩]
  exact
    ComplexShape.next_eq (self := ComplexShape.down ℤ)
      (Exists.choose_spec ⟨n - 1, cone_downRel n⟩) (cone_downRel n)

/-- Helper for Lemma 15.28.9: the degree-`n` term of the cone of a chain map in textbook order
`B.X n ⊞ A.X (n - 1)`. -/
private noncomputable def chainMapConeTextbookXIso
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    (homotopyCofiber φ).X n ≅ B.X n ⊞ A.X (n - 1) :=
  XIsoBiprod φ n (n - 1) (cone_downRel n) ≪≫
    Limits.biprod.braiding (A.X (n - 1)) (B.X n)

/-- Helper for Lemma 15.28.9: the inverse braiding sends the textbook left summand to the
owner right summand. -/
@[simp] private lemma biprod_braiding_inv_inl
    {X Y : ModuleCat R} [Limits.HasBinaryBiproduct X Y] :
    Limits.biprod.inl ≫ (Limits.biprod.braiding X Y).inv = (Limits.biprod.inr : Y ⟶ X ⊞ Y) := by
  -- Verify the two projections out of `X ⊞ Y`.
  apply Limits.biprod.hom_ext <;> simp [Category.assoc]

/-- Helper for Lemma 15.28.9: the inverse braiding sends the textbook right summand to the
owner left summand. -/
@[simp] private lemma biprod_braiding_inv_inr
    {X Y : ModuleCat R} [Limits.HasBinaryBiproduct X Y] :
    Limits.biprod.inr ≫ (Limits.biprod.braiding X Y).inv = (Limits.biprod.inl : X ⟶ X ⊞ Y) := by
  -- Verify the two projections out of `X ⊞ Y`.
  apply Limits.biprod.hom_ext <;> simp [Category.assoc]

/-- Helper for Lemma 15.28.9: the braiding sends the owner first projection to the textbook
second projection. -/
@[simp] private lemma biprod_braiding_hom_fst
    {X Y : ModuleCat R} [Limits.HasBinaryBiproduct X Y] :
    (Limits.biprod.braiding X Y).hom ≫ Limits.biprod.fst = (Limits.biprod.snd : X ⊞ Y ⟶ Y) := by
  -- Unfold the braiding and evaluate the first projection.
  simp

/-- Helper for Lemma 15.28.9: the braiding sends the owner second projection to the textbook
first projection. -/
@[simp] private lemma biprod_braiding_hom_snd
    {X Y : ModuleCat R} [Limits.HasBinaryBiproduct X Y] :
    (Limits.biprod.braiding X Y).hom ≫ Limits.biprod.snd = (Limits.biprod.fst : X ⊞ Y ⟶ X) := by
  -- Unfold the braiding and evaluate the second projection.
  simp

/-- Helper for Lemma 15.28.9: postcomposing with `eqToHom` is proof-irrelevant. -/
private lemma comp_eqToHom_eq
    {C : Type*} [Category C] {X Y Z : C} (f : Z ⟶ X) (p q : X = Y) :
    f ≫ eqToHom p = f ≫ eqToHom q := by
  cases p
  cases q
  rfl

/-- Helper for Lemma 15.28.9: transporting a cone differential across an equality of target
degrees only changes the endpoint `eqToHom`. -/
private lemma homotopyCofiber_d_comp_eqToHom_of_index_eq
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (i j j' : ℤ) (h : j = j') :
    (homotopyCofiber φ).d i j ≫
        eqToHom (congrArg (fun k ↦ (homotopyCofiber φ).X k) h) =
      (homotopyCofiber φ).d i j' := by
  -- Once the endpoint equality becomes literal, the transport is the identity map.
  cases h
  simp

/-- Helper for Lemma 15.28.9: precomposing with `eqToHom` is proof-irrelevant. -/
private lemma eqToHom_comp_eq
    {C : Type*} [Category C] {X Y Z : C} (p q : X = Y) (f : Y ⟶ Z) :
    eqToHom p ≫ f = eqToHom q ≫ f := by
  cases p
  cases q
  rfl

/-- Helper for Lemma 15.28.9: in `ComplexShape.down`, `inrX` is the owner right inclusion at the
actual predecessor `next n`. -/
private lemma inrX_eq_XIsoBiprod_inv_inr_next
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    homotopyCofiber.inrX φ n =
      Limits.biprod.inr ≫
        (XIsoBiprod φ n ((ComplexShape.down ℤ).next n)
          (by
            -- The `down` shape always has the predecessor `n - 1`.
            rw [cone_down_next]
            exact cone_downRel n)).inv := by
  -- Unfold `inrX`; in the `down` shape the `if`-branch is always the biproduct branch.
  have hrel : (ComplexShape.down ℤ).Rel n ((ComplexShape.down ℤ).next n) := by
    rw [cone_down_next]
    exact cone_downRel n
  rw [homotopyCofiber.inrX, dif_pos hrel]

/-- Helper for Lemma 15.28.9: in `ComplexShape.down`, `sndX` is the owner second projection at the
actual predecessor `next n`. -/
private lemma sndX_eq_XIsoBiprod_hom_snd_next
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    homotopyCofiber.sndX φ n =
      (XIsoBiprod φ n ((ComplexShape.down ℤ).next n)
        (by
          -- The same predecessor relation identifies the degree used by `sndX`.
          rw [cone_down_next]
          exact cone_downRel n)).hom ≫ Limits.biprod.snd := by
  -- Unfold `sndX`; again the `down` shape lands in the biproduct branch.
  have hrel : (ComplexShape.down ℤ).Rel n ((ComplexShape.down ℤ).next n) := by
    rw [cone_down_next]
    exact cone_downRel n
  rw [homotopyCofiber.sndX, dif_pos hrel]

/-- Helper for Lemma 15.28.9: the predecessor selected by `ComplexShape.down.next` satisfies the
downward relation from degree `n`. -/
private lemma cone_down_next_rel (n : ℤ) : (ComplexShape.down ℤ).Rel n ((ComplexShape.down ℤ).next n) := by
  rw [cone_down_next]
  exact cone_downRel n

/-- Helper for Lemma 15.28.9: textbook `inr` becomes the owner inclusion of the shifted summand. -/
@[simp] private lemma chainMapConeTextbookXIso_inv_inr
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    Limits.biprod.inr ≫ (chainMapConeTextbookXIso φ n).inv =
      homotopyCofiber.inlX φ (n - 1) n (cone_downRel n) := by
  -- Expand the textbook coordinate isomorphism and swap the two cone summands by the braiding.
  calc
    Limits.biprod.inr ≫ (chainMapConeTextbookXIso φ n).inv =
        Limits.biprod.inr ≫ (Limits.biprod.braiding (A.X (n - 1)) (B.X n)).inv ≫
          (XIsoBiprod φ n (n - 1) (cone_downRel n)).inv := by
        simp [chainMapConeTextbookXIso]
    _ = Limits.biprod.inl ≫ (XIsoBiprod φ n (n - 1) (cone_downRel n)).inv := by
        exact congrArg (fun k ↦ k ≫ (XIsoBiprod φ n (n - 1) (cone_downRel n)).inv)
          (biprod_braiding_inv_inr (X := A.X (n - 1)) (Y := B.X n))
    _ = homotopyCofiber.inlX φ (n - 1) n (cone_downRel n) := by
        simp [homotopyCofiber.inlX, HomologicalComplex.homotopyCofiber.XIsoBiprod]

/-- Helper for Lemma 15.28.9: the textbook second projection is the owner projection to `A`. -/
@[simp] private lemma chainMapConeTextbookXIso_hom_snd
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    (chainMapConeTextbookXIso φ n).hom ≫ Limits.biprod.snd =
      homotopyCofiber.fstX φ n (n - 1) (cone_downRel n) := by
  -- Expand the textbook coordinate isomorphism and swap the two cone summands by the braiding.
  calc
    (chainMapConeTextbookXIso φ n).hom ≫ Limits.biprod.snd =
        (XIsoBiprod φ n (n - 1) (cone_downRel n)).hom ≫
          (Limits.biprod.braiding (A.X (n - 1)) (B.X n)).hom ≫ Limits.biprod.snd := by
        simp [chainMapConeTextbookXIso, Category.assoc]
    _ = (XIsoBiprod φ n (n - 1) (cone_downRel n)).hom ≫ Limits.biprod.fst := by
        exact congrArg (fun k ↦ (XIsoBiprod φ n (n - 1) (cone_downRel n)).hom ≫ k)
          (biprod_braiding_hom_snd (X := A.X (n - 1)) (Y := B.X n))
    _ = homotopyCofiber.fstX φ n (n - 1) (cone_downRel n) := by
        simp [homotopyCofiber.fstX, HomologicalComplex.homotopyCofiber.XIsoBiprod]

/-- Helper for Lemma 15.28.9: the owner left summand includes into the cone via `inlX`. -/
@[reassoc (attr := simp)] private lemma XIsoBiprod_inv_inl
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    Limits.biprod.inl ≫ (XIsoBiprod φ n (n - 1) (cone_downRel n)).inv =
      homotopyCofiber.inlX φ (n - 1) n (cone_downRel n) := by
  -- In owner order, the left summand is definitionally the `inlX` inclusion.
  simp [homotopyCofiber.inlX, HomologicalComplex.homotopyCofiber.XIsoBiprod]

/-- Helper for Lemma 15.28.9: the owner inclusion composite is unchanged when the predecessor
index is transported from `n - 1` to `ComplexShape.down.next n`. -/
private lemma XIsoBiprod_inv_inr_transport_down_next
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    Limits.biprod.inr ≫ (XIsoBiprod φ n (n - 1) (cone_downRel n)).inv =
      Limits.biprod.inr ≫
        (XIsoBiprod φ n ((ComplexShape.down ℤ).next n) (cone_down_next_rel n)).inv := by
  -- Unfold `XIsoBiprod` to `eqToIso`, then compare both composites through the same inclusion.
  simp [HomologicalComplex.homotopyCofiber.XIsoBiprod]
  apply eq_of_heq
  have hleft :
      HEq
        (Limits.biprod.inr ≫
          eqToHom
            (HomologicalComplex.homotopyCofiber.XIsoBiprod._proof_1 φ n (n - 1)
              (cone_downRel n)).symm)
        (Limits.biprod.inr : B.X n ⟶ A.X (n - 1) ⊞ B.X n) := by
    -- Postcomposing with `eqToHom` is heterogeneously equal to the underlying inclusion.
    simpa using
      (CategoryTheory.comp_eqToHom_heq
        (f := (Limits.biprod.inr : B.X n ⟶ A.X (n - 1) ⊞ B.X n))
        (h := (HomologicalComplex.homotopyCofiber.XIsoBiprod._proof_1 φ n (n - 1)
          (cone_downRel n)).symm))
  have hright :
      HEq
        (Limits.biprod.inr ≫
          eqToHom
            (HomologicalComplex.homotopyCofiber.XIsoBiprod._proof_1 φ n
              ((ComplexShape.down ℤ).next n) (cone_down_next_rel n)).symm)
        (Limits.biprod.inr : B.X n ⟶ A.X ((ComplexShape.down ℤ).next n) ⊞ B.X n) := by
    -- The same normalization applies to the owner `next n` presentation.
    simpa using
      (CategoryTheory.comp_eqToHom_heq
        (f := (Limits.biprod.inr : B.X n ⟶ A.X ((ComplexShape.down ℤ).next n) ⊞ B.X n))
        (h := (HomologicalComplex.homotopyCofiber.XIsoBiprod._proof_1 φ n
          ((ComplexShape.down ℤ).next n) (cone_down_next_rel n)).symm))
  have hmid :
      HEq
        (Limits.biprod.inr : B.X n ⟶ A.X (n - 1) ⊞ B.X n)
        (Limits.biprod.inr : B.X n ⟶ A.X ((ComplexShape.down ℤ).next n) ⊞ B.X n) := by
    -- Only the left cone summand changes, so transport along `A.X (n - 1) = A.X (next n)`.
    have hA : A.X (n - 1) = A.X ((ComplexShape.down ℤ).next n) := by
      simpa using congrArg A.X (cone_down_next n).symm
    refine Eq.rec ?_ hA
    exact HEq.rfl
  exact hleft.trans (hmid.trans hright.symm)

/-- Helper for Lemma 15.28.9: the owner right summand includes into the cone via `inrX`. -/
@[reassoc (attr := simp)] private lemma XIsoBiprod_inv_inr
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    Limits.biprod.inr ≫ (XIsoBiprod φ n (n - 1) (cone_downRel n)).inv =
      homotopyCofiber.inrX φ n := by
  -- Route correction: `inrX_eq_XIsoBiprod_inv_inr_next` already identifies the owner inclusion at
  -- the canonical predecessor `next n`; the only remaining gap is transporting that formula to
  -- the explicit textbook index `n - 1`.
  calc
    Limits.biprod.inr ≫ (XIsoBiprod φ n (n - 1) (cone_downRel n)).inv =
        Limits.biprod.inr ≫
          (XIsoBiprod φ n ((ComplexShape.down ℤ).next n) (cone_down_next_rel n)).inv := by
          -- First normalize the predecessor transport in `XIsoBiprod`.
          simpa using XIsoBiprod_inv_inr_transport_down_next (φ := φ) n
    _ = homotopyCofiber.inrX φ n := by
          -- Then apply the owner formula at the canonical predecessor `next n`.
          simpa using (inrX_eq_XIsoBiprod_inv_inr_next (φ := φ) n).symm

/-- Helper for Lemma 15.28.9: the owner first projection out of the cone is `fstX`. -/
@[reassoc (attr := simp)] private lemma XIsoBiprod_hom_fst
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    (XIsoBiprod φ n (n - 1) (cone_downRel n)).hom ≫ Limits.biprod.fst =
      homotopyCofiber.fstX φ n (n - 1) (cone_downRel n) := by
  -- The first owner projection is exactly `fstX`.
  simp [homotopyCofiber.fstX, HomologicalComplex.homotopyCofiber.XIsoBiprod]

/-- Helper for Lemma 15.28.9: the owner projection composite is unchanged when the predecessor
index is transported from `n - 1` to `ComplexShape.down.next n`. -/
private lemma XIsoBiprod_hom_snd_transport_down_next
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    (XIsoBiprod φ n (n - 1) (cone_downRel n)).hom ≫ Limits.biprod.snd =
      (XIsoBiprod φ n ((ComplexShape.down ℤ).next n) (cone_down_next_rel n)).hom ≫
        Limits.biprod.snd := by
  -- Unfold `XIsoBiprod` to `eqToIso`, then compare both projections through the same output map.
  simp [HomologicalComplex.homotopyCofiber.XIsoBiprod]
  apply eq_of_heq
  have hleft :
      HEq
        (eqToHom
            (HomologicalComplex.homotopyCofiber.XIsoBiprod._proof_1 φ n (n - 1)
              (cone_downRel n)) ≫
          (Limits.biprod.snd : A.X (n - 1) ⊞ B.X n ⟶ B.X n))
        (Limits.biprod.snd : A.X (n - 1) ⊞ B.X n ⟶ B.X n) := by
    -- Precomposing with `eqToHom` is heterogeneously equal to the underlying projection.
    simpa using
      (CategoryTheory.eqToHom_comp_heq
        (f := (Limits.biprod.snd : A.X (n - 1) ⊞ B.X n ⟶ B.X n))
        (h := HomologicalComplex.homotopyCofiber.XIsoBiprod._proof_1 φ n (n - 1)
          (cone_downRel n)))
  have hright :
      HEq
        (eqToHom
            (HomologicalComplex.homotopyCofiber.XIsoBiprod._proof_1 φ n
              ((ComplexShape.down ℤ).next n) (cone_down_next_rel n)) ≫
          (Limits.biprod.snd : A.X ((ComplexShape.down ℤ).next n) ⊞ B.X n ⟶ B.X n))
        (Limits.biprod.snd : A.X ((ComplexShape.down ℤ).next n) ⊞ B.X n ⟶ B.X n) := by
    -- The same normalization applies to the owner `next n` presentation.
    simpa using
      (CategoryTheory.eqToHom_comp_heq
        (f := (Limits.biprod.snd : A.X ((ComplexShape.down ℤ).next n) ⊞ B.X n ⟶ B.X n))
        (h := HomologicalComplex.homotopyCofiber.XIsoBiprod._proof_1 φ n
          ((ComplexShape.down ℤ).next n) (cone_down_next_rel n)))
  have hmid :
      HEq
        (Limits.biprod.snd : A.X (n - 1) ⊞ B.X n ⟶ B.X n)
        (Limits.biprod.snd : A.X ((ComplexShape.down ℤ).next n) ⊞ B.X n ⟶ B.X n) := by
    -- Only the left cone summand changes, so transport along `A.X (n - 1) = A.X (next n)`.
    have hA : A.X (n - 1) = A.X ((ComplexShape.down ℤ).next n) := by
      simpa using congrArg A.X (cone_down_next n).symm
    refine Eq.rec ?_ hA
    exact HEq.rfl
  exact hleft.trans (hmid.trans hright.symm)

/-- Helper for Lemma 15.28.9: the owner second projection out of the cone is `sndX`. -/
@[reassoc (attr := simp)] private lemma XIsoBiprod_hom_snd
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    (XIsoBiprod φ n (n - 1) (cone_downRel n)).hom ≫ Limits.biprod.snd =
      homotopyCofiber.sndX φ n := by
  -- Route correction: `sndX_eq_XIsoBiprod_hom_snd_next` already gives the owner projection at
  -- the canonical predecessor `next n`; the remaining work is the same transport to `n - 1`.
  calc
    (XIsoBiprod φ n (n - 1) (cone_downRel n)).hom ≫ Limits.biprod.snd =
        (XIsoBiprod φ n ((ComplexShape.down ℤ).next n) (cone_down_next_rel n)).hom ≫
          Limits.biprod.snd := by
          -- First normalize the predecessor transport in `XIsoBiprod`.
          simpa using XIsoBiprod_hom_snd_transport_down_next (φ := φ) n
    _ = homotopyCofiber.sndX φ n := by
          -- Then apply the owner formula at the canonical predecessor `next n`.
          simpa using (sndX_eq_XIsoBiprod_hom_snd_next (φ := φ) n).symm

/-- Helper for Lemma 15.28.9: the cone differential in owner `XIsoBiprod` coordinates.

Route correction: the previous textbook-first route got stuck on `ComplexShape.next` transport in
`homotopyCofiber.inrX` and `homotopyCofiber.sndX`, so the proof now follows the source-faithful
owner order first and braids to textbook order only afterward. -/
private theorem chainMap_cone_d_eq_ofComponents_owner_local
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
    (XIsoBiprod φ n (n - 1) (cone_downRel n)).inv ≫ (homotopyCofiber φ).d n (n - 1) ≫
        (XIsoBiprod φ (n - 1) ((n - 1) - 1) (cone_downRel (n - 1))).hom =
      Biprod.ofComponents (-A.d (n - 1) ((n - 1) - 1)) (φ.f (n - 1)) 0 (B.d n (n - 1)) := by
  -- `biprod.hom_ext` and `biprod.hom_ext'` reduce the matrix identity to its four entries.
  apply Limits.biprod.hom_ext <;> apply Limits.biprod.hom_ext'
  · -- The `A`-to-`A` entry is the negative differential on the shifted summand.
    simpa [Category.assoc,
      homotopyCofiber.inlX_d_assoc φ n (n - 1) ((n - 1) - 1)
        (cone_downRel n) (cone_downRel (n - 1))]
  · -- The `B`-to-`A` entry vanishes because `inrX` lands in the right cone summand.
    simpa [Category.assoc, homotopyCofiber.inrX_d_assoc (φ := φ) n (n - 1)]
  · -- The `A`-to-`B` entry is exactly the structure map `φ`.
    simpa [Category.assoc,
      homotopyCofiber.inlX_d_assoc φ n (n - 1) ((n - 1) - 1)
        (cone_downRel n) (cone_downRel (n - 1))]
  · -- The `B`-to-`B` entry is the target differential.
    simpa [Category.assoc, homotopyCofiber.inrX_d_assoc (φ := φ) n (n - 1)]

/-- Helper for Lemma 15.28.9: the cone differential in textbook coordinates.

Route correction: the source-faithful owner theorem already exists in `15.28.6.1`, but the
current readonly Lake state does not provide the corresponding `.olean`, so this file keeps a
local copy of the same coordinate statement until the canonical import path is buildable again. -/
private theorem chainMap_cone_d_eq_ofComponents
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) (n : ℤ) :
      (chainMapConeTextbookXIso φ n).inv ≫ (homotopyCofiber φ).d n (n - 1) ≫
        (chainMapConeTextbookXIso φ (n - 1)).hom =
      Biprod.ofComponents (B.d n (n - 1)) 0 (φ.f (n - 1))
        (-A.d (n - 1) ((n - 1) - 1)) := by
  -- Conjugate the owner-order block matrix by the biproduct braiding to recover textbook order.
  calc
    (chainMapConeTextbookXIso φ n).inv ≫ (homotopyCofiber φ).d n (n - 1) ≫
        (chainMapConeTextbookXIso φ (n - 1)).hom =
      (Limits.biprod.braiding (A.X (n - 1)) (B.X n)).inv ≫
          ((XIsoBiprod φ n (n - 1) (cone_downRel n)).inv ≫
            (homotopyCofiber φ).d n (n - 1) ≫
            (XIsoBiprod φ (n - 1) ((n - 1) - 1) (cone_downRel (n - 1))).hom) ≫
          (Limits.biprod.braiding (A.X ((n - 1) - 1)) (B.X (n - 1))).hom := by
        simp [chainMapConeTextbookXIso, Category.assoc]
    _ =
      (Limits.biprod.braiding (A.X (n - 1)) (B.X n)).inv ≫
          Biprod.ofComponents (-A.d (n - 1) ((n - 1) - 1)) (φ.f (n - 1)) 0
            (B.d n (n - 1)) ≫
          (Limits.biprod.braiding (A.X ((n - 1) - 1)) (B.X (n - 1))).hom := by
        rw [chainMap_cone_d_eq_ofComponents_owner_local]
    _ =
      Biprod.ofComponents (B.d n (n - 1)) 0 (φ.f (n - 1))
        (-A.d (n - 1) ((n - 1) - 1)) := by
        rw [← Biprod.ofComponents_eq
          ((Limits.biprod.braiding (A.X (n - 1)) (B.X n)).inv ≫
            Biprod.ofComponents (-A.d (n - 1) ((n - 1) - 1)) (φ.f (n - 1)) 0
              (B.d n (n - 1)) ≫
            (Limits.biprod.braiding (A.X ((n - 1) - 1)) (B.X (n - 1))).hom)]
        ext <;> simp

/-- Helper for Lemma 15.28.9: every degree in a chain complex has a predecessor in
`ComplexShape.down ℤ`, so the generic `homotopyCofiber.desc` API applies. -/
private lemma chain_down_exists (j : ℤ) : ∃ i, (ComplexShape.down ℤ).Rel i j := by
  refine ⟨j + 1, ?_⟩
  exact ComplexShape.down_mk (j + 1) j (by omega)

/-- Helper for Lemma 15.28.9: the comparison map `C(g) ⟶ C(fg)` is obtained from the
owner inclusion `A ⟶ C(fg)` after precomposing with multiplication by `f`. -/
private noncomputable def smul_mul_homotopyCofiber_factor_left_homotopy
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    Homotopy
      ((g • 𝟙 A) ≫ ((f • 𝟙 A) ≫ homotopyCofiber.inr ((f * g) • 𝟙 A)))
      0 := by
  -- Rewrite the scalar composite to multiplication by `f * g`, then invoke the owner null-homotopy.
  have hcomp :
      (g • 𝟙 A) ≫ ((f • 𝟙 A) ≫ homotopyCofiber.inr ((f * g) • 𝟙 A)) =
        ((f * g) • 𝟙 A) ≫ homotopyCofiber.inr ((f * g) • 𝟙 A) := by
    simp [smul_smul]
  exact
    (Homotopy.ofEq hcomp).trans
      (homotopyCofiber.inrCompHomotopy ((f * g) • 𝟙 A) chain_down_exists)

/-- Helper for Lemma 15.28.9: the left comparison map in the octahedral factorization
`C(g) ⟶ C(fg) ⟶ C(f)`. -/
noncomputable def smul_mul_homotopyCofiber_factor_left
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    homotopyCofiber (g • 𝟙 A) ⟶ homotopyCofiber ((f * g) • 𝟙 A) :=
  homotopyCofiber.desc (g • 𝟙 A)
    ((f • 𝟙 A) ≫ homotopyCofiber.inr ((f * g) • 𝟙 A))
    (smul_mul_homotopyCofiber_factor_left_homotopy A f g)

/-- Helper for Lemma 15.28.9: the right comparison map `C(fg) ⟶ C(f)` is obtained from the
owner inclusion `A ⟶ C(f)` by the obvious scalar factorization through `g`. -/
private noncomputable def smul_mul_homotopyCofiber_factor_right_homotopy
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    Homotopy
      (((f * g) • 𝟙 A) ≫ homotopyCofiber.inr (f • 𝟙 A))
      0 := by
  -- Pull out the extra factor `g` and reuse the owner null-homotopy for `f`.
  have hcomp :
      ((f * g) • 𝟙 A) ≫ homotopyCofiber.inr (f • 𝟙 A) =
        (g • 𝟙 A) ≫ ((f • 𝟙 A) ≫ homotopyCofiber.inr (f • 𝟙 A)) := by
    simp [smul_smul]
  exact
    (Homotopy.ofEq hcomp).trans
      ((homotopyCofiber.inrCompHomotopy (f • 𝟙 A) chain_down_exists).compLeft (g • 𝟙 A))

/-- Helper for Lemma 15.28.9: the right comparison map in the octahedral factorization
`C(g) ⟶ C(fg) ⟶ C(f)`. -/
noncomputable def smul_mul_homotopyCofiber_factor_right
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    homotopyCofiber ((f * g) • 𝟙 A) ⟶ homotopyCofiber (f • 𝟙 A) :=
  homotopyCofiber.desc ((f * g) • 𝟙 A)
    (homotopyCofiber.inr (f • 𝟙 A))
    (smul_mul_homotopyCofiber_factor_right_homotopy A f g)

/-- Helper for Lemma 15.28.9: the left comparison restricts to multiplication by `f` on the
owner summand `A ⟶ C(fg)`. -/
@[simp] private lemma smul_mul_homotopyCofiber_factor_left_inr
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    homotopyCofiber.inr (g • 𝟙 A) ≫ smul_mul_homotopyCofiber_factor_left A f g =
      (f • 𝟙 A) ≫ homotopyCofiber.inr ((f * g) • 𝟙 A) := by
  -- This is the defining property of `homotopyCofiber.desc`.
  simp [smul_mul_homotopyCofiber_factor_left]

/-- Helper for Lemma 15.28.9: the right comparison restricts to the owner inclusion
`A ⟶ C(f)`. -/
@[simp] private lemma smul_mul_homotopyCofiber_factor_right_inr
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    homotopyCofiber.inr ((f * g) • 𝟙 A) ≫ smul_mul_homotopyCofiber_factor_right A f g =
      homotopyCofiber.inr (f • 𝟙 A) := by
  -- This is the defining property of `homotopyCofiber.desc`.
  simp [smul_mul_homotopyCofiber_factor_right]

/-- Helper for Lemma 15.28.9: on the owner summand, the composite
`C(g) ⟶ C(fg) ⟶ C(f)` is exactly the null-homotopic map `(f • 𝟙 A) ≫ inr`. -/
private lemma smul_mul_factor_composite_inr
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    homotopyCofiber.inr (g • 𝟙 A) ≫
        smul_mul_homotopyCofiber_factor_left A f g ≫
        smul_mul_homotopyCofiber_factor_right A f g =
      f • homotopyCofiber.inr (f • 𝟙 A) := by
  -- The two owner-side description lemmas reduce the composite to the obvious scalar map.
  have hleft :
      (homotopyCofiber.inr (g • 𝟙 A) ≫ smul_mul_homotopyCofiber_factor_left A f g) ≫
          smul_mul_homotopyCofiber_factor_right A f g =
        ((f • 𝟙 A) ≫ homotopyCofiber.inr ((f * g) • 𝟙 A)) ≫
          smul_mul_homotopyCofiber_factor_right A f g :=
    congrArg
      (fun k ↦ k ≫ smul_mul_homotopyCofiber_factor_right A f g)
      (smul_mul_homotopyCofiber_factor_left_inr A f g)
  have hright :
      ((f • 𝟙 A) ≫ homotopyCofiber.inr ((f * g) • 𝟙 A)) ≫
          smul_mul_homotopyCofiber_factor_right A f g =
        (f • 𝟙 A) ≫ homotopyCofiber.inr (f • 𝟙 A) :=
    congrArg
      (fun k ↦ (f • 𝟙 A) ≫ k)
      (smul_mul_homotopyCofiber_factor_right_inr A f g)
  calc
    homotopyCofiber.inr (g • 𝟙 A) ≫
        smul_mul_homotopyCofiber_factor_left A f g ≫
        smul_mul_homotopyCofiber_factor_right A f g =
      (f • 𝟙 A) ≫ homotopyCofiber.inr ((f * g) • 𝟙 A) ≫
        smul_mul_homotopyCofiber_factor_right A f g := by
        -- Postcompose the owner-side description of the left factor map.
        exact hleft
    _ =
      (f • 𝟙 A) ≫ homotopyCofiber.inr (f • 𝟙 A) := by
        -- Precompose the owner-side description of the right factor map.
        exact hright
    _ = f • homotopyCofiber.inr (f • 𝟙 A) := by
        simp

/-- Helper for Lemma 15.28.9: the degree-`n` term of the shifted cone `C(f)[1]`
identified in textbook coordinates as `A.X (n + 1) ⊞ A.X n`. -/
private noncomputable def smul_mul_connecting_sourceXIso
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (n : ℤ) :
    ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).X n ≅ A.X (n + 1) ⊞ A.X n :=
  ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 n (n + 1) rfl ≪≫
    chainMapConeTextbookXIso (f • 𝟙 A) (n + 1) ≪≫
      eqToIso (by simp)

/-- Helper for Lemma 15.28.9: the degree-`n` term of `C(g)` in textbook coordinates. -/
private noncomputable def smul_mul_connecting_targetXIso
    (A : ChainComplex (ModuleCat R) ℤ) (g : R) (n : ℤ) :
    (homotopyCofiber (g • 𝟙 A)).X n ≅ A.X n ⊞ A.X (n - 1) :=
  chainMapConeTextbookXIso (g • 𝟙 A) n

/-- Helper for Lemma 15.28.9: the target cone differential is the expected textbook matrix in
the coordinates `A.X i ⊞ A.X (i - 1)`. -/
private theorem smul_mul_connecting_target_d_eq_ofComponents
    (A : ChainComplex (ModuleCat R) ℤ) (g : R) (i : ℤ) :
    (smul_mul_connecting_targetXIso A g i).inv ≫
        (homotopyCofiber (g • 𝟙 A)).d i (i - 1) ≫
        (smul_mul_connecting_targetXIso A g (i - 1)).hom =
      Biprod.ofComponents (A.d i (i - 1)) 0 ((g • 𝟙 A).f (i - 1))
        (-A.d (i - 1) ((i - 1) - 1)) := by
  -- This is exactly the local cone differential formula specialized to `g • 𝟙 A`.
  simpa [smul_mul_connecting_targetXIso] using
    (chainMap_cone_d_eq_ofComponents (φ := g • 𝟙 A) (n := i))

/-- Helper for Lemma 15.28.9: the predecessor index written as `i + 1 - 1` agrees with the
shifted-source index written as `i - 1 + 1`. -/
private lemma smul_mul_connecting_predecessor_transport
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) =
      (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) := by
  -- Both presentations simplify to the same predecessor pair `(i, i - 1)`.
  simp

/-- Helper for Lemma 15.28.9: the source coordinates at degree `i` identify the second summand
with the predecessor presentation coming from the unshifted cone in degree `i + 1`. -/
private lemma smul_mul_connecting_source_domain_transport
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    (A.X (i + 1) ⊞ A.X ((i + 1) - 1)) = (A.X (i + 1) ⊞ A.X i) := by
  simp

/-- Helper for Lemma 15.28.9: the codomain of the cone differential at degree `i + 1` matches the
source coordinates at degree `i - 1`. -/
private lemma smul_mul_connecting_source_codomain_transport
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    (A.X i ⊞ A.X (i - 1)) =
      (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) := by
  simp

/-- Helper for Lemma 15.28.9: expanding the shifted-source coordinate isomorphisms exposes the
exact `shiftFunctorObjXIso` conjugation that must be rewritten before any endpoint transport is
simplified. -/
private lemma smul_mul_connecting_source_shift_conjugation
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    (smul_mul_connecting_sourceXIso A f i).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (smul_mul_connecting_sourceXIso A f (i - 1)).hom =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 i (i + 1) rfl).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
          rfl).hom ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (by simp) := by
  -- Expand both source coordinate isomorphisms so the shift differential sits between the
  -- explicit shift-degree identifications and the unshifted cone-coordinate isomorphisms.
  simp [smul_mul_connecting_sourceXIso, Iso.trans_inv, Iso.trans_hom, Category.assoc]

/-- Helper for Lemma 15.28.9: the middle shifted differential term rewrites to the
`(-1)`-multiple of the unshifted cone differential before any endpoint transport is simplified. -/
private lemma smul_mul_connecting_source_shift_terminal_transport
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 i (i + 1) rfl).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
          rfl).hom ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (by simp) =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 i (i + 1) rfl).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
          rfl).hom ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm := by
  -- Only the terminal transport witness changes; the preceding composite is fixed.
  exact
    comp_eqToHom_eq
      (eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 i (i + 1) rfl).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
          rfl).hom ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom)
      _ _

/-- Helper for Lemma 15.28.9: the middle shifted differential term rewrites to the
`(-1)`-multiple of the unshifted cone differential before any endpoint transport is simplified. -/
private lemma smul_mul_connecting_source_middle_shift_d
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 i (i + 1) rfl).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
          rfl).hom ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm := by
  -- Route correction: isolate the whiskered `shiftFunctor_obj_d` rewrite before inserting the
  -- cone matrix formula, so Lean only sees one transport normalization at a time.
  calc
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 i (i + 1) rfl).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
          rfl).hom ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (by simp) =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (((ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 i (i + 1) rfl).inv ≫
            ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1)) ≫
          (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
            rfl).hom) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm := by
        -- First reassociate so the shifted differential theorem matches literally.
        simp [Category.assoc]
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        ((((1 : ℤ).negOnePow • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1)) ≫
            (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1)
              ((i - 1) + 1) rfl).inv) ≫
          (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
            rfl).hom) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm := by
        -- Then rewrite the middle composite by the canonical shift formula.
        rw [ChainComplex.shiftFunctor_obj_d]
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm := by
        -- Finally cancel the adjacent shift isomorphism, normalize `(-1)^1`, and use proof
        -- irrelevance for the terminal `eqToHom`.
        rw [Int.negOnePow_one]
        simp [Category.assoc]
        exact
          comp_eqToHom_eq
            (eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
              (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
              (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
              (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom)
            _ _

/-- Helper for Lemma 15.28.9: changing the degree of the textbook cone-coordinate isomorphism
only inserts the corresponding source and target `eqToHom` transports. -/
private lemma chainMapConeTextbookXIso_hom_transport
    {A B : ChainComplex (ModuleCat R) ℤ} (φ : A ⟶ B) {n m : ℤ} (h : n = m) :
    (chainMapConeTextbookXIso φ n).hom ≫
        eqToHom (congrArg (fun k ↦ B.X k ⊞ A.X (k - 1)) h) =
      eqToHom (congrArg (fun k ↦ (homotopyCofiber φ).X k) h) ≫
        (chainMapConeTextbookXIso φ m).hom := by
  -- Both sides are the same morphism after replacing `n` by `m`.
  cases h
  simp

private lemma smul_mul_connecting_source_endpoint_transport
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm =
      eqToHom
          (show (homotopyCofiber (f • 𝟙 A)).X ((i - 1) + 1) =
              (homotopyCofiber (f • 𝟙 A)).X ((i + 1) - 1) by
            simp) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom ≫
        eqToHom
          (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) = (A.X i ⊞ A.X (i - 1)) by
            simp) := by
  -- First isolate the raw predecessor transport inside `chainMapConeTextbookXIso.hom`.
  let hnm : ((i - 1) + 1) = ((i + 1) - 1) := by simp
  let hsource_raw :
      (homotopyCofiber (f • 𝟙 A)).X ((i - 1) + 1) =
        (homotopyCofiber (f • 𝟙 A)).X ((i + 1) - 1) :=
    congrArg (fun k ↦ (homotopyCofiber (f • 𝟙 A)).X k) hnm
  let hcodomain_raw :
      (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) =
        (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) :=
    congrArg (fun k ↦ A.X k ⊞ A.X (k - 1)) hnm
  let hsource :
      (homotopyCofiber (f • 𝟙 A)).X ((i - 1) + 1) =
        (homotopyCofiber (f • 𝟙 A)).X ((i + 1) - 1) := by
      simp
  let hcodomain :
      (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) = (A.X i ⊞ A.X (i - 1)) := by
      simp
  have hsource_eq : hsource_raw = hsource := by
    -- Equality proofs are propositions, so the concrete transport witness is irrelevant.
    apply Subsingleton.elim
  have hcodomain_eq :
      (smul_mul_connecting_source_codomain_transport A i).symm =
        hcodomain_raw.trans hcodomain := by
    -- The codomain transport factors through the raw predecessor endpoint.
    apply Subsingleton.elim
  calc
    (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm =
      (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
          eqToHom hcodomain_raw ≫ eqToHom hcodomain := by
        -- Split the terminal transport into the raw predecessor step and the final simplification.
        cases hcodomain_eq
        simp [eqToHom_trans, Category.assoc]
    _ =
      eqToHom hsource_raw ≫
          (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom ≫ eqToHom hcodomain := by
        -- Transport `chainMapConeTextbookXIso.hom` itself across the raw predecessor equality.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫ eqToHom hcodomain)
            (chainMapConeTextbookXIso_hom_transport (φ := f • 𝟙 A) (h := hnm))
    _ =
      eqToHom hsource ≫
          (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom ≫ eqToHom hcodomain := by
        -- Replace the source transport witness by the proof-irrelevant `simp` witness.
        rw [hsource_eq]

/-- Helper for Lemma 15.28.9: after normalizing the shifted-source endpoint from
`((i - 1) + 1)` to `((i + 1) - 1)`, the raw `(-1)`-multiple of the cone differential is the
negated textbook cone matrix in degree `i + 1`. -/
private lemma smul_mul_connecting_negated_differential_transport
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        eqToHom
          (show (homotopyCofiber (f • 𝟙 A)).X ((i - 1) + 1) =
              (homotopyCofiber (f • 𝟙 A)).X ((i + 1) - 1) by
            simp) =
      -((homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1)) := by
  -- Route correction: isolate the raw cone-level transport first, so later matrix lemmas only
  -- need reassociation and the cone differential formula.
  let hindex : ((i - 1) + 1) = ((i + 1) - 1) := by
    simp
  let hsource :
      (homotopyCofiber (f • 𝟙 A)).X ((i - 1) + 1) =
        (homotopyCofiber (f • 𝟙 A)).X ((i + 1) - 1) :=
    congrArg (fun k ↦ (homotopyCofiber (f • 𝟙 A)).X k) hindex
  have htransport :
      (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1) ≫ eqToHom hsource =
        (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1) := by
    -- First transport the differential itself across the predecessor equality.
    simpa [hsource, hindex] using
      homotopyCofiber_d_comp_eqToHom_of_index_eq
        (φ := f • 𝟙 A) (i := i + 1) (j := ((i - 1) + 1)) (j' := ((i + 1) - 1))
        (h := hindex)
  calc
    (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        eqToHom
          (show (homotopyCofiber (f • 𝟙 A)).X ((i - 1) + 1) =
              (homotopyCofiber (f • 𝟙 A)).X ((i + 1) - 1) by
            simp) =
      (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        eqToHom hsource := by
        -- The displayed `simp` witness is propositionally equal to the canonical raw transport.
        exact
          comp_eqToHom_eq
            (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) _ _
    _ =
      (-1 : ℤ) •
        ((homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1) ≫ eqToHom hsource) := by
        -- Pull the scalar through the composition so the transport lemma applies to the raw
        -- differential itself.
        simpa using
          (CategoryTheory.Preadditive.zsmul_comp
            ((homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1)) (eqToHom hsource)
            (-1 : ℤ))
    _ =
      (-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1) := by
        -- Now replace the transported differential by the literal predecessor differential.
        rw [htransport]
    _ = -((homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1)) := by
        -- Finally rewrite the scalar `(-1)` as categorical negation.
        rw [neg_one_zsmul]

/-- Helper for Lemma 15.28.9: negating a biproduct block matrix negates each of its four
entries. -/
private lemma biprod_ofComponents_neg
    {X₁ X₂ Y₁ Y₂ : ModuleCat R}
    [Limits.HasBinaryBiproduct X₁ X₂] [Limits.HasBinaryBiproduct Y₁ Y₂]
    (a : X₁ ⟶ Y₁) (b : X₁ ⟶ Y₂) (c : X₂ ⟶ Y₁) (d : X₂ ⟶ Y₂) :
    -Biprod.ofComponents a b c d = Biprod.ofComponents (-a) (-b) (-c) (-d) := by
  -- Reduce the block-matrix equality to the four projection/inclusion composites.
  rw [← Biprod.ofComponents_eq (-Biprod.ofComponents a b c d)]
  ext <;> simp

/-- Helper for Lemma 15.28.9: after endpoint normalization, the transported `(-1)`-multiple of
the cone differential becomes the negation of the conjugated literal predecessor differential. -/
private lemma smul_mul_connecting_negated_conjugation_after_endpoint_transport
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        ((((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1)) ≫
            eqToHom
              (show (homotopyCofiber (f • 𝟙 A)).X ((i - 1) + 1) =
                  (homotopyCofiber (f • 𝟙 A)).X ((i + 1) - 1) by
                simp))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (-((chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
            (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1) ≫
            (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom)) := by
  -- First normalize the transported raw differential to the literal predecessor differential.
  calc
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        ((((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1)) ≫
            eqToHom
              (show (homotopyCofiber (f • 𝟙 A)).X ((i - 1) + 1) =
                  (homotopyCofiber (f • 𝟙 A)).X ((i + 1) - 1) by
                simp))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (-((homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom := by
        -- This isolates the transport rewrite from the later matrix calculation.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
                (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
                k ≫
                (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom)
            (smul_mul_connecting_negated_differential_transport A f i)
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        ((chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
          (-((homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1))) ≫
          (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom) := by
        -- Reassociate so the categorical negation can be pushed through the conjugation.
        simp [Category.assoc]
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        ((-((chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
            (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1))) ≫
          (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom) := by
        -- Move the minus sign across the left whisker only.
        have hcomp :
            (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
                (-((homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1))) =
              -((chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
                (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1)) := by
          rw [CategoryTheory.Preadditive.comp_neg]
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
                (k ≫ (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom))
            hcomp
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (-(((chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
            (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1)) ≫
            (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom)) := by
        -- Then move the minus sign across the right whisker.
        rw [CategoryTheory.Preadditive.neg_comp]
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (-((chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
            (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1) ≫
            (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom)) := by
        -- Finally reassociate back to the literal cone-matrix conjugation shape.
        simp [Category.assoc]

/-- Helper for Lemma 15.28.9: after normalizing the shifted-source endpoint from
`((i - 1) + 1)` to `((i + 1) - 1)`, the raw `(-1)`-multiple of the cone differential is the
negated textbook cone matrix in degree `i + 1`. -/
private lemma smul_mul_connecting_source_matrix_after_endpoint_transport
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) ≫
        eqToHom (by simp) := by
  let hcodomain :
      (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) = (A.X i ⊞ A.X (i - 1)) := by
    simp
  -- Normalize the terminal coordinate transport before invoking the cone-matrix formula.
  calc
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        ((((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1)) ≫
            eqToHom
              (show (homotopyCofiber (f • 𝟙 A)).X ((i - 1) + 1) =
                  (homotopyCofiber (f • 𝟙 A)).X ((i + 1) - 1) by
                simp))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom ≫
        eqToHom hcodomain := by
        -- This isolates the endpoint transport as a separate rewrite from the differential itself.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
                (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
                (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
                k)
            (smul_mul_connecting_source_endpoint_transport A f i)
    _ =
      (eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (-((chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
            (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i + 1) - 1) ≫
            (chainMapConeTextbookXIso (f • 𝟙 A) ((i + 1) - 1)).hom))) ≫
        eqToHom hcodomain := by
        -- The dedicated adapter handles the transported negation separately from the matrix step.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫ eqToHom hcodomain)
            (smul_mul_connecting_negated_conjugation_after_endpoint_transport A f i)
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (-(Biprod.ofComponents (A.d (i + 1) ((i + 1) - 1)) 0
            ((f • 𝟙 A).f ((i + 1) - 1))
            (-A.d ((i + 1) - 1) (((i + 1) - 1) - 1)))) ≫
        eqToHom hcodomain := by
        -- Insert the literal degree-`i + 1` cone differential matrix in textbook coordinates.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
                (-k) ≫ eqToHom hcodomain)
            (chainMap_cone_d_eq_ofComponents (φ := f • 𝟙 A) (n := i + 1))
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) ≫
        eqToHom hcodomain := by
        -- Negate the explicit `2 × 2` block matrix entrywise.
        simpa using
          congrArg
            (fun k ↦
              eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
                k ≫ eqToHom hcodomain)
            (biprod_ofComponents_neg
              (a := A.d (i + 1) ((i + 1) - 1))
              (b := 0)
              (c := (f • 𝟙 A).f ((i + 1) - 1))
              (d := -A.d ((i + 1) - 1) (((i + 1) - 1) - 1)))
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) ≫
        eqToHom (by simp) := by
        -- The final endpoint transport witness is proof-irrelevant.
        exact
          comp_eqToHom_eq
            (eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
              Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
                (-((f • 𝟙 A).f ((i + 1) - 1)))
                (A.d ((i + 1) - 1) (((i + 1) - 1) - 1))) _ _

/-- Helper for Lemma 15.28.9: the final codomain transport in the shifted-source matrix is
proof-irrelevant once the predecessor endpoint is simplified to the literal degree `i`. -/
private lemma smul_mul_connecting_source_codomain_eqToHom_irrel
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_codomain_transport A i).symm =
      eqToHom
        (show (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) = (A.X i ⊞ A.X (i - 1)) by
          simp) := by
  -- Equality proofs between the same codomain objects are propositions.
  apply congrArg eqToHom
  exact Subsingleton.elim _ _

/-- Helper for Lemma 15.28.9: the fully simplified endpoint transport factors through the raw
predecessor presentation before the final codomain simplification to degree `i`. -/
private lemma smul_mul_connecting_source_endpoint_predecessor_transport
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    eqToHom
        (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) = (A.X i ⊞ A.X (i - 1)) by
          simp) =
      eqToHom (smul_mul_connecting_predecessor_transport A i) ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm := by
  -- The two equality proofs differ only by how the arithmetic normalization is parenthesized.
  have htransport :
      (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) = (A.X i ⊞ A.X (i - 1)) by
        simp) =
        (smul_mul_connecting_predecessor_transport A i).trans
          (smul_mul_connecting_source_codomain_transport A i).symm := by
    apply Subsingleton.elim
  cases htransport
  simp [Category.assoc]

/-- Helper for Lemma 15.28.9: the endpoint-normalized source matrix can be factored through the
explicit predecessor transport before the final simplification to the literal degree `i`. -/
private lemma smul_mul_connecting_source_matrix_after_predecessor_transport
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) ≫
        eqToHom (smul_mul_connecting_predecessor_transport A i) ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm := by
  -- Keep the predecessor endpoint explicit before the final `i`-normalization.
  calc
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) ≫
        eqToHom
          (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) = (A.X i ⊞ A.X (i - 1)) by
            simp) := by
        -- First reuse the already-proved endpoint-normalized source matrix formula.
        simpa using smul_mul_connecting_source_matrix_after_endpoint_transport A f i
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) ≫
        eqToHom (smul_mul_connecting_predecessor_transport A i) ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm := by
        -- Then split the final transport into the requested predecessor step and the last
        -- degree simplification.
        rw [smul_mul_connecting_source_endpoint_predecessor_transport]

/-- Helper for Lemma 15.28.9: first rewrite the shifted source differential in the exact
transported endpoint coordinates produced by `shiftFunctor_obj_d` and the degree-`i + 1` cone
matrix. -/
private lemma smul_mul_connecting_source_unsimplified_target_transport
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    (A.X i ⊞ A.X (i - 1)) = (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) := by
  -- The first summand is the same degree written in predecessor form.
  simp

/-- Helper for Lemma 15.28.9: postcomposing the simplified codomain transport with the explicit
unsimplified target identification recovers the endpoint transport used by
`smul_mul_connecting_source_shift_conjugation`. -/
private lemma smul_mul_connecting_source_codomain_to_unsimplified_eqToHom
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_codomain_transport A i).symm ≫
        eqToHom (smul_mul_connecting_source_unsimplified_target_transport A i) =
      eqToHom
        (show (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) =
            (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
          simp) := by
  -- Both composites are transports along the same endpoint equality.
  have htransport :
      ((smul_mul_connecting_source_codomain_transport A i).symm.trans
          (smul_mul_connecting_source_unsimplified_target_transport A i)) =
        (show (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) =
            (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
          simp) := by
    apply Subsingleton.elim
  cases htransport
  simp [eqToHom_trans]

/-- Helper for Lemma 15.28.9: after the predecessor and codomain simplifications are both
postcomposed to the unsimplified source target, the result is the single endpoint transport from
the raw predecessor matrix to `A.X ((i - 1) + 1) ⊞ A.X (i - 1)`. -/
private lemma smul_mul_connecting_source_endpoint_predecessor_to_unsimplified_eqToHom
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    eqToHom (smul_mul_connecting_predecessor_transport A i) ≫
        eqToHom (smul_mul_connecting_source_codomain_transport A i).symm ≫
        eqToHom (smul_mul_connecting_source_unsimplified_target_transport A i) =
      eqToHom
        (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) =
            (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
          simp) := by
  -- Again the two routes are the same transport after proof irrelevance.
  have htransport :
      (((smul_mul_connecting_predecessor_transport A i).trans
            (smul_mul_connecting_source_codomain_transport A i).symm).trans
          (smul_mul_connecting_source_unsimplified_target_transport A i)) =
        (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) =
            (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
          simp) := by
    apply Subsingleton.elim
  cases htransport
  simp [eqToHom_trans, Category.assoc]

/-- Helper for Lemma 15.28.9: after postcomposing back to the unsimplified source target, the
shifted differential rewrite keeps the same endpoint as the source-coordinate isomorphism at
degree `i - 1`. -/
private lemma smul_mul_connecting_source_middle_shift_d_unsimplified
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 i (i + 1) rfl).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
          rfl).hom ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom
          (show (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) =
              (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
            simp) =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom
          (show (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) =
              (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
            simp) := by
  -- Postcompose the simplified-target differential rewrite back to the unsimplified endpoint.
  have hpost :
      (eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
          (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
          (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 i (i + 1) rfl).inv ≫
          ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
          (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
            rfl).hom ≫
          (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
          eqToHom (smul_mul_connecting_source_codomain_transport A i).symm) ≫
        eqToHom (smul_mul_connecting_source_unsimplified_target_transport A i) =
      (eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
          (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
          (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
          (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
          eqToHom (smul_mul_connecting_source_codomain_transport A i).symm) ≫
        eqToHom (smul_mul_connecting_source_unsimplified_target_transport A i) := by
    exact congrArg (fun k ↦ k ≫ eqToHom (smul_mul_connecting_source_unsimplified_target_transport A i))
      (smul_mul_connecting_source_middle_shift_d A f i)
  simpa [Category.assoc, smul_mul_connecting_source_codomain_to_unsimplified_eqToHom] using hpost

/-- Helper for Lemma 15.28.9: after postcomposing back to the unsimplified source target, the
endpoint-normalized source matrix becomes the raw predecessor matrix with the single endpoint
transport expected by `smul_mul_connecting_source_d_transport`. -/
private lemma smul_mul_connecting_source_matrix_unsimplified
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom
          (show (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) =
              (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
            simp) =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) ≫
        eqToHom
          (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) =
              (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
            simp) := by
  -- Postcompose the predecessor-transport formula back to the unsimplified target.
  have hpost :
      (eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
          (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
          (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
          (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
          eqToHom (smul_mul_connecting_source_codomain_transport A i).symm) ≫
        eqToHom (smul_mul_connecting_source_unsimplified_target_transport A i) =
      (eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
          Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
            (-((f • 𝟙 A).f ((i + 1) - 1)))
            (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) ≫
          eqToHom (smul_mul_connecting_predecessor_transport A i) ≫
          eqToHom (smul_mul_connecting_source_codomain_transport A i).symm) ≫
        eqToHom (smul_mul_connecting_source_unsimplified_target_transport A i) := by
    exact congrArg (fun k ↦ k ≫ eqToHom (smul_mul_connecting_source_unsimplified_target_transport A i))
      (smul_mul_connecting_source_matrix_after_predecessor_transport A f i)
  simpa [Category.assoc,
    smul_mul_connecting_source_codomain_to_unsimplified_eqToHom,
    smul_mul_connecting_source_endpoint_predecessor_to_unsimplified_eqToHom] using hpost

private theorem smul_mul_connecting_source_d_transport
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    (smul_mul_connecting_sourceXIso A f i).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (smul_mul_connecting_sourceXIso A f (i - 1)).hom =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1))) ≫
        eqToHom (by simp) := by
  -- Keep the codomain in the unsimplified source coordinates all the way through the source-side
  -- calculation.
  calc
    (smul_mul_connecting_sourceXIso A f i).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (smul_mul_connecting_sourceXIso A f (i - 1)).hom =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 i (i + 1) rfl).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (ChainComplex.shiftFunctorObjXIso (homotopyCofiber (f • 𝟙 A)) 1 (i - 1) ((i - 1) + 1)
          rfl).hom ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom
          (show (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) =
              (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
            simp) := by
        -- First expand the shifted source coordinates exactly as in the dedicated conjugation
        -- lemma.
        simpa using smul_mul_connecting_source_shift_conjugation A f i
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) (i + 1)).inv ≫
        (((-1 : ℤ) • (homotopyCofiber (f • 𝟙 A)).d (i + 1) ((i - 1) + 1))) ≫
        (chainMapConeTextbookXIso (f • 𝟙 A) ((i - 1) + 1)).hom ≫
        eqToHom
          (show (A.X ((i - 1) + 1) ⊞ A.X (((i - 1) + 1) - 1)) =
              (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
            simp) := by
        -- Then rewrite the shifted differential while keeping the unsimplified target.
        exact smul_mul_connecting_source_middle_shift_d_unsimplified A f i
    _ =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) ≫
        eqToHom
          (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) =
              (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
            simp) := by
        -- Finally insert the cone matrix while staying in the same unsimplified target.
        exact smul_mul_connecting_source_matrix_unsimplified A f i

/-- Helper for Lemma 15.28.9: the source-domain transport entering the shifted-source matrix is
proof-irrelevant once the predecessor index is simplified. -/
private lemma smul_mul_connecting_source_domain_eqToHom_irrel
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm =
      eqToHom
        (show (A.X (i + 1) ⊞ A.X i) = (A.X (i + 1) ⊞ A.X ((i + 1) - 1)) by
          simp) := by
  -- Equality proofs between the same source and target objects are propositions.
  apply congrArg eqToHom
  exact Subsingleton.elim _ _

/-- Helper for Lemma 15.28.9: precomposing the raw source matrix with the source-domain transport
simply rewrites the predecessor index `((i + 1) - 1)` to the literal degree `i`. -/
private lemma smul_mul_connecting_source_raw_codomain_transport
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    (A.X i ⊞ A.X (i - 1)) =
      (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) := by
  -- The target biproduct is the same pair of degrees written in raw predecessor form.
  simp

/-- Helper for Lemma 15.28.9: the source-domain transport is inverse to its opposite transport. -/
private lemma smul_mul_connecting_source_domain_transport_symm_comp
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        eqToHom (smul_mul_connecting_source_domain_transport A i) =
      𝟙 (A.X (i + 1) ⊞ A.X i) := by
  -- The two endpoint transports cancel by the standard `eqToHom_trans` normalization.
  simp

/-- Helper for Lemma 15.28.9: the scalar endomorphism family commutes with the predecessor
transport from `i` to `((i + 1) - 1)`. -/
private lemma smul_mul_connecting_scalar_transport
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    ((f • 𝟙 A).f i) ≫ eqToHom (show A.X i = A.X ((i + 1) - 1) by simp) =
      eqToHom (show A.X i = A.X ((i + 1) - 1) by simp) ≫ ((f • 𝟙 A).f ((i + 1) - 1)) := by
  -- This is the naturality of the degreewise scalar endomorphism family.
  let h : i = (i + 1) - 1 := by
    simp
  simpa only [h] using
    (CategoryTheory.eqToHom_naturality
      (f := fun j : ℤ ↦ A.X j)
      (g := fun j : ℤ ↦ A.X j)
      (z := fun j ↦ (f • 𝟙 A).f j)
      (w := h))

/-- Helper for Lemma 15.28.9: the source-side `inr` inclusion is compatible with the degree
transport that rewrites `((i + 1) - 1)` to `i`. -/
private lemma smul_mul_connecting_source_domain_transport_inr
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    (Limits.biprod.inr : A.X i ⟶ A.X (i + 1) ⊞ A.X i) ≫
        eqToHom (smul_mul_connecting_source_domain_transport A i).symm =
      eqToHom (show A.X i = A.X ((i + 1) - 1) by simp) ≫
        (Limits.biprod.inr : A.X ((i + 1) - 1) ⟶ A.X (i + 1) ⊞ A.X ((i + 1) - 1)) := by
  -- This is exactly the naturality of the `inr` family under the predecessor equality.
  let h : i = (i + 1) - 1 := by
    simp
  simpa [h] using
    (CategoryTheory.eqToHom_naturality
      (f := fun j : ℤ ↦ A.X j)
      (g := fun j : ℤ ↦ A.X (i + 1) ⊞ A.X j)
      (z := fun j ↦ (Limits.biprod.inr : A.X j ⟶ A.X (i + 1) ⊞ A.X j))
      (w := h))

/-- Helper for Lemma 15.28.9: the first projection out of the raw source codomain is compatible
with the predecessor transport back to the literal degree `i`. -/
private lemma smul_mul_connecting_source_raw_codomain_transport_fst
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_raw_codomain_transport A i) ≫
        (Limits.biprod.fst :
          A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1) ⟶ A.X ((i + 1) - 1)) =
      (Limits.biprod.fst : A.X i ⊞ A.X (i - 1) ⟶ A.X i) ≫
        eqToHom (show A.X i = A.X ((i + 1) - 1) by simp) := by
  -- This is the same naturality statement for the `fst` family, read in reverse.
  let h : i = (i + 1) - 1 := by
    simp
  simpa [h] using
    (CategoryTheory.eqToHom_naturality
      (f := fun j : ℤ ↦ A.X j ⊞ A.X (j - 1))
      (g := fun j : ℤ ↦ A.X j)
      (z := fun j ↦ (Limits.biprod.fst : A.X j ⊞ A.X (j - 1) ⟶ A.X j))
      (w := h)).symm

/-- Helper for Lemma 15.28.9: the second projection out of the raw source codomain is compatible
with the predecessor transport back to the literal degree `i - 1`. -/
private lemma smul_mul_connecting_source_raw_codomain_transport_snd
    (A : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_raw_codomain_transport A i) ≫
        (Limits.biprod.snd :
          A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1) ⟶ A.X (((i + 1) - 1) - 1)) =
      (Limits.biprod.snd : A.X i ⊞ A.X (i - 1) ⟶ A.X (i - 1)) ≫
        eqToHom (show A.X (i - 1) = A.X (((i + 1) - 1) - 1) by simp) := by
  -- The same naturality argument handles the second projection.
  let h : i = (i + 1) - 1 := by
    simp
  simpa [h] using
    (CategoryTheory.eqToHom_naturality
      (f := fun j : ℤ ↦ A.X j ⊞ A.X (j - 1))
      (g := fun j : ℤ ↦ A.X (j - 1))
      (z := fun j ↦ (Limits.biprod.snd : A.X j ⊞ A.X (j - 1) ⟶ A.X (j - 1)))
      (w := h)).symm

/-- Helper for Lemma 15.28.9: precomposing the raw source matrix with the source-domain transport
simply rewrites the predecessor index `((i + 1) - 1)` to the literal degree `i`. -/
private lemma smul_mul_connecting_source_domain_transport_matrix
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) =
      Biprod.ofComponents (-A.d (i + 1) i) 0 (-((f • 𝟙 A).f i)) (A.d i (i - 1)) ≫
        eqToHom (smul_mul_connecting_source_raw_codomain_transport A i) :=
by
  -- TODO: rewrite both sides as `Biprod.ofComponents` and solve the four entries after a single
  -- stable reassociation step that exposes `(inl ≫ eqToHom ...)` on the left and
  -- `(eqToHom ... ≫ fst/snd)` on the right. The new projection lemmas above now close the actual
  -- transport subgoals; only the remaining biproduct reassociation wrapper is still open.
  sorry

/-- Helper for Lemma 15.28.9: after shifting `C(f)` by one, the source differential becomes the
negated cone matrix in the textbook coordinates `A.X (i + 1) ⊞ A.X i`. -/
private theorem smul_mul_connecting_source_d_eq_ofComponents
    (A : ChainComplex (ModuleCat R) ℤ) (f : R) (i : ℤ) :
    (smul_mul_connecting_sourceXIso A f i).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (smul_mul_connecting_sourceXIso A f (i - 1)).hom =
      Biprod.ofComponents (-A.d (i + 1) i) 0 (-((f • 𝟙 A).f i)) (A.d i (i - 1)) ≫
        eqToHom (by simp) := by
  -- Collapse the source-domain transport and the predecessor indices to the literal degree `i`
  -- after the transport-heavy source differential formula is in place.
  calc
    (smul_mul_connecting_sourceXIso A f i).inv ≫
        ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i (i - 1) ≫
        (smul_mul_connecting_sourceXIso A f (i - 1)).hom =
      eqToHom (smul_mul_connecting_source_domain_transport A i).symm ≫
        Biprod.ofComponents (-A.d (i + 1) ((i + 1) - 1)) 0
          (-((f • 𝟙 A).f ((i + 1) - 1)))
          (A.d ((i + 1) - 1) (((i + 1) - 1) - 1)) ≫
        eqToHom (by simp) := by
        exact smul_mul_connecting_source_d_transport A f i
    _ =
      Biprod.ofComponents (-A.d (i + 1) i) 0 (-((f • 𝟙 A).f i)) (A.d i (i - 1)) ≫
        eqToHom (by simp) := by
        -- First simplify the source-domain transport on the raw matrix, then postcompose with the
        -- unchanged endpoint transport.
        have htransport :
            eqToHom (smul_mul_connecting_source_raw_codomain_transport A i) ≫
                eqToHom
                  (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) =
                      (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
                    simp) =
              eqToHom
                (show (A.X i ⊞ A.X (i - 1)) =
                    (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
                  simp) := by
          -- The raw-codomain simplification followed by the endpoint transport is the direct
          -- endpoint transport from the literal degree `i`.
          have hproof :
              (smul_mul_connecting_source_raw_codomain_transport A i).trans
                  (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) =
                      (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
                    simp) =
                (show (A.X i ⊞ A.X (i - 1)) =
                    (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
                  simp) := by
            apply Subsingleton.elim
          cases hproof
          simp [eqToHom_trans]
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              k ≫
                eqToHom
                  (show (A.X ((i + 1) - 1) ⊞ A.X (((i + 1) - 1) - 1)) =
                      (A.X ((i - 1) + 1) ⊞ A.X (i - 1)) by
                    simp))
            (smul_mul_connecting_source_domain_transport_matrix A f i)

/-- Helper for Lemma 15.28.9: in textbook coordinates, the connecting map has the single
nonzero block `A.X n ⟶ A.X n` from the second source summand to the first target summand. -/
private noncomputable def smul_mul_connecting_component
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) (n : ℤ) :
    ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).X n ⟶ (homotopyCofiber (g • 𝟙 A)).X n :=
  (smul_mul_connecting_sourceXIso A f n).hom ≫
    Biprod.ofComponents 0 0 (𝟙 (A.X n)) 0 ≫
      (smul_mul_connecting_targetXIso A g n).inv

/-- Helper for Lemma 15.28.9: a `ComplexShape.down` arrow from degree `i` lands at the unique
predecessor `i - 1`. -/
private lemma cone_down_rel_eq_sub_one {i j : ℤ} (hij : (ComplexShape.down ℤ).Rel i j) :
    j = i - 1 := by
  have hsucc : j + 1 = i := by
    simpa [ComplexShape.down] using hij
  omega

/-- Helper for Lemma 15.28.9: the explicit connecting morphism satisfies the chain-map
equation in textbook coordinates. -/
private theorem smul_mul_connecting_component_comm
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) (i j : ℤ)
    (hij : (ComplexShape.down ℤ).Rel i j) :
    smul_mul_connecting_component A f g i ≫ (homotopyCofiber (g • 𝟙 A)).d i j =
      ((homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧).d i j ≫
        smul_mul_connecting_component A f g j := by
  -- Rewrite the unique predecessor in `ComplexShape.down`; then both sides become explicit
  -- biproduct matrices, so the chain-map condition is a direct `2 × 2` computation.
  obtain rfl : j = i - 1 := cone_down_rel_eq_sub_one hij
  -- TODO: conjugate by `smul_mul_connecting_sourceXIso` and
  -- `smul_mul_connecting_targetXIso`, rewrite the two middle differentials by
  -- `smul_mul_connecting_source_d_eq_ofComponents` and
  -- `smul_mul_connecting_target_d_eq_ofComponents`, and then verify the resulting `2 × 2`
  -- matrix identity entrywise with `Limits.biprod.hom_ext`, keeping the unsimplified source
  -- codomain `A.X ((i - 1) + 1) ⊞ A.X (i - 1)` until the final step.
  sorry

/-- Helper for Lemma 15.28.9: the rotated connecting morphism `C(f)[1] ⟶ C(g)` whose cone
should recover `C(fg)`. -/
private noncomputable def smul_mul_connecting_map
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    (homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧ ⟶ homotopyCofiber (g • 𝟙 A) where
  f := smul_mul_connecting_component A f g
  comm' := smul_mul_connecting_component_comm A f g

/-- Lemma 15.28.9: for a chain complex `A_•` of `R`-modules and scalars `f, g : R`, the cone of
multiplication by `f * g` on `A_•` is homotopy equivalent to the cone of some morphism from the
degree-one shift of the cone of multiplication by `f` to the cone of multiplication by `g`. -/
@[stacks 062A]
theorem homotopyCofiber_smul_mul_exists_homotopyEquiv_homotopyCofiber
    (A : ChainComplex (ModuleCat R) ℤ) (f g : R) :
    ∃ α : (homotopyCofiber (f • 𝟙 A))⟦(1 : ℤ)⟧ ⟶ homotopyCofiber (g • 𝟙 A),
      Nonempty (HomotopyEquiv (homotopyCofiber ((f * g) • 𝟙 A)) (homotopyCofiber α)) := by
  refine ⟨smul_mul_connecting_map A f g, ?_⟩
  let ι := smul_mul_homotopyCofiber_factor_left A f g
  let π := smul_mul_homotopyCofiber_factor_right A f g
  have hι :
      homotopyCofiber.inr (g • 𝟙 A) ≫ ι =
        (f • 𝟙 A) ≫ homotopyCofiber.inr ((f * g) • 𝟙 A) := by
    -- The left comparison is already normalized on the owner summand.
    simpa [ι] using smul_mul_homotopyCofiber_factor_left_inr A f g
  have hπ :
      homotopyCofiber.inr ((f * g) • 𝟙 A) ≫ π =
        homotopyCofiber.inr (f • 𝟙 A) := by
    -- The right comparison is also normalized on the owner summand.
    simpa [π] using smul_mul_homotopyCofiber_factor_right_inr A f g
  have hcomp :
      homotopyCofiber.inr (g • 𝟙 A) ≫ ι ≫ π =
        (f • 𝟙 A) ≫ homotopyCofiber.inr (f • 𝟙 A) := by
    -- The owner-side composite already matches the standard null-homotopic map into `C(f)`.
    simpa [ι, π] using smul_mul_factor_composite_inr A f g
  -- Route correction: the octahedral comparison is more naturally organized as
  -- `C(g) ⟶ C(fg) ⟶ C(f)`, because the connecting morphism of this null-homotopic composite has
  -- the required source and target shape `C(f)[1] ⟶ C(g)`.
  -- TODO: upgrade `hcomp` to a null-homotopy of `ι ≫ π`, identify the induced connecting
  -- morphism with the explicit `smul_mul_connecting_map A f g`, and then compare its cone with
  -- `homotopyCofiber ((f * g) • 𝟙 A)` by the four-summand coordinate splitting and cancellation
  -- of the contractible identity block.
  sorry
