import stacks_proof.stacks_project.Chap13.Lemma_13_19_8
import stacks_proof.stacks_project.Chap15.Definition_15_75_1
import Mathlib.Tactic.StacksAttribute

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)

/- Domain-style sampling for Lemma 15.75.5:
- primary domain: perfect objects in the derived category `D(R)` as an object property, together
  with the generic retract/direct-summand API for additive categories;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`;
- best owner abstraction: the `core/canonical` owner is the object property `PerfectObj`; the
  textbook biproduct statement is a `bridge/view` specialization of the generic direct-summand API;
- primitive vs. derived:
  primitive data are the perfectness owner `DerivedCategory.IsPerfect` and its representative-based
  definition from Definition `15.75.1`;
  derived API is retract stability and the direct-summand consequence below.
-/

-- Proof sketch: choose a bounded finite-projective complex representing `K ⊞ L`; the projection
-- maps onto `K` and `L` split in the derived category, so degreewise splitting by projectivity
-- yields bounded finite-projective representatives of both summands.
/-- Helper for Lemma 15.75.5: conjugating a homotopy-category map along
`DerivedCategory.quotientCompQhIso` recovers the corresponding `DerivedCategory.Q`-image. -/
private theorem quotientCompQhIso_homCongr_map
    {K L : Cpx} (f : K ⟶ L) :
    (Iso.homCongr
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app K)
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L))
      (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map f)) =
        DerivedCategory.Q.map f := by
  -- Proof comment: this is the naturality square of `quotient ⋙ Qh ≅ Q`, rewritten on Homs.
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

/-- Helper for Lemma 15.75.5: a bounded finite-projective complex is a bounded-above projective
source for the `Qh` comparison theorem. -/
private theorem qh_map_bijective_of_isBoundedFiniteProjective
    (K L : Cpx) [hK : CochainComplex.IsBoundedFiniteProjective K] :
    Function.Bijective
      (DerivedCategory.Qh.map :
        (((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj K) ⟶
            ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj L)) →
          (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj K) ⟶
            DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj L))) := by
  rcases hK.bounded with ⟨_a, b, _hKGE, hKLE⟩
  let P : CochainComplex.ProjectiveMinus (ModuleCat R) :=
    ⟨⟨K, (CochainComplex.minus_iff (ModuleCat R) K).2 ⟨b, hKLE⟩⟩, fun i ↦ by
      change Projective (K.X i)
      infer_instance⟩
  -- Proof comment: once the representative is packaged as `ProjectiveMinus`, the Chapter 13
  -- comparison theorem applies directly.
  simpa using
    (CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective
      P L)

/-- Helper for Lemma 15.75.5: the retract idempotent on a bounded finite-projective representative
can be realized by a literal cochain endomorphism. -/
private theorem exists_endomorphism_representative_of_retract
    {X : DMod} (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L]
    (r : Retract X (DerivedCategory.Q.obj L)) :
    ∃ f : L ⟶ L, DerivedCategory.Q.map f = r.r ≫ r.i := by
  let eHom :
      (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj L) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj L)) ≃
      (DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj L) :=
    Iso.homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L)
  let αh :
      DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj L) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj L) :=
    eHom.symm (r.r ≫ r.i)
  -- Proof comment: bounded-above projective sources see all derived endomorphisms already in the
  -- homotopy category, so we lift the retract idempotent there first.
  obtain ⟨fh, hfh⟩ :=
    (qh_map_bijective_of_isBoundedFiniteProjective (R := R) L L).surjective αh
  obtain ⟨f, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map_surjective fh
  refine ⟨f, eHom.injective ?_⟩
  -- Proof comment: transporting the `Qh` equality back through `quotientCompQhIso` recovers the
  -- desired equality in `D(R)`.
  simpa [αh, quotientCompQhIso_homCongr_map (R := R) (f := f)] using
    congrArg eHom hfh

/-- Helper for Lemma 15.75.5: the lifted cochain endomorphism represents an idempotent after
passing to the derived category. -/
private theorem exists_idempotent_representative_of_retract
    {X : DMod} (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L]
    (r : Retract X (DerivedCategory.Q.obj L)) :
    ∃ f : L ⟶ L,
      DerivedCategory.Q.map f = r.r ≫ r.i ∧
        DerivedCategory.Q.map (f ≫ f) = DerivedCategory.Q.map f := by
  obtain ⟨f, hf⟩ := exists_endomorphism_representative_of_retract (R := R) L r
  refine ⟨f, hf, ?_⟩
  -- Proof comment: the retract relation `r.r ≫ r.i = 𝟙` makes the represented endomorphism
  -- idempotent in the derived category.
  calc
    DerivedCategory.Q.map (f ≫ f) = DerivedCategory.Q.map f ≫ DerivedCategory.Q.map f := by
      simp
    _ = (r.r ≫ r.i) ≫ (r.r ≫ r.i) := by rw [hf]
    _ = r.r ≫ (r.i ≫ r.r) ≫ r.i := by simp [Category.assoc]
    _ = r.r ≫ r.i := by simpa [Category.assoc, r.retract]
    _ = DerivedCategory.Q.map f := hf.symm

/-- Helper for Lemma 15.75.5: if a cochain endomorphism is idempotent after passing to the
derived category, then its chain-level idempotency defect is null-homotopic. -/
private theorem homotopy_idempotent_defect_nullhomotopic
    {L : Cpx} [hL : CochainComplex.IsBoundedFiniteProjective L] (f : L ⟶ L)
    (hf : DerivedCategory.Q.map (f ≫ f) = DerivedCategory.Q.map f) :
    Nonempty (Homotopy (f ≫ f - f) 0) := by
  have hQzero : DerivedCategory.Q.map (f ≫ f - f) = 0 := by
    -- Proof comment: functoriality turns the defect into the difference of two equal derived maps.
    calc
      DerivedCategory.Q.map (f ≫ f - f) =
          DerivedCategory.Q.map (f ≫ f) - DerivedCategory.Q.map f := by
            simp
      _ = 0 := by rw [hf, sub_self]
  let eHom :
      (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj L) ⟶
        DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).obj L)) ≃
      (DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj L) :=
    Iso.homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L)
      ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app L)
  have hQhzero_conj :
      eHom
          (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map (f ≫ f - f))) =
        eHom 0 := by
    -- Proof comment: `quotientCompQhIso` identifies the homotopy-category quotient map with the
    -- derived localization on this defect morphism.
    calc
      eHom
          (DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map (f ≫ f - f))) =
          DerivedCategory.Q.map (f ≫ f - f) := by
            simpa using quotientCompQhIso_homCongr_map (R := R) (f := f ≫ f - f)
      _ = 0 := hQzero
      _ = eHom 0 := by
            dsimp [eHom]
            simp
  have hQhzero :
      DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map (f ≫ f - f)) =
        0 := by
    exact eHom.injective hQhzero_conj
  have hquot_zero :
      (HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map (f ≫ f - f) = 0 := by
    -- Proof comment: bounded-above projective sources see the homotopy-category quotient
    -- faithfully after applying `Qh`.
    have hQhzero' :
        DerivedCategory.Qh.map
            ((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)).map (f ≫ f - f)) =
          DerivedCategory.Qh.map 0 := by
      simpa using hQhzero
    exact (qh_map_bijective_of_isBoundedFiniteProjective (R := R) L L).injective hQhzero'
  -- Proof comment: vanishing in the homotopy-category quotient is exactly null-homotopy.
  exact (HomotopyCategory.quotient_map_eq_zero_iff (f ≫ f - f)).1 hquot_zero

/-- Helper for Lemma 15.75.5: a strict cochain-level retract of a bounded finite-projective
complex is again bounded finite-projective. -/
private theorem boundedFiniteProjective_of_complex_retract
    {M L : Cpx} (ret : Retract M L) [hL : CochainComplex.IsBoundedFiniteProjective L] :
    CochainComplex.IsBoundedFiniteProjective M := by
  rcases hL.bounded with ⟨a, b, hLGE, hLLE⟩
  refine
    { bounded := ⟨a, b, ?_, ?_⟩
      finite := ?_
      projective := ?_ }
  · letI : L.IsStrictlyGE a := hLGE
    exact (CochainComplex.isStrictlyGE_iff (K := M) a).2 <| fun i hi ↦ by
      have hcompMor : ret.i.f i ≫ ret.r.f i = 𝟙 (M.X i) := by
        simpa using congrArg (fun f : M ⟶ M ↦ f.f i) ret.retract
      let retX : Retract (M.X i) (L.X i) :=
        ⟨ret.i.f i, ret.r.f i, hcompMor⟩
      -- Proof comment: below the lower bound the ambient term is zero, and zero objects are
      -- stable under retracts.
      exact IsZero.of_mono retX.i (L.isZero_of_isStrictlyGE a i hi)
  · letI : L.IsStrictlyLE b := hLLE
    exact (CochainComplex.isStrictlyLE_iff (K := M) b).2 <| fun i hi ↦ by
      have hcompMor : ret.i.f i ≫ ret.r.f i = 𝟙 (M.X i) := by
        simpa using congrArg (fun f : M ⟶ M ↦ f.f i) ret.retract
      let retX : Retract (M.X i) (L.X i) :=
        ⟨ret.i.f i, ret.r.f i, hcompMor⟩
      exact IsZero.of_mono retX.i (L.isZero_of_isStrictlyLE b i hi)
  · intro i
    have hcompMor : ret.i.f i ≫ ret.r.f i = 𝟙 (M.X i) := by
      simpa using congrArg (fun f : M ⟶ M ↦ f.f i) ret.retract
    have hsplit : (ret.r.f i).hom.comp (ret.i.f i).hom = LinearMap.id := by
      -- Proof comment: degreewise, the retraction makes `M.X i` a quotient of the finite module
      -- `L.X i`.
      simpa using congrArg ModuleCat.Hom.hom hcompMor
    exact Module.Finite.of_surjective (ret.r.f i).hom <| by
      intro x
      refine ⟨(ret.i.f i).hom x, ?_⟩
      simpa using congrArg (fun f : M.X i →ₗ[R] M.X i ↦ f x) hsplit
  · intro i
    -- Proof comment: each term is a strict direct summand of a projective module, hence
    -- projective.
    have hcompMor : ret.i.f i ≫ ret.r.f i = 𝟙 (M.X i) := by
      simpa using congrArg (fun f : M ⟶ M ↦ f.f i) ret.retract
    exact Module.Projective.of_split (ret.i.f i).hom (ret.r.f i).hom <| by
      simpa using congrArg ModuleCat.Hom.hom hcompMor

/-- Perfect objects of `D(R)` are stable under retracts/direct summands. -/
instance perfectObjectProperty_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts PerfectObj where
  of_retract {X Y} h hY := by
    -- Proof comment: first transport the retract to a chosen bounded finite-projective
    -- representative of `Y`, so the remaining frontier is entirely on the representative side.
    rcases hY with ⟨L, eY, hL⟩
    letI : CochainComplex.IsBoundedFiniteProjective L := hL
    let r' : Retract X (DerivedCategory.Q.obj L) := h.trans (Retract.ofIso eY)
    obtain ⟨f, hf, hf_idem⟩ :=
      exists_idempotent_representative_of_retract (R := R) L r'
    have hdefect : Nonempty (Homotopy (f ≫ f - f) 0) :=
      homotopy_idempotent_defect_nullhomotopic (R := R) f hf_idem
    -- Route correction: the Agent C nilpotence pivot is false in this generality. The remaining
    -- source-faithful blocker is to strictify the derived/homotopy retract of `L` to an actual
    -- cochain-level retract (or an equivalent strict split summand) without changing the ambient
    -- perfect representative.
    -- TODO: prove a strictification lemma turning the lifted retract data on `L` in the homotopy
    -- or derived category into a strict cochain-level retract `M ↪ L ↠ M` together with
    -- `DerivedCategory.Q.obj M ≅ X`; once that exists, the new helper
    -- `boundedFiniteProjective_of_complex_retract` finishes the representative side immediately.
    let _unused_defect : Nonempty (Homotopy (f ≫ f - f) 0) := hdefect
    sorry

/-- Lemma 15.75.5: if the biproduct `K^• ⊕ L^•` is perfect, then both summands `K^•` and
`L^•` are perfect. -/
@[stacks 066S]
theorem isPerfect_summands_of_biprod
    (K L : DMod) (hKL : (K ⊞ L).IsPerfect) :
    K.IsPerfect ∧ L.IsPerfect :=
  ⟨of_biprod_left PerfectObj hKL, of_biprod_right PerfectObj hKL⟩

end

end CategoryTheory
