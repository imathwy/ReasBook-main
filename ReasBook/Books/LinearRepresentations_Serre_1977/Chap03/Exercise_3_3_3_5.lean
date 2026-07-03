import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.Finiteness.Basic
import Serre.Chap02.Theorem_2_2_3_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Representation

section

open CategoryTheory
open scoped MonoidAlgebra

variable {G : Type u} [Group G] [Finite G]
variable {k : Type v} [Field k]
variable {H : Subgroup G}

-- Source/core/bridge triage:
-- * source-facing: existence of an irreducible `H`-representation whose induced
--   `G`-representation contains `X` as a subrepresentation.
-- * core/canonical owners: subgroup induction is `Rep.ind H.subtype`, and literal
--   subrepresentations are owned by `Subrepresentation`.
-- * bridge/view: `Rep.of U.toRepresentation` is the canonical rebundling of the chosen
--   subrepresentation `U` as an object of `Rep k G`.
--
-- Primitive data are the subgroup `H`, the irreducible inducing representation `W`, and the
-- subrepresentation `U` of `Rep.ind H.subtype W`. The final equivalence with `X` is derived data,
-- so the theorem exposes those witnesses directly rather than through a separate wrapper; the only
-- remaining `Nonempty` is the proposition-level packaging of the resulting isomorphism witness.
-- Proof sketch: view the given irreducible representation as an irreducible constituent of the
-- regular representation of `G`. Restrict the regular representation to `H`, choose an
-- irreducible `H`-subrepresentation occurring there, and use Frobenius reciprocity together with
-- the universal property of induction to obtain a nonzero intertwining map from `X` to the
-- induced representation from that `H`-representation. Irreducibility of `X` makes this map an
-- embedding, so `X` is isomorphic to a subrepresentation of the induced representation. For a
-- finite group, irreducible representations over a field are automatically finite-dimensional by
-- `IsIrreducible.finiteDimensional_of_finite`, so the statement is expressed without extra
-- finite-dimensionality data.
omit [Finite G] in
/-- Helper for Exercise 3-3.3-5: a nontrivial finite-dimensional `k[H]`-module admits a nonzero
map onto an irreducible `H`-representation coming from a simple quotient. -/
private theorem exists_irreducible_quotient_of_finiteDimensional_nontrivial
    (H : Subgroup G) (M : ModuleCat k[H]) [Module.Finite k[H] M] [Nontrivial M] :
    ∃ (W : Rep k H) (_ : W.ρ.IsIrreducible)
      (q : ((Rep.ofModuleMonoidAlgebra : ModuleCat k[H] ⥤ Rep k H).obj M ⟶ W)),
        q ≠ 0 := by
  -- Finite generation over `k[H]` makes the owner module coatomic.
  let ofH : ModuleCat k[H] ⥤ Rep k H := Rep.ofModuleMonoidAlgebra
  obtain ⟨N, hN, -⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule k[H] M)).resolve_left bot_ne_top
  let W : Rep k H := ofH.obj (ModuleCat.of k[H] (M ⧸ N))
  have hWirr : W.ρ.IsIrreducible := by
    -- A coatom quotient is simple, hence irreducible in the canonical `Rep` owner.
    have hSimple : IsSimpleModule k[H] (M ⧸ N) := (isSimpleModule_iff_isCoatom).2 hN
    simpa [W, Rep.ofModuleMonoidAlgebra_obj_ρ] using
      (Representation.isSimpleModule_iff_irreducible_ofModule (M ⧸ N)).mp hSimple
  let q : ofH.obj M ⟶ W := ofH.map (ModuleCat.ofHom (Submodule.mkQ N))
  have hmkQ_nonzero : Submodule.mkQ N ≠ 0 := by
    -- The quotient map is nonzero because a proper coatom omits some vector.
    obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hN.1)
    intro hzero
    have hx0 : (Submodule.mkQ N) x = 0 := by
      simp [hzero]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx0
    exact hx hx0
  have hq_nonzero : q ≠ 0 := by
    -- Faithfulness of `ofModuleMonoidAlgebra` reflects the nonvanishing of `mkQ`.
    intro hq
    apply hmkQ_nonzero
    have hmodule : ModuleCat.ofHom (Submodule.mkQ N) = 0 := ofH.map_injective hq
    ext x
    have hpoint :=
      congrArg (fun f : M ⟶ ModuleCat.of k[H] (M ⧸ N) ↦ f.hom x) hmodule
    simpa using hpoint
  exact ⟨W, hWirr, q, hq_nonzero⟩

omit [Finite G] in
/-- Helper for Exercise 3-3.3-5: an injective morphism identifies its source with its image
subrepresentation. -/
private theorem equiv_to_range_of_injective_hom
    {X Y : Rep k G} (f : X ⟶ Y) (hf : Function.Injective f.hom) :
    let U := f.hom.range
    Nonempty (X.ρ.Equiv U.toRepresentation) := by
  let U := f.hom.range
  let fLin := f.hom.toLinearMap
  let fRangeLin := fLin.rangeRestrict
  let fRange : X.ρ.IntertwiningMap U.toRepresentation :=
    fRangeLin.intertwiningMap_of_isIntertwiningMap X.ρ U.toRepresentation
      (by
        -- The range is stable because `f` intertwines the two actions.
        intro g x
        apply Subtype.ext
        change f.hom (X.ρ g x) = Y.ρ g (f.hom x)
        simpa using congrArg (fun l : X →ₗ[k] Y ↦ l x) (f.hom.2 g))
  have hfRange_bijective : Function.Bijective fRange := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hf
      exact congrArg Subtype.val hxy
    · simpa [fRange, fLin, fRangeLin] using fLin.surjective_rangeRestrict
  exact ⟨fRange.ofBijective hfRange_bijective⟩

/-- Exercise 3-3.3-5: every irreducible `k`-representation of a finite group `G` is
equivariantly isomorphic to a subrepresentation of a representation induced from some irreducible
`k`-representation of the subgroup `H`. -/
theorem exists_subrepresentation_equiv_induced_from_irreducible
    (H : Subgroup G) (X : Rep.{max (max u v) w} k G) [X.ρ.IsIrreducible] :
    ∃ (W : Rep.{max (max u v) w} k H) (_ : W.ρ.IsIrreducible)
      (U : Subrepresentation (Rep.ind H.subtype W).ρ),
        Nonempty (X.ρ.Equiv U.toRepresentation) := by
  let XH := Rep.res H.subtype X
  letI : Module k[G] X := X.ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule k[G] X := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule X.ρ).mp inferInstance
  letI : Nontrivial X := IsSimpleModule.nontrivial k[G] X
  letI : FiniteDimensional k X := IsIrreducible.finiteDimensional_of_finite X.ρ
  letI : FiniteDimensional k XH := by infer_instance
  letI : Nontrivial XH := by infer_instance
  letI : Module k[H] XH.ρ.asModule := inferInstance
  let e := XH.ρ.asModuleEquiv
  letI : Module.Finite k[H] XH.ρ.asModule := by
    letI : Module.Finite k XH.ρ.asModule :=
      Module.Finite.of_surjective e.symm.toLinearMap fun y ↦
        ⟨e y, by simp⟩
    exact Module.Finite.of_restrictScalars_finite k k[H] XH.ρ.asModule
  letI : Nontrivial XH.ρ.asModule := e.toEquiv.nontrivial
  let ofH : ModuleCat k[H] ⥤ Rep k H := Rep.ofModuleMonoidAlgebra
  let MXH : ModuleCat k[H] := Rep.toModuleMonoidAlgebra.obj XH
  letI : Module.Finite k[H] MXH := by
    simpa [MXH] using (inferInstance : Module.Finite k[H] XH.ρ.asModule)
  letI : Nontrivial MXH := by
    simpa [MXH] using (inferInstance : Nontrivial XH.ρ.asModule)
  -- First choose an irreducible quotient of the restricted representation on the owner-module side.
  have hquotient :
      ∃ (W : Rep.{max (max u v) w} k H) (_ : W.ρ.IsIrreducible) (q : ofH.obj MXH ⟶ W), q ≠ 0 := by
    simpa [MXH] using
      exists_irreducible_quotient_of_finiteDimensional_nontrivial H MXH
  obtain ⟨W, hWirr, qModule, hqModule⟩ := hquotient
  let q : XH ⟶ W := XH.unitIso.hom ≫ qModule
  have hq : q ≠ 0 := by
    -- Precomposing with the inverse unit isomorphism reduces back to the module quotient.
    intro hq
    apply hqModule
    have hcomp := congrArg (fun m ↦ XH.unitIso.inv ≫ m) hq
    simpa [q] using hcomp
  -- Then use the finite-index `Res ⊣ Ind` adjunction to get a nonzero map into the induced
  -- representation.
  classical
  letI : DecidableRel ⇑(QuotientGroup.rightRel H) := Classical.decRel _
  let f := (Rep.resIndAdjunction k H).homEquiv X W q
  have hf : f ≠ 0 := by
    -- The adjunction hom-equivalence reflects nonvanishing.
    intro hf
    apply hq
    have hsymm_zero :
        ((Rep.resIndAdjunction k H).homEquiv X W).symm
            (0 : X ⟶ Rep.ind H.subtype W) = 0 := by
      simpa using
        (Rep.resIndAdjunction_homEquiv_symm_apply W (0 : X ⟶ Rep.ind H.subtype W))
    calc
      q = ((Rep.resIndAdjunction k H).homEquiv X W).symm f := by
        symm
        exact ((Rep.resIndAdjunction k H).homEquiv X W).left_inv q
      _ = ((Rep.resIndAdjunction k H).homEquiv X W).symm 0 := by rw [hf]
      _ = 0 := hsymm_zero
  have hf_injective : Function.Injective f.hom := by
    -- Irreducibility of `X` upgrades any nonzero intertwiner out of `X` to an embedding.
    refine
      (Representation.IsIrreducible.injective_or_eq_zero f.hom).resolve_right ?_
    intro hf_zero
    apply hf
    ext x
    exact congrArg (fun ℓ ↦ ℓ x) hf_zero
  -- Finally identify `X` with the image subrepresentation of that injective map.
  refine ⟨W, hWirr, f.hom.range, ?_⟩
  simpa using equiv_to_range_of_injective_hom f hf_injective

end

end Representation
