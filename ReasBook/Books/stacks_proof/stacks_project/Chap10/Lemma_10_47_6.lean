import Mathlib
import StacksProject_2024.Chap10.Definition_10_47_4
import StacksProject_2024.Chap10.Lemma_10_43_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped TensorProduct
open Algebra.TensorProduct
open AlgebraicGeometry CommRingCat

universe u

namespace Algebra

-- Local shorthand for the canonical geometric-irreducibility owner property from
-- `Definition_10_47_4`.
local notation "GeomIrreducibleOver[" k "] " R =>
  GeometricallyIrreducible (Spec.map (ofHom (algebraMap k R)))

section

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- Helper for Lemma 10.47.6: an irreducible prime spectrum is automatically nonempty, hence the
underlying ring is nontrivial. -/
private theorem nontrivial_of_irreducible_primeSpectrum {R : Type u} [CommRing R]
    (hR : IrreducibleSpace (PrimeSpectrum R)) : Nontrivial R := by
  -- An irreducible space is nonempty, and `Spec R` is nonempty exactly when `R` is nontrivial.
  letI : IrreducibleSpace (PrimeSpectrum R) := hR
  exact PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance

/-- Helper for Lemma 10.47.6: irreducibility of prime spectra descends along injective ring maps. -/
private theorem irreducibleSpace_primeSpectrum_of_injective {R S : Type u} [CommRing R]
    [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    IrreducibleSpace (PrimeSpectrum S) → IrreducibleSpace (PrimeSpectrum R) := by
  intro hS
  -- Compare the nilradicals via injectivity, then pull primeness back along `f`.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hS ⊢
  letI : (nilradical S).IsPrime := hS
  have hcomap : Ideal.comap f (nilradical S) = nilradical R := by
    ext x
    simp [Ideal.mem_comap, mem_nilradical, IsNilpotent.map_iff hf]
  simpa [hcomap] using Ideal.comap_isPrime f (nilradical S)

/-- Helper for Lemma 10.47.6: a witness that the nilradical of a ring fails to be prime. -/
private structure NonprimeNilradicalWitness (R : Type u) [CommRing R] where
  left : R
  right : R
  mul_isNilpotent : IsNilpotent (left * right)
  left_not_isNilpotent : ¬ IsNilpotent left
  right_not_isNilpotent : ¬ IsNilpotent right

/-- Helper for Lemma 10.47.6: such a witness forces the prime spectrum to be non-irreducible. -/
private theorem not_irreducibleSpace_primeSpectrum_of_nonprime_nilradical_witness
    {R : Type u} [CommRing R] :
    Nonempty (NonprimeNilradicalWitness R) → ¬ IrreducibleSpace (PrimeSpectrum R) := by
  intro h hR
  obtain ⟨w⟩ := h
  -- Primeness of the nilradical would force one of the two factors to be nilpotent.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hR
  have hmul : w.left * w.right ∈ nilradical R := by
    exact mem_nilradical.mpr w.mul_isNilpotent
  rcases hR.mem_or_mem hmul with hleft | hright
  · exact w.left_not_isNilpotent (mem_nilradical.mp hleft)
  · exact w.right_not_isNilpotent (mem_nilradical.mp hright)

/-- Helper for Lemma 10.47.6: in a nontrivial ring, failure of irreducibility of `Spec R`
produces a concrete witness that the nilradical is not prime. -/
private theorem exists_nonprime_nilradical_witness_of_not_irreducibleSpace_primeSpectrum
    {R : Type u} [CommRing R] [Nontrivial R] :
    ¬ IrreducibleSpace (PrimeSpectrum R) → Nonempty (NonprimeNilradicalWitness R) := by
  intro hR
  -- Rewrite non-irreducibility into non-primeness of the nilradical.
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical] at hR
  have htop : (nilradical R) ≠ ⊤ := by
    intro htop
    have hnil : IsNilpotent (1 : R) := by
      apply mem_nilradical.mp
      simpa [htop] using (show (1 : R) ∈ (⊤ : Ideal R) from Ideal.mem_top)
    obtain ⟨n, hn⟩ := hnil
    exact (show (1 : R) ≠ 0 from one_ne_zero) (by simpa using hn)
  obtain ⟨x, hx, y, hy, hxy⟩ := (Ideal.not_isPrime_iff.mp hR).resolve_left htop
  -- The failed primeness statement is exactly the desired witness.
  exact ⟨{
    left := x
    right := y
    mul_isNilpotent := mem_nilradical.mp hxy
    left_not_isNilpotent := by simpa [mem_nilradical] using hx
    right_not_isNilpotent := by simpa [mem_nilradical] using hy
  }⟩

/-- Helper for Lemma 10.47.6: a nonprime-nilradical witness in a tensor product already appears
in a finitely generated tensor stage on both sides. -/
private theorem exists_fg_subalgebras_tensorProduct_has_nonprime_nilradical_witness
    {K : Type u} [Field K] [Algebra k K]
    (h : Nonempty (NonprimeNilradicalWitness (A ⊗[k] K))) :
    ∃ T : @FGSubalgebraPair k A K _ _ _ _ _,
      Nonempty (NonprimeNilradicalWitness (T.left ⊗[k] T.right)) := by
  obtain ⟨w⟩ := h
  -- Descend the two witness elements to one common finitely generated tensor stage.
  obtain ⟨T, x', y', hx_map, hy_map⟩ :=
    exists_fg_subalgebras_tensorProduct_lift_pair (k := k) (R := A) (S := K) w.left w.right
  have h_inj := tensorProduct_map_injective_of_fgSubalgebraPair (k := k) (R := A) (S := K) T
  have hmul_nilpotent : IsNilpotent (x' * y') := by
    rw [← IsNilpotent.map_iff h_inj]
    simpa [map_mul, hx_map, hy_map] using w.mul_isNilpotent
  have hx_not_nilpotent : ¬ IsNilpotent x' := by
    intro hx_nilpotent
    apply w.left_not_isNilpotent
    simpa [hx_map] using hx_nilpotent.map (Algebra.TensorProduct.map T.left.val T.right.val)
  have hy_not_nilpotent : ¬ IsNilpotent y' := by
    intro hy_nilpotent
    apply w.right_not_isNilpotent
    simpa [hy_map] using hy_nilpotent.map (Algebra.TensorProduct.map T.left.val T.right.val)
  refine ⟨T, ?_⟩
  -- The descended elements give the same obstruction at the finite stage.
  exact ⟨{
    left := x'
    right := y'
    mul_isNilpotent := hmul_nilpotent
    left_not_isNilpotent := hx_not_nilpotent
    right_not_isNilpotent := hy_not_nilpotent
  }⟩

-- Proof sketch: after any field extension of `k`, tensoring with that field preserves injectivity
-- of `f`; irreducibility then descends along the induced map on prime spectra.
private theorem geometricallyIrreducible_of_injective {B : Type u} [CommRing B] [Algebra k B]
    (f : B →ₐ[k] A) (hf : Function.Injective f) :
    (GeomIrreducibleOver[k] A) → GeomIrreducibleOver[k] B := by
  intro hA
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange] at hA ⊢
  intro K _ _
  let g : B ⊗[k] K →ₐ[k] A ⊗[k] K :=
    Algebra.TensorProduct.map f (AlgHom.id k K)
  have hg : Function.Injective g := by
    -- Tensoring with a field preserves injectivity of the algebra map.
    simpa [g] using TensorProduct.map_injective_of_flat_flat
      f.toLinearMap (AlgHom.id k K).toLinearMap hf (AlgHom.id k K).injective
  -- Apply the ring-level irreducibility descent after base change.
  exact irreducibleSpace_primeSpectrum_of_injective g.toRingHom hg (hA K)

/-- Lemma 10.47.6 (1): every `k`-subalgebra of a geometrically irreducible `k`-algebra is
geometrically irreducible over `k`. -/
@[stacks 037N]
theorem geometricallyIrreducible_subalgebra (S : Subalgebra k A) :
    (GeomIrreducibleOver[k] A) → GeomIrreducibleOver[k] S :=
  geometricallyIrreducible_of_injective S.val Subtype.val_injective

instance (S : Subalgebra k A) [GeomIrreducibleOver[k] A] : GeomIrreducibleOver[k] S :=
  geometricallyIrreducible_subalgebra S inferInstance

/-- Lemma 10.47.6 (2): if every finitely generated `k`-subalgebra of `A` is geometrically
irreducible over `k`, then `A` is geometrically irreducible over `k`. -/
-- Proof sketch: every field-valued base change of `A` is the directed union of the corresponding
-- base changes of its finitely generated `k`-subalgebras, so irreducibility is detected on those
-- finitely generated stages.
@[stacks 037N]
theorem geometricallyIrreducible_of_forall_fg
    (h : ∀ S : Subalgebra k A, S.FG → GeomIrreducibleOver[k] S) :
    GeomIrreducibleOver[k] A := by
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange]
  intro K _ _
  by_contra hK
  have hbot :
      GeomIrreducibleOver[k] (⊥ : Subalgebra k A) :=
    h ⊥ Subalgebra.fg_bot
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange] at hbot
  have hbotk : IrreducibleSpace (PrimeSpectrum ((⊥ : Subalgebra k A) ⊗[k] k)) := hbot k
  letI : Nontrivial ((⊥ : Subalgebra k A) ⊗[k] k) :=
    nontrivial_of_irreducible_primeSpectrum hbotk
  let ebot : ((⊥ : Subalgebra k A) ⊗[k] k) ≃ (⊥ : Subalgebra k A) :=
    (Algebra.TensorProduct.rid k (⊥ : Subalgebra k A) (⊥ : Subalgebra k A)).toEquiv
  letI : Nontrivial (⊥ : Subalgebra k A) := ebot.injective.nontrivial
  have hbot_inj : Function.Injective ((⊥ : Subalgebra k A).val) := Subtype.val_injective
  letI : Nontrivial A := hbot_inj.nontrivial
  letI : Nontrivial (A ⊗[k] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
      (R := k) (A := A) (B := K) (algebraMap k K).injective
  have hwitness : Nonempty (NonprimeNilradicalWitness (A ⊗[k] K)) :=
    exists_nonprime_nilradical_witness_of_not_irreducibleSpace_primeSpectrum hK
  obtain ⟨T, ⟨w⟩⟩ :=
    exists_fg_subalgebras_tensorProduct_has_nonprime_nilradical_witness
      (k := k) (A := A) (K := K) hwitness
  let j : T.right →ₐ[k] K := T.right.val
  let g : T.left ⊗[k] T.right →ₐ[k] T.left ⊗[k] K :=
    Algebra.TensorProduct.map (AlgHom.id k T.left) j
  have hg : Function.Injective g := by
    -- Tensoring with the ambient field preserves injectivity of the right-hand inclusion.
    simpa [g, j] using TensorProduct.map_injective_of_flat_flat
      (AlgHom.id k T.left).toLinearMap j.toLinearMap
      Function.injective_id Subtype.val_injective
  have hTK : IrreducibleSpace (PrimeSpectrum (T.left ⊗[k] K)) := by
    -- The finitely generated left stage is geometrically irreducible by hypothesis.
    have hT : GeomIrreducibleOver[k] T.left := h T.left T.left_fg
    rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange] at hT
    exact hT K
  have hsmall : IrreducibleSpace (PrimeSpectrum (T.left ⊗[k] T.right)) :=
    irreducibleSpace_primeSpectrum_of_injective g.toRingHom hg hTK
  -- The finite-stage witness contradicts irreducibility of that finite tensor product.
  exact
    (not_irreducibleSpace_primeSpectrum_of_nonprime_nilradical_witness
      (R := T.left ⊗[k] T.right) ⟨w⟩) hsmall

end

section

variable {k I : Type u} [Field k] [Preorder I] [IsDirectedOrder I]

omit [IsDirectedOrder I] in
/-- Helper for Lemma 10.47.6: any finitely generated subalgebra of a filtered colimit of
`k`-algebras factors injectively through one stage. -/
private theorem exists_injective_stage_of_fg_subalgebra_colimit
    (F : I ⥤ CommAlgCat.{u} k) [Nonempty I] [IsFiltered I]
    (T : Subalgebra k (colimit F : CommAlgCat.{u} k)) (hT : T.FG) :
    ∃ (i : I) (φ : T →ₐ[k] F.obj i), Function.Injective φ := by
  let E := commAlgCatEquivUnder (CommRingCat.of k)
  let G : I ⥤ Under (CommRingCat.of k) := F ⋙ E.functor
  let c : Cocone G := E.functor.mapCocone (colimit.cocone F)
  have hc : IsColimit c := isColimitOfPreserves E.functor (colimit.isColimit F)
  have hfp : (algebraMap k T).FinitePresentation := by
    -- A finitely generated algebra over a field is finitely presented.
    simpa [RingHom.finitePresentation_algebraMap] using
      (Algebra.FinitePresentation.of_finiteType).mp ((Subalgebra.fg_iff_finiteType T).mp hT)
  let g : CommRingCat.mkUnder (CommRingCat.of k) T ⟶ c.pt := T.val.toUnder
  letI : IsFinitelyPresentable.{u} (CommRingCat.mkUnder (CommRingCat.of k) T) :=
    CommRingCat.isFinitelyPresentable_under
      (R := CommRingCat.of k) (S := CommRingCat.mkUnder (CommRingCat.of k) T) hfp
  obtain ⟨i, g', hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (X := CommRingCat.mkUnder (CommRingCat.of k) T) hc g
  let g'' :
      CommRingCat.mkUnder (CommRingCat.of k) T ⟶
        CommRingCat.mkUnder (CommRingCat.of k) (F.obj i) := by
    simpa [G, E] using g'
  let ιi : CommRingCat.mkUnder (CommRingCat.of k) (F.obj i) ⟶ c.pt := by
    simpa [G, E] using c.ι.app i
  have hg' : g = g'' ≫ ιi := by
    dsimp [g'', ιi]
    simpa [g, G, E] using hg.symm
  let φ : T →ₐ[k] F.obj i :=
    { __ := g''.right.hom
      commutes' := by
        intro x
        have hw := CommRingCat.hom_ext_iff.mp (Under.w g'')
        change ((CommRingCat.Hom.hom g''.right).comp (algebraMap k T)) x =
          (algebraMap k (F.obj i)) x
        simpa [CommRingCat.mkUnder_hom, CommRingCat.hom_comp] using DFunLike.congr_fun hw x }
  have hfac (x : T) : ιi.right (φ x) = T.val x := by
    -- The stage map factors the subalgebra inclusion into the colimit.
    have hw := CommRingCat.hom_ext_iff.mp (congrArg (fun f ↦ f.right) hg')
    simpa [g, φ, CommRingCat.hom_comp] using (DFunLike.congr_fun hw x).symm
  have hφ : Function.Injective φ := by
    intro x y hxy
    exact Subtype.ext <| by
      change T.val x = T.val y
      rw [← hfac x, ← hfac y, hxy]
  exact ⟨i, φ, hφ⟩

/-- Lemma 10.47.6 (3): a directed colimit of geometrically irreducible `k`-algebras is
geometrically irreducible over `k`. -/
-- Proof sketch: if the index type is empty, the colimit in `CommAlgCat k` is the initial
-- `k`-algebra `k`, which is geometrically irreducible by `Definition_10_47_4`. Otherwise every
-- finitely generated `k`-subalgebra of the colimit is generated by finitely many elements coming
-- from stages of the directed system; directedness moves those generators to a common stage, and
-- part `(2)` finishes.
@[stacks 037N]
theorem geometricallyIrreducible_colimit_of_directedSystem
    (F : I ⥤ CommAlgCat.{u} k)
    (hF : ∀ i, GeomIrreducibleOver[k] (F.obj i)) :
    GeomIrreducibleOver[k] (colimit F : CommAlgCat.{u} k) :=
  by
    by_cases hI : Nonempty I
    · letI : Nonempty I := hI
      letI : IsFiltered I := inferInstance
      -- Reduce the colimit statement to finitely generated subalgebras of the colimit.
      apply geometricallyIrreducible_of_forall_fg
      intro T hT
      obtain ⟨i, φ, hφ⟩ :=
        exists_injective_stage_of_fg_subalgebra_colimit (F := F) T hT
      -- Part `(1)` descends geometric irreducibility from that stage to the chosen subalgebra.
      exact geometricallyIrreducible_of_injective φ hφ (hF i)
    · letI : IsEmpty I := not_nonempty_iff.mp hI
      have hcolim : IsInitial (colimit F : CommAlgCat.{u} k) :=
        (isColimitEquivIsInitialOfIsEmpty (CommAlgCat.{u} k) (colimit.cocone F))
          (colimit.isColimit F)
      have hself : IsInitial (CommAlgCat.of k k) := CommAlgCat.isInitialSelf
      let e : (colimit F : CommAlgCat.{u} k) ≅ CommAlgCat.of k k :=
        hcolim.coconePointUniqueUpToIso hself
      let e' : (colimit F : CommAlgCat.{u} k) ≃ₐ[k] CommAlgCat.of k k :=
        CommAlgCat.algEquivOfIso e
      have hk : GeomIrreducibleOver[k] (CommAlgCat.of k k) := inferInstance
      -- The empty filtered colimit is just `k`, and geometric irreducibility descends across the
      -- resulting algebra equivalence.
      exact geometricallyIrreducible_of_injective e'.toAlgHom e'.injective hk

end

end Algebra
