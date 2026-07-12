import Mathlib
import StacksProject_2024.Chap10.Definition_10_82_1
import StacksProject_2024.Chap10.Definition_10_88_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u v w z

namespace LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v} [AddCommGroup N] [Module R N]
variable {M' : Type v} [AddCommGroup M'] [Module R M']

/-- Helper for Lemma 10.88.4: the difference map whose cokernel presents the pushout of `f`
and `g`. -/
def pushoutDifference (f : M →ₗ[R] N) (g : M →ₗ[R] M') : M →ₗ[R] N × M' :=
  LinearMap.prod (-f) g

/-- Helper for Lemma 10.88.4: the quotient module realizing the pushout of `f` and `g`. -/
abbrev pushoutQuotient (f : M →ₗ[R] N) (g : M →ₗ[R] M') :=
  (N × M') ⧸ LinearMap.range (pushoutDifference f g)

/-- Helper for Lemma 10.88.4: the left leg of the explicit quotient pushout model. -/
def pushoutQuotientInl (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    N →ₗ[R] pushoutQuotient f g :=
  (LinearMap.range (pushoutDifference f g)).mkQ.comp (LinearMap.inl R N M')

/-- Helper for Lemma 10.88.4: the right leg of the explicit quotient pushout model. -/
def pushoutQuotientInr (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    M' →ₗ[R] pushoutQuotient f g :=
  (LinearMap.range (pushoutDifference f g)).mkQ.comp (LinearMap.inr R N M')

/-- Helper for Lemma 10.88.4: the canonical map from `N × M'` to the pushout of `f` and `g`. -/
noncomputable def pushoutCopair (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    N × M' →ₗ[R] (pushout (ModuleCat.ofHom f) (ModuleCat.ofHom g) : ModuleCat R) :=
  let j := (pushout.inl (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom
  let i := (pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom
  LinearMap.coprod j i

variable (f : M →ₗ[R] N) (g : M →ₗ[R] M')

/-- Helper for Lemma 10.88.4: the quotient-model legs satisfy the pushout relation. -/
lemma pushout_quotient_condition :
    (pushoutQuotientInl f g).comp f = (pushoutQuotientInr f g).comp g := by
  -- The defining relation of the quotient identifies `(f x, 0)` with `(0, g x)`.
  ext x
  change Submodule.Quotient.mk
      (((LinearMap.inl R N M').comp f) x : N × M') =
    Submodule.Quotient.mk (((LinearMap.inr R N M').comp g) x : N × M')
  exact (Submodule.Quotient.eq _).2 ⟨-x, by
    simp [pushoutDifference]⟩

/-- Helper for Lemma 10.88.4: the quotient module with its canonical maps forms a pushout
cocone. -/
def pushoutQuotientCocone :
    PushoutCocone (ModuleCat.ofHom f) (ModuleCat.ofHom g) :=
  PushoutCocone.mk
    (ModuleCat.ofHom (pushoutQuotientInl f g))
    (ModuleCat.ofHom (pushoutQuotientInr f g))
    (by
      simpa [ModuleCat.ofHom_comp] using congrArg ModuleCat.ofHom (pushout_quotient_condition f g))

section QuotientModel

variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Helper for Lemma 10.88.4: a compatible pair of maps out of `N` and `M'` kills the range of
the pushout difference map. -/
lemma pushoutDifference_range_le_ker_coprod
    (β : N →ₗ[R] P) (γ : M' →ₗ[R] P) (hβγ : β.comp f = γ.comp g) :
    LinearMap.range (pushoutDifference f g) ≤ LinearMap.ker (LinearMap.coprod β γ) := by
  -- The compatibility `β ∘ f = γ ∘ g` is exactly the statement that the copair vanishes on the
  -- relation generators `( -f x, g x )`.
  rw [LinearMap.range_le_ker_iff]
  ext x
  have hx : β (f x) = γ (g x) := LinearMap.congr_fun hβγ x
  simpa [pushoutDifference, sub_eq_add_neg, add_comm] using sub_eq_zero.mpr hx.symm

/-- Helper for Lemma 10.88.4: the universal map out of the explicit quotient pushout model. -/
noncomputable def pushoutQuotientDesc
    (β : N →ₗ[R] P) (γ : M' →ₗ[R] P) (hβγ : β.comp f = γ.comp g) :
    pushoutQuotient f g →ₗ[R] P :=
  (LinearMap.range (pushoutDifference f g)).liftQ (LinearMap.coprod β γ)
    (pushoutDifference_range_le_ker_coprod (f := f) (g := g) β γ hβγ)

/-- Helper for Lemma 10.88.4: the quotient-model universal map restricts to `β` on the `N`
summand. -/
@[simp] lemma pushoutQuotientInl_desc
    (β : N →ₗ[R] P) (γ : M' →ₗ[R] P) (hβγ : β.comp f = γ.comp g) :
    (pushoutQuotientDesc (f := f) (g := g) β γ hβγ).comp (pushoutQuotientInl f g) = β := by
  -- The quotient lift is defined from the copair, so composing with the left inclusion recovers
  -- the left component.
  simp [pushoutQuotientDesc, pushoutQuotientInl, ← LinearMap.comp_assoc]

/-- Helper for Lemma 10.88.4: the quotient-model universal map restricts to `γ` on the `M'`
summand. -/
@[simp] lemma pushoutQuotientInr_desc
    (β : N →ₗ[R] P) (γ : M' →ₗ[R] P) (hβγ : β.comp f = γ.comp g) :
    (pushoutQuotientDesc (f := f) (g := g) β γ hβγ).comp (pushoutQuotientInr f g) = γ := by
  -- The same computation on the right summand recovers the right component.
  simp [pushoutQuotientDesc, pushoutQuotientInr, ← LinearMap.comp_assoc]

/-- Helper for Lemma 10.88.4: maps out of the quotient pushout model are determined by their
restrictions to the two summands. -/
lemma pushoutQuotientDesc_unique
    (β : N →ₗ[R] P) (γ : M' →ₗ[R] P) (hβγ : β.comp f = γ.comp g)
    {δ : pushoutQuotient f g →ₗ[R] P}
    (hδN : δ.comp (pushoutQuotientInl f g) = β)
    (hδM' : δ.comp (pushoutQuotientInr f g) = γ) :
    δ = pushoutQuotientDesc (f := f) (g := g) β γ hβγ := by
  -- Every quotient class is represented by a pair `(n, m')`, and that pair splits into the two
  -- obvious summands. Equality on those two summands determines the whole map.
  apply LinearMap.ext
  intro q
  refine
    Submodule.Quotient.induction_on (LinearMap.range (pushoutDifference f g)) q ?_
  intro z
  rcases z with ⟨n, m'⟩
  have hsplit :
      (Submodule.Quotient.mk (n, m') : pushoutQuotient f g) =
        Submodule.Quotient.mk (n, 0) + Submodule.Quotient.mk (0, m') := by
    simpa using
      (Submodule.Quotient.mk_add (LinearMap.range (pushoutDifference f g)) :
        (Submodule.Quotient.mk
            ((((n, (0 : M')) : N × M') + (((0 : N), m') : N × M')) :
              N × M') :
          pushoutQuotient f g) =
        Submodule.Quotient.mk (((n, (0 : M')) : N × M')) +
          Submodule.Quotient.mk (((0 : N), m') : N × M'))
  have hδN' :
      δ (Submodule.Quotient.mk (n, 0) : pushoutQuotient f g) = β n := by
    simpa [pushoutQuotientInl] using LinearMap.congr_fun hδN n
  have hδM'' :
      δ (Submodule.Quotient.mk (0, m') : pushoutQuotient f g) = γ m' := by
    simpa [pushoutQuotientInr] using LinearMap.congr_fun hδM' m'
  have hdescN :
      pushoutQuotientDesc (f := f) (g := g) β γ hβγ
          (Submodule.Quotient.mk (n, 0) : pushoutQuotient f g) =
        β n := by
    simpa [pushoutQuotientInl] using
      LinearMap.congr_fun (pushoutQuotientInl_desc (f := f) (g := g) β γ hβγ) n
  have hdescM' :
      pushoutQuotientDesc (f := f) (g := g) β γ hβγ
          (Submodule.Quotient.mk (0, m') : pushoutQuotient f g) =
        γ m' := by
    simpa [pushoutQuotientInr] using
      LinearMap.congr_fun (pushoutQuotientInr_desc (f := f) (g := g) β γ hβγ) m'
  rw [hsplit, map_add, map_add, hδN', hδM'', hdescN, hdescM']

end QuotientModel

/-- Helper for Lemma 10.88.4: the explicit quotient model satisfies the pushout universal
property. -/
noncomputable def pushoutQuotientIsColimit :
    IsColimit (pushoutQuotientCocone f g) :=
  PushoutCocone.IsColimit.mk
    (by
      simpa [ModuleCat.ofHom_comp] using congrArg ModuleCat.ofHom (pushout_quotient_condition f g))
    (fun s ↦ ModuleCat.ofHom <|
      pushoutQuotientDesc (f := f) (g := g) s.inl.hom s.inr.hom
        (congrArg ModuleCat.Hom.hom s.condition))
    (fun s ↦ ModuleCat.hom_ext <|
      pushoutQuotientInl_desc (f := f) (g := g) s.inl.hom s.inr.hom
        (congrArg ModuleCat.Hom.hom s.condition))
    (fun s ↦ ModuleCat.hom_ext <|
      pushoutQuotientInr_desc (f := f) (g := g) s.inl.hom s.inr.hom
        (congrArg ModuleCat.Hom.hom s.condition))
    (fun s m hmN hmM' ↦ ModuleCat.hom_ext <|
      pushoutQuotientDesc_unique (f := f) (g := g) s.inl.hom s.inr.hom
        (congrArg ModuleCat.Hom.hom s.condition)
        (congrArg ModuleCat.Hom.hom <| by simpa using hmN)
        (congrArg ModuleCat.Hom.hom <| by simpa using hmM'))

/-- Helper for Lemma 10.88.4: the categorical pushout is linearly equivalent to the explicit
quotient model. -/
noncomputable def pushout_quotient_equiv :
    (pushout (ModuleCat.ofHom f) (ModuleCat.ofHom g) : ModuleCat R) ≃ₗ[R] pushoutQuotient f g :=
  ((pushoutIsPushout (ModuleCat.ofHom f) (ModuleCat.ofHom g)).coconePointUniqueUpToIso
    (pushoutQuotientIsColimit f g)).toLinearEquiv

/-- Helper for Lemma 10.88.4: the pushout equivalence sends the categorical left leg to the
quotient-model left leg. -/
@[simp] lemma pushout_quotient_equiv_comp_inl :
    (pushout_quotient_equiv f g).toLinearMap.comp
        (pushout.inl (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom =
      pushoutQuotientInl f g := by
  -- This is the left-leg compatibility of the unique isomorphism between the two pushout cocones.
  simpa [pushout_quotient_equiv, pushoutQuotientCocone] using
    congrArg ModuleCat.Hom.hom
      ((pushoutIsPushout (ModuleCat.ofHom f) (ModuleCat.ofHom g)).comp_coconePointUniqueUpToIso_hom
        (pushoutQuotientIsColimit f g) WalkingSpan.left)

/-- Helper for Lemma 10.88.4: the pushout equivalence sends the categorical right leg to the
quotient-model right leg. -/
@[simp] lemma pushout_quotient_equiv_comp_inr :
    (pushout_quotient_equiv f g).toLinearMap.comp
        (pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom =
      pushoutQuotientInr f g := by
  -- The same compatibility holds for the right leg.
  simpa [pushout_quotient_equiv, pushoutQuotientCocone] using
    congrArg ModuleCat.Hom.hom
      ((pushoutIsPushout (ModuleCat.ofHom f) (ModuleCat.ofHom g)).comp_coconePointUniqueUpToIso_hom
        (pushoutQuotientIsColimit f g) WalkingSpan.right)

/-- Helper for Lemma 10.88.4: after distributing tensor products over the product, tensoring the
difference map becomes the expected pair `((-f) ⊗ 1, g ⊗ 1)`. -/
lemma prodLeft_rTensor_pushoutDifference
    {Q : Type w} [AddCommMonoid Q] [Module R Q] :
    (TensorProduct.prodLeft R R N M' Q).toLinearMap.comp ((pushoutDifference f g).rTensor Q) =
      LinearMap.prod (((-f).rTensor Q)) (g.rTensor Q) := by
  -- Both maps are determined on pure tensors, and on those tensors they agree coordinatewise.
  ext x q <;> rfl

/-- Helper for Lemma 10.88.4: after distributing tensor products over the product, tensoring the
right inclusion becomes the right inclusion of tensor products. -/
lemma prodLeft_rTensor_inr
    {Q : Type w} [AddCommMonoid Q] [Module R Q] :
    (TensorProduct.prodLeft R R N M' Q).toLinearMap.comp
        ((LinearMap.inr R N M').rTensor Q) =
      LinearMap.inr R (TensorProduct R N Q) (TensorProduct R M' Q) := by
  -- Again, it is enough to check the formula on pure tensors.
  ext m' q <;> simp

/-- Helper for Lemma 10.88.4: in the explicit quotient model, the tensor-kernel of the right leg
is described by witnesses from `ker (f ⊗ 1_Q)`. -/
lemma mem_ker_rTensor_pushoutQuotientInr_iff
    {Q : Type w} [AddCommMonoid Q] [Module R Q]
    (y : TensorProduct R M' Q) :
    y ∈ LinearMap.ker ((pushoutQuotientInr f g).rTensor Q) ↔
      ∃ x : TensorProduct R M Q, (f.rTensor Q) x = 0 ∧ (g.rTensor Q) x = y := by
  letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup R (M := Q)
  let q : N × M' →ₗ[R] pushoutQuotient f g := (LinearMap.range (pushoutDifference f g)).mkQ
  have hq_exact :
      Function.Exact ((pushoutDifference f g).rTensor Q) (q.rTensor Q) := by
    exact
      rTensor_exact Q (LinearMap.exact_map_mkQ_range (pushoutDifference f g))
        (Submodule.mkQ_surjective _)
  constructor
  · intro hy
    -- Move the kernel condition to the quotient map on `(N × M') ⊗ Q`.
    have hzero :
        (q.rTensor Q) (((LinearMap.inr R N M').rTensor Q) y) = 0 := by
      simpa [pushoutQuotientInr, LinearMap.rTensor_comp] using (show
        ((pushoutQuotientInr f g).rTensor Q) y = 0 by
          simpa [LinearMap.mem_ker] using hy)
    have hrange :
        ((LinearMap.inr R N M').rTensor Q) y ∈ LinearMap.range ((pushoutDifference f g).rTensor Q) := by
      rw [← hq_exact.linearMap_ker_eq]
      simpa [LinearMap.mem_ker] using hzero
    rcases hrange with ⟨x, hx⟩
    -- Distribute over the product to read off the two coordinate conditions.
    have hprod :
        (TensorProduct.prodLeft R R N M' Q) (((pushoutDifference f g).rTensor Q) x) =
          (((-f).rTensor Q) x, (g.rTensor Q) x) := by
      exact congrArg (fun φ ↦ φ x) (prodLeft_rTensor_pushoutDifference f g)
    have hinr :
        (TensorProduct.prodLeft R R N M' Q) (((LinearMap.inr R N M').rTensor Q) y) = (0, y) := by
      exact congrArg (fun φ ↦ φ y) (prodLeft_rTensor_inr (R := R) (N := N) (M' := M') (Q := Q))
    have hpair' : (((-f).rTensor Q) x, (g.rTensor Q) x) = (0, y) := by
      calc
        (((-f).rTensor Q) x, (g.rTensor Q) x)
            = (TensorProduct.prodLeft R R N M' Q) (((pushoutDifference f g).rTensor Q) x) := by
                simpa using hprod.symm
        _ = (TensorProduct.prodLeft R R N M' Q) (((LinearMap.inr R N M').rTensor Q) y) := by
              rw [hx]
        _ = (0, y) := hinr
    have hfst : ((-f).rTensor Q) x = 0 := congrArg Prod.fst hpair'
    have hsnd : (g.rTensor Q) x = y := congrArg Prod.snd hpair'
    refine ⟨x, ?_, hsnd⟩
    exact neg_eq_zero.mp <| by simpa using hfst
  · rintro ⟨x, hfx, hgx⟩
    -- Repackage the witness as an element of the range of the tensored difference map.
    have hx :
        ((pushoutDifference f g).rTensor Q) x = ((LinearMap.inr R N M').rTensor Q) y := by
      apply (TensorProduct.prodLeft R R N M' Q).injective
      have hprod :
          (TensorProduct.prodLeft R R N M' Q) (((pushoutDifference f g).rTensor Q) x) =
            (((-f).rTensor Q) x, (g.rTensor Q) x) := by
        exact congrArg (fun φ ↦ φ x) (prodLeft_rTensor_pushoutDifference f g)
      have hinr :
          (TensorProduct.prodLeft R R N M' Q) (((LinearMap.inr R N M').rTensor Q) y) = (0, y) := by
        exact congrArg (fun φ ↦ φ y)
          (prodLeft_rTensor_inr (R := R) (N := N) (M' := M') (Q := Q))
      have hpair : (((-f).rTensor Q) x, (g.rTensor Q) x) = (0, y) := by
        ext <;> simp [hfx, hgx]
      calc
        (TensorProduct.prodLeft R R N M' Q) (((pushoutDifference f g).rTensor Q) x)
            = (((-f).rTensor Q) x, (g.rTensor Q) x) := hprod
        _ = (0, y) := hpair
        _ = (TensorProduct.prodLeft R R N M' Q) (((LinearMap.inr R N M').rTensor Q) y) := by
              simpa using hinr.symm
    -- Exactness of the quotient sequence then forces the right-leg tensor to vanish.
    have hzero :
        (q.rTensor Q) (((LinearMap.inr R N M').rTensor Q) y) = 0 := by
      calc
        (q.rTensor Q) (((LinearMap.inr R N M').rTensor Q) y)
            = (q.rTensor Q) (((pushoutDifference f g).rTensor Q) x) := by rw [hx]
        _ = 0 := by
          simpa using LinearMap.congr_fun hq_exact.linearMap_comp_eq_zero x
    simpa [pushoutQuotientInr, LinearMap.rTensor_comp, LinearMap.mem_ker] using hzero

/-- Helper for Lemma 10.88.4: the pushout is the cokernel of the difference map
`x ↦ (-f x, g x)`. -/
lemma pushout_difference_exact :
    Function.Exact (pushoutDifference f g) (pushoutCopair f g) ∧
      Function.Surjective (pushoutCopair f g) := by
  let q : N × M' →ₗ[R] pushoutQuotient f g := (LinearMap.range (pushoutDifference f g)).mkQ
  let e := pushout_quotient_equiv (f := f) (g := g)
  have hq_exact : Function.Exact (pushoutDifference f g) q :=
    LinearMap.exact_map_mkQ_range (pushoutDifference f g)
  have hcopair :
      e.toLinearMap.comp (pushoutCopair f g) = q := by
    -- The pushout copair becomes the quotient map after passing through the quotient-model
    -- equivalence.
    calc
      e.toLinearMap.comp (pushoutCopair f g)
          = LinearMap.coprod (pushoutQuotientInl f g) (pushoutQuotientInr f g) := by
              rw [pushoutCopair, LinearMap.comp_coprod, pushout_quotient_equiv_comp_inl (f := f)
                (g := g), pushout_quotient_equiv_comp_inr (f := f) (g := g)]
      _ = q := by
            rw [pushoutQuotientInl, pushoutQuotientInr, ← LinearMap.comp_coprod,
              LinearMap.coprod_inl_inr, LinearMap.comp_id]
  refine ⟨?_, ?_⟩
  · -- Exactness is transported across the injective codomain equivalence.
    rw [LinearMap.exact_iff]
    calc
      LinearMap.ker (pushoutCopair f g)
          = LinearMap.ker (e.toLinearMap.comp (pushoutCopair f g)) := by
              symm
              apply LinearMap.ker_comp_of_ker_eq_bot
              rw [LinearMap.ker_eq_bot]
              exact e.injective
      _ = LinearMap.range (pushoutDifference f g) := by
            rw [hcopair, hq_exact.linearMap_ker_eq]
  · intro z
    -- Surjectivity is transported from the quotient map through the same equivalence.
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (LinearMap.range (pushoutDifference f g)) (e z)
    refine ⟨x, ?_⟩
    have hx' : q x = e z := by simpa using hx
    have hx'' : e ((pushoutCopair f g) x) = e z := by
      calc
        e ((pushoutCopair f g) x) = q x := by
          simpa [LinearMap.comp_apply] using congrArg (fun φ ↦ φ x) hcopair
        _ = e z := hx'
    exact e.injective hx''

/-- Helper for Lemma 10.88.4: after tensoring, the kernel of the pushout map `M' → N'`
consists exactly of the images of elements killed by `f ⊗ 1`. -/
lemma mem_ker_rTensor_pushout_inr_iff
    {Q : Type w} [AddCommMonoid Q] [Module R Q]
    (y : TensorProduct R M' Q) :
    y ∈ LinearMap.ker (((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q) ↔
      ∃ x : TensorProduct R M Q, (f.rTensor Q) x = 0 ∧ (g.rTensor Q) x = y := by
  let e := pushout_quotient_equiv f g
  have hcomp :
      ((e.toLinearMap).rTensor Q).comp
          (((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q) =
        (pushoutQuotientInr f g).rTensor Q := by
    -- Tensoring commutes with composition, so the quotient-model comparison remains compatible
    -- after tensoring.
    rw [← LinearMap.rTensor_comp]
    simpa using congrArg (fun φ ↦ φ.rTensor Q) (pushout_quotient_equiv_comp_inr (f := f) (g := g))
  constructor
  · intro hy
    have hzero :
        (((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q) y = 0 := by
      simpa [LinearMap.mem_ker] using hy
    have hzero' : ((pushoutQuotientInr f g).rTensor Q) y = 0 := by
      calc
        ((pushoutQuotientInr f g).rTensor Q) y
            = (((e.toLinearMap).rTensor Q).comp
                (((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q)) y := by
                  rw [hcomp]
        _ = ((e.toLinearMap).rTensor Q) 0 := by simp [hzero]
        _ = 0 := by simp
    exact (mem_ker_rTensor_pushoutQuotientInr_iff (f := f) (g := g) y).1 <| by
      simpa [LinearMap.mem_ker] using hzero'
  · rintro ⟨x, hfx, hgx⟩
    have hzero' : ((pushoutQuotientInr f g).rTensor Q) y = 0 := by
      simpa [LinearMap.mem_ker] using
        (mem_ker_rTensor_pushoutQuotientInr_iff (f := f) (g := g) y).2 ⟨x, hfx, hgx⟩
    have hzero :
        (((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q) y = 0 := by
      apply (e.rTensor Q).injective
      calc
        ((e.toLinearMap).rTensor Q)
            ((((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q) y)
            = ((((e.toLinearMap).rTensor Q).comp
                (((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q)) y) := by
                  rfl
        _ = ((pushoutQuotientInr f g).rTensor Q) y := by rw [hcomp]
        _ = 0 := hzero'
    simpa [LinearMap.mem_ker] using hzero

/-- Helper for Lemma 10.88.4: after tensoring with `Q`, injectivity of the pushout map is
equivalent to the domination condition for that same `Q`. -/
lemma injective_rTensor_pushout_inr_iff
    {Q : Type w} [AddCommMonoid Q] [Module R Q] :
    Function.Injective (((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q) ↔
      LinearMap.ker (f.rTensor Q) ≤ LinearMap.ker (g.rTensor Q) := by
  constructor
  · intro hinj
    intro x hx
    -- A tensor element killed by `f ⊗ 1` gives a kernel element for the pushout map.
    have hy :
        (g.rTensor Q) x ∈
          LinearMap.ker (((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom).rTensor Q) := by
      exact (mem_ker_rTensor_pushout_inr_iff (f := f) (g := g) ((g.rTensor Q) x)).2
        ⟨x, by simpa [LinearMap.mem_ker] using hx, rfl⟩
    have hy_zero : (g.rTensor Q) x = 0 := by
      exact hinj <| by simpa [LinearMap.mem_ker] using hy
    simpa [LinearMap.mem_ker] using hy_zero
  · -- The reverse implication is the kernel-triviality reformulation of injectivity.
    intro hdomQ
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff _]
    intro y hy
    rcases (mem_ker_rTensor_pushout_inr_iff (f := f) (g := g) y).1 hy with ⟨x, hfx, hgx⟩
    have hgx_zero : (g.rTensor Q) x = 0 := hdomQ <| by simpa [LinearMap.mem_ker] using hfx
    simpa [LinearMap.mem_ker] using hgx.symm.trans hgx_zero

-- Proof sketch: identify the pushout of `f` and `g` with the cokernel of the map
-- `x ↦ (g x, -f x)` from `M` to `M' ⊕ N`. After tensoring with any `R`-module `Q`, the kernel of
-- the induced map from `M' ⊗[R] Q` is the quotient of `ker (f.rTensor Q)` by
-- `ker (f.rTensor Q) ∩ ker (g.rTensor Q)`. Thus the pushout map is injective after tensoring with
-- `Q` exactly when `ker (f.rTensor Q) ≤ ker (g.rTensor Q)`, which is the domination condition.
/-- Helper for Lemma 10.88.4: once the test-module universe is fixed to `max u v`, the domination
condition is exactly universal injectivity of the pushout map in that same universe. -/
lemma dominates_iff_universallyInjective_pushout_inr_fixed_universe
    (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    g.Dominates f ↔
      LinearMap.UniversallyInjective.{u, v, v, max u v}
        ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom) := by
  -- Route correction: the pushout/tensor kernel computation is already complete; the remaining
  -- work is only to align `UniversallyInjective` with the fixed test-module universe of
  -- `Dominates`.
  constructor
  · intro hdom
    intro Q _ _
    -- For this fixed `Q`, the kernel criterion turns domination directly into injectivity.
    exact (injective_rTensor_pushout_inr_iff (f := f) (g := g) (Q := Q)).2 (hdom Q)
  · intro huniv
    intro Q _ _
    -- Specializing universal injectivity to the same `Q` recovers the domination inequality.
    exact (injective_rTensor_pushout_inr_iff (f := f) (g := g) (Q := Q)).1
      (huniv Q (Module.addCommMonoidToAddCommGroup R (M := Q)) inferInstance)

/-- Lemma 10.88.4: for maps `f : M →ₗ[R] N` and `g : M →ₗ[R] M'`, the map `g` dominates `f` if
and only if the canonical map `f' : M' → N'` in the pushout square of `f` and `g` is universally
injective. -/
@[stacks 0AUM]
theorem dominates_iff_universallyInjective_pushout_inr (f : M →ₗ[R] N) (g : M →ₗ[R] M') :
    g.Dominates f ↔
      LinearMap.UniversallyInjective.{u, v, v, max u v}
        ((pushout.inr (ModuleCat.ofHom f) (ModuleCat.ofHom g)).hom) := by
  -- Route correction: the theorem must use the same test-module universe as `Dominates`; after
  -- that alignment, the fixed-universe helper closes the proof immediately.
  simpa using dominates_iff_universallyInjective_pushout_inr_fixed_universe (f := f) (g := g)

end

end LinearMap
