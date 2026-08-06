import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.Monoidal

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex
open HomologicalComplex

universe u

-- Semantic recall via `lean_leansearch`: `HomologicalComplex.tensorObj` is the canonical tensor
-- product of chain complexes, and `HomComplex` is mathlib's canonical
-- mapping complex for `ℤ`-indexed cochain complexes. Definition 17.5.1 packages that mapping
-- complex back into chain-complex conventions through `ChainComplex.cochainComplexEquivalence`.

/-- The standard tensor-product sign convention on `ℤ`-indexed chain complexes. -/
private instance downIntTensorSigns : (ComplexShape.down ℤ).TensorSigns where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r hpq := by
    dsimp at hpq ⊢
    lia
  add_rel p q r hpq := by
    dsimp at hpq ⊢
    lia
  ε'_succ p q hpq := by
    have hq : q = p - 1 := by
      dsimp at hpq
      lia
    subst hq
    change (p - 1).negOnePow = -p.negOnePow
    rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one]

/-- The canonical cochain-complex view of a `ℤ`-indexed chain complex. -/
private abbrev asCochainComplex (R : Type u) [CommRing R]
    (K : ChainComplex (ModuleCat R) ℤ) : CochainComplex (ModuleCat R) ℤ :=
  (ChainComplex.cochainComplexEquivalence (ModuleCat R)).functor.obj K

/-- An auxiliary cochain-level model for the internal Hom between two chain complexes. -/
private def cochainHomComplex (R : Type u) [CommRing R]
    (B M : ChainComplex (ModuleCat R) ℤ) : CochainComplex (ModuleCat R) ℤ :=
  let B' := asCochainComplex R B
  let M' := asCochainComplex R M
  { X := fun n ↦ ModuleCat.of R (Cochain B' M' n)
    d := fun n m ↦ ModuleCat.ofHom (δ_hom R B' M' n m)
    shape := by
      intro n m hnm
      apply ModuleCat.hom_ext
      ext z p q hpq x
      exact congrArg (fun w ↦ (w.v p q hpq).hom x)
        (δ_shape n m hnm z)
    d_comp_d' := by
      intro n m l _ _
      apply ModuleCat.hom_ext
      ext z p q hpq x
      exact congrArg (fun w ↦ (w.v p q hpq).hom x)
        (δ_δ n m l z) }

/-- The chain-level Hom complex obtained by reindexing mathlib's canonical cochain mapping complex
back to `ℤ`-indexed chain complexes. -/
abbrev chainHomComplex (R : Type u) [CommRing R]
    (B M : ChainComplex (ModuleCat R) ℤ) : ChainComplex (ModuleCat R) ℤ :=
  (ChainComplex.cochainComplexEquivalence (ModuleCat R)).inverse.obj (cochainHomComplex R B M)

/-- Projection from a degree `i` term of `chainHomComplex R B M` to the component
`B.X r ⟶ M.X n`, with the double-negation reindexing made explicit. -/
def chainHomComplexProjAt (R : Type u) [CommRing R]
    (B M : ChainComplex (ModuleCat R) ℤ) (i r n : ℤ) (hir : i + r = n) :
    (chainHomComplex R B M).X i ⟶ (B.X r ⟶[ModuleCat R] M.X n) :=
  ModuleCat.ofHom
    { toFun := fun z ↦
        (B.XIsoOfEq (by simp)).hom ≫
          z.v (-r) (-n) (by
            simpa [neg_add_rev, add_comm] using congrArg Neg.neg hir) ≫
          (M.XIsoOfEq (by simp)).inv
      map_add' := by
        intro z z'
        -- The visible component of a sum cochain is the sum of the visible components.
        apply ModuleCat.hom_ext
        ext x
        simpa using
          ((M.XIsoOfEq (by simp)).inv.hom.map_add
            (((z.v (-r) (-n) (by simpa [neg_add_rev, add_comm] using congrArg Neg.neg hir)).hom)
              (((B.XIsoOfEq (by simp)).hom.hom) x))
            (((z'.v (-r) (-n) (by simpa [neg_add_rev, add_comm] using congrArg Neg.neg hir)).hom)
              (((B.XIsoOfEq (by simp)).hom.hom) x)))
      map_smul' := by
        intro a z
        -- Scalar multiplication is computed componentwise on the chosen cochain entry.
        apply ModuleCat.hom_ext
        ext x
        simpa using
          ((M.XIsoOfEq (by simp)).inv.hom.map_smul a
            (((z.v (-r) (-n) (by simpa [neg_add_rev, add_comm] using congrArg Neg.neg hir)).hom)
              (((B.XIsoOfEq (by simp)).hom.hom) x))) }

/-- Helper for Definition 17.5.1: `ModuleCat.monoidalClosedHomEquiv` evaluates by applying the
underlying curried bilinear map to the tensor generator. -/
private theorem monoidalClosedHomEquiv_hom₂_apply (R : Type u) [CommRing R]
    {M N P : ModuleCat R} (f : M ⊗ N ⟶ P) (n : N) (m : M) :
    ((ModuleCat.monoidalClosedHomEquiv M N P f).hom₂ n) m =
      ((β_ N M).hom ≫ f) (n ⊗ₜ[R] m) := rfl

/-- Helper for Definition 17.5.1: negating a visible cochain degree relation produces the
corresponding chain-level index relation for `chainHomComplexProjAt`. -/
private theorem chainHomComplexProjAt_relation {i p q : ℤ} (hpq : p + (-i) = q) :
    i + (-p) = -q := by
  -- This is the exact arithmetic conversion used when passing from cochain indices to chain indices.
  simpa [neg_add_rev, add_comm] using congrArg Neg.neg hpq

/-- Helper for Definition 17.5.1: evaluating a cochain on a triplet does not depend on the chosen
proof of the degree equation. -/
private theorem cochain_v_proofIrrel (R : Type u) [CommRing R]
    {B M : ChainComplex (ModuleCat R) ℤ} {n p q : ℤ}
    (z : Cochain (asCochainComplex R B) (asCochainComplex R M) n)
    (h₁ h₂ : p + n = q) :
    z.v p q h₁ = z.v p q h₂ := by
  -- The proof component in `Triplet` is propositional, so the two triplets are definitionally equal
  -- up to proof irrelevance and evaluate to the same morphism.
  change z ⟨p, q, h₁⟩ = z ⟨p, q, h₂⟩
  congr

/-- Helper for Definition 17.5.1: the pointwise evaluation of a visible cochain component is also
independent of the chosen degree proof. -/
private theorem cochain_v_apply_proofIrrel (R : Type u) [CommRing R]
    {B M : ChainComplex (ModuleCat R) ℤ} {i p q : ℤ}
    (z : (chainHomComplex R B M).X i) (h₁ h₂ : p + (-i) = q) (b : B.X (-p)) :
    ((z.v p q h₁).hom b) = ((z.v p q h₂).hom b) := by
  -- Apply the proof-irrelevance bridge at the morphism level and then evaluate at `b`.
  simpa using
    congrArg (fun f : B.X (-p) ⟶ M.X (-q) => f.hom b)
      (cochain_v_proofIrrel R (B := B) (M := M) (n := -i) z h₁ h₂)

/-- Helper for Definition 17.5.1: negating the chain-level relation produced from `hpq` returns to
the original visible cochain relation. -/
private theorem chainHomComplexProjAt_relation_roundTrip {i p q : ℤ} (hpq : p + (-i) = q) :
    (by
      simpa [neg_add_rev, add_comm] using
        congrArg Neg.neg (chainHomComplexProjAt_relation hpq) : p + (-i) = q) = hpq := by
  -- The round-trip relation lives in a proposition, so proof irrelevance identifies the two proofs.
  apply Subsingleton.elim

/-- Helper for Definition 17.5.1: evaluating an `eqToHom` in `ModuleCat` is just the corresponding
transport of the element. -/
private theorem moduleCatEqToHom_hom_apply (R : Type u) [CommRing R]
    {X Y : ModuleCat R} (h : X = Y) (x : X) :
    (((eqToHom h : X ⟶ Y).hom) x) = cast (by cases h; rfl) x := by
  -- Collapse the owner-side transport by reducing to the reflexive equality case.
  cases h
  rfl

/-- Helper for Definition 17.5.1: evaluating a `ModuleCat` morphism sandwiched between two
`eqToHom` transports amounts to transporting the input into the source, applying the morphism,
and transporting the result back out. -/
private theorem moduleCatEqToHomSandwich_apply (R : Type u) [CommRing R]
    {X X' Y Y' : ModuleCat R} (hX : X' = X) (f : X ⟶ Y) (hY : Y = Y') (x : X') :
    (((eqToHom hX ≫ f ≫ eqToHom hY).hom) x) =
      cast (by cases hY; rfl) (f.hom (cast (by cases hX; rfl) x)) := by
  -- Reduce both transports to the reflexive equality case so only the underlying linear map remains.
  cases hX
  cases hY
  rfl

/-- Helper for Definition 17.5.1: the codomain-side `eqToHom` cast coming from the
`asCochainComplex` reindexing also acts trivially on elements. -/
private theorem asCochainComplexOutputCast_apply (R : Type u) [CommRing R]
    {K : ChainComplex (ModuleCat R) ℤ} {n : ℤ} (x : (asCochainComplex R K).X n) :
    (((eqToHom
      (show (asCochainComplex R K).X n = K.X (-n) by
        simp [asCochainComplex, ChainComplex.cochainComplexEquivalence]))).hom x) = x := by
  rfl

/-- Helper for Definition 17.5.1: the source-side cast from `K.X (-n)` to the corresponding
term of `asCochainComplex R K` is also the identity on elements. -/
private theorem asCochainComplexInputCast_apply (R : Type u) [CommRing R]
    {K : ChainComplex (ModuleCat R) ℤ} {n : ℤ} (x : K.X (-n)) :
    cast
      (show ↑(K.X (-n)) = ↑((asCochainComplex R K).X n) by
        simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
      x = x := by
  rfl

/-- Helper for Definition 17.5.1: the exact source-side cast appearing in the normalized
projection formula is the identity on the visible element. -/
private theorem chainHomComplexProjAtNormalizedSourceCast_apply (R : Type u) [CommRing R]
    {B : ChainComplex (ModuleCat R) ℤ} {p : ℤ} (b : B.X (-p)) :
    cast
      (show (B.X (-p) : Type u) = ((asCochainComplex R B).X (- -p) : Type u) by
        simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
      b =
        (show (asCochainComplex R B).X (- -p) from by
          simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b) := by
  -- Specialize the generic input-cast collapse to the double-negated index used by the normalized
  -- projection formula.
  rfl

/-- Helper for Definition 17.5.1: the identity `XIsoOfEq` on a chain-complex term acts trivially on
elements. -/
private theorem chainHomComplexProjAtXIso_hom_apply (R : Type u) [CommRing R]
    {K : ChainComplex (ModuleCat R) ℤ} {n : ℤ} (x : K.X n) :
    ((((K.XIsoOfEq (by simp) : K.X n ≅ K.X n).hom).hom) x) = x := by
  -- The `XIsoOfEq` generated by a reflexive index equality is definitionally the identity.
  simp [HomologicalComplex.XIsoOfEq]

/-- Helper for Definition 17.5.1: the inverse identity `XIsoOfEq` on a chain-complex term also
acts trivially on elements. -/
private theorem chainHomComplexProjAtXIso_inv_apply (R : Type u) [CommRing R]
    {K : ChainComplex (ModuleCat R) ℤ} {n : ℤ} (x : K.X n) :
    ((((K.XIsoOfEq (by simp) : K.X n ≅ K.X n).inv).hom) x) = x := by
  -- The inverse of a reflexive `XIsoOfEq` is still the identity map.
  simp [HomologicalComplex.XIsoOfEq]

/-- Helper for Definition 17.5.1: projecting a fixed cochain by `chainHomComplexProjAt` first
exposes the visible composite of reindexing isomorphisms and the chosen `v`-component. -/
private theorem chainHomComplexProjAt_hom_eq_visibleComposite (R : Type u) [CommRing R]
    {B M : ChainComplex (ModuleCat R) ℤ} {i r n : ℤ} (hir : i + r = n)
    (z : (chainHomComplex R B M).X i) :
    ((chainHomComplexProjAt R B M i r n hir).hom z) =
      (B.XIsoOfEq (by simp)).hom ≫
        z.v (-r) (-n) (by
          simpa [neg_add_rev, add_comm] using congrArg Neg.neg hir) ≫
        (M.XIsoOfEq (by simp)).inv := by
  -- Unfold the projection once, at the morphism level, so later proofs can rewrite through it.
  rfl

attribute [local simp] ChainComplex.cochainComplexEquivalence HomologicalComplex.XIsoOfEq in
/-- Helper for Definition 17.5.1: the normalized visible degree proof obtained from
`chainHomComplexProjAt_relation rfl` is propositionally equal to `rfl`. -/
private theorem chainHomComplexProjAt_component_apply_normalized_proof_eq_rfl
    {i p : ℤ} :
    (by
      simpa [neg_add_rev, add_comm] using
        congrArg Neg.neg (chainHomComplexProjAt_relation (i := i) (p := p) (q := p + (-i)) rfl) :
      p + (-i) = p + (-i)) = rfl := by
  -- The degree equality lives in a proposition, so the normalized witness and `rfl` coincide.
  apply Subsingleton.elim

/-- Helper for Definition 17.5.1: the visible cochain degree relation appearing in the normalized
projection formula is exactly the double-negation rewrite of `rfl`. -/
private theorem chainHomComplexProjAt_component_apply_normalized_visibleRelation
    {i p : ℤ} :
    (- -p) + (-i) = - -(p + (-i)) := by
  -- This is the arithmetic identity underlying the visible `v`-component in the normalized
  -- projection formula.
  simpa [neg_add_rev, add_comm] using
    congrArg Neg.neg
      (chainHomComplexProjAt_relation (i := i) (p := p) (q := p + (-i)) rfl)

/-- Helper for Definition 17.5.1: the visible composite defining the normalized projection acts on
an element by transporting into the cochain source, applying the visible component, and
transporting back out of the cochain target. -/
private theorem chainHomComplexProjAtVisibleComposite_apply_castBridge
    (R : Type u) [CommRing R] {B M : ChainComplex (ModuleCat R) ℤ} {i p : ℤ}
    (z : (chainHomComplex R B M).X i) (b : B.X (-p)) :
    ((((eqToHom
          (show B.X (-p) = (asCochainComplex R B).X (- -p) by
            simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])) ≫
          z.v (- -p) (- -(p + (-i)))
            chainHomComplexProjAt_component_apply_normalized_visibleRelation ≫
          eqToHom
            (show (asCochainComplex R M).X (- -(p + (-i))) = M.X (-(p + (-i))) by
              simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])).hom) b) =
      cast
        (show ↑((asCochainComplex R M).X (- -(p + (-i)))) = ↑(M.X (-(p + (-i)))) by
          simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
        (((z.v (- -p) (- -(p + (-i)))
            chainHomComplexProjAt_component_apply_normalized_visibleRelation).hom)
          (cast
            (show (B.X (-p) : Type u) = ((asCochainComplex R B).X (- -p) : Type u) by
              simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
            b)) := by
  -- Evaluate the transport sandwich on `b`; this packages the exact input and output casts.
  simpa using
    moduleCatEqToHomSandwich_apply R
      (hX := show B.X (-p) = (asCochainComplex R B).X (- -p) by
        simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
      (f := z.v (- -p) (- -(p + (-i)))
        chainHomComplexProjAt_component_apply_normalized_visibleRelation)
      (hY := show (asCochainComplex R M).X (- -(p + (-i))) = M.X (-(p + (-i))) by
        simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
      b

attribute [local simp] ChainComplex.cochainComplexEquivalence HomologicalComplex.XIsoOfEq in
/-- Helper for Definition 17.5.1: the exact normalized output cast in the projection formula is
the identity on the visible target element. -/
private theorem chainHomComplexProjAtNormalizedOutputCast_apply
    (R : Type u) [CommRing R] {M : ChainComplex (ModuleCat R) ℤ} {i p : ℤ}
    (x : (asCochainComplex R M).X (- -(p + (-i)))) :
    cast
      (show ↑((asCochainComplex R M).X (- -(p + (-i)))) = ↑(M.X (-(p + (-i)))) by
        simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
      x =
        (show M.X (-(p + (-i))) from by
          simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using x) := by
  -- Specialize the generic output-cast collapse to the normalized target index.
  simpa using
    (asCochainComplexOutputCast_apply R (K := M) (n := - -(p + (-i))) x)

attribute [local simp] ChainComplex.cochainComplexEquivalence HomologicalComplex.XIsoOfEq in
/-- Helper for Definition 17.5.1: after moving the source element into the cochain carrier, the
normalized visible component is independent of whether we use the arithmetic normalization witness
or the canonical double-negated witness. -/
private theorem chainHomComplexProjAtNormalizedVisibleCanonical_apply
    (R : Type u) [CommRing R] {B M : ChainComplex (ModuleCat R) ℤ} {i p : ℤ}
    (z : (chainHomComplex R B M).X i) (b : B.X (-p)) :
    (((z.v (- -p) (- -(p + (-i)))
        chainHomComplexProjAt_component_apply_normalized_visibleRelation).hom)
      (show (asCochainComplex R B).X (- -p) from by
        simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b)) =
      (((z.v (- -p) (- -(p + (-i)))
          (by
            simpa using
              (rfl : p + (-i) = p + (-i)))).hom)
        (show (asCochainComplex R B).X (- -p) from by
          simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b)) := by
  -- Route correction: isolate the witness replacement first, so the remaining blocker is only the
  -- explicit codomain cast from the canonical double-negated component to the public component.
  exact cochain_v_apply_proofIrrel R
    (z := z)
    (h₁ := chainHomComplexProjAt_component_apply_normalized_visibleRelation)
    (h₂ := by
      simpa using
        (rfl : p + (-i) = p + (-i)))
    (b := show B.X (- (- -p)) from by
      simpa using b)

attribute [local simp] ChainComplex.cochainComplexEquivalence HomologicalComplex.XIsoOfEq in
/-- Helper for Definition 17.5.1: the canonical double-negated visible triplet is exactly the
public visible triplet. -/
private theorem chainHomComplexProjAtCanonicalVisibleTriplet_eq {i p : ℤ} :
    (⟨- -p, - -(p + (-i)),
        (by
          simpa using
            (rfl : p + (-i) = p + (-i)))⟩ : Triplet (-i)) =
      ⟨p, p + (-i), rfl⟩ := by
  -- Normalize the visible indices once at the `Triplet` level so later transport lemmas can reuse
  -- the same arithmetic equality instead of rebuilding it locally.
  congr <;> simp

/-- Helper for Definition 17.5.1: the canonical double-negated visible component is the public
visible component, up to the precise `eqToHom` source and target transports induced by the triplet
equality. -/
private theorem chainHomComplexProjAtCanonicalVisibleTransport
    (R : Type u) [CommRing R] {B M : ChainComplex (ModuleCat R) ℤ} {i p : ℤ}
    (z : (chainHomComplex R B M).X i) :
    z ⟨- -p, - -(p + (-i)),
        by
          simpa using
            (rfl : p + (-i) = p + (-i))⟩ =
      eqToHom
          (congrArg
            (fun T : Triplet (-i) => (asCochainComplex R B).X T.p)
            (chainHomComplexProjAtCanonicalVisibleTriplet_eq (i := i) (p := p))) ≫
        z ⟨p, p + (-i), rfl⟩ ≫
          eqToHom
            (congrArg
              (fun T : Triplet (-i) => (asCochainComplex R M).X T.q)
              (chainHomComplexProjAtCanonicalVisibleTriplet_eq (i := i) (p := p)).symm) := by
  -- Use the owner-side dependent congruence theorem, so later proofs only have to normalize the
  -- explicit source and target casts produced by the triplet equality.
  simpa using
    (CategoryTheory.dcongr_arg
      (F := fun T : Triplet (-i) => (asCochainComplex R B).X T.p)
      (G := fun T : Triplet (-i) => (asCochainComplex R M).X T.q)
      z
      (chainHomComplexProjAtCanonicalVisibleTriplet_eq (i := i) (p := p)))

attribute [local simp] ChainComplex.cochainComplexEquivalence HomologicalComplex.XIsoOfEq in
  /-- Helper for Definition 17.5.1: once the visible source is already written in the cochain
carrier, the canonical double-negated visible component is exactly the public component after
normalizing only the codomain spelling. -/
private theorem chainHomComplexProjAtCanonicalVisibleCodomainCast_apply
    (R : Type u) [CommRing R] {B M : ChainComplex (ModuleCat R) ℤ} {i p : ℤ}
    (z : (chainHomComplex R B M).X i) (b : B.X (-p)) :
    (((z.v (- -p) (- -(p + (-i)))
        (by
          simpa using
            (rfl : p + (-i) = p + (-i)))).hom)
      (show (asCochainComplex R B).X (- -p) from by
        simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b)) =
      (show (asCochainComplex R M).X (- -(p + (-i))) from by
        simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using
          ((z.v p (p + (-i)) rfl).hom b)) := by
  -- Replace the canonical double-negated visible component by the public one together with its
  -- exact source and codomain transports.
  let hSource :
      (asCochainComplex R B).X (- -p) = (asCochainComplex R B).X p :=
    congrArg
      (fun T : Triplet (-i) => (asCochainComplex R B).X T.p)
      (chainHomComplexProjAtCanonicalVisibleTriplet_eq (i := i) (p := p))
  let hTarget :
      (asCochainComplex R M).X (p + (-i)) = (asCochainComplex R M).X (- -(p + (-i))) :=
    congrArg
      (fun T : Triplet (-i) => (asCochainComplex R M).X T.q)
      (chainHomComplexProjAtCanonicalVisibleTriplet_eq (i := i) (p := p)).symm
  let b' : (asCochainComplex R B).X (- -p) := by
    simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b
  let bPublic : (asCochainComplex R B).X p := by
    simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b
  let mPublic : (asCochainComplex R M).X (p + (-i)) := by
    simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using
      ((z.v p (p + (-i)) rfl).hom b)
  have htransport :=
    chainHomComplexProjAtCanonicalVisibleTransport
      R (B := B) (M := M) (i := i) (p := p) z
  have hSourceApply :
      (((eqToHom hSource).hom) b') = bPublic := by
    -- The source-side `eqToHom` is exactly the reindexing identification from `- -p` to `p`.
    simpa [b', bPublic, asCochainComplex, ChainComplex.cochainComplexEquivalence] using
      (moduleCatEqToHom_hom_apply R hSource b')
  have hTargetApply :
      (((eqToHom hTarget).hom) mPublic) =
        (show (asCochainComplex R M).X (- -(p + (-i))) from by
          simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using
            ((z.v p (p + (-i)) rfl).hom b)) := by
    -- The codomain-side `eqToHom` is the matching reindexing identification from `p + (-i)` to
    -- `- -(p + (-i))`.
    simpa [mPublic, asCochainComplex, ChainComplex.cochainComplexEquivalence] using
      (moduleCatEqToHom_hom_apply R hTarget mPublic)
  calc
    (((z.v (- -p) (- -(p + (-i)))
          (by
            simpa using
              (rfl : p + (-i) = p + (-i)))).hom)
        (show (asCochainComplex R B).X (- -p) from by
          simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b)) =
      (((eqToHom hSource ≫ z.v p (p + (-i)) rfl ≫ eqToHom hTarget).hom) b') := by
      -- Evaluate the transport identity on the source element already moved into the cochain
      -- carrier.
      simpa [b', hSource, hTarget] using
        congrArg (fun f => f.hom b') htransport
    _ =
      (((eqToHom hTarget).hom)
        (((z.v p (p + (-i)) rfl).hom) (((eqToHom hSource).hom) b'))) := by
      -- Expand the categorical composition before normalizing the two transport maps separately.
      rfl
    _ =
      (((eqToHom hTarget).hom) (((z.v p (p + (-i)) rfl).hom) bPublic)) := by
      -- Rewrite the source transport into the public cochain-side spelling of `b`.
      rw [hSourceApply]
    _ = (((eqToHom hTarget).hom) mPublic) := by
      -- The visible public component on `bPublic` is exactly the public codomain-side value.
      simp [mPublic, bPublic, asCochainComplex, ChainComplex.cochainComplexEquivalence]
    _ =
      (show (asCochainComplex R M).X (- -(p + (-i))) from by
        simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using
          ((z.v p (p + (-i)) rfl).hom b)) := by
      -- Rewrite the target transport into the final public cochain-side spelling.
      exact hTargetApply

attribute [local simp] ChainComplex.cochainComplexEquivalence HomologicalComplex.XIsoOfEq in
/-- Helper for Definition 17.5.1: once the source element is already written in the cochain
carrier, the normalized visible component agrees with the public component in that same cochain
carrier. -/
private theorem chainHomComplexProjAtNormalizedVisibleTargetCast_apply
    (R : Type u) [CommRing R] {B M : ChainComplex (ModuleCat R) ℤ} {i p : ℤ}
    (z : (chainHomComplex R B M).X i) (b : B.X (-p)) :
    (((z.v (- -p) (- -(p + (-i)))
        chainHomComplexProjAt_component_apply_normalized_visibleRelation).hom)
      (show (asCochainComplex R B).X (- -p) from by
        simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b)) =
      (show (asCochainComplex R M).X (- -(p + (-i))) from by
        simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using
          ((z.v p (p + (-i)) rfl).hom b)) := by
  -- Route correction: first replace the visible proof witness, then normalize only the codomain
  -- spelling of the canonical double-negated component.
  calc
    (((z.v (- -p) (- -(p + (-i)))
          chainHomComplexProjAt_component_apply_normalized_visibleRelation).hom)
        (show (asCochainComplex R B).X (- -p) from by
          simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b)) =
      (((z.v (- -p) (- -(p + (-i)))
            (by
              simpa using
                (rfl : p + (-i) = p + (-i)))).hom)
          (show (asCochainComplex R B).X (- -p) from by
            simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b)) := by
      -- The source is fixed; only the proof witness for the visible degree equation changes here.
      exact chainHomComplexProjAtNormalizedVisibleCanonical_apply R z b
    _ =
      (show (asCochainComplex R M).X (- -(p + (-i))) from by
        simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using
          ((z.v p (p + (-i)) rfl).hom b)) := by
      -- The new bridge keeps the remaining normalization entirely inside the cochain carrier.
      exact chainHomComplexProjAtCanonicalVisibleCodomainCast_apply R z b

attribute [local simp] ChainComplex.cochainComplexEquivalence HomologicalComplex.XIsoOfEq in
/-- Helper for Definition 17.5.1: before applying the final output cast, the normalized visible
component already agrees with the public component in the cochain carrier. -/
private theorem chainHomComplexProjAtNormalizedVisible_applyCast
    (R : Type u) [CommRing R] {B M : ChainComplex (ModuleCat R) ℤ} {i p : ℤ}
    (z : (chainHomComplex R B M).X i) (b : B.X (-p)) :
    (((z.v (- -p) (- -(p + (-i)))
        chainHomComplexProjAt_component_apply_normalized_visibleRelation).hom)
      (cast
        (show (B.X (-p) : Type u) = ((asCochainComplex R B).X (- -p) : Type u) by
          simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
        b)) =
      (show (asCochainComplex R M).X (- -(p + (-i))) from by
        simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using
          ((z.v p (p + (-i)) rfl).hom b)) := by
  -- Route correction: the source cast and the codomain transport are now separated, so this proof
  -- only rewrites the source into the cochain carrier and invokes the dedicated target bridge.
  rw [chainHomComplexProjAtNormalizedSourceCast_apply R b]
  exact chainHomComplexProjAtNormalizedVisibleTargetCast_apply R z b

attribute [local simp] ChainComplex.cochainComplexEquivalence HomologicalComplex.XIsoOfEq in
/-- Helper for Definition 17.5.1: after collapsing the exact source and target casts, the
normalized visible component agrees with the public component formula. -/
private theorem chainHomComplexProjAtNormalizedVisible_apply
    (R : Type u) [CommRing R] {B M : ChainComplex (ModuleCat R) ℤ} {i p : ℤ}
    (z : (chainHomComplex R B M).X i) (b : B.X (-p)) :
    cast
      (show ↑((asCochainComplex R M).X (- -(p + (-i)))) = ↑(M.X (-(p + (-i)))) by
        simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
      (((z.v (- -p) (- -(p + (-i)))
          chainHomComplexProjAt_component_apply_normalized_visibleRelation).hom)
        (cast
          (show (B.X (-p) : Type u) = ((asCochainComplex R B).X (- -p) : Type u) by
            simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
          b)) =
      ((z.v p (p + (-i)) rfl).hom b) := by
  -- Apply the output-cast collapse only after the in-carrier visible component has already been
  -- normalized to the public `v`-component.
  calc
    cast
        (show ↑((asCochainComplex R M).X (- -(p + (-i)))) = ↑(M.X (-(p + (-i)))) by
          simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
        (((z.v (- -p) (- -(p + (-i)))
            chainHomComplexProjAt_component_apply_normalized_visibleRelation).hom)
          (cast
            (show (B.X (-p) : Type u) = ((asCochainComplex R B).X (- -p) : Type u) by
              simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
            b)) =
        (show M.X (-(p + (-i))) from by
          simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using
            (((z.v (- -p) (- -(p + (-i)))
                chainHomComplexProjAt_component_apply_normalized_visibleRelation).hom)
              (cast
                (show (B.X (-p) : Type u) = ((asCochainComplex R B).X (- -p) : Type u) by
                  simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
                b))) := by
      -- This is the exact codomain transport appearing in the normalized projection formula.
      simpa using
        chainHomComplexProjAtNormalizedOutputCast_apply R
          (((z.v (- -p) (- -(p + (-i)))
              chainHomComplexProjAt_component_apply_normalized_visibleRelation).hom)
            (cast
              (show (B.X (-p) : Type u) = ((asCochainComplex R B).X (- -p) : Type u) by
                simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
              b))
    _ = ((z.v p (p + (-i)) rfl).hom b) := by
      -- The new bridge keeps the comparison inside the cochain carrier until the final cast.
      rw [chainHomComplexProjAtNormalizedVisible_applyCast R z b]
      simp [asCochainComplex, ChainComplex.cochainComplexEquivalence]

attribute [local simp] ChainComplex.cochainComplexEquivalence HomologicalComplex.XIsoOfEq in
/-- Helper for Definition 17.5.1: evaluating `chainHomComplexProjAt` on an element recovers the
corresponding visible cochain component. -/
private theorem chainHomComplexProjAt_component_apply_normalized (R : Type u) [CommRing R]
    {B M : ChainComplex (ModuleCat R) ℤ} {i p : ℤ}
    (z : (chainHomComplex R B M).X i) (b : B.X (-p)) :
    (((chainHomComplexProjAt R B M i (-p) (-(p + (-i))) (chainHomComplexProjAt_relation rfl)).hom
          z).hom
      b) =
      ((z.v p (p + (-i)) rfl).hom b) := by
  -- Route correction: the visible-composite transport has now been isolated in
  -- `chainHomComplexProjAtVisibleComposite_apply_castBridge`, so the proof is now a pure rewrite
  -- chain through the exact normalized visible-component theorem.
  rw [chainHomComplexProjAt_hom_eq_visibleComposite]
  have hbridge :
      ((((B.XIsoOfEq (by simp)).hom ≫
            z.v (- -p) (- -(p + (-i)))
              chainHomComplexProjAt_component_apply_normalized_visibleRelation ≫
            (M.XIsoOfEq (by simp)).inv).hom) b) =
        cast
          (show ↑((asCochainComplex R M).X (- -(p + (-i)))) = ↑(M.X (-(p + (-i)))) by
            simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
          (((z.v (- -p) (- -(p + (-i)))
              chainHomComplexProjAt_component_apply_normalized_visibleRelation).hom)
            (cast
              (show (B.X (-p) : Type u) = ((asCochainComplex R B).X (- -p) : Type u) by
                simp [asCochainComplex, ChainComplex.cochainComplexEquivalence])
              b)) := by
    -- Rewrite the reindexing isomorphisms into the exact transport sandwich recorded by the bridge
    -- theorem, then reuse that theorem verbatim.
    simpa [HomologicalComplex.XIsoOfEq] using
      (chainHomComplexProjAtVisibleComposite_apply_castBridge R (B := B) (M := M) (i := i)
        (p := p) z b)
  exact hbridge.trans (chainHomComplexProjAtNormalizedVisible_apply R z b)

/-- Helper for Definition 17.5.1: evaluating `chainHomComplexProjAt` on an element recovers the
corresponding visible cochain component. -/
private theorem chainHomComplexProjAt_component_apply (R : Type u) [CommRing R]
    {B M : ChainComplex (ModuleCat R) ℤ} {i p q : ℤ}
    (z : (chainHomComplex R B M).X i) (hpq : p + (-i) = q) (b : B.X (-p)) :
    (((chainHomComplexProjAt R B M i (-p) (-q) (chainHomComplexProjAt_relation hpq)).hom z).hom
      b) =
      ((z.v p q hpq).hom b) := by
  -- Reduce to the normal form where the visible degree equation is definitional.
  subst q
  -- The normalized projection lemma removes the `eqToHom` transport.
  exact (chainHomComplexProjAt_component_apply_normalized R z b).trans
    (by simpa using cochain_v_apply_proofIrrel R z rfl rfl b)

/-- Helper for Definition 17.5.1: morphisms into `chainHomComplex R B M` are determined by their
visible `B.X r ⟶ M.X n` components. -/
private theorem chainHomComplex_hom_ext (R : Type u) [CommRing R]
    {X B M : ChainComplex (ModuleCat R) ℤ}
    {f g : X ⟶ chainHomComplex R B M}
    (h : ∀ (i r n : ℤ) (hir : i + r = n),
      f.f i ≫ chainHomComplexProjAt R B M i r n hir =
        g.f i ≫ chainHomComplexProjAt R B M i r n hir) :
    f = g := by
  -- Compare the underlying cochains degreewise through the visible projections.
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  ext x
  apply Cochain.ext
  intro p q hpq
  apply ModuleCat.hom_ext
  ext b
  let hir : i + (-p) = -q := chainHomComplexProjAt_relation hpq
  have hcomp :=
    congrArg
      (fun φ : X.X i ⟶ (B.X (-p) ⟶[ModuleCat R] M.X (-q)) ↦ (φ.hom x).hom b)
      (h i (-p) (-q) hir)
  -- The normalization bridge turns both projected values into the target `Cochain.v` component.
  exact
    (chainHomComplexProjAt_component_apply R (B := B) (M := M) (i := i) (p := p) (q := q)
      (z := f.f i x) hpq b).symm.trans
      (hcomp.trans
        (chainHomComplexProjAt_component_apply R (B := B) (M := M) (i := i) (p := p) (q := q)
          (z := g.f i x) hpq b))

/-- Helper for Definition 17.5.1: the explicit curried degreewise maps satisfy the chain-map
compatibility equation. -/
private theorem chainTensorHomAdjunctionToHom_comm (R : Type u) [CommRing R]
    (A B M : ChainComplex (ModuleCat R) ℤ) (h : tensorObj A B ⟶ M) :
    let f : ∀ i, A.X i ⟶ (chainHomComplex R B M).X i := fun i ↦
      ModuleCat.ofHom
        { toFun := fun a ↦
            Cochain.mk
              (fun p q hpq ↦ by
                let curried : A.X i ⟶ (B.X (-p) ⟶[ModuleCat R] M.X (-q)) :=
                  ModuleCat.monoidalClosedHomEquiv (B.X (-p)) (A.X i) (M.X (-q))
                    ((β_ (B.X (-p)) (A.X i)).hom ≫
                      ιTensorObj A B i (-p) (-q) (by
                        dsimp at hpq ⊢
                        lia) ≫
                      h.f (-q))
                exact ModuleCat.ofHom (curried.hom₂ a))
          map_add' := by
            intro a a'
            -- The curried map is linear in the `A.X i` input, so the resulting cochain is too.
            apply Cochain.ext
            intro p q hpq
            ext b
            let curried : A.X i ⟶ (B.X (-p) ⟶[ModuleCat R] M.X (-q)) :=
              ModuleCat.monoidalClosedHomEquiv (B.X (-p)) (A.X i) (M.X (-q))
                ((β_ (B.X (-p)) (A.X i)).hom ≫
                  ιTensorObj A B i (-p) (-q) (by
                    dsimp at hpq ⊢
                    lia) ≫
                  h.f (-q))
            change curried.hom₂ (a + a') b = (curried.hom₂ a + curried.hom₂ a') b
            exact congrArg (fun t ↦ t.hom b) (curried.hom.map_add a a')
          map_smul' := by
            intro r a
            -- The same pointwise argument handles scalar multiplication.
            apply Cochain.ext
            intro p q hpq
            ext b
            let curried : A.X i ⟶ (B.X (-p) ⟶[ModuleCat R] M.X (-q)) :=
              ModuleCat.monoidalClosedHomEquiv (B.X (-p)) (A.X i) (M.X (-q))
                ((β_ (B.X (-p)) (A.X i)).hom ≫
                  ιTensorObj A B i (-p) (-q) (by
                    dsimp at hpq ⊢
                    lia) ≫
                  h.f (-q))
            change curried.hom₂ (r • a) b = (r • curried.hom₂ a) b
            exact congrArg (fun t ↦ t.hom b) (curried.hom.map_smul r a) }
    ∀ i j, (hij : (ComplexShape.down ℤ).Rel i j) →
      f i ≫ (chainHomComplex R B M).d i j = A.d i j ≫ f j := by
  dsimp
  intro i j hij
  -- Route correction: the visible-component formula should drive this proof rather than
  -- unfolding the full reindexed Hom complex in the main definition body.
  -- TODO: postcompose with `chainHomComplexProjAt`, expand the projected differential via `δ_v`,
  -- and compare the two branches with the tensor differential identity for `h`.
  sorry

/-- Curry a morphism `tensorObj A B ⟶ M` degreewise into a morphism `A ⟶ chainHomComplex R B M`.
-/
private def chainTensorHomAdjunctionToHom (R : Type u) [CommRing R]
    (A B M : ChainComplex (ModuleCat R) ℤ) (h : tensorObj A B ⟶ M) :
    A ⟶ chainHomComplex R B M where
  f := fun i ↦
    ModuleCat.ofHom
      { toFun := fun a ↦
          Cochain.mk
            (fun p q hpq ↦ by
              let curried : A.X i ⟶ (B.X (-p) ⟶[ModuleCat R] M.X (-q)) :=
                ModuleCat.monoidalClosedHomEquiv (B.X (-p)) (A.X i) (M.X (-q))
                  ((β_ (B.X (-p)) (A.X i)).hom ≫
                    ιTensorObj A B i (-p) (-q) (by
                      dsimp at hpq ⊢
                      lia) ≫
                    h.f (-q))
              exact ModuleCat.ofHom (curried.hom₂ a))
        map_add' := by
          intro a a'
          -- The curried map is linear in the `A.X i` input, so the resulting cochain is too.
          apply Cochain.ext
          intro p q hpq
          ext b
          let curried : A.X i ⟶ (B.X (-p) ⟶[ModuleCat R] M.X (-q)) :=
            ModuleCat.monoidalClosedHomEquiv (B.X (-p)) (A.X i) (M.X (-q))
              ((β_ (B.X (-p)) (A.X i)).hom ≫
                ιTensorObj A B i (-p) (-q) (by
                  dsimp at hpq ⊢
                  lia) ≫
                h.f (-q))
          change curried.hom₂ (a + a') b = (curried.hom₂ a + curried.hom₂ a') b
          exact congrArg (fun t ↦ t.hom b) (curried.hom.map_add a a')
        map_smul' := by
          intro r a
          -- The same pointwise argument handles scalar multiplication.
          apply Cochain.ext
          intro p q hpq
          ext b
          let curried : A.X i ⟶ (B.X (-p) ⟶[ModuleCat R] M.X (-q)) :=
            ModuleCat.monoidalClosedHomEquiv (B.X (-p)) (A.X i) (M.X (-q))
              ((β_ (B.X (-p)) (A.X i)).hom ≫
                ιTensorObj A B i (-p) (-q) (by
                  dsimp at hpq ⊢
                  lia) ≫
                h.f (-q))
          change curried.hom₂ (r • a) b = (r • curried.hom₂ a) b
          exact congrArg (fun t ↦ t.hom b) (curried.hom.map_smul r a) }
  comm' := by
    intro i j hij
    -- Reuse the standalone compatibility theorem so the chain-map proof stays centralized.
    simpa using chainTensorHomAdjunctionToHom_comm R A B M h i j hij

/-- Helper for Definition 17.5.1: the explicit uncurried degreewise maps satisfy the chain-map
compatibility equation. -/
private theorem chainTensorHomAdjunctionInvHom_comm (R : Type u) [CommRing R]
    (A B M : ChainComplex (ModuleCat R) ℤ) (g : A ⟶ chainHomComplex R B M) :
    let f : ∀ n, (tensorObj A B).X n ⟶ M.X n := fun n ↦
      (mapBifunctorDesc
        (fun i r hir ↦
          let proj : (chainHomComplex R B M).X i ⟶ (B.X r ⟶[ModuleCat R] M.X n) :=
            chainHomComplexProjAt R B M i r n (by simpa using hir)
          let curried : A.X i ⟶ (B.X r ⟶[ModuleCat R] M.X n) :=
            g.f i ≫ proj
          (β_ (A.X i) (B.X r)).hom ≫
            (ModuleCat.monoidalClosedHomEquiv (B.X r) (A.X i) (M.X n)).symm curried) :
        (tensorObj A B).X n ⟶ M.X n)
    ∀ i j, (hij : (ComplexShape.down ℤ).Rel i j) →
      f i ≫ M.d i j = (tensorObj A B).d i j ≫ f j := by
  dsimp
  intro i j hij
  -- Route correction: prove the tensor differential identity summandwise instead of leaving the
  -- `mapBifunctorDesc` computation inline in the definition body.
  -- TODO: precompose with each `ιTensorObj`, rewrite `tensorObj` differentials with
  -- `mapBifunctor.d_eq`, `mapBifunctor.d₁_eq`, and `mapBifunctor.d₂_eq`, and identify the
  -- resulting branches using the visible-summand formula for the uncurry construction.
  sorry

/-- Uncurry a morphism `A ⟶ chainHomComplex R B M` degreewise into a morphism
`tensorObj A B ⟶ M`. -/
private def chainTensorHomAdjunctionInvHom (R : Type u) [CommRing R]
    (A B M : ChainComplex (ModuleCat R) ℤ) (g : A ⟶ chainHomComplex R B M) :
    tensorObj A B ⟶ M where
  f := fun n ↦
    (mapBifunctorDesc
      (fun i r hir ↦
        let proj : (chainHomComplex R B M).X i ⟶ (B.X r ⟶[ModuleCat R] M.X n) :=
          chainHomComplexProjAt R B M i r n (by simpa using hir)
        let curried : A.X i ⟶ (B.X r ⟶[ModuleCat R] M.X n) :=
          g.f i ≫ proj
        (β_ (A.X i) (B.X r)).hom ≫
          (ModuleCat.monoidalClosedHomEquiv (B.X r) (A.X i) (M.X n)).symm curried) :
      (tensorObj A B).X n ⟶ M.X n)
  comm' := by
    intro i j hij
    -- Reuse the standalone compatibility theorem so the summandwise differential proof is unique.
    simpa using chainTensorHomAdjunctionInvHom_comm R A B M g i j hij

/-- Helper for Definition 17.5.1: exposing an `ιMapBifunctor` summand of the uncurry
construction recovers the branch used to define it. -/
private theorem chainTensorHomAdjunctionInvHom_mapBifunctorSummand (R : Type u) [CommRing R]
    (A B M : ChainComplex (ModuleCat R) ℤ) (g : A ⟶ chainHomComplex R B M)
    (i r n : ℤ) (hir : i + r = n) :
    HomologicalComplex.ιMapBifunctor A B (MonoidalCategory.curriedTensor (ModuleCat R))
        (ComplexShape.down ℤ) i r n hir ≫
        (chainTensorHomAdjunctionInvHom R A B M g).f n =
      (β_ (A.X i) (B.X r)).hom ≫
        (ModuleCat.monoidalClosedHomEquiv (B.X r) (A.X i) (M.X n)).symm
          (g.f i ≫ chainHomComplexProjAt R B M i r n hir) := by
  -- Unfold the `mapBifunctorDesc` once and apply its canonical computation rule on the chosen
  -- `(i,r)` summand.
  simpa [chainTensorHomAdjunctionInvHom] using
    (HomologicalComplex.ι_mapBifunctorDesc
      (K₁ := A) (K₂ := B) (F := curriedTensor (ModuleCat R)) (c := ComplexShape.down ℤ)
      (j := n)
      (f := fun i r hir ↦
        let proj : (chainHomComplex R B M).X i ⟶ (B.X r ⟶[ModuleCat R] M.X n) :=
          chainHomComplexProjAt R B M i r n (by simpa using hir)
        let curried : A.X i ⟶ (B.X r ⟶[ModuleCat R] M.X n) :=
          g.f i ≫ proj
        (β_ (A.X i) (B.X r)).hom ≫
          (ModuleCat.monoidalClosedHomEquiv (B.X r) (A.X i) (M.X n)).symm curried)
      i r hir)

/-- Helper for Definition 17.5.1: taking the chosen tensor summand of the uncurry construction
recovers the branch used to define it. -/
theorem ιTensorObj_chainTensorHomAdjunctionInvHom_f (R : Type u) [CommRing R]
    (A B M : ChainComplex (ModuleCat R) ℤ) (g : A ⟶ chainHomComplex R B M)
    (i r n : ℤ) (hir : i + r = n) :
    ιTensorObj A B i r n hir ≫ (chainTensorHomAdjunctionInvHom R A B M g).f n =
      (β_ (A.X i) (B.X r)).hom ≫
        (ModuleCat.monoidalClosedHomEquiv (B.X r) (A.X i) (M.X n)).symm
          (g.f i ≫ chainHomComplexProjAt R B M i r n hir) := by
  -- Convert the internal `ιMapBifunctor` computation rule to the public `ιTensorObj` spelling.
  simpa [HomologicalComplex.ιTensorObj] using
    chainTensorHomAdjunctionInvHom_mapBifunctorSummand R A B M g i r n hir

/-- Helper for Definition 17.5.1: negating `hir : i + r = n` and then converting back through
`chainHomComplexProjAt_relation` yields the canonical double-negated proof of the same index
relation. -/
private theorem chainTensorHomAdjunctionToHom_projAt_doubleNegRelation
    {i r n : ℤ} (hir : i + r = n) :
    chainHomComplexProjAt_relation
        (by
          simpa [neg_add_rev, add_comm] using congrArg Neg.neg hir :
          (-r) + (-i) = -n) =
      (show i + - -r = - -n from by simpa using hir) := by
  -- The two witnesses prove the same proposition, so proof irrelevance identifies them.
  apply Subsingleton.elim

/-- Helper for Definition 17.5.1: the normalized public degree relation is exactly the double
negation of `hir`. -/
private theorem chainTensorHomAdjunctionToHom_projAt_doubleNegEq
    {i r n : ℤ} (hir : i + r = n) :
    i + - -r = - -n := by
  -- This keeps the normalized public `(r,n)` spelling available as a named arithmetic witness.
  simpa using hir

/-- Helper for Definition 17.5.1: the normalized public projection term used by the visible
component computation. -/
private abbrev chainTensorHomAdjunctionToHomNormalizedProj
    (R : Type u) [CommRing R] (B M : ChainComplex (ModuleCat R) ℤ)
    (i r n : ℤ) (hir : i + r = n) :
    (chainHomComplex R B M).X i ⟶ (B.X (- -r) ⟶[ModuleCat R] M.X (- -n)) :=
  chainHomComplexProjAt R B M i (- -r) (- -n)
    (chainTensorHomAdjunctionToHom_projAt_doubleNegEq (hir := hir))

/-- Helper for Definition 17.5.1: the normalized degreewise currying branch used by the visible
projection formula. -/
private abbrev chainTensorHomAdjunctionToHomNormalizedCurried
    (R : Type u) [CommRing R] (A B M : ChainComplex (ModuleCat R) ℤ)
    (h : tensorObj A B ⟶ M) (i r n : ℤ) (hir : i + r = n) :
    A.X i ⟶ (B.X (- -r) ⟶[ModuleCat R] M.X (- -n)) :=
  ModuleCat.monoidalClosedHomEquiv (B.X (- -r)) (A.X i) (M.X (- -n))
    ((β_ (B.X (- -r)) (A.X i)).hom ≫
      ιTensorObj A B i (- -r) (- -n)
        (chainTensorHomAdjunctionToHom_projAt_doubleNegEq (hir := hir)) ≫
      h.f (- -n))

/-- Helper for Definition 17.5.1: the explicit cast from `B.X r` to `B.X (- -r)` is exactly the
retagged source element used in the normalized projection formulas. -/
private theorem chainTensorHomAdjunction_doubleNegSource_cast
    (R : Type u) [CommRing R] {B : ChainComplex (ModuleCat R) ℤ} {r : ℤ}
    (b : B.X r) :
    cast (by simp : (B.X r : Type u) = B.X (- -r)) b =
      (show B.X (- -r) from by simpa using b) := by
  -- Both terms are the same explicit double-negation retagging of `b`.
  rfl

/-- Helper for Definition 17.5.1: the final codomain cast from `M.X (- -n)` to `M.X n` is exactly
the visible double-negation retagging on the target element. -/
private theorem chainTensorHomAdjunctionDoubleNegTargetCast
    (R : Type u) [CommRing R] {M : ChainComplex (ModuleCat R) ℤ} {n : ℤ}
    (m : M.X (- -n)) :
    cast (by simp : (M.X (- -n) : Type u) = M.X n) m =
      (show M.X n from by simpa using m) := by
  -- The public target element is obtained by the same explicit double-negation retagging.
  rfl

/-- Helper for Definition 17.5.1: evaluating the public `(r,n)` projection is the same as
evaluating the normalized `(- -r,- -n)` projection on the correspondingly retyped source element.
-/
private theorem chainHomComplexProjAt_publicNormalized_apply
    (R : Type u) [CommRing R] {B M : ChainComplex (ModuleCat R) ℤ}
    {i r n : ℤ} (hir : i + r = n) (z : (chainHomComplex R B M).X i) (b : B.X r) :
    (((chainHomComplexProjAt R B M i r n hir).hom z).hom b) =
      (show M.X n from by
        simpa using
          (((chainTensorHomAdjunctionToHomNormalizedProj R B M i r n hir).hom z).hom
            (show B.X (- -r) from by simpa using b))) := by
  let hneg : (-r) + (-i) = -n := by
    simpa [neg_add_rev, add_comm] using congrArg Neg.neg hir
  let bdd : B.X (- -r) := show B.X (- -r) from by simpa using b
  let mPublic : M.X n := show M.X n from by
    simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence, bdd] using
      ((z.v (-r) (-n) hneg).hom bdd)
  have hpublic :
      (((chainHomComplexProjAt R B M i r n hir).hom z).hom b) =
        cast (by simp : (M.X (- -n) : Type u) = M.X n)
          (((z.v (-r) (-n) hneg).hom)
            (cast (by simp : (B.X r : Type u) = B.X (- -r)) b)) := by
    -- Expose the public projection as the exact source-and-target transport sandwich around the
    -- visible `(-r,-n)` component.
    rw [chainHomComplexProjAt_hom_eq_visibleComposite]
    simpa [HomologicalComplex.XIsoOfEq] using
      (moduleCatEqToHomSandwich_apply R
        (hX := show B.X r = B.X (- -r) by simp)
        (f := z.v (-r) (-n) hneg)
        (hY := show M.X (- -n) = M.X n by simp)
        b)
  have hpublicNormalized :
      (((chainHomComplexProjAt R B M i r n hir).hom z).hom b) = mPublic := by
    change (((chainHomComplexProjAt R B M i r n hir).hom z).hom b) = mPublic
    -- Collapse the source retagging first, then use the dedicated normalized output-cast theorem
    -- on the visible target component.
    calc
      (((chainHomComplexProjAt R B M i r n hir).hom z).hom b) =
        cast
          (by
            simpa [hneg, asCochainComplex, ChainComplex.cochainComplexEquivalence] :
              (((asCochainComplex R M).X (-n)) : Type u) = (M.X n : Type u))
          (((z.v (-r) (-n) hneg).hom)
            (cast (by simp : (B.X r : Type u) = (B.X (- -r) : Type u)) b)) := hpublic
      _ =
        cast
          (by
            simpa [hneg, asCochainComplex, ChainComplex.cochainComplexEquivalence] :
              (((asCochainComplex R M).X (-n)) : Type u) = (M.X n : Type u))
          (((z.v (-r) (-n) hneg).hom) bdd) := by
        have hsrc :
            cast (by simp : (B.X r : Type u) = (B.X (- -r) : Type u)) b = bdd :=
          chainTensorHomAdjunction_doubleNegSource_cast (R := R) (B := B) (r := r) b
        cases hsrc
        rfl
      _ = mPublic := by
        rfl
  have hnormalized :
      (((chainTensorHomAdjunctionToHomNormalizedProj R B M i r n hir).hom z).hom bdd) =
        ((z.v (-r) (-n) hneg).hom bdd) := by
    -- The normalized projection exposes the same visible component after replacing the witness by
    -- the named double-negated public relation.
    simpa [chainTensorHomAdjunctionToHomNormalizedProj,
        chainTensorHomAdjunctionToHom_projAt_doubleNegRelation (hir := hir)] using
      (chainHomComplexProjAt_component_apply R (B := B) (M := M) (i := i) (p := -r) (q := -n)
        (z := z) hneg bdd)
  have hnormalizedPublic :
      (show M.X n from by
        simpa using
          (((chainTensorHomAdjunctionToHomNormalizedProj R B M i r n hir).hom z).hom bdd)) =
        mPublic := by
    -- Transport the normalized comparison to the public target surface by the single double-neg
    -- retagging packaged above.
    change cast (by simp : (M.X (- -n) : Type u) = M.X n)
        ((((chainTensorHomAdjunctionToHomNormalizedProj R B M i r n hir).hom z).hom) bdd) =
      cast (by simp : (M.X (- -n) : Type u) = M.X n) (((z.v (-r) (-n) hneg).hom) bdd)
    exact congrArg
      (fun x : M.X (- -n) => cast (by simp : (M.X (- -n) : Type u) = M.X n) x)
      hnormalized
  simpa [mPublic] using hpublicNormalized.trans hnormalizedPublic.symm

/-- Helper for Definition 17.5.1: evaluating the visible `(-r,-n)` branch of the curried chain
map gives the normalized module-level currying map. -/
private theorem chainTensorHomAdjunctionToHomVisibleBranchUnfold_apply
    (R : Type u) [CommRing R] (A B M : ChainComplex (ModuleCat R) ℤ)
    (h : tensorObj A B ⟶ M) (i r n : ℤ) (hir : i + r = n)
    (a : A.X i) (b : B.X (- -r)) :
    let hneg : (-r) + (-i) = -n := by
      simpa [neg_add_rev, add_comm] using congrArg Neg.neg hir
    (show M.X (- -n) from by
      simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using
        (((((chainTensorHomAdjunctionToHom R A B M h).f i).hom a).v (-r) (-n) hneg).hom
          (show (asCochainComplex R B).X (-r) from by
            simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b))) =
      ((ModuleCat.monoidalClosedHomEquiv (B.X (- -r)) (A.X i) (M.X (- -n))
          ((β_ (B.X (- -r)) (A.X i)).hom ≫
            ιTensorObj A B i (- -r) (- -n) (by
              lia) ≫
            h.f (- -n))).hom₂ a) b := by
  -- Unfold the visible branch exactly once; the only remaining mismatch is the autogenerated
  -- `ιTensorObj` witness, which the next lemma normalizes by proof irrelevance.
  -- Evaluate the exposed `Cochain.mk` branch and let the reindexing casts collapse
  -- simultaneously, so the visible branch reduces to the generated currying term.
  simp [chainTensorHomAdjunctionToHom, asCochainComplex,
    ChainComplex.cochainComplexEquivalence, Cochain.v]
  -- After the branch is exposed, only the beta-reduction of the chosen triplet remains.
  change (((ModuleCat.ofHom
      ((ModuleCat.monoidalClosedHomEquiv (B.X (- -r)) (A.X i) (M.X (- -n))
        ((β_ (B.X (- -r)) (A.X i)).hom ≫
          ιTensorObj A B i (- -r) (- -n) (by lia) ≫
          h.f (- -n))).hom₂ a)).hom) b) =
    ((ModuleCat.monoidalClosedHomEquiv (B.X (- -r)) (A.X i) (M.X (- -n))
        ((β_ (B.X (- -r)) (A.X i)).hom ≫
          ιTensorObj A B i (- -r) (- -n) (by lia) ≫
          h.f (- -n))).hom₂ a) b
  rfl

/-- Helper for Definition 17.5.1: evaluating the visible `(-r,-n)` branch of the curried chain
map gives the normalized module-level currying map. -/
private theorem chainTensorHomAdjunctionToHomNormalizedBranch_apply
    (R : Type u) [CommRing R] (A B M : ChainComplex (ModuleCat R) ℤ)
    (h : tensorObj A B ⟶ M) (i r n : ℤ) (hir : i + r = n)
    (a : A.X i) (b : B.X (- -r)) :
    let hneg : (-r) + (-i) = -n := by
      simpa [neg_add_rev, add_comm] using congrArg Neg.neg hir
    (show M.X (- -n) from by
      simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using
        (((((chainTensorHomAdjunctionToHom R A B M h).f i).hom a).v (-r) (-n) hneg).hom
          (show (asCochainComplex R B).X (-r) from by
            simpa [asCochainComplex, ChainComplex.cochainComplexEquivalence] using b))) =
      ((chainTensorHomAdjunctionToHomNormalizedCurried R A B M h i r n hir).hom₂ a) b := by
  dsimp
  have hproof :
      (by
        lia : i + - -r = - -n) =
        chainTensorHomAdjunctionToHom_projAt_doubleNegEq (hir := hir) := by
    -- The branch witness generated from `hneg` proves the same proposition as the named
    -- double-negation witness, so proof irrelevance identifies the two.
    apply Subsingleton.elim
  -- Route correction: use the one-step visible-branch unfold helper, then normalize the
  -- autogenerated `ιTensorObj` witness to the named public double-negation witness.
  simpa [chainTensorHomAdjunctionToHomNormalizedCurried, hproof] using
    chainTensorHomAdjunctionToHomVisibleBranchUnfold_apply R A B M h i r n hir a b

/-- Helper for Definition 17.5.1: the normalized `(- -r,- -n)` projection of the curried chain
map is exactly the normalized currying branch. -/
private theorem chainTensorHomAdjunctionToHomNormalizedProj_apply
    (R : Type u) [CommRing R] (A B M : ChainComplex (ModuleCat R) ℤ)
    (h : tensorObj A B ⟶ M) (i r n : ℤ) (hir : i + r = n)
    (a : A.X i) (b : B.X (- -r)) :
    (((chainTensorHomAdjunctionToHomNormalizedProj R B M i r n hir).hom
        (((chainTensorHomAdjunctionToHom R A B M h).f i).hom a)).hom b) =
      ((chainTensorHomAdjunctionToHomNormalizedCurried R A B M h i r n hir).hom₂ a) b := by
  let z : (chainHomComplex R B M).X i := ((chainTensorHomAdjunctionToHom R A B M h).f i).hom a
  let hneg : (-r) + (-i) = -n := by
    simpa [neg_add_rev, add_comm] using congrArg Neg.neg hir
  have hnormalizedToVisible :
      (((chainTensorHomAdjunctionToHomNormalizedProj R B M i r n hir).hom z).hom b) =
        (show M.X (- -n) from by
          simpa [z, asCochainComplex, ChainComplex.cochainComplexEquivalence] using
            ((z.v (-r) (-n) hneg).hom b)) := by
    -- Expose the normalized projection as the visible `(-r,-n)` branch.
    simpa [z, hneg, chainTensorHomAdjunctionToHomNormalizedProj,
      chainTensorHomAdjunctionToHom_projAt_doubleNegRelation (hir := hir)] using
      (chainHomComplexProjAt_component_apply R (B := B) (M := M) (i := i) (p := -r) (q := -n)
        (z := z) hneg b)
  have hvisibleToCurried :
      (show M.X (- -n) from by
        simpa [z, asCochainComplex, ChainComplex.cochainComplexEquivalence] using
          ((z.v (-r) (-n) hneg).hom b)) =
        ((chainTensorHomAdjunctionToHomNormalizedCurried R A B M h i r n hir).hom₂ a) b := by
    -- Replace that visible branch by the normalized currying branch.
    simpa [z, hneg, asCochainComplex, ChainComplex.cochainComplexEquivalence] using
      (chainTensorHomAdjunctionToHomNormalizedBranch_apply R A B M h i r n hir a b)
  exact hnormalizedToVisible.trans hvisibleToCurried

/-- Helper for Definition 17.5.1: the normalized double-negated currying branch agrees with the
public `(r,n)` currying branch after retagging the source and target degrees back to the public
surface. -/
private theorem chainTensorHomAdjunctionNormalizedCurriedPublic_apply
    (R : Type u) [CommRing R] (A B M : ChainComplex (ModuleCat R) ℤ)
    (h : tensorObj A B ⟶ M) (i r n : ℤ) (hir : i + r = n)
    (a : A.X i) (b : B.X r) :
    (show M.X n from by
      simpa using
        ((chainTensorHomAdjunctionToHomNormalizedCurried R A B M h i r n hir).hom₂ a)
          (show B.X (- -r) from by simpa using b)) =
      ((ModuleCat.monoidalClosedHomEquiv (B.X r) (A.X i) (M.X n)
          ((β_ (B.X r) (A.X i)).hom ≫ ιTensorObj A B i r n hir ≫ h.f n)).hom₂ a) b := by
  -- TODO: evaluate both sides with `monoidalClosedHomEquiv_hom₂_apply`, rewrite the normalized
  -- double-negated tensor summand to the public `(i,r)` summand, and then transport the resulting
  -- source element through `h.f` from degree `- -(i + r)` to degree `i + r`.
  sorry

/-- Helper for Definition 17.5.1: projecting the curried chain map recovers the usual
module-level currying branch. -/
private theorem chainTensorHomAdjunctionToHom_projAt (R : Type u) [CommRing R]
    (A B M : ChainComplex (ModuleCat R) ℤ) (h : tensorObj A B ⟶ M)
    (i r n : ℤ) (hir : i + r = n) :
    (chainTensorHomAdjunctionToHom R A B M h).f i ≫ chainHomComplexProjAt R B M i r n hir =
      ModuleCat.monoidalClosedHomEquiv (B.X r) (A.X i) (M.X n)
        ((β_ (B.X r) (A.X i)).hom ≫ ιTensorObj A B i r n hir ≫ h.f n) := by
  -- Compare both sides on `a : A.X i` and `b : B.X r`, then expose the visible component of the
  -- curried cochain using `chainHomComplexProjAt_component_apply`.
  apply ModuleCat.hom_ext
  ext a
  apply ModuleCat.hom_ext
  ext b
  -- Route correction: the public-to-normalized projection bridge is now established by
  -- `chainHomComplexProjAt_publicNormalized_apply`, so the remaining work is to identify the
  -- normalized visible branch with the normalized currying morphism and then erase the double
  -- negations in the curried formula.
  let bdd : B.X (- -r) := show B.X (- -r) from by simpa using b
  have hpublic :
      ((((chainTensorHomAdjunctionToHom R A B M h).f i ≫ chainHomComplexProjAt R B M i r n hir).hom
          a).hom
        b) =
        (show M.X n from by
          simpa using
            (((chainTensorHomAdjunctionToHomNormalizedProj R B M i r n hir).hom
                (((chainTensorHomAdjunctionToHom R A B M h).f i).hom a)).hom bdd)) := by
    -- Rewrite the public `(r,n)` projection to the normalized `(- -r,- -n)` projection.
    simpa using
      (chainHomComplexProjAt_publicNormalized_apply R (B := B) (M := M) (hir := hir)
        (((chainTensorHomAdjunctionToHom R A B M h).f i).hom a) b)
  have hnormalized :
      (((chainTensorHomAdjunctionToHomNormalizedProj R B M i r n hir).hom
          (((chainTensorHomAdjunctionToHom R A B M h).f i).hom a)).hom bdd) =
        ((chainTensorHomAdjunctionToHomNormalizedCurried R A B M h i r n hir).hom₂ a) bdd :=
    chainTensorHomAdjunctionToHomNormalizedProj_apply R A B M h i r n hir a bdd
  have hnormalizedPublic :
      (show M.X n from by
        simpa using
          (((chainTensorHomAdjunctionToHomNormalizedProj R B M i r n hir).hom
              (((chainTensorHomAdjunctionToHom R A B M h).f i).hom a)).hom bdd)) =
        (show M.X n from by
          simpa using
            ((chainTensorHomAdjunctionToHomNormalizedCurried R A B M h i r n hir).hom₂ a) bdd) :=
    congrArg (fun x : M.X (- -n) => (show M.X n from by simpa using x)) hnormalized
  have hcurried :
      (show M.X n from by
        simpa using
          ((chainTensorHomAdjunctionToHomNormalizedCurried R A B M h i r n hir).hom₂ a) bdd) =
        ((ModuleCat.monoidalClosedHomEquiv (B.X r) (A.X i) (M.X n)
            ((β_ (B.X r) (A.X i)).hom ≫ ιTensorObj A B i r n hir ≫ h.f n)).hom₂ a) b :=
    chainTensorHomAdjunctionNormalizedCurriedPublic_apply R A B M h i r n hir a b
  -- The public projection now factors through the normalized projection and the single public
  -- currying adapter above, so the remaining comparison is a short transitive chain.
  exact hpublic.trans (hnormalizedPublic.trans hcurried)

/-- Definition 17.5.1. For chain complexes `A`, `B`, and `M` of `R`-modules, the tensor-Hom
adjunction identifies morphisms `tensorObj A B ⟶ M` with morphisms
`A ⟶ chainHomComplex R B M`. The degree signs are the standard chain-level signs encoded in the
reindexed cochain mapping complex underlying `chainHomComplex`. -/
noncomputable def chainTensorHomAdjunction (R : Type u) [CommRing R]
    (A B M : ChainComplex (ModuleCat R) ℤ) :
    (tensorObj A B ⟶ M) ≃ (A ⟶ chainHomComplex R B M) where
  toFun := chainTensorHomAdjunctionToHom R A B M
  invFun := chainTensorHomAdjunctionInvHom R A B M
  left_inv := by
    intro h
    -- Compare on each tensor summand; there the inverse construction exposes the chosen branch,
    -- and the forward projection formula turns that branch back into the original map.
    -- TODO: after `chainTensorHomAdjunctionToHom_projAt` is available, use
    -- `HomologicalComplex.hom_ext` and `mapBifunctor.hom_ext`, rewrite the chosen summand with
    -- `ιTensorObj_chainTensorHomAdjunctionInvHom_f`, normalize `hir : π (...) = n` to
    -- `hir' : i + r = n`, and finish by `symm_apply_apply` after the two braidings cancel.
    sorry
  right_inv := by
    intro g
    -- Compare the two morphisms into `chainHomComplex` on every visible component.
    -- TODO: after `chainTensorHomAdjunctionToHom_projAt` is available, use
    -- `chainHomComplex_hom_ext`, rewrite the projected branch with
    -- `ιTensorObj_chainTensorHomAdjunctionInvHom_f`, and finish by `apply_symm_apply` once the
    -- braidings reduce to the identity.
    sorry

/-- The forward direction of `chainTensorHomAdjunction` is characterized on the
`B.X r ⟶ M.X n` component by the usual tensor-Hom currying map. -/
theorem chainTensorHomAdjunction_apply (R : Type u) [CommRing R]
    (A B M : ChainComplex (ModuleCat R) ℤ) (h : tensorObj A B ⟶ M)
    (i r n : ℤ) (hir : i + r = n) :
    (chainTensorHomAdjunction R A B M h).f i ≫ chainHomComplexProjAt R B M i r n hir =
      ModuleCat.monoidalClosedHomEquiv (B.X r) (A.X i) (M.X n)
        ((β_ (B.X r) (A.X i)).hom ≫ ιTensorObj A B i r n hir ≫ h.f n) :=
  by
    -- The public formula is exactly the private visible-component computation rule.
    simpa [chainTensorHomAdjunction] using
      chainTensorHomAdjunctionToHom_projAt R A B M h i r n hir

/-- In degree `i`, `chainHomComplex R B M` is the degree `-i` term of the reindexed cochain
mapping complex. -/
theorem chainHomComplex_X (R : Type u) [CommRing R]
    (B M : ChainComplex (ModuleCat R) ℤ) (i : ℤ) :
    (chainHomComplex R B M).X i =
      ModuleCat.of R
        (Cochain
          ((ChainComplex.cochainComplexEquivalence (ModuleCat R)).functor.obj B)
          ((ChainComplex.cochainComplexEquivalence (ModuleCat R)).functor.obj M) (-i)) :=
  rfl

/-- The differential on `chainHomComplex R B M` is the standard signed differential induced from
the cochain mapping complex after the `n ↦ -n` reindexing. -/
theorem chainHomComplex_d (R : Type u) [CommRing R]
    (B M : ChainComplex (ModuleCat R) ℤ) (i j : ℤ) :
    (chainHomComplex R B M).d i j =
      ModuleCat.ofHom
        (δ_hom R
          ((ChainComplex.cochainComplexEquivalence (ModuleCat R)).functor.obj B)
          ((ChainComplex.cochainComplexEquivalence (ModuleCat R)).functor.obj M) (-i) (-j)) :=
  rfl
