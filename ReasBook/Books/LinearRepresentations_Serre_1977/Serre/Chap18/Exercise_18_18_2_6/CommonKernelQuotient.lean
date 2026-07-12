import LinearRepresentations_Serre_1977.Chap09.Exercise_9_9_1_3.ExteriorDeterminants
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_1_2

noncomputable section

universe v w

namespace Representation

section EquivalenceCriterion

variable {k : Type} [Field k]
variable {G : Type v} [Monoid G]
variable {V W : Type*}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Helper for Exercise 18-18.2-6: equality of the determinant polynomials
`det (1 + ρ(s) T)` forces equality of the ordinary characters. -/
lemma character_eq_of_det_one_add_polynomial_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hdet : ∀ s : G, (-ρ s).charpoly.reverse = (-ρ' s).charpoly.reverse) :
    ρ.character = ρ'.character := by
  ext s
  -- Read the coefficient of `T` on each side through the Chapter `9` determinant/exterior bridge.
  have hρcoeff : ((-ρ s).charpoly.reverse : Polynomial k).coeff 1 = ρ.character s := by
    have hone :
        LinearMap.trace k ↥(⋀[k]^1 V) (exteriorPower.map 1 (ρ s)) =
          LinearMap.trace k V (ρ s) := by
      let e := exteriorPower.oneEquiv k V
      calc
        LinearMap.trace k ↥(⋀[k]^1 V) (exteriorPower.map 1 (ρ s)) =
            LinearMap.trace k V (e.conj (exteriorPower.map 1 (ρ s))) := by
              symm
              exact LinearMap.trace_conj' (exteriorPower.map 1 (ρ s)) e
        _ = LinearMap.trace k V (ρ s) := by
              congr 1
              ext x
              have hnat :=
                LinearMap.congr_fun
                  (exteriorPower.oneEquiv_naturality (R := k) (M := V) (N := V) (ρ s))
                  (e.symm x)
              simpa [e] using hnat
    calc
      ((-ρ s).charpoly.reverse : Polynomial k).coeff 1 =
          LinearMap.trace k (⋀[k]^1 V) (exteriorPower.map 1 (ρ s)) := by
            exact (trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ s) 1).symm
      _ = ρ.character s := by
            simpa [Representation.character] using hone
  have hρ'coeff : ((-ρ' s).charpoly.reverse : Polynomial k).coeff 1 = ρ'.character s := by
    have hone :
        LinearMap.trace k ↥(⋀[k]^1 W) (exteriorPower.map 1 (ρ' s)) =
          LinearMap.trace k W (ρ' s) := by
      let e := exteriorPower.oneEquiv k W
      calc
        LinearMap.trace k ↥(⋀[k]^1 W) (exteriorPower.map 1 (ρ' s)) =
            LinearMap.trace k W (e.conj (exteriorPower.map 1 (ρ' s))) := by
              symm
              exact LinearMap.trace_conj' (exteriorPower.map 1 (ρ' s)) e
        _ = LinearMap.trace k W (ρ' s) := by
              congr 1
              ext x
              have hnat :=
                LinearMap.congr_fun
                  (exteriorPower.oneEquiv_naturality (R := k) (M := W) (N := W) (ρ' s))
                  (e.symm x)
              simpa [e] using hnat
    calc
      ((-ρ' s).charpoly.reverse : Polynomial k).coeff 1 =
          LinearMap.trace k (⋀[k]^1 W) (exteriorPower.map 1 (ρ' s)) := by
            exact (trace_exteriorPower_map_eq_coeff_neg_charpoly_reverse (A := ρ' s) 1).symm
      _ = ρ'.character s := by
            simpa [Representation.character] using hone
  rw [← hρcoeff, ← hρ'coeff]
  exact congrArg (fun p : Polynomial k ↦ p.coeff 1) (hdet s)

/-- Helper for Exercise 18-18.2-6: character equality extends to trace equality on all elements
of the monoid algebra. -/
lemma trace_eq_asAlgebraHom_of_character_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hchar : ρ.character = ρ'.character) (a : MonoidAlgebra k G) :
    LinearMap.trace k V (ρ.asAlgebraHom a) = LinearMap.trace k W (ρ'.asAlgebraHom a) := by
  -- Compare traces first on the monoid generators, then extend across the additive and scalar
  -- structure of the monoid algebra.
  refine
    MonoidAlgebra.induction_on
      (p := fun a : MonoidAlgebra k G ↦
        LinearMap.trace k V (ρ.asAlgebraHom a) = LinearMap.trace k W (ρ'.asAlgebraHom a))
      a ?_ ?_ ?_
  · intro g
    simpa [Representation.character, Representation.asAlgebraHom_of] using congrFun hchar g
  · intro a b ha hb
    simp [ha, hb]
  · intro r a ha
    simp [ha]

/-- Helper for Exercise 18-18.2-6: the kernel of the product algebra action is contained in the
kernel of the left factor. -/
lemma prod_asAlgebraHom_ker_le_left
    {ρ : Representation k G V} {ρ' : Representation k G W} :
    RingHom.ker (ρ.asAlgebraHom.prod ρ'.asAlgebraHom) ≤ RingHom.ker ρ.asAlgebraHom := by
  -- Project the vanishing product action to its left coordinate.
  intro a ha
  exact congrArg Prod.fst ha

/-- Helper for Exercise 18-18.2-6: the kernel of the product algebra action is contained in the
kernel of the right factor. -/
lemma prod_asAlgebraHom_ker_le_right
    {ρ : Representation k G V} {ρ' : Representation k G W} :
    RingHom.ker (ρ.asAlgebraHom.prod ρ'.asAlgebraHom) ≤ RingHom.ker ρ'.asAlgebraHom := by
  -- Project the vanishing product action to its right coordinate.
  intro a ha
  exact congrArg Prod.snd ha

/-- Helper for Exercise 18-18.2-6: the common kernel ideal of two representations is the kernel
of their product action on the product of endomorphism algebras. -/
abbrev commonKernelIdeal
    (ρ : Representation k G V) (ρ' : Representation k G W) :
    Ideal (MonoidAlgebra k G) :=
  RingHom.ker (ρ.asAlgebraHom.prod ρ'.asAlgebraHom)

/-- Helper for Exercise 18-18.2-6: the common kernel quotient algebra through which both
representations factor. -/
abbrev commonKernelQuotient
    (ρ : Representation k G V) (ρ' : Representation k G W) :=
  MonoidAlgebra k G ⧸ commonKernelIdeal (k := k) (G := G) ρ ρ'

/-- Helper for Exercise 18-18.2-6: the quotient projection onto the common kernel quotient. -/
noncomputable def commonKernelProjection
    (ρ : Representation k G V) (ρ' : Representation k G W) :
    MonoidAlgebra k G →ₐ[k] commonKernelQuotient (k := k) (G := G) ρ ρ' :=
  Ideal.Quotient.mkₐ k (commonKernelIdeal (k := k) (G := G) ρ ρ')

/-- Helper for Exercise 18-18.2-6: the left representation action descends to the common
kernel quotient. -/
noncomputable def commonKernelLeftAction
    (ρ : Representation k G V) (ρ' : Representation k G W) :
    commonKernelQuotient (k := k) (G := G) ρ ρ' →ₐ[k] Module.End k V :=
  Ideal.Quotient.liftₐ (commonKernelIdeal (k := k) (G := G) ρ ρ') ρ.asAlgebraHom
    (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))

/-- Helper for Exercise 18-18.2-6: the right representation action descends to the common
kernel quotient. -/
noncomputable def commonKernelRightAction
    (ρ : Representation k G V) (ρ' : Representation k G W) :
    commonKernelQuotient (k := k) (G := G) ρ ρ' →ₐ[k] Module.End k W :=
  Ideal.Quotient.liftₐ (commonKernelIdeal (k := k) (G := G) ρ ρ') ρ'.asAlgebraHom
    (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))

/-- Helper for Exercise 18-18.2-6: the left descended action precomposed with the quotient
projection is the original monoid-algebra action. -/
lemma commonKernelLeftAction_comp_projection
    {ρ : Representation k G V} {ρ' : Representation k G W} :
    (commonKernelLeftAction (k := k) (G := G) ρ ρ').comp
        (commonKernelProjection (k := k) (G := G) ρ ρ') =
      ρ.asAlgebraHom := by
  -- The named quotient action is exactly the quotient lift of the original left action.
  simpa [commonKernelLeftAction, commonKernelProjection, commonKernelIdeal,
    commonKernelQuotient] using
      Ideal.Quotient.liftₐ_comp
        (commonKernelIdeal (k := k) (G := G) ρ ρ') ρ.asAlgebraHom
        (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))

/-- Helper for Exercise 18-18.2-6: the right descended action precomposed with the quotient
projection is the original monoid-algebra action. -/
lemma commonKernelRightAction_comp_projection
    {ρ : Representation k G V} {ρ' : Representation k G W} :
    (commonKernelRightAction (k := k) (G := G) ρ ρ').comp
        (commonKernelProjection (k := k) (G := G) ρ ρ') =
      ρ'.asAlgebraHom := by
  -- The right action has the same quotient-lift computation.
  simpa [commonKernelRightAction, commonKernelProjection, commonKernelIdeal,
    commonKernelQuotient] using
      Ideal.Quotient.liftₐ_comp
        (commonKernelIdeal (k := k) (G := G) ρ ρ') ρ'.asAlgebraHom
        (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))

/-- Helper for Exercise 18-18.2-6: character equality descends to trace equality on the common
kernel quotient algebra. -/
lemma trace_eq_on_common_kernel_quotient_of_character_eq
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hchar : ρ.character = ρ'.character) :
    let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
    let A := MonoidAlgebra k G ⧸ I
    let φV : A →ₐ[k] Module.End k V :=
      Ideal.Quotient.liftₐ I ρ.asAlgebraHom
        (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
    let φW : A →ₐ[k] Module.End k W :=
      Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
        (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
    ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) := by
  let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
    ρ.asAlgebraHom.prod ρ'.asAlgebraHom
  let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
  letI : I.IsTwoSided := by
    change (RingHom.ker ψ).IsTwoSided
    infer_instance
  let A := MonoidAlgebra k G ⧸ I
  let φV : A →ₐ[k] Module.End k V :=
    Ideal.Quotient.liftₐ I ρ.asAlgebraHom
      (prod_asAlgebraHom_ker_le_left (ρ := ρ) (ρ' := ρ'))
  let φW : A →ₐ[k] Module.End k W :=
    Ideal.Quotient.liftₐ I ρ'.asAlgebraHom
      (prod_asAlgebraHom_ker_le_right (ρ := ρ) (ρ' := ρ'))
  have htrace : ∀ a : A, LinearMap.trace k V (φV a) = LinearMap.trace k W (φW a) := by
    intro a
    -- Lift a quotient element back to the monoid algebra, where the original trace identity
    -- applies.
    rcases Ideal.Quotient.mkₐ_surjective k I a with ⟨b, hb⟩
    rw [← hb]
    simpa [φV, φW] using
      trace_eq_asAlgebraHom_of_character_eq (ρ := ρ) (ρ' := ρ') hchar b
  simpa [ψ, I, A, φV, φW] using htrace

/-- Helper for Exercise 18-18.2-6: the common kernel quotient algebra is finite-dimensional over
`k`. -/
lemma common_kernel_quotient_finite
    {ρ : Representation k G V} {ρ' : Representation k G W} :
    let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
    let A := MonoidAlgebra k G ⧸ I
    Module.Finite k A := by
  let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
    ρ.asAlgebraHom.prod ρ'.asAlgebraHom
  let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
  let A := MonoidAlgebra k G ⧸ I
  have hfiniteRange : Module.Finite k ψ.range := by
    infer_instance
  let e : A ≃ₐ[k] ψ.range := by
    simpa [A, I] using Ideal.quotientKerEquivRange (R := k) ψ
  -- Transport finiteness across the canonical quotient-range equivalence.
  have hfinite : Module.Finite k A := Module.Finite.equiv e.toLinearEquiv.symm
  simpa [ψ, I, A] using hfinite

/-- Helper for Exercise 18-18.2-6: the named common kernel quotient is finite-dimensional over
`k`. -/
lemma commonKernelQuotient_finite
    {ρ : Representation k G V} {ρ' : Representation k G W} :
    Module.Finite k (commonKernelQuotient (k := k) (G := G) ρ ρ') := by
  -- Rewrite the stable API spelling to the original `let`-based finite-dimensionality lemma.
  simpa [commonKernelQuotient, commonKernelIdeal] using
    common_kernel_quotient_finite (ρ := ρ) (ρ' := ρ')

/-- Helper for Exercise 18-18.2-6: semisimplicity descends along a surjective ring action after
restricting scalars along the quotient map. -/
lemma isSemisimpleModule_of_ringHom_surjective
    {R A M : Type*} [Ring R] [Ring A] [AddCommGroup M] [Module A M]
    (q : R →+* A) (hq : Function.Surjective q)
    (hM : let _ : Module R M := Module.compHom M q
      IsSemisimpleModule R M) :
    IsSemisimpleModule A M := by
  let _ : Module R M := Module.compHom M q
  letI : RingHomSurjective q := ⟨hq⟩
  let l : M →ₛₗ[q] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hbij : Function.Bijective l := by
    constructor
    · intro x y hxy
      exact hxy
    · intro x
      exact ⟨x, rfl⟩
  -- The semilinear identity identifies the restricted `R`-action with the original `A`-action.
  exact (l.isSemisimpleModule_iff_of_bijective hbij).mp hM

/-- Helper for Exercise 18-18.2-6: semisimplicity is unchanged under restriction of scalars along
a surjective ring homomorphism. -/
lemma isSemisimpleModule_iff_of_ringHom_surjective
    {R A M : Type*} [Ring R] [Ring A] [AddCommGroup M] [Module A M]
    (q : R →+* A) (hq : Function.Surjective q) :
    (let _ : Module R M := Module.compHom M q;
      IsSemisimpleModule R M) ↔ IsSemisimpleModule A M := by
  let _ : Module R M := Module.compHom M q
  letI : RingHomSurjective q := ⟨hq⟩
  let l : M →ₛₗ[q] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hbij : Function.Bijective l := by
    constructor
    · intro x y hxy
      exact hxy
    · intro x
      exact ⟨x, rfl⟩
  -- The identity semilinear map compares the restricted and descended scalar actions directly.
  simpa [l] using (LinearMap.isSemisimpleModule_iff_of_bijective (l := l) hbij)

/-- Helper for Exercise 18-18.2-6: simplicity is unchanged under restriction of scalars along a
surjective ring homomorphism. -/
lemma isSimpleModule_iff_of_ringHom_surjective
    {R A M : Type*} [Ring R] [Ring A] [AddCommGroup M] [Module A M]
    (q : R →+* A) (hq : Function.Surjective q) :
    (let _ : Module R M := Module.compHom M q;
      IsSimpleModule R M) ↔ IsSimpleModule A M := by
  let _ : Module R M := Module.compHom M q
  letI : RingHomSurjective q := ⟨hq⟩
  let l : M →ₛₗ[q] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hbij : Function.Bijective l := by
    constructor
    · intro x y hxy
      exact hxy
    · intro x
      exact ⟨x, rfl⟩
  -- The same semilinear identity used for semisimplicity identifies the simple-module lattices.
  simpa [l] using (LinearMap.isSimpleModule_iff_of_bijective (l := l) hbij)

/-- Helper for Exercise 18-18.2-6: the common kernel quotient algebra is semisimple. -/
lemma common_kernel_quotient_isSemisimpleRing
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ') :
    let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
      ρ.asAlgebraHom.prod ρ'.asAlgebraHom
    let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
    let A := MonoidAlgebra k G ⧸ I
    IsSemisimpleRing A := by
  let ψ : MonoidAlgebra k G →ₐ[k] Module.End k V × Module.End k W :=
    ρ.asAlgebraHom.prod ρ'.asAlgebraHom
  let I : Ideal (MonoidAlgebra k G) := RingHom.ker ψ
  letI : I.IsTwoSided := by
    change (RingHom.ker ψ).IsTwoSided
    infer_instance
  let A := MonoidAlgebra k G ⧸ I
  let B := ψ.range
  let φV : B →ₐ[k] Module.End k V :=
    (AlgHom.fst k (Module.End k V) (Module.End k W)).comp (Subalgebra.val B)
  let φW : B →ₐ[k] Module.End k W :=
    (AlgHom.snd k (Module.End k V) (Module.End k W)).comp (Subalgebra.val B)
  letI : Module B V := Module.compHom V φV.toRingHom
  letI : Module B W := Module.compHom W φW.toRingHom
  have hsemV_fromR :
      let _ : Module (MonoidAlgebra k G) V :=
        Module.compHom V (φV.toRingHom.comp ψ.rangeRestrict.toRingHom)
      IsSemisimpleModule (MonoidAlgebra k G) V := by
    -- The descended `B`-action on `V` restricts back to the original `k[G]`-action.
    simpa [B, φV, ψ] using
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hρ
  have hsemW_fromR :
      let _ : Module (MonoidAlgebra k G) W :=
        Module.compHom W (φW.toRingHom.comp ψ.rangeRestrict.toRingHom)
      IsSemisimpleModule (MonoidAlgebra k G) W := by
    -- The same restriction-of-scalars comparison holds for `W`.
    simpa [B, φW, ψ] using
      (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ').mp hρ'
  have hsemV : IsSemisimpleModule B V :=
    isSemisimpleModule_of_ringHom_surjective
      (q := ψ.rangeRestrict.toRingHom) ψ.rangeRestrict_surjective hsemV_fromR
  have hsemW : IsSemisimpleModule B W :=
    isSemisimpleModule_of_ringHom_surjective
      (q := ψ.rangeRestrict.toRingHom) ψ.rangeRestrict_surjective hsemW_fromR
  have hjacV : Ring.jacobson B ≤ Module.annihilator B V := by
    simpa using (IsSemisimpleModule.jacobson_le_annihilator (R := B) (M := V))
  have hjacW : Ring.jacobson B ≤ Module.annihilator B W := by
    simpa using (IsSemisimpleModule.jacobson_le_annihilator (R := B) (M := W))
  have hann :
      Module.annihilator B V ⊓ Module.annihilator B W = ⊥ := by
    apply le_antisymm
    · intro a ha
      -- Vanishing in both coordinate actions forces the element of the image algebra to be zero.
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · ext x
        exact Module.mem_annihilator.mp ha.1 x
      · ext x
        exact Module.mem_annihilator.mp ha.2 x
    · exact bot_le
  have hjac :
      Ring.jacobson B ≤ Module.annihilator B V ⊓ Module.annihilator B W := by
    intro a ha
    exact ⟨hjacV ha, hjacW ha⟩
  have hjac_eq_bot : Ring.jacobson B = ⊥ := by
    exact le_antisymm (hjac.trans <| by simpa [hann]) bot_le
  let _ : Module.Finite k B := by
    infer_instance
  let _ : IsArtinianRing k := inferInstance
  let _ : IsArtinianRing B := IsArtinianRing.of_finite k B
  have hsemB : IsSemisimpleRing B := by
    -- The finite image algebra is Artinian, so Jacobson-zero is equivalent to semisimplicity.
    exact (IsArtinianRing.isSemisimpleRing_iff_jacobson (R := B)).2 hjac_eq_bot
  let e : A ≃ₐ[k] B := by
    simpa [A, I] using Ideal.quotientKerEquivRange (R := k) ψ
  -- Transport semisimplicity back across the canonical quotient-to-range equivalence.
  exact e.symm.isSemisimpleRing

/-- Helper for Exercise 18-18.2-6: the named common kernel quotient is semisimple when both
representations are semisimple. -/
lemma commonKernelQuotient_isSemisimpleRing
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ') :
    IsSemisimpleRing (commonKernelQuotient (k := k) (G := G) ρ ρ') := by
  -- Rewrite the stable API spelling to the original common-kernel semisimplicity lemma.
  simpa [commonKernelQuotient, commonKernelIdeal] using
    common_kernel_quotient_isSemisimpleRing (ρ := ρ) (ρ' := ρ') hρ hρ'

/-- Helper for Exercise 18-18.2-6: the left descended common-kernel module is semisimple. -/
lemma commonKernelQuotient_left_isSemisimpleModule
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ') :
    let _ : Module (commonKernelQuotient (k := k) (G := G) ρ ρ') V :=
      Module.compHom V (commonKernelLeftAction (k := k) (G := G) ρ ρ').toRingHom
    IsSemisimpleModule (commonKernelQuotient (k := k) (G := G) ρ ρ') V := by
  -- Register the finite semisimple common-kernel quotient before asking for the module instance.
  let _ : Module.Finite k (commonKernelQuotient (k := k) (G := G) ρ ρ') :=
    commonKernelQuotient_finite (ρ := ρ) (ρ' := ρ')
  let _ : IsSemisimpleRing (commonKernelQuotient (k := k) (G := G) ρ ρ') :=
    commonKernelQuotient_isSemisimpleRing (ρ := ρ) (ρ' := ρ') hρ hρ'
  infer_instance

/-- Helper for Exercise 18-18.2-6: the right descended common-kernel module is semisimple. -/
lemma commonKernelQuotient_right_isSemisimpleModule
    {ρ : Representation k G V} {ρ' : Representation k G W}
    (hρ : IsSemisimpleRepresentation ρ) (hρ' : IsSemisimpleRepresentation ρ') :
    let _ : Module (commonKernelQuotient (k := k) (G := G) ρ ρ') W :=
      Module.compHom W (commonKernelRightAction (k := k) (G := G) ρ ρ').toRingHom
    IsSemisimpleModule (commonKernelQuotient (k := k) (G := G) ρ ρ') W := by
  -- The same finite semisimple quotient gives semisimplicity of the right descended module.
  let _ : Module.Finite k (commonKernelQuotient (k := k) (G := G) ρ ρ') :=
    commonKernelQuotient_finite (ρ := ρ) (ρ' := ρ')
  let _ : IsSemisimpleRing (commonKernelQuotient (k := k) (G := G) ρ ρ') :=
    commonKernelQuotient_isSemisimpleRing (ρ := ρ) (ρ' := ρ') hρ hρ'
  infer_instance

end EquivalenceCriterion

end Representation
