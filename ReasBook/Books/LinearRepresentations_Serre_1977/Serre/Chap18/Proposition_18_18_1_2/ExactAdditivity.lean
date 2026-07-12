import Mathlib
import LinearRepresentations_Serre_1977.Chap10.Definition_10_10_1_2
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_3_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1.ProjectiveScalarExtensionClasses
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_1_2
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.FiniteOrderEigenbasis
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.QuotientCharpoly
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.RealizationCore

noncomputable section

open CategoryTheory
open scoped Representation
open scoped TensorProduct

universe u v x y

namespace Representation

section BasicProperties

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v}
variable {G : Type u}
variable {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Helper for Proposition 18-18.1-2: if two multisets agree, then sums over their attached
copies agree once the summands are matched along that equality. -/
theorem attached_sum_eq_of_eq
    [AddCommMonoid A]
    {m₁ m₂ : Multiset k} (hm : m₁ = m₂)
    (f₁ : {x // x ∈ m₁} → A) (f₂ : {x // x ∈ m₂} → A)
    (hfun : ∀ μ : {x // x ∈ m₁}, f₁ μ = f₂ ⟨μ.1, hm ▸ μ.2⟩) :
    (Multiset.map f₁ m₁.attach).sum = (Multiset.map f₂ m₂.attach).sum := by
  -- Transport the attached roots across `hm`, then compare the two mapped multisets termwise.
  subst hm
  have hmap :
      Multiset.map f₁ m₁.attach = Multiset.map f₂ m₁.attach := by
    apply Multiset.map_congr rfl
    intro μ _
    simpa using hfun μ
  simpa [hmap]


section Exactness

variable [AddCommMonoid A]
variable [Group G]

/-- Helper for Proposition 18-18.1-2: the characteristic polynomial of an endomorphism preserving
an invariant submodule factors into the characteristic polynomials on the submodule and on the
quotient. -/
private theorem charpoly_eq_charpoly_restrict_mul_charpoly_mapQ_local
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] V) (W : Submodule k V) (hW : W ≤ W.comap f) :
    f.charpoly = (f.restrict hW).charpoly * (W.mapQ W f hW).charpoly := by
  classical
  let m := Module.Free.ChooseBasisIndex k W
  let bW : Module.Basis m k W := Module.Free.chooseBasis k W
  let n := Module.Free.ChooseBasisIndex k (V ⧸ W)
  let bQ : Module.Basis n k (V ⧸ W) := Module.Free.chooseBasis k (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let A : Matrix m m k := LinearMap.toMatrix bW bW (f.restrict hW)
  let B : Matrix m n k := Matrix.of fun i j ↦
    (b.repr (f (b (Sum.inr j)))) (Sum.inl i)
  let D : Matrix n n k := LinearMap.toMatrix bQ bQ (W.mapQ W f hW)
  have hmat : LinearMap.toMatrix b b f = Matrix.fromBlocks A B 0 D := by
    -- In a basis adapted to `W` and the quotient, the matrix is block upper triangular.
    ext u v
    cases u with
    | inl i =>
        cases v with
        | inl j =>
            simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
              LinearMap.toMatrix_apply]
            apply Module.Basis.sumQuot_repr_inl_of_mem
        | inr j =>
            simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr i =>
        cases v with
        | inl j =>
            suffices W.mkQ (f (bW j)) = 0 by
              simp [LinearMap.toMatrix_apply, b, this]
            rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
            exact hW (Submodule.coe_mem (bW j))
        | inr j =>
            simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
              Matrix.fromBlocks_apply₂₂, b, D]
            rw [← Module.Basis.sumQuot_inr bW bQ j, W.mapQ_apply]
            simp
  -- The block-upper-triangular matrix formula yields the desired factorization.
  rw [← LinearMap.charpoly_toMatrix f b, hmat, Matrix.charpoly_fromBlocks_zero₂₁,
    ← LinearMap.charpoly_toMatrix (f.restrict hW) bW,
    ← LinearMap.charpoly_toMatrix (W.mapQ W f hW) bQ]

/-- Helper for Proposition 18-18.1-2: a representation equivalence preserves the modular
character on the `p`-regular locus. -/
private theorem modularCharacter_eq_of_equiv
    (lift : PrimeToPRoot p k → A)
    {V₁ : Type x} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    {V₂ : Type x} [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    (e : ρ₁.Equiv ρ₂) :
    Representation.modularCharacter lift ρ₁ = Representation.modularCharacter lift ρ₂ := by
  funext s
  -- An equivariant linear equivalence conjugates `ρ₁ s` to `ρ₂ s`, so the two modular-character
  -- sums run over the same root multiset.
  have hchar : (ρ₂ s.1).charpoly = (ρ₁ s.1).charpoly := by
    simpa [Representation.Equiv.conj_apply_self (ρ := ρ₁) (σ := ρ₂) s.1 e] using
      (LinearEquiv.charpoly_conj e.toLinearEquiv (ρ₁ s.1))
  have hroots : (ρ₂ s.1).charpoly.roots = (ρ₁ s.1).charpoly.roots := by
    -- The equality of characteristic polynomials lets us compare the attached roots termwise.
    simpa using congrArg Polynomial.roots hchar
  change
    (Multiset.map
      (fun μ : { x // x ∈ (ρ₁ s.1).charpoly.roots } ↦
        lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ₁ s.2 μ.2))
      (ρ₁ s.1).charpoly.roots.attach).sum =
    (Multiset.map
      (fun μ : { x // x ∈ (ρ₂ s.1).charpoly.roots } ↦
        lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ₂ s.2 μ.2))
      (ρ₂ s.1).charpoly.roots.attach).sum
  symm
  exact attached_sum_eq_of_eq hroots
    (fun μ ↦ lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ₂ s.2 μ.2))
    (fun μ ↦ lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ₁ s.2 μ.2))
      (fun μ ↦ by
        apply congrArg lift
        ext
        simp [charpolyRoot_primeToPRoot_coe])

/-- Helper for Proposition 18-18.1-2: summing a proof-dependent `pmap` over a sum of multisets
splits into the corresponding two `pmap` sums. -/
private theorem pmap_sum_add_split
    {α : Type x}
    (m₁ m₂ : Multiset α)
    (f : ∀ a, a ∈ m₁ + m₂ → A) :
    ((m₁ + m₂).pmap f (by intro a ha; exact ha)).sum =
      (m₁.pmap (fun a ha ↦ f a (Multiset.mem_add.mpr (Or.inl ha)))
        (by intro a ha; exact ha)).sum +
      (m₂.pmap (fun a ha ↦ f a (Multiset.mem_add.mpr (Or.inr ha)))
        (by intro a ha; exact ha)).sum := by
  induction m₁ using Multiset.induction_on with
  | empty =>
      -- With no left summand, the right branch is the original `pmap` after proof-irrelevant
      -- transport along `0 + m₂ = m₂`.
      have hright :
          m₂.pmap (fun a ha ↦ f a (Multiset.mem_add.mpr (Or.inr ha)))
            (by intro a ha; exact ha) =
          m₂.pmap f (by
            intro a ha
            exact show a ∈ 0 + m₂ by simpa using ha) := by
        simpa using (Multiset.pmap_congr (s := m₂)
          (H₁ := by intro a ha; exact ha)
          (H₂ := by
            intro a ha
            exact show a ∈ 0 + m₂ by simpa using ha)
          (fun a ha h₁ h₂ ↦ by rfl))
      simp [hright]
  | @cons a m ih =>
      let fTail : ∀ b, b ∈ m + m₂ → A := fun b hb ↦
        f b (show b ∈ a ::ₘ m + m₂ by
          simpa [Multiset.cons_add] using
            (Multiset.mem_cons_of_mem hb : b ∈ a ::ₘ (m + m₂)))
      have htail_total :
          (m + m₂).pmap fTail (by intro b hb; exact hb) =
          (m + m₂).pmap f (by
            intro b hb
            simpa [Multiset.cons_add] using
              (Multiset.mem_cons_of_mem hb : b ∈ a ::ₘ (m + m₂))) := by
        refine Multiset.pmap_congr (s := m + m₂) ?_
        intro b hb h₁ h₂
        rfl
      have hleft :
          m.pmap (fun b hb ↦ fTail b (Multiset.mem_add.mpr (Or.inl hb)))
            (by intro b hb; exact hb) =
          m.pmap
            (fun b hb ↦ f b (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_of_mem hb))))
            (by intro b hb; exact hb) := by
        simp [fTail]
      have hright :
          m₂.pmap (fun b hb ↦ fTail b (Multiset.mem_add.mpr (Or.inr hb)))
            (by intro b hb; exact hb) =
          m₂.pmap (fun b hb ↦ f b (Multiset.mem_add.mpr (Or.inr hb)))
            (by intro b hb; exact hb) := by
        simp [fTail]
      have hmain := ih fTail
      rw [hleft, hright] at hmain
      have ha_eq :
          f a (show a ∈ a ::ₘ m + m₂ by
            simpa [Multiset.cons_add] using (Multiset.mem_cons_self a (m + m₂))) =
          f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) := by
        simp
      have hcons_total' :
          (((a ::ₘ m) + m₂).pmap f (by intro b hb; exact hb)).sum =
          f a (show a ∈ a ::ₘ m + m₂ by
            simpa [Multiset.cons_add] using (Multiset.mem_cons_self a (m + m₂))) +
            ((m + m₂).pmap f (by
              intro b hb
              simpa [Multiset.cons_add] using
                (Multiset.mem_cons_of_mem hb : b ∈ a ::ₘ (m + m₂)))).sum := by
        simpa [Multiset.cons_add, Multiset.sum_cons] using
          congrArg Multiset.sum
            (Multiset.pmap_cons f a (m + m₂) (by
              intro b hb
              simpa [Multiset.cons_add] using hb))
      have hcons_total :
          (((a ::ₘ m) + m₂).pmap f (by intro b hb; exact hb)).sum =
          f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) +
            ((m + m₂).pmap fTail (by intro b hb; exact hb)).sum := by
        calc
          (((a ::ₘ m) + m₂).pmap f (by intro b hb; exact hb)).sum =
              f a (show a ∈ a ::ₘ m + m₂ by
                  simpa [Multiset.cons_add] using
                    (Multiset.mem_cons_self a (m + m₂))) +
                ((m + m₂).pmap f (by
                  intro b hb
                  simpa [Multiset.cons_add] using
                    (Multiset.mem_cons_of_mem hb : b ∈ a ::ₘ (m + m₂)))).sum := hcons_total'
          _ =
              f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) +
                ((m + m₂).pmap f (by
                  intro b hb
                  simpa [Multiset.cons_add] using
                    (Multiset.mem_cons_of_mem hb : b ∈ a ::ₘ (m + m₂)))).sum := by
                simp [ha_eq]
          _ =
              f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) +
                ((m + m₂).pmap fTail (by intro b hb; exact hb)).sum := by
                rw [← htail_total]
      have hcons_left :
          ((a ::ₘ m).pmap (fun b hb ↦ f b (Multiset.mem_add.mpr (Or.inl hb)))
            (by intro b hb; exact hb)).sum =
          f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) +
            (m.pmap
              (fun b hb ↦ f b (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_of_mem hb))))
              (by intro b hb; exact hb)).sum := by
        simp [Multiset.pmap_cons, Multiset.sum_cons]
        apply congrArg (fun t ↦
          f a (Multiset.mem_add.mpr (Or.inl (Multiset.mem_cons_self a m))) + t)
        refine congrArg Multiset.sum ?_
        refine Multiset.pmap_congr (s := m) ?_
        intro b hb h₁ h₂
        rfl
      -- After peeling off the head term, the tail is exactly the induction hypothesis.
      rw [hcons_total, hcons_left, hmain]
      simpa [add_assoc]

/-- Helper for Proposition 18-18.1-2: the factorization of the characteristic polynomial across
an invariant submodule and quotient yields the additive modular-character formula. -/
private theorem modularCharacter_roots_mul_add_local
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (lift : PrimeToPRoot p k → A) (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g, W ≤ W.comap (ρ g))
    (s : { t : G // IsPRegular p t }) :
    Representation.modularCharacter lift ρ s =
      Representation.modularCharacter lift (ρ.subrepresentation W hW) s +
        Representation.modularCharacter lift (ρ.quotient W hW) s := by
  classical
  let P : Multiset k := (ρ.subrepresentation W hW s.1).charpoly.roots
  let Q : Multiset k := (ρ.quotient W hW s.1).charpoly.roots
  have hchar :
      (ρ s.1).charpoly =
        (ρ.subrepresentation W hW s.1).charpoly *
          (ρ.quotient W hW s.1).charpoly := by
    -- The source proof uses the invariant-submodule factorization of the characteristic
    -- polynomial at the chosen `p`-regular element.
    simpa using
      charpoly_eq_charpoly_restrict_mul_charpoly_mapQ_local
        (ρ s.1) W (hW s.1)
  have hmul_ne_zero :
      (ρ.subrepresentation W hW s.1).charpoly *
          (ρ.quotient W hW s.1).charpoly ≠ 0 := by
    rw [← hchar]
    exact (LinearMap.charpoly_monic (ρ s.1)).ne_zero
  have hroots : (ρ s.1).charpoly.roots = P + Q := by
    rw [hchar]
    simpa [P, Q] using Polynomial.roots_mul hmul_ne_zero
  have hgoal :
      (((ρ s.1).charpoly.roots).pmap
        (fun μ hμ ↦
          lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ s.2 hμ))
        (by intro μ hμ; exact hμ)).sum =
      ((((ρ.subrepresentation W hW) s.1).charpoly.roots).pmap
        (fun μ hμ ↦
          lift <|
            charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.subrepresentation W hW) s.2 hμ)
        (by intro μ hμ; exact hμ)).sum +
      ((((ρ.quotient W hW) s.1).charpoly.roots).pmap
        (fun μ hμ ↦
          lift <|
            charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.quotient W hW) s.2 hμ)
        (by intro μ hμ; exact hμ)).sum := by
    -- Route correction: split the ambient roots at the plain-multiset level, rather than
    -- transporting attached roots across `hroots`.
    let ambientLift : ∀ μ, μ ∈ P + Q → A := fun μ hμ ↦
      lift <|
        charpolyRoot_primeToPRoot (p := p) (k := k) ρ s.2 <|
          show μ ∈ (ρ s.1).charpoly.roots by
            simpa [hroots] using hμ
    have hsplit :
        (((ρ s.1).charpoly.roots).pmap
          (fun μ hμ ↦
            lift (charpolyRoot_primeToPRoot (p := p) (k := k) ρ s.2 hμ))
          (by intro μ hμ; exact hμ)).sum =
        (((P + Q).pmap
          (fun μ hμ ↦ ambientLift μ hμ)
          (by intro μ hμ; exact hμ)).sum) := by
      simp [ambientLift, hroots]
      refine congrArg Multiset.sum ?_
      refine Multiset.pmap_congr (s := P + Q) ?_
      intro μ hμ h₁ h₂
      apply congrArg lift
      ext
      simp [ambientLift, charpolyRoot_primeToPRoot_coe, hroots]
    rw [hsplit]
    rw [pmap_sum_add_split]
    have hsub :
        (P.pmap
          (fun μ hμ ↦ ambientLift μ (Multiset.mem_add.mpr (Or.inl hμ)))
          (by intro μ hμ; exact hμ)).sum =
        ((((ρ.subrepresentation W hW) s.1).charpoly.roots).pmap
          (fun μ hμ ↦
            lift <|
              charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.subrepresentation W hW) s.2 hμ)
          (by intro μ hμ; exact hμ)).sum := by
      -- The left branch packages the same scalar roots as the subrepresentation.
      have hpmap :
          P.pmap
            (fun μ hμ ↦ ambientLift μ (Multiset.mem_add.mpr (Or.inl hμ)))
            (by intro μ hμ; exact hμ) =
          P.pmap
            (fun μ hμ ↦
              lift <|
                charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.subrepresentation W hW) s.2 hμ)
            (by intro μ hμ; exact hμ) := by
        refine Multiset.pmap_congr (s := P) ?_
        intro μ hμ h₁ h₂
        apply congrArg lift
        ext
        simp [ambientLift, charpolyRoot_primeToPRoot_coe, hroots]
      simpa [P] using congrArg Multiset.sum hpmap
    have hquot :
        (Q.pmap
          (fun μ hμ ↦ ambientLift μ (Multiset.mem_add.mpr (Or.inr hμ)))
          (by intro μ hμ; exact hμ)).sum =
        ((((ρ.quotient W hW) s.1).charpoly.roots).pmap
          (fun μ hμ ↦
            lift <|
              charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.quotient W hW) s.2 hμ)
          (by intro μ hμ; exact hμ)).sum := by
      -- The quotient branch is identical after comparing the packaged roots termwise.
      have hpmap :
          Q.pmap
            (fun μ hμ ↦ ambientLift μ (Multiset.mem_add.mpr (Or.inr hμ)))
            (by intro μ hμ; exact hμ) =
          Q.pmap
            (fun μ hμ ↦
              lift <|
                charpolyRoot_primeToPRoot (p := p) (k := k) (ρ.quotient W hW) s.2 hμ)
            (by intro μ hμ; exact hμ) := by
        refine Multiset.pmap_congr (s := Q) ?_
        intro μ hμ h₁ h₂
        apply congrArg lift
        ext
        simp [ambientLift, charpolyRoot_primeToPRoot_coe, hroots]
      simpa [Q] using congrArg Multiset.sum hpmap
    rw [hsub, hquot]
  simpa [Representation.modularCharacter, Multiset.pmap_eq_map_attach] using hgoal

/-- Helper for Proposition 18-18.1-2: the modular character of a representation splits as the sum
of the modular characters of an invariant subrepresentation and its quotient. -/
private theorem modularCharacter_add_of_invariant_submodule
    {V : Type x} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (lift : PrimeToPRoot p k → A) (ρ : Representation k G V)
    (W : Submodule k V) (hW : ∀ g, W ≤ W.comap (ρ g))
    (s : { t : G // IsPRegular p t }) :
    Representation.modularCharacter lift ρ s =
      Representation.modularCharacter lift (ρ.subrepresentation W hW) s +
        Representation.modularCharacter lift (ρ.quotient W hW) s := by
  -- The invariant-submodule additivity is exactly the root-splitting statement proved above.
  simpa using modularCharacter_roots_mul_add_local
    (p := p) (lift := lift) ρ W hW s

-- Proof sketch: for each `p`-regular element, the middle action in a short exact sequence is

/-- Helper for Proposition 18-18.1-2: the modular character is additive on short exact
sequences of finite-dimensional representations. -/
theorem modularCharacter_add_of_shortExactSequence_bridge
    (lift : PrimeToPRoot p k → A)
    (S : ShortComplex (FDRep k G)) (hS : S.ShortExact) (s : { t : G // IsPRegular p t }) :
    φ[lift](S.X₂.ρ) s =
      φ[lift](S.X₁.ρ) s +
        φ[lift](S.X₃.ρ) s := by
  let F : FDRep k G ⥤ ModuleCat k :=
    (forget₂ (FDRep k G) (Rep k G)) ⋙ (forget₂ (Rep k G) (ModuleCat k))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat k` preserves the given short exact sequence.
    simpa [F] using hS.map_of_exact F
  let f : S.X₁.V →ₗ[k] S.X₂.V := ((forget₂ (FDRep k G) (Rep k G)).map S.f).hom.toLinearMap
  let g : S.X₂.V →ₗ[k] S.X₃.V := ((forget₂ (FDRep k G) (Rep k G)).map S.g).hom.toLinearMap
  have hExact : Function.Exact f g := by
    -- In `ModuleCat k`, short exactness means exactness of the underlying linear maps.
    simpa [f, g] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hf : Function.Injective f := by
    -- The left map of a short exact sequence is mono, hence injective on vectors.
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    -- The right map of a short exact sequence is epi, hence surjective on vectors.
    exact (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  let W : Submodule k S.X₂.V := LinearMap.range f
  have hWker : W = LinearMap.ker g := by
    -- Exactness identifies the image of the left map with the kernel of the right map.
    simpa [W, f, g] using hExact.linearMap_ker_eq.symm
  have hW : ∀ a : G, W ≤ W.comap (S.X₂.ρ a) := by
    intro a y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨S.X₁.ρ a x, ?_⟩
    -- The image of `f` is stable because `f` intertwines the two actions.
    change
      ((forget₂ (FDRep k G) (Rep k G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep k G) (Rep k G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep k G) (Rep k G)).map S.f) a x
  let e₁ : Representation.Equiv S.X₁.ρ (Representation.subrepresentation S.X₂.ρ W hW) := by
    refine Representation.Equiv.mk (LinearEquiv.ofInjective f hf) ?_
    intro a
    ext x
    -- The image equivalence intertwines the source action with the induced subrepresentation.
    change
      ((forget₂ (FDRep k G) (Rep k G)).map S.f).hom.toLinearMap (S.X₁.ρ a x) =
        S.X₂.ρ a (((forget₂ (FDRep k G) (Rep k G)).map S.f).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep k G) (Rep k G)).map S.f) a x
  let qg : S.X₂.V ⧸ W →ₗ[k] S.X₃.V :=
    W.liftQ g hWker.le
  have hqg_injective : Function.Injective qg := by
    -- The quotient map has trivial kernel because exactness gives `W = ker g`.
    refine LinearMap.ker_eq_bot.mp ?_
    rw [Submodule.ker_liftQ_eq_bot']
    exact hWker
  have hqg_surjective : Function.Surjective qg := by
    -- Surjectivity descends from the original map `g`.
    rw [← LinearMap.range_eq_top]
    rw [Submodule.range_liftQ]
    exact LinearMap.range_eq_top.2 hg
  let e₃ : Representation.Equiv (Representation.quotient S.X₂.ρ W hW) S.X₃.ρ := by
    refine Representation.Equiv.mk (LinearEquiv.ofBijective qg ⟨hqg_injective, hqg_surjective⟩) ?_
    intro a
    ext x
    -- On quotient classes, the induced action is still defined by the intertwining map `g`.
    change
      ((forget₂ (FDRep k G) (Rep k G)).map S.g).hom.toLinearMap (S.X₂.ρ a x) =
        S.X₃.ρ a (((forget₂ (FDRep k G) (Rep k G)).map S.g).hom.toLinearMap x)
    exact Rep.hom_comm_apply ((forget₂ (FDRep k G) (Rep k G)).map S.g) a x
  have hmod₁ :
      Representation.modularCharacter lift S.X₁.ρ =
        Representation.modularCharacter lift (Representation.subrepresentation S.X₂.ρ W hW) := by
    -- Equivariant linear equivalence preserves the modular character.
    simpa [W, f] using modularCharacter_eq_of_equiv (p := p) (lift := lift) e₁
  have hmod₃ :
      Representation.modularCharacter lift S.X₃.ρ =
        Representation.modularCharacter lift (Representation.quotient S.X₂.ρ W hW) := by
    -- The quotient equivalence transports the modular character back to `S.X₃`.
    simpa [W, qg] using (modularCharacter_eq_of_equiv (p := p) (lift := lift) e₃).symm
  -- Apply invariant-submodule additivity to the image of `f`, then transport the two summands
  -- back to the ends of the short exact sequence.
  calc
    φ[lift](S.X₂.ρ) s =
        Representation.modularCharacter lift (Representation.subrepresentation S.X₂.ρ W hW) s +
          Representation.modularCharacter lift (Representation.quotient S.X₂.ρ W hW) s := by
            simpa [W] using
              modularCharacter_add_of_invariant_submodule
                (p := p) (lift := lift) S.X₂.ρ W hW s
    _ = Representation.modularCharacter lift S.X₁.ρ s +
          Representation.modularCharacter lift S.X₃.ρ s := by
          rw [← hmod₁, ← hmod₃]
    _ = φ[lift](S.X₁.ρ) s + φ[lift](S.X₃.ρ) s := by
          rfl

end Exactness

end BasicProperties

end Representation
