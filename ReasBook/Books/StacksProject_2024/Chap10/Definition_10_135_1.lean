import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S]

/-
Source/core/bridge triage:
* source-facing: `IsGlobalCompleteIntersection k S` and `IsLocalCompleteIntersection k S`, the
  textbook field-algebra notions from Definition 10.135.1;
* core/canonical: finite algebra presentations `Algebra.Presentation k S (Fin n) (Fin c)` and the
  canonical finiteness owner `Algebra.FinitePresentation k S`;
* bridge/view: the quotient-presentation reformulation
  `IsGlobalCompleteIntersection.quotientPresentation_or_subsingleton`.

Primitive data for the global notion are presentation-level: either the zero-ring convention holds,
or there is a finite presentation whose presentation dimension matches `dim S`.
`Algebra.FinitePresentation k S` is derived from that source-facing data, while the quotient model
is bridge API only.
-/
/-- Definition 10.135.1 (1): a finite type `k`-algebra `S` is a global complete intersection over
`k` if either `S` is subsingleton (the zero-ring convention) or `S` admits a finite algebra
presentation whose presentation dimension equals `dim S`. For a presentation indexed by
`Fin n` generators and `Fin c` relations, this is the textbook condition `dim S = n - c`. -/
class IsGlobalCompleteIntersection (k : Type u) (S : Type v) [Field k] [CommRing S] [Algebra k S] :
    Prop where
  presentation_or_subsingleton :
    Subsingleton S ∨
      ∃ (n c : ℕ) (P : Algebra.Presentation k S (Fin n) (Fin c)),
        ringKrullDim S = P.dimension

namespace IsGlobalCompleteIntersection

/-- The global complete-intersection condition is invariant under `k`-algebra equivalence. -/
theorem of_algEquiv {T : Type*} [CommRing T] [Algebra k T]
    (hS : IsGlobalCompleteIntersection k S) (e : S ≃ₐ[k] T) :
    IsGlobalCompleteIntersection k T where
  presentation_or_subsingleton := by
    rcases hS.presentation_or_subsingleton with hsub | ⟨n, c, P, hP⟩
    · left
      exact ⟨fun x y ↦ by
        simpa using congrArg e (Subsingleton.elim (e.symm x) (e.symm y))⟩
    · right
      refine ⟨n, c, P.ofAlgEquiv e, ?_⟩
      calc
        ringKrullDim T = ringKrullDim S := by
          simpa using (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
        _ = P.dimension := hP
        _ = (P.ofAlgEquiv e).dimension := by
          exact_mod_cast (P.dimension_ofAlgEquiv e).symm

end IsGlobalCompleteIntersection

instance [h : IsGlobalCompleteIntersection k S] : Algebra.FinitePresentation k S := by
  rcases h.presentation_or_subsingleton with hS | ⟨n, c, P, _⟩
  · let _ : Subsingleton S := hS
    have hsurj : Function.Surjective (Algebra.ofId k S) := fun x ↦ ⟨0, Subsingleton.elim _ _⟩
    have hker : (RingHom.ker (algebraMap k S)).FG := by
      simpa [RingHom.ker_eq_top_of_subsingleton (algebraMap k S)] using Ideal.fg_top k
    have hfp' : (Algebra.ofId k S).FinitePresentation :=
      AlgHom.FinitePresentation.of_surjective (Algebra.ofId k S) hsurj <| by
        simpa [Algebra.toRingHom_ofId] using hker
    have hfp : (algebraMap k S).FinitePresentation := by
      simpa [AlgHom.FinitePresentation, Algebra.toRingHom_ofId] using hfp'
    exact (RingHom.finitePresentation_algebraMap).mp hfp
  · simpa using P.finitePresentation_of_isFinite

/-- Helper for Definition 10.135.1: a finite presentation identifies `S` with the quotient by the
span of its defining relations. -/
theorem presentation_relation_quotient_model {n c : ℕ}
    (P : Algebra.Presentation k S (Fin n) (Fin c)) :
    Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range P.relation)) ≃ₐ[k] S) := by
  -- Transport the quotient from the explicit span of relations to the kernel-based presentation.
  refine ⟨?_⟩
  exact (Ideal.quotientEquivAlgOfEq k P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars k)

/-- Helper for Definition 10.135.1: a presentation with `Fin n` generators and `Fin c` relations
has presentation dimension `n - c`. -/
lemma presentation_dimension_eq_fin_sub {n c : ℕ}
    (P : Algebra.Presentation k S (Fin n) (Fin c)) :
    P.dimension = n - c := by
  -- Unfold presentation dimension and evaluate the cardinalities of the finite index sets.
  simpa [Algebra.Presentation.dimension]

/-- Textbook quotient-presentation form of `IsGlobalCompleteIntersection`. -/
theorem IsGlobalCompleteIntersection.quotientPresentation_or_subsingleton
    [IsGlobalCompleteIntersection k S] :
    Subsingleton S ∨
      ∃ (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k),
        Nonempty ((MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] S) ∧
          ringKrullDim S = n - c := by
  rcases (inferInstance : IsGlobalCompleteIntersection k S).presentation_or_subsingleton with
    hsub | ⟨n, c, P, hdim⟩
  · -- The zero-ring convention is one branch of the definition itself.
    exact Or.inl hsub
  · -- In the genuine presentation branch, reuse the chosen presentation data directly.
    refine Or.inr ⟨n, c, P.relation, presentation_relation_quotient_model P, ?_⟩
    -- Rewrite the stored presentation dimension into the textbook count `n - c`.
    rw [presentation_dimension_eq_fin_sub P] at hdim
    exact hdim

-- Proof sketch: the convention in the source declares every subsingleton `k`-algebra, hence in
-- particular the zero ring, to be a global complete intersection.
/-- Subsingleton `k`-algebras are global complete intersections by convention. -/
instance [Subsingleton S] : IsGlobalCompleteIntersection k S where
  presentation_or_subsingleton := .inl inferInstance

/-- Definition 10.135.1 (2): a `k`-algebra `S` is a local complete intersection over `k` if
`Spec(S)` is covered by finitely many basic opens `D(g)` such that each localization `S[g⁻¹]` is
a global complete intersection over `k`; algebraically, the cover is encoded by
`Ideal.span (s : Set S) = ⊤`. This cover condition already implies finite presentation, hence
finite type, by the standard locality theorem for `Algebra.FinitePresentation`. -/
class IsLocalCompleteIntersection (k : Type u) (S : Type v) [Field k] [CommRing S]
    [Algebra k S] : Prop where
  exists_basicOpen_cover :
    ∃ s : Finset S,
      Ideal.span (s : Set S) = ⊤ ∧
        ∀ g ∈ s, IsGlobalCompleteIntersection k (Localization.Away g)

instance [h : IsLocalCompleteIntersection k S] : Algebra.FinitePresentation k S := by
  rcases h.exists_basicOpen_cover with ⟨s, hs, hglobal⟩
  letI (g : s) : IsGlobalCompleteIntersection k (Localization.Away (g : S)) := hglobal g g.2
  letI (g : s) : Algebra.FinitePresentation k (Localization.Away (g : S)) := inferInstance
  exact Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway
    (fun g : s ↦ (g : S)) (by simpa using hs) (fun g : s ↦ Localization.Away (g : S))

-- Proof sketch: take the single basic open `D(1) = Spec(S)`, whose localization is canonically
-- `S`, and apply the global complete intersection hypothesis.
/-- Every global complete intersection is a local complete intersection. -/
instance [IsGlobalCompleteIntersection k S] :
    IsLocalCompleteIntersection k S where
  exists_basicOpen_cover := by
    refine ⟨{1}, by simp, ?_⟩
    intro g hg
    have hg1 : g = (1 : S) := by simpa using hg
    subst hg1
    simpa using IsGlobalCompleteIntersection.of_algEquiv
      ‹IsGlobalCompleteIntersection k S›
      ((IsLocalization.atOne S (Localization.Away (1 : S))).restrictScalars k)
