import stacks_proof.stacks_project.Chap10.Lemma_10_99_16.PrincipalQuotients

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Pointwise
open scoped TensorProduct

noncomputable section

universe u

section

variable {A : Type u} [CommRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- Helper for Lemma 10.99.16: in every degree, the quotient-first public owner
`K ↦ Tor_n^A(K, M)` is naturally isomorphic to the fixed-left source owner
`K ↦ Tor'_n^A(M, K)`. This is the owner bridge needed to transport the low-degree source exact
row back to the public quotient-first statement. -/
noncomputable def tor_left_owner_iso (n : ℕ) :
    (((Tor (ModuleCat A) n).flip).obj (ModuleCat.of A M)) ≅
      ((Tor' (ModuleCat A) n).obj (ModuleCat.of A M)) where
  hom :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat A) n).hom.app X).app (ModuleCat.of A M))
      naturality := by
        intro X Y g
        -- Proof comment: naturality of `tor_flip_iso` in the first Tor variable becomes
        -- naturality of the fixed-right owner after evaluation at `M`.
        simpa using congrArg (fun α => α.app (ModuleCat.of A M))
          ((tor_flip_iso (ModuleCat A) n).hom.naturality g) }
  inv :=
    { app := fun X ↦ (((tor_flip_iso (ModuleCat A) n).inv.app X).app (ModuleCat.of A M))
      naturality := by
        intro X Y g
        -- Proof comment: the inverse comparison is natural for the same evaluated reason.
        simpa using congrArg (fun α => α.app (ModuleCat.of A M))
          ((tor_flip_iso (ModuleCat A) n).inv.naturality g) }
  hom_inv_id := by
    ext X x
    -- Proof comment: the componentwise inverse law is inherited from `tor_flip_iso`.
    have h := congrArg (fun α => α.app (ModuleCat.of A M))
      ((tor_flip_iso (ModuleCat A) n).hom_inv_id_app X)
    simpa using congrArg (fun g => g x) (congrArg ModuleCat.Hom.hom h)
  inv_hom_id := by
    ext X x
    -- Proof comment: the same componentwise argument proves the opposite inverse law.
    have h := congrArg (fun α => α.app (ModuleCat.of A M))
      ((tor_flip_iso (ModuleCat A) n).inv_hom_id_app X)
    simpa using congrArg (fun g => g x) (congrArg ModuleCat.Hom.hom h)

/-- Helper for Lemma 10.99.16: degree `1` of `tor_left_owner_iso`. -/
abbrev tor_one_left_owner_iso :
    (((Tor (ModuleCat A) 1).flip).obj (ModuleCat.of A M)) ≅
      ((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)) :=
  tor_left_owner_iso (A := A) (M := M) 1

/-- Helper for Lemma 10.99.16: when the quotient `A / (f)` is the first Tor variable, the public
owner is already identified with the fixed-left source owner needed for the source-faithful exact
sequence argument. -/
noncomputable def tor_one_quotient_source_owner_iso
    (f : A) :
    (((Tor (ModuleCat A) 1).obj
        (ModuleCat.of A (A ⧸ Ideal.span ({f} : Set A)))).obj (ModuleCat.of A M)) ≅
      (((Tor' (ModuleCat A) 1).obj (ModuleCat.of A M)).obj
        (ModuleCat.of A (A ⧸ Ideal.span ({f} : Set A)))) := by
  -- Proof comment: fix the right Tor variable `M` and evaluate the quotient-first owner bridge
  -- at the principal quotient `A / (f)`.
  simpa using
    (tor_one_left_owner_iso (A := A) (M := M)).app
      (ModuleCat.of A (A ⧸ Ideal.span ({f} : Set A)))

end
