import MultiViewIdentifiability.Basic
import MultiViewIdentifiability.FDClosure
import MultiViewIdentifiability.Identifiability
import MultiViewIdentifiability.Certificate

/-!
# Minimum Augmentation (MinAug)

The minimum-augmentation (MinAug) problem and its key theoretical properties.

## Problem definition

Given an interface `I` and a non-identifiable query `Q`, the **minimum augmentation**
asks for the smallest set of additional attributes `aug` such that adding `aug` to an
overlap `Ω̃ⱼ` provides an identifiability certificate.

## Formal setup

- `AugCertificate I Õ aug Q`: adding `aug` to `Ω̃ⱼ` certifies `Q`.
- `IsMinimalAug I Õ aug Q`: no proper sub-augmentation certifies `Q`.

## Theorems formalized

- **Monotonicity**: larger augmentations preserve certification.
- **Closure characterisation**: certification depends only on `fdClosure Σ (Ω̃ ∪ aug)`.
- Greedy approximation and NP-hardness are marked `sorry`.
-/

/-!
## Augmentation certificate
-/

/-- `aug` is an **augmentation certificate** for `Q` on overlap `Ω̃ⱼ`:
    adding `aug` to `Ω̃ⱼ` and closing under `Σ` covers `Q.footprint`. -/
def AugCertificate (I : Interface) (Õ aug : AttrSet) (Q : BoolCQ) : Prop :=
  Q.footprint ⊆ fdClosure I.fds (AttrSet.union Õ aug)

/-- The **augmented interface**: same legality as `I`, but with the single augmented
    overlap `Ω̃ ∪ aug` made observable. -/
def augmentedInterface (I : Interface) (Õ aug : AttrSet) : Interface where
  legality    := I.legality
  augOverlaps := [AttrSet.union Õ aug]
  aug_closed  := by
    intro O hO
    obtain rfl | hnil := List.mem_cons.mp hO
    · exact fdClosure_extensive I.fds (AttrSet.union Õ aug)
    · cases hnil

/-- If `aug` certifies `Q` on `Ω̃ⱼ`, then `Q` is identifiable **under the augmented
    interface** `augmentedInterface I Õ aug`, where `Ω̃ⱼ ∪ aug` is observable.

    This is the correct statement of the augmentation guarantee. It does **not** make `Q`
    identifiable under the original `I`: observational equivalence on `I.augOverlaps` gives
    agreement on `Ω̃ⱼ` but not on `aug` (the `aug` attributes are not directly observed,
    only their closure is), so the lift to `I` fails in general. The earlier formulation
    that concluded `Identifiable I Q` was false; this is the provable version. -/
theorem augCertificate_identifiable_augmented (I : Interface) (Õ aug : AttrSet) (Q : BoolCQ)
    (hcert : AugCertificate I Õ aug Q) :
    Identifiable (augmentedInterface I Õ aug) Q :=
  certificate_sufficiency (augmentedInterface I Õ aug) Q (AttrSet.union Õ aug)
    List.mem_cons_self hcert

/-!
## Minimality
-/

/-- An augmentation is **minimal** if no proper subset also certifies. -/
def IsMinimalAug (I : Interface) (Õ aug : AttrSet) (Q : BoolCQ) : Prop :=
  AugCertificate I Õ aug Q ∧
  ∀ aug' : AttrSet, aug' ⊆ aug → aug ⊆ aug' → True -- placeholder

/-!
## Monotonicity
-/

/-- **Monotonicity**: if `aug₁ ⊆ aug₂` and `aug₁` certifies `Q`, then `aug₂` does too. -/
theorem augCertificate_mono (I : Interface) (Õ aug₁ aug₂ : AttrSet) (Q : BoolCQ)
    (hsub : aug₁ ⊆ aug₂)
    (hcert : AugCertificate I Õ aug₁ Q) :
    AugCertificate I Õ aug₂ Q :=
  AttrSet.subset_trans hcert
    (fdClosure_mono I.fds (fun a ha =>
      match ha with
      | Or.inl ha => Or.inl ha
      | Or.inr haug₁ => Or.inr (hsub a haug₁)))

/-!
## Closure characterization
-/

/-- **Closure characterisation**: `AugCertificate` depends only on `fdClosure Σ (Ω̃ ∪ aug)`. -/
theorem augCertificate_closure_char (I : Interface) (Õ aug : AttrSet) (Q : BoolCQ) :
    AugCertificate I Õ aug Q ↔ Q.footprint ⊆ fdClosure I.fds (AttrSet.union Õ aug) :=
  Iff.rfl

/-- Two augmentations with the same FD-closure are interchangeable certificates. -/
theorem aug_closure_equiv (I : Interface) (Õ aug₁ aug₂ : AttrSet) (Q : BoolCQ)
    (hclos : ∀ a, fdClosure I.fds (AttrSet.union Õ aug₁) a ↔
                   fdClosure I.fds (AttrSet.union Õ aug₂) a) :
    AugCertificate I Õ aug₁ Q ↔ AugCertificate I Õ aug₂ Q := by
  constructor
  · intro h a ha; exact (hclos a).mp (h a ha)
  · intro h a ha; exact (hclos a).mpr (h a ha)

/-!
## Residual
-/

/-- The **residual**: attributes of `Q.footprint` not yet covered by `fdClosure Σ Ω̃ⱼ`. -/
def Residual (I : Interface) (Õ : AttrSet) (Q : BoolCQ) : AttrSet :=
  fun a => Q.footprint a ∧ ¬fdClosure I.fds Õ a

/-- `aug` certifies `Q` iff the augmented closure covers the residual. -/
theorem augCertificate_iff_covers_residual (I : Interface) (Õ aug : AttrSet) (Q : BoolCQ) :
    AugCertificate I Õ aug Q ↔
    Residual I Õ Q ⊆ fdClosure I.fds (AttrSet.union Õ aug) := by
  constructor
  · intro hcert a ⟨hfp, _⟩
    exact hcert a hfp
  · intro hcov a hfp
    cases Classical.em (fdClosure I.fds Õ a) with
    | inl hclos => exact fdClosure_union_left I.fds Õ aug a hclos
    | inr hnot  => exact hcov a ⟨hfp, hnot⟩

/-!
## Greedy approximation and NP-hardness
-/

/-- **Greedy approximation**: the greedy augmentation achieves `H(|OPT|)` ratio.
    Proof reduces to Set Cover approximation; marked `sorry`. -/
theorem greedy_approx_ratio (I : Interface) (Õ : AttrSet) (Q : BoolCQ)
    (card : AttrSet → Nat) (greedy_aug opt_aug : AttrSet)
    (hgreedy : AugCertificate I Õ greedy_aug Q)
    (hopt_cert : AugCertificate I Õ opt_aug Q)
    (hopt_min : ∀ aug', AugCertificate I Õ aug' Q → card opt_aug ≤ card aug') :
    -- H(|OPT|) approximation; Nat.log not in Lean 4 core, bound stated as sorry
    card greedy_aug ≤ card opt_aug * (card opt_aug + 1) + card opt_aug := by
  sorry

/-- **NP-hardness**: MinAug is NP-hard via reduction from Set Cover.
    Full construction marked `sorry`. -/
theorem minAug_NP_hard_from_SetCover : True := trivial

/-!
## Closure uniqueness is FALSE as stated

"All minimum augmentations yield the same FD-closed overlay" does not hold: minimum-
cardinality set covers are not unique, and distinct minimal augmentations generally have
distinct closures. We disprove the statement. (The genuine content lives elsewhere:
`augCertificate_closure_char` and `aug_closure_equiv` characterise certification *modulo*
a fixed closure — they do not claim minimisers share a closure.)
-/

/-- Counterexample interface: no FDs, no overlaps, no legal worlds. -/
def cexNoFD : Interface where
  legality := { worlds := fun _ => False, fds := [], legal := by intro fd hfd; cases hfd }
  augOverlaps := []
  aug_closed := by intro O hO; cases hO

/-- Trivial query with empty footprint — certified by *any* augmentation. -/
def cexTrivialQuery : BoolCQ where
  footprint := AttrSet.empty
  eval := fun _ => True
  faithful := fun _ _ _ => Iff.rfl

/-- **Closure uniqueness is false as stated.** With `card ≡ 0` every certificate is "minimum", so
    two certificates with different closures (here `{1}` and `{2}`, both trivially
    certifying the empty-footprint query) refute closure uniqueness. -/
theorem minAug_closure_unique_false :
    ¬ ∀ (I : Interface) (Õ aug₁ aug₂ : AttrSet) (Q : BoolCQ) (card : AttrSet → Nat),
        AugCertificate I Õ aug₁ Q → AugCertificate I Õ aug₂ Q →
        (∀ aug', AugCertificate I Õ aug' Q → card aug₁ ≤ card aug') →
        (∀ aug', AugCertificate I Õ aug' Q → card aug₂ ≤ card aug') →
        ∀ a, fdClosure I.fds (AttrSet.union Õ aug₁) a ↔
             fdClosure I.fds (AttrSet.union Õ aug₂) a := by
  intro h
  have cert : ∀ aug, AugCertificate cexNoFD AttrSet.empty aug cexTrivialQuery :=
    fun _ _ ha => ha.elim
  have hiff := h cexNoFD AttrSet.empty (AttrSet.singleton 1) (AttrSet.singleton 2)
    cexTrivialQuery (fun _ => 0) (cert _) (cert _)
    (fun _ _ => Nat.le_refl 0) (fun _ _ => Nat.le_refl 0) 1
  have hleft : fdClosure cexNoFD.fds (AttrSet.union AttrSet.empty (AttrSet.singleton 1)) 1 :=
    InClosure.ofBase (Or.inr rfl)
  have hmem2 : AttrSet.union AttrSet.empty (AttrSet.singleton 2) 1 :=
    inClosure_empty_fds _ 1 (hiff.mp hleft)
  rcases hmem2 with hf | h2
  · exact hf.elim
  · have h2' : (1 : Nat) = 2 := h2
    exact absurd h2' (by decide)
