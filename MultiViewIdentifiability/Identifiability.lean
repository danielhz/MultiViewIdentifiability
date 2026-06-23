import MultiViewIdentifiability.Basic
import MultiViewIdentifiability.FDClosure

/-!
# Query Identifiability

Identifiability of queries and its basic monotonicity properties.
-/

/-!
## Interface structure
-/

/-- An **interface**: a `LegalityStructure` plus augmented-overlap sets `Ω̃₁, …, Ω̃ₖ`. -/
structure Interface where
  legality    : LegalityStructure
  augOverlaps : List AttrSet
  aug_closed  : ∀ Õ ∈ augOverlaps, Õ ⊆ fdClosure legality.fds Õ

def Interface.worlds (I : Interface) : World → Prop := I.legality.worlds
def Interface.fds (I : Interface) : List FD := I.legality.fds

/-!
## Identifiability
-/

/-- `Q` is **identifiable** under `I`. -/
def Identifiable (I : Interface) (Q : BoolCQ) : Prop :=
  ∀ w w', I.worlds w → I.worlds w' →
    ObsEquiv I.augOverlaps w w' → (Q.eval w ↔ Q.eval w')

/-- `Q` is **not identifiable**: witness pair exists. -/
def NotIdentifiable (I : Interface) (Q : BoolCQ) : Prop :=
  ∃ w w', I.worlds w ∧ I.worlds w' ∧
    ObsEquiv I.augOverlaps w w' ∧ (Q.eval w ↔ ¬Q.eval w')

/-!
## Overlap-groundedness
-/

def OverlapGrounded (fds : List FD) (Õ : AttrSet) (Q : BoolCQ) : Prop :=
  Q.footprint ⊆ fdClosure fds Õ

def FullyGrounded (I : Interface) (Q : BoolCQ) : Prop :=
  ∃ Õ ∈ I.augOverlaps, OverlapGrounded I.fds Õ Q

/-!
## Monotonicity

Adding more overlaps makes more queries identifiable.
If Q is identifiable under I₁ (fewer overlaps) and I₁.augOverlaps ⊆ I₂.augOverlaps,
then Q is identifiable under I₂ (more overlaps).
-/

theorem identifiable_mono {I₁ I₂ : Interface} {Q : BoolCQ}
    (hL : I₁.legality = I₂.legality)
    (hfam : ∀ O ∈ I₁.augOverlaps, O ∈ I₂.augOverlaps)
    (hid : Identifiable I₁ Q) :
    Identifiable I₂ Q := by
  intro w w' hw hw' hobs₂
  apply hid w w'
  · -- I₁.worlds w: by hL, I₁.legality = I₂.legality so worlds are the same
    show I₁.legality.worlds w
    rw [hL]; exact hw
  · show I₁.legality.worlds w'
    rw [hL]; exact hw'
  · -- obs-equiv under I₂ (more overlaps) → under I₁ (fewer overlaps)
    intro O hO₁
    exact hobs₂ O (hfam O hO₁)

/-!
## Witness characterisation
-/

/-- Q is identifiable iff no witness pair (obs-equiv worlds disagreeing on Q) exists. -/
theorem identifiable_iff_no_witness (I : Interface) (Q : BoolCQ) :
    Identifiable I Q ↔
    ¬∃ w w', I.worlds w ∧ I.worlds w' ∧ ObsEquiv I.augOverlaps w w' ∧
             (Q.eval w ∧ ¬Q.eval w') := by
  constructor
  · intro hid ⟨w, w', hw, hw', hobs, hQw, hnotQw'⟩
    exact hnotQw' ((hid w w' hw hw' hobs).mp hQw)
  · intro hno w w' hw hw' hobs
    constructor
    · intro hQw
      exact Classical.byContradiction
        (fun hnotQw' => hno ⟨w, w', hw, hw', hobs, hQw, hnotQw'⟩)
    · intro hQw'
      exact Classical.byContradiction
        (fun hnotQw => hno ⟨w', w, hw', hw, ObsEquiv.symm hobs, hQw', hnotQw⟩)

/-!
## Helper
-/

/-- Observational equivalence gives a matching tuple in the other world. -/
theorem obsEquiv_agree_on {I : Interface} {w w' : World}
    (hobs : ObsEquiv I.augOverlaps w w')
    (Õ : AttrSet) (hÕ : Õ ∈ I.augOverlaps)
    (s : Tuple) (hs : w s) :
    ∃ t, w' t ∧ s.AgreeOn Õ t :=
  (hobs Õ hÕ).1 s hs
