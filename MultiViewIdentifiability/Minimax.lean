import MultiViewIdentifiability.Basic
import MultiViewIdentifiability.Identifiability

/-!
# Minimax Error Floor

When `Q` is not identifiable, any deterministic
observation-determined classifier has worst-case error ≥ 1/2.

## Proof sketch

Since `Q` is not identifiable, ∃ w, w' observationally equivalent with `Q(w) ≠ Q(w')`.
Any classifier that predicts True for the shared observation errs on w' (Q = False there),
and any classifier predicting False errs on w (Q = True there). In either case ≥ 1 of
the 2 worlds is misclassified.
-/

/-- A **classifier** for interface `I`: maps worlds to Boolean predictions. -/
abbrev Classifier (I : Interface) := World → Bool

/-- A classifier is **observation-determined** if it gives the same output to
    any two observationally equivalent worlds. -/
def ObsDetermined (I : Interface) (f : Classifier I) : Prop :=
  ∀ w w', ObsEquiv I.augOverlaps w w' → f w = f w'

/-!
## Minimax lower bound
-/

/-- **Minimax error floor**: if `Q` is not identifiable, then for every
    observation-determined classifier `f` there exists a legal world on which `f` errs. -/
theorem minimax_error_floor (I : Interface) (Q : BoolCQ)
    (hnotid : NotIdentifiable I Q)
    (f : Classifier I) (hf : ObsDetermined I f) :
    ∃ w, I.worlds w ∧ (f w = true ↔ ¬Q.eval w) := by
  obtain ⟨w, w', hw, hw', hobs, hdiff⟩ := hnotid
  -- hdiff : Q.eval w ↔ ¬Q.eval w'
  -- f w = f w' by observation-determinedness
  have hfeq : f w = f w' := hf w w' hobs
  cases h : (f w) with
  | false =>
    cases Classical.em (Q.eval w) with
    | inl hQw =>
      exact ⟨w, hw, by simp [h, hQw]⟩
    | inr hnotQw =>
      have hQw' : Q.eval w' :=
        Classical.byContradiction (fun hn => hnotQw (hdiff.mpr hn))
      exact ⟨w', hw', by simp [← hfeq, h, hQw']⟩
  | true =>
    cases Classical.em (Q.eval w') with
    | inl hQw' =>
      have hnotQw : ¬Q.eval w := fun hQw => (hdiff.mp hQw) hQw'
      exact ⟨w, hw, by simp [h, hnotQw]⟩
    | inr hnotQw' =>
      exact ⟨w', hw', by simp [← hfeq, h, hnotQw']⟩

/-- **Corollary**: no observation-determined classifier achieves perfect balanced accuracy
    on a witness pair. -/
theorem not_perfect_balanced_accuracy (I : Interface) (Q : BoolCQ)
    (hnotid : NotIdentifiable I Q)
    (f : Classifier I) (hf : ObsDetermined I f) :
    ¬∃ wt wf : World, I.worlds wt ∧ I.worlds wf ∧
        Q.eval wt ∧ ¬Q.eval wf ∧
        ObsEquiv I.augOverlaps wt wf ∧
        (f wt = true ∧ f wf = false) := by
  intro h
  obtain ⟨wt, wf, _, _, _, _, hobs, hft, hff⟩ := h
  have hfeq := hf wt wf hobs
  rw [hft] at hfeq
  simp at hfeq
  rw [hfeq] at hff
  simp at hff
