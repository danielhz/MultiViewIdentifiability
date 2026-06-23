import MultiViewIdentifiability.Basic
import MultiViewIdentifiability.Identifiability

/-!
# Robust Threshold Identifiability

Under distributional assumptions, a query `Q` becomes
identifiable iff the Jensen–Shannon divergence between the conditional distributions exceeds
a threshold `τ`.

This theorem connects structural (set-theoretic) identifiability to statistical separability.
The full proof requires real analysis and information theory (Jensen–Shannon divergence,
KL divergence, real-valued probability measures). We state the theorem formally and provide
the purely structural consequence that can be proved without real numbers.
-/

/-!
## Structural consequences (fully proved)
-/

/-- If `Q` is identifiable, then for any two legal observationally equivalent worlds,
    the conditional Q-answer must agree. (Restatement of identifiability definition.) -/
theorem identifiable_implies_consistent (I : Interface) (Q : BoolCQ)
    (hid : Identifiable I Q)
    (w w' : World) (hw : I.worlds w) (hw' : I.worlds w')
    (hobs : ObsEquiv I.augOverlaps w w') :
    Q.eval w ↔ Q.eval w' :=
  hid w w' hw hw' hobs

/-- Contrapositive: a separating pair (obs-equiv worlds with Q(w) ≠ Q(w')) proves
    non-identifiability. -/
theorem separation_implies_not_identifiable (I : Interface) (Q : BoolCQ)
    (w w' : World) (hw : I.worlds w) (hw' : I.worlds w')
    (hobs : ObsEquiv I.augOverlaps w w')
    (hdiff : Q.eval w ↔ ¬Q.eval w') :
    ¬Identifiable I Q := by
  intro hid
  have heq := hid w w' hw hw' hobs
  cases Classical.em (Q.eval w) with
  | inl hQw   => exact (hdiff.mp hQw) (heq.mp hQw)
  | inr hnotQw =>
    have hnotQw' : ¬Q.eval w' := fun hQw' => hnotQw (heq.mpr hQw')
    exact hnotQw (hdiff.mpr hnotQw')

/-!
## Robust threshold — now fully proved with Mathlib

The earlier `sorry` here was a placeholder with a `jsDiv ≡ 0` stub, which made its statement
false. The robust threshold is proved with genuine Jensen–Shannon divergence in
`MultiViewIdentifiability.Information` as `MultiViewIdentifiability.robust_threshold`
(via `js_mode`, the Pinsker-type unique-mode lemma). It states: under the overlap-anchored loss
`η · JS(δ_{w|Õ} ‖ p_O) ≤ ℓ(w)` and footprint coverage `footprint(Q) ⊆ closure(O)`, every
`ε < η/8` makes `Q` `(ε,0)`-identifiable. See `Information.lean`.
-/
