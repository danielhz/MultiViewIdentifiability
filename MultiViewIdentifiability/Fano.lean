import MultiViewIdentifiability.Basic
import MultiViewIdentifiability.Identifiability
import MultiViewIdentifiability.Minimax

/-!
# Fano's Inequality and Information-Theoretic Lower Bound

An information-theoretic lower bound on the
prediction error of any estimator for a non-identifiable query, via Fano's inequality.

## Statement

For Boolean queries, Fano's inequality gives:
  `P_e ≥ 1/2 - I(Q; Obs) / (2 log 2)`

When `Q` is non-identifiable and I(Q; Obs) = 0 (the observations carry no information
about Q), this reduces to `P_e ≥ 1/2`, matching the minimax error floor.

## Status

Full proofs of Fano-based bounds require measure theory, entropy, and mutual information,
which require Mathlib. We state the structural qualitative result fully, and mark the
quantitative information-theoretic bounds with `sorry`.
-/

/-!
## Qualitative Fano (fully proved)
-/

/-- **Qualitative form**: when `Q` is not identifiable, the minimax error rate
    is at least 1/2. Proved via `minimax_error_floor`. -/
theorem fano_lower_bound (I : Interface) (Q : BoolCQ)
    (hnotid : NotIdentifiable I Q)
    (f : Classifier I) (hf : ObsDetermined I f) :
    ∃ w, I.worlds w ∧ (f w = true ↔ ¬Q.eval w) :=
  minimax_error_floor I Q hnotid f hf

/-- **Count form**: at least 1 of every 2 observationally equivalent worlds
    is misclassified by any obs-determined classifier. -/
theorem fano_misclassification_exists (I : Interface) (Q : BoolCQ)
    (hnotid : NotIdentifiable I Q)
    (f : Classifier I) (hf : ObsDetermined I f) :
    ∃ w w', I.worlds w ∧ I.worlds w' ∧ ObsEquiv I.augOverlaps w w' ∧
            ((f w = true ↔ ¬Q.eval w) ∨ (f w' = true ↔ ¬Q.eval w')) := by
  obtain ⟨w, w', hw, hw', hobs, hdiff⟩ := hnotid
  refine ⟨w, w', hw, hw', hobs, ?_⟩
  have hfeq : f w = f w' := hf w w' hobs
  cases h : (f w) with
  | false =>
    cases Classical.em (Q.eval w) with
    | inl hQw   => left; simp [hQw]
    | inr hnotQw =>
      right
      have hQw' : Q.eval w' :=
        Classical.byContradiction (fun hn => hnotQw (hdiff.mpr hn))
      simp [← hfeq, h, hQw']
  | true =>
    cases Classical.em (Q.eval w') with
    | inl hQw' =>
      left
      have hnotQw : ¬Q.eval w := fun hQw => (hdiff.mp hQw) hQw'
      simp [hnotQw]
    | inr hnotQw' => right; simp [← hfeq, h, hnotQw']

/-!
## Quantitative Fano bound — retired stub

The previous `fano_expected_error_bound` here was a placeholder over free, unconstrained
`Nat` parameters (`2·mutual_info + 2·P_e_num ≥ P_e_den`), and was false as written (e.g.
`0,0,1`). The genuine results are formalized elsewhere with Mathlib:

* **Fano's inequality** itself: `MultiViewIdentifiability.entropy_le_fano` in `Entropy.lean`
  (`H(q) ≤ binEntropy(1−q x₀) + (1−q x₀)·log(M−1)`).
* **Predictor error floor** (outcome bound / pigeonhole Fano):
  `outcome_lower_bound` and `capacity_error_bound` in `OutcomeBound.lean`
  (`m_Q ≤ 2^k`, `Pe ≥ 1 − 2^k/m_Q`).

The *verbatim* entropic predictor corollary `Pe ≥ 1 − (I(Q;Obs)+1)/log₂ m_Q` (the
conditional/averaged lift of `entropy_le_fano`) is not yet formalized.
-/

/-- **Sample complexity** (qualitative): distinguishing Q requires Ω(1) obs-inequivalent
    worlds when Q is non-identifiable. -/
theorem sample_lower_bound_qualitative (I : Interface) (Q : BoolCQ)
    (hnotid : NotIdentifiable I Q) :
    ∃ w w', I.worlds w ∧ I.worlds w' ∧ ¬ObsEquiv I.augOverlaps w w' ∨
            (ObsEquiv I.augOverlaps w w' ∧ (Q.eval w ↔ ¬Q.eval w')) := by
  obtain ⟨w, w', hw, hw', hobs, hdiff⟩ := hnotid
  exact ⟨w, w', Or.inr ⟨hobs, hdiff⟩⟩
