import MultiViewIdentifiability.Basic
import MultiViewIdentifiability.FDClosure
import MultiViewIdentifiability.Identifiability
import MultiViewIdentifiability.Certificate
import MultiViewIdentifiability.Minimax
import MultiViewIdentifiability.InterfaceVisible
import MultiViewIdentifiability.MinAug
import MultiViewIdentifiability.RobustThreshold
import MultiViewIdentifiability.Fano
import MultiViewIdentifiability.OutcomeBound
import MultiViewIdentifiability.Information
import MultiViewIdentifiability.Entropy
import MultiViewIdentifiability.Determinacy

/-!
# Multi-View Query Identifiability — a Lean 4 formalization

A self-contained Lean 4 development of **query identifiability under view-based
observation**: when does the answer to a Boolean conjunctive query depend only on what a
family of overlap (view) projections reveals about a relational world? Identifiability is
shown to coincide with **query determinacy** by the overlap-projection views; it admits a
sound polynomial **closure certificate**; and it has information-theoretic and robustness
consequences.

## Module structure

- `Basic`:            Core types — `Attr`, `Tuple`, `World`, `AttrSet`, `FD`,
                      `LegalityStructure`, `ObsEquiv`, `BoolCQ`.
- `FDClosure`:        The functional-dependency closure operator `X⁺_Σ`, its basic
                      properties, FD determinacy, and both directions of the
                      Armstrong-entailment ⇔ closure-membership correspondence.
- `Identifiability`:  The interface structure and identifiability, with monotonicity.
- `Certificate`:      The closure certificate — footprint ⊆ a closed overlap ⇒ identifiable.
- `Minimax`:          Non-identifiable queries have minimax error floor ≥ 1/2.
- `InterfaceVisible`: Single-overlap grounded queries are identifiable.
- `MinAug`:           The minimum-augmentation problem and its monotonicity / closure
                      characterisations.
- `RobustThreshold`:  Robustness — a small overlap loss already forces exact agreement on
                      certified queries, via Jensen–Shannon divergence.
- `Fano`:             Information-theoretic error lower bounds.
- `OutcomeBound`:     Representation-capacity lower bounds for predictors.
- `Information`:      Finite-distribution KL / Jensen–Shannon divergence and a Pinsker-type
                      unique-mode lemma.
- `Entropy`:          Finite Shannon entropy and Fano's inequality.
- `Determinacy`:      Identifiability is query determinacy by the overlap-projection views.

## What is proved (no `sorry`)

- All core definitions and the FD-closure machinery, including both directions of the
  Armstrong-entailment ⇔ closure-membership correspondence (`fdClosure_sound`,
  `fdClosure_complete`).
- `certificate_sufficiency`: footprint ⊆ a closed overlap ⇒ identifiable; with
  `footprint_lifting`, `hasCertificate_identifiable`.
- `minimax_error_floor`: the 1/2 error floor for non-identifiable queries.
- `footprint_in_overlap_identifiable`, `singleOverlap_identifiable`: single-overlap cases.
- `augCertificate_mono`, `augCertificate_closure_char`, `augCertificate_iff_covers_residual`,
  `aug_closure_equiv`, `augCertificate_identifiable_augmented` (identifiability under the
  augmented interface).
- `identifiable_iff_determined`: identifiability is exactly query determinacy by the
  overlap-projection views.
- `outcome_lower_bound`: a correct predictor with a `≤ 2^k`-state representation realises at
  most `2^k` query outcomes (`m_Q ≤ 2^k`); `capacity_error_bound` / `capacity_error_rate`:
  the approximate sibling `Pe ≥ 1 − 2^k/m_Q`.
- `robust_threshold`: under an overlap-anchored loss, a small loss forces agreement on
  certified queries — a full Jensen–Shannon-divergence proof, via `js_mode` (a Pinsker-type
  unique-mode bound), `kl_nonneg` (finite Gibbs' inequality), and `unique_majority`.
- `entropy_le_fano`: Fano's inequality `H(q) ≤ binEntropy(1−q x₀) + (1−q x₀)·log(M−1)`, on a
  finite Shannon-entropy library (`entropy`, `entropy_le_log_card`, `condEntropy_nonneg`,
  `binEntropy_eq_negMulLog`, `negMulLog_sum_le_total`).

## Disproofs (machine-checked counterexamples)

Three natural-looking strengthenings are in fact false; each is refuted with a checked
counterexample:
- `certificate_necessity_false`: the closure certificate is sufficient but not necessary
  (it fails for a degenerate single-world interface).
- `interface_visible_identifiable_false`: footprint ⊆ closure(⋃ overlaps) does *not* imply
  identifiability — observational equivalence gives only per-overlap agreement; the provable
  content is the single-overlap case (`singleOverlap_identifiable`).
- `minAug_closure_unique_false`: minimum augmentations are not closure-unique (minimum set
  covers are not unique).

## Open / not formalized

- `greedy_approx_ratio` (`MinAug`) is the one remaining `sorry`: the greedy Set-Cover `H_k`
  approximation bound, which would need a Set-Cover/greedy development (and the companion
  NP-hardness an `NP`-completeness framework) not available here.
- The conditional/averaged predictor form of the information-theoretic bound
  (`Pe ≥ 1 − (I+1)/log₂ m_Q`) is not formalized; its operational content (capacity ⇒ error
  floor) is `capacity_error_bound`, and Fano's inequality itself is `entropy_le_fano`.

See `COVERAGE.md` for the full verification-status table.
-/
