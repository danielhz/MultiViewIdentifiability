# Verification status

Which results in this development are machine-checked, verified against a green `lake build`
(Lean 4.30.0 + Mathlib v4.30.0). "Proved" means the declaration compiles with no `sorry`.

| Result | Lean declaration(s) | Status |
|---|---|---|
| Closure certificate | `certificate_sufficiency` (`Certificate.lean`) | **Proved.** Sufficient condition for identifiability. Its converse (`Identifiable → FullyGrounded`) is **false**, disproved by `certificate_necessity_false`. |
| Atom-wise closure certificate | `atomwise_certificate`, `cq_footprint`, `AtomCQ` (`AtomCertificate.lean`) | **Proved** (no axioms). A conjunctive query each of whose relation atoms has its schema inside a single overlap's FD-closure is identifiable. Refines the closure certificate: covering attributes *separately* across overlaps is insufficient; the single-overlap case is one atom. |
| Determinacy correspondence | `identifiable_iff_determined` (`Determinacy.lean`) | **Proved.** Identifiability equals query determinacy by the overlap-projection views. |
| Interface-visible fragment | `iv_identifiable`, `IVQuery` (`Determinacy.lean`) | **Proved.** Any query whose answer is determined by the observable-schema projections (a query over the interface-visible vocabulary) is identifiable — needs no legality assumption, and permits joins over the observable relations. |
| Single-overlap identifiability | `footprint_in_overlap_identifiable`, `singleOverlap_identifiable` (`InterfaceVisible.lean`) | **Proved.** The footprint-over-**union** generalization is **false** (`union_footprint_coverage_insufficient`). |
| FD closure / Armstrong | `fd_determinacy`, `fdClosure_sound`, `fdClosure_complete` (`FDClosure.lean`) | **Proved.** Both directions of the Armstrong-entailment ⇔ closure-membership correspondence. |
| Multi-grounded sufficiency | `fully_grounded_identifiable`, `hasCertificate_identifiable` (`Certificate.lean`) | **Proved.** |
| Minimax error floor | `minimax_error_floor`, `not_perfect_balanced_accuracy` (`Minimax.lean`) | **Proved.** Error ≥ 1/2 for non-identifiable queries. |
| Robust threshold | `robust_threshold` (`Information.lean`) | **Proved.** Full Jensen–Shannon-divergence proof: a small overlap-anchored loss forces exact agreement on certified queries. Built on `js_mode` (Pinsker-type unique-mode lemma), `kl_nonneg` (finite Gibbs' inequality), `unique_majority`. |
| Outcome / capacity bounds | `outcome_lower_bound`, `capacity_error_bound`, `capacity_error_rate` (`OutcomeBound.lean`) | **Proved.** A `≤ 2^k`-state predictor realises ≤ `2^k` outcomes (`m_Q ≤ 2^k`) and errs on ≥ `m_Q − 2^k` of them (`Pe ≥ 1 − 2^k/m_Q`). Qualitative floor `fano_lower_bound` also proved. |
| Fano's inequality | `entropy_le_fano` (`Entropy.lean`) | **Proved.** `H(q) ≤ binEntropy(1−q x₀) + (1−q x₀)·log(M−1)`, on a finite Shannon-entropy library (`entropy`, `entropy_le_log_card`, `condEntropy_nonneg`, `negMulLog` superadditivity, Jensen). |
| MinAug structure | `augCertificate_mono`, `augCertificate_closure_char`, `augCertificate_iff_covers_residual`, `aug_closure_equiv`, `augCertificate_identifiable_augmented` (`MinAug.lean`) | **Proved.** Two earlier overclaims were **false**: `augCertificate_identifiable` (now the augmented-interface form) and closure-uniqueness (disproved by `minAug_closure_unique_false`). |

## Open / not formalized

- **MinAug greedy approximation + NP-hardness** (`greedy_approx_ratio`, the one remaining
  `sorry`; `minAug_NP_hard_from_SetCover`, a `True := trivial` placeholder): the greedy
  `H_k` Set-Cover approximation bound would need a Set-Cover/greedy development, and the
  NP-hardness an `NP`-completeness framework — neither is available here.
- **Distributional / averaged information-theoretic bound** `Pe ≥ 1 − (I+1)/log₂ m_Q`: not
  formalized. Its operational content (capacity ⇒ error floor) is `capacity_error_bound`,
  and Fano's inequality itself is `entropy_le_fano`.
- **General view-vocabulary identifiability** (queries written over the per-overlap view
  predicates, beyond single-overlap footprint coverage): not formalized.

## Reproducing

```sh
lake exe cache get
lake build
```

Lean `4.30.0` via `elan` (pinned by `lean-toolchain`); Mathlib `v4.30.0` (pinned by
`lake-manifest.json`). A successful build reports only the one documented `sorry`
(`greedy_approx_ratio`) and unused-variable linter warnings.
