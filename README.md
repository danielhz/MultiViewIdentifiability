# MultiViewIdentifiability

A Lean 4 formalization of **query identifiability under view-based observation**: when does
the answer to a Boolean conjunctive query depend only on what a family of *overlap* (view)
projections reveals about a relational world?

The development shows that identifiability coincides with **query determinacy** by the
overlap-projection views, that it admits a sound **closure certificate** based on functional
dependencies, and it derives information-theoretic and robustness consequences. All results
are machine-checked with no `sorry` except where explicitly noted in
[`COVERAGE.md`](COVERAGE.md).

## What is formalized

- **Closure certificate** (`certificate_sufficiency`): a query whose footprint lies in the
  FD-closure of a designated overlap is identifiable; with both directions of the
  Armstrong-entailment ⇔ closure-membership correspondence (`fdClosure_sound`,
  `fdClosure_complete`).
- **Determinacy correspondence** (`identifiable_iff_determined`): identifiability is exactly
  query determinacy (Nash–Segoufin–Vianu) by the overlap-projection views.
- **Minimax error floor** (`minimax_error_floor`): a non-identifiable query cannot be
  predicted better than chance (error ≥ 1/2).
- **Robust threshold** (`robust_threshold`): under an overlap-anchored loss measured by
  Jensen–Shannon divergence, a small loss already forces exact agreement on certified
  queries. Includes a finite-distribution KL / JS-divergence library and a Pinsker-type
  unique-mode lemma (`js_mode`).
- **Capacity / outcome bounds** (`outcome_lower_bound`, `capacity_error_bound`): a predictor
  with a `≤ 2^k`-state representation realises at most `2^k` query outcomes, and errs on at
  least `m_Q − 2^k` of them.
- **Fano's inequality** (`entropy_le_fano`), on a finite Shannon-entropy library.
- **Minimum augmentation** (`MinAug`): monotonicity and closure characterisations of the
  smallest interface augmentation that certifies a query.
- Several natural strengthenings are shown **false** with machine-checked counterexamples
  (`certificate_necessity_false`, `interface_visible_identifiable_false`,
  `minAug_closure_unique_false`).

See [`COVERAGE.md`](COVERAGE.md) for the full verification-status table, including what is
left open.

## Module layout

| Module | Contents |
|---|---|
| `MultiViewIdentifiability/Basic.lean` | Core types: attributes, tuples, worlds, FDs, legality, observation equivalence, Boolean CQs |
| `…/FDClosure.lean` | FD closure operator, determinacy, Armstrong correspondence |
| `…/Identifiability.lean` | Identifiability and monotonicity |
| `…/Certificate.lean` | The closure certificate |
| `…/Minimax.lean` | Minimax error floor |
| `…/InterfaceVisible.lean` | Single-overlap grounded queries |
| `…/MinAug.lean` | Minimum augmentation |
| `…/RobustThreshold.lean` | Robust threshold (statement + structural consequences) |
| `…/Information.lean` | Finite KL / Jensen–Shannon divergence, unique-mode lemma, robust threshold |
| `…/Entropy.lean` | Finite Shannon entropy, Fano's inequality |
| `…/OutcomeBound.lean` | Representation-capacity lower bounds |
| `…/Fano.lean` | Information-theoretic error floor |
| `…/Determinacy.lean` | Identifiability ⇔ query determinacy |

## Building

Requires [`elan`](https://github.com/leanprover/elan). The toolchain is pinned by
`lean-toolchain` (Lean `v4.30.0`) and dependencies by `lake-manifest.json`
([Mathlib](https://github.com/leanprover-community/mathlib4) `v4.30.0`).

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build
```

A successful build reports only the documented `sorry` and unused-variable linter warnings
listed in [`COVERAGE.md`](COVERAGE.md).

## Authors

- Ratan Bahadur Thapa
- Daniel Hernández

## Related

Companion experiment-code repository (independent companion project): https://github.com/danielhz/query-identifiability.

## License

Licensed under the [Apache License 2.0](LICENSE).
