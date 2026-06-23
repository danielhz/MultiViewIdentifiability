import Mathlib

/-!
# Outcome lower bound

*Outcome lower bound*: for an identifiable query `Q` with outcome
multiplicity `m_Q = |{Q(w) : w ∈ LegalWorlds}|`, any predictor that reads interface
evidence, stores it in a representation of size at most `2^k`, and answers `Q` correctly on
every legal world must satisfy `2^k ≥ m_Q` (equivalently `k ≥ log₂ m_Q`).

## Model

A predictor is modelled as a representation map `rep : W → R` into a finite representation
type `R` (the "≤ 2^k states"), followed by a decoder `ans : R → Y`. Correctness means the
composite recovers `Q` on every legal world: `ans (rep w) = Q w`. This is *more* general
than "reads interface evidence" (which would further require `rep` to factor
through observational equivalence); the lower bound holds for any correct predictor, so we
do not need that restriction. `W` (worlds), `Y` (answer values), and `R` (representation)
are arbitrary types; `m_Q` is `(Q '' legal).ncard`.

## Proof

`Q '' legal = (ans ∘ rep) '' legal ⊆ range ans`, and `range ans` has at most
`Fintype.card R ≤ 2^k` elements; cardinality monotonicity finishes.
-/

namespace MultiViewIdentifiability

/-- **Outcome lower bound.** Any predictor `rep`/`ans` whose representation
type `R` has at most `2^k` elements and which answers `Q` correctly on every legal world
realises at most `2^k` distinct outcomes: `m_Q ≤ 2^k`. -/
theorem outcome_lower_bound {W Y R : Type*} [Fintype R]
    (legal : Set W) (Q : W → Y) (rep : W → R) (ans : R → Y) (k : ℕ)
    (hcard : Fintype.card R ≤ 2 ^ k)
    (hcorrect : ∀ w ∈ legal, ans (rep w) = Q w) :
    (Q '' legal).ncard ≤ 2 ^ k := by
  -- The realised outcomes are a subset of the decoder's range.
  have hsub : Q '' legal ⊆ Set.range ans := by
    rintro y ⟨w, hw, rfl⟩
    exact ⟨rep w, hcorrect w hw⟩
  -- The decoder's range has at most `card R` elements.
  have hrange : (Set.range ans).ncard ≤ Fintype.card R := by
    rw [← Set.image_univ, ← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_image_le Set.finite_univ
  calc (Q '' legal).ncard
      ≤ (Set.range ans).ncard := Set.ncard_le_ncard hsub (Set.finite_range ans)
    _ ≤ Fintype.card R := hrange
    _ ≤ 2 ^ k := hcard

/-!
## Capacity error bound (approximate form)

The combinatorial sibling of `outcome_lower_bound`, for *approximate* prediction. `O` indexes
the `m_Q` distinct outcomes under the uniform prior over obs-equivalence classes (so
`trueAns` is injective and `Fintype.card O = m_Q`). A predictor `rep`/`ans` with a
representation of `≤ 2^k` states errs on at least `m_Q − 2^k` of them, hence
`Pe ≥ 1 − 2^k / m_Q`.

This is the deterministic-predictor pigeonhole bound. It is *stronger* than (and distinct
from) the entropic Fano bound `Pe ≥ 1 − (k+1)/log₂ m_Q`; that exact
information-theoretic statement is left to a future entropy/mutual-information development.
-/

/-- **Capacity error bound** (count form): with `trueAns` injective (`card O = m_Q`), any
`≤ 2^k`-state predictor errs on at least `m_Q − 2^k` outcomes. -/
theorem capacity_error_bound {O R Y : Type*} [Fintype O] [Fintype R] [DecidableEq Y]
    (trueAns : O → Y) (htrue : Function.Injective trueAns)
    (rep : O → R) (ans : R → Y) (k : ℕ) (hcard : Fintype.card R ≤ 2 ^ k) :
    (Fintype.card O : ℝ) - 2 ^ k
      ≤ ((Finset.univ.filter (fun o => ans (rep o) ≠ trueAns o)).card : ℝ) := by
  classical
  -- `rep` is injective on the correctly-classified set.
  have hinj : Set.InjOn rep (Finset.univ.filter (fun o => ans (rep o) = trueAns o)) := by
    intro o1 h1 o2 h2 he
    have e1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have e2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    exact htrue (by rw [← e1, ← e2, he])
  -- Hence at most `2^k` outcomes are classified correctly.
  have hcorrect_le :
      (Finset.univ.filter (fun o => ans (rep o) = trueAns o)).card ≤ 2 ^ k :=
    calc (Finset.univ.filter (fun o => ans (rep o) = trueAns o)).card
        = ((Finset.univ.filter (fun o => ans (rep o) = trueAns o)).image rep).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ Fintype.card R := by
          rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
      _ ≤ 2 ^ k := hcard
  -- Correct + wrong = all outcomes.
  have hsplit :
      (Finset.univ.filter (fun o => ans (rep o) = trueAns o)).card
      + (Finset.univ.filter (fun o => ans (rep o) ≠ trueAns o)).card = Fintype.card O := by
    rw [← Finset.card_univ (α := O)]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  have hcast :
      ((Finset.univ.filter (fun o => ans (rep o) = trueAns o)).card : ℝ)
      + ((Finset.univ.filter (fun o => ans (rep o) ≠ trueAns o)).card : ℝ)
      = (Fintype.card O : ℝ) := by exact_mod_cast hsplit
  have hle : ((Finset.univ.filter (fun o => ans (rep o) = trueAns o)).card : ℝ) ≤ 2 ^ k := by
    exact_mod_cast hcorrect_le
  linarith [hcast, hle]

/-- **Capacity error bound** (rate form): `Pe ≥ 1 − 2^k / m_Q`. -/
theorem capacity_error_rate {O R Y : Type*} [Fintype O] [Fintype R] [DecidableEq Y]
    (hO : 0 < Fintype.card O)
    (trueAns : O → Y) (htrue : Function.Injective trueAns)
    (rep : O → R) (ans : R → Y) (k : ℕ) (hcard : Fintype.card R ≤ 2 ^ k) :
    1 - (2 : ℝ) ^ k / Fintype.card O
      ≤ ((Finset.univ.filter (fun o => ans (rep o) ≠ trueAns o)).card : ℝ) / Fintype.card O := by
  have hb := capacity_error_bound trueAns htrue rep ans k hcard
  have hOpos : (0 : ℝ) < Fintype.card O := by exact_mod_cast hO
  have hne : (Fintype.card O : ℝ) ≠ 0 := ne_of_gt hOpos
  rw [show (1 : ℝ) - 2 ^ k / (Fintype.card O : ℝ)
        = ((Fintype.card O : ℝ) - 2 ^ k) / Fintype.card O from by field_simp]
  gcongr

end MultiViewIdentifiability
