import Mathlib
import MultiViewIdentifiability.Information

/-!
# Discrete Shannon entropy (toward the distributional Fano bound)

Increment 1 of the entropy/Fano build: Shannon entropy of a finite mass function (in nats,
using `Real.negMulLog`), with nonnegativity and the uniform value `H(uniform) = log (card α)`.

Working in nats keeps Mathlib's `negMulLog`/`log` API directly usable; the eventual Fano
bound `Pe ≥ 1 − (I + log 2)/log m_Q` (nats) is the *same inequality* as the
`1 − (I + 1)/log₂ m_Q` (bits), obtained by dividing through by `log 2`.
-/

namespace MultiViewIdentifiability

open scoped BigOperators

/-- Superadditivity of `negMulLog` (binary): `negMulLog(x+y) ≤ negMulLog x + negMulLog y`
    for `x, y ≥ 0`. Since `0 < x ≤ x+y`, `log` monotonicity gives
    `x log x + y log y ≤ (x+y) log(x+y)`. -/
theorem negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · rw [← hx0]; simp
  rcases eq_or_lt_of_le hy with hy0 | hypos
  · rw [← hy0]; simp
  have hlx : Real.log x ≤ Real.log (x + y) := Real.log_le_log hxpos (by linarith)
  have hly : Real.log y ≤ Real.log (x + y) := Real.log_le_log hypos (by linarith)
  have h1 : x * Real.log x ≤ x * Real.log (x + y) := mul_le_mul_of_nonneg_left hlx hx
  have h2 : y * Real.log y ≤ y * Real.log (x + y) := mul_le_mul_of_nonneg_left hly hy
  have hexp : (x + y) * Real.log (x + y)
      = x * Real.log (x + y) + y * Real.log (x + y) := by ring
  simp only [Real.negMulLog_eq_neg]
  linarith [h1, h2, hexp]

/-- `binEntropy p = negMulLog p + negMulLog (1 - p)`. -/
theorem binEntropy_eq_negMulLog (p : ℝ) :
    Real.binEntropy p = Real.negMulLog p + Real.negMulLog (1 - p) := by
  simp only [Real.binEntropy, Real.negMulLog, Real.log_inv]; ring

/-- **Max entropy with given total**: `∑ negMulLog(aᵢ) ≤ negMulLog(∑ aᵢ) + (∑ aᵢ)·log N`,
    `N = card`. By Jensen on the concave `negMulLog` with uniform weights. -/
theorem negMulLog_sum_le_total {β : Type*} (s : Finset β) (hs : s.Nonempty) (a : β → ℝ)
    (ha : ∀ b ∈ s, 0 ≤ a b) :
    ∑ b ∈ s, Real.negMulLog (a b)
      ≤ Real.negMulLog (∑ b ∈ s, a b) + (∑ b ∈ s, a b) * Real.log s.card := by
  have hN : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hjen := Real.concaveOn_negMulLog.le_map_sum (t := s) (w := fun _ => 1 / (s.card : ℝ))
    (p := a) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp) (fun i hi => ha i hi)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hjen
  have hmul := mul_le_mul_of_nonneg_left hjen hN.le
  rw [← mul_assoc, mul_one_div, div_self (ne_of_gt hN), one_mul] at hmul
  refine hmul.trans (le_of_eq ?_)
  rcases eq_or_lt_of_le (Finset.sum_nonneg ha) with hS0 | hSpos
  · rw [← hS0]; simp
  · rw [Real.negMulLog, Real.log_mul (by positivity) (ne_of_gt hSpos), one_div, Real.log_inv,
        Real.negMulLog]
    field_simp
    ring

/-- Superadditivity of `negMulLog` over a finite sum. -/
theorem negMulLog_sum_le {β : Type*} (s : Finset β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    Real.negMulLog (∑ b ∈ s, f b) ≤ ∑ b ∈ s, Real.negMulLog (f b) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro b t hbt ih
    rw [Finset.sum_insert hbt, Finset.sum_insert hbt]
    have hfs : 0 ≤ ∑ x ∈ t, f x := Finset.sum_nonneg (fun x _ => hf x)
    calc Real.negMulLog (f b + ∑ x ∈ t, f x)
        ≤ Real.negMulLog (f b) + Real.negMulLog (∑ x ∈ t, f x) := negMulLog_add_le (hf b) hfs
      _ ≤ Real.negMulLog (f b) + ∑ x ∈ t, Real.negMulLog (f x) := by linarith [ih]

variable {α : Type*} [Fintype α]

/-- Shannon entropy of a finite mass function (nats): `H(p) = ∑ −p(a) log p(a)`. -/
noncomputable def entropy (p : α → ℝ) : ℝ := ∑ a, Real.negMulLog (p a)

/-- Entropy of a mass function is nonnegative. -/
theorem entropy_nonneg {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1) :
    0 ≤ entropy p :=
  Finset.sum_nonneg (fun a _ => Real.negMulLog_nonneg (hp a) (hp1 a))

/-- Entropy of the uniform distribution on a nonempty finite type is `log (card α)`. -/
theorem entropy_uniform [Nonempty α] :
    entropy (fun _ : α => (1 : ℝ) / Fintype.card α) = Real.log (Fintype.card α) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [entropy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.negMulLog,
      one_div, Real.log_inv]
  field_simp

/-- **Maximum entropy**: `H(p) ≤ log (card α)`. Proved from `0 ≤ KL(p ‖ uniform)`
    (reusing `kl_nonneg`), since `KL(p ‖ uniform) = log (card α) − H(p)`. -/
theorem entropy_le_log_card [Nonempty α] {p : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hsp : ∑ a, p a = 1) :
    entropy p ≤ Real.log (Fintype.card α) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hnpos : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have huni_nonneg : ∀ _a : α, (0 : ℝ) ≤ 1 / Fintype.card α := fun _ => by positivity
  have huni_sum : ∑ _a : α, (1 : ℝ) / Fintype.card α = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have hac : ∀ a, p a ≠ 0 → (0 : ℝ) < 1 / Fintype.card α := fun _ _ => by positivity
  have hkl : 0 ≤ KL p (fun _ => 1 / Fintype.card α) :=
    kl_nonneg hp huni_nonneg hsp huni_sum hac
  have hterm : ∀ a, p a * Real.log (p a / (1 / Fintype.card α))
      = p a * Real.log (p a) + p a * Real.log (Fintype.card α) := by
    intro a
    rcases eq_or_lt_of_le (hp a) with h0 | hpos
    · rw [← h0]; ring
    · have h1 : p a / (1 / (Fintype.card α : ℝ)) = p a * (Fintype.card α : ℝ) := by
        field_simp
      rw [h1, Real.log_mul (ne_of_gt hpos) hn, mul_add]
  have hKLeq : KL p (fun _ => 1 / Fintype.card α)
      = (∑ a, p a * Real.log (p a)) + Real.log (Fintype.card α) := by
    rw [KL, Finset.sum_congr rfl (fun a _ => hterm a), Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_mul, hsp, one_mul]
  have hent : entropy p + ∑ a, p a * Real.log (p a) = 0 := by
    rw [entropy, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun a _ => by rw [Real.negMulLog]; ring)
  linarith [hkl, hKLeq, hent]

/-- **Fano's inequality** (single-distribution form): for a mass function `q` with a
    distinguished outcome `x₀`, writing `p = 1 − q x₀` for the "error" mass,
    `H(q) ≤ binEntropy p + p · log(M − 1)`. -/
theorem entropy_le_fano [Nonempty α] {q : α → ℝ} (hq : ∀ a, 0 ≤ q a) (hsq : ∑ a, q a = 1)
    (x0 : α) :
    entropy q ≤ Real.binEntropy (1 - q x0)
      + (1 - q x0) * Real.log ((Fintype.card α : ℝ) - 1) := by
  classical
  have hsplit : entropy q
      = Real.negMulLog (q x0) + ∑ a ∈ Finset.univ.erase x0, Real.negMulLog (q a) := by
    rw [entropy, ← Finset.add_sum_erase _ _ (Finset.mem_univ x0)]
  have hsum_erase : ∑ a ∈ Finset.univ.erase x0, q a = 1 - q x0 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ x0), hsq]
  rcases (Finset.univ.erase x0).eq_empty_or_nonempty with hempty | hne
  · rw [hsplit, hempty, Finset.sum_empty, add_zero]
    have hqx0 : q x0 = 1 := by
      have h := hsum_erase; rw [hempty, Finset.sum_empty] at h; linarith
    rw [hqx0]; simp [Real.negMulLog_one, Real.binEntropy_zero]
  · have hbound := negMulLog_sum_le_total (Finset.univ.erase x0) hne q (fun b _ => hq b)
    rw [hsum_erase, Finset.card_erase_of_mem (Finset.mem_univ x0), Finset.card_univ,
        Nat.cast_sub Fintype.card_pos, Nat.cast_one] at hbound
    rw [hsplit, binEntropy_eq_negMulLog, show (1 : ℝ) - (1 - q x0) = q x0 from by ring]
    linarith [hbound]

/-!
## Joint distributions, conditional entropy, mutual information

Definitions for the Fano build (proofs of nonnegativity etc. come in the next increment).
-/

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `X`-marginal of a joint mass function on `X × Y`. -/
noncomputable def marginalX (j : X × Y → ℝ) : X → ℝ := fun a => ∑ b, j (a, b)

/-- `Y`-marginal of a joint mass function on `X × Y`. -/
noncomputable def marginalY (j : X × Y → ℝ) : Y → ℝ := fun b => ∑ a, j (a, b)

/-- Mutual information `I(X;Y) = H(X) + H(Y) − H(X,Y)`. -/
noncomputable def mutualInfo (j : X × Y → ℝ) : ℝ :=
  entropy (marginalX j) + entropy (marginalY j) - entropy j

/-- Conditional entropy `H(Y|X) = H(X,Y) − H(X)`. -/
noncomputable def condEntropy (j : X × Y → ℝ) : ℝ := entropy j - entropy (marginalX j)

/-- **Joint entropy dominates the marginal**: `H(X) ≤ H(X,Y)` (conditioning the other way,
    `H(X,Y) ≥ H(marginalX)`). Proof: per row `a`, `negMulLog(∑_b j(a,b)) ≤ ∑_b negMulLog(j(a,b))`
    by superadditivity. -/
theorem entropy_marginalX_le (j : X × Y → ℝ) (hj : ∀ ab, 0 ≤ j ab) :
    entropy (marginalX j) ≤ entropy j := by
  rw [entropy, entropy, Fintype.sum_prod_type]
  refine Finset.sum_le_sum (fun a _ => ?_)
  simp only [marginalX]
  exact negMulLog_sum_le Finset.univ (fun b => j (a, b)) (fun b => hj (a, b))

/-- **Conditional entropy is nonnegative**: `0 ≤ H(Y|X)`. -/
theorem condEntropy_nonneg (j : X × Y → ℝ) (hj : ∀ ab, 0 ≤ j ab) : 0 ≤ condEntropy j := by
  rw [condEntropy]; linarith [entropy_marginalX_le j hj]

end MultiViewIdentifiability
