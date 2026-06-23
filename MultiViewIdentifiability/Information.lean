import Mathlib

/-!
# Finite-distribution information theory (for the robust threshold)

Self-contained Kullback–Leibler and Jensen–Shannon divergences over a finite type, with the
two facts the unique-mode lemma (`js_mode`) needs:

* `kl_nonneg` — Gibbs' inequality (finite form), via `Real.log_le_sub_one_of_pos`.
* `unique_majority` — a finite distribution has at most one outcome of mass `> 1/2`.

Divergences are in **nats** (natural log), i.e. `κ = 1`.
-/

namespace MultiViewIdentifiability

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Kullback–Leibler divergence of finite mass functions (nats). -/
noncomputable def KL (p q : α → ℝ) : ℝ := ∑ a, p a * Real.log (p a / q a)

/-- Pointwise mixture `(p + q)/2`. -/
noncomputable def mix (p q : α → ℝ) : α → ℝ := fun a => (p a + q a) / 2

/-- Jensen–Shannon divergence of finite mass functions (nats, `κ = 1`). -/
noncomputable def JSdiv (p q : α → ℝ) : ℝ := (KL p (mix p q) + KL q (mix p q)) / 2

open Classical in
/-- Point mass at `x`. -/
noncomputable def dirac (x : α) : α → ℝ := fun a => if a = x then 1 else 0

theorem dirac_nonneg (x : α) : ∀ a, 0 ≤ dirac x a := by
  intro a; unfold dirac; split <;> norm_num

theorem dirac_sum_one (x : α) : ∑ a, dirac x a = 1 := by
  have hsingle : ∑ a, dirac x a = dirac x x := by
    apply Finset.sum_eq_single
    · intro b _ hbx; unfold dirac; rw [if_neg hbx]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  rw [hsingle]; unfold dirac; rw [if_pos rfl]

theorem mix_nonneg {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a) :
    ∀ a, 0 ≤ mix p q a := by
  intro a; unfold mix; have := hp a; have := hq a; linarith

theorem mix_sum_one {p q : α → ℝ} (hsp : ∑ a, p a = 1) (hsq : ∑ a, q a = 1) :
    ∑ a, mix p q a = 1 := by
  unfold mix
  rw [← Finset.sum_div, Finset.sum_add_distrib, hsp, hsq]; norm_num

theorem mix_dirac_self (x : α) (p : α → ℝ) : mix (dirac x) p x = (1 + p x) / 2 := by
  unfold mix dirac; rw [if_pos rfl]

/-- **Gibbs' inequality** (finite form): KL divergence of two mass functions is nonnegative,
    assuming `q` is absolutely continuous w.r.t. `p` (`p a ≠ 0 → q a > 0`). -/
theorem kl_nonneg {p q : α → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hsp : ∑ a, p a = 1) (hsq : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → 0 < q a) :
    0 ≤ KL p q := by
  -- Term bound: `p a · log(q a / p a) ≤ q a − p a`.
  have hterm : ∀ a ∈ (Finset.univ : Finset α),
      p a * Real.log (q a / p a) ≤ q a - p a := by
    intro a _
    rcases (hp a).lt_or_eq with hpos | h0
    · have hqa : 0 < q a := hac a (ne_of_gt hpos)
      have hlog : Real.log (q a / p a) ≤ q a / p a - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hqa hpos)
      have h2 : p a * Real.log (q a / p a) ≤ p a * (q a / p a - 1) :=
        mul_le_mul_of_nonneg_left hlog (le_of_lt hpos)
      have h3 : p a * (q a / p a - 1) = q a - p a := by field_simp
      linarith [h2, h3.le, h3.ge]
    · rw [← h0]; simp only [zero_mul, sub_zero]; exact hq a
  have key : ∑ a, p a * Real.log (q a / p a) ≤ ∑ a, (q a - p a) :=
    Finset.sum_le_sum hterm
  have hrhs : ∑ a, (q a - p a) = 0 := by
    rw [Finset.sum_sub_distrib, hsq, hsp]; ring
  -- `KL p q = − ∑ p a · log(q a / p a)`.
  have hflip : KL p q = - ∑ a, p a * Real.log (q a / p a) := by
    rw [eq_neg_iff_add_eq_zero, KL, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro a _
    rcases (hp a).lt_or_eq with hpos | h0
    · have hqa : 0 < q a := hac a (ne_of_gt hpos)
      have hlogsum : Real.log (p a / q a) + Real.log (q a / p a) = 0 := by
        rw [Real.log_div (ne_of_gt hpos) (ne_of_gt hqa),
            Real.log_div (ne_of_gt hqa) (ne_of_gt hpos)]; ring
      rw [← mul_add, hlogsum, mul_zero]
    · rw [← h0]; ring
  rw [hflip]
  have key0 : ∑ a, p a * Real.log (q a / p a) ≤ 0 := le_trans key (le_of_eq hrhs)
  linarith [key0]

/-- A finite mass function has at most one outcome with mass strictly above `1/2`. -/
theorem unique_majority {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    {x x' : α} (hx : 1/2 < p x) (hx' : 1/2 < p x') : x = x' := by
  classical
  by_contra hne
  have hpair : p x + p x' ≤ ∑ a, p a := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hp i)
  rw [hsum] at hpair
  linarith

/-- Point-mass KL against the mixture: `KL(δ_x ‖ (δ_x+p)/2) = log(2/(1+p x))`. -/
theorem kl_dirac_mix (x : α) (p : α → ℝ) :
    KL (dirac x) (mix (dirac x) p) = Real.log (2 / (1 + p x)) := by
  have hsingle : ∑ a, dirac x a * Real.log (dirac x a / mix (dirac x) p a)
      = dirac x x * Real.log (dirac x x / mix (dirac x) p x) := by
    apply Finset.sum_eq_single
    · intro b _ hbx; unfold dirac; rw [if_neg hbx, zero_mul]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  rw [KL, hsingle, mix_dirac_self]
  unfold dirac
  rw [if_pos rfl, one_mul, one_div_div]

/-- JS lower bound at a point mass: `JS(δ_x ‖ p) ≥ ½ log(2/(1+p x))` for a mass function `p`. -/
theorem jsdiv_dirac_lower {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hsp : ∑ a, p a = 1) (x : α) :
    (1 / 2) * Real.log (2 / (1 + p x)) ≤ JSdiv (dirac x) p := by
  have h1 : KL (dirac x) (mix (dirac x) p) = Real.log (2 / (1 + p x)) := kl_dirac_mix x p
  have h2 : 0 ≤ KL p (mix (dirac x) p) := by
    refine kl_nonneg hp (mix_nonneg (dirac_nonneg x) hp) hsp
      (mix_sum_one (dirac_sum_one x) hsp) ?_
    intro a hpa
    have hpos : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm hpa)
    have hdx : 0 ≤ dirac x a := dirac_nonneg x a
    unfold mix; linarith
  rw [JSdiv, h1]; linarith [h2]

/-- If `JS(δ_x ‖ p) ≤ γ` with `γ < 1/8` (nats, `κ=1`), then `p x > 1/2`.
    Uses `e^{-t} ≥ 1 - t` to get `p x ≥ 1 - 4γ` without a tight numeric `exp` bound. -/
theorem px_gt_half {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hsp : ∑ a, p a = 1)
    (x : α) {γ : ℝ} (hγ : γ < 1/8) (hjs : JSdiv (dirac x) p ≤ γ) : 1/2 < p x := by
  have hpx : 0 ≤ p x := hp x
  have h1px : 0 < 1 + p x := by linarith
  have hzpos : 0 < 2 / (1 + p x) := by positivity
  have hlow := jsdiv_dirac_lower hp hsp x
  have hlog : Real.log (2 / (1 + p x)) ≤ 2 * γ := by linarith [hlow, hjs]
  have hexp : 2 / (1 + p x) ≤ Real.exp (2 * γ) := by
    have h := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log hzpos] at h
  have h2 : 2 ≤ Real.exp (2 * γ) * (1 + p x) := (div_le_iff₀ h1px).mp hexp
  have hEE : Real.exp (2 * γ) * Real.exp (-(2 * γ)) = 1 := by
    rw [← Real.exp_add, show 2 * γ + -(2 * γ) = 0 from by ring, Real.exp_zero]
  have hexpneg : 1 - 2 * γ ≤ Real.exp (-(2 * γ)) := by
    have := Real.add_one_le_exp (-(2 * γ)); linarith
  have h1pxlb : 2 * Real.exp (-(2 * γ)) ≤ 1 + p x := by
    have hF : (0 : ℝ) ≤ Real.exp (-(2 * γ)) := (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_left h2 hF
    calc 2 * Real.exp (-(2 * γ)) = Real.exp (-(2 * γ)) * 2 := by ring
      _ ≤ Real.exp (-(2 * γ)) * (Real.exp (2 * γ) * (1 + p x)) := hmul
      _ = 1 + p x := by
          rw [← mul_assoc, mul_comm (Real.exp (-(2 * γ))) (Real.exp (2 * γ)), hEE, one_mul]
  linarith [h1pxlb, hexpneg, hγ]

/-- **Unique-mode lemma**: if `δ_x` and `δ_{x'}` are both within JS-divergence `γ < 1/8` of the
    same mass function `p`, then `x = x'`. -/
theorem js_mode {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hsp : ∑ a, p a = 1)
    {x x' : α} {γ : ℝ} (hγ : γ < 1/8)
    (hx : JSdiv (dirac x) p ≤ γ) (hx' : JSdiv (dirac x') p ≤ γ) : x = x' :=
  unique_majority hp hsp (px_gt_half hp hsp x hγ hx) (px_gt_half hp hsp x' hγ hx')

/-- **Robust threshold.**

    `proj w` is the closure-augmented overlap projection `w|_{Õ}` (valued in a finite space
    `X`), `anchor` is the fixed anchor `p_O`, and `loss` is the overlap-anchored loss with
    `η · JS(δ_{proj w} ‖ anchor) ≤ loss w` (`η = η_O > 0`, JS in nats). Footprint coverage
    `footprint(Q) ⊆ closure(O)` is captured by `hfp` (equal projections ⇒ equal answer).
    Then for every `ε < η/8 = ε₀`, `Q` is `(ε,0)`-identifiable: any two worlds with loss
    `≤ ε` agree on `Q`. -/
theorem robust_threshold {W X Y : Type*} [Fintype X]
    (Q : W → Y) (proj : W → X) (anchor : X → ℝ)
    (hanc_nonneg : ∀ a, 0 ≤ anchor a) (hanc_sum : ∑ a, anchor a = 1)
    (loss : W → ℝ) (η : ℝ) (hη : 0 < η)
    (hanchor : ∀ w, η * JSdiv (dirac (proj w)) anchor ≤ loss w)
    (hfp : ∀ w w', proj w = proj w' → Q w = Q w')
    {ε : ℝ} (hε : ε < η / 8)
    {w w' : W} (hw : loss w ≤ ε) (hw' : loss w' ≤ ε) :
    Q w = Q w' := by
  have hjsw : JSdiv (dirac (proj w)) anchor ≤ ε / η := by
    rw [le_div_iff₀ hη, mul_comm]; linarith [hanchor w, hw]
  have hjsw' : JSdiv (dirac (proj w')) anchor ≤ ε / η := by
    rw [le_div_iff₀ hη, mul_comm]; linarith [hanchor w', hw']
  have hlt : ε / η < 1 / 8 := by rw [div_lt_iff₀ hη]; linarith [hε]
  exact hfp w w' (js_mode hanc_nonneg hanc_sum hlt hjsw hjsw')

end MultiViewIdentifiability
