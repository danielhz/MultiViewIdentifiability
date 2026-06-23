import MultiViewIdentifiability.Basic

/-!
# Functional-Dependency Closure

Formalizes the FD closure operator `X⁺_Σ` and proves the key properties used
throughout this development.

## Definition

`a ∈ fd_closure Σ X` iff `a` is derivable from `X` using `Σ` via the Armstrong
inference rules (reflexivity + transitivity), encoded by the inductive predicate
`InClosure`.

This is equivalent to "the smallest `Y ⊇ X` closed under applying every FD in Σ"
(the correspondence with Armstrong entailment is established below).
-/

/-!
## Inductive closure predicate
-/

/-- `InClosure Σ base a` holds iff `a` is derivable from `base` using FDs in `Σ`.

    Written `a ∈ base⁺_Σ` in the standard notation.

    Two rules:
    - `ofBase`:  every attribute in `base` is in the closure.
    - `ofFD`:    if all LHS attributes of some FD are in the closure, the RHS is too. -/
inductive InClosure (fds : List FD) (base : AttrSet) : Attr → Prop where
  | ofBase {a}  : base a → InClosure fds base a
  | ofFD  {fd}  : fd ∈ fds
                → (∀ b, fd.lhs b → InClosure fds base b)
                → InClosure fds base fd.rhs

/-- The **FD closure** of `base` under `fds` as an attribute set predicate. -/
def fdClosure (fds : List FD) (base : AttrSet) : AttrSet :=
  InClosure fds base

/-!
## Basic properties of the closure operator
-/

section FDClosureProps
variable (fds : List FD)

/-- **Extensivity**: `base ⊆ fdClosure fds base` (every base attribute is in the closure). -/
theorem fdClosure_extensive (base : AttrSet) : base ⊆ fdClosure fds base :=
  fun a ha => InClosure.ofBase ha

/-- **Monotonicity**: if `base₁ ⊆ base₂` then `fdClosure fds base₁ ⊆ fdClosure fds base₂`. -/
theorem fdClosure_mono {base₁ base₂ : AttrSet} (h : base₁ ⊆ base₂) :
    fdClosure fds base₁ ⊆ fdClosure fds base₂ := by
  intro _ ha
  induction ha with
  | ofBase hb  => exact InClosure.ofBase (h _ hb)
  | ofFD hmem _ ih => exact InClosure.ofFD hmem ih

/-- **Idempotency** (≤ direction): `fdClosure fds (fdClosure fds base) ⊆ fdClosure fds base`. -/
theorem fdClosure_idem_le (base : AttrSet) :
    fdClosure fds (fdClosure fds base) ⊆ fdClosure fds base := by
  intro _ ha
  induction ha with
  | ofBase hb  => exact hb
  | ofFD hmem _ ih => exact InClosure.ofFD hmem ih

/-- **Idempotency** (≥ direction): `fdClosure fds base ⊆ fdClosure fds (fdClosure fds base)`. -/
theorem fdClosure_idem_ge (base : AttrSet) :
    fdClosure fds base ⊆ fdClosure fds (fdClosure fds base) :=
  fdClosure_mono fds (fdClosure_extensive fds base)

/-- Union-monotonicity: `fdClosure fds (S ∪ T) ⊇ fdClosure fds S`. -/
theorem fdClosure_union_left (S T : AttrSet) :
    fdClosure fds S ⊆ fdClosure fds (AttrSet.union S T) :=
  fdClosure_mono fds (fun _ ha => Or.inl ha)

theorem fdClosure_union_right (S T : AttrSet) :
    fdClosure fds T ⊆ fdClosure fds (AttrSet.union S T) :=
  fdClosure_mono fds (fun _ ha => Or.inr ha)

end FDClosureProps

/-!
## FD determinacy

The core lemma: if `Σ` holds on `W` (cross-world), then for any two tuples from
legal worlds, agreement on `X` implies agreement on `X⁺_Σ`.
-/

/-- **FD determinacy**: under cross-world legality, agreement on `X` propagates
    to agreement on the entire closure `X⁺_Σ`.

    Proof: by induction on the `InClosure` derivation.
    - Base case: `a ∈ X`, so `s a = t a` by hypothesis.
    - FD case: all LHS attributes of `fd` are determined by induction hypothesis;
      the RHS is determined by the cross-world FD condition. -/
theorem fd_determinacy (L : LegalityStructure) (w w' : World)
    (hw : L.worlds w) (hw' : L.worlds w')
    (X : AttrSet) (s t : Tuple) (hs : w s) (ht : w' t)
    (hXagree : s.AgreeOn X t) :
    s.AgreeOn (fdClosure L.fds X) t := by
  intro _ ha
  induction ha with
  | ofBase hb  => exact hXagree _ hb
  | ofFD hmem _ ih =>
      apply L.legal _ hmem w w' hw hw' s t hs ht
      exact fun b hlhs => ih b hlhs

/-- Agreement on `X` implies agreement on `X⁺_Σ`. -/
theorem fdClosure_propagates_agreement (L : LegalityStructure) (w w' : World)
    (hw : L.worlds w) (hw' : L.worlds w')
    (X : AttrSet) (s t : Tuple) (hs : w s) (ht : w' t)
    (hXagree : s.AgreeOn X t) :
    s.AgreeOn (fdClosure L.fds X) t :=
  fd_determinacy L w w' hw hw' X s t hs ht hXagree

/-- Agreement on overlap `O` implies agreement on `O⁺_Σ`. -/
theorem fdClosure_propagates_from_overlap (L : LegalityStructure) (w w' : World)
    (hw : L.worlds w) (hw' : L.worlds w')
    (O : AttrSet) (s t : Tuple) (hs : w s) (ht : w' t)
    (hOagree : s.AgreeOn O t) :
    s.AgreeOn (fdClosure L.fds O) t :=
  fd_determinacy L w w' hw hw' O s t hs ht hOagree

/-!
## Closure characterization (Armstrong entailment)

`Y ⊆ X⁺_Σ` iff `Σ ⊨ X → Y` under Armstrong entailment.
We formalize "Σ ⊨ X → Y" as: for any cross-world legality structure satisfying Σ,
any two tuples agreeing on X also agree on Y.

This is provable in both directions using the inductive closure definition.
-/

/-- **Closure soundness**: if `Y ⊆ X⁺_Σ`, then `Σ ⊨ X → Y`
    (agreement on X propagates to Y under any satisfying structure). -/
theorem fdClosure_sound (fds : List FD) (X Y : AttrSet) (hYinX : Y ⊆ fdClosure fds X)
    (L : LegalityStructure) (hfds : L.fds = fds)
    (w w' : World) (hw : L.worlds w) (hw' : L.worlds w')
    (s t : Tuple) (hs : w s) (ht : w' t) (hXagree : s.AgreeOn X t) :
    s.AgreeOn Y t := by
  intro a ha
  have hdet := fd_determinacy L w w' hw hw' X s t hs ht hXagree a
  rw [hfds] at hdet
  exact hdet (hYinX a ha)

/-!
### Canonical separating structure (for completeness)

The completeness direction is proved by the standard *chase* construction. The canonical
world contains two tuples: the all-zero tuple `zeroTuple`, and `sepTuple`, which is `0`
exactly on the closure `X⁺_Σ` and `1` elsewhere. These agree on `X` (indeed on all of
`X⁺_Σ`) and satisfy every FD cross-world, but they disagree on any attribute outside the
closure — which contradicts entailment whenever `a ∉ X⁺_Σ`.
-/

/-- The all-zero tuple. (`abbrev` so `zeroTuple u` reduces to `0` for `rfl`.) -/
abbrev zeroTuple : Tuple := fun _ => 0

open Classical in
/-- The canonical separating tuple: value `0` on `X⁺_Σ`, value `1` off it. -/
noncomputable def sepTuple (fds : List FD) (X : AttrSet) : Tuple :=
  fun u => if InClosure fds X u then 0 else 1

theorem sepTuple_closure {fds : List FD} {X : AttrSet} {u : Attr}
    (h : InClosure fds X u) : sepTuple fds X u = 0 := by
  simp only [sepTuple, if_pos h]

theorem sepTuple_eq_zero {fds : List FD} {X : AttrSet} {u : Attr}
    (h : sepTuple fds X u = 0) : InClosure fds X u := by
  cases Classical.em (InClosure fds X u) with
  | inl hc => exact hc
  | inr hc =>
    have h1 : sepTuple fds X u = 1 := by simp only [sepTuple, if_neg hc]
    rw [h1] at h
    exact absurd h (by decide)

/-- The canonical world: the all-zero tuple together with `sepTuple`. -/
noncomputable def canonWorld (fds : List FD) (X : AttrSet) : World :=
  fun u => u = zeroTuple ∨ u = sepTuple fds X

/-- The canonical legality structure: a single legal world (`canonWorld`) under `fds`.
    The cross-world FDs hold because any LHS-agreement between the two tuples forces all
    LHS attributes into the closure, hence the RHS into the closure too. -/
noncomputable def canonStruct (fds : List FD) (X : AttrSet) : LegalityStructure where
  worlds := fun w => w = canonWorld fds X
  fds := fds
  legal := by
    intro fd hfd w w' hw hw'
    have hw2 : w = canonWorld fds X := hw
    have hw2' : w' = canonWorld fds X := hw'
    subst hw2; subst hw2'
    intro p q hp hq hpq
    simp only [canonWorld] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · rfl
    · have hlhs : ∀ b, fd.lhs b → InClosure fds X b := by
        intro b hb
        have hb0 : sepTuple fds X b = 0 := (hpq b hb).symm
        exact sepTuple_eq_zero hb0
      rw [sepTuple_closure (InClosure.ofFD hfd hlhs)]
    · have hlhs : ∀ b, fd.lhs b → InClosure fds X b := by
        intro b hb
        have hb0 : sepTuple fds X b = 0 := hpq b hb
        exact sepTuple_eq_zero hb0
      rw [sepTuple_closure (InClosure.ofFD hfd hlhs)]
    · rfl

/-- **Closure completeness**: `a ∈ X⁺_Σ` iff `Σ ⊨ X → {a}`.
    The "only if" direction: if `Σ ⊨ X → {a}` in every structure, then `a ∈ X⁺_Σ`.
    Proved via the canonical separating structure `canonStruct`. -/
theorem fdClosure_complete (fds : List FD) (X : AttrSet) (a : Attr)
    (hEntail : ∀ (L : LegalityStructure), L.fds = fds →
               ∀ w w' : World, L.worlds w → L.worlds w' →
               ∀ s t, w s → w' t → s.AgreeOn X t → s a = t a) :
    fdClosure fds X a := by
  apply Classical.byContradiction
  intro hna
  have hna' : ¬ InClosure fds X a := hna
  -- The two canonical tuples agree on X (every X-attribute is in the closure).
  have hagree : zeroTuple.AgreeOn X (sepTuple fds X) := by
    intro u hu
    rw [sepTuple_closure (InClosure.ofBase hu)]
  -- Entailment forces them to agree on a as well.
  have key : zeroTuple a = sepTuple fds X a :=
    hEntail (canonStruct fds X) rfl (canonWorld fds X) (canonWorld fds X)
      rfl rfl zeroTuple (sepTuple fds X) (Or.inl rfl) (Or.inr rfl) hagree
  -- But sepTuple a = 1 ≠ 0 = zeroTuple a, since a ∉ X⁺_Σ.
  have hsa : sepTuple fds X a = 1 := by simp only [sepTuple, if_neg hna']
  rw [hsa] at key
  have key0 : (0 : Val) = 1 := key
  exact absurd key0 (by decide)
