import MultiViewIdentifiability.Basic
import MultiViewIdentifiability.FDClosure
import MultiViewIdentifiability.Identifiability

/-!
# Identifiability Certificate

The closure certificate for identifiability, with the footprint-lifting lemma.

## Certification sufficiency

If the query's footprint `S = Q.footprint` is contained in `fdClosure Σ Ω̃ⱼ` for some
augmented-overlap `Ω̃ⱼ`, then `Q` is identifiable under the interface `I`.

## Proof sketch

Given two legal worlds `w, w'` with `w.AgreeOn Ω̃ⱼ w'`:
1. Take any `s ∈ w`; by observational equivalence on `Ω̃ⱼ`, get `t ∈ w'` with `s.AgreeOn Ω̃ⱼ t`.
2. By FD determinacy, `s.AgreeOn (fdClosure Σ Ω̃ⱼ) t`.
3. Since `S ⊆ fdClosure Σ Ω̃ⱼ`, we get `s.AgreeOn S t`.
4. By `Q.faithful`, `Q(w) ↔ Q(w')`.
-/

/-!
## Footprint lifting
-/

/-- **Footprint lifting**: agreement on `Ω̃ⱼ` propagates, via FD closure, to
    agreement on `Q.footprint` whenever `Q.footprint ⊆ fdClosure Σ Ω̃ⱼ`. -/
theorem footprint_lifting (L : LegalityStructure) (w w' : World)
    (hw : L.worlds w) (hw' : L.worlds w')
    (Õ : AttrSet) (Q : BoolCQ)
    (hground : Q.footprint ⊆ fdClosure L.fds Õ)
    (s t : Tuple) (hs : w s) (ht : w' t)
    (hOagree : s.AgreeOn Õ t) :
    s.AgreeOn Q.footprint t := by
  have hclos : s.AgreeOn (fdClosure L.fds Õ) t :=
    fd_determinacy L w w' hw hw' Õ s t hs ht hOagree
  exact AgreeOn.mono hclos hground

/-!
## Certification sufficiency (theorem)
-/

/-- **Certification**: if `Q.footprint ⊆ fdClosure I.fds Ω̃ⱼ` for some
    `Ω̃ⱼ ∈ I.augOverlaps`, then `Q` is identifiable under `I`. -/
theorem certificate_sufficiency (I : Interface) (Q : BoolCQ)
    (Õ : AttrSet) (hÕ : Õ ∈ I.augOverlaps)
    (hground : Q.footprint ⊆ fdClosure I.fds Õ) :
    Identifiable I Q := by
  intro w w' hw hw' hobs
  have hOeq : World.AgreeOn Õ w w' := hobs Õ hÕ
  apply Q.faithful
  constructor
  · intro s hs
    obtain ⟨t, ht, hst⟩ := hOeq.1 s hs
    exact ⟨t, ht, footprint_lifting I.legality w w' hw hw' Õ Q hground s t hs ht hst⟩
  · intro t ht
    obtain ⟨s, hs, hst⟩ := hOeq.2 t ht
    exact ⟨s, hs, footprint_lifting I.legality w w' hw hw' Õ Q hground s t hs ht hst⟩

/-!
## Full groundedness implies identifiability
-/

/-- **Full groundedness**: if `Q` is fully grounded, then `Q` is identifiable. -/
theorem fully_grounded_identifiable (I : Interface) (Q : BoolCQ)
    (hg : FullyGrounded I Q) : Identifiable I Q := by
  obtain ⟨Õ, hÕ, hground⟩ := hg
  exact certificate_sufficiency I Q Õ hÕ hground

/-!
## Converse: necessity is FALSE as stated

The converse — `Identifiable I Q → FullyGrounded I Q` — does **not** hold
for an arbitrary interface, and it is not claimed here: the closure certificate is stated
as a one-directional *sufficient* certificate, and its companion remark explicitly notes
that failure to certify "does not by itself prove non-identifiability".

Concretely, take an interface whose only legal world is the empty instance. Every query
is then trivially identifiable (there is only one legal world, so observationally
equivalent legal worlds are equal and agree on every query). Yet a query whose footprint
is the singleton `{0}` is not grounded by the sole overlap `∅`, because
`fdClosure [] ∅ = ∅`. Hence `Identifiable` holds while `FullyGrounded` fails. The
declarations below formalize this disproof, replacing the earlier (unprovable) `sorry`.
-/

/-- The empty instance: a world containing no tuples. -/
def emptyWorld : World := fun _ => False

/-- An interface with a single legal world (the empty instance), no FDs, and the sole
    augmented overlap `∅`. It is a well-formed `Interface` (`aug_closed` holds since
    `∅ ⊆ anything`). -/
def degenerateInterface : Interface where
  legality :=
    { worlds := fun w => w = emptyWorld
      fds := []
      legal := by intro fd hfd; cases hfd }
  augOverlaps := [AttrSet.empty]
  aug_closed := by
    intro Õ hÕ
    cases hÕ with
    | head => intro a ha; exact ha.elim
    | tail _ h => cases h

/-- A query with non-grounded footprint `{0}` but a constant (hence trivially
    identifiable) answer. -/
def degenerateQuery : BoolCQ where
  footprint := AttrSet.singleton 0
  eval := fun _ => True
  faithful := fun _ _ _ => Iff.rfl

/-- The degenerate interface/query pair is identifiable: there is only one legal world,
    so any two legal worlds give the same query answer. -/
theorem degenerate_identifiable : Identifiable degenerateInterface degenerateQuery := by
  intro w w' _ _ _; exact Iff.rfl

/-- With no FDs, the closure of a base is the base itself. -/
theorem inClosure_empty_fds (base : AttrSet) (a : Attr) (h : InClosure [] base a) : base a := by
  induction h with
  | ofBase hb => exact hb
  | ofFD hmem _ _ => cases hmem

/-- … but it is **not** fully grounded: the only overlap is `∅`, whose closure under the
    empty FD set is `∅`, which does not contain the footprint attribute `0`. -/
theorem degenerate_not_fullyGrounded : ¬ FullyGrounded degenerateInterface degenerateQuery := by
  intro ⟨Õ, hÕ, hg⟩
  cases hÕ with
  | head =>
    -- Õ = ∅, so hg : {0} ⊆ fdClosure [] ∅; instantiate at the footprint attribute 0.
    have h0 : InClosure [] AttrSet.empty 0 := hg 0 rfl
    exact (inClosure_empty_fds _ _ h0).elim
  | tail _ h => cases h

/-- **The converse is false.** There is an interface and a query that are
    identifiable but not fully grounded, so `Identifiable I Q → FullyGrounded I Q` cannot
    hold for arbitrary `I`. Here the closure
    certificate as sufficient only. -/
theorem certificate_necessity_false :
    ¬ ∀ (I : Interface) (Q : BoolCQ), Identifiable I Q → FullyGrounded I Q := by
  intro h
  exact degenerate_not_fullyGrounded (h degenerateInterface degenerateQuery degenerate_identifiable)

/-!
## Certificate decision predicate
-/

/-- `HasCertificate I Q` holds when there is a concrete `Ω̃ⱼ` covering `Q.footprint`. -/
def HasCertificate (I : Interface) (Q : BoolCQ) : Prop :=
  ∃ Õ ∈ I.augOverlaps, Q.footprint ⊆ fdClosure I.fds Õ

theorem hasCertificate_iff_fullyGrounded (I : Interface) (Q : BoolCQ) :
    HasCertificate I Q ↔ FullyGrounded I Q := Iff.rfl

theorem hasCertificate_identifiable (I : Interface) (Q : BoolCQ)
    (h : HasCertificate I Q) : Identifiable I Q :=
  fully_grounded_identifiable I Q h
