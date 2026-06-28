import MultiViewIdentifiability.Basic
import MultiViewIdentifiability.FDClosure
import MultiViewIdentifiability.Identifiability
import MultiViewIdentifiability.Certificate

/-!
# Interface-Visible Queries

Single-overlap grounded queries: any Boolean CQ whose footprint is contained in the
FD-closure of some single augmented-overlap set is identifiable.

The easy, fully proved case: footprint ⊆ Ω̃ⱼ (direct containment in a single overlap)
implies identifiability. This is just an application of `certificate_sufficiency`.

For the harder case (footprint ⊆ fdClosure Σ (⋃ Ω̃ⱼ)), we need FDs that "bridge" overlaps,
which requires more infrastructure.
-/

/-!
## Single-overlap grounded queries
-/

/-- `Q` is **single-overlap grounded** if its footprint is covered by the FD-closure of
    some single augmented-overlap. -/
def SingleOverlapGrounded (I : Interface) (Q : BoolCQ) : Prop :=
  ∃ Õ ∈ I.augOverlaps, Q.footprint ⊆ fdClosure I.fds Õ

/-- Single-overlap groundedness implies identifiability (direct from the closure certificate). -/
theorem singleOverlap_identifiable (I : Interface) (Q : BoolCQ)
    (h : SingleOverlapGrounded I Q) : Identifiable I Q :=
  let ⟨Õ, hÕ, hground⟩ := h
  certificate_sufficiency I Q Õ hÕ hground

/-!
## Union-overlap coverage (general case)
-/

/-- The union of a list of attribute sets. -/
def AttrSet.unionList : List AttrSet → AttrSet
  | []      => AttrSet.empty
  | S :: Ss => AttrSet.union S (AttrSet.unionList Ss)

/-- Any element of a set in the list is in `unionList`. -/
theorem mem_unionList_of_mem {Ss : List AttrSet} {S : AttrSet} (hS : S ∈ Ss) (a : Attr) (ha : S a) :
    AttrSet.unionList Ss a := by
  induction Ss with
  | nil => cases hS
  | cons T Ts ih =>
    simp only [AttrSet.unionList, AttrSet.union]
    obtain rfl | hTail := List.mem_cons.mp hS
    · exact Or.inl ha
    · exact Or.inr (ih hTail)

/-!
## Union-overlap coverage is NOT sufficient (general form is FALSE)

The naive generalization — `Q.footprint ⊆ fdClosure Σ (⋃ⱼ Ω̃ⱼ)` ⇒ identifiable — is
**false**. Observational equivalence only forces agreement on each overlap `Ω̃ⱼ`
*separately*, with a possibly *different* matching tuple per overlap; it does not give a
single tuple agreeing on the whole union. So a query coupling attributes from different
overlaps can differ on obs-equivalent worlds.

What is refuted here is the flat *union-of-footprint* heuristic — **not** the interface-visible
result. Queries expressed over the observable `R_{Ω̃ⱼ}` predicates *are* identifiable
(`iv_identifiable`), and a footprint inside a single overlap is too
(`singleOverlap_identifiable` / `footprint_in_overlap_identifiable`). The failure is specific
to covering a footprint by the *union* of overlaps when an atom couples attributes drawn from
different overlaps.

The classic counterexample: overlaps `{0}`, `{1}`, no FDs, with
`wA = {(0,0),(1,1)}` and `wB = {(0,1),(1,0)}`. Their projections on `{0}` and on `{1}`
agree as sets (so they are obs-equivalent), but the query "∃ a tuple with attr₀ = attr₁"
is true on `wA` and false on `wB`.
-/

/-- Helper: agreement on a singleton overlap is just agreement at that one attribute. -/
theorem agreeOn_singleton {s t : Tuple} {k : Attr} (h : s k = t k) :
    s.AgreeOn (AttrSet.singleton k) t := by
  intro a ha
  have hak : a = k := ha
  subst hak
  exact h

/-- Tuple `(0,0,…)`. -/ def t00 : Tuple := fun _ => 0
/-- Tuple `(1,1,…)`. -/ def t11 : Tuple := fun _ => 1
/-- Tuple with attr₀=0, attr₁=1. -/ def t01 : Tuple := fun i => if i = 0 then 0 else 1
/-- Tuple with attr₀=1, attr₁=0. -/ def t10 : Tuple := fun i => if i = 0 then 1 else 0

/-- World `{(0,0),(1,1)}`. -/ def wA : World := fun u => u = t00 ∨ u = t11
/-- World `{(0,1),(1,0)}`. -/ def wB : World := fun u => u = t01 ∨ u = t10

/-- Counterexample interface: overlaps `{0}`, `{1}`, no FDs, legal worlds `wA`, `wB`. -/
def cexIV : Interface where
  legality :=
    { worlds := fun u => u = wA ∨ u = wB
      fds := []
      legal := by intro fd hfd; cases hfd }
  augOverlaps := [AttrSet.singleton 0, AttrSet.singleton 1]
  aug_closed := by
    intro O hO
    rcases List.mem_cons.mp hO with rfl | hO1
    · exact fdClosure_extensive _ (AttrSet.singleton 0)
    · rcases List.mem_cons.mp hO1 with rfl | hO2
      · exact fdClosure_extensive _ (AttrSet.singleton 1)
      · cases hO2

/-- The coupling query: true iff some tuple has `attr₀ = attr₁`. Footprint `{0,1}`. -/
def cexIVQuery : BoolCQ where
  footprint := AttrSet.union (AttrSet.singleton 0) (AttrSet.singleton 1)
  eval := fun w => ∃ s, w s ∧ s 0 = s 1
  faithful := by
    intro w w' hagree
    constructor
    · rintro ⟨s, hs, heq⟩
      obtain ⟨t, ht, hst⟩ := hagree.1 s hs
      refine ⟨t, ht, ?_⟩
      have h0 : s 0 = t 0 := hst 0 (Or.inl rfl)
      have h1 : s 1 = t 1 := hst 1 (Or.inr rfl)
      rw [← h0, ← h1]; exact heq
    · rintro ⟨t, ht, heq⟩
      obtain ⟨s, hs, hst⟩ := hagree.2 t ht
      refine ⟨s, hs, ?_⟩
      have h0 : s 0 = t 0 := hst 0 (Or.inl rfl)
      have h1 : s 1 = t 1 := hst 1 (Or.inr rfl)
      rw [h0, h1]; exact heq

/-- `wA` and `wB` are observationally equivalent: projections agree on `{0}` and on `{1}`. -/
theorem cexIV_obsequiv : ObsEquiv cexIV.augOverlaps wA wB := by
  intro O hO
  rcases List.mem_cons.mp hO with rfl | hO1
  · -- O = {0}
    exact ⟨fun s hs => by
            rcases hs with rfl | rfl
            · exact ⟨t01, Or.inl rfl, agreeOn_singleton rfl⟩
            · exact ⟨t10, Or.inr rfl, agreeOn_singleton rfl⟩,
           fun t ht => by
            rcases ht with rfl | rfl
            · exact ⟨t00, Or.inl rfl, agreeOn_singleton rfl⟩
            · exact ⟨t11, Or.inr rfl, agreeOn_singleton rfl⟩⟩
  · rcases List.mem_cons.mp hO1 with rfl | hO2
    · -- O = {1}
      exact ⟨fun s hs => by
              rcases hs with rfl | rfl
              · exact ⟨t10, Or.inr rfl, agreeOn_singleton rfl⟩
              · exact ⟨t01, Or.inl rfl, agreeOn_singleton rfl⟩,
             fun t ht => by
              rcases ht with rfl | rfl
              · exact ⟨t11, Or.inr rfl, agreeOn_singleton rfl⟩
              · exact ⟨t00, Or.inl rfl, agreeOn_singleton rfl⟩⟩
    · cases hO2

/-- **The general (union-overlap) form is false.** There is an interface and a query with
    `Q.footprint ⊆ fdClosure Σ (⋃ⱼ Ω̃ⱼ)` that is nonetheless not identifiable. -/
theorem union_footprint_coverage_insufficient :
    ¬ ∀ (I : Interface) (Q : BoolCQ),
        Q.footprint ⊆ fdClosure I.fds (AttrSet.unionList I.augOverlaps) → Identifiable I Q := by
  intro h
  have hcover : cexIVQuery.footprint ⊆
      fdClosure cexIV.fds (AttrSet.unionList cexIV.augOverlaps) := by
    intro a ha
    apply InClosure.ofBase
    rcases ha with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
  have hid : Identifiable cexIV cexIVQuery := h cexIV cexIVQuery hcover
  have hAB : cexIVQuery.eval wA ↔ cexIVQuery.eval wB :=
    hid wA wB (Or.inl rfl) (Or.inr rfl) cexIV_obsequiv
  have hevalA : cexIVQuery.eval wA := ⟨t00, Or.inl rfl, rfl⟩
  obtain ⟨s, hs, heq⟩ := hAB.mp hevalA
  rcases hs with rfl | rfl
  · exact absurd heq (by decide)
  · exact absurd heq (by decide)

/-!
## Direct containment
-/

/-- **Direct containment**: if `Q.footprint ⊆ Ω̃ⱼ` (direct containment), then `Q` is
    identifiable. The proof is immediate from `certificate_sufficiency` and extensivity. -/
theorem footprint_in_overlap_identifiable (I : Interface) (Q : BoolCQ)
    (Õ : AttrSet) (hÕ : Õ ∈ I.augOverlaps)
    (hfp : Q.footprint ⊆ Õ) :
    Identifiable I Q :=
  certificate_sufficiency I Q Õ hÕ (AttrSet.subset_trans hfp (fdClosure_extensive I.fds Õ))

/-- Corollary: singleton-overlap interface. If every augmented-overlap is a singleton `{aⱼ}`
    and `Q.footprint ⊆ fdClosure Σ {a₁,…,aₖ}`, then `Q` is identifiable. -/
theorem singletonOverlap_identifiable (I : Interface) (Q : BoolCQ)
    (a : Attr) (hÕ : AttrSet.singleton a ∈ I.augOverlaps)
    (hfp : Q.footprint ⊆ fdClosure I.fds (AttrSet.singleton a)) :
    Identifiable I Q :=
  certificate_sufficiency I Q (AttrSet.singleton a) hÕ hfp
