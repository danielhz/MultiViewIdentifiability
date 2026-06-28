import MultiViewIdentifiability.Identifiability
import MultiViewIdentifiability.FDClosure

/-!
# Atom-wise closure certificate

A conjunctive query is identifiable when **each of its relation atoms** is covered by a
single observable schema (here, an FD-closed designated overlap). Observation equivalence
then fixes every atom's projection, and the query — a join over those atoms — has an
invariant answer.

This refines the single-overlap certificate (`certificate_sufficiency`): covering a query's
attributes *separately* across overlaps is **not** enough — equal `A`- and `B`-projections
need not fix the joint `AB`-projection (see `union_footprint_coverage_insufficient`). The
certificate must therefore work atom by atom, with each atom's *whole* schema inside one
observable schema. The single-overlap result is the special case of one atom.
-/

/-- A conjunctive query presented by its relation-atom schemas, with an answer that depends
    only on the per-atom projections of the world (the atom-footprint invariant). -/
structure AtomCQ where
  atoms    : List AttrSet
  eval     : World → Prop
  faithful : ∀ w w', (∀ U ∈ atoms, World.AgreeOn U w w') → (eval w ↔ eval w')

/-- Identifiability of an `AtomCQ` under an interface: observationally equivalent legal
    worlds give the same answer. -/
def AtomIdentifiable (I : Interface) (Q : AtomCQ) : Prop :=
  ∀ w w', I.worlds w → I.worlds w' → ObsEquiv I.augOverlaps w w' → (Q.eval w ↔ Q.eval w')

/-- **Atom-footprint lemma**: if two worlds agree on every atom schema of `Q`, they agree on
    `Q`'s answer. (Named restatement of the query's defining invariant.) -/
theorem cq_footprint (Q : AtomCQ) {w w' : World}
    (h : ∀ U ∈ Q.atoms, World.AgreeOn U w w') : Q.eval w ↔ Q.eval w' :=
  Q.faithful w w' h

/-- Agreement on a designated overlap lifts, via FD closure, to agreement on any attribute
    set contained in that overlap's closure. -/
theorem agreeOn_lift (L : LegalityStructure) (w w' : World)
    (hw : L.worlds w) (hw' : L.worlds w') (O U : AttrSet)
    (hsub : U ⊆ fdClosure L.fds O) (hO : World.AgreeOn O w w') :
    World.AgreeOn U w w' := by
  refine ⟨fun s hs => ?_, fun t ht => ?_⟩
  · obtain ⟨t, ht, hst⟩ := hO.1 s hs
    exact ⟨t, ht, AgreeOn.mono (fd_determinacy L w w' hw hw' O s t hs ht hst) hsub⟩
  · obtain ⟨s, hs, hst⟩ := hO.2 t ht
    exact ⟨s, hs, AgreeOn.mono (fd_determinacy L w w' hw hw' O s t hs ht hst) hsub⟩

/-- **Atom-wise closure certificate**: if every relation atom of `Q` has its schema contained
    in the FD-closure of some designated overlap, then `Q` is identifiable. -/
theorem atomwise_certificate (I : Interface) (Q : AtomCQ)
    (h : ∀ U ∈ Q.atoms, ∃ O ∈ I.augOverlaps, U ⊆ fdClosure I.fds O) :
    AtomIdentifiable I Q := by
  intro w w' hw hw' hobs
  refine cq_footprint Q ?_
  intro U hU
  obtain ⟨O, hO, hsub⟩ := h U hU
  exact agreeOn_lift I.legality w w' hw hw' O U hsub (hobs O hO)
