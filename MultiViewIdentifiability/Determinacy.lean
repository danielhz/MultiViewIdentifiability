import MultiViewIdentifiability.Identifiability

/-!
# Identifiability is query determinacy (Nash–Segoufin–Vianu)

Our `Identifiable I Q` is exactly **query determinacy** (Nash, Segoufin, Vianu, *Views and
Queries: Determinacy and Rewriting*, TODS 2010) of `Q` by the **overlap-projection views**:
worlds that agree on every view agree on `Q`. The "views" here are projection views (no
joins) — the closure-augmented overlap projections — so this is a decidable, in fact
polynomial (the closure certificate), sub-case of the determinacy problem, which is
undecidable for general conjunctive-query views.

The content is that observational equivalence (`ObsEquiv`) coincides with agreement of the
projection views (`projView_eq_iff_agreeOn`).
-/

/-- The **projection view** of world `w` onto attribute set `O`: the set of tuples that some
    tuple of `w` matches on `O`. (`O`-projection of `w`, saturated under `O`-agreement.) -/
def projView (O : AttrSet) (w : World) : Tuple → Prop := fun t => ∃ s, w s ∧ s.AgreeOn O t

/-- Two worlds have the same `O`-projection view iff they agree on `O`. -/
theorem projView_eq_iff_agreeOn (O : AttrSet) (w w' : World) :
    projView O w = projView O w' ↔ World.AgreeOn O w w' := by
  constructor
  · intro hEq
    refine ⟨fun s hs => ?_, fun t ht => ?_⟩
    · obtain ⟨u, hu, hus⟩ := Eq.mp (congrFun hEq s) ⟨s, hs, AgreeOn.refl O s⟩
      exact ⟨u, hu, AgreeOn.symm hus⟩
    · obtain ⟨u, hu, hut⟩ := Eq.mpr (congrFun hEq t) ⟨t, ht, AgreeOn.refl O t⟩
      exact ⟨u, hu, hut⟩
  · intro hAgree
    funext t
    apply propext
    constructor
    · rintro ⟨s, hs, hst⟩
      obtain ⟨u, hu, hsu⟩ := hAgree.1 s hs
      exact ⟨u, hu, AgreeOn.trans (AgreeOn.symm hsu) hst⟩
    · rintro ⟨s, hs, hst⟩
      obtain ⟨u, hu, hsu⟩ := hAgree.2 s hs
      exact ⟨u, hu, AgreeOn.trans hsu hst⟩

/-- **Query determinacy** (Nash–Segoufin–Vianu): `Q` is determined by a family of `views`
    over the `legal` worlds if any two legal worlds agreeing on every view agree on `Q`. -/
def DeterminedBy {β : Type _} (legal : World → Prop) (views : List (World → β))
    (Q : World → Prop) : Prop :=
  ∀ w w', legal w → legal w' → (∀ v ∈ views, v w = v w') → (Q w ↔ Q w')

/-- **Identifiability is determinacy by the overlap-projection views.** This places our
    identifiability inside the query-determinacy framework: the views are the projection
    views of the designated overlaps. -/
theorem identifiable_iff_determined (I : Interface) (Q : BoolCQ) :
    Identifiable I Q ↔ DeterminedBy I.worlds (I.augOverlaps.map projView) Q.eval := by
  constructor
  · intro hId w w' hw hw' hviews
    refine hId w w' hw hw' ?_
    intro O hO
    rw [← projView_eq_iff_agreeOn]
    exact hviews (projView O) (List.mem_map.mpr ⟨O, hO, rfl⟩)
  · intro hDet w w' hw hw' hobs
    refine hDet w w' hw hw' ?_
    intro v hv
    obtain ⟨O, hO, rfl⟩ := List.mem_map.mp hv
    rw [projView_eq_iff_agreeOn]
    exact hobs O hO

/-!
## The interface-visible fragment

A query is **interface-visible** when its answer is determined by the observable-schema
projections `w|_H` — the interpretations `R_H` of the base view predicates. A query over the
interface-visible vocabulary `L_iv` is built from these base predicates `R_H` together with
derived predicates defined by queries over them; since every such symbol is interpreted from
the observation, the whole query is determined by the observation. Such queries are
identifiable. (Unlike the closure certificate, this needs no legality assumption: the
relation symbols are fixed by the observation outright. It also allows joins *across*
overlaps — provided they are expressed over the observable `R_H` relations, not over raw
attributes spanning overlaps, which is the case the union-form counterexample rules out.)
-/

/-- An **interface-visible query**: its answer is determined by the projections `w|_H` onto
    the observable schemas (the `R_H` interpretations). Models a conjunctive query over the
    interface-visible vocabulary `L_iv`. -/
structure IVQuery (I : Interface) where
  eval    : World → Prop
  visible : ∀ w w', (∀ H ∈ I.augOverlaps, projView H w = projView H w') → (eval w ↔ eval w')

/-- **The interface-visible fragment is identifiable**: every interface-visible query is
    identifiable from the interface. -/
theorem iv_identifiable (I : Interface) (Q : IVQuery I) (w w' : World)
    (_hw : I.worlds w) (_hw' : I.worlds w') (hobs : ObsEquiv I.augOverlaps w w') :
    Q.eval w ↔ Q.eval w' := by
  refine Q.visible w w' ?_
  intro H hH
  exact (projView_eq_iff_agreeOn H w w').mpr (hobs H hH)
