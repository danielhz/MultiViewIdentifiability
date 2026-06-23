/-!
# Basic Types for Multi-View Query Identifiability

The core data model.

We model attributes as `Nat` (indices into a finite universal schema), values as `Nat`,
and attribute sets as predicates `Attr → Prop`. This avoids a dependency on `Finset`
(which lives in Mathlib) while remaining fully general for the identifiability proofs.

Cross-world FDs are stronger than instance-level FDs:
`s|_X = t|_X ⟹ s|_{rhs} = t|_{rhs}` must hold for tuples from *any two* legal worlds.
-/

/-- Attribute index (universal schema). -/
abbrev Attr := Nat

/-- Value domain. -/
abbrev Val := Nat

/-- A **tuple** is a total map from attributes to values. -/
abbrev Tuple := Attr → Val

/-- A **world** is a set of tuples, represented as a predicate. -/
abbrev World := Tuple → Prop

/-- Attribute set as a predicate. -/
abbrev AttrSet := Attr → Prop

-- In Lean 4, `Membership.mem : γ → α → Prop` and `a ∈ S` elaborates to `Membership.mem S a`.
-- So the instance wraps `fun (S : AttrSet) (a : Attr) => S a`.
instance : Membership Attr AttrSet := ⟨fun S a => S a⟩

def AttrSet.Subset (S T : AttrSet) : Prop := ∀ a, S a → T a
instance : HasSubset AttrSet := ⟨AttrSet.Subset⟩

theorem AttrSet.subset_refl (S : AttrSet) : S ⊆ S := fun _ h => h

theorem AttrSet.subset_trans {S T U : AttrSet} (h₁ : S ⊆ T) (h₂ : T ⊆ U) : S ⊆ U :=
  fun a ha => h₂ a (h₁ a ha)

def AttrSet.empty : AttrSet := fun _ => False
def AttrSet.singleton (a : Attr) : AttrSet := fun b => b = a
def AttrSet.union (S T : AttrSet) : AttrSet := fun a => S a ∨ T a

/-!
## Functional dependencies
-/

/-- A **functional dependency**: LHS attribute set → RHS attribute. -/
structure FD where
  lhs : AttrSet
  rhs : Attr

/-- Two tuples **agree on** `X` when they return the same value for every `a ∈ X`.
    Defined with `X` first so that dot notation `s.AgreeOn X t` fills the `Tuple`-typed
    leading implicit via Lean's first-`Tuple`-arg rule. -/
def Tuple.AgreeOn (X : AttrSet) (s t : Tuple) : Prop :=
  ∀ a, X a → s a = t a

namespace AgreeOn

theorem refl (X : AttrSet) (s : Tuple) : s.AgreeOn X s := fun _ _ => rfl

theorem symm {X : AttrSet} {s t : Tuple} (h : s.AgreeOn X t) : t.AgreeOn X s :=
  fun a ha => (h a ha).symm

theorem trans {X : AttrSet} {s t u : Tuple}
    (h₁ : s.AgreeOn X t) (h₂ : t.AgreeOn X u) : s.AgreeOn X u :=
  fun a ha => (h₁ a ha).trans (h₂ a ha)

theorem mono {X Y : AttrSet} {s t : Tuple} (h : s.AgreeOn Y t) (hXY : X ⊆ Y) :
    s.AgreeOn X t :=
  fun a ha => h a (hXY a ha)

end AgreeOn

/-- An FD **holds cross-world** between `w` and `w'` when agreement on LHS implies
    agreement on RHS for any `s ∈ w`, `t ∈ w'`. -/
def FD.HoldsOnPair (fd : FD) (w w' : World) : Prop :=
  ∀ s t, w s → w' t → s.AgreeOn fd.lhs t → s fd.rhs = t fd.rhs

/-- A **legality structure**: worlds together with cross-world FDs. -/
structure LegalityStructure where
  worlds  : World → Prop
  fds     : List FD
  legal   : ∀ fd, fd ∈ fds → ∀ w w', worlds w → worlds w' → fd.HoldsOnPair w w'

/-!
## Observation equivalence
-/

/-- Two worlds **agree on** attribute set `O`: every O-projection in one has a matching
    O-projection in the other (set-equality of projections). -/
def World.AgreeOn (O : AttrSet) (w w' : World) : Prop :=
  (∀ s, w s → ∃ t, w' t ∧ s.AgreeOn O t) ∧
  (∀ t, w' t → ∃ s, w s ∧ s.AgreeOn O t)

-- Avoid name collision with AgreeOn.refl by using `_root_` or inlining.
theorem World.AgreeOn.refl (O : AttrSet) (w : World) : w.AgreeOn O w :=
  ⟨fun s hs => ⟨s, hs, fun _ _ => rfl⟩,
   fun t ht => ⟨t, ht, fun _ _ => rfl⟩⟩

theorem World.AgreeOn.symm {O : AttrSet} {w w' : World} (h : w.AgreeOn O w') :
    w'.AgreeOn O w :=
  ⟨fun s hs =>
      let ⟨t, ht, hts⟩ := h.2 s hs
      ⟨t, ht, fun a ha => (hts a ha).symm⟩,
   fun t ht =>
      let ⟨s, hs, hst⟩ := h.1 t ht
      ⟨s, hs, fun a ha => (hst a ha).symm⟩⟩

/-- **Observational equivalence**: two worlds agree on every augmented-overlap in the family
   . -/
def ObsEquiv (family : List AttrSet) (w w' : World) : Prop :=
  ∀ O ∈ family, World.AgreeOn O w w'

theorem ObsEquiv.refl (family : List AttrSet) (w : World) : ObsEquiv family w w :=
  fun O _ => World.AgreeOn.refl O w

theorem ObsEquiv.symm {family : List AttrSet} {w w' : World}
    (h : ObsEquiv family w w') : ObsEquiv family w' w :=
  fun O hO => (h O hO).symm

theorem ObsEquiv.trans {family : List AttrSet} {w w' w'' : World}
    (h₁ : ObsEquiv family w w') (h₂ : ObsEquiv family w' w'') :
    ObsEquiv family w w'' := by
  intro O hO
  constructor
  · intro s hs
    obtain ⟨u, hu, hsu⟩ := (h₁ O hO).1 s hs
    obtain ⟨t, ht, hut⟩ := (h₂ O hO).1 u hu
    exact ⟨t, ht, fun a ha => (hsu a ha).trans (hut a ha)⟩
  · intro t ht
    obtain ⟨u, hu, hut⟩ := (h₂ O hO).2 t ht
    obtain ⟨s, hs, hsu⟩ := (h₁ O hO).2 u hu
    exact ⟨s, hs, fun a ha => (hsu a ha).trans (hut a ha)⟩

/-!
## Boolean conjunctive queries

We represent a Boolean CQ by:
- its **footprint** `S = ⋃_j attr(U_j)` (union of view attribute sets used by atoms),
- its **evaluation** `eval : World → Prop`,
- the **footprint condition**: the answer depends only on the world's S-projection.
-/

/-- A **Boolean CQ** together with its footprint and footprint faithfulness. -/
structure BoolCQ where
  footprint  : AttrSet
  eval       : World → Prop
  /-- The query answer depends only on the world's restriction to `footprint`
      (if `w|_S = w'|_S` then `Q(w) = Q(w')`). -/
  faithful   : ∀ w w', w.AgreeOn footprint w' → (eval w ↔ eval w')

/-- Query answer on a world. -/
def BoolCQ.answer (Q : BoolCQ) (w : World) : Prop := Q.eval w
