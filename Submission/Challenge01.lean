import Defs_and_Lems.Minor
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Set.Card
import Mathlib.Data.Finite.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.ByContra

set_option linter.all false


namespace HadwigerConj

/-- `IsMinor H G`: the graph `H` is a minor of the graph `G`, expressed through branch sets.
There is a family `B w` (one for each vertex `w` of `H`) of vertex sets of `G` such that
each `B w` induces a connected (in particular nonempty) subgraph of `G`, distinct branch sets
are disjoint, and whenever `w₁ w₂` is an edge of `H` some vertex of `B w₁` is adjacent in `G`
to some vertex of `B w₂`. -/
def IsMinor {W V : Type*} (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ B : W → Set V,
    (∀ w, (G.induce (B w)).Connected) ∧
    (∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (B w₁) (B w₂)) ∧
    (∀ w₁ w₂, H.Adj w₁ w₂ → ∃ u ∈ B w₁, ∃ v ∈ B w₂, G.Adj u v)

/-- `HasCompleteMinor G t`: the complete graph `K_t` is a minor of `G`. -/
def HasCompleteMinor {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop :=
  IsMinor (⊤ : SimpleGraph (Fin t)) G

/-- `HC t`: every finite graph with no `K_{t+1}` minor is `t`-colourable. -/
def HC (t : ℕ) : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V), ¬ HasCompleteMinor G (t + 1) → G.Colorable t

/-- `IsDegenerate G k`: every nonempty set `S` of vertices contains a vertex with at most `k`
neighbours inside `S` (i.e. every non-null induced subgraph has a vertex of degree `≤ k`). -/
def IsDegenerate {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Set V, S.Nonempty → ∃ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ k

end HadwigerConj



namespace DiracK4
open HadwigerConj SimpleGraph

lemma walk_prop {W : Type*} {G' : SimpleGraph W} {s : Set W} (P : W → Prop)
    (hc : (G'.induce s).Preconnected) {y1 : W} (h1 : y1 ∈ s) (hP1 : P y1)
    (hstep : ∀ y z, y ∈ s → z ∈ s → G'.Adj y z → P y → P z) : ∀ y ∈ s, P y := by
  intro y hy
  obtain ⟨p⟩ := hc ⟨y1, h1⟩ ⟨y, hy⟩
  suffices ∀ (a b : s) (_ : (G'.induce s).Walk a b), P a → P b from this _ _ p hP1
  intro a b q
  induction q with
  | nil => exact id
  | cons h _ ih => exact fun ha => ih (hstep _ _ (Subtype.prop _) (Subtype.prop _) (by simpa using h) ha)

lemma reach_in {V : Type*} {G : SimpleGraph V} {s t : Set V} (hst : s ⊆ t)
    (hs : (G.induce s).Connected) {a b : V} (ha : a ∈ s) (hb : b ∈ s) :
    (G.induce t).Reachable ⟨a, hst ha⟩ ⟨b, hst hb⟩ :=
  (hs.preconnected ⟨a, ha⟩ ⟨b, hb⟩).map (G.induceHomOfLE hst).toHom

lemma minor_trans {U W V : Type*} {H : SimpleGraph U} {G' : SimpleGraph W} {G : SimpleGraph V}
    (h1 : IsMinor H G') (h2 : IsMinor G' G) : IsMinor H G := by
  obtain ⟨B, hBc, hBd, hBa⟩ := h1
  obtain ⟨C, hCc, hCd, hCa⟩ := h2
  refine ⟨fun w => ⋃ y ∈ B w, C y, fun w => ?_, fun w1 w2 hw => ?_, fun w1 w2 hw => ?_⟩
  · set U := ⋃ y ∈ B w, C y with hU
    have hsub : ∀ y ∈ B w, C y ⊆ U := fun y hy => Set.subset_biUnion_of_mem (u := C) hy
    rw [connected_iff]
    obtain ⟨⟨y0, hy0⟩⟩ := (hBc w).nonempty
    obtain ⟨⟨c0, hc0⟩⟩ := (hCc y0).nonempty
    refine ⟨?_, ⟨⟨c0, hsub y0 hy0 hc0⟩⟩⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨y1, hy1, ha'⟩ := Set.mem_iUnion₂.1 ha
    obtain ⟨y2, hy2, hb'⟩ := Set.mem_iUnion₂.1 hb
    have key := walk_prop (s := B w) (G' := G')
      (fun z => ∀ (hz : z ∈ B w) c (hc : c ∈ C z), (G.induce U).Reachable ⟨a, ha⟩ ⟨c, hsub z hz hc⟩)
      (hBc w).preconnected hy1
      (fun _ c hc => reach_in (hsub y1 hy1) (hCc y1) ha' hc)
      (by
        intro y z hy hz hyz hPy _ c hc
        obtain ⟨u', hu', v', hv', huv⟩ := hCa y z hyz
        refine (hPy hy u' hu').trans (Reachable.trans ?_ (reach_in (hsub z hz) (hCc z) hv' hc))
        exact Adj.reachable (by simpa using huv))
    exact key y2 hy2 hy2 b hb'
  · rw [Set.disjoint_left]
    intro a ha hb
    obtain ⟨y1, hy1, ha'⟩ := Set.mem_iUnion₂.1 ha
    obtain ⟨y2, hy2, hb'⟩ := Set.mem_iUnion₂.1 hb
    have hne : y1 ≠ y2 := fun h => Set.disjoint_left.1 (hBd w1 w2 hw) hy1 (h ▸ hy2)
    exact Set.disjoint_left.1 (hCd y1 y2 hne) ha' hb'
  · obtain ⟨y1, hy1, y2, hy2, hy⟩ := hBa w1 w2 hw
    obtain ⟨u, hu, v, hv, huv⟩ := hCa y1 y2 hy
    exact ⟨u, Set.mem_biUnion hy1 hu, v, Set.mem_biUnion hy2 hv, huv⟩

lemma sing {V : Type*} (G : SimpleGraph V) (v : V) : (G.induce {v}).Connected := by
  have := (Walk.nil : G.Walk v v).connected_induce_support
  have e : {y | y ∈ (Walk.nil : G.Walk v v).support} = {v} := by ext; simp
  rwa [e] at this

/-- Subgraph is a minor. -/
lemma minor_of_le {V : Type*} {G' G : SimpleGraph V} (h : G' ≤ G) : IsMinor G' G :=
  ⟨fun y => {y}, fun y => sing G y, fun a b hab => by simpa using hab,
    fun a b hab => ⟨a, rfl, b, rfl, h hab⟩⟩

end DiracK4

namespace DiracK4
open HadwigerConj SimpleGraph

variable {V : Type*}

lemma deg_ge [Finite V] {S : Set V} (G' : SimpleGraph S) (w : S) (T : Set V)
    (hT : ∀ t ∈ T, ∃ h : t ∈ S, G'.Adj w ⟨t, h⟩) : T.ncard ≤ (G'.neighborSet w).ncard := by
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  intro t ht
  obtain ⟨h, hadj⟩ := hT t ht
  exact ⟨⟨t, h⟩, hadj, rfl⟩

/-- contraction of the edge `uv` onto `u` -/
def contr (G : SimpleGraph V) (u v : V) : SimpleGraph {y // y ≠ v} where
  Adj a b := a.1 ≠ b.1 ∧ (G.Adj a.1 b.1 ∨ (a.1 = u ∧ G.Adj v b.1) ∨ (b.1 = u ∧ G.Adj v a.1))
  symm := ⟨by
    intro a b ⟨h1, h2⟩
    refine ⟨Ne.symm h1, ?_⟩
    rcases h2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨fun a h => h.1 rfl⟩

lemma contr_minor {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    IsMinor (contr G u v) G := by
  classical
  refine ⟨fun y => if y.1 = u then {u, v} else {y.1}, fun y => ?_, fun a b hab => ?_,
    fun a b hab => ?_⟩
  · dsimp only
    by_cases h : y.1 = u
    · rw [if_pos h]; exact induce_pair_connected_of_adj huv
    · rw [if_neg h]; exact sing G _
  · have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    have ha := a.2; have hb := b.2
    dsimp only
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2.symm) hab'
    · rw [Set.disjoint_singleton_right]; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact h2 (h ▸ rfl)
      · exact hb h
    · rw [Set.disjoint_singleton_left]; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h)
      · exact h1 h
      · exact ha h
    · simpa using hab'
  · have mem : ∀ y : {y // y ≠ v}, y.1 ∈ (if y.1 = u then ({u, v} : Set V) else {y.1}) := by
      intro y; split_ifs with h
      · simp [h]
      · simp
    have memv : ∀ y : {y // y ≠ v}, y.1 = u → v ∈ (if y.1 = u then ({u, v} : Set V) else {y.1}) := by
      intro y h; simp [h]
    obtain ⟨_, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hab
    · exact ⟨a.1, mem a, b.1, mem b, h⟩
    · exact ⟨v, memv a h1, b.1, mem b, h2⟩
    · exact ⟨a.1, mem a, v, memv b h1, h2.symm⟩

lemma contr_deg [Finite V] {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (hδ : ∀ y, 3 ≤ (G.neighborSet y).ncard)
    (hc : ∀ w, G.Adj u w → G.Adj v w → 4 ≤ (G.neighborSet w).ncard)
    (hm : 3 ≤ ((G.neighborSet u ∪ G.neighborSet v) \ {u, v}).ncard) :
    ∀ y, 3 ≤ ((contr G u v).neighborSet y).ncard := by
  intro y
  by_cases hyu : y.1 = u
  · refine hm.trans (deg_ge _ y _ ?_)
    rintro t ⟨ht1, ht2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht2
    refine ⟨ht2.2, ?_⟩
    show y.1 ≠ t ∧ (G.Adj y.1 t ∨ (y.1 = u ∧ G.Adj v t) ∨ (t = u ∧ G.Adj v y.1))
    rw [hyu]
    refine ⟨fun h => ht2.1 h.symm, ?_⟩
    rcases ht1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨rfl, h⟩)
  · have hyv := y.2
    have hk : ∀ t ∈ G.neighborSet y.1 \ {v}, ∃ h : t ≠ v, (contr G u v).Adj y ⟨t, h⟩ := by
      rintro t ⟨ht1, ht2⟩
      exact ⟨ht2, G.ne_of_adj ht1, Or.inl ht1⟩
    by_cases hyv' : G.Adj y.1 v
    · by_cases hyu' : G.Adj y.1 u
      · -- common neighbour: degree drops by one
        have h4 := hc y.1 hyu'.symm hyv'.symm
        have : (G.neighborSet y.1 \ {v}).ncard = (G.neighborSet y.1).ncard - 1 :=
          Set.ncard_sdiff_singleton_of_mem hyv'
        exact (by omega : 3 ≤ (G.neighborSet y.1 \ {v}).ncard).trans (deg_ge _ y _ hk)
      · have hu : u ∉ G.neighborSet y.1 \ {v} := fun h => hyu' h.1
        have e1 : (insert u (G.neighborSet y.1 \ {v})).ncard = (G.neighborSet y.1 \ {v}).ncard + 1 :=
          Set.ncard_insert_of_notMem hu
        have e2 : (G.neighborSet y.1 \ {v}).ncard = (G.neighborSet y.1).ncard - 1 :=
          Set.ncard_sdiff_singleton_of_mem hyv'
        have h3 := hδ y.1
        refine (by omega : 3 ≤ (insert u (G.neighborSet y.1 \ {v})).ncard).trans (deg_ge _ y _ ?_)
        rintro t (rfl | ht)
        · exact ⟨G.ne_of_adj huv, fun h => hyu h, Or.inr (Or.inr ⟨rfl, hyv'.symm⟩)⟩
        · exact hk t ht
    · have e : G.neighborSet y.1 \ {v} = G.neighborSet y.1 := by
        ext t; simp only [Set.mem_sdiff, Set.mem_singleton_iff, mem_neighborSet, and_iff_left_iff_imp]
        rintro h rfl; exact hyv' h
      exact (e ▸ hδ y.1).trans (deg_ge _ y _ hk)

end DiracK4

namespace DiracK4
open HadwigerConj SimpleGraph

variable {V : Type*}

/-- replace the diamond `x, m` (attached at `p, q`) by the edge `pq` -/
def diam (G : SimpleGraph V) (x m p q : V) : SimpleGraph {y // y ≠ x ∧ y ≠ m} where
  Adj a b := a.1 ≠ b.1 ∧ (G.Adj a.1 b.1 ∨ (a.1 = p ∧ b.1 = q) ∨ (a.1 = q ∧ b.1 = p))
  symm := ⟨by
    intro a b ⟨h1, h2⟩
    refine ⟨Ne.symm h1, ?_⟩
    rcases h2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)⟩
  loopless := ⟨fun a h => h.1 rfl⟩

open Classical in
noncomputable def diamC (x m p q : V) (y : {y // y ≠ x ∧ y ≠ m}) : Set V :=
  if y.1 = p then {p, x} else if y.1 = q then {q, m} else {y.1}

lemma diamC_mem {x m p q : V} (hpq : p ≠ q) (y : {y // y ≠ x ∧ y ≠ m}) (t : V) :
    t ∈ diamC x m p q y ↔ (t = y.1 ∨ (y.1 = p ∧ t = x) ∨ (y.1 = q ∧ t = m)) := by
  unfold diamC
  by_cases h1 : y.1 = p
  · rw [if_pos h1]; simp [h1, hpq]
  · rw [if_neg h1]
    by_cases h2 : y.1 = q
    · rw [if_pos h2]; simp [h2, hpq.symm]
    · rw [if_neg h2]; simp [h1, h2]

lemma diam_minor {G : SimpleGraph V} {x m p q : V} (hpx : G.Adj p x) (hqm : G.Adj q m)
    (hxm : G.Adj x m) (hpq : p ≠ q) :
    IsMinor (diam G x m p q) G := by
  classical
  have hmem := diamC_mem (x := x) (m := m) hpq
  refine ⟨diamC x m p q, fun y => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  · unfold diamC
    by_cases h1 : y.1 = p
    · rw [if_pos h1]; exact induce_pair_connected_of_adj hpx
    · rw [if_neg h1]
      by_cases h2 : y.1 = q
      · rw [if_pos h2]; exact induce_pair_connected_of_adj hqm
      · rw [if_neg h2]; exact sing G _
  · have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    have ha := a.2; have hb := b.2
    rw [Set.disjoint_left]
    intro t h1 h2
    rw [hmem] at h1 h2
    rcases h1 with h1 | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
      simp_all
  · obtain ⟨_, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hab
    · exact ⟨a.1, (hmem _ _).2 (Or.inl rfl), b.1, (hmem _ _).2 (Or.inl rfl), h⟩
    · exact ⟨x, (hmem _ _).2 (Or.inr (Or.inl ⟨h1, rfl⟩)), m,
        (hmem _ _).2 (Or.inr (Or.inr ⟨h2, rfl⟩)), hxm⟩
    · exact ⟨m, (hmem _ _).2 (Or.inr (Or.inr ⟨h1, rfl⟩)), x,
        (hmem _ _).2 (Or.inr (Or.inl ⟨h2, rfl⟩)), hxm.symm⟩

lemma diam_deg [Finite V] {G : SimpleGraph V} {x m p q : V}
    (hδ : ∀ y, 3 ≤ (G.neighborSet y).ncard)
    (hNx : ∀ y, G.Adj x y → y = p ∨ y = m ∨ y = q)
    (hNm : ∀ y, G.Adj m y → y = x ∨ y = p ∨ y = q)
    (hpq : ¬ G.Adj p q) (hpq' : p ≠ q) (hpx : p ≠ x) (hpm : p ≠ m) (hqx : q ≠ x) (hqm : q ≠ m)
    (hp : 2 ≤ (G.neighborSet p \ {x, m}).ncard) (hq : 2 ≤ (G.neighborSet q \ {x, m}).ncard) :
    ∀ y, 3 ≤ ((diam G x m p q).neighborSet y).ncard := by
  intro y
  have hk : ∀ t ∈ G.neighborSet y.1 \ {x, m}, ∃ h : t ≠ x ∧ t ≠ m, (diam G x m p q).Adj y ⟨t, h⟩ := by
    rintro t ⟨ht1, ht2⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht2
    exact ⟨ht2, G.ne_of_adj ht1, Or.inl ht1⟩
  -- the generic bound with one extra vertex
  have extra : ∀ r, r ≠ x → r ≠ m → r ∉ G.neighborSet y.1 → y.1 ≠ r →
      (y.1 = p ∧ r = q ∨ y.1 = q ∧ r = p) → 2 ≤ (G.neighborSet y.1 \ {x, m}).ncard →
      3 ≤ ((diam G x m p q).neighborSet y).ncard := by
    intro r hrx hrm hrN hyr hr h2
    have hr' : r ∉ G.neighborSet y.1 \ {x, m} := fun h => hrN h.1
    have e := Set.ncard_insert_of_notMem hr' (Set.toFinite _)
    refine (by omega : 3 ≤ (insert r (G.neighborSet y.1 \ {x, m})).ncard).trans (deg_ge _ y _ ?_)
    rintro t (rfl | ht)
    · exact ⟨⟨hrx, hrm⟩, hyr, Or.inr hr⟩
    · exact hk t ht
  by_cases hyp : y.1 = p
  · exact extra q hqx hqm (by rw [hyp]; exact hpq) (by rw [hyp]; exact hpq') (Or.inl ⟨hyp, rfl⟩)
      (by rw [hyp]; exact hp)
  by_cases hyq : y.1 = q
  · exact extra p hpx hpm (by rw [hyq]; exact fun h => hpq h.symm) (by rw [hyq]; exact hpq'.symm)
      (Or.inr ⟨hyq, rfl⟩) (by rw [hyq]; exact hq)
  · have e : G.neighborSet y.1 \ {x, m} = G.neighborSet y.1 := by
      ext t
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, mem_neighborSet,
        and_iff_left_iff_imp]
      have hy2 := y.2
      rintro h (rfl | rfl)
      · rcases hNx _ h.symm with h' | h' | h' <;> simp_all
      · rcases hNm _ h.symm with h' | h' | h' <;> simp_all
    exact (e ▸ hδ y.1).trans (deg_ge _ y _ hk)

end DiracK4

namespace DiracK4
open HadwigerConj SimpleGraph

variable {V : Type*}

lemma three_le [Finite V] {s : Set V} {a b c : V} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.ncard := by
  have : ({a, b, c} : Set V).ncard = 3 := Set.ncard_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
  rw [← this]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  intro t ht; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl | rfl <;> assumption

lemma two_le [Finite V] {s : Set V} {a b : V} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    2 ≤ s.ncard := by
  have : ({a, b} : Set V).ncard = 2 := Set.ncard_pair hab
  rw [← this]
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  intro t ht; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with rfl | rfl <;> assumption

/-- some element of `s` outside a set of size `< s.ncard` -/
lemma exists_out [Finite V] {s t : Set V} (h : t.ncard < s.ncard) : ∃ y ∈ s, y ∉ t :=
  Set.exists_mem_notMem_of_ncard_lt_ncard h

lemma k4_of_triangle {G : SimpleGraph V} {x a b c : V} (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hxc : G.Adj x c) (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    HasCompleteMinor G 4 := by
  refine ⟨![{x}, {a}, {b}, {c}], fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · fin_cases i <;> exact sing G _
  · have := G.ne_of_adj hxa; have := G.ne_of_adj hxb; have := G.ne_of_adj hxc
    have := G.ne_of_adj hab; have := G.ne_of_adj hbc; have := G.ne_of_adj hac
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  · fin_cases i <;> fin_cases j <;> simp_all [hxa.symm, hxb.symm, hxc.symm, hab.symm, hbc.symm, hac.symm]

end DiracK4

namespace DiracK4
open HadwigerConj SimpleGraph

variable {V : Type*}

lemma pair_le (a b : V) : ({a, b} : Set V).ncard ≤ 2 :=
  (Set.ncard_insert_le _ _).trans (by simp)

/-- In the irreducible situation, every neighbour of `x` has a neighbour in `N(x)`. -/
lemma nbr_in [Finite V] {G : SimpleGraph V} (hδ : ∀ y, 3 ≤ (G.neighborSet y).ncard)
    (hC : ∀ u v, G.Adj u v → (∃ w, G.Adj u w ∧ G.Adj v w ∧ (G.neighborSet w).ncard < 4) ∨
      ((G.neighborSet u ∪ G.neighborSet v) \ {u, v}).ncard < 3)
    {x t : V} (hxt : G.Adj x t) (hx : (G.neighborSet x).ncard = 3) :
    ∃ s, G.Adj x s ∧ G.Adj t s := by
  by_contra hne
  push Not at hne
  rcases hC x t hxt with ⟨w, hxw, htw, _⟩ | h
  · exact hne w hxw htw
  · obtain ⟨y, hy, hy'⟩ := exists_out (s := G.neighborSet t) (t := {x})
      (by rw [Set.ncard_singleton]; have := hδ t; omega)
    have hy1 : y ≠ x := by simpa using hy'
    have hyN : y ∉ G.neighborSet x := fun h => hne y h (by simpa using hy)
    have e1 : (G.neighborSet x \ {t}).ncard = 2 := by
      rw [Set.ncard_sdiff_singleton_of_mem (show t ∈ G.neighborSet x from hxt), hx]
    have e2 := Set.ncard_insert_of_notMem (fun h => hyN h.1) (Set.toFinite (G.neighborSet x \ {t}))
    have : (insert y (G.neighborSet x \ {t})).ncard ≤
        ((G.neighborSet x ∪ G.neighborSet t) \ {x, t}).ncard := by
      apply Set.ncard_le_ncard _ (Set.toFinite _)
      rintro s (rfl | ⟨hs1, hs2⟩)
      · refine ⟨Or.inr hy, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hy1, (G.ne_of_adj hy).symm⟩
      · refine ⟨Or.inl hs1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨(G.ne_of_adj hs1).symm, by simpa using hs2⟩
    omega

lemma side [Finite V] {G : SimpleGraph V} (hδ : ∀ y, 3 ≤ (G.neighborSet y).ncard)
    (hC : ∀ u v, G.Adj u v → (∃ w, G.Adj u w ∧ G.Adj v w ∧ (G.neighborSet w).ncard < 4) ∨
      ((G.neighborSet u ∪ G.neighborSet v) \ {u, v}).ncard < 3)
    {x p m q : V} (hN : ∀ y, G.Adj x y → y = p ∨ y = m ∨ y = q)
    (hNm : ∀ y, G.Adj m y → y = x ∨ y = p ∨ y = q)
    (hxp : G.Adj x p) (hxm : G.Adj x m) (hpm : G.Adj p m) (hpq : ¬ G.Adj p q) :
    2 ≤ (G.neighborSet p \ {x, m}).ncard := by
  obtain ⟨p', hp', hp'n⟩ := exists_out (s := G.neighborSet p) (t := {x, m})
    (by have := hδ p; have := pair_le x m; omega)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hp'n
  have hp'a : G.Adj p p' := hp'
  have hxp' : ¬ G.Adj x p' := by
    intro h
    rcases hN p' h with rfl | rfl | rfl
    · exact G.loopless.irrefl _ hp'a
    · exact hp'n.2 rfl
    · exact hpq hp'a
  have hmp' : ¬ G.Adj m p' := by
    intro h
    rcases hNm p' h with rfl | rfl | rfl
    · exact hp'n.1 rfl
    · exact G.loopless.irrefl _ hp'a
    · exact hpq hp'a
  rcases hC p p' hp'a with ⟨w, hpw, hp'w, _⟩ | h
  · refine two_le (a := p') (b := w) ⟨hp'a, by simp [hp'n.1, hp'n.2]⟩ ⟨hpw, ?_⟩ (G.ne_of_adj hp'w)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hxp' (h ▸ hp'w.symm), fun h => hmp' (h ▸ hp'w.symm)⟩
  · exfalso
    obtain ⟨y, hy, hy'⟩ := exists_out (s := G.neighborSet p') (t := {p})
      (by rw [Set.ncard_singleton]; have := hδ p'; omega)
    have hy1 : y ≠ p := by simpa using hy'
    have hya : G.Adj p' y := hy
    have := three_le (s := (G.neighborSet p ∪ G.neighborSet p') \ {p, p'}) (a := x) (b := m) (c := y)
      ⟨Or.inl hxp.symm, by simp [(G.ne_of_adj hxp), Ne.symm hp'n.1]⟩
      ⟨Or.inl hpm, by simp [(G.ne_of_adj hpm).symm, Ne.symm hp'n.2]⟩
      ⟨Or.inr hya, by simp [hy1, (G.ne_of_adj hya).symm]⟩
      (G.ne_of_adj hxm) (fun h => hxp' (h ▸ hya.symm)) (fun h => hmp' (h ▸ hya.symm))
    omega

lemma diamond_step [Finite V] {G : SimpleGraph V} (hδ : ∀ y, 3 ≤ (G.neighborSet y).ncard)
    (hC : ∀ u v, G.Adj u v → (∃ w, G.Adj u w ∧ G.Adj v w ∧ (G.neighborSet w).ncard < 4) ∨
      ((G.neighborSet u ∪ G.neighborSet v) \ {u, v}).ncard < 3)
    {x p m q : V} (hN : ∀ y, G.Adj x y → y = p ∨ y = m ∨ y = q)
    (hxp : G.Adj x p) (hxm : G.Adj x m) (hxq : G.Adj x q)
    (hpm : G.Adj p m) (hmq : G.Adj m q) (hpq : ¬ G.Adj p q) (hpq' : p ≠ q) :
    ∀ y, 3 ≤ ((diam G x m p q).neighborSet y).ncard := by
  have hmdeg : (G.neighborSet m).ncard < 4 := by
    rcases hC x p hxp with ⟨w, hxw, hpw, hw⟩ | h
    · rcases hN w hxw with rfl | rfl | rfl
      · exact absurd hpw (G.loopless.irrefl _)
      · exact hw
      · exact absurd hpw hpq
    · exfalso
      obtain ⟨y, hy, hy'⟩ := exists_out (s := G.neighborSet p) (t := {x, m})
        (by have := hδ p; have := pair_le x m; omega)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy'
      have hya : G.Adj p y := hy
      have := three_le (s := (G.neighborSet x ∪ G.neighborSet p) \ {x, p}) (a := m) (b := q) (c := y)
        ⟨Or.inl hxm, by simp [(G.ne_of_adj hxm).symm, (G.ne_of_adj hpm).symm]⟩
        ⟨Or.inl hxq, by simp [(G.ne_of_adj hxq).symm, hpq'.symm]⟩
        ⟨Or.inr hya, by simp [hy'.1, (G.ne_of_adj hya).symm]⟩
        (G.ne_of_adj hmq) (Ne.symm hy'.2) (fun h => hpq (h ▸ hya))
      omega
  have hNm : ∀ y, G.Adj m y → y = x ∨ y = p ∨ y = q := by
    have hsub : ({x, p, q} : Set V) ⊆ G.neighborSet m := by
      intro t ht; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · exact hxm.symm
      · exact hpm.symm
      · exact hmq
    have h3 : ({x, p, q} : Set V).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨x, p, q, G.ne_of_adj hxp, G.ne_of_adj hxq, hpq', rfl⟩
    have heq := Set.eq_of_subset_of_ncard_le hsub (by have := hδ m; omega) (Set.toFinite _)
    intro y hy
    have : y ∈ ({x, p, q} : Set V) := heq ▸ hy
    simpa using this
  have hN' : ∀ y, G.Adj x y → y = q ∨ y = m ∨ y = p := by
    intro y h; rcases hN y h with h | h | h <;> simp [h]
  have hNm' : ∀ y, G.Adj m y → y = x ∨ y = q ∨ y = p := by
    intro y h; rcases hNm y h with h | h | h <;> simp [h]
  exact diam_deg hδ hN hNm hpq hpq' (G.ne_of_adj hxp).symm (G.ne_of_adj hpm)
    (G.ne_of_adj hxq).symm (G.ne_of_adj hmq).symm
    (side hδ hC hN hNm hxp hxm hpm hpq)
    (side hδ hC hN' hNm' hxq hxm hmq.symm (fun h => hpq h.symm))

end DiracK4

namespace DiracK4
open HadwigerConj SimpleGraph

lemma del_deg {V : Type*} [Finite V] {G : SimpleGraph V} {u v : V} (huv : G.Adj u v)
    (hδ : ∀ y, 3 ≤ (G.neighborSet y).ncard)
    (hu : 4 ≤ (G.neighborSet u).ncard) (hv : 4 ≤ (G.neighborSet v).ncard) :
    ∀ y, 3 ≤ ((G.deleteEdges {s(u, v)}).neighborSet y).ncard := by
  have huv' := G.ne_of_adj huv
  intro y
  by_cases hyu : y = u
  · subst hyu
    have e := Set.ncard_sdiff_singleton_of_mem (show v ∈ G.neighborSet y from huv)
    refine (by omega : 3 ≤ (G.neighborSet y \ {v}).ncard).trans
      (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro t ⟨ht1, ht2⟩
    simp only [Set.mem_singleton_iff] at ht2
    simp only [mem_neighborSet, deleteEdges_adj, Set.mem_singleton_iff]
    refine ⟨ht1, ?_⟩
    rw [Sym2.eq_iff]; rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact ht2 h
    · exact huv' h
  by_cases hyv : y = v
  · subst hyv
    have e := Set.ncard_sdiff_singleton_of_mem (show u ∈ G.neighborSet y from huv.symm)
    refine (by omega : 3 ≤ (G.neighborSet y \ {u}).ncard).trans
      (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro t ⟨ht1, ht2⟩
    simp only [Set.mem_singleton_iff] at ht2
    simp only [mem_neighborSet, deleteEdges_adj, Set.mem_singleton_iff]
    refine ⟨ht1, ?_⟩
    rw [Sym2.eq_iff]; rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact huv' h.symm
    · exact ht2 h
  · refine (hδ y).trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    intro t ht
    simp only [mem_neighborSet, deleteEdges_adj, Set.mem_singleton_iff]
    refine ⟨ht, ?_⟩
    rw [Sym2.eq_iff]; rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact hyu h
    · exact hyv h

theorem dirac : ∀ (n : ℕ) (V : Type) [Finite V] [Nonempty V] (G : SimpleGraph V),
    Nat.card V = n → (∀ y, 3 ≤ (G.neighborSet y).ncard) → HasCompleteMinor G 4 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro V _ _ G hn
  suffices ∀ k (G : SimpleGraph V), G.edgeSet.ncard = k →
      (∀ y, 3 ≤ (G.neighborSet y).ncard) → HasCompleteMinor G 4 from this _ G rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro G hk hδ
  by_contra hno
  have hD : ∀ u v, G.Adj u v → 4 ≤ (G.neighborSet u).ncard → (G.neighborSet v).ncard < 4 := by
    intro u v huv hu
    by_contra hv; push Not at hv
    apply hno
    refine minor_trans (ihk _ ?_ (G.deleteEdges {s(u, v)}) rfl (del_deg huv hδ hu hv))
      (minor_of_le (G.deleteEdges_le _))
    rw [← hk, edgeSet_deleteEdges]
    exact Set.ncard_sdiff_singleton_lt_of_mem huv (Set.toFinite _)
  have hC : ∀ u v, G.Adj u v → (∃ w, G.Adj u w ∧ G.Adj v w ∧ (G.neighborSet w).ncard < 4) ∨
      ((G.neighborSet u ∪ G.neighborSet v) \ {u, v}).ncard < 3 := by
    intro u v huv
    by_contra h
    push Not at h
    apply hno
    have hlt : Nat.card {y // y ≠ v} < n := hn ▸ Finite.card_subtype_lt (x := v) (by simp)
    have : Nonempty {y // y ≠ v} := ⟨⟨u, G.ne_of_adj huv⟩⟩
    exact minor_trans (ihn _ hlt {y // y ≠ v} (contr G u v) rfl
      (contr_deg huv hδ (fun w h1 h2 => h.1 w h1 h2) h.2)) (contr_minor huv)
  -- a vertex of degree 3
  obtain ⟨x, hx⟩ : ∃ x, (G.neighborSet x).ncard = 3 := by
    obtain ⟨y0⟩ := ‹Nonempty V›
    by_cases h : (G.neighborSet y0).ncard < 4
    · exact ⟨y0, by have := hδ y0; omega⟩
    · obtain ⟨z, hz⟩ := Set.nonempty_of_ncard_ne_zero (s := G.neighborSet y0)
        (by have := hδ y0; omega)
      have := hD y0 z hz (by omega)
      exact ⟨z, by have := hδ z; omega⟩
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ := Set.ncard_eq_three.1 hx
  have hxa : G.Adj x a := show a ∈ G.neighborSet x by rw [hN]; simp
  have hxb : G.Adj x b := show b ∈ G.neighborSet x by rw [hN]; simp
  have hxc : G.Adj x c := show c ∈ G.neighborSet x by rw [hN]; simp
  have hNx : ∀ y, G.Adj x y → y = a ∨ y = b ∨ y = c := by
    intro y h
    have : y ∈ G.neighborSet x := h
    rw [hN] at this; simpa using this
  have dia : ∀ p m q, (∀ y, G.Adj x y → y = p ∨ y = m ∨ y = q) → G.Adj x p → G.Adj x m →
      G.Adj x q → G.Adj p m → G.Adj m q → ¬ G.Adj p q → p ≠ q → False := by
    intro p m q hN' hxp hxm hxq hpm hmq hpq hpq'
    apply hno
    have hlt : Nat.card {y // y ≠ x ∧ y ≠ m} < n :=
      hn ▸ Finite.card_subtype_lt (x := x) (by simp)
    have : Nonempty {y // y ≠ x ∧ y ≠ m} := ⟨⟨p, (G.ne_of_adj hxp).symm, G.ne_of_adj hpm⟩⟩
    exact minor_trans (ihn _ hlt _ (diam G x m p q) rfl
      (diamond_step hδ hC hN' hxp hxm hxq hpm hmq hpq hpq'))
      (diam_minor hxp.symm hmq.symm hxm hpq')
  have nb := fun t (h : G.Adj x t) => nbr_in hδ hC h hx
  obtain ⟨sa, hsa1, hsa2⟩ := nb a hxa
  obtain ⟨sb, hsb1, hsb2⟩ := nb b hxb
  obtain ⟨sc, hsc1, hsc2⟩ := nb c hxc
  have ha' : G.Adj a b ∨ G.Adj a c := by
    rcases hNx sa hsa1 with rfl | rfl | rfl
    · exact absurd hsa2 (G.loopless.irrefl _)
    · exact Or.inl hsa2
    · exact Or.inr hsa2
  have hb' : G.Adj a b ∨ G.Adj b c := by
    rcases hNx sb hsb1 with rfl | rfl | rfl
    · exact Or.inl hsb2.symm
    · exact absurd hsb2 (G.loopless.irrefl _)
    · exact Or.inr hsb2
  have hc' : G.Adj a c ∨ G.Adj b c := by
    rcases hNx sc hsc1 with rfl | rfl | rfl
    · exact Or.inl hsc2.symm
    · exact Or.inr hsc2.symm
    · exact absurd hsc2 (G.loopless.irrefl _)
  by_cases e1 : G.Adj a b <;> by_cases e2 : G.Adj b c <;> by_cases e3 : G.Adj a c
  · exact hno (k4_of_triangle hxa hxb hxc e1 e2 e3)
  · exact dia a b c hNx hxa hxb hxc e1 e2 e3 hac
  · exact dia b a c (fun y h => by rcases hNx y h with h | h | h <;> simp [h])
      hxb hxa hxc e1.symm e3 e2 hbc
  · tauto
  · exact dia a c b (fun y h => by rcases hNx y h with h | h | h <;> simp [h])
      hxa hxc hxb e3 e2.symm e1 hab
  all_goals tauto

end DiracK4

open HadwigerConj in
theorem exists_degree_le_two_of_no_K4_minor {V : Type} [Finite V] [Nonempty V]
    (G : SimpleGraph V) (hG : ¬ HasCompleteMinor G 4) :
    ∃ v : V, (G.neighborSet v).ncard ≤ 2 := by
  by_contra h
  push Not at h
  exact hG (DiracK4.dirac _ V G rfl fun y => h y)


open HadwigerConj

theorem colorable_of_isDegenerate {V : Type} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : IsDegenerate G k) : G.Colorable (k + 1) := by
  classical
  have key : ∀ (n : ℕ) (s : Finset V), s.card = n →
      ∃ c : V → Fin (k + 1), ∀ u ∈ s, ∀ w ∈ s, G.Adj u w → c u ≠ c w := by
    intro n
    induction n with
    | zero =>
      intro s _
      exact ⟨fun _ => 0, fun u hu w hw h => by simp_all⟩
    | succ n ih =>
      intro s hs
      have hne : (s : Set V).Nonempty := by
        rw [Finset.coe_nonempty, ← Finset.card_pos]; omega
      obtain ⟨v, hv, hdeg⟩ := hG _ hne
      obtain ⟨c, hc⟩ := ih (s.erase v) (by rw [Finset.card_erase_of_mem hv]; omega)
      -- the set of colours used on neighbours of `v` in `s`
      set N : Finset V := s.filter (fun u => G.Adj v u) with hN
      have hNcard : N.card ≤ k := by
        have : (N : Set V) = G.neighborSet v ∩ (s : Set V) := by
          ext u; simp [hN, and_comm]
        rw [← Set.ncard_coe_finset, this]; exact hdeg
      have himg : (N.image c).card < (Finset.univ : Finset (Fin (k + 1))).card := by
        calc (N.image c).card ≤ N.card := Finset.card_image_le
          _ ≤ k := hNcard
          _ < k + 1 := Nat.lt_succ_self k
          _ = _ := by simp
      obtain ⟨col, -, hcol⟩ := Finset.exists_mem_notMem_of_card_lt_card himg
      refine ⟨Function.update c v col, ?_⟩
      have hfree : ∀ u ∈ s, G.Adj v u → c u ≠ col := by
        intro u hu hadj heq
        exact hcol (Finset.mem_image.mpr ⟨u, by simp [hN, hu, hadj], heq⟩)
      intro u hu w hw hadj
      by_cases huv : u = v
      · subst huv
        have hwv : w ≠ u := fun h => by subst h; exact G.irrefl hadj
        rw [Function.update_self, Function.update_of_ne hwv]
        exact fun h => hfree w hw hadj h.symm
      · by_cases hwv : w = v
        · subst hwv
          rw [Function.update_self, Function.update_of_ne huv]
          exact hfree u hu hadj.symm
        · rw [Function.update_of_ne huv, Function.update_of_ne hwv]
          exact hc u (Finset.mem_erase.mpr ⟨huv, hu⟩) w (Finset.mem_erase.mpr ⟨hwv, hw⟩) hadj
  have := Fintype.ofFinite V
  obtain ⟨c, hc⟩ := key _ Finset.univ rfl
  exact ⟨SimpleGraph.Coloring.mk c (fun {u w} h => hc u (Finset.mem_univ _) w (Finset.mem_univ _) h)⟩


namespace HDRed
open HadwigerConj SimpleGraph

lemma sing {V : Type} (G : SimpleGraph V) (v : V) : (G.induce {v}).Connected := by
  have := (Walk.nil : G.Walk v v).connected_induce_support
  have e : {y | y ∈ (Walk.nil : G.Walk v v).support} = {v} := by ext; simp
  rwa [e] at this

/-- A vertex gives a `K₁` minor. -/
lemma k1 {V : Type} (G : SimpleGraph V) (v : V) : HasCompleteMinor G 1 := by
  refine ⟨fun _ => {v}, fun _ => ?_, fun a b h => absurd (Subsingleton.elim a b) h, fun a b h => ?_⟩
  · exact sing G v
  · exact absurd (Subsingleton.elim a b) (by simpa using h)

/-- An edge gives a `K₂` minor. -/
lemma k2 {V : Type} (G : SimpleGraph V) {u v : V} (h : G.Adj u v) : HasCompleteMinor G 2 := by
  refine ⟨![{u}, {v}], fun i => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  · fin_cases i <;> exact sing G _
  · have := G.ne_of_adj h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  · fin_cases a <;> fin_cases b <;> simp_all [h.symm]

/-- A cycle gives a `K₃` minor. -/
lemma k3 {V : Type} (G : SimpleGraph V) (hG : ¬ G.IsAcyclic) : HasCompleteMinor G 3 := by
  simp only [IsAcyclic, not_forall, not_not] at hG
  obtain ⟨u, c, hc⟩ := hG
  cases c with
  | nil => exact absurd hc (Walk.not_isCycle_nil)
  | @cons _ v1 _ h p =>
    rw [Walk.cons_isCycle_iff] at hc
    obtain ⟨hp, hne⟩ := hc
    have hpr : p.reverse.IsPath := hp.reverse
    cases hq : p.reverse with
    | nil =>
      exact absurd (G.ne_of_adj h) (by simp)
    | @cons _ w _ h' r =>
      rw [hq] at hpr
      have hr : r.IsPath := hpr.of_cons
      have hu : u ∉ r.support := (Walk.cons_isPath_iff _ _).1 hpr |>.2
      cases r with
      | nil =>
        -- p is the single edge v1 u, contradicting s(u,v1) ∉ p.edges
        exfalso; apply hne
        have : p = (Walk.cons h' Walk.nil).reverse := by rw [← hq, Walk.reverse_reverse]
        subst this; simp [Sym2.eq_swap]
      | @cons _ x _ hwx r' =>
        have hw : w ∉ r'.support := (Walk.cons_isPath_iff _ _).1 hr |>.2
        have hu' : u ≠ w ∧ u ∉ r'.support := by simpa using hu
        refine ⟨![{u}, {w}, {y | y ∈ r'.support}], fun i => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
        · fin_cases i
          · exact sing G _
          · exact sing G _
          · exact r'.connected_induce_support
        · rw [Set.disjoint_iff]
          fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
        · fin_cases a <;> fin_cases b <;> simp at hab ⊢
          · exact h'
          · exact ⟨v1, r'.end_mem_support, h⟩
          · exact h'.symm
          · exact ⟨x, r'.start_mem_support, hwx⟩
          · exact ⟨v1, r'.end_mem_support, h.symm⟩
          · exact ⟨x, r'.start_mem_support, hwx.symm⟩

/-- A complete minor of an induced subgraph lifts. -/
lemma lift {V : Type} (G : SimpleGraph V) (S : Set V) (t : ℕ)
    (h : HasCompleteMinor (G.induce S) t) : HasCompleteMinor G t := by
  obtain ⟨B, hc, hd, ha⟩ := h
  refine ⟨fun w => Subtype.val '' B w, fun w => ?_, fun a b hab => ?_, fun a b hab => ?_⟩
  · let f : (G.induce S).induce (B w) →g G.induce (Subtype.val '' B w) :=
      { toFun := fun y => ⟨y.1.1, y.1, y.2, rfl⟩
        map_rel' := fun {a b} hab => by simpa using hab }
    refine (hc w).map f ?_
    rintro ⟨y, z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, rfl⟩
  · exact (Set.disjoint_image_iff Subtype.val_injective).2 (hd a b hab)
  · obtain ⟨u, hu, v, hv, huv⟩ := ha a b hab
    exact ⟨u.1, ⟨u, hu, rfl⟩, v.1, ⟨v, hv, rfl⟩, huv⟩

lemma degen {V : Type} [Finite V] (G : SimpleGraph V) (hG : ¬ HasCompleteMinor G 4) :
    IsDegenerate G 2 := by
  intro S hS
  have : Nonempty S := hS.to_subtype
  have h4 : ¬ HasCompleteMinor (G.induce S) 4 := fun h => hG (lift G S 4 h)
  obtain ⟨v, hv⟩ := exists_degree_le_two_of_no_K4_minor (G.induce S) h4
  refine ⟨v.1, v.2, ?_⟩
  have : G.neighborSet v.1 ∩ S = Subtype.val '' (G.induce S).neighborSet v := by
    ext y; constructor
    · rintro ⟨hy, hyS⟩; exact ⟨⟨y, hyS⟩, by simpa using hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨by simpa using hz, z.2⟩
  rw [this, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact hv

end HDRed

open HadwigerConj SimpleGraph in
theorem hc_of_le_three (t : ℕ) (ht : t ≤ 3) : HC t := by
  intro V _ G hG
  interval_cases t
  · have : IsEmpty V := ⟨fun v => hG (HDRed.k1 G v)⟩
    exact Colorable.of_isEmpty 0
  · refine ⟨Coloring.mk (fun _ => 0) fun {u v} h => absurd (HDRed.k2 G h) hG⟩
  · exact (by_contra fun hA => hG (HDRed.k3 G hA) : G.IsAcyclic).colorable_two
  · exact colorable_of_isDegenerate G 2 (HDRed.degen G hG)

namespace Submission

open SimpleGraph HadwigerConj

lemma no_K4_minor_of_hadwigerNumber_le_three {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : hadwigerNumber G ≤ 3) : ¬ HasCompleteMinor G 4 := by
  classical
  rintro ⟨B, hconn, hdisj, hadj⟩
  have hne : ∀ i : Fin 4, (B i).Nonempty := by
    intro i
    obtain ⟨⟨v, hv⟩⟩ := (hconn i).nonempty
    exact ⟨v, hv⟩
  choose f hf using hne
  have hfinj : Function.Injective f := by
    intro i j hij
    by_contra hne_ij
    exact Set.disjoint_left.mp (hdisj i j hne_ij) (hf i) (hij ▸ hf j)
  have hcard : 4 ≤ Fintype.card V := by
    simpa using Fintype.card_le_of_injective f hfinj
  have hminor : Nonempty (Minor (completeGraph (Fin 4)) G) := by
    refine ⟨{
      branchSet := B
      pairwise_disjoint_branchSet := fun i j hij => hdisj i j hij
      connectedOn_branchSet := hconn
      exists_mem_branchSet_of_adj := fun i j hij => hadj i j hij
    }⟩
  have hle : 4 ≤ hadwigerNumber G := by
    unfold hadwigerNumber
    exact Nat.le_findGreatest hcard hminor
  omega

theorem challenge_1_proof : ∀ {V : Type*} [Fintype V] (G : SimpleGraph V), hadwigerNumber G ≤ 3 → G.Colorable 3 := by
  intro V _ G hG
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let G' : SimpleGraph (Fin (Fintype.card V)) := G.map e.toEmbedding
  have hno4 : ¬ HasCompleteMinor G 4 := no_K4_minor_of_hadwigerNumber_le_three G hG
  have hno4' : ¬ HasCompleteMinor G' 4 := by
    rintro ⟨B, hconn, hdisj, hadj⟩
    apply hno4
    refine ⟨fun i => e.symm '' B i, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
    · let f_hom : G'.induce (B i) →g G.induce (e.symm '' B i) :=
        ⟨fun y => ⟨e.symm y.1, y.1, y.2, rfl⟩, fun {a b} hab => by
          change G.Adj (e.symm a.1) (e.symm b.1)
          obtain ⟨_, u, v, huv, ha, hb⟩ := hab
          have hu : u = e.symm a.1 := e.apply_eq_iff_eq_symm_apply.mp ha
          have hv : v = e.symm b.1 := e.apply_eq_iff_eq_symm_apply.mp hb
          rwa [← hu, ← hv]⟩
      refine (hconn i).map f_hom ?_
      rintro ⟨y, z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · exact (Set.disjoint_image_iff e.symm.injective).mpr (hdisj i j hij)
    · obtain ⟨u, hu, v, hv, huv⟩ := hadj i j hij
      obtain ⟨_, u0, v0, huv0, rfl, rfl⟩ := huv
      exact ⟨u0, ⟨e u0, hu, by simp⟩, v0, ⟨e v0, hv, by simp⟩, huv0⟩
  have hcol' : G'.Colorable 3 := hc_of_le_three 3 (by decide) (Fin (Fintype.card V)) G' hno4'
  obtain ⟨c'⟩ := hcol'
  refine ⟨SimpleGraph.Coloring.mk (fun v => c' (e v)) ?_⟩
  intro u v huv
  apply c'.valid
  change (G.map e.toEmbedding).Adj (e u) (e v)
  exact ⟨e.injective.ne (G.ne_of_adj huv), u, v, huv, rfl, rfl⟩

end Submission
