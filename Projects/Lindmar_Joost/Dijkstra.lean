import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric

inductive BinaryTree (α : Type u)
  | leaf : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α

structure BinaryHeap (α : Type u) where
  tree : BinaryTree α

namespace BinaryHeap

def empty {α : Type u} : BinaryHeap α := { tree := BinaryTree.leaf }
set_option linter.unusedVariables false
def add {α : Type u} (h : BinaryHeap α) (v : α) (priority : Nat) : BinaryHeap α := sorry
noncomputable def extract_min {α : Type u} [Nonempty α] (h : BinaryHeap α) : (α × BinaryHeap α) :=sorry

def sizeOf {α : Type u} (h : BinaryHeap α) : Nat := sorry
def isEmpty {α : Type u} (h : BinaryHeap α) : Bool := sorry
def decrease_priority (h : BinaryHeap α) (v : α) (n : ENat) : BinaryHeap α := sorry

-- Helper lemma: decreasing priority does not increase heap size
theorem sizeOf_decrease_priority_le {α : Type u} (h : BinaryHeap α) (v : α) (n : ENat) :
  sizeOf (decrease_priority h v n) ≤ sizeOf h := by
  -- To be proved from the concrete heap implementation
  sorry

-- Helper lemma: extracting the minimum from a non-empty heap strictly decreases its size.
theorem sizeOf_extract_min_lt_of_isEmpty_eq_false
    {V : Type*} [Nonempty V] (h : BinaryHeap V) (hNE : h.isEmpty = false) :
    sizeOf (Prod.snd (extract_min h)) < sizeOf h := by
  -- To be proved from the concrete heap implementation
  sorry


end BinaryHeap

structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance  fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)


open Finset SimpleGraph BinaryHeap

variable  {V : Type*} [Fintype V] [DecidableEq V]



noncomputable def relaxNeighbors (g : FinSimpleGraph V) (u : V) (dist : V → ENat) (queue : BinaryHeap V) : (V → ENat) × (BinaryHeap V) :=
  List.foldl
    (fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
      let (dist, queue) := acc
      let alt := dist u + 1
      if alt < dist v then
        let dist' : V → ENat := fun x => if x = v then alt else dist x
        let queue' := queue.decrease_priority v alt
        (dist', queue')
      else
        (dist, queue)
    )
    (dist, queue)
    (g.neighborFinset u).val.toList

theorem sizeOf_relaxNeighbors_le
    (g : FinSimpleGraph V) (u : V) (dist : V → ENat) (q : BinaryHeap V) :
    BinaryHeap.sizeOf (Prod.snd (relaxNeighbors g u dist q)) ≤ BinaryHeap.sizeOf q := by
  -- Proof by induction on the list of neighbors
  let neighbors := (g.neighborFinset u).val.toList
  let f := fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
    let (dist, queue) := acc
    let alt := dist u + 1
    if alt < dist v then
      let dist' : V → ENat := fun x => if x = v then alt else dist x
      let queue' := queue.decrease_priority v alt
      (dist', queue')
    else
      (dist, queue)
  -- Induction on neighbors
  induction neighbors generalizing dist q with
  | nil =>
    simp [relaxNeighbors]
    exact le_refl _
  | cons v vs ih =>
    simp [relaxNeighbors]
    specialize ih
    cases acc : f (dist, q) v with
    | mk dist' queue' =>
      have hle : BinaryHeap.sizeOf queue' ≤ BinaryHeap.sizeOf q := by
        -- If decrease_priority is called, use its lemma
        dsimp [f] at acc
        split at acc
        case isTrue h =>
          -- decrease_priority branch
          injection acc with h_dist h_queue
          subst h_queue
          apply sizeOf_decrease_priority_le
        case isFalse h =>
          -- else branch, queue unchanged
          injection acc with h_dist h_queue
          subst h_queue
          exact le_refl _
      calc
        BinaryHeap.sizeOf (Prod.snd (List.foldl f (dist', queue') vs)) ≤ BinaryHeap.sizeOf queue'
          := ih dist' queue'
        _ ≤ BinaryHeap.sizeOf q := hle


#check ENat

noncomputable def dijkstra_rec [Nonempty V] (g: FinSimpleGraph V) (source : V) (target : V) (dist : V → ENat) (queue : BinaryHeap V) : V → ENat :=
  if queue.isEmpty then dist
  else
    let (u, queue') := queue.extract_min
    let (dist', queue'') := relaxNeighbors g u dist queue'
    dijkstra_rec g source target dist' queue''
termination_by BinaryHeap.sizeOf queue
decreasing_by
  apply BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false
  simp only [*]



noncomputable def dijkstra [Nonempty V] (g : FinSimpleGraph V) (source : V) (target : V) : V → ENat  :=
  let dist : V → ENat := fun v => if v = source then 0 else ⊤ -- distance map
  let queue := BinaryHeap.empty.add source 0 -- initialize BinaryHeap with source at priority 0
  dijkstra_rec g source target dist queue

/-!
Correctness of Dijkstra's algorithm on unweighted graphs.
We state the theorem using the graph distance from Mathlib (`SimpleGraph.dist`).
The proof will be provided once the BinaryHeap operations and termination are fully implemented.
-/

noncomputable def delta (g : FinSimpleGraph V) (s v : V) : Nat :=
  (SimpleGraph.dist (G := (by exact g.toSimpleGraph)) s v)


/-!
Helper lemmas capturing standard Dijkstra invariants and
shortest-path structure. Implementations are deferred (`sorry`) so we
can focus on the main proof structure. These can be discharged once the
BinaryHeap and queue semantics are fully formalized.
-/



-- If there is a counterexample, pick one with minimal δ(s,·).
-- Returns `u` with `dist u ≠ δ(s,u)` and the minimality certificate.
lemma minimalCounterexample
  [Nonempty V]
  (g : FinSimpleGraph V) (s : V)
  (dist : V → ENat)
  (h : ∃ u, dist u ≠ delta g s u) :
  ∃ u, dist u ≠ delta g s u ∧ ∀ w, delta g s w < delta g s u → dist w = delta g s w := by
  -- Consider the finite set of counterexamples
  let S : Finset V := (Finset.univ.filter (fun u => dist u ≠ delta g s u))
  have hS_ne : S.Nonempty := by
    rcases h with ⟨u, hu⟩
    refine Finset.nonempty_of_ne_empty ?hcontr
    intro h_empty
    have : u ∈ S := by
      -- u is in univ and satisfies the predicate
      have : u ∈ Finset.univ := by simp
      have : u ∈ Finset.univ.filter (fun u => dist u ≠ delta g s u) := by
        simp [hu]-- using Finset.mem_filter.2 ⟨by simp, hu⟩
      exact this
    -- Contradiction with S empty
    simpa [h_empty] --using this
  -- Pick u in S minimizing δ(s,·)
  obtain ⟨u, huS, hmin⟩ := Finset.exists_min_image S (fun x : V => delta g s x) (by
    -- S is nonempty
    rcases hS_ne with ⟨x, hx⟩; exact ⟨x, hx⟩)
  -- From membership, get that u is indeed a counterexample
  have hu_ne : dist u ≠ delta g s u := by
    -- Unfold membership in filter
    have : u ∈ Finset.univ ∧ dist u ≠ delta g s u := by
      simpa [S] using (Finset.mem_filter.mp huS)
    exact this.2
  -- Show minimality property: any w closer than u cannot be a counterexample
  refine ⟨u, hu_ne, ?hcloser⟩
  intro w hw_lt
  -- Suppose, for contradiction, that w is also a counterexample.
  by_contra h_w_ne
  have hwS : w ∈ S := by
    have : w ∈ Finset.univ := by simp
    have : w ∈ Finset.univ.filter (fun u => dist u ≠ delta g s u) := by
      simp [h_w_ne] --using Finset.mem_filter.2 ⟨by simp, h_w_ne⟩
    exact this
  -- From minimality, δ(s,u) ≤ δ(s,w)
  have hmin_le : delta g s u ≤ delta g s w := hmin w hwS
  exact (not_le_of_gt hw_lt) hmin_le



-- Dijkstra never underestimates the true graph distance.
lemma neverUnderestimates
  [Nonempty V]
  (g : FinSimpleGraph V) (s t : V) :
  ∀ u : V, (delta g s u : ENat) ≤ (dijkstra g s t) u := by
  intro u; sorry

-- For a genuine counterexample `u`, the distance from `s` must be positive
-- (i.e., `u ≠ s`). Otherwise initialization already matches.
lemma positiveDistance_of_counterexample
  [Nonempty V]
  (g : FinSimpleGraph V) (s t : V) (dist : V → ENat)
  (u : V) (hu : dist u ≠ delta g s u) (u_ne_s : u ≠ s) :
  0 < delta g s u := by
  -- If `u ≠ s` then `δ(s,u) ≠ 0` because `dist s u = 0 ↔ u = s`.
  unfold delta
  simp_all
  refine Nat.pos_of_ne_zero ?_
  intro hzero
  -- `hzero : delta g s u = 0` implies `u = s` by Mathlib's lemma, contradiction.
  have := (SimpleGraph.Reachable.dist_eq_zero_iff (G := g.toSimpleGraph) (u := s) (v := u))
  sorry





-- Along an edge, distances step by at most 1 (ENat form), problem is we need acyclicty for this
lemma delta_adj_step_ENat
  (g : FinSimpleGraph V) (s u v : V)
  (hAdj : g.toSimpleGraph.Adj u v) :
  (delta g s v : ENat) ≤ (delta g s u : ENat) + 1 := by
  classical
  -- Work in Nat first, then cast to ENat.
  have h_nat : delta g s v ≤ delta g s u + 1 := by
    unfold delta
    -- Distance to an adjacent node increases by at most 1
    have h:= (SimpleGraph.Adj.diff_dist_adj (G := g.toSimpleGraph) (u := s) (v := u) (w := v) hAdj)
    simp [*]
    grind
  exact_mod_cast h_nat


-- On any shortest path from `s` to `u`, there exists a predecessor `y`
-- adjacent to `u` with the distance stepping by one.
lemma existsPredOnShortestPath
  (g : FinSimpleGraph V) (s u : V)
  (hpos : 0 < delta g s u) :
  ∃ y : V, g.toSimpleGraph.Adj y u ∧ delta g s u = delta g s y + 1 := by
  /-
  Conceptual proof:
  Take a shortest walk `p : Walk s u` with `p.length = δ(s,u)`.
  Reverse it to `pᵣ : Walk u s`. Since `δ(s,u) > 0`, `pᵣ` is of the
  form `cons (Adj u y) q` for some `y` and tail walk `q : Walk y s`.
  Then `δ(s,y) ≤ q.length` (because distance is minimal), hence
  `δ(s,y)+1 ≤ q.length+1 = pᵣ.length = δ(s,u)`. Conversely, the edge
  `(y,u)` gives `δ(s,u) ≤ δ(s,y)+1`. Therefore `δ(s,u) = δ(s,y)+1`.
  -/
  classical
  -- Reachability follows from positive distance.
  have hconn : SimpleGraph.Reachable g.toSimpleGraph s u := by
    -- `delta g s u` is a natural number; positivity implies nonzero distance and thus reachability.
    exact SimpleGraph.Reachable.of_dist_ne_zero (by
      -- `of_dist_ne_zero` expects `dist s u ≠ 0`.
      simpa [delta] using (Nat.ne_of_gt hpos))
  -- Pick a shortest walk `p` from `s` to `u`.
  obtain ⟨p, hp⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist hconn
  -- Work with the reversed walk `pᵣ : Walk u s` to expose the last edge.
  -- Case-analyse `p.reverse` directly so the `tail` from the `cons`
  -- branch is definitionally the tail of `p.reverse` (avoids `rfl` issues).
  have hlen_pr : (p.reverse).length = delta g s u := by
    -- `length (reverse p) = length p = dist s u = δ(s,u)`.
    have h := SimpleGraph.Walk.length_reverse p
    have : (p.reverse).length = p.length := by simp
    simpa [delta, this] using hp
  -- Since `δ(s,u) > 0`, the reversed walk is non-empty and thus a `cons`.
  have hnonzero : (p.reverse).length ≠ 0 := by
    simpa [hlen_pr] using (Nat.ne_of_gt hpos)
    -- Decompose `p.reverse` into its first edge and tail.
    -- Use an equation binder so we keep the definitional equality
    -- `hpr : p.reverse = Walk.cons hAdj tail` in the `cons` branch.
  cases hpr : p.reverse with
    | nil =>
      simp_all
    | cons hAdj tail =>
    -- Here, `hAdj : g.toSimpleGraph.Adj u y` for the start vertex `y` of `tail : Walk y s`.
    -- Name the implicit start vertex of `tail` as `y`.
    rename_i y
    -- Define pr as the reverse for convenience and record length facts.
    let pr := p.reverse
    have hlen_pr : pr.length = delta g s u := by
      have h := SimpleGraph.Walk.length_reverse p
      have : pr.length = p.length := by simp [pr]
      simpa [delta, this] using hp
    have hnonzero : pr.length ≠ 0 := by
      simpa [hlen_pr] using (Nat.ne_of_gt hpos)
    -- We will witness `y` as the predecessor.
    refine ⟨y, SimpleGraph.Adj.symm hAdj, ?_⟩
    -- First inequality: `δ(s,y) + 1 ≤ δ(s,u)` via `tail.length` and `length_cons`.
    have hy_le_tail : delta g s y ≤ tail.length := by
      -- For `tail : Walk y s`, the distance from s to y is at most the length of this walk (by definition of distance).
      -- delta g s y = dist s y = dist y s (by symmetry)
      -- dist y s ≤ tail.length by definition of dist as the infimum of walk lengths.
      rw [delta, SimpleGraph.dist_comm]
      simp_all
      exact dist_le tail
    have hlen_cons : pr.length = tail.length + 1 := by
      -- Avoid `simp [pr]` which can further simplify `(p.reverse).length` to `p.length`.
      -- Instead explicitly change the goal to `(p.reverse).length = _` so `rw [hpr]` matches.
      change (p.reverse).length = tail.length + 1
      rw [hpr]
      rw [SimpleGraph.Walk.length_cons]


    have h_le : delta g s y + 1 ≤ delta g s u := by
      -- δ(s,y) ≤ tail.length, so δ(s,y)+1 ≤ tail.length+1 = pr.length = δ(s,u).
      calc
        delta g s y + 1 ≤ tail.length + 1 := by apply Nat.add_le_add_right; exact hy_le_tail
        _ = pr.length := by rw [hlen_cons]
        _ = delta g s u := by rw [hlen_pr]
    -- Second inequality: `δ(s,u) ≤ δ(s,y) + 1` via adjacency `(y,u)`.
    have h_ge : delta g s u ≤ delta g s y + 1 := by
      -- Use the standard distance step along an edge.
      have := SimpleGraph.Adj.diff_dist_adj (G := g.toSimpleGraph) (u := s) (v := y) (w := u) (SimpleGraph.Adj.symm hAdj)
      simp_all [delta]
      cases this
      · simp_all
      · expose_names
        cases h
        · simp_all
        · expose_names
          rw [h]
          grind
    -- Conclude equality.
    exact Nat.le_antisymm h_ge h_le



-- Relaxation of an edge (y,u) yields, in the final map, the bound
-- `dist[u] ≤ dist[y] + 1`. This uses that when `y` is extracted, its
-- value is final and the relax step is applied.
lemma relaxAdj_final_bound
  [Nonempty V]
  (g : FinSimpleGraph V) (s t : V)
  {y u : V} (hAdj : g.toSimpleGraph.Adj y u) :
  (dijkstra g s t) u ≤ (dijkstra g s t) y + 1 := by
  -- This is a standard Dijkstra invariant: when y is extracted, its distance is final,
  -- and relaxing (y, u) ensures the final value for u is at most dist[y] + 1.
  -- The proof relies on the fact that after y is extracted, dist y = (dijkstra g s t) y,
  -- and the only way u can be updated is via y (since all shorter paths have been finalized).
  -- The main proof is by induction on the execution of dijkstra_rec, but here we just state the invariant.
  -- A full formal proof would require a detailed simulation of the queue and extraction process.
  -- For now, we leave this as a placeholder for the main algorithmic invariant.
  admit


/-!
Additional helper lemmas used for invariants. The adjacency and
distance-step facts are stated against Mathlib's graph metric and
can be proved from `SimpleGraph` API; we leave them as `sorry` here
to focus on an easy-to-prove algorithmic invariant below.
-/

-- Membership in neighborFinset implies adjacency (wrapper lemma).
lemma mem_neighborFinset_adj
  (g : FinSimpleGraph V) (u v : V)
  (h : v ∈ g.neighborFinset u) : g.toSimpleGraph.Adj u v := by
  classical
  -- Convert membership to the underlying SimpleGraph, then use the
    -- Convert membership to the underlying SimpleGraph and use the
    -- equivalence between neighborFinset membership and adjacency.
    have hv : v ∈ (g.toSimpleGraph).neighborFinset u := by simpa using h
    have hEquiv := SimpleGraph.mem_neighborFinset (G := g.toSimpleGraph) (v := u) (w := v)
    exact hEquiv.mp hv


-- Relaxing neighbors preserves the global lower bound `δ ≤ dist`.
lemma relaxNeighbors_preserves_lowerBound
  (g : FinSimpleGraph V) (s u : V)
  (dist : V → ENat) (q : BinaryHeap V)
  (LB : ∀ x, (delta g s x : ENat) ≤ dist x) :
  ∀ x, (delta g s x : ENat) ≤ (Prod.fst (relaxNeighbors g u dist q)) x := by
  classical
  intro x
  -- Unfold and perform induction over the neighbor list of `u`.
  let neighbors := (g.neighborFinset u).val.toList
  let f := fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
    let (dist, queue) := acc
    let alt := dist u + 1
    if alt < dist v then
      let dist' : V → ENat := fun x => if x = v then alt else dist x
      let queue' := queue.decrease_priority v alt
      (dist', queue')
    else
      (dist, queue)
  -- We'll show the property is preserved after folding over `neighbors`.
  -- First, a one-step helper: applying `f` to a single `v` preserves LB.
  have step_preserve : ∀ dist q v, (∀ x, (delta g s x : ENat) ≤ dist x) →
    (∀ x : V, (delta g s x : ENat) ≤ (Prod.fst (f (dist, q) v)) x) := by
    intro dist0 q0 v0 LB0 x
    -- Expand `f` at `(dist0, q0)` and `v0`.
    dsimp [f]
    set alt := dist0 u + 1 with halt
    by_cases hupd : alt < dist0 v0
    · -- Update happens only at index `v0`.
      simp [hupd]
      by_cases hx : x = v0
      · -- Show δ(s,v0) ≤ alt using adjacency and LB at `u`.
        subst hx
        have hv_mem_list : x ∈ neighbors := by
          -- By construction, v0 is in neighbors, and x = v0

          --exact List.mem_head _ _
          sorry
        -- Instead of using membership here, we derive the needed inequality
        -- at the call site. For now, we derive a bound using `LB0` and
        -- monotonicity of addition.
        -- We need `(delta g s v0 : ENat) ≤ alt`. We'll establish this
        -- later in the outer induction using adjacency; so we leave this
        -- obligation to that place by rewriting structure below.
        -- Since the local lemma cannot access adjacency, we short-circuit
        -- with a generic inequality chain placeholder. This branch will not
        -- be used directly; see main proof below where adjacency is available.
        -- To keep the lemma usable, we relax it by not requiring this case
        -- to be solved here. We'll close it using `sorry` and keep the lemma
        -- as a local scaffold.
        simp_all
        sorry
      · -- x ≠ v0, value unchanged, LB preserved.
        simpa [hupd, hx] using LB0 x
    · -- No update; map unchanged, LB preserved.
      simpa [hupd] using LB0 x
  -- Now induct over the neighbors list to fully discharge adjacency cases
  -- and obtain the global preservation.
  -- We'll perform the induction manually to have access to the head `v`.
  revert dist q
  /-
  refine
    (List.rec (motive := fun l => ∀ dist q, (∀ x: V, (delta g s x : ENat) ≤ dist x) →
      ∀ x, (delta g s x : ENat) ≤ (Prod.fst (List.foldl f (dist, q) l)) x)
      (by
        intro dist q LB x
        simp [neighbors, relaxNeighbors, f] at *
        exact LB x)
      (fun v vs ih => ?step)) neighbors
      -/
  -- Step case where the head is exactly a neighbor of `u`.
  intro dist q LB
  simp [neighbors, relaxNeighbors, f]
  -- Unfold once and analyze the head update.
  set alt := dist u + 1 with halt
  by_cases hupd : alt < dist u
  · -- Update at `v`. We need to show LB for the updated map.
    -- First, prove adjacency `Adj u v` from membership of `v` in neighbors.
    have hv_mem_list : u ∈ (g.neighborFinset u).val.toList := by simp; sorry
    have hv_mem_ms : u ∈ (g.neighborFinset u).val := by
      -- Convert list membership to multiset membership
      simpa [Multiset.mem_toList] using hv_mem_list
    have hv_mem_fin : u ∈ g.neighborFinset u := by
      -- Convert to finset membership
      exact hv_mem_ms
    have hAdj : g.toSimpleGraph.Adj u u := mem_neighborFinset_adj g u u hv_mem_fin
    -- Now show the lower bound for all x.

    by_cases hx : x = u
    · simp [hupd, hx]
      -- δ(s,v) ≤ δ(s,u)+1 ≤ dist u + 1 = alt
      have : (delta g s u : ENat) ≤ (delta g s u : ENat) + 1 :=
        delta_adj_step_ENat g s u u hAdj
      have : (delta g s u : ENat) ≤ dist u + 1 :=
        le_trans this (by simpa [halt] using add_le_add_right (LB u) 1)
      simp [halt, hupd, hx]
      have : ¬ (dist u + 1 < dist u) := by
        -- For ENat, n + 1 < n is never true
        intro h
        simp_all

      -- So the value is unchanged
      simp [this]
      -- The value at u is never updated by the fold
      have : (List.foldl
                (fun (acc : (V → ENat) × BinaryHeap V) (v : V) ↦
  if acc.1 u + 1 < acc.1 v then
    (fun x ↦ if x = v then acc.1 u + 1 else acc.1 x, acc.2.decrease_priority v (acc.1 u + 1))
  else acc)
                (dist, q) (g.neighborFinset u).val.toList).1 u = dist u := by
        -- At each step, the update for u would require dist u + 1 < dist u, which is impossible
        induction (g.neighborFinset u).val.toList with
        | nil => simp
        | cons v vs ih =>
          simp only [List.foldl]
          split_ifs
          · -- The update would only happen if acc.1 u + 1 < acc.1 v and u = v, but acc.1 u + 1 < acc.1 u is never true
            by_cases h' : u = v
            · subst h'
              --simp only [if_pos rfl]
              have : (dist u + 1 < dist u) := by expose_names; exact h
              simp_all [this]

            · simp_all
          · exact ih
      -- So the value at u is unchanged, and the lower bound is preserved
      rw [this]
      simp_all



    · -- x ≠ v: unchanged
      simp [hupd, hx]
      simp_all

  · -- No update at head; unchanged map, then recurse on tail.
    have : ∀ x, (delta g s x : ENat) ≤ dist x := LB

    -- Use induction hypothesis on the tail with the same `dist` and `q`.
    have h_tail := step_preserve dist q u this
    simp [hupd, h_tail]
    -- In the "no update" case, f (dist, q) u = (dist, q)
    have fold_eq : (List.foldl f (dist, q) (u :: vs)).1 x = (List.foldl f (dist, q) vs).1 x := by
      simp [List.foldl, f, hupd]

    -- Now apply the induction hypothesis to the tail
    rw [fold_eq]
    exact h_tail x
    sorry


-- Relaxing neighbors never changes the value at the source when it is 0.
lemma relaxNeighbors_preserves_source_zero
  (g : FinSimpleGraph V) (source u : V)
  (dist : V → ENat) (q : BinaryHeap V)
  (h0 : dist source = 0) :
  (Prod.fst (relaxNeighbors g u dist q)) source = 0 := by
  -- Induction on the neighbor list of `u`.
  let neighbors := (g.neighborFinset u).val.toList
  let f := fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
    let (dist, queue) := acc
    let alt := dist u + 1
    if alt < dist v then
      let dist' : V → ENat := fun x => if x = v then alt else dist x
      let queue' := queue.decrease_priority v alt
      (dist', queue')
    else
      (dist, queue)
  unfold relaxNeighbors
  induction neighbors generalizing dist q with
  | nil =>
    have h3: neighbors = List.nil := by sorry
    -- unfold relaxNeighbors
    simp_all [neighbors]
  | cons v vs ih =>
    simp [relaxNeighbors, f]
    --dsimp [f]
    set alt := dist u + 1 with halt
    by_cases hupd : alt < dist v
    · -- update at `v` case
      let dist' := fun x => if x = v then alt else dist x
      let q' := q.decrease_priority v alt
      by_cases hv : v = source
      · -- would require `alt < dist source = 0`, impossible
        subst hv
        have : alt < 0 := by simpa [h0] using hupd
        simp at this
      · -- source unchanged, apply IH to tail
        have hdist' : dist' source = 0 := by simp_all [hv, h0]; grind
        specialize ih dist' q' hdist'
        -- Show the head-step equals the updated accumulator, rewrite the fold, then apply IH.
        have head_eq : f (dist, q) v = (dist', q') := by
          dsimp [f]
          rw [if_pos hupd]
        -- The goal contains an explicit lambda using `Prod.fst`/`Prod.snd`.
        -- Prove this lambda equals `f` by extensionality so we can rewrite
        -- the goal to use `f` and finish with `List.foldl_cons` + `head_eq`.
        have fun_eq_f :
          (fun (acc : (V → ENat) × BinaryHeap V) (v' : V) =>
            if (Prod.fst acc) u + 1 < (Prod.fst acc) v' then
              (fun x => if x = v' then (Prod.fst acc) u + 1 else (Prod.fst acc) x,
                BinaryHeap.decrease_priority (Prod.snd acc) v' ((Prod.fst acc) u + 1))
            else acc) = f := by
          funext acc v'
          cases acc with
          | mk dist0 queue0 =>
            dsimp [f]
        -- Rewrite the explicit lambda to `f` in the goal, then use the
        -- fold-cons rewrite + `head_eq` to reduce to `ih`.
        rw [fun_eq_f]
        rw [fun_eq_f] at ih
        have hn: (g.neighborFinset u).val.toList = v :: vs := by sorry
        rw [hn]
        calc
          (List.foldl f (dist, q) (v :: vs)).1 source
            = (List.foldl f (f (dist, q) v) vs).1 source := by rw [List.foldl_cons]
          _ = (List.foldl f (dist', q') vs).1 source := by rw [head_eq]
          _ = 0 := by sorry
    · -- no update at head; proceed to tail
      have hdist_tail := ih dist q h0
      exact hdist_tail


-- The recursive Dijkstra preserves `dist source = 0`.
lemma dijkstra_rec_preserves_source_zero
  [Nonempty V]
  (g : FinSimpleGraph V) (source target : V) :
  ∀ (dist : V → ENat) (queue : BinaryHeap V), dist source = 0 → (dijkstra_rec g source target dist queue) source = 0 := by
  intro dist queue h
  -- Strong induction on the heap size measure used for termination.
  let n := BinaryHeap.sizeOf queue
  induction n using Nat.strong_induction_on
  expose_names
  -- intro dist queue hsize hdist0
  dsimp [dijkstra_rec]
  by_cases hq : queue.isEmpty
  · simp [dijkstra_rec, hq, h]
  -- Non-empty case: extract min, relax neighbors, recurse on smaller heap
  · have hne : queue.isEmpty = false := hq
    let (u, queue') := queue.extract_min
    let (dist', queue'') := relaxNeighbors g u dist queue'
    -- dist' preserves source = 0
    have dist'_src_zero : dist' source = 0 := by sorry
    -- size decreases: sizeOf queue'' ≤ sizeOf queue' and sizeOf queue' < n
    have hq'_lt : BinaryHeap.sizeOf queue' < BinaryHeap.sizeOf queue :=
      BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false queue hne
    have hq''le : BinaryHeap.sizeOf queue'' ≤ BinaryHeap.sizeOf queue' :=
      sizeOf_relaxNeighbors_le g u dist queue'
    have hq''lt : BinaryHeap.sizeOf queue'' < BinaryHeap.sizeOf queue := by
      exact lt_of_le_of_lt hq''le hq'_lt
    -- Apply IH to smaller size
    have myrec := h_1 (BinaryHeap.sizeOf queue'') hq''lt dist' queue'' dist'_src_zero
    exact myrec


-- The final dijkstra map keeps the source at 0.
lemma dijkstra_source_zero
  [Nonempty V]
  (g : FinSimpleGraph V) (s t : V) : (dijkstra g s t) s = 0 := by
  dsimp [dijkstra]
  let dist0 : V → ENat := fun v => if v = s then 0 else ⊤
  let queue := BinaryHeap.empty.add s 0
  have : dist0 s = 0 := by simp [dist0]
  exact dijkstra_rec_preserves_source_zero g s t dist0 queue this



theorem dijkstra_correctness
  [Nonempty V]
  (g : FinSimpleGraph V) (s : V) :
  ∀ v : V, (dijkstra g s v) v = delta g s v := by
  classical
  -- We prove correctness via a minimal-counterexample/shortest-path argument.
  -- To keep focus on structure, we assume a few standard Dijkstra invariants
  -- as helper lemmas (stated below this proof) and use them here.
  intro v
  -- Shorthand for the final distance map returned by Dijkstra when run
  -- from source `s` (the extra `target` parameter is unused in our
  -- implementation, but we pass `v` to match the function's arity).
  set dist := (dijkstra g s v) with hdist
  -- Global lower bound: Dijkstra never underestimates true distances.
  have h_lower : ∀ u, (delta g s u : ENat) ≤ dist u :=
    neverUnderestimates g s v

  -- If `dist v = δ(s,v)`, we are done. Otherwise argue by contradiction
  -- using a minimal counterexample w.r.t. graph distance from `s`.
  by_contra hneq_v
  have hexists : ∃ u, dist u ≠ delta g s u := ⟨v, by simpa [hdist] using hneq_v⟩
  obtain ⟨u, hu_ne, h_min⟩ := minimalCounterexample g s dist hexists
  -- Pick a predecessor `y` on a shortest path from `s` to `u` so that
  -- δ(s,u) = δ(s,y) + 1 and `y` is adjacent to `u`.
  have u_ne_s : u ≠ s := by
    intro h
    have h2: s = u := by exact ((fun a ↦ a) ∘ fun a ↦ a) (id (Eq.symm h))
    subst h2
    -- If `u = s` then the final Dijkstra map has `dist s = 0`.
    have hsrc : dist s = 0 := by exact dijkstra_source_zero g s v
    -- Also `δ(s,s) = 0`.
    have hdelta0 : delta g s s = 0 := by
      unfold delta
      exact SimpleGraph.dist_self
      --exact (SimpleGraph.dist_eq_zero_iff (G := g.toSimpleGraph) (u := s) (v := s)).mpr rfl
    -- So `dist s = δ(s,s)`, contradicting `hu_ne` when `u = s`.
    have heq : dist s = delta g s s := by simp [hsrc, hdelta0]
    exact hu_ne heq

  have hpos : 0 < delta g s u := by
    exact positiveDistance_of_counterexample g s v dist u hu_ne u_ne_s
  obtain ⟨y, hyu_adj, hδ⟩ := existsPredOnShortestPath g s u hpos
  -- By minimality of `u`, every vertex strictly closer than `u` is
  -- already correct; in particular `y` is correct.
  have hy_lt_u : delta g s y < delta g s u := by simp [hδ]
  have hy_eq : dist y = delta g s y := by
    exact (h_min y hy_lt_u)
  -- When processing `y`, relaxing edge (y,u) ensures the final bound
  -- `dist u ≤ dist y + 1`.
  have h_relax : dist u ≤ dist y + 1 :=
    relaxAdj_final_bound g s v hyu_adj
  -- Combine with `hy_eq` and the shortest-path step `hδ` to obtain
  -- an upper bound `dist u ≤ δ(s,u)`.
  have h_upper : dist u ≤ (delta g s u : ENat) := by
    -- Using `hy_eq` and `hδ : δ(s,u) = δ(s,y) + 1`.
    -- Coercions between `Nat` and `ENat` are implicit; details omitted.
    -- Outline:
    --   dist u ≤ dist y + 1 = δ(s,y) + 1 = δ(s,u)
    simpa [hy_eq, hδ] using h_relax
  -- Lower bound from never-underestimates: δ(s,u) ≤ dist u.
  have h_lower_u : (delta g s u : ENat) ≤ dist u := h_lower u
  -- Hence equality, contradicting that `u` was a counterexample.
  have : dist u = delta g s u := le_antisymm h_upper h_lower_u
  exact hu_ne this
