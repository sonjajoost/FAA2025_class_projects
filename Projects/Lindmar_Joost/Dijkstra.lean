import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.List.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Projects.Lindmar_Joost.BinaryHeapTreeV

open Finset SimpleGraph
open BinaryTree BinaryHeap

set_option autoImplicit true

structure FinSimpleGraph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance  fintypeFinSimpleGraph {V : Type u} [Fintype V] [DecidableEq V] (G : FinSimpleGraph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)




variable  {V : Type*} [Fintype V] [DecidableEq V]


-- Local invariant: at a state `(d, pq)`, the next extracted vertex's value
-- is at least the current value at `y`. Requires a proof the heap is non-empty.
def MinGeYInvariant [Nonempty V] (y : V) (p : (V → ENat) × BinaryHeap V) (hh : ¬ isEmpty p.2) : Prop :=
  ∀ u1 : V, Prod.fst (p.2.extract_min p.1 hh) = u1 → p.1 y ≤ p.1 u1



noncomputable def relaxNeighbors (g : FinSimpleGraph V) (u : V) (dist : V → ENat) (queue : BinaryHeap V) : (V → ENat) × (BinaryHeap V) :=
  List.foldl
    (fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
      let (dist, queue) := acc
      let alt := dist u + 1
      if alt < dist v then
        let dist' : V → ENat := fun x => if x = v then alt else dist x
        let queue' := queue.decrease_priority v dist'
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
      let queue' := queue.decrease_priority v dist'
      (dist', queue')
    else
      (dist, queue)
  -- Induction on neighbors
  simp [relaxNeighbors]
  induction (g.neighborFinset u).val.toList generalizing dist q with
  | nil =>
    simp
  | cons v vs ih =>
    simp
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
      have ih_used := ih dist' queue'
      grind


-- Relaxation step never increases any entry of the distance map.
lemma relaxNeighbors_nonincrease
    (g : FinSimpleGraph V) (u : V) (dist : V → ENat) (q : BinaryHeap V) :
    ∀ x, (Prod.fst (relaxNeighbors g u dist q)) x ≤ dist x := by
  -- Unfold as a fold over neighbors and prove by induction on the list.
  let neighbors := (g.neighborFinset u).val.toList
  let f := fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
    let (d, pq) := acc
    let alt := d u + 1
    if alt < d v then
      let d' : V → ENat := fun x => if x = v then alt else d x
      let pq' := pq.decrease_priority v d'
      (d', pq')
    else
      (d, pq)
  have step : ∀ (d : V → ENat) (pq : BinaryHeap V) (v x : V),
      (Prod.fst (f (d, pq) v)) x ≤ d x := by
    intro d pq v x
    dsimp [f]
    by_cases h : (d u + 1) < d v
    · by_cases hx : x = v
      · subst hx; simp [h, le_of_lt h]
      · simp [h, hx]
    · simp [h]
  have fold : ∀ (l : List V) (d : V → ENat) (pq : BinaryHeap V) (x : V),
      (Prod.fst (List.foldl f (d, pq) l)) x ≤ d x := by
    intro l
    induction l with
    | nil => intro d pq x; simp
    | cons v vs ih =>
      intro d pq x
      cases hacc : f (d, pq) v with
      | mk d' pq' =>
        have hx : (Prod.fst (List.foldl f (d', pq') vs)) x ≤ d' x := by
          simpa using ih d' pq' x
        have hx' : d' x ≤ d x := by
          simpa [hacc] using step d pq v x
        -- Relate folds: (d,pq)::(v::vs) = (f (d,pq) v)::vs and f (d,pq) v = (d',pq')
        have hdef : (Prod.fst (List.foldl f (d, pq) (v :: vs))) x
                    = (Prod.fst (List.foldl f (f (d, pq) v) vs)) x := by
          simp [List.foldl, f]
        have hrewrite : (Prod.fst (List.foldl f (f (d, pq) v) vs)) x
                        = (Prod.fst (List.foldl f (d', pq') vs)) x := by
          simp [f, hacc]
        have hle' : (Prod.fst (List.foldl f (f (d, pq) v) vs)) x ≤ d x := by
          have hle := le_trans hx hx'
          simpa [hrewrite] using hle
        simpa [hdef] using hle'
  intro x; simpa [relaxNeighbors, neighbors, f] using fold neighbors dist q x






-- Helper lemma: if input heap is non-empty, relaxNeighbors result is also non-empty
-- (because decrease_priority preserves the isEmpty status)
lemma relaxNeighbors_nonempty_of_input_nonempty [Nonempty V] (g : FinSimpleGraph V) (u : V) (dist : V → ENat) (q : BinaryHeap V) :
  q.isEmpty = false → (relaxNeighbors g u dist q).2.isEmpty = false := by
  intro hq_ne
  unfold relaxNeighbors
  -- Prove a general fact: the fold preserves non-emptiness of the queue component
  -- because each step either keeps the queue or calls decrease_priority which preserves isEmpty
  suffices ∀ (neighbors : List V) (d : V → ENat) (queue : BinaryHeap V),
      queue.isEmpty = false →
      (List.foldl
        (fun (acc : (V → ENat) × BinaryHeap V) (w : V) =>
          let (dist_acc, queue_acc) := acc
          let alt := dist_acc u + 1
          if alt < dist_acc w then
            let dist' := fun x => if x = w then alt else dist_acc x
            let queue' := queue_acc.decrease_priority w dist'
            (dist', queue')
          else
            (dist_acc, queue_acc))
        (d, queue) neighbors).2.isEmpty = false by
    exact this (g.neighborFinset u).val.toList dist q hq_ne
  intro neighbors
  induction neighbors with
  | nil =>
    intro d queue hqueue
    simp [List.foldl_nil]
    exact hqueue
  | cons v neighbors' ih =>
    intro d queue hqueue
    simp only [List.foldl_cons]
    split_ifs with hcond
    · -- After decrease_priority
      apply ih
      rw [BinaryHeap.decrease_priority_preserves_isEmpty]
      exact hqueue
    · -- Queue unchanged
      exact ih d queue hqueue


-- Helper lemma: after relaxing neighbors, the heap is non-empty
-- This works because: if input is non-empty, it stays non-empty.
-- In Dijkstra's context, the initial queue has source, so after each extraction+relaxation,
-- we process neighbors which ensures non-emptiness for the next iteration.
lemma relaxNeighbors_nonempty [Nonempty V] (g : FinSimpleGraph V) (u : V) (dist : V → ENat) (q : BinaryHeap V) :
  q.isEmpty = false → (relaxNeighbors g u dist q).2.isEmpty = false :=
  relaxNeighbors_nonempty_of_input_nonempty g u dist q

noncomputable def dijkstra_rec [Nonempty V] (g: FinSimpleGraph V) (source : V) (target : V) (dist : V → ENat) (queue : BinaryHeap V) : V → ENat :=
  if hq: queue.isEmpty then dist
  else
    have hne : ¬ queue.isEmpty = true := by exact  hq
    let extract_result := queue.extract_min dist hne
    let u := extract_result.1
    let queue' := extract_result.2
    let relax_result := relaxNeighbors g u dist queue'
    let dist' := relax_result.1
    let queue'' := relax_result.2
    dijkstra_rec g source target dist' queue''

termination_by queue.sizeOf
decreasing_by
  -- In the else branch, extract_result, u, queue', relax_result, dist', queue'' are all in scope
  have hne : queue.isEmpty = false := by exact eq_false_of_ne_true hq
  -- Key: show queue' = (queue.extract_min ...).2 and queue'' = (relaxNeighbors ...).2
  have hq'_eq : queue' = (queue.extract_min dist (by exact hq)).2 := rfl
  have hq''_eq : queue'' = (relaxNeighbors g u dist queue').2 := rfl
  -- Now chain the inequalities
  calc queue''.sizeOf
      = (relaxNeighbors g u dist queue').2.sizeOf := by rw [hq''_eq]
    _ ≤ queue'.sizeOf := sizeOf_relaxNeighbors_le g u dist queue'
    _ = (queue.extract_min dist (by exact hq)).2.sizeOf := by rw [hq'_eq]
    _ < queue.sizeOf := BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false queue hne dist


-- The recursive Dijkstra map is pointwise ≤ the input map (distances never increase).
lemma dijkstra_rec_le_input_map
  [Nonempty V]
  (g : FinSimpleGraph V) (s t : V) :
  ∀ (dist : V → ENat) (queue : BinaryHeap V) (x : V),
    (dijkstra_rec g s t dist queue) x ≤ dist x := by
  intro dist queue x
  -- Strong induction on the heap size
  generalize hsize : BinaryHeap.sizeOf queue = n
  revert queue dist hsize
  induction' n using Nat.strong_induction_on with n ih
  intro dist queue hsize
  by_cases hq : queue.isEmpty
  · simp [dijkstra_rec, hq]
  · -- Non-empty case: one step then recurse on smaller heap
    have hne : queue.isEmpty = false := by exact eq_false_of_ne_true hq
    unfold dijkstra_rec
    simp [hq]
    -- Match the structure of dijkstra_rec: extract_result, then relax_result
    have hne_proof : ¬queue.isEmpty = true := by exact hq
    let extract_result := queue.extract_min dist hne_proof
    let u := extract_result.1
    let queue' := extract_result.2
    let relax_result := relaxNeighbors g u dist queue'
    let dist' := relax_result.1
    let queue'' := relax_result.2
    -- Size decreases
    have hq'_eq : queue' = (queue.extract_min dist hne_proof).2 := rfl
    have hq'_lt : BinaryHeap.sizeOf queue' < BinaryHeap.sizeOf queue := by
      rw [hq'_eq]
      exact BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false queue hne dist
    have hq''le : BinaryHeap.sizeOf queue'' ≤ BinaryHeap.sizeOf queue' :=
      sizeOf_relaxNeighbors_le g u dist queue'
    have hq''lt : BinaryHeap.sizeOf queue'' < BinaryHeap.sizeOf queue :=
      lt_of_le_of_lt hq''le hq'_lt
    have hq''lt' : BinaryHeap.sizeOf queue'' < n := by
      exact Nat.lt_of_lt_of_eq hq''lt hsize
    -- Apply IH to smaller heap
    have hIH := ih (BinaryHeap.sizeOf queue'') hq''lt' dist' queue'' rfl
    -- dijkstra_rec g s t dist' queue'' x ≤ dist' x
    have hmono := hIH
    -- dist' x ≤ dist x by nonincrease of relaxNeighbors
    have hstep_noninc : dist' x ≤ dist x := by
      simpa using relaxNeighbors_nonincrease g u dist queue' x
    exact le_trans hmono hstep_noninc



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



-- Dijkstra never underestimates the true graph distance.
lemma neverUnderestimates
  [Nonempty V]
  (g : FinSimpleGraph V) (s t : V) :
  ∀ u : V, (delta g s u : ENat) ≤ (dijkstra g s t) u := by
  intro u
  admit


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


-- For a genuine counterexample `u`, the distance from `s` must be positive
-- (i.e., `u ≠ s`). Otherwise initialization already matches.
lemma positiveDistance_of_counterexample
  [Nonempty V]
  (g : FinSimpleGraph V) (s : V) (u : V) (u_ne_s : u ≠ s)
  (is_connected : SimpleGraph.Connected g.toSimpleGraph)
  :
  0 < delta g s u := by
  -- If `u ≠ s` then `δ(s,u) ≠ 0` because `dist s u = 0 ↔ u = s`.
  unfold delta
  simp_all
  refine Nat.pos_of_ne_zero ?_
  intro hzero
  -- `hzero : delta g s u = 0` implies `u = s` by Mathlib's lemma, contradiction.
  have := (SimpleGraph.Reachable.dist_eq_zero_iff (G := g.toSimpleGraph) (u := s) (v := u))
  -- Use connectivity to get reachability between s and u
  rw [SimpleGraph.connected_iff_exists_forall_reachable] at is_connected
  rcases is_connected with ⟨sink, hsink⟩
  have hreachu : g.toSimpleGraph.Reachable sink u := hsink u
  have hreachs : g.toSimpleGraph.Reachable sink s := hsink s
  have hreachus : g.toSimpleGraph.Reachable s u := by
    exact Reachable.trans (id (Reachable.symm hreachs)) (hsink u)
  apply this at hreachus
  rw [hreachus] at hzero
  have u_e_s : u = s := by exact ((fun a ↦ a) ∘ fun a ↦ a) (id (Eq.symm hzero))
  contradiction






-- Along an edge, distances step by at most 1 (ENat form), problem is we need acyclicty for this
lemma delta_adj_step_ENat
  (g : FinSimpleGraph V) (s u v : V)
  (hAdj : g.toSimpleGraph.Adj u v)
  (is_connected: SimpleGraph.Connected g.toSimpleGraph) :
  (delta g s v : ENat) ≤ (delta g s u : ENat) + 1 := by
  -- Work in Nat first, then cast to ENat.
  have h_nat : delta g s v ≤ delta g s u + 1 := by
    unfold delta
    -- Triangle: dist s v ≤ dist s u + dist u v
    have htri :  g.toSimpleGraph.dist s v ≤ g.toSimpleGraph.dist s u + g.toSimpleGraph.dist u v := SimpleGraph.Connected.dist_triangle (G := g.toSimpleGraph) is_connected
    -- adjacency gives dist u v = 1
    have hduv := (SimpleGraph.dist_eq_one_iff_adj (G := g.toSimpleGraph)).mpr hAdj
    calc
      (g.toSimpleGraph).dist s v ≤ (g.toSimpleGraph).dist s u + (g.toSimpleGraph).dist u v := htri
      _ = (g.toSimpleGraph).dist s u + 1 := by rw [hduv]

  exact_mod_cast h_nat


-- On any shortest path from `s` to `u`, there exists a predecessor `y`
-- adjacent to `u` with the distance stepping by one.
lemma existsPredOnShortestPath
  (g : FinSimpleGraph V) (s u : V)
  (hpos : 0 < delta g s u)
  (is_connected: SimpleGraph.Connected g.toSimpleGraph):
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
        have h_enat : (delta g s u : ENat) ≤ (delta g s y : ENat) + 1 :=
          delta_adj_step_ENat g s y u (SimpleGraph.Adj.symm hAdj) is_connected
        exact_mod_cast h_enat
    -- Conclude equality.
    exact Nat.le_antisymm h_ge h_le


-- Relaxation of an edge (y,u) yields, in the final map, the bound
-- `dist[u] ≤ dist[y] + 1`. This uses that when `y` is extracted, its
-- value is final and the relax step is applied.
-- Standard Dijkstra relaxation invariant (assumed):
-- for any edge (y,u), the final map satisfies
-- (dijkstra g s t) u ≤ (dijkstra g s t) y + 1.
-- Convenience: adjacency implies membership in the neighbor set.
lemma adj_mem_neighborFinset
  (g : FinSimpleGraph V) (u v : V)
  (hAdj : g.toSimpleGraph.Adj u v) : v ∈ g.neighborFinset u := by
  have hEquiv := SimpleGraph.mem_neighborFinset (G := g.toSimpleGraph) (v := u) (w := v)
  have hv : v ∈ (g.toSimpleGraph).neighborFinset u := hEquiv.mpr hAdj
  simpa using hv

-- Membership in neighborFinset implies adjacency (wrapper lemma).
lemma mem_neighborFinset_adj
  (g : FinSimpleGraph V) (u v : V)
  (h : v ∈ g.neighborFinset u) : g.toSimpleGraph.Adj u v := by
  -- Convert membership to the underlying SimpleGraph, then use the
    -- Convert membership to the underlying SimpleGraph and use the
    -- equivalence between neighborFinset membership and adjacency.
    have hv : v ∈ (g.toSimpleGraph).neighborFinset u := by simpa using h
    have hEquiv := SimpleGraph.mem_neighborFinset (G := g.toSimpleGraph) (v := u) (w := v)
    exact hEquiv.mp hv


-- Separate lemma: extracted vertex stabilizes its value: once y is extracted, its value
-- equals the value immediately after relaxing its neighbors.
-- Strengthened induction lemma: after extracting `y`, its value never decreases.
lemma extracted_value_never_decreases_after_step
  [Nonempty V]
  (g : FinSimpleGraph V) (s t y : V)
  (dist : V → ENat) (q : BinaryHeap V)
  (hq : ¬q.isEmpty = true)
  (hy : Prod.fst (q.extract_min dist hq) = y)
    (hInvPreserve : ∀ p : (V → ENat) × BinaryHeap V,
      ∀ (hh : ¬ isEmpty p.2), MinGeYInvariant (V := V) y p hh →
      ∀ (hne : ¬p.2.isEmpty = true),
      let step := p.2.extract_min p.1 hne
      let u := Prod.fst step
      let q1 := Prod.snd step
      let next := relaxNeighbors g u p.1 q1;
      ∀ (hhNext : ¬ isEmpty next.2), MinGeYInvariant (V := V) y next hhNext)
  :
  let q' := Prod.snd (q.extract_min dist hq); let next := relaxNeighbors g y dist q';
  ∀ (hhNext : ¬ isEmpty next.2), MinGeYInvariant (V := V) y next hhNext →
  next.1 y ≤ (dijkstra_rec g s t next.1 next.2) y := by
  -- Strong induction on the size of the post-step heap `next.2`.
  classical
  let q' := Prod.snd (q.extract_min dist hq)
  let next := relaxNeighbors g y dist q'
  -- Strong induction with a motive that carries the local invariant.
  have nondec : ∀ (p : (V → ENat) × BinaryHeap V) (n : Nat),
      BinaryHeap.sizeOf p.2 = n →
      ∀ (hh : ¬ isEmpty p.2), MinGeYInvariant (V := V) y p hh →
      p.1 y ≤ dijkstra_rec g s t p.1 p.2 y := by
    intro p n
    induction' n using Nat.strong_induction_on with k h generalizing p
    intro hsz' hh hmin
    expose_names
    by_cases hEmpty : p.2.isEmpty
    · -- Base: no further recursion, so the result is `p.1`.
      unfold dijkstra_rec; simp [hEmpty]
    · -- Step: unfold one recursive call on a strictly smaller heap.
      unfold dijkstra_rec; simp [hEmpty]
      have hne_proof : ¬p.2.isEmpty = true := by exact hEmpty
      let extract_result := p.2.extract_min p.1 hne_proof
      let u1 := extract_result.1
      let q1 := extract_result.2
      let next2 := relaxNeighbors g u1 p.1 q1
      -- Monotonicity towards the immediate post-step map.
      have hmono : (dijkstra_rec g s t next2.1 next2.2) y ≤ next2.1 y :=
        dijkstra_rec_le_input_map g s t next2.1 next2.2 y
      -- After one more relaxation (at `u1`), `y` cannot decrease anymore once `y` was extracted.
      -- We show `(next2.1 y) = p.1 y`, hence `p.1 y ≤ next2.1 y`.
      have hpreserve_y : p.1 y ≤ next2.1 y := by
        -- Basic correctness fact of the priority queue: after extracting `y`,
        -- every remaining entry `u1` has distance at least `p.1 y`.
        -- This is a standard Dijkstra invariant; we assume it as a basic fact.
        have heap_min_ge_y : p.1 y ≤ p.1 u1 := by
          exact hmin u1 rfl
        -- Show that relaxing neighbors of `u1` preserves the value at `y`.
        -- Concretely, if `v = y`, the update condition `alt < d y` is false
        -- because `alt = d u1 + 1 ≥ p.1 y + 1 > p.1 y = d y`.
        let neighbors1 := (g.neighborFinset u1).val.toList
        let f1 := fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
          let (d, pq) := acc
          let alt := d u1 + 1
          if alt < d v then
            let d' : V → ENat := fun x => if x = v then alt else d x
            let pq' := pq.decrease_priority v d'
            (d', pq')
          else
            (d, pq)
        -- Neighbors of `u1` are distinct from `u1`.
        have all_ne_u1 : ∀ v, v ∈ neighbors1 → v ≠ u1 := by
          intro v hv
          have hvF : v ∈ g.neighborFinset u1 := by
            simpa [neighbors1] using (Finset.mem_toList.mp hv)
          have hvAdj : g.toSimpleGraph.Adj u1 v := mem_neighborFinset_adj g u1 v hvF
          have hIr : ¬ g.toSimpleGraph.Adj u1 u1 := by simp
          intro h; subst h; exact hIr.elim hvAdj
        -- One-step preservation of `y` given the invariant `p.1 y ≤ d u1 + 1` and `d y = p.1 y`.
        have step_preserve_y : ∀ (d : V → ENat) (pq : BinaryHeap V) (v : V),
            v ≠ u1 → (p.1 y ≤ d u1 + 1) → (d y = p.1 y) →
            (Prod.fst (f1 (d, pq) v)) y = d y := by
          intro d pq v hv_ne_u1 hy_ge hdy
          dsimp [f1]
          by_cases hlt : d u1 + 1 < d v
          · -- Update branch: only `v` changes. If `v = y`, the update guard is false.
            by_cases hyv : v = y
            · subst hyv
              --have : ¬ d u1 + 1 < d y := not_lt_of_ge (by simpa [hdy, add_comm] using hy_ge)
              simp [hdy]
              grind
            · simp [hlt, hdy]
              grind
          · -- No-update branch: everything is preserved.
            simp [hlt]
        -- Fold preservation over the neighbor list, maintaining the invariants.
        have preserve_eq_list : ∀ (l : List V) (q : BinaryHeap V) (d : V → ENat),
            p.1 y ≤ d u1 + 1 → d y = p.1 y → (∀ v, v ∈ l → v ≠ u1) →
            (Prod.fst (List.foldl f1 (d, q) l)) y = p.1 y := by
          intro l
          induction l with
          | nil =>
            intro q d _ hdy _; simp [hdy]
          | cons v vs ih =>
            intro q d hy_ge hdy hAllNe
            dsimp [List.foldl]
            cases hacc : f1 (d, q) v with
            | mk d' q' =>
              have hv_ne_u1 : v ≠ u1 := by
                have : v ∈ v :: vs := by simp
                exact hAllNe v this
              have hstep := step_preserve_y d q v hv_ne_u1 hy_ge hdy
              have h_y_pres : d' y = d y := by simpa [hacc] using hstep
              -- Maintain invariants across the fold: `d' u1 = d u1` and `p.1 y ≤ d' u1 + 1`.
              have h_u1_pres : d' u1 = d u1 := by
                -- Since `v ≠ u1`, `u1` is never updated by `f1`.
                dsimp [f1] at hacc
                by_cases hlt : d u1 + 1 < d v
                · simp [hlt] at hacc
                  cases hacc
                  have : d' = (fun x => if x = v then d u1 + 1 else d x) := by
                    expose_names; exact left.symm
                  simp [this]
                  grind
                · simp [hlt] at hacc
                  cases hacc
                  have : d' = d := by expose_names; exact left.symm
                  simp [this]
              have hy_ge' : p.1 y ≤ d' u1 + 1 := by grind
              have hdy' : d' y = p.1 y := by simpa [h_y_pres] using hdy
              have hAllNe_vs : ∀ w, w ∈ vs → w ≠ u1 := by
                intro w hw
                have : w ∈ v :: vs := by simpa [List.mem_cons] using Or.inr hw
                exact hAllNe w this
              have hih := ih q' d' hy_ge' hdy' hAllNe_vs
              simpa [List.foldl, f1, hacc]
        -- Apply to the concrete neighbor list starting from `(p.1, q1)`.
        have hy_ge1 : p.1 y ≤ p.1 u1 + 1 := by
          -- Monotonicity of `+ 1`.
          have : p.1 u1 ≤ p.1 u1 + 1 := by
            -- ENat: `a ≤ a + 1`.
            have h01 : (0 : ℕ∞) ≤ 1 := by decide
            simp
          exact le_trans heap_min_ge_y this
        have : (Prod.fst (List.foldl f1 (p.1, q1) neighbors1)) y = p.1 y :=
          preserve_eq_list neighbors1 q1 p.1 hy_ge1 rfl all_ne_u1
        -- Conclude equality of the `y`-coordinate after the relaxation step.
        have hEqY : next2.1 y = p.1 y := by simpa [relaxNeighbors, neighbors1, f1] using this
        -- Therefore, `p.1 y ≤ next2.1 y`.
        simp [hEqY]
      -- Size strictly decreases across extract+relax, enabling the strong IH.
      have hq1_eq : q1 = (p.2.extract_min p.1 hEmpty).2 := rfl
      have hlt_extract : BinaryHeap.sizeOf q1 < BinaryHeap.sizeOf p.2 := by
        rw [hq1_eq]
        exact BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false p.2 (by exact eq_false_of_ne_true hEmpty) p.1
      have hle_relax : BinaryHeap.sizeOf next2.2 ≤ BinaryHeap.sizeOf q1 :=
        sizeOf_relaxNeighbors_le g u1 p.1 q1
      have hlt_total : BinaryHeap.sizeOf next2.2 < BinaryHeap.sizeOf p.2 :=
        lt_of_le_of_lt hle_relax hlt_extract
      have hlt_k : BinaryHeap.sizeOf next2.2 < k := by simpa [hsz'] using hlt_total
      -- Case split on the emptiness of next2.2 to avoid needing a proof out of thin air.
      by_cases hEmpty2 : next2.2.isEmpty
      · -- If next heap is empty, the recursion stops and equality is immediate.
        have : p.1 y ≤ dijkstra_rec g s t next2.1 next2.2 y := by
          have : p.1 y ≤ next2.1 y := hpreserve_y
          simpa [dijkstra_rec, hEmpty2] using this
        exact this
      · -- Non-empty: get invariant at next2 from preservation, then apply IH.
        have hhNext : ¬ next2.2.isEmpty = true := by exact hEmpty2
        have hmin_next : MinGeYInvariant (V := V) y next2 hhNext := by
          have hpres := hInvPreserve p hh hmin hne_proof
          exact hpres hhNext
        have hih' := h (BinaryHeap.sizeOf next2.2) hlt_k next2 rfl hhNext hmin_next
        -- Chain inequalities to conclude: p.1 y ≤ next2.1 y ≤ dijkstra_rec ... next2 ... y
        exact le_trans hpreserve_y hih'
  -- Apply the general induction to our concrete post-extraction state `next`.
  intro hhNext hInvNext
  grind
  --exact nondec next (BinaryHeap.sizeOf next.2) rfl hhNext hInvNext

-- Finality lemma using the strengthened induction statement.
lemma extracted_value_is_final_lemma
  [Nonempty V]
  (g : FinSimpleGraph V) (s t y : V)
  (dist : V → ENat) (q : BinaryHeap V)
  (hq : ¬q.isEmpty = true)
  (qempty : ¬q.isEmpty = true)
  (hy : Prod.fst (q.extract_min dist qempty) = y)

    (hInvPreserve : ∀ p : (V → ENat) × BinaryHeap V,
      ∀ (hh : ¬ isEmpty p.2), MinGeYInvariant (V := V) y p hh →
      ∀ (hne : ¬p.2.isEmpty = true),
      let step := p.2.extract_min p.1 hne
      let u := Prod.fst step
      let q1 := Prod.snd step
      let next := relaxNeighbors g u p.1 q1;
      ∀ (hhNext : ¬ isEmpty next.2), MinGeYInvariant (V := V) y next hhNext)


  :
  let q' := Prod.snd (q.extract_min dist qempty); let next := relaxNeighbors g y dist q';
  ∀ (hhNext : ¬ isEmpty next.2), MinGeYInvariant (V := V) y next hhNext →
  dist y = (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y := by
  -- Bind the post-extraction queue and relaxation result for clarity.
  let q' := Prod.snd (q.extract_min dist hq)
  let next := relaxNeighbors g y dist q'
  -- 1) Final value at y is ≤ the pre-step `dist y`.
  have h_final_le_dist : (dijkstra_rec g s t next.1 next.2) y ≤ dist y := by
    have hmono : (dijkstra_rec g s t next.1 next.2) y ≤ next.1 y :=
      dijkstra_rec_le_input_map g s t next.1 next.2 y
    have hstep_noninc : next.1 y ≤ dist y := by
      simpa using relaxNeighbors_nonincrease g y dist q' y
    exact le_trans hmono hstep_noninc
  -- 2) `dist y ≤` final value, via: `next.1 y = dist y` and the strong lemma.
  -- Show the relaxation step at `y` does not change the `y`-coordinate.
  let neighbors := (g.neighborFinset y).val.toList
  let f := fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
    let (d, pq) := acc
    let alt := d y + 1
    if alt < d v then
      let d' : V → ENat := fun x => if x = v then alt else d x
      let pq' := pq.decrease_priority v d'
      (d', pq')
    else
      (d, pq)
  have all_ne_neighbors : ∀ v, v ∈ neighbors → v ≠ y := by
    intro v hv
    have hvF : v ∈ (g.neighborFinset y) := by
      rw [Multiset.mem_toList] at hv
      rw [mem_val] at hv
      exact hv
    have hAdj_vy : g.toSimpleGraph.Adj y v := mem_neighborFinset_adj g y v hvF
    have hIr : ¬ g.toSimpleGraph.Adj y y := by simp
    intro hEq; subst hEq; exact hIr.elim hAdj_vy
  have preserve_y : ∀ (l : List V) (d : V → ENat) (pq : BinaryHeap V),
      (∀ v, v ∈ l → v ≠ y) →
      (Prod.fst (List.foldl f (d, pq) l)) y = d y := by
    intro l
    induction l with
    | nil => intro d pq _; simp
    | cons v vs ih =>
      intro d pq hAllNe'
      cases hacc : f (d, pq) v with
      | mk d' pq' =>
        have hdy : d' y = d y := by
          simp [f] at hacc
          by_cases hlt : d y + 1 < d v
          · have hv_ne_y : v ≠ y := by
              apply hAllNe'
              simp
            simp [hlt] at hacc
            cases hacc
            have : d' = fun x => if x = v then d y + 1 else d x := by
              expose_names
              exact left.symm
            simp [this]
            grind
          · simp [hlt] at hacc
            cases hacc
            have : d' = d := by
              expose_names
              exact left.symm
            simp [this]
        have hAllNe_vs : ∀ w, w ∈ vs → w ≠ y := by
          intro w hw
          have : w ∈ v :: vs := by simpa [List.mem_cons] using Or.inr hw
          exact hAllNe' w this
        have := ih d' pq' hAllNe_vs
        simpa [List.foldl, f, hacc, hdy]
  have hnext_y_eq : next.1 y = dist y := by
    have : (Prod.fst (List.foldl f (dist, q') neighbors)) y = dist y :=
      preserve_y neighbors dist q' all_ne_neighbors
    simpa [relaxNeighbors, neighbors, f] using this
  -- Strong lemma (parameterized by invariant): after extracting `y`, its value never decreases.
  have hlemma := extracted_value_never_decreases_after_step g s t y dist q hq hy hInvPreserve
  -- Conclude equality by antisymmetry, given an invariant at `next` with hhNext.
  intro hhN hInvN hhNext invariant
  have hsteps := hlemma (by grind) invariant
  apply le_antisymm
  · grind
  · grind

lemma relaxNeighbors_adj_upper
(hAdj : g.Adj y u) :
      ∀ (dist : V → ENat) (q : BinaryHeap V),
        (Prod.fst (relaxNeighbors g y dist q)) u ≤ dist y + 1 := by
    intro dist q
    -- Unfold relaxNeighbors as a fold over the neighbor list.
    let neighbors := (g.neighborFinset y).val.toList
    let f := fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
      let (dist, queue) := acc
      let alt := dist y + 1
      if alt < dist v then
        let dist' : V → ENat := fun x => if x = v then alt else dist x
        let queue' := queue.decrease_priority v dist'
        (dist', queue')
      else
        (dist, queue)
    -- We proceed by induction on the neighbor list.
    -- `u` is adjacent to `y`, hence appears in the neighbor list.
    have hu_mem_fin : u ∈ g.neighborFinset y := adj_mem_neighborFinset g y u hAdj
    have hu_mem_list : u ∈ neighbors := by
      simpa [neighbors] using (Finset.mem_toList.mpr hu_mem_fin)
    -- The neighbor list is nodup.
    have hnodup_neighbors : neighbors.Nodup := by
      simpa [neighbors] using (g.neighborFinset y).nodup_toList

    -- Helper: one step at vertex `u` yields `(≤ dist y + 1)` at `u`.
    have step_u_bound : ∀ (d : V → ENat) (pq : BinaryHeap V),
        (Prod.fst (f (d, pq) u)) u ≤ d y + 1 := by
      intro d pq
      dsimp [f]
      by_cases hlt : d y + 1 < d u
      · simp [hlt]
      · have hle : d u ≤ d y + 1 := by
          -- From linear order on ENat: ¬ (d y + 1 < d u) ⇒ d u ≤ d y + 1
          have : ¬ d u > d y + 1 := by simpa [gt_iff_lt] using hlt
          exact le_of_not_gt this
        simp [hlt, hle]

    -- Helper: steps at vertices different from `u` preserve the `(≤ dist y + 1)` bound at `u`.
    have step_other_preserve : ∀ (d : V → ENat) (pq : BinaryHeap V) (v : V),
        v ≠ u → (Prod.fst (d, pq)) u ≤ d y + 1 → (Prod.fst (f (d, pq) v)) u ≤ d y + 1 := by
      intro d pq v hv_ne hbound
      dsimp [f]
      by_cases hlt : d y + 1 < d v
      · grind
      · simp [hlt, hbound]

    -- Helper: preserving bound when folding over a list that does not contain `u`.
    have preserve_no_u : ∀ (l : List V) (d : V → ENat) (pq : BinaryHeap V),
        u ∉ l → (Prod.fst (d, pq)) u ≤ d y + 1 →
        (Prod.fst (List.foldl f (d, pq) l)) u ≤ d y + 1 := by
      intro l
      induction l with
      | nil => intro d pq _ hb; simpa using hb
      | cons v vs ih =>
        intro d pq hu_not hb
        have hv_ne_u : v ≠ u := by
          have : u ∉ v :: vs := hu_not
          simp
          grind
        cases hacc : f (d, pq) v with
        | mk d' pq' =>
          have hb' : (Prod.fst (d', pq')) u ≤ d y + 1 := by
            have := step_other_preserve d pq v hv_ne_u hb
            simpa [f, hacc] using this
          have hu_not_vs : u ∉ vs := by
            have : u ∉ v :: vs := hu_not
            grind
          simp_all
            -- Apply the induction hypothesis to the tail vs.
          -- Show d' y = d y
          have hdy : d' y = d y := by
            simp [f] at hacc
            by_cases hlt : d y + 1 < d v
            · simp [hlt] at hacc
              -- d' = fun x => if x = v then d y + 1 else d x
              -- We want d' y = d y
              have : d' y = (fun x => if x = v then d y + 1 else d x) y := by rw [hacc.left]
              simp only [this]
              by_cases hyv : y = v
              · have hfalse : False := by
                  have hle : d y ≤ d y + 1 := by
                    have : (0 : ℕ∞) ≤ 1 := by decide
                    simp
                  have hlt' : d y + 1 < d y := by
                    simpa [hyv] using hlt
                  have h : d y < d y :=
                    lt_of_le_of_lt hle hlt'
                  exact lt_irrefl _ h
                exact hfalse.elim
              · simp [hyv]
            · simp_all [f]
          -- Rewrite the target bound to d' y + 1
          have hb'' : d' u ≤ d' y + 1 := by
            rw [hdy]
            exact hb'
          grind

    -- Main lemma: if `u ∈ l`, `l` is nodup, and no element of `l` equals `y`,
    -- then the fold yields `(≤ d y + 1)` at `u`.
    have bound_if_mem_nodup : ∀ (l : List V) (d : V → ENat) (pq : BinaryHeap V),
        l.Nodup → (∀ v, v ∈ l -> v ≠ y) → u ∈ l →
        (Prod.fst (List.foldl f (d, pq) l)) u ≤ d y + 1 := by

      intro l
      induction l with
      | nil => intro d pq hnodup hAllNe hmem; cases hmem
      | cons v vs ih =>
        intro d pq hnodup hAllNe hmem
        have hmem_cases : u = v ∨ u ∈ vs := by
          simpa [List.mem_cons] using hmem
        have hv_ne_y : v ≠ y := by
          have : v ∈ v :: vs := by simp
          exact hAllNe v this
        have hnodup_vs : vs.Nodup := (List.nodup_cons.mp hnodup).2
        have hAllNe_vs : ∀ w, w ∈ vs -> w ≠ y := by
          intro w hw
          have : w ∈ v :: vs := by simpa [List.mem_cons] using Or.inr hw
          exact hAllNe w this
        cases hmem_cases with
        | inl hv_eq =>
          -- Head equals `u`: take one step at `u`, then preserve bound over tail.
          subst hv_eq
          cases hacc : f (d, pq) u with
          | mk d1 q1 =>
            --simp [List.foldl, hacc] at *
            have h_d1y : d1 y = d y := by
              -- Inspect which branch of the `if` in `f` was taken by comparing `d y + 1 < d u`.
              by_cases hlt : d y + 1 < d u
              · -- If true, f (d,pq) u = (fun x => if x = u then d y + 1 else d x, pq.decrease_priority u (d y + 1))
                have : d1 = fun x => if x = u then d y + 1 else d x := by
                  simp [f, hlt] at hacc
                  cases hacc-- with hd hq
                  expose_names
                  exact left.symm
                simp [this]
                grind
              · -- Otherwise f (d,pq) u = (d, pq)
                have : d1 = d := by
                  simp [f, hlt] at hacc
                  cases hacc --with hd hq
                  expose_names
                  exact left.symm
                simp [this]

            have hfold_eq : (List.foldl f (d, pq) (u :: vs)).1 u = (List.foldl f (d1, q1) vs).1 u := by simp [List.foldl, f, hacc]
            rw [hfold_eq, ← h_d1y]
            -- After processing the head `u` we obtained `d1, q1` from `hacc`.
            -- Now fold over the tail `vs` starting from `(d1, q1)`.
            apply preserve_no_u vs d1 q1
            · -- to show: ⊢ u ∉ vs
              -- nodup on `u :: vs` gives `u ∉ vs`
              have hu_not_vs : u ∉ vs := (List.nodup_cons.mp hnodup).1
              exact hu_not_vs
            · -- to show: (Prod.fst (d1, q1)) u ≤ d1 y + 1, i.e. d1 u ≤ d1 y + 1
              -- use the one-step bound at `u` and `h_d1y : d1 y = d y`
              have h_step : (Prod.fst (f (d, pq) u)) u ≤ d y + 1 := step_u_bound d pq
              simpa [hacc, h_d1y] using h_step
        | inr hu_in_vs =>
          -- Process `v` first (note `v ≠ u` from membership), then apply IH to `vs`.
          have hv_ne_u : v ≠ u := by
            -- If `v = u`, then `u ∉ vs` by nodup, contradicting `hu_in_vs`.
            intro hv_eq
            subst hv_eq
            exact (List.nodup_cons.mp hnodup).1 hu_in_vs
          cases hacc : f (d, pq) v with
          | mk d' q' =>
            -- Show `y` is unchanged by this step since `v ≠ y`.
            have hdy : d' y = d y := by
              simp [f] at hacc
              by_cases hlt : d y + 1 < d v
              · simp_all [f]
                grind
              · grind
            have hih := ih d' q' hnodup_vs hAllNe_vs hu_in_vs
            -- Rewrite the target fold and `d' y`.
            simpa [List.foldl, f, hacc, hdy] using hih

    -- For neighbors of `y`, every element is distinct from `y`.
    have all_ne_neighbors : ∀ v, v ∈ neighbors -> v ≠ y := by
      intro v hv
      classical
      -- Convert to Finset membership and use irreflexivity of adjacency.
      have hvF : v ∈ (g.neighborFinset y) := by
        simpa [neighbors] using (Finset.mem_toList.mp hv)
      have hAdj : g.toSimpleGraph.Adj y v := mem_neighborFinset_adj g y v hvF
      have hIr : ¬ g.toSimpleGraph.Adj y y := by simp
      intro hEq; subst hEq; exact hIr.elim hAdj

    -- Apply the main lemma to the concrete neighbor list.
    have : (Prod.fst (List.foldl f (dist, q) neighbors)) u ≤ dist y + 1 :=
      bound_if_mem_nodup neighbors dist q hnodup_neighbors all_ne_neighbors hu_mem_list
    simpa [relaxNeighbors, neighbors, f] using this


lemma exists_extract_or_top [Nonempty V]
  (g : FinSimpleGraph V) (s t : V)
  {y u : V} (hAdj : g.toSimpleGraph.Adj y u)
    (hInvPreserve : ∀ p : (V → ENat) × BinaryHeap V,
      ∀ (hh : ¬ isEmpty p.2), MinGeYInvariant (V := V) y p hh →
      ∀ (hne : ¬p.2.isEmpty = true),
      let step := p.2.extract_min p.1 hne
      let u := Prod.fst step
      let q1 := Prod.snd step
      let next := relaxNeighbors g u p.1 q1;
      ∀ (hhNext : ¬ isEmpty next.2), MinGeYInvariant (V := V) y next hhNext)
    (hInvInit : ∀ (dist : V → ENat) (q : BinaryHeap V) (hne : ¬q.isEmpty = true),
      Prod.fst (q.extract_min dist hne) = y →
      let q' := Prod.snd (q.extract_min dist hne)
      let next := relaxNeighbors g y dist q'
      ∀ (hhNext : ¬ isEmpty next.2), MinGeYInvariant (V := V) y next hhNext)
      :
      (dijkstra g s t) y = ⊤ ∨
      (∃ (dist : V → ENat) (q : BinaryHeap V) (hne : ¬q.isEmpty = true),
          Prod.fst (q.extract_min dist hne) = y ∧
            (let q' := Prod.snd (q.extract_min dist hne);
                 let next := relaxNeighbors g y dist q'
             (dijkstra g s t) = dijkstra_rec g s t (Prod.fst next) (Prod.snd next))) := by
    by_cases hyTop : (dijkstra g s t) y = ⊤
    · left; exact hyTop
    · right
      dsimp [dijkstra] at hyTop
      dsimp [dijkstra]

      -- Initial state
      set dist0 : V → ENat := fun v => if v = s then 0 else ⊤
      set q0 := BinaryHeap.empty.add s 0

      sorry

/-
      -- The search lemma with strong induction
      have search :
        ∀ (n : Nat), ∀ (d : V → ENat) (q : BinaryHeap V), BinaryHeap.sizeOf q ≤ n →
          q.isEmpty = true ∧ d y = ⊤ ∨
          ∃ (u : V) (q' : BinaryHeap V) (next : (V → ENat) × BinaryHeap V),
            q'.sizeOf < n ∧
            q.extract_min = (u, q') ∧
            next = relaxNeighbors g u d q' ∧
            (dijkstra_rec g s t d q y = dijkstra_rec g s t next.1 next.2 y) := by
          -- Strong induction on heap size bound `n`
          intro n
          refine Nat.strong_induction_on n ?ih
          intro n1 ih d q hle

          by_cases hq : q.isEmpty
          · left
            simp [dijkstra_rec, hq]
            -- to show q.isEmpty -> d y = ⊤
            sorry
          · let step := q.extract_min
            let u := Prod.fst step
            set q' := Prod.snd step
            set next := relaxNeighbors g u d q'
            right
            use u, q', next
            -- Here we prove the one-step recursion equality definitionally
            --dsimp [dijkstra_rec, hq]
            constructor
            · -- size decreases strictly after extract_min
              have hdec : BinaryHeap.sizeOf q' < BinaryHeap.sizeOf q :=
                BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false q (by simp [hq])
              exact lt_of_lt_of_le hdec hle
            · constructor
              · exact Prod.ext rfl rfl
              · dsimp [hq]
                constructor
                · rfl
                · -- use ih to finish this
                  have hq'_lt : BinaryHeap.sizeOf q' < n1 := by
                    have : BinaryHeap.sizeOf q' < BinaryHeap.sizeOf q :=
                      BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false q (by simp [hq])
                    exact lt_of_lt_of_le this hle
                  have hnext_le : BinaryHeap.sizeOf next.2 ≤ BinaryHeap.sizeOf q' :=
                    sizeOf_relaxNeighbors_le g u d q'
                  have hnext_lt : BinaryHeap.sizeOf next.2 < n1 :=
                    lt_of_le_of_lt hnext_le hq'_lt
                  -- Apply the induction hypothesis to the smaller heap `next.2`
                  -- Pass the concrete post-step state `(next.1, next.2)` and `rfl` for its size.
                  have hIH := ih (BinaryHeap.sizeOf next.2) hnext_lt (next.1) (next.2) le_rfl
                  cases hIH
                  · expose_names
                    simp_all
                    sorry
                  · expose_names
                    obtain ⟨u_ih, q_ih, hextract, hsizes, hextract2, hextract3, ih2⟩ := h
                    simp_all

                    sorry


      -- Apply the search predicate to the initial state `(dist0, q0)`.
      have hsearch0 := search (BinaryHeap.sizeOf q0) dist0 q0 le_rfl
      -- Since `(dijkstra g s t) y ≠ ⊤` by `hyTop`, the right branch holds.
      cases hsearch0 with
      | inl htop =>
        -- Contradicts `hyTop`.
        exact False.elim (hyTop htop)
      | inr hexists => grind
-/

lemma relaxAdj_final_bound
  [Nonempty V]
  (g : FinSimpleGraph V) (s t : V)
  {y u : V} (hAdj : g.toSimpleGraph.Adj y u)

  (hInvPreserve : ∀ p : (V → ENat) × BinaryHeap V,
    ∀ (hh : ¬ isEmpty p.2), MinGeYInvariant (V := V) y p hh →
    ∀ (hne : ¬p.2.isEmpty = true),
    let step := p.2.extract_min p.1 hne
    let u := Prod.fst step
    let q1 := Prod.snd step
    let next := relaxNeighbors g u p.1 q1;
    ∀ (hhNext : ¬ isEmpty next.2), MinGeYInvariant (V := V) y next hhNext)
  (hInvInit : ∀ (dist : V → ENat) (q : BinaryHeap V) (hne : ¬q.isEmpty = true),
    Prod.fst (q.extract_min dist hne) = y →
    let q' := Prod.snd (q.extract_min dist hne)
    let next := relaxNeighbors g y dist q'
    ∀ (hhNext : ¬ isEmpty next.2), MinGeYInvariant (V := V) y next hhNext)
  :
  (dijkstra g s t) u ≤ (dijkstra g s t) y + 1 := by

  have enat_top_add_one_eq_top : (⊤ : ENat) + 1 = (⊤ : ENat) := by rfl

  -- Unfold the starting state of Dijkstra.
  dsimp [dijkstra]
  let dist0 : V → ENat := fun v => if v = s then 0 else ⊤
  let queue0 := BinaryHeap.empty.add s 0

  -- Apply the extraction/top dichotomy.
  have hfinal_or_step := exists_extract_or_top g s t hAdj hInvPreserve hInvInit
  -- Replace (dijkstra g s t) with the definitional recursion from (dist0, queue0).
  -- Note: `exists_extract_or_top` is stated already in terms of `(dijkstra g s t)`.
  -- We perform case analysis on it.
  cases hfinal_or_step with
  | inl hyTop =>
    -- Final y is ⊤; RHS is ⊤, and any ENat is ≤ ⊤.
    have htop : (dijkstra_rec g s t dist0 queue0) y = ⊤ := by
      simpa [dijkstra] using hyTop
    have hle_top : (dijkstra_rec g s t dist0 queue0) u ≤ (⊤ : ENat) := le_top
    have : (dijkstra_rec g s t dist0 queue0) u ≤ (dijkstra_rec g s t dist0 queue0) y + 1 := by simp [htop]
    exact this
  | inr hstep =>
    rcases hstep with ⟨dist, q, hne, hyExtract, hfinEq⟩
    -- Define post-step state.
    have qempty : ¬q.isEmpty = true := by grind
    let q' := Prod.snd (q.extract_min dist qempty)
    let next := relaxNeighbors g y dist q'
    -- Monotonicity: final map ≤ post-step map.
    have hmono : ∀ x, (dijkstra_rec g s t dist q) x ≤ (Prod.fst next) x := by
      intro x
      -- Unfold one step of recursion and use nonincrease of subsequent recursion.
      unfold dijkstra_rec
      simp [hne, hyExtract]
      exact dijkstra_rec_le_input_map g s t (Prod.fst next) (Prod.snd next) x
    -- Local relaxation bound at u through edge (y,u).
    have relaxNeighbors_adj_upper:  ∀ (dist : V → ℕ∞) (q : BinaryHeap V), (relaxNeighbors g y dist q).1 u ≤ dist y + 1 := relaxNeighbors_adj_upper hAdj
    have hrelax : (Prod.fst next) u ≤ dist y + 1 := relaxNeighbors_adj_upper dist q'
    -- Stability of y after extraction.
    have hstable : dist y = (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y := by
      -- Obtain the initial invariant at `next` from `hInvInit`.
      by_cases hEmptyNext : next.2.isEmpty
      · let neighbors := (g.neighborFinset y).val.toList
        let f := fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
          let (d, pq) := acc
          let alt := d y + 1
          if alt < d v then
            let d' : V → ENat := fun x => if x = v then alt else d x
            let pq' := pq.decrease_priority v d'
            (d', pq')
          else
            (d, pq)
        have all_ne_neighbors : ∀ v ∈ neighbors, v ≠ y := by
          intro v hv
          have hvF : v ∈ (g.neighborFinset y) := by
            simpa [neighbors] using (Finset.mem_toList.mp hv)
          have hAdj_vy : g.toSimpleGraph.Adj y v := mem_neighborFinset_adj g y v hvF
          have hIr : ¬ g.toSimpleGraph.Adj y y := by simp
          intro hEq; subst hEq; exact hIr.elim hAdj_vy
        have preserve_y : ∀ (l : List V) (d : V → ENat) (pq : BinaryHeap V),
              (∀ v, v ∈ l → v ≠ y) →
              (Prod.fst (List.foldl f (d, pq) l)) y = d y := by
            intro l
            induction l with
            | nil => intro d pq _; simp
            | cons v vs ih =>
              intro d pq hAllNe'
              cases hacc : f (d, pq) v with
              | mk d' pq' =>
                have hdy : d' y = d y := by
                  simp [f] at hacc
                  by_cases hlt : d y + 1 < d v
                  · have hv_ne_y : v ≠ y := by
                      apply hAllNe'
                      simp
                    simp [hlt] at hacc
                    cases hacc
                    have : d' = fun x => if x = v then d y + 1 else d x := by
                      expose_names; exact left.symm
                    simp [this]
                    grind
                  · simp [hlt] at hacc
                    cases hacc
                    have : d' = d := by
                      expose_names; exact left.symm
                    simp [this]
                have hAllNe_vs : ∀ w, w ∈ vs → w ≠ y := by
                  intro w hw
                  have : w ∈ v :: vs := by simpa [List.mem_cons] using Or.inr hw
                  exact hAllNe' w this
                have := ih d' pq' hAllNe_vs
                simpa [List.foldl, f, hacc, hdy]
        have hnext_y_eq : next.1 y = dist y := by
          have : (Prod.fst (List.foldl f (dist, q') neighbors)) y = dist y :=
            preserve_y neighbors dist q' all_ne_neighbors
          simpa [relaxNeighbors, neighbors, f] using this

        -- With empty next.2, dijkstra_rec returns next.1; finish this branch directly
        have : dist y = (dijkstra_rec g s t next.1 next.2) y := by
          simp [dijkstra_rec, hEmptyNext, hnext_y_eq]
        exact this
      · have helper : ¬next.2.isEmpty = true := by grind
        have hInv0 : MinGeYInvariant (V := V) y next helper := by
          exact (hInvInit dist q hne hyExtract helper)
        have  helper : ¬q.isEmpty = true := by grind
        have h1 := extracted_value_is_final_lemma g s t y dist q qempty helper hyExtract hInvPreserve-- hInv0
        grind
    -- Rewrite final map using equality hfinEq.
    have hfinal_u : (dijkstra_rec g s t dist0 queue0) u = (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) u := by
      exact congrFun hfinEq u
    have hfinal_y : (dijkstra_rec g s t dist0 queue0) y = (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y := by
      exact congrFun hfinEq y
    -- Combine: final u ≤ (Prod.fst next) u ≤ dist y + 1 = final y + 1.
    have hchain : (dijkstra_rec g s t dist q) u ≤ (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y + 1 := by
      -- hmono u : (dijkstra_rec g s t dist q) u ≤ next.1 u
      -- hrelax : next.1 u ≤ dist y + 1
      -- hstable : dist y = (dijkstra_rec g s t next.1 next.2) y
      have hrelax' : next.1 u ≤ (dijkstra_rec g s t next.1 next.2) y + 1 := by
        rw [←hstable]
        exact hrelax
      exact le_trans (hmono u) hrelax'
    -- Replace final (from dist0, queue0) using equality hfinEq.
    -- First, rewrite final y via stability.
    have htarget : (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) u ≤ (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y + 1 := by
      -- By monotonicity, (dijkstra_rec ... u) ≤ next.1 u
      -- By relaxation, next.1 u ≤ dist y + 1 = (dijkstra_rec ... y) + 1
      -- So (dijkstra_rec ... u) ≤ (dijkstra_rec ... y) + 1
      have hmono' : (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) u ≤ next.1 u := by
        exact dijkstra_rec_le_input_map g s t (Prod.fst next) (Prod.snd next) u
      have hrelax' : next.1 u ≤ (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y + 1 := by
        rw [←hstable]
        exact hrelax
      exact le_trans hmono' hrelax'
    grind








-- Relaxing neighbors never changes the value at the source when it is 0.
lemma relaxNeighbors_preserves_source_zero
  (g : FinSimpleGraph V) (source u : V)
  (dist : V → ENat) (q : BinaryHeap V)
  (h0 : dist source = 0)
  (h1 := relaxNeighbors g u dist q)
  (h1' : h1 = relaxNeighbors g u dist q)
  :
  (Prod.fst h1) source = 0 := by

  -- A small helper assumption about ENat: adding 1 is never < 0.
  -- We keep it as a placeholder as permitted.
  have enat_add_one_not_lt_zero : ∀ x : ENat, ¬ x + 1 < 0 := by
    -- This follows from monotonicity of addition and 0 ≤ x + 1.
    -- Placeholder; can be discharged from ENat arithmetic.
    intro x; exact ENat.not_lt_zero (x + 1)

  -- Unfold relaxNeighbors into a fold over the neighbor list with a step function.
  let neighbors := (g.neighborFinset u).val.toList
  let f := fun (acc : (V → ENat) × BinaryHeap V) (v : V) =>
    let (d, pq) := acc
    let alt := d u + 1
    if alt < d v then
      let d' : V → ENat := fun x => if x = v then alt else d x
      let pq' := pq.decrease_priority v d'
      (d', pq')
    else
      (d, pq)

  -- One-step preservation: after processing any neighbor v once, the value at `source` remains 0.
  have step_preserve : ∀ (d : V → ENat) (pq : BinaryHeap V) (v : V),
      d source = 0 → (Prod.fst (f (d, pq) v)) source = 0 := by
    intro d pq v h0'
    dsimp [f]
    set alt := d u + 1 with halt
    by_cases hv : source = v
    · subst hv
      have hfalse : ¬ alt < d source := by
        simp [h0']
      by_cases h : alt < d source
      · exact False.elim (hfalse h)
      · simp [h0']
    · by_cases h : alt < d v
      · simp [h, hv, h0']
      · simp [h, h0']

  -- Fold preservation over the entire neighbor list.
  have fold_preserve : ∀ (l : List V) (d : V → ENat) (pq : BinaryHeap V),
      d source = 0 → (Prod.fst (List.foldl f (d, pq) l)) source = 0 := by
    intro l
    induction l with
    | nil =>
      intro d pq h0'
      simp [List.foldl, h0']
    | cons v vs ih =>
      intro d pq h0'
      cases acc : f (d, pq) v with
      | mk d' pq' =>
        -- After one step, the source entry remains 0.
        have h0'' : d' source = 0 := by
          have := step_preserve d pq v h0'
          simpa [acc] using this
        -- Recurse on the tail of the list.
        have := ih d' pq' h0''
        simpa [List.foldl, f, acc]

  -- Apply the fold preservation to the specific neighbor list and step function used by relaxNeighbors.
  have : (Prod.fst (List.foldl f (dist, q) neighbors)) source = 0 :=
    fold_preserve neighbors dist q h0
  have h1' : h1 =  relaxNeighbors g u dist q := by exact h1'
  simpa [relaxNeighbors, neighbors, f, h1'] using this


-- The recursive Dijkstra preserves `dist source = 0`.
lemma dijkstra_rec_preserves_source_zero
  [Nonempty V]
  (g : FinSimpleGraph V) (source target : V) :
  ∀ (dist : V → ENat) (queue : BinaryHeap V), dist source = 0 → (dijkstra_rec g source target dist queue) source = 0 := by
  intro dist queue h
  generalize hsize : BinaryHeap.sizeOf queue = n
  revert queue dist hsize
  induction' n using Nat.strong_induction_on with n ih
  expose_names
  intro dist queue hdist qsize

  by_cases hq : queue.isEmpty
  · simp [dijkstra_rec, hq, hdist]
  -- Non-empty case: extract min, relax neighbors, recurse on smaller heap
  · have hne : queue.isEmpty = false := by exact eq_false_of_ne_true hq
    unfold dijkstra_rec
    simp [hq]

    have qempty :  ¬queue.isEmpty = true  := by grind
    let extract_result := queue.extract_min dist qempty
    let u := extract_result.1
    let queue' := extract_result.2
    set h1 := relaxNeighbors g u dist queue'
    have h1' : h1 = relaxNeighbors g u dist queue' := by grind
    --let (dist', queue'') := h1
    let dist' := Prod.fst h1
    let queue'' := Prod.snd h1
    have dist'_src_zero : dist' source = 0 :=
      relaxNeighbors_preserves_source_zero g source u dist queue' hdist h1 h1'

    -- size decreases: sizeOf queue'' ≤ sizeOf queue' and sizeOf queue' < n
    have hq'_eq : queue' = (queue.extract_min dist qempty).2 := rfl
    have hq'_lt : BinaryHeap.sizeOf queue' < BinaryHeap.sizeOf queue := by
      rw [hq'_eq]
      exact BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false queue hne dist
    have hq''le : BinaryHeap.sizeOf queue'' ≤ BinaryHeap.sizeOf queue' :=
      sizeOf_relaxNeighbors_le g u dist queue'
    have hq''lt : BinaryHeap.sizeOf queue'' < BinaryHeap.sizeOf queue := by
      exact lt_of_le_of_lt hq''le hq'_lt
    have hq''lt' : BinaryHeap.sizeOf queue'' < n := by exact Nat.lt_of_lt_of_eq hq''lt qsize-- Nat.lt_of_lt_of_eq hq'_lt qsize
    -- Apply IH to smaller size
    have := ih
      (BinaryHeap.sizeOf queue'')
      hq''lt'
      dist'
      queue''
      dist'_src_zero
      rfl
    exact this


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
  (g : FinSimpleGraph V) (s : V)
  (is_connected: SimpleGraph.Connected g.toSimpleGraph):
  ∀ v : V, (dijkstra g s v) v = delta g s v := by
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
    exact positiveDistance_of_counterexample g s u u_ne_s is_connected
  obtain ⟨y, hyu_adj, hδ⟩ := existsPredOnShortestPath g s u hpos is_connected
  -- By minimality of `u`, every vertex strictly closer than `u` is
  -- already correct; in particular `y` is correct.
  have hy_lt_u : delta g s y < delta g s u := by simp [hδ]
  have hy_eq : dist y = delta g s y := by
    exact (h_min y hy_lt_u)
  -- When processing `y`, relaxing edge (y,u) ensures the final bound
  -- `dist u ≤ dist y + 1`.
  have h_relax : dist u ≤ dist y + 1 :=
    relaxAdj_final_bound g s v hyu_adj (fun _ _ => by
    intro step u q1 next u2 hu2;
    expose_names;
    have step' : MinGeYInvariant y x u := by simpa using step
    unfold MinGeYInvariant
    intro w hw
    have h1 := BinaryHeap.key_at_y_le_extracted_min y hu2 hu2.1 (by grind) hw
    exact h1
    ) (fun _ _ _ _ => by
    intro q' next u2 hu2;
    expose_names
    have helper : next.2.isEmpty = false := by grind
    have h1 := BinaryHeap.key_at_y_le_extracted_min y next next.1 (by grind) hu2
    exact h1
    )
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
