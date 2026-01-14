import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Projects.Lindmar_Joost.BinaryHeap

open Finset SimpleGraph
open BinaryTree BinaryHeap

set_option autoImplicit true

structure fin_simple_graph (V : Type u) [Fintype V] [DecidableEq V]  extends SimpleGraph V

noncomputable
instance  fintype_fin_simple_graph {V : Type u} [Fintype V] [DecidableEq V] (G : fin_simple_graph V) (v : V): Fintype (G.neighborSet v) :=  Fintype.ofFinite ↑(G.neighborSet v)

variable  {V : Type*} [Fintype V] [DecidableEq V]

def min_y_invariant [Nonempty V] (y : V) (p : (V → ENat) × BinaryHeap V) (hh : ¬ isEmpty p.2) : Prop :=
  ∀ u1 : V, Prod.fst (p.2.extract_min p.1 hh) = u1 → p.1 y ≤ p.1 u1

noncomputable def relax_neighbors (g : fin_simple_graph V) (u : V) (dist : V → ENat) (queue : BinaryHeap V) : (V → ENat) × (BinaryHeap V) :=
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

theorem sizeOf_relax_neighbors_le
    (g : fin_simple_graph V) (u : V) (dist : V → ENat) (q : BinaryHeap V) :
    BinaryHeap.sizeOf (Prod.snd (relax_neighbors g u dist q)) ≤ BinaryHeap.sizeOf q := by
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
  simp [relax_neighbors]
  induction (g.neighborFinset u).val.toList generalizing dist q with
  | nil =>
    simp
  | cons v vs ih =>
    simp
    specialize ih
    cases acc : f (dist, q) v with
    | mk dist' queue' =>
      have hle : BinaryHeap.sizeOf queue' ≤ BinaryHeap.sizeOf q := by
        dsimp [f] at acc
        split at acc
        case isTrue h =>
          injection acc with h_dist h_queue
          subst h_queue
          apply sizeOf_decrease_priority_le
        case isFalse h =>
          injection acc with h_dist h_queue
          subst h_queue
          exact le_refl _
      have ih_used := ih dist' queue'
      simp_all
      have := Nat.le_trans (ih dist' queue') hle
      simpa [f, acc] using this


lemma relax_neighbors_nonincrease
    (g : fin_simple_graph V) (u : V) (dist : V → ENat) (q : BinaryHeap V) :
    ∀ x, (Prod.fst (relax_neighbors g u dist q)) x ≤ dist x := by
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
  intro x; simpa [relax_neighbors, neighbors, f] using fold neighbors dist q x

lemma relax_neighbors_nonempty_of_input_nonempty [Nonempty V] (g : fin_simple_graph V) (u : V) (dist : V → ENat) (q : BinaryHeap V) :
  q.isEmpty = false → (relax_neighbors g u dist q).2.isEmpty = false := by
  intro hq_ne
  unfold relax_neighbors
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
    · apply ih
      rw [BinaryHeap.decrease_priority_preserves_isEmpty]
      exact hqueue
    · exact ih d queue hqueue

lemma relax_neighbors_nonempty [Nonempty V] (g : fin_simple_graph V) (u : V) (dist : V → ENat) (q : BinaryHeap V) :
  q.isEmpty = false → (relax_neighbors g u dist q).2.isEmpty = false :=
  relax_neighbors_nonempty_of_input_nonempty g u dist q

noncomputable def dijkstra_rec [Nonempty V] (g: fin_simple_graph V) (source : V) (target : V) (dist : V → ENat) (queue : BinaryHeap V) : V → ENat :=
  if hq: queue.isEmpty then dist
  else
    have hne : ¬ queue.isEmpty = true := by exact  hq
    let extract_result := queue.extract_min dist hne
    let u := extract_result.1
    let queue' := extract_result.2
    let relax_result := relax_neighbors g u dist queue'
    let dist' := relax_result.1
    let queue'' := relax_result.2
    dijkstra_rec g source target dist' queue''

termination_by queue.sizeOf
decreasing_by
  have hne : queue.isEmpty = false := by exact eq_false_of_ne_true hq
  have hq'_eq : queue' = (queue.extract_min dist (by exact hq)).2 := rfl
  have hq''_eq : queue'' = (relax_neighbors g u dist queue').2 := rfl
  calc queue''.sizeOf
      = (relax_neighbors g u dist queue').2.sizeOf := by rw [hq''_eq]
    _ ≤ queue'.sizeOf := sizeOf_relax_neighbors_le g u dist queue'
    _ = (queue.extract_min dist (by exact hq)).2.sizeOf := by rw [hq'_eq]
    _ < queue.sizeOf := BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false queue hne dist

lemma dijkstra_rec_le_input_map
  [Nonempty V]
  (g : fin_simple_graph V) (s t : V) :
  ∀ (dist : V → ENat) (queue : BinaryHeap V) (x : V),
    (dijkstra_rec g s t dist queue) x ≤ dist x := by
  intro dist queue x
  generalize hsize : BinaryHeap.sizeOf queue = n
  revert queue dist hsize
  induction' n using Nat.strong_induction_on with n ih
  intro dist queue hsize
  by_cases hq : queue.isEmpty
  · simp [dijkstra_rec, hq]
  · have hne : queue.isEmpty = false := by exact eq_false_of_ne_true hq
    unfold dijkstra_rec
    simp [hq]
    have hne_proof : ¬queue.isEmpty = true := by exact hq
    let extract_result := queue.extract_min dist hne_proof
    let u := extract_result.1
    let queue' := extract_result.2
    let relax_result := relax_neighbors g u dist queue'
    let dist' := relax_result.1
    let queue'' := relax_result.2
    have hq'_eq : queue' = (queue.extract_min dist hne_proof).2 := rfl
    have hq'_lt : BinaryHeap.sizeOf queue' < BinaryHeap.sizeOf queue := by
      rw [hq'_eq]
      exact BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false queue hne dist
    have hq''le : BinaryHeap.sizeOf queue'' ≤ BinaryHeap.sizeOf queue' :=
      sizeOf_relax_neighbors_le g u dist queue'
    have hq''lt : BinaryHeap.sizeOf queue'' < BinaryHeap.sizeOf queue :=
      lt_of_le_of_lt hq''le hq'_lt
    have hq''lt' : BinaryHeap.sizeOf queue'' < n := by
      exact Nat.lt_of_lt_of_eq hq''lt hsize
    have hIH := ih (BinaryHeap.sizeOf queue'') hq''lt' dist' queue'' rfl
    have hmono := hIH
    have hstep_noninc : dist' x ≤ dist x := by
      simpa using relax_neighbors_nonincrease g u dist queue' x
    exact le_trans hmono hstep_noninc

noncomputable def dijkstra [Nonempty V] (g : fin_simple_graph V) (source : V) (target : V) : V → ENat  :=
  let dist : V → ENat := fun v => if v = source then 0 else ⊤
  let queue := Finset.univ.val.toList.foldl (fun acc v => acc.add v dist) BinaryHeap.empty
  dijkstra_rec g source target dist queue

noncomputable def delta (g : fin_simple_graph V) (s v : V) : Nat :=
  (SimpleGraph.dist (G := (by exact g.toSimpleGraph)) s v)

lemma never_underestimates
  [Nonempty V]
  (g : fin_simple_graph V) (s t : V) :
  ∀ u : V, (delta g s u : ENat) ≤ (dijkstra g s t) u := by
  intro u
  admit

lemma minimal_counterexample
  [Nonempty V]
  (g : fin_simple_graph V) (s : V)
  (dist : V → ENat)
  (h : ∃ u, dist u ≠ delta g s u) :
  ∃ u, dist u ≠ delta g s u ∧ ∀ w, delta g s w < delta g s u → dist w = delta g s w := by
  let S : Finset V := (Finset.univ.filter (fun u => dist u ≠ delta g s u))
  have hS_ne : S.Nonempty := by
    rcases h with ⟨u, hu⟩
    refine Finset.nonempty_of_ne_empty ?hcontr
    intro h_empty
    have : u ∈ S := by
      have : u ∈ Finset.univ := by simp
      have : u ∈ Finset.univ.filter (fun u => dist u ≠ delta g s u) := by
        simp [hu]
      exact this
    simpa [h_empty]
  obtain ⟨u, huS, hmin⟩ := Finset.exists_min_image S (fun x : V => delta g s x) (by rcases hS_ne with ⟨x, hx⟩; exact ⟨x, hx⟩)
  have hu_ne : dist u ≠ delta g s u := by
    have : u ∈ Finset.univ ∧ dist u ≠ delta g s u := by
      simpa [S] using (Finset.mem_filter.mp huS)
    exact this.2
  refine ⟨u, hu_ne, ?hcloser⟩
  intro w hw_lt
  by_contra h_w_ne
  have hwS : w ∈ S := by
    have : w ∈ Finset.univ := by simp
    have : w ∈ Finset.univ.filter (fun u => dist u ≠ delta g s u) := by
      simp [h_w_ne]
    exact this
  have hmin_le : delta g s u ≤ delta g s w := hmin w hwS
  exact (not_le_of_gt hw_lt) hmin_le

lemma positive_distance_of_counterexample
  [Nonempty V]
  (g : fin_simple_graph V) (s : V) (u : V) (u_ne_s : u ≠ s)
  (is_connected : SimpleGraph.Connected g.toSimpleGraph)
  :
  0 < delta g s u := by
  unfold delta
  simp_all
  refine Nat.pos_of_ne_zero ?_
  intro hzero
  have := (SimpleGraph.Reachable.dist_eq_zero_iff (G := g.toSimpleGraph) (u := s) (v := u))
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

lemma delta_adj_step_ENat
  (g : fin_simple_graph V) (s u v : V)
  (hAdj : g.toSimpleGraph.Adj u v)
  (is_connected: SimpleGraph.Connected g.toSimpleGraph) :
  (delta g s v : ENat) ≤ (delta g s u : ENat) + 1 := by
  have h_nat : delta g s v ≤ delta g s u + 1 := by
    unfold delta
    have htri :  g.toSimpleGraph.dist s v ≤ g.toSimpleGraph.dist s u + g.toSimpleGraph.dist u v := SimpleGraph.Connected.dist_triangle (G := g.toSimpleGraph) is_connected
    have hduv := (SimpleGraph.dist_eq_one_iff_adj (G := g.toSimpleGraph)).mpr hAdj
    calc
      (g.toSimpleGraph).dist s v ≤ (g.toSimpleGraph).dist s u + (g.toSimpleGraph).dist u v := htri
      _ = (g.toSimpleGraph).dist s u + 1 := by rw [hduv]
  exact_mod_cast h_nat

lemma exists_pred_on_shortest_path
  (g : fin_simple_graph V) (s u : V)
  (hpos : 0 < delta g s u)
  (is_connected: SimpleGraph.Connected g.toSimpleGraph):
  ∃ y : V, g.toSimpleGraph.Adj y u ∧ delta g s u = delta g s y + 1 := by
  have hconn : SimpleGraph.Reachable g.toSimpleGraph s u := by
    exact SimpleGraph.Reachable.of_dist_ne_zero (by
      simpa [delta] using (Nat.ne_of_gt hpos))
  obtain ⟨p, hp⟩ := SimpleGraph.Reachable.exists_walk_length_eq_dist hconn
  have hlen_pr : (p.reverse).length = delta g s u := by
    have h := SimpleGraph.Walk.length_reverse p
    have : (p.reverse).length = p.length := by simp
    simpa [delta, this] using hp
  have hnonzero : (p.reverse).length ≠ 0 := by
    simpa [hlen_pr] using (Nat.ne_of_gt hpos)
  cases hpr : p.reverse with
    | nil =>
      simp_all
    | cons hAdj tail =>
    rename_i y
    let pr := p.reverse
    have hlen_pr : pr.length = delta g s u := by
      have h := SimpleGraph.Walk.length_reverse p
      have : pr.length = p.length := by simp [pr]
      simpa [delta, this] using hp
    have hnonzero : pr.length ≠ 0 := by
      simpa [hlen_pr] using (Nat.ne_of_gt hpos)
    refine ⟨y, SimpleGraph.Adj.symm hAdj, ?_⟩
    have hy_le_tail : delta g s y ≤ tail.length := by
      rw [delta, SimpleGraph.dist_comm]
      simp_all
      exact dist_le tail
    have hlen_cons : pr.length = tail.length + 1 := by
      change (p.reverse).length = tail.length + 1
      rw [hpr]
      rw [SimpleGraph.Walk.length_cons]

    have h_le : delta g s y + 1 ≤ delta g s u := by
      calc
        delta g s y + 1 ≤ tail.length + 1 := by apply Nat.add_le_add_right; exact hy_le_tail
        _ = pr.length := by rw [hlen_cons]
        _ = delta g s u := by rw [hlen_pr]
    have h_ge : delta g s u ≤ delta g s y + 1 := by
        have h_enat : (delta g s u : ENat) ≤ (delta g s y : ENat) + 1 :=
          delta_adj_step_ENat g s y u (SimpleGraph.Adj.symm hAdj) is_connected
        exact_mod_cast h_enat
    exact Nat.le_antisymm h_ge h_le

lemma adj_mem_neighbor_finset
  (g : fin_simple_graph V) (u v : V)
  (hAdj : g.toSimpleGraph.Adj u v) : v ∈ g.neighborFinset u := by
  have hEquiv := SimpleGraph.mem_neighborFinset (G := g.toSimpleGraph) (v := u) (w := v)
  have hv : v ∈ (g.toSimpleGraph).neighborFinset u := hEquiv.mpr hAdj
  simpa using hv

lemma mem_neighbor_finset_adj
  (g : fin_simple_graph V) (u v : V)
  (h : v ∈ g.neighborFinset u) : g.toSimpleGraph.Adj u v := by
    have hv : v ∈ (g.toSimpleGraph).neighborFinset u := by simpa using h
    have hEquiv := SimpleGraph.mem_neighborFinset (G := g.toSimpleGraph) (v := u) (w := v)
    exact hEquiv.mp hv

lemma extracted_value_never_decreases_after_step
  [Nonempty V]
  (g : fin_simple_graph V) (s t y : V)
  (dist : V → ENat) (q : BinaryHeap V)
  (hq : ¬q.isEmpty = true)
  (hy : Prod.fst (q.extract_min dist hq) = y)
    (hInvPreserve : ∀ p : (V → ENat) × BinaryHeap V,
      ∀ (hh : ¬ isEmpty p.2), min_y_invariant (V := V) y p hh →
      ∀ (hne : ¬p.2.isEmpty = true),
      let step := p.2.extract_min p.1 hne
      let u := Prod.fst step
      let q1 := Prod.snd step
      let next := relax_neighbors g u p.1 q1;
      ∀ (hhNext : ¬ isEmpty next.2), min_y_invariant (V := V) y next hhNext)
  :
  let q' := Prod.snd (q.extract_min dist hq); let next := relax_neighbors g y dist q';
  ∀ (hhNext : ¬ isEmpty next.2), min_y_invariant (V := V) y next hhNext →
  next.1 y ≤ (dijkstra_rec g s t next.1 next.2) y := by
  let q' := Prod.snd (q.extract_min dist hq)
  let next := relax_neighbors g y dist q'
  have nondec : ∀ (p : (V → ENat) × BinaryHeap V) (n : Nat),
      BinaryHeap.sizeOf p.2 = n →
      ∀ (hh : ¬ isEmpty p.2), min_y_invariant (V := V) y p hh →
      p.1 y ≤ dijkstra_rec g s t p.1 p.2 y := by
    intro p n
    induction' n using Nat.strong_induction_on with k h generalizing p
    intro hsz' hh hmin
    expose_names
    by_cases hEmpty : p.2.isEmpty
    · unfold dijkstra_rec; simp [hEmpty]
    · unfold dijkstra_rec; simp [hEmpty]
      have hne_proof : ¬p.2.isEmpty = true := by exact hEmpty
      let extract_result := p.2.extract_min p.1 hne_proof
      let u1 := extract_result.1
      let q1 := extract_result.2
      let next2 := relax_neighbors g u1 p.1 q1
      have hmono : (dijkstra_rec g s t next2.1 next2.2) y ≤ next2.1 y :=
        dijkstra_rec_le_input_map g s t next2.1 next2.2 y
      have hpreserve_y : p.1 y ≤ next2.1 y := by
        have heap_min_ge_y : p.1 y ≤ p.1 u1 := by
          exact hmin u1 rfl
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
        have all_ne_u1 : ∀ v, v ∈ neighbors1 → v ≠ u1 := by
          intro v hv
          have hvF : v ∈ g.neighborFinset u1 := by
            simpa [neighbors1] using (Finset.mem_toList.mp hv)
          have hvAdj : g.toSimpleGraph.Adj u1 v := mem_neighbor_finset_adj g u1 v hvF
          have hIr : ¬ g.toSimpleGraph.Adj u1 u1 := by simp
          intro h; subst h; exact hIr.elim hvAdj
        have step_preserve_y : ∀ (d : V → ENat) (pq : BinaryHeap V) (v : V),
            v ≠ u1 → (p.1 y ≤ d u1 + 1) → (d y = p.1 y) →
            (Prod.fst (f1 (d, pq) v)) y = d y := by
          intro d pq v hv_ne_u1 hy_ge hdy
          dsimp [f1]
          by_cases hlt : d u1 + 1 < d v
          · by_cases hyv : v = y
            · subst hyv
              simp [hdy]
              simp_all
              have hchain : d u1 + 1 < d u1 + 1 := by
                calc
                  d u1 + 1 < d v := by exact lt_of_lt_of_eq hlt (id (Eq.symm hdy))
                  _ = p.1 v := by rw [hdy]
                  _ ≤ d u1 + 1 := hy_ge
              exact False.elim (lt_irrefl _ hchain)
            · simp [hlt, hdy]
              intro eq
              exfalso
              have eq2 : v = y := by exact id (Eq.symm eq)
              contradiction
          · simp [hlt]
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
              have h_u1_pres : d' u1 = d u1 := by
                dsimp [f1] at hacc
                by_cases hlt : d u1 + 1 < d v
                · simp [hlt] at hacc
                  cases hacc
                  have : d' = (fun x => if x = v then d u1 + 1 else d x) := by
                    expose_names; exact left.symm
                  simp [this]
                  intro eq
                  exact False.elim (hv_ne_u1 (id (Eq.symm eq)))
                · simp [hlt] at hacc
                  cases hacc
                  have : d' = d := by expose_names; exact left.symm
                  simp [this]
              have hy_ge' : p.1 y ≤ d' u1 + 1 := by exact le_of_le_of_eq hy_ge (congrFun (congrArg HAdd.hAdd (id (Eq.symm h_u1_pres))) 1)
              have hdy' : d' y = p.1 y := by simpa [h_y_pres] using hdy
              have hAllNe_vs : ∀ w, w ∈ vs → w ≠ u1 := by
                intro w hw
                have : w ∈ v :: vs := by simpa [List.mem_cons] using Or.inr hw
                exact hAllNe w this
              have hih := ih q' d' hy_ge' hdy' hAllNe_vs
              simpa [List.foldl, f1, hacc]
        have hy_ge1 : p.1 y ≤ p.1 u1 + 1 := by
          have : p.1 u1 ≤ p.1 u1 + 1 := by
            have h01 : (0 : ℕ∞) ≤ 1 := by decide
            simp
          exact le_trans heap_min_ge_y this
        have : (Prod.fst (List.foldl f1 (p.1, q1) neighbors1)) y = p.1 y :=
          preserve_eq_list neighbors1 q1 p.1 hy_ge1 rfl all_ne_u1
        have hEqY : next2.1 y = p.1 y := by simpa [relax_neighbors, neighbors1, f1] using this
        simp [hEqY]
      have hq1_eq : q1 = (p.2.extract_min p.1 hEmpty).2 := rfl
      have hlt_extract : BinaryHeap.sizeOf q1 < BinaryHeap.sizeOf p.2 := by
        rw [hq1_eq]
        exact BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false p.2 (by exact eq_false_of_ne_true hEmpty) p.1
      have hle_relax : BinaryHeap.sizeOf next2.2 ≤ BinaryHeap.sizeOf q1 :=
        sizeOf_relax_neighbors_le g u1 p.1 q1
      have hlt_total : BinaryHeap.sizeOf next2.2 < BinaryHeap.sizeOf p.2 :=
        lt_of_le_of_lt hle_relax hlt_extract
      have hlt_k : BinaryHeap.sizeOf next2.2 < k := by simpa [hsz'] using hlt_total
      by_cases hEmpty2 : next2.2.isEmpty
      · have : p.1 y ≤ dijkstra_rec g s t next2.1 next2.2 y := by
          have : p.1 y ≤ next2.1 y := hpreserve_y
          simpa [dijkstra_rec, hEmpty2] using this
        exact this
      · have hhNext : ¬ next2.2.isEmpty = true := by exact hEmpty2
        have hmin_next : min_y_invariant (V := V) y next2 hhNext := by
          have hpres := hInvPreserve p hh hmin hne_proof
          exact hpres hhNext
        have hih' := h (BinaryHeap.sizeOf next2.2) hlt_k next2 rfl hhNext hmin_next
        exact le_trans hpreserve_y hih'
  intro q' next2 hNext2 hInvNext
  clear hInvPreserve next
  exact nondec next2 next2.2.sizeOf rfl hNext2 hInvNext

lemma extracted_value_is_final_lemma
  [Nonempty V]
  (g : fin_simple_graph V) (s t y : V)
  (dist : V → ENat) (q : BinaryHeap V)
  (hq : ¬q.isEmpty = true)
  (qempty : ¬q.isEmpty = true)
  (hy : Prod.fst (q.extract_min dist qempty) = y)

    (hInvPreserve : ∀ p : (V → ENat) × BinaryHeap V,
      ∀ (hh : ¬ isEmpty p.2), min_y_invariant (V := V) y p hh →
      ∀ (hne : ¬p.2.isEmpty = true),
      let step := p.2.extract_min p.1 hne
      let u := Prod.fst step
      let q1 := Prod.snd step
      let next := relax_neighbors g u p.1 q1;
      ∀ (hhNext : ¬ isEmpty next.2), min_y_invariant (V := V) y next hhNext)
  :
  let q' := Prod.snd (q.extract_min dist qempty); let next := relax_neighbors g y dist q';
  ∀ (hhNext : ¬ isEmpty next.2), min_y_invariant (V := V) y next hhNext →
  dist y = (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y := by
  let q' := Prod.snd (q.extract_min dist hq)
  let next := relax_neighbors g y dist q'
  have h_final_le_dist : (dijkstra_rec g s t next.1 next.2) y ≤ dist y := by
    have hmono : (dijkstra_rec g s t next.1 next.2) y ≤ next.1 y :=
      dijkstra_rec_le_input_map g s t next.1 next.2 y
    have hstep_noninc : next.1 y ≤ dist y := by
      simpa using relax_neighbors_nonincrease g y dist q' y
    exact le_trans hmono hstep_noninc
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
    have hAdj_vy : g.toSimpleGraph.Adj y v := mem_neighbor_finset_adj g y v hvF
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
            intro eq
            exact False.elim (hv_ne_y (id (Eq.symm eq)))
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
    simpa [relax_neighbors, neighbors, f] using this
  have hlemma := extracted_value_never_decreases_after_step g s t y dist q hq hy hInvPreserve
  intro hhN hInvN hhNext invariant
  have hsteps := hlemma hhNext invariant
  apply le_antisymm
  · clear preserve_y hlemma invariant hhNext all_ne_neighbors f hInvPreserve h_final_le_dist hy
    rw [← hnext_y_eq]
    exact hsteps
  · clear preserve_y hlemma invariant hhNext all_ne_neighbors f hInvPreserve hy hsteps
    subst hInvN
    subst next
    exact h_final_le_dist

lemma relax_neighbors_adj_upper
(hAdj : g.Adj y u) :
      ∀ (dist : V → ENat) (q : BinaryHeap V),
        (Prod.fst (relax_neighbors g y dist q)) u ≤ dist y + 1 := by
    intro dist q
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
    have hu_mem_fin : u ∈ g.neighborFinset y := adj_mem_neighbor_finset g y u hAdj
    have hu_mem_list : u ∈ neighbors := by
      simpa [neighbors] using (Finset.mem_toList.mpr hu_mem_fin)
    have hnodup_neighbors : neighbors.Nodup := by
      simpa [neighbors] using (g.neighborFinset y).nodup_toList
    have step_u_bound : ∀ (d : V → ENat) (pq : BinaryHeap V),
        (Prod.fst (f (d, pq) u)) u ≤ d y + 1 := by
      intro d pq
      dsimp [f]
      by_cases hlt : d y + 1 < d u
      · simp [hlt]
      · have hle : d u ≤ d y + 1 := by
          have : ¬ d u > d y + 1 := by simpa [gt_iff_lt] using hlt
          exact le_of_not_gt this
        simp [hlt, hle]

    have step_other_preserve : ∀ (d : V → ENat) (pq : BinaryHeap V) (v : V),
        v ≠ u → (Prod.fst (d, pq)) u ≤ d y + 1 → (Prod.fst (f (d, pq) v)) u ≤ d y + 1 := by
      intro d pq v hv_ne hbound
      dsimp [f]
      by_cases hlt : d y + 1 < d v
      · simp_all
        by_cases eq : u = v
        · simp [eq]
        · simp [eq]
          exact hbound
      · simp [hlt, hbound]

    have preserve_no_u : ∀ (l : List V) (d : V → ENat) (pq : BinaryHeap V),
        u ∉ l → (Prod.fst (d, pq)) u ≤ d y + 1 →
        (Prod.fst (List.foldl f (d, pq) l)) u ≤ d y + 1 := by
      intro l
      induction l with
      | nil => intro d pq _ hb; simpa using hb
      | cons v vs ih =>
        intro d pq hu_not hb
        have hv_ne_u : v ≠ u := by
          simp
          clear step_u_bound step_other_preserve ih f
          intro neq
          subst neq
          rw [show (v ∉ v :: vs) = (v ∈ v :: vs → False) from rfl] at hu_not
          apply hu_not
          exact List.mem_cons_self
        cases hacc : f (d, pq) v with
        | mk d' pq' =>
          have hb' : (Prod.fst (d', pq')) u ≤ d y + 1 := by
            have := step_other_preserve d pq v hv_ne_u hb
            simpa [f, hacc] using this
          have hu_not_vs : u ∉ vs := by
            exact List.not_mem_of_not_mem_cons hu_not
          simp_all
          have hdy : d' y = d y := by
            simp [f] at hacc
            by_cases hlt : d y + 1 < d v
            · simp [hlt] at hacc
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
          have hb'' : d' u ≤ d' y + 1 := by
            rw [hdy]
            exact hb'
          rw [← hdy]
          exact ih d' pq' hb''

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
          subst hv_eq
          cases hacc : f (d, pq) u with
          | mk d1 q1 =>
            have h_d1y : d1 y = d y := by
              by_cases hlt : d y + 1 < d u
              · have : d1 = fun x => if x = u then d y + 1 else d x := by
                  simp [f, hlt] at hacc
                  cases hacc
                  expose_names
                  exact left.symm
                simp [this]
                intro eq
                exact False.elim (hAllNe u hmem (id (Eq.symm eq)))
              · have : d1 = d := by
                  simp [f, hlt] at hacc
                  cases hacc
                  expose_names
                  exact left.symm
                simp [this]

            have hfold_eq : (List.foldl f (d, pq) (u :: vs)).1 u = (List.foldl f (d1, q1) vs).1 u := by simp [List.foldl, f, hacc]
            rw [hfold_eq, ← h_d1y]
            apply preserve_no_u vs d1 q1
            · have hu_not_vs : u ∉ vs := (List.nodup_cons.mp hnodup).1
              exact hu_not_vs
            · have h_step : (Prod.fst (f (d, pq) u)) u ≤ d y + 1 := step_u_bound d pq
              simpa [hacc, h_d1y] using h_step
        | inr hu_in_vs =>
          have hv_ne_u : v ≠ u := by
            intro hv_eq
            subst hv_eq
            exact (List.nodup_cons.mp hnodup).1 hu_in_vs
          cases hacc : f (d, pq) v with
          | mk d' q' =>
            have hdy : d' y = d y := by
              simp [f] at hacc
              by_cases hlt : d y + 1 < d v
              · simp_all [f]
                clear ih preserve_no_u step_other_preserve step_u_bound
                cases hacc
                expose_names
                clear right
                subst left
                simp
                intro eq
                exact False.elim (hv_ne_y (id (Eq.symm eq)))
              · clear ih preserve_no_u step_other_preserve step_u_bound
                simp_all
            have hih := ih d' q' hnodup_vs hAllNe_vs hu_in_vs
            simpa [List.foldl, f, hacc, hdy] using hih

    have all_ne_neighbors : ∀ v, v ∈ neighbors -> v ≠ y := by
      intro v hv
      have hvF : v ∈ (g.neighborFinset y) := by
        simpa [neighbors] using (Finset.mem_toList.mp hv)
      have hAdj : g.toSimpleGraph.Adj y v := mem_neighbor_finset_adj g y v hvF
      have hIr : ¬ g.toSimpleGraph.Adj y y := by simp
      intro hEq; subst hEq; exact hIr.elim hAdj

    have : (Prod.fst (List.foldl f (dist, q) neighbors)) u ≤ dist y + 1 :=
      bound_if_mem_nodup neighbors dist q hnodup_neighbors all_ne_neighbors hu_mem_list
    simpa [relax_neighbors, neighbors, f] using this

lemma exists_extract_or_top [Nonempty V]
  (g : fin_simple_graph V) (s t : V)
  {y u : V} (hAdj : g.toSimpleGraph.Adj y u)
    (hInvPreserve : ∀ p : (V → ENat) × BinaryHeap V,
      ∀ (hh : ¬ isEmpty p.2), min_y_invariant (V := V) y p hh →
      ∀ (hne : ¬p.2.isEmpty = true),
      let step := p.2.extract_min p.1 hne
      let u := Prod.fst step
      let q1 := Prod.snd step
      let next := relax_neighbors g u p.1 q1;
      ∀ (hhNext : ¬ isEmpty next.2), min_y_invariant (V := V) y next hhNext)
    (hInvInit : ∀ (dist : V → ENat) (q : BinaryHeap V) (hne : ¬q.isEmpty = true),
      Prod.fst (q.extract_min dist hne) = y →
      let q' := Prod.snd (q.extract_min dist hne)
      let next := relax_neighbors g y dist q'
      ∀ (hhNext : ¬ isEmpty next.2), min_y_invariant (V := V) y next hhNext)
      :
      (dijkstra g s t) y = ⊤ ∨
      (∃ (dist : V → ENat) (q : BinaryHeap V) (hne : ¬q.isEmpty = true),
          Prod.fst (q.extract_min dist hne) = y ∧
            (let q' := Prod.snd (q.extract_min dist hne);
                 let next := relax_neighbors g y dist q'
             (dijkstra g s t) = dijkstra_rec g s t (Prod.fst next) (Prod.snd next))) := by
    by_cases hyTop : (dijkstra g s t) y = ⊤
    · left; exact hyTop
    · right
      set dist0 : V → ENat := fun v => if v = s then 0 else ⊤
      set q0 := Finset.univ.val.toList.foldl (fun acc v => acc.add v dist0) BinaryHeap.empty

      have dijkstra_def : (dijkstra g s t) y = dijkstra_rec g s t dist0 q0 y := rfl

      have hyTop' : ¬(dijkstra_rec g s t dist0 q0 y = ⊤) := by
        simpa [dijkstra_def] using hyTop

      have search :
        ∀ (n : Nat), ∀ (d : V → ENat) (q : BinaryHeap V), BinaryHeap.sizeOf q ≤ n →
          (q.isEmpty = true ∧ d y = ⊤) ∨
          (q.isEmpty = false ∧
           ∃ (next : (V → ENat) × BinaryHeap V),
            (dijkstra_rec g s t d q : V → ENat) = dijkstra_rec g s t next.1 next.2) := by
          intro n
          refine Nat.strong_induction_on n ?ih
          intro n1 ih d q hle

          by_cases hq : q.isEmpty
          · left
            exact ⟨hq, sorry⟩
          · right
            have hne : ¬q.isEmpty = true := by simp [hq]
            have hq_false : q.isEmpty = false := by simp [hq]
            refine ⟨hq_false, ?_⟩
            let step := q.extract_min d hne
            let u := Prod.fst step
            set q' := Prod.snd step with hq'_def
            set next := relax_neighbors g u d q' with hnext_def
            use next
            unfold dijkstra_rec
            simp [hq]
            simp_all
            sorry


      have hsearch0 := search (BinaryHeap.sizeOf q0) dist0 q0 le_rfl
      cases hsearch0 with
      | inl htop =>
        have : dijkstra_rec g s t dist0 q0 y = dist0 y := by
          simp [dijkstra_rec, htop.1]
        rw [this] at hyTop'
        exact False.elim (hyTop' htop.2)
      | inr h =>
        obtain ⟨hq0, next, heq⟩ := h
        use dist0, q0
        have hne : ¬q0.isEmpty = true := by simp [hq0]
        use hne
        sorry

lemma relax_adj_final_bound
  [Nonempty V]
  (g : fin_simple_graph V) (s t : V)
  {y u : V} (hAdj : g.toSimpleGraph.Adj y u)

  (hInvPreserve : ∀ p : (V → ENat) × BinaryHeap V,
    ∀ (hh : ¬ isEmpty p.2), min_y_invariant (V := V) y p hh →
    ∀ (hne : ¬p.2.isEmpty = true),
    let step := p.2.extract_min p.1 hne
    let u := Prod.fst step
    let q1 := Prod.snd step
    let next := relax_neighbors g u p.1 q1;
    ∀ (hhNext : ¬ isEmpty next.2), min_y_invariant (V := V) y next hhNext)
  (hInvInit : ∀ (dist : V → ENat) (q : BinaryHeap V) (hne : ¬q.isEmpty = true),
    Prod.fst (q.extract_min dist hne) = y →
    let q' := Prod.snd (q.extract_min dist hne)
    let next := relax_neighbors g y dist q'
    ∀ (hhNext : ¬ isEmpty next.2), min_y_invariant (V := V) y next hhNext)
  :
  (dijkstra g s t) u ≤ (dijkstra g s t) y + 1 := by

  have enat_top_add_one_eq_top : (⊤ : ENat) + 1 = (⊤ : ENat) := by rfl

  dsimp [dijkstra]
  let dist0 : V → ENat := fun v => if v = s then 0 else ⊤
  let queue0 := Finset.univ.val.toList.foldl (fun acc v => acc.add v dist0) BinaryHeap.empty

  have hfinal_or_step := exists_extract_or_top g s t hAdj hInvPreserve hInvInit
  cases hfinal_or_step with
  | inl hyTop =>
    have htop : (dijkstra_rec g s t dist0 queue0) y = ⊤ := by
      simpa [dijkstra] using hyTop
    have hle_top : (dijkstra_rec g s t dist0 queue0) u ≤ (⊤ : ENat) := le_top
    have : (dijkstra_rec g s t dist0 queue0) u ≤ (dijkstra_rec g s t dist0 queue0) y + 1 := by simp [htop]
    exact this
  | inr hstep =>
    rcases hstep with ⟨dist, q, hne, hyExtract, hfinEq⟩
    have qempty : ¬q.isEmpty = true := hne
    let q' := Prod.snd (q.extract_min dist qempty)
    let next := relax_neighbors g y dist q'
    have hmono : ∀ x, (dijkstra_rec g s t dist q) x ≤ (Prod.fst next) x := by
      intro x
      unfold dijkstra_rec
      simp [hne, hyExtract]
      exact dijkstra_rec_le_input_map g s t (Prod.fst next) (Prod.snd next) x
    have relax_neighbors_adj_upper:  ∀ (dist : V → ℕ∞) (q : BinaryHeap V), (relax_neighbors g y dist q).1 u ≤ dist y + 1 := relax_neighbors_adj_upper hAdj
    have hrelax : (Prod.fst next) u ≤ dist y + 1 := relax_neighbors_adj_upper dist q'
    have hstable : dist y = (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y := by
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
          have hAdj_vy : g.toSimpleGraph.Adj y v := mem_neighbor_finset_adj g y v hvF
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
                    intro eq
                    exact False.elim (hv_ne_y (id (Eq.symm eq)))
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
          simpa [relax_neighbors, neighbors, f] using this
        have : dist y = (dijkstra_rec g s t next.1 next.2) y := by
          simp [dijkstra_rec, hEmptyNext, hnext_y_eq]
        exact this
      · have hInv0 : min_y_invariant (V := V) y next hEmptyNext := by
          exact (hInvInit dist q hne hyExtract hEmptyNext)
        have h1 := extracted_value_is_final_lemma g s t y dist q qempty qempty hyExtract hInvPreserve
        exact h1 hEmptyNext hInv0
    have hfinal_u : (dijkstra_rec g s t dist0 queue0) u = (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) u := by
      exact congrFun hfinEq u
    have hfinal_y : (dijkstra_rec g s t dist0 queue0) y = (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y := by
      exact congrFun hfinEq y
    have hchain : (dijkstra_rec g s t dist q) u ≤ (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y + 1 := by
      have hrelax' : next.1 u ≤ (dijkstra_rec g s t next.1 next.2) y + 1 := by
        rw [←hstable]
        exact hrelax
      exact le_trans (hmono u) hrelax'
    have htarget : (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) u ≤ (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y + 1 := by
      have hmono' : (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) u ≤ next.1 u := by
        exact dijkstra_rec_le_input_map g s t (Prod.fst next) (Prod.snd next) u
      have hrelax' : next.1 u ≤ (dijkstra_rec g s t (Prod.fst next) (Prod.snd next)) y + 1 := by
        rw [←hstable]
        exact hrelax
      exact le_trans hmono' hrelax'
    rw [hfinal_u]
    rw[hfinal_y]
    exact htarget




lemma relax_neighbors_preserves_source_zero
  (g : fin_simple_graph V) (source u : V)
  (dist : V → ENat) (q : BinaryHeap V)
  (h0 : dist source = 0)
  (h1 := relax_neighbors g u dist q)
  (h1' : h1 = relax_neighbors g u dist q)
  :
  (Prod.fst h1) source = 0 := by
  have enat_add_one_not_lt_zero : ∀ x : ENat, ¬ x + 1 < 0 := by
    intro x; exact ENat.not_lt_zero (x + 1)

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
        have h0'' : d' source = 0 := by
          have := step_preserve d pq v h0'
          simpa [acc] using this
        have := ih d' pq' h0''
        simpa [List.foldl, f, acc]

  have : (Prod.fst (List.foldl f (dist, q) neighbors)) source = 0 :=
    fold_preserve neighbors dist q h0
  have h1' : h1 =  relax_neighbors g u dist q := by exact h1'
  simpa [relax_neighbors, neighbors, f, h1'] using this

lemma dijkstra_rec_preserves_source_zero
  [Nonempty V]
  (g : fin_simple_graph V) (source target : V) :
  ∀ (dist : V → ENat) (queue : BinaryHeap V), dist source = 0 → (dijkstra_rec g source target dist queue) source = 0 := by
  intro dist queue h
  generalize hsize : BinaryHeap.sizeOf queue = n
  revert queue dist hsize
  induction' n using Nat.strong_induction_on with n ih
  expose_names
  intro dist queue hdist qsize
  by_cases hq : queue.isEmpty
  · simp [dijkstra_rec, hq, hdist]
  · have hne : queue.isEmpty = false := by exact eq_false_of_ne_true hq
    unfold dijkstra_rec
    simp [hq]
    have qempty :  ¬queue.isEmpty = true  := by exact hq
    let extract_result := queue.extract_min dist qempty
    let u := extract_result.1
    let queue' := extract_result.2
    set h1 := relax_neighbors g u dist queue'
    have h1' : h1 = relax_neighbors g u dist queue' := by rfl
    let dist' := Prod.fst h1
    let queue'' := Prod.snd h1
    have dist'_src_zero : dist' source = 0 :=
      relax_neighbors_preserves_source_zero g source u dist queue' hdist h1 h1'
    have hq'_eq : queue' = (queue.extract_min dist qempty).2 := rfl
    have hq'_lt : BinaryHeap.sizeOf queue' < BinaryHeap.sizeOf queue := by
      rw [hq'_eq]
      exact BinaryHeap.sizeOf_extract_min_lt_of_isEmpty_eq_false queue hne dist
    have hq''le : BinaryHeap.sizeOf queue'' ≤ BinaryHeap.sizeOf queue' :=
      sizeOf_relax_neighbors_le g u dist queue'
    have hq''lt : BinaryHeap.sizeOf queue'' < BinaryHeap.sizeOf queue := by
      exact lt_of_le_of_lt hq''le hq'_lt
    have hq''lt' : BinaryHeap.sizeOf queue'' < n := by exact Nat.lt_of_lt_of_eq hq''lt qsize-- Nat.lt_of_lt_of_eq hq'_lt qsize
    have := ih
      (BinaryHeap.sizeOf queue'')
      hq''lt'
      dist'
      queue''
      dist'_src_zero
      rfl
    exact this

lemma dijkstra_source_zero
  [Nonempty V]
  (g : fin_simple_graph V) (s t : V) : (dijkstra g s t) s = 0 := by
  dsimp [dijkstra]
  let dist0 : V → ENat := fun v => if v = s then 0 else ⊤
  let queue := Finset.univ.val.toList.foldl (fun acc v => acc.add v dist0) BinaryHeap.empty
  have : dist0 s = 0 := by simp [dist0]
  exact dijkstra_rec_preserves_source_zero g s t dist0 queue this

lemma extract_min_still_correct_1 [Nonempty V] (g : fin_simple_graph V) (s : V) (v : V) (y : V) (x : (V → ℕ∞) × BinaryHeap V) (min : V)
(hempty : ¬x.2.isEmpty = true)
(min_variant : min_y_invariant y x hempty)
(step : V × BinaryHeap V := x.2.extract_min x.1 hempty)
(y2 : V := step.1)
(q' : BinaryHeap V := step.2)
(next : (V → ℕ∞) × BinaryHeap V := relax_neighbors g y2 x.1 q')
(hempty2 : ¬next.2.isEmpty = true)
: (next.2.extract_min next.1 hempty2).1 = min → next.1 y ≤ next.1 min := by sorry

lemma extract_min_still_correct_2 [Nonempty V] (g : fin_simple_graph V) (s : V) (v : V) (y : V) (x : (V → ℕ∞) × BinaryHeap V) (min : V)
(hempty : ¬x.2.isEmpty = true)
(hextract : (x.2.extract_min x.1 hempty).1 = y)
(q' : BinaryHeap V := (x.2.extract_min x.1 hempty).2)
(next : (V → ℕ∞) × BinaryHeap V := relax_neighbors g y x.1 q')
(hempty2 : ¬next.2.isEmpty = true)
: (next.2.extract_min next.1 hempty2).1 = min → next.1 y ≤ next.1 min := by sorry

theorem dijkstra_correctness
  [Nonempty V]
  (g : fin_simple_graph V) (s : V)
  (is_connected: SimpleGraph.Connected g.toSimpleGraph):
  ∀ v : V, (dijkstra g s v) v = delta g s v := by
  intro v
  set dist := (dijkstra g s v) with hdist
  have h_lower : ∀ u, (delta g s u : ENat) ≤ dist u :=
    never_underestimates g s v
  by_contra hneq_v
  have hexists : ∃ u, dist u ≠ delta g s u := ⟨v, by simpa [hdist] using hneq_v⟩
  obtain ⟨u, hu_ne, h_min⟩ := minimal_counterexample g s dist hexists
  have u_ne_s : u ≠ s := by
    intro h
    have h2: s = u := by exact ((fun a ↦ a) ∘ fun a ↦ a) (id (Eq.symm h))
    subst h2
    have hsrc : dist s = 0 := by exact dijkstra_source_zero g s v
    have hdelta0 : delta g s s = 0 := by
      unfold delta
      exact SimpleGraph.dist_self
    have heq : dist s = delta g s s := by simp [hsrc, hdelta0]
    exact hu_ne heq
  have hpos : 0 < delta g s u := by
    exact positive_distance_of_counterexample g s u u_ne_s is_connected
  obtain ⟨y, hyu_adj, hδ⟩ := exists_pred_on_shortest_path g s u hpos is_connected
  have hy_lt_u : delta g s y < delta g s u := by simp [hδ]
  have hy_eq : dist y = delta g s y := by
    exact (h_min y hy_lt_u)
  have h_relax : dist u ≤ dist y + 1 :=
    relax_adj_final_bound g s v hyu_adj
    (fun x hempty => by
      intro min_variant hne step y2 q' next
      have step' : min_y_invariant y x hne := by simpa using min_variant
      unfold min_y_invariant
      intro hempty2 min
      exact extract_min_still_correct_1 g s v y x min hempty min_variant step y2 q' next hempty2
    )
    (fun x_left x_right hempty hextract => by
      intro q' next hempty2 min
      exact extract_min_still_correct_2 g s v y (x_left, x_right) min hempty hextract q' next hempty2
    )
  have h_upper : dist u ≤ (delta g s u : ENat) := by
    simpa [hy_eq, hδ] using h_relax
  have h_lower_u : (delta g s u : ENat) ≤ dist u := h_lower u
  have : dist u = delta g s u := le_antisymm h_upper h_lower_u
  exact hu_ne this
