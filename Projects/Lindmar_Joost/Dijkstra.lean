import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk
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

theorem dijkstra_correctness
  [Nonempty V]
  (g : FinSimpleGraph V) (s : V) :
  ∀ v : V, dijkstra g s v = delta g s v := by
  intro v
  -- Proof sketch: By induction on the number of extract-min operations.
  -- Use the invariant that dist[u] is finalized when u is extracted,
  -- and every relaxation preserves upper bounds and eventually reaches the true distance.
  -- This relies on the correctness of the BinaryHeap operations and termination of `dijkstra_rec`.
  sorry
