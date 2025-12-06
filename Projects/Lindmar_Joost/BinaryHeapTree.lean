import Mathlib.Tactic



inductive BinaryTree (α : Type)
  | leaf : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α

namespace BinaryTree

def isMinHeap : BinaryTree ℕ → Bool
| leaf => true
| node l v r => match l, r with
      | leaf, leaf => true
      | node _ lv _, leaf => v <= lv ∧ isMinHeap l
      | leaf, node _ rv _ => v <= rv ∧ isMinHeap r
      | node _ lv _, node _ rv _ => v <= lv ∧ isMinHeap l ∧ v <= rv ∧ isMinHeap r

def heapify (bt: BinaryTree ℕ): BinaryTree ℕ := match bt with
| leaf => bt
| node l v r => match l, r with
    | leaf, leaf => bt
    | leaf, node rl rv rr => if rv < v then node l rv (heapify (node rl v rr)) else bt
    | node ll lv lr, leaf => if lv < v then node (heapify (node ll v lr)) lv r else bt
    | node ll lv lr, node rl rv rr =>  if lv <= rv then
                                          if v <= lv then bt
                                          else node (heapify (node ll v lr)) lv r
                                        else
                                          if v <= rv then bt
                                          else node l rv (heapify (node rl v rr))

def leftAndRightAreMinHeap: (BinaryTree ℕ) →  Bool
| leaf => true
| node l _ r => isMinHeap l ∧ isMinHeap r

def rootIsMinOfChildren: (BinaryTree ℕ) →  Bool
| leaf => true
| node l v r => match l, r with
    | leaf, leaf => true
    | leaf, node _ rv _ => v <= rv
    | node _ lv _, leaf => v <= lv
    | node _ lv _, node _ rv _ =>  v <= lv && v <= rv


lemma minHeapThenLeftAndRightAreMinHeap (bt: BinaryTree ℕ): isMinHeap bt = true → leftAndRightAreMinHeap bt = true := by
intro hbt
fun_induction isMinHeap
. simp [leftAndRightAreMinHeap]
. simp [leftAndRightAreMinHeap, isMinHeap]
. expose_names
  simp at hbt
  simp [leftAndRightAreMinHeap, hbt]
  simp [isMinHeap]
. expose_names
  simp at hbt
  simp [leftAndRightAreMinHeap, hbt]
  simp [isMinHeap]
. expose_names
  simp at hbt
  simp [leftAndRightAreMinHeap, hbt]

lemma leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap (bt: BinaryTree ℕ): leftAndRightAreMinHeap bt ∧ rootIsMinOfChildren bt → isMinHeap bt := by
intro hbt
fun_induction isMinHeap
. simp
. simp
. simp [rootIsMinOfChildren, leftAndRightAreMinHeap] at hbt
  simp [hbt]
. simp [rootIsMinOfChildren, leftAndRightAreMinHeap] at hbt
  simp [hbt]
. simp [rootIsMinOfChildren, leftAndRightAreMinHeap] at hbt
  simp [hbt]

lemma leftAndRightAreMinHeapLeft (l: BinaryTree ℕ) (r: BinaryTree ℕ) (v: ℕ): leftAndRightAreMinHeap (node l v r) → leftAndRightAreMinHeap l := by
intro hbt
simp [leftAndRightAreMinHeap] at hbt
simp [minHeapThenLeftAndRightAreMinHeap, hbt]


lemma leftAndRightAreMinHeapRight (l: BinaryTree ℕ) (r: BinaryTree ℕ) (v: ℕ): leftAndRightAreMinHeap (node l v r) = true → leftAndRightAreMinHeap r =true := by
intro hbt
simp [leftAndRightAreMinHeap] at hbt
simp [minHeapThenLeftAndRightAreMinHeap, hbt]

lemma heapifyPreservesStructure (bt: BinaryTree ℕ): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt = node l' v' r' := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals simp

lemma heapifyPreserversMinHeapChildren (bt: BinaryTree ℕ) (hbt: leftAndRightAreMinHeap bt):leftAndRightAreMinHeap (heapify bt) := by
all_goals sorry



lemma heapifyEstablishesRootIsMinOfChildren (bt: BinaryTree ℕ) (hbt: leftAndRightAreMinHeap bt): rootIsMinOfChildren (heapify bt) := by
fun_induction heapify; all_goals expose_names
. simp [rootIsMinOfChildren]
. simp [rootIsMinOfChildren]
. have hr: (rl.node rv rr).leftAndRightAreMinHeap := by
    grind [leftAndRightAreMinHeapRight]
  simp [leftAndRightAreMinHeap] at hr
  simp [leftAndRightAreMinHeap] at ih1
  obtain ⟨hr1, hr2⟩ := hr
  apply ih1 at hr1
  apply hr1 at hr2
  have: ∃ l' v' r', heapify (node rl v rr) = node l' v' r' := by
    simp [heapifyPreservesStructure (node rl v rr)]
  obtain ⟨rl', v', rr', hrw⟩ := this
  rw [hrw]
  simp[rootIsMinOfChildren]
  grw[h]
  rw [hrw] at hr2

  sorry
all_goals sorry

lemma heapifyEstablishesLeftAndRigthAreMinHeap (bt: BinaryTree ℕ) (hbt: leftAndRightAreMinHeap bt): leftAndRightAreMinHeap (heapify bt) := by
fun_induction heapify; all_goals expose_names
. simp [leftAndRightAreMinHeap]
. simp [leftAndRightAreMinHeap, isMinHeap]
. simp [leftAndRightAreMinHeap, isMinHeap]
  simp [leftAndRightAreMinHeap] at hbt
  have hbtr: (rl.node rv rr).leftAndRightAreMinHeap := by grind [←minHeapThenLeftAndRightAreMinHeap]
  apply ih1 at hbtr
  sorry
all_goals sorry


lemma heapifyEstablishesMinHeap (bt: BinaryTree ℕ) (hbt: leftAndRigthAreMinHeap bt): isMinHeap (heapify bt) := by
fun_induction heapify; all_goals expose_names
. simp [isMinHeap]
. simp [isMinHeap]
all_goals sorry
