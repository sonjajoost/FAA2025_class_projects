import Mathlib.Tactic
#check Nat.div2Induction
#check ENat
inductive BinaryTree (α : Type)
  | leaf : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α

namespace BinaryTree

def isMinHeap : BinaryTree ENat → Prop
| leaf => true
| node l v r => match l, r with
      | leaf, leaf => true
      | node _ lv _, leaf => v <= lv ∧ isMinHeap l
      | leaf, node _ rv _ => v <= rv ∧ isMinHeap r
      | node _ lv _, node _ rv _ => v <= lv ∧ isMinHeap l ∧ v <= rv ∧ isMinHeap r

def heapify (bt: BinaryTree ENat): BinaryTree ENat := match bt with
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

def extractMin: BinaryTree ENat → Option ENat
| leaf => none
| node _ v _ => some v

def minHeap:  BinaryTree ENat → ENat
| leaf => ⊤
| node l v r => match l, r with
    | leaf, leaf => v
    | leaf, node _ rv _ => if v <= rv then v else rv
    | node _ lv _, leaf => if v <= lv then v else lv
    | node _ lv _, node _ rv _ =>  if lv <= rv then
                                     if v <= lv then v
                                     else lv
                                    else
                                      if v <= rv then v
                                      else rv
-- def min:  BinaryTree ENat → ENat
-- | leaf => ⊤
-- | node l v r => if l
--     | leaf, leaf => v
--     | leaf, node _ rv _ => if v <= rv then v else rv
--     | node _ lv _, leaf => if v <= lv then v else lv
--     | node _ lv _, node _ rv _ =>  if lv <= rv then
--                                      if v <= lv then v
--                                      else lv
--                                     else
--                                       if v <= rv then v
--                                       else rv

lemma extractMinCorrect (bt: BinaryTree ENat): isMinHeap bt → extractMin bt = minHeap bt := by sorry

def leftAndRightAreMinHeap: (BinaryTree ENat) →  Prop
| leaf => true
| node l _ r => isMinHeap l ∧ isMinHeap r

def rootIsMinOfChildren: (BinaryTree ENat) →  Prop
| leaf => true
| node l v r => match l, r with
    | leaf, leaf => true
    | leaf, node _ rv _ => v <= rv
    | node _ lv _, leaf => v <= lv
    | node _ lv _, node _ rv _ =>  v <= lv ∧ v <= rv


lemma minHeapThenLeftAndRightAreMinHeap (bt: BinaryTree ENat): isMinHeap bt → leftAndRightAreMinHeap bt := by
intro hbt
fun_induction isMinHeap; all_goals (grind [leftAndRightAreMinHeap, isMinHeap])

lemma minHeapThenRootIsMinOfChildren (bt: BinaryTree ENat): isMinHeap bt → rootIsMinOfChildren bt := by
intro hbt
fun_induction isMinHeap; all_goals (grind [rootIsMinOfChildren])


lemma leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap (bt: BinaryTree ENat): leftAndRightAreMinHeap bt ∧ rootIsMinOfChildren bt → isMinHeap bt := by
intro hbt
fun_induction isMinHeap; all_goals (simp [rootIsMinOfChildren, leftAndRightAreMinHeap] at hbt;simp[hbt])

lemma leftAndRightAreMinHeapLeft (l: BinaryTree ENat) (r: BinaryTree ENat) (v: ENat): leftAndRightAreMinHeap (node l v r) → leftAndRightAreMinHeap l := by
intro hbt
simp [leftAndRightAreMinHeap] at hbt
simp [minHeapThenLeftAndRightAreMinHeap, hbt]


lemma leftAndRightAreMinHeapRight (l: BinaryTree ENat) (r: BinaryTree ENat) (v: ENat): leftAndRightAreMinHeap (node l v r)  → leftAndRightAreMinHeap r := by
intro hbt
simp [leftAndRightAreMinHeap] at hbt
simp [minHeapThenLeftAndRightAreMinHeap, hbt]

lemma heapifyPreservesStructure (bt: BinaryTree ENat): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt = node l' v' r' := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals simp



lemma heapifyPreservesStructureAndRootMin (bt: BinaryTree ENat): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt = node l' v' r' ∧ v' ≤ (minHeap bt) := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals grind [minHeap]

def contains: (BinaryTree ENat) → ENat → Prop
| leaf, _ => false
| node l v r, v' => v=v' ∨ contains l v' ∨ contains r v'


--lemma heapifyPreserversMinHeapChildren (bt: BinaryTree ℕ) (hbt: leftAndRightAreMinHeap bt):leftAndRightAreMinHeap (heapify bt) := by
--all_goals sorry


lemma heapifyPreservesMembers (bt: BinaryTree ENat) (v: ENat): contains bt v → contains (heapify bt) v := by
intro hbt
fun_induction heapify generalizing v; all_goals try grind[contains]

lemma containsIsNode (bt: BinaryTree ENat) (v: ENat): contains bt v → ∃ l v' r, bt = node l v' r := by
fun_induction contains; all_goals simp

lemma minHeapRootMin (bt l r: BinaryTree ENat) (v: ENat): bt = (node l v r) → isMinHeap bt → v = minHeap bt := by
intro hbt hmin
fun_induction isMinHeap; all_goals grind [minHeap]


lemma minHeapMemberLeRoot (bt: BinaryTree ENat) (v: ENat):  isMinHeap bt →  contains bt v → v ≤ minHeap bt := by
intro hmin hl
fun_induction contains
. contradiction
. expose_names
  cases hl
  . sorry
  sorry
  -- cases hc; all_goals expose_names
  -- . obtain ⟨v'', l', r', h⟩ := h
  --   have: v_1 ≤ v := by grind
  --   grind
  -- . cases h; all_goals expose_names
  --   . apply ih2
  --     . apply minHeapThenLeftAndRightAreMinHeap at hmin
  --       simp [leftAndRightAreMinHeap] at hmin
  --       simp [hmin]
  --     . sorry


--     . cases l
--       . contradiction
--       . expose_names
--         have: l = a.node a_1 a_2


-- lemma heapifyEstablishesRootIsMinOfChildren (bt: BinaryTree ENat) (hbt: leftAndRightAreMinHeap bt): rootIsMinOfChildren (heapify bt) := by
-- fun_induction heapify; all_goals expose_names; all_goals try grind[rootIsMinOfChildren, leftAndRightAreMinHeap]
-- .
--  have hr: (rl.node rv rr).leftAndRightAreMinHeap := by
--     grind [leftAndRightAreMinHeapRight]
--   simp [leftAndRightAreMinHeap] at hr
--   simp [leftAndRightAreMinHeap] at ih1
--   obtain ⟨hr1, hr2⟩ := hr
--   apply ih1 at hr1
--   apply hr1 at hr2
--   have: ∃ l' v' r', heapify (node rl v rr) = node l' v' r' := by
--     simp [heapifyPreservesStructure (node rl v rr)]
--   obtain ⟨rl', v', rr', hrw⟩ := this
--   rw [hrw]
--   simp[rootIsMinOfChildren]
--   grw[h]
--   rw [hrw] at hr2
--   have: contains (node rl' v' rr') v := by
--     rw [←hrw]
--     apply heapifyPreservesMembers
--     simp [contains]



--   sorry
-- all_goals sorry

-- lemma heapifyEstablishesLeftAndRigthAreMinHeap (bt: BinaryTree ENat) (hbt: leftAndRightAreMinHeap bt): leftAndRightAreMinHeap (heapify bt) := by
-- fun_induction heapify; all_goals expose_names
-- . simp [leftAndRightAreMinHeap]
-- . simp [leftAndRightAreMinHeap, isMinHeap]
-- . simp [leftAndRightAreMinHeap, isMinHeap]
--   simp [leftAndRightAreMinHeap] at hbt
--   have hbtr: (rl.node rv rr).leftAndRightAreMinHeap := by grind [←minHeapThenLeftAndRightAreMinHeap]
--   apply ih1 at hbtr
--   sorry
-- all_goals sorry

--lemma leftAndRightAreMinHeapAndRootIsMinImpliesIsHeap ()

lemma heapifyPreservesMinHeap (bt: BinaryTree ENat): isMinHeap bt → bt = heapify bt := by
fun_induction heapify; all_goals expose_names; all_goals try grind
. intro hbt
  by_contra
  have hbtmin: v = minHeap (leaf.node v (rl.node rv rr)) := by grind [minHeapRootMin]
  grind[minHeap]
. intro hbt
  by_contra
  have hbtmin: v = minHeap ((ll.node lv lr).node v leaf) := by grind [minHeapRootMin]
  grind[minHeap]
. intro hbt
  have hbtmin: v = minHeap ((ll.node lv lr).node v (rl.node rv rr)) := by grind [minHeapRootMin]
  grind[minHeap]
. intro hbt
  have hbtmin: v = minHeap ((ll.node lv lr).node v (rl.node rv rr)) := by grind [minHeapRootMin]
  grind[minHeap]

lemma binTreeEq (l r l' r': BinaryTree ENat) (v v': ENat): (node l v r) = (node l' v' r') → r = r' := by
grind only

lemma decreaseRootIsHeap (l r: BinaryTree ENat) (v v': ENat): isMinHeap (node l v r) →  v' ≤ minHeap (node l v r) → isMinHeap (node l v' r) := by sorry

lemma heapifyEstablishesMinHeap' (bt l r: BinaryTree ENat) (v: ENat): bt = node l v r ∧  isMinHeap l ∧ isMinHeap r → isMinHeap (heapify bt) := by
fun_induction heapify generalizing l r v; all_goals expose_names
. simp [isMinHeap]
. simp [isMinHeap]
. intro ⟨hr, hminl, hminr⟩
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  have: ∃ rl' v' rr', (rl.node v_1 rr).heapify = node rl' v' rr' ∧ v' ≤ minHeap (rl.node v_1 rr) := by
        apply heapifyPreservesStructureAndRootMin
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hrnode: r = (rl.node rv rr) := by
        apply binTreeEq at hr
        simp [hr]
  constructor
  . simp [leftAndRightAreMinHeap]
    constructor
    . simp [isMinHeap]
    . specialize ih1 rl rr v_1
      simp at ih1
      apply minHeapThenLeftAndRightAreMinHeap at hminr
      simp [leftAndRightAreMinHeap] at hminr
      simp [hrnode] at hminr
      apply ih1; all_goals grind
  . rw [hr1]
    simp [rootIsMinOfChildren]
    have hrvmin : rv = minHeap (rl.node rv rr) := by sorry
    have hcontains: contains (rl.node rv rr) v' ∨ v'= v_1 := by sorry
    cases hcontains
    . expose_names
      apply minHeapMemberLeRoot r v' at hminr
      rw [← hrnode] at h_1
      apply hminr at h_1
      sorry
    . expose_names
      rw [h_1]
      grw [h]



. grind [isMinHeap]
. sorry
. grind [isMinHeap]
. grind [isMinHeap]
. sorry
. grind [isMinHeap]
. sorry


  -- have: ∃ rl' v' rr', (rl.node v_1 rr).heapify = node rl' v' rr' ∧ v' ≤ min (rl.node v_1 rr) := by
  --     apply heapifyPreservesStructureAndRootMin
  --     simp
  -- obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  -- rw [hr1]
  -- apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  -- constructor
  -- . simp [leftAndRightAreMinHeap]
  --   constructor
  --   . simp [isMinHeap]
  --   . rw [← hr1]
  --     apply ih1
  --     simp [hr]
  --     have: r = (rl.node rv rr) := by
  --       apply binTreeEq at hr
  --       simp [hr]

  --     apply decreaseRootIsHeap rl' rr' v_1


--   .

lemma heapifyEstablishesMinHeap (bt: BinaryTree ENat): (hbt: leftAndRightAreMinHeap bt) → isMinHeap (heapify bt) := by
fun_induction heapify; all_goals expose_names; all_goals try grind [isMinHeap]
. intro hbt
  simp [leftAndRightAreMinHeap] at hbt
  obtain ⟨hb1, hb2⟩ := hbt
  apply minHeapThenLeftAndRightAreMinHeap at hb2
  apply ih1 at hb2
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  constructor
  . simp [leftAndRightAreMinHeap]
    constructor
    . simp [isMinHeap]
    . exact hb2
  .
    have: ∃ rl' v' rr', (rl.node v rr).heapify = node rl' v' rr' ∧ v' ≤ minHeap (rl.node v rr) := by
      apply heapifyPreservesStructureAndRootMin
      simp
    obtain ⟨rl', v', rr', hr1, hr2⟩ := this
    rw [hr1]

    have: rv <= v' := by sorry

    simp[rootIsMinOfChildren]
    exact this
