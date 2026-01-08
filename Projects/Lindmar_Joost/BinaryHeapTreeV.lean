import Mathlib.Tactic
#check Nat.div2Induction
#check ENat

set_option autoImplicit true

inductive BinaryTree (α : Type u)
  | leaf : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α


namespace BinaryTree
def insert (bt: BinaryTree α) (v: α) (f: α → ENat): BinaryTree α := sorry

@[grind] def isMinHeap : BinaryTree α → (dist : α → ENat) → Prop
| leaf, _ => true
| node l v r, f => match l, r with
      | leaf, leaf => true
      | node _ lv _, leaf => f v <= f lv ∧ isMinHeap l f
      | leaf, node _ rv _ => f v <= f rv ∧ isMinHeap r f
      | node _ lv _, node _ rv _ => f v <= f lv ∧ isMinHeap l f ∧ f v <= f rv ∧ isMinHeap r f

@[grind] def heapify (bt: BinaryTree α) (f: α → ENat): BinaryTree α := match bt with
| leaf => bt
| node l v r => match l, r with
    | leaf, leaf => bt
    | leaf, node rl rv rr => if f rv < f v then node l rv (heapify (node rl v rr) f) else bt
    | node ll lv lr, leaf => if f lv < f v then node (heapify (node ll v lr) f) lv r else bt
    | node ll lv lr, node rl rv rr =>  if f lv <= f rv then
                                          if f v <= f lv then bt
                                          else node (heapify (node ll v lr) f) lv r
                                        else
                                          if f v <= f rv then bt
                                          else node l rv (heapify (node rl v rr) f)

@[grind] def getLast: BinaryTree α → Option α ×  BinaryTree α
| leaf => (none, leaf)
| node l v r => match l, r with
    | leaf, leaf => (some v, leaf)
    | leaf, _ => let (val, tree) := (getLast r)
      (val, node l v tree)
    | _, _ => let (val, tree) := (getLast l)
      (val, node tree v r)

@[grind] def extractMin (bt: BinaryTree α) (f: α → ENat): (Option α × BinaryTree α):=
let (lastNode, treeWithoutLast) := getLast bt
match lastNode with
| none => (none, leaf)
| some v' => match treeWithoutLast with
  | leaf => (some v', leaf)
  | node l v r => (some v, heapify (node l v' r) f)

@[grind] def heapMin:  BinaryTree α → (α → ENat) → ENat
| leaf, _ => ⊤
| node l v r, f => match l, r with
    | leaf, leaf => (f v)
    | leaf, node _ rv _ => if f v <= f rv then f v else f rv
    | node _ lv _, leaf => if f v <= f lv then f v else f lv
    | node _ lv _, node _ rv _ =>  if f lv <= f rv then
                                     if f v <= f lv then f v
                                     else f lv
                                    else
                                      if f v <= f rv then f v
                                      else f rv

@[grind] def rootIsMinOfChildren: (BinaryTree α) → (α → ENat) →  Prop
| leaf, _ => true
| node l v r, f => match l, r with
    | leaf, leaf => true
    | leaf, node _ rv _ => f v <= f rv
    | node _ lv _, leaf => f v <= f lv
    | node _ lv _, node _ rv _ =>  f v <= f lv ∧ f v <= f rv


@[grind] def leftAndRightAreMinHeap: (BinaryTree α) →  (f: α → ENat) →  Prop
| leaf, _ => true
| node l _ r, f => isMinHeap l f ∧ isMinHeap r f

@[grind] def contains : (BinaryTree α) → α → Prop
| leaf, _ => false
| node l v r, v' => v = v' ∨ contains l v' ∨ contains r v'


@[grind] def containsB [DecidableEq α] : (BinaryTree α) → α → Bool
| leaf, _ => false
| node l v r, v' => (v = v') ∨ containsB l v' ∨ containsB r v'

lemma minHeapThenLeftAndRightAreMinHeap (bt: BinaryTree α) (f: α → ENat): isMinHeap bt f → leftAndRightAreMinHeap bt f := by
intro hbt
fun_induction isMinHeap; all_goals (grind [leftAndRightAreMinHeap, isMinHeap])

lemma minHeapThenRootIsMinOfChildren (bt: BinaryTree α) (f: α → ENat): isMinHeap bt f → rootIsMinOfChildren bt f := by
intro hbt
fun_induction isMinHeap; all_goals (grind [rootIsMinOfChildren])


lemma leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap (bt: BinaryTree α) (f: α → ENat): leftAndRightAreMinHeap bt f ∧ rootIsMinOfChildren bt f → isMinHeap bt f := by
intro hbt
fun_induction isMinHeap; all_goals (simp [rootIsMinOfChildren, leftAndRightAreMinHeap] at hbt;simp[hbt])

lemma leftAndRightAreMinHeapLeft (l: BinaryTree α) (r: BinaryTree α) (v: α) (f: α → ENat): leftAndRightAreMinHeap (node l v r) f → leftAndRightAreMinHeap l f := by
intro hbt
simp [leftAndRightAreMinHeap] at hbt
simp [minHeapThenLeftAndRightAreMinHeap, hbt]


lemma leftAndRightAreMinHeapRight (l: BinaryTree α) (r: BinaryTree α) (v: α) (f: α → ENat): leftAndRightAreMinHeap (node l v r) f → leftAndRightAreMinHeap r f := by
intro hbt
simp [leftAndRightAreMinHeap] at hbt
simp [minHeapThenLeftAndRightAreMinHeap, hbt]

lemma heapifyPreservesStructure (bt: BinaryTree α) (f: α → ENat): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt f = node l' v' r' := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals simp

lemma heapifyPreservesStructureAndRootMin (bt: BinaryTree α) (f: α → ENat): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt f = node l' v' r' ∧ f v' ≤ (heapMin bt f) := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals grind [heapMin]

lemma heapifyPreservesMembers (bt: BinaryTree α) (v: α) (f: α → ENat): contains bt v → contains (heapify bt f) v := by
intro hbt
fun_induction heapify generalizing v; all_goals try grind[contains]

lemma heapifyPreservesMembers2 (bt: BinaryTree α) (v: α) (f: α → ENat):  contains (heapify bt f) v → contains bt v := by
intro hbt
fun_induction heapify generalizing v; all_goals try grind[contains]

lemma containsIsNode (bt: BinaryTree α) (v: α): contains bt v → ∃ l v' r, bt = node l v' r := by
fun_induction contains; all_goals simp

lemma minHeapRootMin (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = (node l v r) → isMinHeap bt f → f v = heapMin bt f := by
intro hbt hmin
fun_induction isMinHeap; all_goals grind [heapMin]

lemma rootIsMinOfChildrenLeft (l r ll lr: BinaryTree α) (v lv: α) (f: α → ENat): rootIsMinOfChildren (node l v r) f →  l = (node ll lv lr) →  f v ≤ f lv := by
  intros; expose_names
  rw [h_1] at h
  cases r; all_goals grind[rootIsMinOfChildren]

lemma rootIsMinOfChildrenRight (l r rl rr: BinaryTree α) (v rv: α) (f: α → ENat): rootIsMinOfChildren (node l v r) f →  r = (node rl rv rr) → f v ≤ f rv := by
  intros; expose_names
  rw [h_1] at h
  cases r; all_goals try grind[rootIsMinOfChildren]
  . grind [rootIsMinOfChildren.eq_def]

lemma minHeapMemberLeRoot (bt: BinaryTree α) (v: α) (f: α → ENat): isMinHeap bt f →  contains bt v →  heapMin bt f ≤ f v := by
intro hmin hl
fun_induction contains
. contradiction
. expose_names
  cases hl; all_goals expose_names
  . expose_names
    rw [←h]
    suffices f v = (l.node v r).heapMin f by grind
    apply minHeapRootMin (l.node v r) l r v; all_goals grind
  . cases h; all_goals expose_names
    . have h2: l.contains v' := by exact h
      apply containsIsNode at h2
      obtain ⟨l'', v'', r'', h2 ⟩:= h2
      have h3: l = l''.node v'' r'' := by exact h2
      have hmin2: (l.node v r).isMinHeap f := by assumption
      have hmin3: (l.node v r).isMinHeap f := by assumption
      apply minHeapThenLeftAndRightAreMinHeap at hmin
      simp [leftAndRightAreMinHeap] at hmin
      have hlmin: l.isMinHeap f:= by grind
      have hlmin2: l.isMinHeap f:= by grind
      apply ih2 at hlmin
      apply hlmin at h
      grw[← h]
      apply minHeapThenRootIsMinOfChildren at hmin2
      apply rootIsMinOfChildrenLeft l r l'' r'' v v'' f hmin2 at h2
      have hhl: f v'' = l.heapMin f:= by grind [minHeapRootMin]
      have hh: f v = (l.node v r).heapMin f:= by grind [minHeapRootMin]
      grw [← hh, ← hhl]
      exact h2
    . have h2: r.contains v' := by exact h
      apply containsIsNode at h2
      obtain ⟨l'', v'', r'', h2 ⟩:= h2
      have h3: r = l''.node v'' r'' := by exact h2
      have hmin2: (l.node v r).isMinHeap f:= by assumption
      have hmin3: (l.node v r).isMinHeap f:= by assumption
      apply minHeapThenLeftAndRightAreMinHeap at hmin
      simp [leftAndRightAreMinHeap] at hmin
      have hlmin: r.isMinHeap f:= by grind
      have hlmin2: r.isMinHeap f:= by grind
      apply ih1 at hlmin
      apply hlmin at h
      grw[← h]
      apply minHeapThenRootIsMinOfChildren at hmin2
      apply rootIsMinOfChildrenRight l r l'' r'' v v'' f hmin2 at h2
      have hhl: f v'' = r.heapMin f:= by grind [minHeapRootMin]
      have hh: f v = (l.node v r).heapMin f:= by grind [minHeapRootMin]
      grw [← hh, ← hhl]
      exact h2

lemma heapifyPreservesMinHeap (bt: BinaryTree α) (f: α → ENat): isMinHeap bt f → bt = heapify bt f:= by
fun_induction heapify; all_goals expose_names; all_goals try grind

lemma binTreeEqR (l r l' r': BinaryTree α) (v v': α): (node l v r) = (node l' v' r') → r = r' := by
grind only

lemma binTreeEqL (l r l' r': BinaryTree α) (v v': α): (node l v r) = (node l' v' r') → l = l' := by
grind only

lemma heapifyPreservesValues (tree r l: BinaryTree α) (v: α) (f: α → ENat): tree.heapify f = node r v l → contains tree v := by
grind [contains, heapifyPreservesMembers2]

lemma containsRootOrChildren (tree r l: BinaryTree α) (v v': α) : tree = node r v l → contains tree v' → contains r v' ∨ contains l v' ∨ v= v' := by
grind [contains]

lemma containsRootOrChildrenLeftLeaf (tree r: BinaryTree α) (v v':  α): tree = node r v leaf → contains tree v' → contains r v' ∨ v= v' := by
grind [contains]

lemma containsRightThenContainsRoot (tree l r: BinaryTree α) (v v':  α): tree = node l v r → contains r v' → contains tree v' := by
grind [contains]

lemma containsLeftThenContainsRoot (tree l r: BinaryTree α) (v v':  α): tree = node l v r → contains l v' → contains tree v' := by
grind [contains]

lemma heapifyEstablishesMinHeap' {α} (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = node l v r ∧  isMinHeap l f ∧ isMinHeap r f → isMinHeap (heapify bt f) f := by
fun_induction heapify generalizing l r v; all_goals expose_names
. simp [isMinHeap]
. simp [isMinHeap]
. intro ⟨hr, hminl, hminr⟩
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  have: ∃ rl' v' rr', (rl.node v_1 rr).heapify f = node rl' v' rr' ∧ f v' ≤ heapMin (rl.node v_1 rr) f:= by
        apply heapifyPreservesStructureAndRootMin
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hrnode: r = (rl.node rv rr) := by
        apply binTreeEqR at hr
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
    have hrvmin : f rv = heapMin (rl.node rv rr) f:= by
      apply minHeapRootMin (rl.node rv rr) rl rr rv f (rfl)
      rw[← hrnode]; exact hminr
    have hcontains: contains (node rl v_1 rr) v' := by
      apply heapifyPreservesMembers2
      rw[hr1]
      simp[contains]
    have hcontains: contains (rl.node rv rr) v' ∨ v'= v_1 := by grind[contains]
    cases hcontains
    . expose_names
      apply minHeapMemberLeRoot r v' at hminr
      rw [← hrnode] at h_1
      apply hminr at h_1
      grw[← h_1]
      rw[hrvmin]
      rw[hrnode]
    . expose_names
      rw [h_1]
      grw [h]
. grind [isMinHeap]
. intro ⟨hl, hminl, hminr⟩
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  have: ∃ ll' v' lr', (ll.node v_1 lr).heapify f = node ll' v' lr' ∧ f v' ≤ heapMin (ll.node v_1 lr) f:= by
        apply heapifyPreservesStructureAndRootMin
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hlnode: l = (ll.node lv lr) := by
        apply binTreeEqL at hl
        simp [hl]
  constructor
  . simp [leftAndRightAreMinHeap]
    constructor
    . specialize ih1 ll lr v_1
      simp at ih1
      apply minHeapThenLeftAndRightAreMinHeap at hminl
      simp [leftAndRightAreMinHeap] at hminl
      simp [hlnode] at hminl
      apply ih1; all_goals grind
    . simp [isMinHeap]
  . rw [hr1]
    simp [rootIsMinOfChildren]
    have hlvmin : f lv = heapMin (ll.node lv lr) f:= by
      apply minHeapRootMin (ll.node lv lr) ll lr lv f (rfl)
      rw[← hlnode]; exact hminl
    have hcontains: contains (node ll v_1 lr) v' := by
      apply heapifyPreservesMembers2
      rw[hr1]
      simp[contains]
    have hcontains: contains (ll.node lv lr) v' ∨ v'= v_1 := by grind[contains]
    cases hcontains
    . expose_names
      apply minHeapMemberLeRoot l v' at hminl
      rw [← hlnode] at h_1
      apply hminl at h_1
      grw[← h_1]
      rw[hlvmin]
      rw[hlnode]
    . expose_names
      rw [h_1]
      grw [h]
. grind [isMinHeap]
. grind [isMinHeap]
. intro ⟨hl, hminl, hminr⟩
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  have: ∃ ll' v' lr', (ll.node v_1 lr).heapify f = node ll' v' lr' ∧ f v' ≤ heapMin (ll.node v_1 lr) f:= by
        apply heapifyPreservesStructureAndRootMin
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hlnode: l = (ll.node lv lr) := by
        apply binTreeEqL at hl
        simp [hl]
  constructor
  . simp [leftAndRightAreMinHeap]
    constructor
    . specialize ih1 ll lr v_1
      simp at ih1
      apply minHeapThenLeftAndRightAreMinHeap at hminl
      simp [leftAndRightAreMinHeap] at hminl
      simp [hlnode] at hminl
      apply ih1; all_goals grind
    . grind
  . rw [hr1]
    simp [rootIsMinOfChildren]
    have hlvmin : f lv = heapMin (ll.node lv lr) f := by
      apply minHeapRootMin (ll.node lv lr) ll lr lv f (rfl)
      rw[← hlnode]; exact hminl
    have hcontains: contains (node ll v_1 lr) v' := by
      apply heapifyPreservesMembers2
      rw[hr1]
      simp[contains]
    have hcontains: contains (ll.node lv lr) v' ∨ v'= v_1 := by grind[contains]
    cases hcontains
    . expose_names
      apply minHeapMemberLeRoot l v' at hminl
      grind
    . expose_names
      grind
. grind [isMinHeap]
. intro ⟨hr, hminl, hminr⟩
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  have: ∃ rl' v' rr', (rl.node v_1 rr).heapify f = node rl' v' rr' ∧ f v' ≤ heapMin (rl.node v_1 rr) f:= by
        apply heapifyPreservesStructureAndRootMin
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hrnode: r = (rl.node rv rr) := by
        apply binTreeEqR at hr
        simp [hr]
  constructor
  . simp [leftAndRightAreMinHeap]
    constructor
    . grind
    . specialize ih1 rl rr v_1
      simp at ih1
      apply minHeapThenLeftAndRightAreMinHeap at hminr
      simp [leftAndRightAreMinHeap] at hminr
      simp [hrnode] at hminr
      apply ih1
      . grind
      . obtain ⟨h1, h2⟩ := hminr
        exact h2
  . rw [hr1]
    simp [rootIsMinOfChildren]
    have hrvmin : f rv = heapMin (rl.node rv rr) f := by
      apply minHeapRootMin (rl.node rv rr) rl rr rv f (rfl)
      rw[← hrnode]; exact hminr
    have hcontains: contains (node rl v_1 rr) v' := by
      apply heapifyPreservesMembers2
      rw[hr1]
      simp[contains]
    have hcontains: contains (rl.node rv rr) v' ∨ v'= v_1 := by
      apply containsRootOrChildren (node rl v_1 rr) rl rr v_1 v' (rfl) at hcontains
      cases hcontains; all_goals expose_names
      . left
        apply containsLeftThenContainsRoot (node rl rv rr) rl rr rv v' (rfl) (h_2)
      . cases h_2; all_goals expose_names
        . left
          apply containsRightThenContainsRoot (node rl rv rr) rl rr rv v' (rfl) (h_2)
        . right
          rw [h_2]
    constructor
    . simp at h
      grw [h]
    cases hcontains
    . expose_names
      apply minHeapMemberLeRoot r v' at hminr
      rw [← hrnode] at h_2
      apply hminr at h_2
      grw[← h_2]
      rw[hrvmin]
      rw[hrnode]
    . expose_names
      rw [h_2]
      simp at h_1
      grw [h_1]

lemma heapifyEstablishesMinHeap (bt: BinaryTree α) (f: α → ENat): (hbt: leftAndRightAreMinHeap bt f) → isMinHeap (heapify bt f) f := by
cases bt
. grind[isMinHeap,leftAndRightAreMinHeap, heapify]
. grind[isMinHeap,leftAndRightAreMinHeap, heapifyEstablishesMinHeap']

lemma getLastPreservesMinHeap (bt: BinaryTree α) (f: α → ENat): isMinHeap bt f → isMinHeap (getLast bt).snd f := by
intros; expose_names
fun_induction isMinHeap; all_goals expose_names
. grind
. grind
. rw [getLast]
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  constructor; all_goals try grind
  . cases a; all_goals (cases a_1; all_goals grind)
. rw [getLast]
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  constructor; all_goals try grind
  . cases a; all_goals (cases a_1; all_goals grind)
. rw [getLast]
  apply leftAndRightAreMinHeapAndRootIsMinOfChildrenToMinHeap
  constructor; all_goals try grind
  . cases a; all_goals (cases a_1; all_goals grind)

lemma getLastPreservesRoot (bt l r: BinaryTree α) (v v': α): bt = node l v r → bt.getLast.snd = node l' v' r' → v = v' := by
fun_induction getLast; all_goals grind

lemma getLastNode (bt l r: BinaryTree α) (v: α): bt = node l v r → ∃ bt' v', (some v', bt') = getLast bt := by
intro hbt
fun_induction getLast generalizing l v r; all_goals (expose_names; try grind)
. cases r_1; all_goals expose_names
  . contradiction
  . have: ∃ bt' v', (some v', bt') = (a.node a_1 a_2).getLast := by
      apply ih1 a a_2 a_1 (rfl)
    obtain ⟨bt', v', h⟩ := this
    use (node leaf v_1 bt'), v'
    grind
. cases l_1; all_goals expose_names
  . contradiction
  . have: ∃ bt' v', (some v', bt') = (a.node a_1 a_2).getLast := by
      apply ih1 a a_2 a_1 (rfl)
    obtain ⟨bt', v', h⟩ := this
    use (node bt' v_1 r_1), v'
    grind

lemma getLastPreservesMembersExceptLast (bt l r: BinaryTree α) (v v': α): bt = node l v r → contains bt v' → (getLast bt).1 ≠ some v' → contains (getLast bt).2 v' := by
intros hbt hbtc hv
fun_induction getLast generalizing l r v; all_goals (expose_names; try grind)
. simp
  cases r_1
  . contradiction
  . expose_names
    cases a
    . cases a_2
      . simp [getLast]
        grind
      . simp [getLast]
        grind
    . cases a_2
      . simp [getLast]
        grind
      . simp [getLast]
        grind
. simp
  cases l_1
  . contradiction
  . expose_names
    cases a
    . cases a_2
      . simp [getLast]
        grind
      . simp [getLast]
        grind
    . cases a_2
      . simp [getLast]
        grind
      . simp [getLast]
        grind

lemma extractMinPreservesMembersExceptRoot (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = node l v r  → isMinHeap bt f → contains bt v' → v ≠  v' → contains (extractMin bt f).2 v' := by
  intros; expose_names

  have hex: ∃ bt' v'', (some v'', bt') = getLast bt := by
    apply getLastNode bt l r v h
  obtain ⟨bt', v'', hv⟩ := hex
  have hlr: contains l v' ∨ contains r v' :=
    by grind
  rw [h] at hv
  rw [h]
  cases bt'
  . have: l = leaf := by grind
    have: r = leaf := by grind
    grind
  . expose_names
    have: a_1 = v := by
      grind[getLastPreservesRoot]
    have: a_1 ≠ v' := by grind
    have: l≠ leaf ∨ r≠leaf := by grind
    cases this; all_goals expose_names
    . rw [extractMin]
      rw [← hv]
      simp
      apply heapifyPreservesMembers (a.node v'' a_2) v' f
      by_cases v'' = v'
      . grind
      . suffices (l.node v r).getLast.2.contains v' by grind
        have hgl: (l.node v r).getLast.1 ≠ some v' := by grind
        apply getLastPreservesMembersExceptLast (node l v r) l r v v' (rfl) (_) hgl
        grind
    . rw [extractMin]
      rw [← hv]
      simp
      apply heapifyPreservesMembers (a.node v'' a_2) v' f
      by_cases v'' = v'
      . grind
      . suffices (l.node v r).getLast.2.contains v' by grind
        have hgl: (l.node v r).getLast.1 ≠ some v' := by grind
        apply getLastPreservesMembersExceptLast (node l v r) l r v v' (rfl) (_) hgl
        grind

lemma extractMinCorrectNode (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = node l v r  → isMinHeap bt f → ∃ bt' v', extractMin bt f = (some v', bt') ∧ isMinHeap bt' f ∧ f v = heapMin bt f := by
  intros; expose_names
  have hex: ∃ bt' v'', (some v'', bt') = getLast bt := by
    apply getLastNode bt l r v h
  obtain ⟨bt', v'', hv⟩ := hex
  cases bt'
  . use leaf
    use v''
    grind [isMinHeap, minHeapRootMin]
  . expose_names
    use (heapify (node a v'' a_2) f)
    use v
    constructor
    . rw [extractMin.eq_1]
      simp [← hv]
      grind [getLastPreservesRoot]
    . constructor
      . have: isMinHeap (node a a_1 a_2) f := by grind[getLastPreservesMinHeap]
        apply minHeapThenLeftAndRightAreMinHeap at this
        grind [leftAndRightAreMinHeap, heapifyEstablishesMinHeap]
      . grind [minHeapRootMin]

lemma getLastReturnsSome {α : Type u} [DecidableEq α] (bt : BinaryTree α) (hbt: bt ≠ leaf): ∃ v, some v = (getLast bt).1 := by
fun_induction getLast; all_goals grind

lemma extractMinReturnsSome {α : Type u} [DecidableEq α] (bt : BinaryTree α) (f : α → ENat) (hbt: bt ≠ leaf): ∃ v, some v = (extractMin bt f).1 := by
have: ∃ v, some v = (getLast bt).1 := by apply getLastReturnsSome bt hbt
grind

lemma extractMinIsSome {α : Type u} [DecidableEq α] (bt : BinaryTree α) (f : α → ENat) (hbt: bt ≠ leaf):(extractMin bt f).1.isSome := by
have: ∃ v, some v = (getLast bt).1 := by apply getLastReturnsSome bt hbt
grind

def getParent [DecidableEq α]: BinaryTree α → α → Option (BinaryTree α)
| leaf, _ => none
| node l v r, v' => match l, r with
    | leaf, leaf => none
    | leaf, node _ rv _ => if rv = v' then (node l v r) else getParent r v'
    | node _ lv _, leaf => if lv = v' then (node l v r) else getParent l v'
    | node _ lv _, node _ rv _ =>   if  rv = v' ∨  lv = v'
                                          then (node l v r)
                                        else let b := getParent l v
                                          match b with
                                          | some _ => b
                                          | none => getParent r v

def emin (m: ENat) (n: ENat): ENat := if m ≤  n then m else n

def dist_to_root [DecidableEq α]: (BinaryTree α) → α → ENat
| leaf, _ => ⊤
| node l v r, v' => if v' = v then 0 else 1 + (emin (dist_to_root l v') (dist_to_root r v'))

def card: BinaryTree α → ENat
| leaf => 0
| node l _ r => 1 + card l + card r


def siftUp [DecidableEq α] (bt: BinaryTree α) (f: α → ENat) (v': α): (BinaryTree α) := match bt with
| leaf => leaf
| node l v r => if v' = v then bt else match l, r with
    | leaf, leaf => leaf
    | leaf, node rl rv rr => if rv = v' then if f rv < f v then  (node l rv (node rl v rr)) else bt else siftUp r f v'
    | node ll lv lr, leaf => if lv = v' then if f lv < f v then  (node (node ll v lr) lv r) else bt else siftUp l f v'
    | node ll lv lr, node rl rv rr => if lv = v' then if f v' < f v then  (node (node ll v lr) lv r)
                                      else if rv = v' then if f v' < f v then  (node l rv (node rl v rr))
                                      else bt
                                      else bt
                                      else bt


def decreasePriority [DecidableEq α] (bt: BinaryTree α)  (v': α) (f: α → ENat): (BinaryTree α) := sorry
-- match bt with
-- | leaf => leaf
-- | node l v r => if v = v' then siftUp bt v
--                     else let n := decreasePriority l v'
--                       match n with
--                       | none => decreasePriority r v'
--                       | some _ => n


-- def decreasePriority [DecidableEq α] (bt: BinaryTree α) (f: α → ENat) (v': α):  (BinaryTree α) :=
-- let


-- lemma decreasePriorityPreservesMembers [DecidableEq α] (bt: BinaryTree α) (v v': α) (f: α → ENat): contains bt v → contains (decreasePriority bt f v') v := by


def size: (BinaryTree α) →  Nat
| leaf => 0
| node l _ r => 1 + size l + size r
structure BinaryHeap (α : Type u) [DecidableEq α] where
  tree : BinaryTree α

#check BinaryTree

namespace BinaryHeap

def empty [DecidableEq α]: BinaryHeap α := { tree := BinaryTree.leaf }
def isEmpty [DecidableEq α] (h: BinaryHeap α): Bool :=  match h.tree with
| leaf => true
| _ => false

def add {α : Type u} [DecidableEq α] (h : BinaryHeap α) (v : α) (priority : α → ENat) : BinaryHeap α :=
  {tree:= (h.tree.insert v priority)}

lemma extractMinIsSomeHeap {α : Type u} [DecidableEq α] (h : BinaryHeap α) (f : α → ENat) (hh: ¬ isEmpty h): (extractMin h.tree f).1.isSome := by
grind[isEmpty, extractMinIsSome]

noncomputable def extract_min {α : Type u} [Nonempty α] [DecidableEq α] (h : BinaryHeap α) (priority : α → ENat) (hh: ¬ isEmpty h): (α × BinaryHeap α) :=
  ((h.tree.extractMin priority).1.get (by grind[extractMinIsSomeHeap]) , {tree:= (h.tree.extractMin priority).2})

def sizeOf {α : Type u} [DecidableEq α] (h : BinaryHeap α) : Nat := h.tree.size

def decrease_priority [DecidableEq α] (h : BinaryHeap α) (v : α) (prio :α →  ENat) : BinaryHeap α :=
{tree:= decreasePriority h.tree v prio}

-- Helper lemma: decreasing priority does not increase heap size
theorem heapSize_decrease_priority_le {α : Type u} [DecidableEq α] (h : BinaryHeap α) (v : α) (prio :α → ENat) :
  sizeOf (decrease_priority h v prio) ≤ sizeOf h := by
  -- To be proved from the concrete heap implementation
  sorry

-- Helper lemma: extracting the minimum from a non-empty heap strictly decreases its size.
theorem heapSize_extract_min_lt_of_isEmpty_eq_false
    {V : Type*} [Nonempty V] [DecidableEq V] (h : BinaryHeap V) (hNE : isEmpty h = false) (priority: V → ENat):
    sizeOf (Prod.snd (extract_min h priority (by grind))) < sizeOf h := by
  -- To be proved from the concrete heap implementation
  sorry


-- minimimla heap-distance consistency lemma
lemma key_at_y_le_extracted_min [Nonempty V] [DecidableEq V]
  (y : V) (p : (V → ENat) × BinaryHeap V) (priority: V → ENat) (hNE : isEmpty p.2 = false) :
  ∀ u1, Prod.fst (p.2.extract_min priority (by grind)) = u1 → p.1 y ≤ p.1 u1 := by
  intro u1 hu1
  -- Admitted: BinaryHeap semantics ensuring the extracted minimum is not
  -- smaller than the finalized key `y`.
  admit

end BinaryHeap
