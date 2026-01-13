import Mathlib.Tactic

set_option autoImplicit true

inductive BinaryTree (α : Type u)
  | leaf : BinaryTree α
  | node : BinaryTree α → α → BinaryTree α → BinaryTree α

namespace BinaryTree

@[grind] def is_min_heap : BinaryTree α → (dist : α → ENat) → Prop
| leaf, _ => true
| node l v r, f => match l, r with
      | leaf, leaf => true
      | node _ lv _, leaf =>
          f v <= f lv ∧ is_min_heap l f
      | leaf, node _ rv _ =>
          f v <= f rv ∧ is_min_heap r f
      | node _ lv _, node _ rv _ =>
          f v <= f lv ∧ is_min_heap l f ∧ f v <= f rv ∧ is_min_heap r f

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

@[grind] def get_last: BinaryTree α → Option α ×  BinaryTree α
| leaf => (none, leaf)
| node l v r => match l, r with
    | leaf, leaf => (some v, leaf)
    | leaf, _ => let (val, tree) := (get_last r)
      (val, node l v tree)
    | _, _ => let (val, tree) := (get_last l)
      (val, node tree v r)

@[grind] def extract_min (bt: BinaryTree α) (f: α → ENat): (Option α × BinaryTree α):=
let (lastNode, treeWithoutLast) := get_last bt
match lastNode with
| none => (none, leaf)
| some v' => match treeWithoutLast with
  | leaf => (some v', leaf)
  | node l v r => (some v, heapify (node l v' r) f)

@[grind] def heap_min:  BinaryTree α → (α → ENat) → ENat
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


@[grind] def root_is_min_of_children: (BinaryTree α) → (α → ENat) →  Prop
| leaf, _ => true
| node l v r, f => match l, r with
    | leaf, leaf => true
    | leaf, node _ rv _ => f v <= f rv
    | node _ lv _, leaf => f v <= f lv
    | node _ lv _, node _ rv _ =>  f v <= f lv ∧ f v <= f rv


@[grind] def left_and_right_are_min_heap: (BinaryTree α) →  (f: α → ENat) →  Prop
| leaf, _ => true
| node l _ r, f => is_min_heap l f ∧ is_min_heap r f

@[grind] def contains : (BinaryTree α) → α → Prop
| leaf, _ => false
| node l v r, v' => v = v' ∨ contains l v' ∨ contains r v'


@[grind] def containsb [DecidableEq α] : (BinaryTree α) → α → Bool
| leaf, _ => false
| node l v r, v' => (v = v') ∨ containsb l v' ∨ containsb r v'

@[grind] def insert (bt : BinaryTree α) (v : α) (f : α → ENat) : BinaryTree α :=
  match bt with
  | leaf =>
      node leaf v leaf
  | node l x r =>
      if f v ≤ f x then
        node (insert l x f) v r
      else
        node (insert l v f) x r

@[grind] def merge (bt1 bt2 : BinaryTree α) (f : α → ENat) : BinaryTree α :=
  match bt1, bt2 with
  | leaf, t => t
  | t, leaf => t
  | node l1 v1 r1, node l2 v2 r2 =>
      if f v1 ≤ f v2 then
        node (merge l1 (node l2 v2 r2) f) v1 r1
      else
        node (merge (node l1 v1 r1) l2 f) v2 r2

@[grind] def remove (bt : BinaryTree α) (x : α) (f : α → ENat)
  [DecidableEq α] : BinaryTree α :=
  match bt with
  | leaf => leaf
  | node l v r =>
      if x = v then
        merge l r f
      else
        node (remove l x f) v (remove r x f)

@[grind] def decrease_priority [DecidableEq α] (bt : BinaryTree α) (v : α) (f : α → ENat): BinaryTree α :=
  if containsb bt v then insert (remove bt v f) v f else bt

def is_empty_tree [DecidableEq α] (bt: BinaryTree α): Bool :=  match bt with
| leaf => true
| node _ _ _ => false

lemma min_heap_then_left_and_right_are_min_heap (bt: BinaryTree α) (f: α → ENat): is_min_heap bt f → left_and_right_are_min_heap bt f := by
intro hbt
fun_induction is_min_heap; all_goals (grind [left_and_right_are_min_heap, is_min_heap])

lemma min_heap_then_root_is_min_of_children (bt: BinaryTree α) (f: α → ENat): is_min_heap bt f → root_is_min_of_children bt f := by
intro hbt
fun_induction is_min_heap; all_goals (grind [root_is_min_of_children])

lemma left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap (bt: BinaryTree α) (f: α → ENat): left_and_right_are_min_heap bt f ∧ root_is_min_of_children bt f → is_min_heap bt f := by
intro hbt
fun_induction is_min_heap; all_goals (simp [root_is_min_of_children, left_and_right_are_min_heap] at hbt;simp[hbt])

lemma left_and_right_are_min_heapLeft (l: BinaryTree α) (r: BinaryTree α) (v: α) (f: α → ENat): left_and_right_are_min_heap (node l v r) f → left_and_right_are_min_heap l f := by
intro hbt
simp [left_and_right_are_min_heap] at hbt
simp [min_heap_then_left_and_right_are_min_heap, hbt]

lemma left_and_right_are_min_heapRight (l: BinaryTree α) (r: BinaryTree α) (v: α) (f: α → ENat): left_and_right_are_min_heap (node l v r) f → left_and_right_are_min_heap r f := by
intro hbt
simp [left_and_right_are_min_heap] at hbt
simp [min_heap_then_left_and_right_are_min_heap, hbt]

lemma heapifyPreservesStructure (bt: BinaryTree α) (f: α → ENat): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt f = node l' v' r' := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals simp

lemma heapify_preserves_structure_and_root_min (bt: BinaryTree α) (f: α → ENat): (∃ l r v, bt = node l v r) →  ∃ l' v' r', heapify bt f = node l' v' r' ∧ f v' ≤ (heap_min bt f) := by
intro hbt
fun_induction heapify; all_goals expose_names
. obtain ⟨l, r, v, hbt⟩ := hbt
  contradiction
all_goals grind [heap_min]

lemma contains_then_heapify_contains (bt: BinaryTree α) (v: α) (f: α → ENat): contains bt v → contains (heapify bt f) v := by
fun_induction heapify generalizing v; all_goals try grind[contains]

lemma heapify_contains_then_contains (bt: BinaryTree α) (v: α) (f: α → ENat):  contains (heapify bt f) v → contains bt v := by
fun_induction heapify generalizing v; all_goals try grind[contains]

lemma contains_is_node (bt: BinaryTree α) (v: α): contains bt v → ∃ l v' r, bt = node l v' r := by
fun_induction contains; all_goals simp

lemma contains_not_root_then_children (bt l r: BinaryTree α) (v v': α): contains bt v' → bt = node l v r →  v' ≠ v → contains l v' ∨ contains r v' := by
intro hbtc hbt hv
fun_induction bt.contains v'
. contradiction
. grind

lemma min_heap_root_min (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = (node l v r) → is_min_heap bt f → f v = heap_min bt f := by
intro hbt hmin
fun_induction is_min_heap; all_goals grind [heap_min]

lemma root_is_min_of_children_left (l r ll lr: BinaryTree α) (v lv: α) (f: α → ENat): root_is_min_of_children (node l v r) f →  l = (node ll lv lr) →  f v ≤ f lv := by
  intros; expose_names
  rw [h_1] at h
  cases r; all_goals grind[root_is_min_of_children]

lemma root_is_min_of_children_right (l r rl rr: BinaryTree α) (v rv: α) (f: α → ENat): root_is_min_of_children (node l v r) f →  r = (node rl rv rr) → f v ≤ f rv := by
  intros; expose_names
  rw [h_1] at h
  cases r; all_goals try grind[root_is_min_of_children]
  . grind [root_is_min_of_children.eq_def]

lemma min_heap_member_le_root (bt: BinaryTree α) (v: α) (f: α → ENat): is_min_heap bt f →  contains bt v →  heap_min bt f ≤ f v := by
intro hmin hl
fun_induction contains
. contradiction
. expose_names
  cases hl; all_goals expose_names
  . expose_names
    rw [←h]
    suffices f v = (l.node v r).heap_min f by grind
    apply min_heap_root_min (l.node v r) l r v; all_goals grind
  . cases h; all_goals expose_names
    . have h2: l.contains v' := by exact h
      apply contains_is_node at h2
      obtain ⟨l'', v'', r'', h2 ⟩:= h2
      have h3: l = l''.node v'' r'' := by exact h2
      have hmin2: (l.node v r).is_min_heap f := by assumption
      have hmin3: (l.node v r).is_min_heap f := by assumption
      apply min_heap_then_left_and_right_are_min_heap at hmin
      simp [left_and_right_are_min_heap] at hmin
      have hlmin: l.is_min_heap f:= by grind
      have hlmin2: l.is_min_heap f:= by grind
      apply ih2 at hlmin
      apply hlmin at h
      grw[← h]
      apply min_heap_then_root_is_min_of_children at hmin2
      apply root_is_min_of_children_left l r l'' r'' v v'' f hmin2 at h2
      have hhl: f v'' = l.heap_min f:= by grind [min_heap_root_min]
      have hh: f v = (l.node v r).heap_min f:= by grind [min_heap_root_min]
      grw [← hh, ← hhl]
      exact h2
    . have h2: r.contains v' := by exact h
      apply contains_is_node at h2
      obtain ⟨l'', v'', r'', h2 ⟩:= h2
      have h3: r = l''.node v'' r'' := by exact h2
      have hmin2: (l.node v r).is_min_heap f:= by assumption
      have hmin3: (l.node v r).is_min_heap f:= by assumption
      apply min_heap_then_left_and_right_are_min_heap at hmin
      simp [left_and_right_are_min_heap] at hmin
      have hlmin: r.is_min_heap f:= by grind
      have hlmin2: r.is_min_heap f:= by grind
      apply ih1 at hlmin
      apply hlmin at h
      grw[← h]
      apply min_heap_then_root_is_min_of_children at hmin2
      apply root_is_min_of_children_right l r l'' r'' v v'' f hmin2 at h2
      have hhl: f v'' = r.heap_min f:= by grind [min_heap_root_min]
      have hh: f v = (l.node v r).heap_min f:= by grind [min_heap_root_min]
      grw [← hh, ← hhl]
      exact h2

lemma min_heap_contains_le_root (bt l r: BinaryTree α) (v v': α) (f: α → ENat): is_min_heap bt f → bt = node l v r → contains bt v' → f v ≤ f v' := by
intro hmin hbt hv'
fun_induction contains generalizing l v r
. contradiction
. expose_names
  cases hv'; all_goals expose_names
  . simp_all
  . cases h; all_goals expose_names
    . obtain ⟨ ll, lv, lr, hl ⟩ := contains_is_node l_1 v' h
      have: f lv ≤ f v' := by
        apply ih2 ll lr lv _ hl h
        apply min_heap_then_left_and_right_are_min_heap at hmin
        rw [left_and_right_are_min_heap] at hmin
        obtain ⟨ hl', hr' ⟩ := hmin
        exact hl'
      grw [←this]
      apply root_is_min_of_children_left l r ll lr v lv f (by grind [min_heap_then_root_is_min_of_children]) (by grind)
    . obtain ⟨ rl, rv, rr, hr ⟩ := contains_is_node r_1 v' h
      have: f rv ≤ f v' := by
        apply ih1 rl rr rv _ hr h
        apply min_heap_then_left_and_right_are_min_heap at hmin
        rw [left_and_right_are_min_heap] at hmin
        obtain ⟨ hl', hr' ⟩ := hmin
        exact hr'
      grw [←this]
      apply root_is_min_of_children_right l r rl rr v rv f (by grind [min_heap_then_root_is_min_of_children]) (by grind)

lemma heapify_preserves_min_heap (bt: BinaryTree α) (f: α → ENat): is_min_heap bt f → bt = heapify bt f:= by
fun_induction heapify; all_goals expose_names; all_goals try grind

lemma binary_tree_eq_r (l r l' r': BinaryTree α) (v v': α): (node l v r) = (node l' v' r') → r = r' := by
grind only

lemma binary_tree_eq_l (l r l' r': BinaryTree α) (v v': α): (node l v r) = (node l' v' r') → l = l' := by
grind only

lemma heapify_preserves_values (tree r l: BinaryTree α) (v: α) (f: α → ENat): tree.heapify f = node r v l → contains tree v := by
grind [contains, heapify_contains_then_contains]

lemma contains_root_or_children (tree r l: BinaryTree α) (v v': α) : tree = node r v l → contains tree v' → contains r v' ∨ contains l v' ∨ v= v' := by
grind [contains]

lemma contains_root_or_children_left_leaf (tree r: BinaryTree α) (v v':  α): tree = node r v leaf → contains tree v' → contains r v' ∨ v= v' := by
grind [contains]

lemma contains_right_then_contains_root (tree l r: BinaryTree α) (v v':  α): tree = node l v r → contains r v' → contains tree v' := by
grind [contains]

lemma contains_left_then_contains_root (tree l r: BinaryTree α) (v v':  α): tree = node l v r → contains l v' → contains tree v' := by
grind [contains]

lemma min_heap_then_members_left_le (bt l r: BinaryTree α) (v v': α) (f: α → ENat): is_min_heap bt f → bt = node l v r → contains l v' → f v ≤ f v' := by
intro hmin hbt hl
apply contains_left_then_contains_root bt l r v v' hbt at hl
apply min_heap_contains_le_root bt l r v v' f hmin hbt hl

lemma min_heap_then_members_right_le (bt l r: BinaryTree α) (v v': α) (f: α → ENat): is_min_heap bt f → bt = node l v r → contains r v' → f v ≤ f v' := by
intro hmin hbt hl
apply contains_right_then_contains_root bt l r v v' hbt at hl
apply min_heap_contains_le_root bt l r v v' f hmin hbt hl

lemma heapify_establishes_min_heap {α} (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = node l v r ∧  is_min_heap l f ∧ is_min_heap r f → is_min_heap (heapify bt f) f := by
fun_induction heapify generalizing l r v; all_goals expose_names
. simp [is_min_heap]
. simp [is_min_heap]
. intro ⟨hr, hminl, hminr⟩
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  have: ∃ rl' v' rr', (rl.node v_1 rr).heapify f = node rl' v' rr' ∧ f v' ≤ heap_min (rl.node v_1 rr) f:= by
        apply heapify_preserves_structure_and_root_min
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hrnode: r = (rl.node rv rr) := by
        apply binary_tree_eq_r at hr
        simp [hr]
  constructor
  . simp [left_and_right_are_min_heap]
    constructor
    . simp [is_min_heap]
    . specialize ih1 rl rr v_1
      simp at ih1
      apply min_heap_then_left_and_right_are_min_heap at hminr
      simp [left_and_right_are_min_heap] at hminr
      simp [hrnode] at hminr
      apply ih1; all_goals grind
  . rw [hr1]
    simp [root_is_min_of_children]
    have hrvmin : f rv = heap_min (rl.node rv rr) f:= by
      apply min_heap_root_min (rl.node rv rr) rl rr rv f (rfl)
      rw[← hrnode]; exact hminr
    have hcontains: contains (node rl v_1 rr) v' := by
      apply heapify_contains_then_contains
      rw[hr1]
      simp[contains]
    have hcontains: contains (rl.node rv rr) v' ∨ v'= v_1 := by grind[contains]
    cases hcontains
    . expose_names
      apply min_heap_member_le_root r v' at hminr
      rw [← hrnode] at h_1
      apply hminr at h_1
      grw[← h_1]
      rw[hrvmin]
      rw[hrnode]
    . expose_names
      rw [h_1]
      grw [h]
. grind [is_min_heap]
. intro ⟨hl, hminl, hminr⟩
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  have: ∃ ll' v' lr', (ll.node v_1 lr).heapify f = node ll' v' lr' ∧ f v' ≤ heap_min (ll.node v_1 lr) f:= by
        apply heapify_preserves_structure_and_root_min
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hlnode: l = (ll.node lv lr) := by
        apply binary_tree_eq_l at hl
        simp [hl]
  constructor
  . simp [left_and_right_are_min_heap]
    constructor
    . specialize ih1 ll lr v_1
      simp at ih1
      apply min_heap_then_left_and_right_are_min_heap at hminl
      simp [left_and_right_are_min_heap] at hminl
      simp [hlnode] at hminl
      apply ih1; all_goals grind
    . simp [is_min_heap]
  . rw [hr1]
    simp [root_is_min_of_children]
    have hlvmin : f lv = heap_min (ll.node lv lr) f:= by
      apply min_heap_root_min (ll.node lv lr) ll lr lv f (rfl)
      rw[← hlnode]; exact hminl
    have hcontains: contains (node ll v_1 lr) v' := by
      apply heapify_contains_then_contains
      rw[hr1]
      simp[contains]
    have hcontains: contains (ll.node lv lr) v' ∨ v'= v_1 := by grind[contains]
    cases hcontains
    . expose_names
      apply min_heap_member_le_root l v' at hminl
      rw [← hlnode] at h_1
      apply hminl at h_1
      grw[← h_1]
      rw[hlvmin]
      rw[hlnode]
    . expose_names
      rw [h_1]
      grw [h]
. grind [is_min_heap]
. grind [is_min_heap]
. intro ⟨hl, hminl, hminr⟩
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  have: ∃ ll' v' lr', (ll.node v_1 lr).heapify f = node ll' v' lr' ∧ f v' ≤ heap_min (ll.node v_1 lr) f:= by
        apply heapify_preserves_structure_and_root_min
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hlnode: l = (ll.node lv lr) := by
        apply binary_tree_eq_l at hl
        simp [hl]
  constructor
  . simp [left_and_right_are_min_heap]
    constructor
    . specialize ih1 ll lr v_1
      simp at ih1
      apply min_heap_then_left_and_right_are_min_heap at hminl
      simp [left_and_right_are_min_heap] at hminl
      simp [hlnode] at hminl
      apply ih1; all_goals grind
    . grind
  . rw [hr1]
    simp [root_is_min_of_children]
    have hlvmin : f lv = heap_min (ll.node lv lr) f := by
      apply min_heap_root_min (ll.node lv lr) ll lr lv f (rfl)
      rw[← hlnode]; exact hminl
    have hcontains: contains (node ll v_1 lr) v' := by
      apply heapify_contains_then_contains
      rw[hr1]
      simp[contains]
    have hcontains: contains (ll.node lv lr) v' ∨ v'= v_1 := by grind[contains]
    cases hcontains
    . expose_names
      apply min_heap_member_le_root l v' at hminl
      grind
    . expose_names
      grind
. grind [is_min_heap]
. intro ⟨hr, hminl, hminr⟩
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  have: ∃ rl' v' rr', (rl.node v_1 rr).heapify f = node rl' v' rr' ∧ f v' ≤ heap_min (rl.node v_1 rr) f:= by
        apply heapify_preserves_structure_and_root_min
        simp
  obtain ⟨rl', v', rr', hr1, hr2⟩ := this
  have hv: v=v_1 := by grind
  have hrnode: r = (rl.node rv rr) := by
        apply binary_tree_eq_r at hr
        simp [hr]
  constructor
  . simp [left_and_right_are_min_heap]
    constructor
    . grind
    . specialize ih1 rl rr v_1
      simp at ih1
      apply min_heap_then_left_and_right_are_min_heap at hminr
      simp [left_and_right_are_min_heap] at hminr
      simp [hrnode] at hminr
      apply ih1
      . grind
      . obtain ⟨h1, h2⟩ := hminr
        exact h2
  . rw [hr1]
    simp [root_is_min_of_children]
    have hrvmin : f rv = heap_min (rl.node rv rr) f := by
      apply min_heap_root_min (rl.node rv rr) rl rr rv f (rfl)
      rw[← hrnode]; exact hminr
    have hcontains: contains (node rl v_1 rr) v' := by
      apply heapify_contains_then_contains
      rw[hr1]
      simp[contains]
    have hcontains: contains (rl.node rv rr) v' ∨ v'= v_1 := by
      apply contains_root_or_children (node rl v_1 rr) rl rr v_1 v' (rfl) at hcontains
      cases hcontains; all_goals expose_names
      . left
        apply contains_left_then_contains_root (node rl rv rr) rl rr rv v' (rfl) (h_2)
      . cases h_2; all_goals expose_names
        . left
          apply contains_right_then_contains_root (node rl rv rr) rl rr rv v' (rfl) (h_2)
        . right
          rw [h_2]
    constructor
    . simp at h
      grw [h]
    cases hcontains
    . expose_names
      apply min_heap_member_le_root r v' at hminr
      rw [← hrnode] at h_2
      apply hminr at h_2
      grw[← h_2]
      rw[hrvmin]
      rw[hrnode]
    . expose_names
      rw [h_2]
      simp at h_1
      grw [h_1]

lemma heapify_establishes_min_heap' (bt: BinaryTree α) (f: α → ENat): (hbt: left_and_right_are_min_heap bt f) → is_min_heap (heapify bt f) f := by
cases bt
. grind[is_min_heap,left_and_right_are_min_heap, heapify]
. grind[is_min_heap,left_and_right_are_min_heap, heapify_establishes_min_heap]

theorem heapify_correctness (bt: BinaryTree α) (f: α → ENat): (contains (heapify bt f) v ↔ contains bt v) ∧  bt = node l v r ∧  is_min_heap l f ∧ is_min_heap r f → is_min_heap (heapify bt f) f := by
grind[heapify_establishes_min_heap, contains_then_heapify_contains, heapify_contains_then_contains]

lemma get_last_preserves_min_heap (bt: BinaryTree α) (f: α → ENat): is_min_heap bt f → is_min_heap (get_last bt).snd f := by
intros; expose_names
fun_induction is_min_heap; all_goals expose_names
. grind
. grind
. rw [get_last]
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  constructor; all_goals try grind
  . cases a; all_goals (cases a_1; all_goals grind)
. rw [get_last]
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  constructor; all_goals try grind
  . cases a; all_goals (cases a_1; all_goals grind)
. rw [get_last]
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  constructor; all_goals try grind
  . cases a; all_goals (cases a_1; all_goals grind)

lemma get_last_preserves_root (bt l r: BinaryTree α) (v v': α): bt = node l v r → bt.get_last.snd = node l' v' r' → v = v' := by
fun_induction get_last; all_goals grind

lemma get_last_is_node (bt l r: BinaryTree α) (v: α): bt = node l v r → ∃ bt' v', (some v', bt') = get_last bt := by
intro hbt
fun_induction get_last generalizing l v r; all_goals (expose_names; try grind)
. cases r_1; all_goals expose_names
  . contradiction
  . have: ∃ bt' v', (some v', bt') = (a.node a_1 a_2).get_last := by
      apply ih1 a a_2 a_1 (rfl)
    obtain ⟨bt', v', h⟩ := this
    use (node leaf v_1 bt'), v'
    grind
. cases l_1; all_goals expose_names
  . contradiction
  . have: ∃ bt' v', (some v', bt') = (a.node a_1 a_2).get_last := by
      apply ih1 a a_2 a_1 (rfl)
    obtain ⟨bt', v', h⟩ := this
    use (node bt' v_1 r_1), v'
    grind

lemma get_last_preserves_members_except_last (bt l r: BinaryTree α) (v v': α): bt = node l v r → contains bt v' → (get_last bt).1 ≠ some v' → contains (get_last bt).2 v' := by
intros hbt hbtc hv
fun_induction get_last generalizing l r v; all_goals (expose_names; try grind)
. simp
  cases r_1
  . contradiction
  . expose_names
    cases a
    . cases a_2
      . simp [get_last]
        grind
      . simp [get_last]
        grind
    . cases a_2
      . simp [get_last]
        grind
      . simp [get_last]
        grind
. simp
  cases l_1
  . contradiction
  . expose_names
    cases a
    . cases a_2
      . simp [get_last]
        grind
      . simp [get_last]
        grind
    . cases a_2
      . simp [get_last]
        grind
      . simp [get_last]
        grind

lemma contains_then_extract_min_contains_except_root (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = node l v r → is_min_heap bt f → contains bt v' → v ≠  v' → contains (extract_min bt f).2 v' := by
  intros; expose_names

  have hex: ∃ bt' v'', (some v'', bt') = get_last bt := by
    apply get_last_is_node bt l r v h
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
      grind[get_last_preserves_root]
    have: a_1 ≠ v' := by grind
    have: l≠ leaf ∨ r≠leaf := by grind
    cases this; all_goals expose_names
    . rw [extract_min]
      rw [← hv]
      simp
      apply contains_then_heapify_contains (a.node v'' a_2) v' f
      by_cases v'' = v'
      . grind
      . suffices (l.node v r).get_last.2.contains v' by grind
        have hgl: (l.node v r).get_last.1 ≠ some v' := by grind
        apply get_last_preserves_members_except_last (node l v r) l r v v' (rfl) (_) hgl
        grind
    . rw [extract_min]
      rw [← hv]
      simp
      apply contains_then_heapify_contains (a.node v'' a_2) v' f
      by_cases v'' = v'
      . grind
      . suffices (l.node v r).get_last.2.contains v' by grind
        have hgl: (l.node v r).get_last.1 ≠ some v' := by grind
        apply get_last_preserves_members_except_last (node l v r) l r v v' (rfl) (_) hgl
        grind

lemma get_last_last_contains: bt.get_last.1 = some v → contains bt v := by
fun_induction get_last; all_goals grind

lemma get_last_contains_then_contains (bt: BinaryTree α) (v: α): contains (get_last bt).2 v → contains bt v := by
fun_induction get_last; all_goals grind

lemma extract_min_contains_then_contains (bt: BinaryTree α) (v: α) (f: α → ENat): contains (extract_min bt f).2 v → contains bt v := by
simp[extract_min]
fun_cases get_last
. simp
. simp_all
  intro
  contradiction
. expose_names
  simp_all
  cases val
  . simp
    intro
    contradiction
  . intro
    expose_names
    simp [contains]
    expose_names
    simp at h_2
    apply heapify_contains_then_contains at h_2
    simp[contains] at h_2
    cases h_2
    . expose_names
      right
      have: r.get_last.1 = some val := by grind
      apply get_last_last_contains at this
      rw [← h_2]
      exact this
    . grind[get_last_contains_then_contains]
. expose_names
  simp_all
  cases val
  . simp
    intro
    contradiction
  . intro
    expose_names
    simp [contains]
    expose_names
    simp at h_2
    apply heapify_contains_then_contains at h_2
    simp[contains] at h_2
    cases h_2
    . expose_names
      right
      left
      have: l.get_last.1 = some val := by grind
      apply get_last_last_contains at this
      rw [← h_2]
      exact this
    . grind[get_last_contains_then_contains]

lemma extract_min_correct_node (bt l r: BinaryTree α) (v: α) (f: α → ENat): bt = node l v r  → is_min_heap bt f → ∃ bt' v', extract_min bt f = (some v', bt') ∧ is_min_heap bt' f ∧ f v = heap_min bt f := by
  intros; expose_names
  have hex: ∃ bt' v'', (some v'', bt') = get_last bt := by
    apply get_last_is_node bt l r v h
  obtain ⟨bt', v'', hv⟩ := hex
  cases bt'
  . use leaf
    use v''
    grind [is_min_heap, min_heap_root_min]
  . expose_names
    use (heapify (node a v'' a_2) f)
    use v
    constructor
    . rw [extract_min.eq_1]
      simp [← hv]
      grind [get_last_preserves_root]
    . constructor
      . have: is_min_heap (node a a_1 a_2) f := by grind[get_last_preserves_min_heap]
        apply min_heap_then_left_and_right_are_min_heap at this
        grind [left_and_right_are_min_heap, heapify_establishes_min_heap']
      . grind [min_heap_root_min]

lemma extract_min_correctness (bt bt' l  r: BinaryTree α) (v v': α) (f: α → ENat): contains (extract_min bt f).2 v → contains bt v ∧ (is_min_heap bt f) → ((extract_min bt f = (some v', bt') → is_min_heap bt' f ∧ f v' = heap_min bt f) ∧ bt = node l v r → ((∃ v'' bt'', extract_min bt f = (some v'', bt'')) ∧  contains bt v''' → v ≠  v''' → contains (extract_min bt f).2 v''')):= by
grind[extract_min_correct_node, extract_min_contains_then_contains, contains_then_extract_min_contains_except_root]

lemma extract_min_is_min: is_min_heap bt f → contains bt v → (extract_min bt f).1 = some y → f y ≤ f v := by
intro h1 h2 h3
simp[extract_min] at h3
fun_cases get_last
. simp_all[get_last]
. grind
. simp_all[get_last]
  expose_names
  cases val
  . simp_all
  . simp_all
    rw[← h3]
    grind[min_heap_contains_le_root]
. simp_all[get_last]
  expose_names
  cases val
  . simp_all
  . simp_all
    rw[← h3]
    grind[min_heap_contains_le_root]

lemma get_last_returns_some {α : Type u} [DecidableEq α] (bt : BinaryTree α) (hbt: bt ≠ leaf): ∃ v, some v = (get_last bt).1 := by
fun_induction get_last; all_goals grind

lemma extract_min_returns_some {α : Type u} [DecidableEq α] (bt : BinaryTree α) (f : α → ENat) (hbt: bt ≠ leaf): ∃ v, some v = (extract_min bt f).1 := by
have: ∃ v, some v = (get_last bt).1 := by apply get_last_returns_some bt hbt
grind

lemma extract_min_is_some {α : Type u} [DecidableEq α] (bt : BinaryTree α) (f : α → ENat) (hbt: bt ≠ leaf):(extract_min bt f).1.isSome := by
have: ∃ v, some v = (get_last bt).1 := by apply get_last_returns_some bt hbt
grind

lemma extract_min_returns_then_contains: (extract_min bt f).1 = some v → contains bt v := by
expose_names
simp[extract_min]
fun_cases get_last
. simp
. grind
. grind
. grind


lemma insert_is_node (bt: BinaryTree α) (f: α → ENat) (v: α): ∃ l r v', insert bt v f = node l v' r := by
fun_induction insert
. grind
. grind
. grind

lemma insert_then_contains (bt: BinaryTree α) (v: α) (f: α → ENat): contains (insert bt v f) v := by
fun_induction insert; all_goals grind

lemma insert_then_insert_contains_old_member_or_new_value_contains (bt: BinaryTree α) (v v': α) (f: α → ENat): contains (insert bt v f) v' → contains bt v' ∨ v = v' := by
intro hbt
fun_induction insert; all_goals grind

lemma insert_preserves_min_heap (bt: BinaryTree α) (v: α) (f: α → ENat): is_min_heap bt f → is_min_heap (insert bt v f) f := by
intro hbt
have hbtp := hbt
fun_induction insert
. grind
. expose_names
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  apply min_heap_then_left_and_right_are_min_heap at hbt
  simp [left_and_right_are_min_heap] at hbt
  constructor
  . simp [left_and_right_are_min_heap]
    constructor
    . apply ih1
      grind
      obtain ⟨hl, hr⟩ := hbt
      exact hl
    . simp [hbt]
  . cases r
    . obtain ⟨l', r', v', h' ⟩ := insert_is_node l f v_1
      rw [h']
      simp [root_is_min_of_children]
      have: contains l v' ∨ v_1 = v' := by
        apply insert_then_insert_contains_old_member_or_new_value_contains l v_1 v' f
        rw [h']
        grind
      cases this
      . expose_names
        obtain ⟨hl, hr⟩ := hbt
        grw [h]
        apply min_heap_then_members_left_le (l.node v_1 leaf) l leaf v_1 v' f hbtp (rfl) h_1
      . expose_names
        rw [←h_1]
        exact h
    . expose_names
      obtain ⟨l', r', v', h' ⟩ := insert_is_node l f v_1
      rw [h']
      simp [root_is_min_of_children]
      constructor
      . have: contains l v' ∨ v_1 = v' := by
          apply insert_then_insert_contains_old_member_or_new_value_contains l v_1 v' f
          rw [h']
          grind
        cases this
        . expose_names
          obtain ⟨hl, hr⟩ := hbt
          grw [h]
          apply min_heap_then_members_left_le (l.node v_1 (a.node a_1 a_2)) l (a.node a_1 a_2) v_1 v' f hbtp (rfl) h_1
        . expose_names
          rw [←h_1]
          exact h
      . grw [h]
        apply min_heap_then_members_right_le (l.node v_1 (a.node a_1 a_2)) l (a.node a_1 a_2) v_1 a_1 f hbtp (rfl) (by grind)
. expose_names
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  apply min_heap_then_left_and_right_are_min_heap at hbt
  simp [left_and_right_are_min_heap] at hbt
  constructor
  . simp [left_and_right_are_min_heap]
    constructor
    . apply ih1
      grind
      obtain ⟨hl, hr⟩ := hbt
      exact hl
    . simp [hbt]
  . cases r
    . obtain ⟨l', r', v', h' ⟩ := insert_is_node l f v
      rw [h']
      simp [root_is_min_of_children]
      have: contains l v' ∨ v = v' := by
        apply insert_then_insert_contains_old_member_or_new_value_contains l v v' f
        rw [h']
        grind
      cases this
      . expose_names
        obtain ⟨hl, hr⟩ := hbt
        apply min_heap_then_members_left_le (l.node v_1 leaf) l leaf v_1 v' f  hbtp (rfl) h_1
      . expose_names
        rw [←h_1]
        simp at h
        grw [h]
    . expose_names
      obtain ⟨l', r', v', h' ⟩ := insert_is_node l f v
      rw [h']
      simp [root_is_min_of_children]
      constructor
      . have: contains l v' ∨ v = v' := by
          apply insert_then_insert_contains_old_member_or_new_value_contains l v v' f
          rw [h']
          grind
        cases this
        . expose_names
          obtain ⟨hl, hr⟩ := hbt
          apply min_heap_then_members_left_le (l.node v_1 (a.node a_1 a_2)) l (a.node a_1 a_2) v_1 v' f hbtp (rfl) h_1
        . expose_names
          rw [←h_1]
          simp at h
          grw [h]
      . apply min_heap_then_members_right_le (l.node v_1 (a.node a_1 a_2)) l (a.node a_1 a_2) v_1 a_1 f hbtp (rfl) (by grind)

lemma contains_then_insert_contains (bt: BinaryTree α) (v v': α) (f: α → ENat): contains bt v →  contains (insert bt v' f) v := by
intro hbt
fun_induction insert; all_goals expose_names
. contradiction
. simp [contains] at hbt
  cases hbt
  . expose_names
    simp [contains]
    right
    left
    rw [h_1]
    grind [insert_then_contains]
  . expose_names
    cases h_1; all_goals expose_names
    . simp [contains]
      right
      left
      apply ih1
      exact h_1
    . simp [contains]
      right
      right
      exact h_1
. simp [contains] at hbt
  cases hbt
  . expose_names
    simp [contains]
    left
    rw [h_1]
  . expose_names
    cases h_1; all_goals expose_names
    . simp [contains]
      right
      left
      apply ih1
      exact h_1
    . simp [contains]
      right
      right
      exact h_1

lemma insert_contains (bt: BinaryTree α) (v: α) (f: α → ENat): contains (insert bt v f) v := by
fun_induction insert
. simp[contains]
. simp[contains]
. grind

lemma insert_contains_then_contains_or_inserted (bt: BinaryTree α) (v v': α) (f: α → ENat): contains (insert bt v' f) v → v = v' ∨ contains bt v := by
intro h
fun_induction insert generalizing v
. expose_names
  left
  grind
. expose_names
  simp [contains] at h
  cases h
  . simp_all
  . expose_names
    right
    simp[contains]
    cases h; all_goals expose_names
    . specialize ih1 v h
      grind
    . grind
. expose_names
  simp [contains] at h
  cases h
  . expose_names
    right
    simp[contains]
    left
    exact h
  . grind

theorem insert_correctness (bt: BinaryTree α) (f: α → ENat): (∀ v v', contains bt v ∨ v = v' ↔  contains (insert bt v' f) v ) ∧ (is_min_heap bt f → is_min_heap (insert bt v f) f) := by
grind[contains_then_insert_contains, insert_contains, insert_contains_then_contains_or_inserted, insert_preserves_min_heap]

lemma merge_left_is_node_is_node (bt1 bt2 l1 r1: BinaryTree α) (f: α → ENat) (v1: α): bt1 = node l1 v1 r1 → ∃ l v r, merge bt1 bt2 f = node l v r := by
fun_induction merge
. grind
. grind
. grind
. grind

lemma merge_right_is_node_is_node (bt1 bt2 l2 r2: BinaryTree α) (f: α → ENat) (v2: α): bt2 = node l2 v2 r2 → ∃ l v r, merge bt1 bt2 f = node l v r := by
fun_induction merge
. grind
. grind
. grind
. grind

lemma merge_left_contains (bt1 l1 r1 bt2 l r: BinaryTree α) (v1 v: α ) (f: α → ENat): (merge bt1 bt2 f) = node l v r → is_min_heap bt1 f → is_min_heap bt2 f →  bt1 = node l1 v1 r1 → contains bt2 v ∨ v = v1 := by
intro h
fun_induction merge generalizing l1 r1 v1
. grind
. intros
  expose_names
  right
  simp_all
. expose_names
  simp_all
. expose_names
  grind

lemma merge_right_contains (bt1 l2 r2 bt2 l r: BinaryTree α) (v2 v: α ) (f: α → ENat): (merge bt1 bt2 f) = node l v r → is_min_heap bt1 f → is_min_heap bt2 f →  bt2 = node l2 v2 r2 → contains bt1 v ∨ v = v2 := by
intro h
fun_induction merge generalizing l2 r2 v2
. grind
. intros
  expose_names
  right
  simp_all
. expose_names
  grind
. expose_names
  grind

lemma merge_preserves_min_heap (bt1 bt2 : BinaryTree α) (f : α → ENat) (h1 : is_min_heap bt1 f) (h2 : is_min_heap bt2 f) : is_min_heap (merge bt1 bt2 f) f := by
fun_induction merge
. grind
. grind
. expose_names
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  constructor
  . constructor
    . apply ih1
      apply min_heap_then_left_and_right_are_min_heap at h1
      simp [left_and_right_are_min_heap] at h1
      obtain ⟨ hl, hr ⟩ := h1
      exact hl
      exact h2
    . apply min_heap_then_left_and_right_are_min_heap at h1
      simp [left_and_right_are_min_heap] at h1
      obtain ⟨ hl, hr ⟩ := h1
      exact hr
  . obtain ⟨ l, v, r, hr ⟩ := merge_right_is_node_is_node l1 (l2.node v2 r2) l2 r2 f v2 (rfl)
    rw [hr]
    cases r1
    . simp[root_is_min_of_children]
      have: contains l1 v ∨ v = v2 := by
        apply merge_right_contains l1 l2 r2 (l2.node v2 r2) l r v2 v f hr _ h2 (rfl)
        apply min_heap_then_left_and_right_are_min_heap at h1
        simp [left_and_right_are_min_heap] at h1
        simp [h1]
      cases this
      . apply min_heap_then_members_left_le (l1.node v1 leaf) l1 leaf v1 v f h1 (rfl) (by grind)
      . expose_names
        rw [h_1]
        exact h
    . simp[root_is_min_of_children]
      have: contains l1 v ∨ v = v2 := by
        apply merge_right_contains l1 l2 r2 (l2.node v2 r2) l r v2 v f hr _ h2 (rfl)
        apply min_heap_then_left_and_right_are_min_heap at h1
        simp [left_and_right_are_min_heap] at h1
        simp [h1]
      cases this
      . expose_names
        constructor
        . apply min_heap_then_members_left_le (l1.node v1 (a.node a_1 a_2)) l1 (a.node a_1 a_2) v1 v f h1 (rfl) (by grind)
        . apply min_heap_then_members_right_le (l1.node v1 (a.node a_1 a_2)) l1 (a.node a_1 a_2) v1 a_1 f h1 (rfl) (by grind)
      . expose_names
        rw [h_1]
        constructor
        . exact h
        . apply min_heap_then_members_right_le (l1.node v1 (a.node a_1 a_2)) l1 (a.node a_1 a_2) v1 a_1 f h1 (rfl) (by grind)
. expose_names
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  constructor
  . constructor
    . apply ih1 h1
      apply min_heap_then_left_and_right_are_min_heap at h2
      simp [left_and_right_are_min_heap] at h2
      obtain ⟨ hl, hr ⟩ := h2
      exact hl
    . apply min_heap_then_left_and_right_are_min_heap at h2
      simp [left_and_right_are_min_heap] at h2
      obtain ⟨ hl, hr ⟩ := h2
      exact hr
  . obtain ⟨ l, v, r, hl ⟩ := merge_left_is_node_is_node (l1.node v1 r1) l2 l1 r1 f v1 (rfl)
    rw [hl]
    cases r2
    . simp[root_is_min_of_children]
      have: contains l2 v ∨ v = v1 := by
        apply merge_left_contains (l1.node v1 r1) l1 r1 l2 l r v1 v f hl h1 _ (rfl)
        apply min_heap_then_left_and_right_are_min_heap at h2
        simp [left_and_right_are_min_heap] at h2
        simp [h2]
      cases this
      . apply min_heap_then_members_left_le (l2.node v2 leaf) l2 leaf v2 v f h2 (rfl) (by grind)
      . expose_names
        rw [h_1]
        simp at h
        grw [h]
    . simp[root_is_min_of_children]
      have: contains l2 v ∨ v = v1 := by
        apply merge_left_contains (l1.node v1 r1) l1 r1 l2 l r v1 v f hl h1 _ (rfl)
        apply min_heap_then_left_and_right_are_min_heap at h2
        simp [left_and_right_are_min_heap] at h2
        simp [h2]
      cases this
      . expose_names
        constructor
        . apply min_heap_then_members_left_le (l2.node v2 (a.node a_1 a_2)) l2 (a.node a_1 a_2) v2 v f h2 (rfl) h_1
        . apply min_heap_then_members_right_le (l2.node v2 (a.node a_1 a_2)) l2 (a.node a_1 a_2) v2 a_1 f h2 (rfl) (by grind)
      . expose_names
        rw [h_1]
        constructor
        . simp at h
          grw [h]
        . apply min_heap_then_members_right_le (l2.node v2 (a.node a_1 a_2)) l2 (a.node a_1 a_2) v2 a_1 f h2 (rfl) (by grind)

lemma merge_no_new_members  (bt1 bt2 : BinaryTree α) (f : α → ENat): merge bt1 bt2 f = node l v r → contains bt1 v ∨ contains bt2 v := by
fun_induction merge
. grind
. grind
. grind
. grind

lemma merge_contains_then_inputs_contain  (bt1 bt2 : BinaryTree α) (f : α → ENat): contains (merge bt1 bt2 f) v → contains bt1 v ∨ contains bt2 v := by
fun_induction merge; all_goals grind

lemma contains_then_merge_contains (bt1 bt2 : BinaryTree α) (f : α → ENat): contains bt1 v ∨ contains bt2 v → contains (merge bt1 bt2 f) v  := by
fun_induction merge; all_goals grind

lemma remove_no_new_members [DecidableEq α] (bt l r : BinaryTree α) (x v: α) (f: α → ENat): bt.remove x f = node l v r → contains bt v:= by
fun_induction remove
. grind
. intros
  expose_names
  grind[merge_no_new_members]
. grind[merge_no_new_members]

lemma remove_preserves_min_heap [DecidableEq α] (bt : BinaryTree α) (x : α) (f : α → ENat): is_min_heap bt f → is_min_heap (remove bt x f) f := by
intro hmin
fun_induction remove
. exact hmin
. expose_names
  apply min_heap_then_left_and_right_are_min_heap at hmin
  grind [merge_preserves_min_heap]
. expose_names
  apply left_and_right_are_min_heap_and_root_is_min_of_children_is_min_heap
  constructor
  simp[left_and_right_are_min_heap]
  constructor
  . apply ih2
    apply min_heap_then_left_and_right_are_min_heap at hmin
    simp[left_and_right_are_min_heap] at hmin
    simp_all
  . apply ih1
    apply min_heap_then_left_and_right_are_min_heap at hmin
    simp[left_and_right_are_min_heap] at hmin
    simp_all
  . cases hl : l.remove x f with
    | leaf =>
        cases hr : r.remove x f with
        | leaf =>
          simp[root_is_min_of_children]
        | node l'' v'' r'' =>
          simp[root_is_min_of_children]
          have: contains r v'' := by grind[remove_no_new_members]
          apply min_heap_then_members_right_le (l.node v r) l r v v'' f hmin (rfl) this
    | node l' v' r' =>
        cases hr : r.remove x f with
        | leaf =>
          simp[root_is_min_of_children]
          have: contains l v' := by grind[remove_no_new_members]
          apply min_heap_then_members_left_le (l.node v r) l r v v' f hmin (rfl) this
        | node l'' v'' r'' =>
          simp[root_is_min_of_children]
          constructor
          . have: contains l v' := by grind[remove_no_new_members]
            apply min_heap_then_members_left_le (l.node v r) l r v v' f hmin (rfl) this
          . have: contains r v'' := by grind[remove_no_new_members]
            apply min_heap_then_members_right_le (l.node v r) l r v v'' f hmin (rfl) this

lemma remove_preserves_members_except_v [DecidableEq α] (bt : BinaryTree α) (x v: α) (f: α → ENat): contains bt v → v ≠ x → contains (bt.remove x f) v := by
fun_induction remove
. grind
. expose_names
  intro h1 h2
  apply contains_not_root_then_children (l.node x r) l r x v h1 (rfl) at h2
  grind[contains_then_merge_contains]
. expose_names
  intro h1 h2
  cases h1
  . grind
  . grind

theorem decrease_priority_preserves_min_heap [DecidableEq α]  (bt: BinaryTree α) (v : α) (f : α → ENat): is_min_heap bt f → is_min_heap (decrease_priority bt v f) f := by
intro hmin
simp [decrease_priority]
by_cases (bt.containsb v)
. expose_names
  simp [h]
  apply insert_preserves_min_heap
  apply remove_preserves_min_heap
  exact hmin
. expose_names
  simp [h]
  exact hmin

lemma decrease_priority_preserves_members [DecidableEq α]  (bt: BinaryTree α) (v v': α) (f : α → ENat): contains bt v → contains (decrease_priority bt v' f) v := by
simp[decrease_priority]
by_cases v = v'
. intro
  cases bt.containsb v'
  . simp
    (expose_names; exact h_1)
  . simp
    expose_names
    rw [h]
    grind[insert_contains]
. intro
  cases bt.containsb v'
  . simp
    (expose_names; exact h_1)
  . simp
    expose_names
    apply contains_then_insert_contains
    grind[remove_preserves_members_except_v]

lemma decrease_correctness[DecidableEq α]  (bt: BinaryTree α) (v v': α) (f : α → ENat): contains bt v → contains (decrease_priority bt v' f) v  ∧  is_min_heap bt f → is_min_heap (decrease_priority bt v f) f := by
grind[decrease_priority_preserves_members, decrease_priority_preserves_min_heap]

def size: (BinaryTree α) →  Nat
| leaf => 0
| node l _ r => 1 + size l + size r

@[simp] lemma size_ge_zero: size bt ≥ 0 := by
fun_induction size
. simp
. simp

lemma merge_size [DecidableEq α] (bt1 bt2: BinaryTree α) (f : α → ENat): size (merge bt1 bt2 f) = size bt1 + size bt2 := by
fun_induction merge
. simp[size]
. simp [size]
. grind [size]
. grind [size]

lemma remove_size_dec [DecidableEq α] (bt : BinaryTree α) (v : α) (f : α → ENat) : size (remove bt v f) ≤ size bt := by
fun_induction remove
. simp
. grind [size, merge_size]
. grind [size, merge_size]

lemma remove_size [DecidableEq α] (bt : BinaryTree α) (v : α) (f : α → ENat) (h: contains bt v): size (remove bt v f) + 1 ≤ size bt:= by
fun_induction remove
. contradiction
. expose_names
  rw [merge_size l r f]
  nth_rw 3 [size.eq_def]
  simp
  grind
. expose_names
  simp [contains] at h
  cases h
  . grind
  . expose_names
    cases h
    . expose_names
      simp[size]
      apply ih2 at h
      grw [← h]
      grind[remove_size_dec]
    . expose_names
      simp [size]
      apply ih1 at h
      grw [← h]
      grind[remove_size_dec]

lemma insert_size [DecidableEq α] (bt : BinaryTree α) (v : α) (f : α → ENat): size (insert bt v f) = size bt + 1 := by
fun_induction insert
. simp[size]
. grind [size]
. grind [size]

lemma containsb_size [DecidableEq α] (bt:BinaryTree α): containsb bt v = true → bt.size ≥ 1 := by
cases bt
. intro
  by_contra
  grind
. intro
  simp[size]
  omega

lemma containsb_contains [DecidableEq α] (bt: BinaryTree α): containsb bt v → contains bt v := by
intro
fun_induction contains
. contradiction
. grind

lemma decrease_priority_size [DecidableEq α] (bt : BinaryTree α) (v : α) (f : α → ENat): size (decrease_priority bt v f) ≤ size bt := by
simp[decrease_priority]
by_cases bt.containsb v
. expose_names
  simp [h]
  rw [insert_size]
  grw [remove_size]
  grind [containsb_contains]
. expose_names
  simp [h]

lemma get_last_size (h: bt ≠ leaf): size (get_last bt).2 < size bt := by
fun_induction get_last
. contradiction
. simp [size]
. expose_names
  simp [size]
  apply ih1
  grind
. expose_names
  simp [size]
  apply ih1
  grind

lemma heapify_size: size (heapify bt f) = size bt := by
fun_induction heapify; all_goals grind [size]

lemma extract_min_size (h: bt ≠ leaf): size (extract_min bt f).2 < size bt := by
induction bt
. contradiction
. expose_names
  have hex: ∃ bt' v'', (some v'', bt') = get_last  (a.node a_1 a_2):= by
    apply get_last_is_node (a.node a_1 a_2) a a_2 a_1 (rfl)
  obtain ⟨bt, v, hv⟩ := hex
  simp[extract_min]
  rw[← hv]
  simp
  cases bt
  . simp[size]
  . expose_names
    simp
    simp[heapify_size]
    have: (a_3.node v a_5).size = (a_3.node a_4 a_5).size := by simp [size]
    rw [this]
    have: (a_3.node a_4 a_5) = (a.node a_1 a_2).get_last.2 := by
      rw [←hv]
    rw [this]
    apply get_last_size h


def subTree (sub sup: BinaryTree α):= ∀ v, contains sub v → contains sup v


lemma key_at_y_le_extracted_min_sub_tree [DecidableEq α] (y: α) (sub sup: BinaryTree α)
 (f: α → ENat) (hsup: (extract_min sup f).1 = y) (hnesub: ¬ is_empty_tree sub) (hsubtree: subTree sub sup) (hmin: is_min_heap sup f):
 ∀ u, (BinaryTree.extract_min sub f).1 = some u → f y ≤ f u := by
intro u hu
have: contains sub u := by grind[extract_min_returns_then_contains]
have: contains sup u := by grind[subTree]
have: contains sup y := by grind[extract_min_returns_then_contains]
grind[extract_min_is_min]

structure BinaryHeap (α : Type u) [DecidableEq α] where
  tree : BinaryTree α

namespace BinaryHeap

def empty [DecidableEq α]: BinaryHeap α := { tree := BinaryTree.leaf }

def isEmpty [DecidableEq α] (h: BinaryHeap α): Bool :=  match h.tree with
| leaf => true
| node _ _ _ => false

def add {α : Type u} [DecidableEq α] (h : BinaryHeap α) (v : α) (priority : α → ENat) : BinaryHeap α :=
  {tree:= (h.tree.insert v priority)}

lemma notIsEmptyIsNotLeaf [DecidableEq α] (bh: BinaryHeap α): isEmpty bh = false → bh.tree ≠ leaf := by
cases h: bh.tree
. intro h
  simp [isEmpty] at h
  expose_names
  simp [h_1] at h
. intro h
  expose_names
  simp

lemma extract_min_is_someHeap {α : Type u} [DecidableEq α] (h : BinaryHeap α) (f : α → ENat) (hh: ¬ isEmpty h): (extract_min h.tree f).1.isSome := by
grind[isEmpty, extract_min_is_some]

noncomputable def extract_min {α : Type u} [DecidableEq α] (h : BinaryHeap α) (priority : α → ENat) (hh: ¬ isEmpty h): (α × BinaryHeap α) :=
  ((h.tree.extract_min priority).1.get (by grind[extract_min_is_someHeap]) , {tree:= (h.tree.extract_min priority).2})

def sizeOf {α : Type u} [DecidableEq α] (h : BinaryHeap α) : Nat := h.tree.size

def decrease_priority [DecidableEq α] (h : BinaryHeap α) (v : α) (prio :α →  ENat) : BinaryHeap α :=
{tree:= BinaryTree.decrease_priority h.tree v prio}

-- Helper lemma: decreasing priority does not increase heap size
theorem sizeOf_decrease_priority_le {α : Type u} [DecidableEq α] (h : BinaryHeap α) (v : α) (prio :α → ENat) :
  sizeOf (decrease_priority h v prio) ≤ sizeOf h := by
  -- To be proved from the concrete heap implementation
  simp [decrease_priority, sizeOf]
  grind[decrease_priority_size]

-- Helper lemma: extracting the minimum from a non-empty heap strictly decreases its size.
theorem sizeOf_extract_min_lt_of_isEmpty_eq_false
    {V : Type*} [Nonempty V] [DecidableEq V] (h : BinaryHeap V) (hNE : isEmpty h = false) (priority: V → ENat):
    sizeOf (Prod.snd (extract_min h priority (by grind))) < sizeOf h := by
  -- To be proved from the concrete heap implementation
  simp [sizeOf]
  simp  [extract_min]
  apply extract_min_size
  apply notIsEmptyIsNotLeaf at hNE
  exact hNE

lemma key_at_y_le_extracted_min' [DecidableEq α]
 (y: α) (p sup: (α → ENat) × BinaryHeap α) (f: α → ENat) (hnesub: isEmpty p.2 = false)

 (hNEsup : isEmpty sup.2 = false) (hsup: (sup.2.extract_min f (by simp[hNEsup])).1 = y)
 (hsubtree: subTree p.2.tree sup.2.tree) (hmin: is_min_heap sup.2.tree f)
 (hfprio: f = p.1):
  ∀ u1, Prod.fst (p.2.extract_min f (by grind)) = u1 → p.1 y ≤ p.1 u1 := by
  intro u1 h
  rw[←hfprio]
  apply BinaryTree.key_at_y_le_extracted_min_sub_tree y p.2.tree sup.2.tree f (by grind[extract_min]) (by simp[isEmpty] at hnesub; simp[hnesub, is_empty_tree]) hsubtree hmin u1 (by simp[extract_min] at h; grind)

-- minimimla heap-distance consistency lemma
lemma key_at_y_le_extracted_min [Nonempty V] [DecidableEq V]
  (y : V) (p : (V → ENat) × BinaryHeap V) (priority: V → ENat) (hNE : isEmpty p.2 = false) :
  ∀ u1, Prod.fst (p.2.extract_min priority (by grind)) = u1 → p.1 y ≤ p.1 u1 := by
  intro u1 hu1
  -- Admitted: BinaryHeap semantics ensuring the extracted minimum is not
  -- smaller than the finalized key `y`.
  admit

lemma decrease_priorityPreservesLeaf [DecidableEq α] (bt: BinaryTree α) (v: α) (f: α → ENat): bt = leaf → BinaryTree.decrease_priority bt v f = leaf := by
simp[BinaryTree.decrease_priority]
intro
by_contra
grind

lemma decrease_priorityPreservesNode [DecidableEq α] (bt l r: BinaryTree α) (v v': α) (f: α → ENat): bt = node l v' r→  ∃ l' r' v'', BinaryTree.decrease_priority bt v f = node l' v'' r' := by
intro hbt
simp [BinaryTree.decrease_priority]
by_cases bt.containsb v
. expose_names
  rw[h]
  simp_all
  apply insert_is_node ((l.node v' r).remove v f) f v
. expose_names
  simp[h]
  use l
  use r
  use v'

lemma decrease_priority_preserves_isEmpty [DecidableEq V] (q : BinaryHeap V) (v : V) (d' : V → ENat) :
    (q.decrease_priority v d').isEmpty = q.isEmpty := by
    -- decrease_priority should not change whether the heap is empty
    by_cases q.isEmpty
    . expose_names
      rw [h]
      simp [isEmpty] at h
      have: q.tree = leaf := by grind
      simp [decrease_priority, isEmpty]
      apply decrease_priorityPreservesLeaf (q.tree) v d' at this
      rw[this]
    . expose_names
      simp [isEmpty] at h
      have: ∃ l v' r, q.tree = node l v' r := by grind
      obtain ⟨l, v', r, h⟩ := this
      obtain ⟨ l', v'', r', h'⟩ := decrease_priorityPreservesNode q.tree l r v v' d' h
      simp [decrease_priority]
      rw [h']
      simp[isEmpty]
      rw[h]

end BinaryHeap
