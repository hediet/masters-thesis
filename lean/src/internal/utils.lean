
import tactic
import data.finset

@[simp]
lemma to_finset_append { α: Type } [decidable_eq α] { l1: list α } { l2: list α }:
    (l1 ++ l2).to_finset = l1.to_finset ∪ l2.to_finset :=
begin
    induction l1;
    finish,
end

lemma subset_right_union { α: Type } [decidable_eq α] { u v w: finset α } (h: u ⊆ v): u ⊆ v ∪ w :=
begin
    have : ∅ ⊆ w := by simp,
    have := finset.union_subset_union h this,
    finish [this],
end

lemma subset_union_right_subset { α: Type } [decidable_eq α] { u v w: finset α } (h: u ∪ v ⊆ w): u ⊆ w :=
begin
    rw finset.subset_iff,
    assume x,
    rw finset.subset_iff at h,
    assume h',
    simp [h', h],
end

@[simp]
lemma list_subset_empty_set { α: Type } [decidable_eq α] { l: list α }: l.to_finset ⊆ ∅ ↔ l = list.nil :=
begin
    -- TODO improve this lemma
    cases l,
    simp,
    simp,
    rw finset.insert_eq,
    by_contra,
    replace a := subset_union_right_subset a,
    finish,
end

lemma subset_subset_insert { α: Type } [decidable_eq α] { u v: finset α } (h: u ⊆ v) (a: α) : u ⊆ insert a v :=
    finset.subset.trans h (finset.subset_insert a v)

lemma sublist_subset { α: Type } [decidable_eq α] { u v: list α } (h: u <+ v): u.to_finset ⊆ v.to_finset :=
begin
    replace h := list.sublist.subset h,
    rw finset.subset_iff,
    assume x,
    assume h',
    replace h' := list.mem_to_finset.mp h',
    exact list.mem_to_finset.mpr (h h'),
end