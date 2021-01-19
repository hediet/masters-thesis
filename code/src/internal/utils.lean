import tactic
import data.finset

lemma subset_right_union { α: Type } [decidable_eq α] { u v w: finset α } (h: u ⊆ v): u ⊆ v ∪ w :=
begin
    have : ∅ ⊆ w := by simp,
    have := finset.union_subset_union h this,
    finish [this],
end

lemma subset_left_union { α: Type } [decidable_eq α] { u v w: finset α } (h: u ⊆ w): u ⊆ v ∪ w :=
begin
    have : ∅ ⊆ v := by simp,
    have := finset.union_subset_union this h,
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

lemma subset_inter_subset { α: Type } [decidable_eq α] { s1 s2 s3: finset α }: s1 ⊆ s3 → s1 ∩ s2 ⊆ s3 :=
begin
    refine finset.subset.trans _,
    exact finset.inter_subset_left s1 s2,
end

lemma subset_inter_subset_subset { α: Type } [decidable_eq α] { s1 s2 s3: finset α } (h: s1 ⊆ s2): s1 ∩ s2 ⊆ s3 ↔ s1 ⊆ s3 :=
begin
    split, {
        refine finset.subset.trans _,
        refine finset.subset_inter _ h,
        exact finset.subset.refl s1,
    }, {
        exact subset_inter_subset,
    },
end

lemma not_subset { α: Type } { u v: finset α }: ¬ u ⊆ v ↔ ∃ x ∈ u, ¬ x ∈ v :=
begin
    exact not_ball
end

lemma list_to_finset_disjoint_iff_list_disjoint { α: Type } [decidable_eq α] (list1 list2: list α ): disjoint list1.to_finset list2.to_finset ↔ list1.disjoint list2 :=
begin
    rw list.disjoint,
    rw finset.disjoint_iff_inter_eq_empty,
    rw finset.ext_iff,
    split; {
        assume h a,
        specialize @h a,
        finish,
    },
end

lemma disjoint_set_union_eq_union_iff_right { α: Type } [decidable_eq α] (a: finset α) { b c: finset α } (h1: disjoint a b) (h2: disjoint a c): a ∪ b = a ∪ c ↔ b = c :=
begin
    split, {
        assume x,
        rw finset.ext_iff,
        assume e,
        rw finset.ext_iff at x,
        specialize x e,

        rw finset.disjoint_iff_inter_eq_empty at h1,
        rw finset.ext_iff at h1,
        specialize h1 e,

        rw finset.disjoint_iff_inter_eq_empty at h2,
        rw finset.ext_iff at h2,
        specialize h2 e,

        simp * at *,
        finish,
    }, {
        assume x,
        simp [x],
    }
end

lemma disjoint_set_union_eq_union_iff_left { α: Type } [decidable_eq α] (a: finset α) { b c: finset α } (h1: disjoint b a) (h2: disjoint c a): b ∪ a = c ∪ a ↔ b = c :=
begin
    have := disjoint_set_union_eq_union_iff_right a (disjoint.comm.1 h1) (disjoint.comm.1 h2),
    simp only [this, finset.union_comm],
end

lemma disjoint_sets { α: Type } [decidable_eq α] { a₁ a₂ b₁ b₂: finset α } (h: disjoint b₁ b₂) (h₁: a₁ ⊆ b₁) (h₂: a₂ ⊆ b₂):
    (b₁ ∪ b₂) \ (a₁ ∪ a₂) = (b₁ \ a₁) ∪ (b₂ \ a₂) :=
begin
    rw finset.subset_iff at h₁,
    rw finset.subset_iff at h₂,
    rw finset.ext_iff,
    assume a,
    specialize @h₁ a,
    specialize @h₂ a,
    rw finset.disjoint_iff_inter_eq_empty at h,
    rw finset.ext_iff at h,
    specialize @h a,
    
    finish,
end

@[simp]
lemma list_to_finset_append { α: Type } [decidable_eq α] { l1: list α } { l2: list α }:
    (l1 ++ l2).to_finset = l1.to_finset ∪ l2.to_finset :=
begin
    induction l1;
    finish,
end

@[simp]
lemma list_to_finset_subset_empty_set { α: Type } [decidable_eq α] { l: list α }: l.to_finset ⊆ ∅ ↔ l = list.nil :=
begin
    split; assume h, {
        cases l;
        finish [finset.subset_empty, finset.insert_ne_empty],
    }, { simp [h], }
end

@[simp]
lemma list_coe_to_finset_eq_list_to_finset { α: Type } [decidable_eq α] (list: list α): (list: multiset α).to_finset = list.to_finset :=
begin
    rw finset.ext_iff,
    assume a,
    simp,
end

lemma list_to_finset_eq_of_perm { α: Type } [decidable_eq α] { list1 list2: list α } (h: list1 ~ list2):
    list1.to_finset = list2.to_finset :=
begin
    have : (list1: multiset α).to_finset = (list2: multiset α).to_finset :=
    by simp [multiset.coe_eq_coe.2 h],
    revert this,
    simp only [list_coe_to_finset_eq_list_to_finset, imp_self],
end
