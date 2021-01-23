import tactic
import data.finset
import ..definitions
import .internal_definitions
import .Ant.rhss
import .utils

variable [GuardModule]
open GuardModule

@[simp]
lemma R_empty (tr: Ant bool) : R (Ant.diverge tt tr) = R tr :=
begin
    cases c1: R tr,
    cases c2: acc;
    cases c3: inacc;
    cases c4: red;
    simp [R, R._match_1, c1, c2, c3, c4],
end

lemma R_diverge_cases (ant: Ant bool) (a: bool):
    (∃ rh: Rhs, ∃ rs: list Rhs, a = ff ∧ R ant = ⟨ [], [], rh::rs ⟩ ∧ R (Ant.diverge a ant) = ⟨ [], [rh], rs ⟩)
    ∨ ((a = tt ∨ (R ant).acc ≠ [] ∨ (R ant).inacc ≠ [] ∨ (R ant).red = []) ∧ R (Ant.diverge a ant) = R ant) :=
begin
    unfold R Ant.map,
    
    cases a;
    cases R ant;
    cases acc;
    cases inacc;
    cases red;
    simp [R._match_1],
end

lemma R_branch_rhss_perm (tr1 tr2: Ant bool) : (R (tr1.branch tr2)).rhss ~ (R tr1).rhss ++ (R tr2).rhss :=
by simp only [RhsPartition.rhss, R, ←multiset.coe_eq_coe, ←multiset.coe_add, add_left_comm, add_comm]

lemma R_rhss_perm { ant: Ant bool }:
    (R ant).rhss ~ ant.rhss_list :=
begin
    induction ant,
    case Ant.rhs { cases ant_a; simp [R, RhsPartition.rhss, Ant.rhss_list], },
    case Ant.branch {
        unfold Ant.rhss_list,
        apply list.perm.trans (R_branch_rhss_perm ant_tr1 ant_tr2),
        apply list.perm.append;
        simp *,
    },
    case Ant.diverge {
        R_diverge_cases, {
            inline R_ant_tr,
            revert ant_ih,
            simp [RhsPartition.rhss, Ant.rhss_list],
        }, {
            simp [Ant.rhss_list, *],
        },
    }
end

lemma R_rhss_to_finset_eq_rhss { ant: Ant bool }: (R ant).rhss.to_finset = ant.rhss :=
list_to_finset_eq_of_perm R_rhss_perm

lemma R_rhss_to_finset_subset_rhss { ant: Ant bool }: (R ant).rhss.to_finset ⊆ ant.rhss :=
finset.subset_of_eq R_rhss_to_finset_eq_rhss

lemma R_acc_subset_rhss { ant: Ant bool }: (R ant).acc.to_finset ⊆ ant.rhss :=
by apply finset.subset.trans _ R_rhss_to_finset_subset_rhss; finish [finset.subset_iff, RhsPartition.rhss]

lemma R_inacc_subset_rhss { ant: Ant bool }: (R ant).inacc.to_finset ⊆ ant.rhss :=
by apply finset.subset.trans _ R_rhss_to_finset_subset_rhss; finish [finset.subset_iff, RhsPartition.rhss]

lemma R_red_subset_rhss { ant: Ant bool }: (R ant).red.to_finset ⊆ ant.rhss :=
by apply finset.subset.trans _ R_rhss_to_finset_subset_rhss; finish [finset.subset_iff, RhsPartition.rhss]

lemma R_rhss_nodup { ant: Ant bool } (ant_disjoint: ant.disjoint_rhss): (R ant).rhss.nodup :=
(list.perm.nodup_iff R_rhss_perm).2 (Ant.rhss_list.nodup ant_disjoint)

lemma R_red_nodup { ant: Ant bool } (ant_disjoint: ant.disjoint_rhss): (R ant).red.nodup :=
list.nodup_of_nodup_append_right (R_rhss_nodup ant_disjoint)

lemma R_acc_nodup { ant: Ant bool } (ant_disjoint: ant.disjoint_rhss): (R ant).acc.nodup :=
list.nodup_of_nodup_append_left (list.nodup_of_nodup_append_left (R_rhss_nodup ant_disjoint))

lemma R_red_l_not_mem_ls { ant: Ant bool } (ant_disjoint: ant.disjoint_rhss) { l: Rhs } { ls: list Rhs } (h: (R ant).red = l::ls):
    l ∉ ls.to_finset :=
begin
    have := R_red_nodup ant_disjoint,
    inline h,
    simp [list.not_mem_of_nodup_cons this],
end

lemma R_acc_l_not_mem_red { ant: Ant bool } (ant_disjoint: ant.disjoint_rhss) { l: Rhs } { ls: list Rhs } (h: (R ant).acc = l::ls):
    l ∉ (R ant).red.to_finset :=
begin
    have := R_rhss_nodup ant_disjoint,
    unfold RhsPartition.rhss at this,
    have d := list.disjoint_of_nodup_append this,
    have : l ∈ ((R ant).acc ++ (R ant).inacc) := by simp [h],
    suffices : l ∉ (R ant).red, { simp [this], },
    exact imp_false.mp (@d l this),
end

lemma R_inacc_l_not_mem_red { ant: Ant bool } (ant_disjoint: ant.disjoint_rhss) { l: Rhs } { ls: list Rhs } (h: (R ant).inacc = l::ls):
    l ∉ (R ant).red.to_finset :=
begin
    have := R_rhss_nodup ant_disjoint,
    unfold RhsPartition.rhss at this,
    have d := list.disjoint_of_nodup_append this,
    have : l ∈ ((R ant).acc ++ (R ant).inacc) := by simp [h],
    suffices : l ∉ (R ant).red, { simp [this], },
    exact imp_false.mp (@d l this),
end

lemma R_eq_ℛ (can_prove_empty: Φ → bool) (ant: Ant Φ): (R (ant.map can_prove_empty)).to_triple = ℛ can_prove_empty ant :=
begin
    induction ant,
    case Ant.rhs {
        cases c: can_prove_empty ant_a;
        simp [R, R._match_1, ℛ, ℛ._match_1, Ant.map, ℛ._match_2, RhsPartition.to_triple, c],
    },
    case Ant.branch {
        rw ℛ,
        rw ←ant_ih_tr1,
        rw ←ant_ih_tr2,
        cases ℛ can_prove_empty ant_tr1 with a1 ir1;
        cases ir1 with i1 r1;
        cases ℛ can_prove_empty ant_tr2 with a2 ir2;
        cases ir2 with i2 r2;
        simp [R, R._match_1, ℛ, ℛ._match_1, Ant.map, ℛ._match_2, RhsPartition.to_triple],
    },
    case Ant.diverge {
        rw ℛ,
        rw ←ant_ih,
        cases c1: can_prove_empty ant_a;
        cases c: (R (Ant.map can_prove_empty ant_tr));
        cases acc;
        cases inacc;
        cases red;
        simp [R, R._match_1, ℛ, ℛ._match_1, Ant.map, ℛ._match_2, RhsPartition.to_triple, c1, c],
    },
end
