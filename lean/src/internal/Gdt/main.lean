import tactic
import data.finset
import .mark_all_leaves_inactive
import .eval
import .eval_option
import ..utils

variable [GuardModule]
open GuardModule

lemma Gdt.remove_leaves_branch { leaves: finset Leaf } { gdt₁ gdt₂: Gdt }:
    (gdt₁.branch gdt₂).remove_leaves leaves ≠ none ↔
         gdt₁.remove_leaves leaves ≠ none ∨
         gdt₂.remove_leaves leaves ≠ none :=
begin
    unfold Gdt.remove_leaves,
    cases gdt₁.remove_leaves leaves;
    cases gdt₂.remove_leaves leaves;
    simp [Gdt.branch_option],
end

lemma Gdt.grd_option_neq_none { gdt: option Gdt } { grd: Grd }: Gdt.grd_option grd gdt ≠ none ↔ gdt ≠ none :=
begin
    cases gdt;
    simp [Gdt.grd_option],
end

lemma Gdt.remove_leaves_neq_none { leaves: finset Leaf } { gdt: Gdt } (h: ∃ l ∈ gdt.leaves, l ∉ leaves): (Gdt.remove_leaves leaves gdt) ≠ none :=
begin
    induction gdt with leaf,
    case Gdt.leaf {
        simp only [Gdt.leaves, exists_prop, exists_eq_left, finset.mem_singleton] at h,
        simp [Gdt.remove_leaves, h],
    },
    case Gdt.branch {
        simp only [Gdt.leaves, exists_prop, finset.mem_union] at h,

        rw Gdt.remove_leaves_branch,
        cases h with l h,
        cases h.1 with l_mem, {
            have : (∃ (l : Leaf) (H : l ∈ gdt_tr1.leaves), l ∉ leaves), {
                use l,
                simp *,
            },
            simp [gdt_ih_tr1 this],
        }, {
            have : (∃ (l : Leaf) (H : l ∈ gdt_tr2.leaves), l ∉ leaves), {
                use l,
                simp *,
            },
            simp [gdt_ih_tr2 this],
        },
    },
    case Gdt.grd {
        unfold Gdt.remove_leaves,
        rw Gdt.leaves at h,
        rw Gdt.grd_option_neq_none,
        simp [gdt_ih h],
    }
end
