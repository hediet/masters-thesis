import tactic
import data.finset
import .mark_all_rhss_inactive
import .eval
import .eval_option
import ..utils

variable [GuardModule]
open GuardModule

lemma Gdt.remove_rhss_branch { rhss: finset Rhs } { gdt₁ gdt₂: Gdt }:
    (gdt₁.branch gdt₂).remove_rhss rhss ≠ none ↔
         gdt₁.remove_rhss rhss ≠ none ∨
         gdt₂.remove_rhss rhss ≠ none :=
begin
    unfold Gdt.remove_rhss,
    cases gdt₁.remove_rhss rhss;
    cases gdt₂.remove_rhss rhss;
    simp [Gdt.branch_option],
end

lemma Gdt.grd_option_neq_none { gdt: option Gdt } { grd: Grd }: Gdt.grd_option grd gdt ≠ none ↔ gdt ≠ none :=
begin
    cases gdt;
    simp [Gdt.grd_option],
end

lemma Gdt.remove_rhss_neq_none { rhss: finset Rhs } { gdt: Gdt } (h: ∃ l ∈ gdt.rhss, l ∉ rhss): (Gdt.remove_rhss rhss gdt) ≠ none :=
begin
    induction gdt with rhs,
    case Gdt.rhs {
        simp only [Gdt.rhss, exists_prop, exists_eq_left, finset.mem_singleton] at h,
        simp [Gdt.remove_rhss, h],
    },
    case Gdt.branch {
        simp only [Gdt.rhss, exists_prop, finset.mem_union] at h,

        rw Gdt.remove_rhss_branch,
        cases h with l h,
        cases h.1 with l_mem, {
            have : (∃ (l : Rhs) (H : l ∈ gdt_tr1.rhss), l ∉ rhss), {
                use l,
                simp *,
            },
            simp [gdt_ih_tr1 this],
        }, {
            have : (∃ (l : Rhs) (H : l ∈ gdt_tr2.rhss), l ∉ rhss), {
                use l,
                simp *,
            },
            simp [gdt_ih_tr2 this],
        },
    },
    case Gdt.grd {
        unfold Gdt.remove_rhss,
        rw Gdt.rhss at h,
        rw Gdt.grd_option_neq_none,
        simp [gdt_ih h],
    }
end
