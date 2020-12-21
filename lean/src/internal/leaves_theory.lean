
import tactic
import ..definitions
import .helper_defs
import data.finset

variable [GuardModule]
open GuardModule

@[simp]
lemma map_leaves_id { α β: Type } (ant: Ant α) (f: α → β): (ant.map f).leaves = ant.leaves :=
begin
    induction ant;
    finish [Ant.leaves, Ant.map],
end

@[simp]
lemma gdt_leaves_eq_ant_leaves { gdt: Gdt }: (A gdt).leaves = gdt.leaves :=
begin
    induction gdt,
    case Gdt.leaf { finish, },
    case Gdt.branch { finish [Gdt.leaves, Ant.leaves, A, Ant.map], },
    case Gdt.grd {
        cases gdt_grd;
        finish [Gdt.leaves, Ant.leaves, A, Ant.map],
    },
end

@[simp]
lemma gdt_remove_leaves_empty_set { gdt: Gdt }: gdt.remove_leaves ∅ = some gdt :=
begin
    induction gdt;
    finish [Gdt.remove_leaves],
end

lemma gdt_remove_leaves_intersect (gdt: Gdt) (ls: finset Leaf): gdt.remove_leaves ls = gdt.remove_leaves (ls ∩ gdt.leaves) :=
begin
    induction gdt with leaf generalizing ls,
    case Gdt.leaf {
        by_cases leaf ∈ ls;
        simp [Gdt.remove_leaves, h, Gdt.leaves],
    },
    case Gdt.branch {
        conv in (Gdt.remove_leaves (ls ∩ (gdt_tr1.branch gdt_tr2).leaves) (gdt_tr1.branch gdt_tr2)) {
            rw Gdt.remove_leaves,
            rw Gdt.leaves,
            rw gdt_ih_tr1,
            rw gdt_ih_tr2,
        },
        simp [Gdt.remove_leaves, Gdt.leaves, gdt_ih_tr1, gdt_ih_tr2],
    },
    case Gdt.grd {
        finish [Gdt.leaves, Gdt.remove_leaves],
    },
end
