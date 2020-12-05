import tactic
import .a_eval_theorem
import .defs
import .helper_defs
import data.finset

variable [GuardModule]
open GuardModule
variable [decidable_eq Leaf]

def gdt_leaves: Gdt → finset Leaf
| (Gdt.leaf leaf) := { leaf }
| (Gdt.branch tr1 tr2) := gdt_leaves tr1 ∪ gdt_leaves tr2
| (Gdt.grd grd tr) := gdt_leaves tr

def ant_leaves { α: Type }: Ant α → finset Leaf
| (Ant.leaf a leaf) := { leaf }
| (Ant.branch tr1 tr2) := ant_leaves tr1 ∪ ant_leaves tr2
| (Ant.diverge a tr) := ant_leaves tr

def disjoint_leaves: Gdt → Prop
| (Gdt.leaf leaf) := tt
| (Gdt.branch tr1 tr2) := disjoint_leaves tr1 ∧ disjoint_leaves tr2 ∧ disjoint (gdt_leaves tr1) (gdt_leaves tr2)
| (Gdt.grd grd tr) := disjoint_leaves tr

@[simp]
lemma map_leaves_id { α: Type } { β: Type } (ant: Ant α) (f: α → β): ant_leaves (map_ant f ant) = ant_leaves ant :=
begin
    induction ant;
    finish [ant_leaves, map_ant],
end

lemma gdt_leaves_eq_ant_leaves (gdt: Gdt): ant_leaves (𝒜' gdt) = gdt_leaves gdt :=
begin
    induction gdt,
    case Gdt.leaf { finish, },
    case Gdt.branch { finish [gdt_leaves, ant_leaves, 𝒜', map_ant], },
    case Gdt.grd {
        cases gdt_grd;
        finish [gdt_leaves, ant_leaves, 𝒜', map_ant],
    },
end


lemma to_finset_append { α: Type } [decidable_eq α] { l1: list α } { l2: list α } : (l1 ++ l2).to_finset = l1.to_finset ∪ l2.to_finset :=
begin
    induction l1;
    finish,
end


lemma gdt_remove_leaves_empty_set (gdt: Gdt): gdt_remove_leaves ∅ gdt = some gdt :=
begin
    induction gdt;
    finish [gdt_remove_leaves],
end

lemma gdt_remove_leaves_intersect (gdt: Gdt) (ls: finset Leaf): gdt_remove_leaves ls gdt = gdt_remove_leaves (ls ∩ gdt_leaves gdt) gdt :=
begin
    induction gdt with leaf generalizing ls,
    case Gdt.leaf {
        by_cases leaf ∈ ls;
        simp [gdt_remove_leaves, h, gdt_leaves],
    },
    case Gdt.branch {
        conv in (gdt_remove_leaves (ls ∩ gdt_leaves (gdt_tr1.branch gdt_tr2)) (gdt_tr1.branch gdt_tr2)) {
            rw gdt_remove_leaves,
            rw gdt_leaves,
            rw gdt_ih_tr1,
            rw gdt_ih_tr2,
        },
        simp [gdt_remove_leaves,gdt_leaves, gdt_ih_tr1, gdt_ih_tr2],
    },
    case Gdt.grd {
        finish [gdt_leaves, gdt_remove_leaves],
    }
end
