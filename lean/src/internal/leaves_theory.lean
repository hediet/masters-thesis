
import tactic
import ..definitions
import data.finset

variable [GuardModule]
open GuardModule



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