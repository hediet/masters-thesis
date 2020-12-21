import tactic
import ..definitions
import .helper_defs
import .gdt_eval
import .phi_eval

variable [GuardModule]
open GuardModule

@[simp]
theorem U_semantic { gdt: Gdt } { env: Env }:
    (U gdt).eval env = !(gdt.eval env).is_match :=
begin
    rw ←bool.coe_bool_iff,
    
    induction gdt with leaf generalizing env,

    case Gdt.leaf { finish, },
    case Gdt.branch { finish [U, Φ.eval], },
    case Gdt.grd {
        cases gdt_grd with xgrd var,
        case Grd.xgrd {
            cases c: (xgrd_eval xgrd env) with env',
            { simp [grd_eval_xgrd_none c, U, Φ_eval_not_xgrd_none c], },
            { simp [grd_eval_xgrd_some c, U, Φ_eval_not_xgrd_some c, Φ_eval_xgrd_some c, @gdt_ih env'], },
        },
        case Grd.bang {
            cases c: is_bottom var env,
            { simp [grd_eval_bang_not_bottom c, U, c, @gdt_ih env], },
            { simp [grd_eval_bang_bottom c, U, c], },
        },
    },
end
