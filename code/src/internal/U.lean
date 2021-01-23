import tactic
import ..definitions
import .internal_definitions
import .Gdt.eval
import .phi.eval
import .phi.utils
import .result

variable [GuardModule]
open GuardModule

lemma U_eq_𝒰_acc { gdt: Gdt } { acc: Φ → Φ } (acc_stable: stable acc) (acc_hom: hom acc) : (acc (U gdt)).eval = (𝒰_acc acc gdt).eval :=
begin
    induction gdt generalizing acc,
    case Gdt.rhs {
        simp [𝒰_acc, U],
    },
    case Gdt.branch {
        have : (𝒰_acc id gdt_tr1).eval = (id (U gdt_tr1)).eval :=
        by simp [←gdt_ih_tr1, stable.id, hom.id],

        have : ((𝒰_acc id gdt_tr1).and (U gdt_tr2)).eval = ((id (U gdt_tr1)).and (U gdt_tr2)).eval :=
        by rw stable.app stable.and_left this,

        simp [𝒰_acc, U, ←gdt_ih_tr2 (stable.comp acc_stable stable.and_right) (hom.comp acc_hom acc_stable hom.and_right stable.and_right),
            function.comp, stable.app acc_stable this],
    },
    case Gdt.grd {
        cases gdt_grd,
        case Grd.xgrd {
            ext env,
            unfold 𝒰_acc U,
            rw (acc_hom _ _).1,

            have : (𝒰_acc (acc ∘ Φ.xgrd_in gdt_grd) gdt_tr).eval = (acc (Φ.xgrd_in gdt_grd (U gdt_tr))).eval :=
            by simp [←gdt_ih (stable.comp acc_stable (stable.xgrd_in _))
                    (hom.comp acc_hom acc_stable (hom.xgrd_in gdt_grd) (stable.xgrd_in gdt_grd))],

            rw stable.app stable.or_right this,
        },
        case Grd.bang {
            simp [𝒰_acc, U, ←gdt_ih (stable.comp acc_stable stable.and_right) (hom.comp acc_hom acc_stable hom.and_right stable.and_right)],
        },
    },
end

lemma U_eq_𝒰 { gdt: Gdt } : (U gdt).eval = (𝒰 gdt).eval :=
by ext env; simp [𝒰, ←U_eq_𝒰_acc (stable.id) (hom.id)]

@[simp]
theorem U_semantic { gdt: Gdt } { env: Env }:
    (U gdt).eval env = !(gdt.eval env).is_match :=
begin
    induction gdt with rhs generalizing env,

    case Gdt.rhs { refl, },
    case Gdt.branch {
        simp [U, *, @gdt_ih_tr1 env, @gdt_ih_tr2 env, ←bool.coe_bool_iff],
    },
    case Gdt.grd {
        rw ←bool.coe_bool_iff,
        cases gdt_grd with xgrd var,
        case Grd.xgrd {
            cases c: (xgrd_eval xgrd env) with env',
            { simp [Gdt.eval_xgrd_of_none c, U, Φ_eval_not_xgrd_none c], },
            { simp [Gdt.eval_xgrd_of_some c, U, Φ_eval_not_xgrd_some c, Φ_eval_xgrd_some c, @gdt_ih env'], },
        },
        case Grd.bang {
            cases c: is_bottom var env,
            { simp [Gdt.eval_bang_of_not_bottom c, U, c, @gdt_ih env], },
            { simp [Gdt.eval_bang_of_bottom c, U, c], },
        },
    },
end
