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
        have : (𝒰_acc acc gdt_tr1).eval = (acc (U gdt_tr1)).eval :=
        by simp [←gdt_ih_tr1, acc_stable, acc_hom],

        have : ((𝒰_acc acc gdt_tr1).and (acc (U gdt_tr2))).eval = ((acc (U gdt_tr1)).and (acc (U gdt_tr2))).eval :=
        by rw stable.app stable.and_left this,

        simp [𝒰_acc, U, this, ←acc_hom _ _,
            ←gdt_ih_tr2 (stable.comp stable.and_right acc_stable) (hom.comp hom.and_right stable.and_right acc_hom acc_stable)],
    },
    case Gdt.grd {
        cases gdt_grd,
        case Grd.tgrd {
            ext env,
            unfold 𝒰_acc U,
            rw (acc_hom _ _).1,

            have : (𝒰_acc (acc ∘ Φ.tgrd_in gdt_grd) gdt_tr).eval = (acc (Φ.tgrd_in gdt_grd (U gdt_tr))).eval :=
            by simp [←gdt_ih (stable.comp acc_stable (stable.tgrd_in _))
                    (hom.comp acc_hom acc_stable (hom.tgrd_in gdt_grd) (stable.tgrd_in gdt_grd))],

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
        cases gdt_grd with tgrd var,
        case Grd.tgrd {
            cases c: (tgrd_eval tgrd env) with env',
            { simp [Gdt.eval_tgrd_of_none c, U, Φ_eval_not_tgrd_none c], },
            { simp [Gdt.eval_tgrd_of_some c, U, Φ_eval_not_tgrd_some c, Φ_eval_tgrd_some c, @gdt_ih env'], },
        },
        case Grd.bang {
            cases c: is_bottom var env,
            { simp [Gdt.eval_bang_of_not_bottom c, U, c, @gdt_ih env], },
            { simp [Gdt.eval_bang_of_bottom c, U, c], },
        },
    },
end
