import tactic
import data.bool
import ...definitions
import ..internal_definitions

variable [GuardModule]
open GuardModule

-- TODO rename Φ_ to Φ.

@[simp]
lemma Φ_eval_or { ty1 ty2: Φ } { env: Env }: (ty1.or ty2).eval env = (ty1.eval env) || (ty2.eval env) :=
by simp [Φ.eval]

@[simp]
lemma Φ_eval_and { ty1 ty2: Φ } { env: Env }: (ty1.and ty2).eval env = (ty1.eval env) && (ty2.eval env) :=
begin
    cases c1: ty1.eval env;
    cases c2: ty2.eval env;
    simp [Φ.eval, c1, c2],
end

lemma Φ_eval_not_tgrd_some { gdt_grd: TGrd } { env env': Env } (h: tgrd_eval gdt_grd env = some env'):
    (Φ.not_tgrd gdt_grd).eval env = ff :=
by simp [Φ.eval, h]

lemma Φ_eval_not_tgrd_none { gdt_grd: TGrd } { env: Env } (h: tgrd_eval gdt_grd env = none):
    (Φ.not_tgrd gdt_grd).eval env = tt :=
by simp [Φ.eval, h]

lemma Φ_eval_tgrd_some { gdt_grd: TGrd } { env env': Env } (h: tgrd_eval gdt_grd env = some env') (ty: Φ):
    (Φ.tgrd_in gdt_grd ty).eval env = ty.eval env' :=
by simp [Φ.eval, h]

lemma Φ_eval_tgrd_none { gdt_grd: TGrd } { env: Env } (h: tgrd_eval gdt_grd env = none) (ty: Φ):
    (Φ.tgrd_in gdt_grd ty).eval env = ff :=
by simp [Φ.eval, h]

@[simp]
lemma Φ_eval_var_is_not_bottom { var: Var } { env: Env }:
    (Φ.var_is_not_bottom var).eval env = !is_bottom var env :=
by simp [Φ.eval]

@[simp]
lemma Φ_eval_var_is_bottom { var: Var } { env: Env }:
    (Φ.var_is_bottom var).eval env = is_bottom var env :=
by simp [Φ.eval]
