import tactic
import data.bool
import ..definitions
import .helper_defs

variable [GuardModule]
open GuardModule

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

lemma Φ_eval_not_xgrd_some { gdt_grd: XGrd } { env env': Env } (h: xgrd_eval gdt_grd env = some env'):
    (Φ.not_xgrd gdt_grd).eval env = ff :=
by simp [Φ.eval, h]

lemma Φ_eval_not_xgrd_none { gdt_grd: XGrd } { env: Env } (h: xgrd_eval gdt_grd env = none):
    (Φ.not_xgrd gdt_grd).eval env = tt :=
by simp [Φ.eval, h]


lemma Φ_eval_xgrd_some { gdt_grd: XGrd } { ty: Φ } { env env': Env } (h: xgrd_eval gdt_grd env = some env'):
    (Φ.xgrd_in gdt_grd ty).eval env = ty.eval env' :=
by simp [Φ.eval, h]

@[simp]
lemma Φ_eval_var_is_not_bottom { var: Var } { env: Env }:
    (Φ.var_is_not_bottom var).eval env = !is_bottom var env :=
by simp [Φ.eval]

@[simp]
lemma Φ_eval_var_is_bottom { var: Var } { env: Env }:
    (Φ.var_is_bottom var).eval env = is_bottom var env :=
by simp [Φ.eval]
