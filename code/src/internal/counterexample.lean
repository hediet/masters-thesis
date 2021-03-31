import tactic
import data.finset
import ..definitions
import .internal_definitions
import .Ant.rhss
import .utils

instance exmpl : GuardModule := {
    Rhs := ℕ,
    TGrd := ℕ,
    Env := ℕ,
    tgrd_eval := λ grd env, some env,
    Var := ℕ,
    is_bottom := λ var env, false
}

def ant_a := Ant.diverge ff ((Ant.rhs tt 1).branch (Ant.rhs ff 2))
def ant_b := Ant.diverge ff ((Ant.rhs tt 1).branch (Ant.rhs tt 2))

example : ant_a ⟶ ant_b ∧ (R ant_a).red = [1] ∧ (R ant_b).red = [2] :=
by finish [ant_a, ant_b, R, Ant.implies.rhs, Ant.implies.branch, Ant.implies.diverge]
