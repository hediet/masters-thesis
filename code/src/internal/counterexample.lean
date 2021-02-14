import tactic
import data.finset
import ..definitions
import .internal_definitions

instance exmpl : GuardModule := {
    Rhs := ℕ,
    Env := ℕ,
    TGrd := ℕ,
    Var := ℕ,
    tgrd_eval := λ tgrd env, some 0,
    is_bottom := λ var env, false,
}

def rhs (n: ℕ): Gdt := Gdt.rhs n
def grd (n: ℕ) (gdt: Gdt): Gdt := Gdt.grd (Grd.tgrd n) gdt

def my_gdt := grd 3 $ ((rhs 1).branch (rhs 2))

example : (A my_gdt ≠ 𝒜 my_gdt) :=
by simp [A, 𝒜, 𝒜_acc, my_gdt, rhs, grd, Ant.map]
