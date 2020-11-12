import ..gdt.defs

-- # Non-Strict Guard Trees
-- This chapter covers abstract guard trees that
-- are non-strict but have a bang guard.
-- The bang guard strictly evaluates a given variable and
-- can make the entire computation diverge.

class NGuardModule :=
    -- Represents the type of all guards.
    (Grd : Type)

    -- Represents the result type of evaluating a guard tree.
    (Leaf : Type)

    -- Represents an environment type that is used to define a semantic for a guard tree.
    (Env : Type)

    -- Represents the type of variables that can be compared against bottom.
    (Var : Type)

    -- None is returned if the guard fails. Guards can modify the environment.
    -- This abstraction allows for "let x = expr", "x == 1" or "let (Cons x:xs) = list" guards.
    (grd_eval : Grd → Env → option Env)

    -- Checks whether a given var in env is bottom
    (is_bottom : Var → Env → bool)

variable [NGuardModule]
open NGuardModule

-- ## Syntax

inductive NGrd
| grd: Grd → NGrd
-- Non-Strict Guard Trees can use the bang guard.
| bang: Var → NGrd

-- We cannot define non-strict guard tree as direct specialization of guard trees,
-- as we need to provide a semantic for that.
-- However, we cannot provide a semantic for the `bang` guard directly.
-- (Such a semantic would not really work with refinement types)
inductive NGdt
| leaf : Leaf → NGdt
| branch : NGdt → NGdt → NGdt
| grd : NGrd → NGdt → NGdt

-- ## Semantic

-- Non-Strict Guard Trees can diverge early with "bottom", so `Leaf` must be extended.
inductive NLeaf
| bottom: NLeaf
| leaf: Leaf → NLeaf

def ngdt_eval : NGdt → Env → (option (Env × NLeaf))
| (NGdt.leaf leaf) env := some (env, NLeaf.leaf leaf)
| (NGdt.branch tr1 tr2) env :=
    match ngdt_eval tr1 env with
    | none := ngdt_eval tr2 env
    | some val := some val
    end
| (NGdt.grd (NGrd.grd grd) tr) env :=
    match grd_eval grd env with
    | none := none
    | some val := ngdt_eval tr env
    end
-- This is the only new case
| (NGdt.grd (NGrd.bang var) tr) env :=
    if is_bottom var env
    -- We diverge and exit early, if `var` evaluates to bottom.
    then some (env, NLeaf.bottom)
    -- Otherwise, we continue.
    else ngdt_eval tr env

-- ## Reduction To Abstract Guard Trees

-- Non-strict guard trees can be reduced to guard trees
-- which allows to apply theorems on guard trees to non-strict guard trees.

-- For this reduction, we need an `is_bottom` guard instead of a `bang` guard.
-- The `is_bottom` guard has a different semantic.
inductive XGrd
| grd: Grd → XGrd
| is_bottom: Var → XGrd

instance GuardModuleInstance : GuardModule := {
    Grd := XGrd,
    Leaf := NLeaf,
    Env := Env,
    grd_eval := λ grd, match grd with
    | XGrd.grd grd := grd_eval grd
    | XGrd.is_bottom var := λ env, if is_bottom var env then some env else none
    end
}

-- This transforms a non-strict guard tree to a guard tree.
def ngdt_to_gdt : NGdt → Gdt
| (NGdt.leaf leaf) := (Gdt.leaf (NLeaf.leaf leaf))
| (NGdt.branch tr1 tr2) := Gdt.branch (ngdt_to_gdt tr1) (ngdt_to_gdt tr2)
| (NGdt.grd (NGrd.bang var) tr) := Gdt.branch
        -- If `var` is bottom, we diverge with a bottom leaf.
        (Gdt.grd (XGrd.is_bottom var) (Gdt.leaf (NLeaf.bottom)))
        -- Otherwise, we continue.
        (ngdt_to_gdt tr)
| (NGdt.grd (NGrd.grd grd) tr) := (Gdt.grd (XGrd.grd grd) $ ngdt_to_gdt tr)


variable is_empty: Φ → bool

-- returns (accessible, inaccessible, redundant) leaves, given that `is_empty` is correct.
def ℛ : Ant → list Leaf × list Leaf × list Leaf
| (Ant.leaf ty (NLeaf.leaf n) ) := if is_empty ty then ([], [], [n]) else ([n], [], [])
| (Ant.leaf ty NLeaf.bottom ) := ([], [], [])
| (Ant.branch (Ant.leaf ty NLeaf.bottom ) tr2) := 
    match (ℛ tr2, is_empty ty) with
    | (([], [], m :: ms), false) := ([], [m], ms)
    | (r, _) := r
    end
| (Ant.branch tr1 tr2) :=
    match (ℛ tr1, ℛ tr2) with
    | ((k, n, m), (k', n', m')) := (k ++ k', n ++ n', m ++ m')
    end


def is_correct : (Φ → bool) → Prop
| g := ∀ ty: Φ, (
        -- If g sais "ty is empty"
        g ty = false →
        -- then `ty` never evaluates to something.
        ∀ env: Env, Φ_eval ty env = none
    )

-- Represents all correct G functions from the paper.
def Gs := { g : Φ → bool // is_correct g }



-- Removes a list of leaves from a guard tree.
-- Returns `none` if the guard tree is empty.
def remove_leaves [decidable_eq Leaf] : list Leaf → NGdt → option NGdt
| leaves (NGdt.leaf leaf) := if leaf ∈ leaves then none else some (NGdt.leaf leaf)
| leaves (NGdt.branch tr1 tr2) :=
    match (remove_leaves leaves tr1, remove_leaves leaves tr2) with
    | ((some tr1), (some tr2)) := some (NGdt.branch tr1 tr2)
    | ((some tr1), none) := some tr1
    | (none, (some tr2)) := some tr2
    | (none, none) := none
    end
| leaves (NGdt.grd grd tr) := 
    match remove_leaves leaves tr with
    | none := none
    | some tr := NGdt.grd grd tr
    end

-- Like `ngdt_eval` in the `some` case, but never accepts anything in the `none` case.
-- This accounts for empty guard trees.
def ngdt_eval_option : option NGdt → Env → (option (Env × NLeaf))
| (some gdt) env := ngdt_eval gdt env
| none env := none

