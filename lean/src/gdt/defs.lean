-- # Abstract Guard Trees
-- This chapter covers basic guard trees with abstract guards.

class GuardModule :=
    -- Represents the type of all guards.
    -- A guard resembles an if-condition that can fail or pass.
    -- If it passes, it can modify the environment.
    -- The semantic of guards is defined in a way that allows for direct reuse in
    -- so called refinement types.
    (Grd : Type)

    -- Represents the result type of evaluating a guard tree.
    (Leaf : Type)

    -- Represents an environment type that is used to define a semantic for a guard tree.
    (Env : Type)

    -- Describes a semantic for guards.
    -- None is returned if the guard fails. Guards can modify the environment.
    -- This abstraction allows for "let x = expr", "x == 1" or "let (Cons x:xs) = list" guards.
    (grd_eval : Grd → Env → option Env)


variable [GuardModule]
open GuardModule

-- ## Syntax

-- A guard tree is a tree of leaves, protected by (abstract) guards.
-- Every execution terminates with a leave. Guards "guard" sub-trees in a non-leathal way!
-- See non-strict guard trees for how a bang "guard" can be transformed to terminate execution.
inductive Gdt
| leaf : Leaf → Gdt
| branch : Gdt → Gdt → Gdt
| grd : Grd → Gdt → Gdt

-- ## Semantic

def gdt_eval : Gdt → Env → (option (Env × Leaf))
| (Gdt.leaf leaf) env := some (env, leaf)
| (Gdt.branch tr1 tr2) env :=
    match gdt_eval tr1 env with
    -- Return the first result.
    | some val := some val
    -- If first tree fails, proceed with second.
    | none := gdt_eval tr2 env
    end
| (Gdt.grd grd tr) env :=
    match grd_eval grd env with
    -- If guard matches, proceed.
    | some val := gdt_eval tr env
    -- Otherwise, fail.
    | none := none
    end


-- ## Refinement Types

-- This is defined as in the paper, but abstracted over Grd and without a context.
-- The context is maintained by Env.
-- An explicit negation of guards is defined here, so guards don't need be closed under negation.
inductive Φ
| false : Φ
| true : Φ
| grd : Grd → Φ
| negGrd : Grd → Φ
| or : Φ → Φ → Φ
| and : Φ → Φ → Φ

-- This describes the semantic of Refinement Types.
def Φ_eval: Φ → Env → option Env
| Φ.false env := none
| Φ.true env := some env
| (Φ.grd grd) env := grd_eval grd env
| (Φ.negGrd grd) env :=
    match grd_eval grd env with
    | some env := none
    -- If a guard fails, it does not modify the environment!
    | none := some env
    end
| (Φ.or t1 t2) env :=
    match Φ_eval t1 env with
    | some env := some env
    | none := Φ_eval t2 env
    end
| (Φ.and t1 t2) env :=
    match (Φ_eval t1 env) with
    -- It is important here to continue with the environment after processing t1!
    | some env' := Φ_eval t2 env'
    | none := none
    end



-- ## Uncovered Refinement Types
 
def 𝒰_acc : Φ → Gdt → Φ
| acc (Gdt.leaf _) := Φ.false
| acc (Gdt.branch tr1 tr2) := (𝒰_acc (𝒰_acc acc tr1) tr2)

| acc (Gdt.grd grd tree) :=
        Φ.or
            (acc.and $ Φ.negGrd grd)
            (𝒰_acc (acc.and (Φ.grd grd)) tree)

def 𝒰 : Gdt → Φ := 𝒰_acc Φ.true


-- Alternative definition without accumulator
def 𝒰' : Gdt → Φ
| (Gdt.leaf _) := Φ.false
| (Gdt.branch tr1 tr2) := (𝒰' tr1).and (𝒰' tr2)
| (Gdt.grd grd tree) :=
                (Φ.negGrd grd)
            .or
                ((Φ.grd grd).and (𝒰' tree))

-- ## Annotate

inductive Ant
| leaf : Φ → Leaf → Ant
| branch : Ant → Ant → Ant

def 𝒜_acc : Φ → Gdt → Ant
| acc (Gdt.leaf leaf) := Ant.leaf acc leaf
| acc (Gdt.branch tr1 tr2) := Ant.branch (𝒜_acc acc tr1) (𝒜_acc (𝒰_acc acc tr1) tr2)
| acc (Gdt.grd grd tr) := (𝒜_acc (acc.and $ Φ.grd grd) tr)

def 𝒜 : Gdt → Ant := 𝒜_acc Φ.true


-- Semantics of Ant

def ant_eval : Ant → Env → list (Env × Leaf)
| (Ant.leaf ty leaf) env := match (Φ_eval ty env) with
    | none := []
    | (some env) := [(env, leaf)]
    end
| (Ant.branch tr1 tr2) env := (ant_eval tr1 env) ++ (ant_eval tr2 env)

def option_to_list { α: Type _ } : option α → list α
| none := []
| (some val) := [val]
