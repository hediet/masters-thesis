class GuardModule :=
    -- Represents the type of all guards.
    -- A guard resembles an if-condition that can fail or pass.
    -- If it passes, it can modify the environment.
    -- The semantic of guards is defined in a way that allows for direct reuse in
    -- so called refinement types.
    (XGrd : Type)

    -- Represents the result type of evaluating a guard tree.
    (Leaf : Type)

    -- Represents an environment type that is used to define a semantic for a guard tree.
    (Env : Type)

    -- Represents the type of variables that can be compared against bottom.
    (Var : Type)

    -- Describes a semantic for guards.
    -- None is returned if the guard fails. Guards can modify the environment.
    -- This abstraction allows for "let x = expr", "x == 1" or "let (Cons x:xs) = list" guards.
    (xgrd_eval : XGrd → Env → option Env)

    -- Checks whether a given var in env is bottom
    (is_bottom : Var → Env → bool)

variable [GuardModule]
open GuardModule

-- # Guard Trees
-- ## Syntax

inductive Grd
| xgrd (xgrd: XGrd): Grd
| bang (var: Var): Grd

inductive Gdt
| leaf (leaf: Leaf) : Gdt
| branch (tr1: Gdt) (tr2: Gdt) : Gdt
| grd (grd: Grd) (tr: Gdt) : Gdt

-- ## Semantic

inductive Result
| leaf (leaf: Leaf) : Result
| diverged : Result
| no_match : Result

def gdt_eval : Gdt → Env → Result
| (Gdt.leaf leaf) env := Result.leaf leaf
| (Gdt.branch tr1 tr2) env :=
    match gdt_eval tr1 env with
    | Result.no_match := gdt_eval tr2 env
    | r := r
    end
| (Gdt.grd (Grd.xgrd grd) tr) env :=
    match xgrd_eval grd env with
    | none := Result.no_match
    | some val := gdt_eval tr env
    end
-- This is the only new case
| (Gdt.grd (Grd.bang var) tr) env :=
    if is_bottom var env
    then Result.diverged
    else gdt_eval tr env

-- # Refinement Types

-- ## Syntax
inductive Φ
| false : Φ
| true : Φ
| xgrd (xgrd: XGrd) : Φ
| not_xgrd (xgrd: XGrd) : Φ
| var_is_bottom (var: Var): Φ
| var_is_not_bottom (var: Var): Φ
| or : Φ → Φ → Φ
| and : Φ → Φ → Φ

-- ## Semantic
-- This describes the semantic of Refinement Types.
def Φ_eval: Φ → Env → option Env
| Φ.false env := none
| Φ.true env := some env
| (Φ.xgrd grd) env := xgrd_eval grd env
| (Φ.not_xgrd grd) env :=
    match xgrd_eval grd env with
    | some env := none
    -- If a guard fails, it does not modify the environment!
    | none := some env
    end
| (Φ.var_is_bottom var) env :=
    if is_bottom var env
    then some env
    else none
| (Φ.var_is_not_bottom var) env :=
    if is_bottom var env
    then none
    else some env
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
| acc (Gdt.grd (Grd.bang var) tree) :=
    𝒰_acc (acc.and $ Φ.var_is_not_bottom var) tree
| acc (Gdt.grd (Grd.xgrd grd) tree) :=
            (acc.and $ Φ.not_xgrd grd)
        .or
            (𝒰_acc (acc.and (Φ.xgrd grd)) tree)

def 𝒰 : Gdt → Φ := 𝒰_acc Φ.true


-- Alternative definition without accumulator
def 𝒰' : Gdt → Φ
| (Gdt.leaf _) := Φ.false
| (Gdt.branch tr1 tr2) := (𝒰' tr1).and (𝒰' tr2)
| (Gdt.grd (Grd.bang var) tree) := (Φ.var_is_not_bottom var).and (𝒰' tree)
| (Gdt.grd (Grd.xgrd grd) tree) :=
                (Φ.not_xgrd grd)
            .or
                ((Φ.xgrd grd).and (𝒰' tree))

-- # Annotate

inductive Ant
| leaf (ty: Φ) (leaf: Leaf): Ant
| branch (tr1: Ant) (tr2: Ant): Ant
| diverge (ty: Φ) (tr: Ant): Ant

def 𝒜_acc : Φ → Gdt → Ant
| acc (Gdt.leaf leaf) := Ant.leaf acc leaf
| acc (Gdt.branch tr1 tr2) := Ant.branch (𝒜_acc acc tr1) (𝒜_acc (𝒰_acc acc tr1) tr2)
| acc (Gdt.grd (Grd.bang var) tr) := Ant.diverge (acc.and (Φ.var_is_bottom var)) (𝒜_acc (acc.and $ Φ.var_is_not_bottom var) tr)
| acc (Gdt.grd (Grd.xgrd grd) tr) := (𝒜_acc (acc.and $ Φ.xgrd grd) tr)

def 𝒜 : Gdt → Ant := 𝒜_acc Φ.true


-- ## Semantics of Ant

inductive AntResult
| leaf (leaf: Leaf): AntResult
| diverged : AntResult

def ant_eval_list : Ant → Env → list AntResult
| (Ant.leaf ty leaf) env := match Φ_eval ty env with
    | none := []
    | (some env) := [AntResult.leaf leaf]
    end
| (Ant.branch tr1 tr2) env := (ant_eval_list tr1 env) ++ (ant_eval_list tr2 env)
| (Ant.diverge diverge_ty tr) env := match Φ_eval diverge_ty env with
    | none := ant_eval_list tr env
    | (some env) := [AntResult.diverged]
    end

def ant_eval (tree: Ant) (env: Env) : option Result :=
    match ant_eval_list tree env with
    | (AntResult.leaf leaf) :: [] := some (Result.leaf leaf)
    | (AntResult.diverged) :: [] := some Result.diverged
    | _ := none
    end

def result_to_list { α: Type _ } : option α → list α
| none := []
| (some val) := [val]

variable is_empty: Φ → bool

def ℛ : Ant → list Leaf × list Leaf × list Leaf
| (Ant.leaf ty n) := if is_empty ty then ([], [], [n]) else ([n], [], [])
| (Ant.diverge ty tr) := 
    match (ℛ tr, is_empty ty) with
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
def remove_leaves [decidable_eq Leaf] : list Leaf → Gdt → option Gdt
| leaves (Gdt.leaf leaf) := if leaf ∈ leaves then none else some (Gdt.leaf leaf)
| leaves (Gdt.branch tr1 tr2) :=
    match (remove_leaves leaves tr1, remove_leaves leaves tr2) with
    | ((some tr1), (some tr2)) := some (Gdt.branch tr1 tr2)
    | ((some tr1), none) := some tr1
    | (none, (some tr2)) := some tr2
    | (none, none) := none
    end
| leaves (Gdt.grd grd tr) := 
    match remove_leaves leaves tr with
    | none := none
    | some tr := Gdt.grd grd tr
    end

-- Like `ngdt_eval` in the `some` case, but never accepts anything in the `none` case.
-- This accounts for empty guard trees.
def gdt_eval_option : option Gdt → Env → Result
| (some gdt) env := gdt_eval gdt env
| none env := Result.no_match
