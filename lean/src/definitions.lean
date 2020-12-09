import data.bool
import data.finset

class GuardModule :=
    -- Represents the result type of evaluating a guard tree.
    (Leaf : Type)
    [leaf_decidable: decidable_eq Leaf]

    -- Represents an environment type that is used to define a semantic for a guard tree.
    (Env : Type)

    -- Represents the type of all guards.
    -- A guard resembles an if-condition that can fail or pass.
    -- If it passes, it can modify the environment.
    -- The semantic of guards is defined in a way that allows for direct reuse in
    -- so called refinement types.
    (XGrd : Type)

    -- Describes a semantic for guards.
    -- None is returned if the guard fails. Guards can modify the environment.
    -- This abstraction allows for "let x = expr", "x == 1" or "let (Cons x:xs) = list" guards.
    (xgrd_eval : XGrd → Env → option Env)

    -- Represents the type of variables that can be compared against bottom.
    (Var : Type)

    -- Checks whether a given var in env is bottom
    (is_bottom : Var → Env → bool)

variable [GuardModule]
open GuardModule

attribute [instance] GuardModule.leaf_decidable

-- # Guard Trees
-- ## Syntax
inductive Grd
| xgrd (xgrd: XGrd)
| bang (var: Var)

inductive Gdt
| leaf (leaf: Leaf)
| branch (tr1: Gdt) (tr2: Gdt)
| grd (grd: Grd) (tr: Gdt)

def gdt_build_branch : option Gdt → option Gdt → option Gdt
| (some tr1) (some tr2) := some (Gdt.branch tr1 tr2)
| (some tr1) none := some tr1
| none (some tr2) := some tr2
| none none := none

def gdt_build_grd : Grd → option Gdt → option Gdt
| grd (some tr) := some (Gdt.grd grd tr)
| _ none := none

-- Removes a set of leaves from a guard tree.
-- Returns `none` if the guard tree is empty.
def gdt_remove_leaves : finset Leaf → Gdt → option Gdt
| leaves (Gdt.leaf leaf) := if leaf ∈ leaves then none else some (Gdt.leaf leaf)
| leaves (Gdt.branch tr1 tr2) := gdt_build_branch (gdt_remove_leaves leaves tr1) (gdt_remove_leaves leaves tr2)
| leaves (Gdt.grd grd tr) := gdt_build_grd grd (gdt_remove_leaves leaves tr)

-- Returns a set of all leaves that a guard tree contains.
def gdt_leaves: Gdt → finset Leaf
| (Gdt.leaf leaf) := { leaf }
| (Gdt.branch tr1 tr2) := gdt_leaves tr1 ∪ gdt_leaves tr2
| (Gdt.grd grd tr) := gdt_leaves tr

-- States that all leaves are different in a given guard tree.
def disjoint_leaves: Gdt → Prop
| (Gdt.leaf leaf) := true
| (Gdt.branch tr1 tr2) := disjoint_leaves tr1 ∧ disjoint_leaves tr2 ∧ disjoint (gdt_leaves tr1) (gdt_leaves tr2)
| (Gdt.grd grd tr) := disjoint_leaves tr

-- ## Semantic
inductive Result
| leaf (leaf: Leaf)
| diverged
| no_match

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
    | some val := gdt_eval tr val
    end
| (Gdt.grd (Grd.bang var) tr) env :=
    if is_bottom var env
    then Result.diverged
    else gdt_eval tr env

-- This continues `gdt_eval` to `option Gdt`.
def gdt_eval_option : option Gdt → Env → Result
| (some gdt) env := gdt_eval gdt env
| none env := Result.no_match

-- # Refinement Types
-- ## Syntax
inductive Φ
| false
| true
| xgrd_in (xgrd: XGrd) (ty: Φ)
| not_xgrd (xgrd: XGrd)
| var_is_bottom (var: Var)
| var_is_not_bottom (var: Var)
| or (ty1: Φ) (ty2: Φ)
| and (ty1: Φ) (ty2: Φ)

-- ## Semantic
def Φ_eval: Φ → Env → bool
| Φ.false env := ff
| Φ.true env := tt
| (Φ.xgrd_in grd ty) env := match xgrd_eval grd env with
    | some env := Φ_eval ty env
    | none := ff
    end
| (Φ.not_xgrd grd) env :=
    match xgrd_eval grd env with
    | some env := ff
    | none := tt
    end
| (Φ.var_is_bottom var) env := is_bottom var env
| (Φ.var_is_not_bottom var) env := !is_bottom var env
| (Φ.or t1 t2) env := Φ_eval t1 env || Φ_eval t2 env
| (Φ.and t1 t2) env := Φ_eval t1 env && Φ_eval t2 env


-- ## Uncovered Refinement Types
-- Φ_eval (𝒰_acc gdt acc ty) = Φ_eval (acc (𝒰' gdt)) :=
def 𝒰_acc : (Φ → Φ) → Gdt → Φ
| acc (Gdt.leaf _) := Φ.false
| acc (Gdt.branch tr1 tr2) := (𝒰_acc (𝒰_acc acc tr1).and tr2)
| acc (Gdt.grd (Grd.bang var) tree) :=
    𝒰_acc (acc ∘ (Φ.var_is_not_bottom var).and) tree
| acc (Gdt.grd (Grd.xgrd grd) tree) :=
            (acc (Φ.not_xgrd grd))
        .or
            (𝒰_acc (acc ∘ (Φ.xgrd_in grd)) tree)

def 𝒰 : Gdt → Φ := 𝒰_acc id

-- # Annotate
inductive Ant (α: Type)
| leaf (a: α) (leaf: Leaf): Ant
| branch (tr1: Ant) (tr2: Ant): Ant
| diverge (a: α) (tr: Ant): Ant

def 𝒜_acc : (Φ → Φ) → Gdt → Ant Φ
| acc (Gdt.leaf leaf) := Ant.leaf (acc Φ.true) leaf
| acc (Gdt.branch tr1 tr2) := Ant.branch (𝒜_acc acc tr1) (𝒜_acc (𝒰_acc acc tr1).and tr2)
| acc (Gdt.grd (Grd.bang var) tr) := Ant.diverge (acc (Φ.var_is_bottom var)) (𝒜_acc (acc ∘ (Φ.var_is_not_bottom var).and) tr)
| acc (Gdt.grd (Grd.xgrd grd) tr) := (𝒜_acc (acc ∘ (Φ.xgrd_in grd)) tr)

def 𝒜 : Gdt → Ant Φ := 𝒜_acc id

-- # Empty Provers

variable can_prove_empty: Φ → bool

def is_empty_prover : (Φ → bool) → Prop
| g := ∀ ty: Φ, (
        -- If g says "ty can be proven to be empty"
        g ty = tt →
        -- then `ty` never evaluates to something.
        ∀ env: Env, ¬ Φ_eval ty env
    )

-- Represents all correct G functions from the paper.
def Gs := { g : Φ → bool // is_empty_prover g }

-- # Definition of ℛ

-- returns (accessible, inaccessible, redundant) leaves, given that `can_prove_empty` is correct.
def ℛ : Ant Φ → list Leaf × list Leaf × list Leaf
| (Ant.leaf ty n) := if can_prove_empty ty then ([], [], [n]) else ([n], [], [])
| (Ant.diverge ty tr) := 
    match ℛ tr, can_prove_empty ty with
    | ([], [], m :: ms), ff := ([], [m], ms)
    | r, _ := r
    end
| (Ant.branch tr1 tr2) :=
    match (ℛ tr1, ℛ tr2) with
    | ((k, n, m), (k', n', m')) := (k ++ k', n ++ n', m ++ m')
    end
