import data.bool
import data.finset

class GuardModule :=
    -- Represents the result type of evaluating a guard tree.
    (Rhs : Type)
    [rhs_decidable: decidable_eq Rhs]

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

attribute [instance] GuardModule.rhs_decidable

-- # Guard Trees
-- ## Syntax
inductive Grd
| xgrd (xgrd: XGrd)
| bang (var: Var)

inductive Gdt
| rhs (rhs: Rhs)
| branch (tr1: Gdt) (tr2: Gdt)
| grd (grd: Grd) (tr: Gdt)

def Gdt.branch_option : option Gdt → option Gdt → option Gdt
| (some tr1) (some tr2) := some (Gdt.branch tr1 tr2)
| (some tr1) none := some tr1
| none (some tr2) := some tr2
| none none := none

def Gdt.grd_option : Grd → option Gdt → option Gdt
| grd (some tr) := some (Gdt.grd grd tr)
| _ none := none

-- Removes a set of rhss from a guard tree.
-- Returns `none` if the guard tree is empty.
def Gdt.remove_rhss : finset Rhs → Gdt → option Gdt
| rhss (Gdt.rhs rhs) := if rhs ∈ rhss then none else some (Gdt.rhs rhs)
| rhss (Gdt.branch tr1 tr2) := Gdt.branch_option (tr1.remove_rhss rhss) (tr2.remove_rhss rhss)
| rhss (Gdt.grd grd tr) := Gdt.grd_option grd (tr.remove_rhss rhss)

-- Returns a set of all rhss that a guard tree contains.
def Gdt.rhss: Gdt → finset Rhs
| (Gdt.rhs rhs) := { rhs }
| (Gdt.branch tr1 tr2) := tr1.rhss ∪ tr2.rhss
| (Gdt.grd grd tr) := tr.rhss

-- States that all rhss are different in a given guard tree.
def Gdt.disjoint_rhss: Gdt → Prop
| (Gdt.rhs rhs) := true
| (Gdt.branch tr1 tr2) := tr1.disjoint_rhss ∧ tr2.disjoint_rhss ∧ disjoint tr1.rhss tr2.rhss
| (Gdt.grd grd tr) := tr.disjoint_rhss

-- ## Semantic
inductive Result (α: Type)
| value: α → Result
| diverged: Result
| no_match: Result

def Grd.eval : Grd → Env → Result Env
| (Grd.xgrd grd) env :=
    match xgrd_eval grd env with
    | none := Result.no_match
    | some env' := Result.value env'
    end
| (Grd.bang var) env :=
    if is_bottom var env
    then Result.diverged
    else Result.value env

def Result.bind { α β: Type } (f: α → Result β): Result α → Result β
| (Result.value val) := f val
| Result.diverged := Result.diverged
| Result.no_match := Result.no_match

def Gdt.eval : Gdt → Env → Result Rhs
| (Gdt.rhs rhs) env := Result.value rhs
| (Gdt.branch tr1 tr2) env :=
    match tr1.eval env with
    | Result.no_match := tr2.eval env
    | r := r
    end
| (Gdt.grd grd tr) env := (grd.eval env).bind tr.eval

-- This continues `gdt_eval` to `option Gdt`.
def Gdt.eval_option : option Gdt → Env → Result Rhs
| (some gdt) env := gdt.eval env
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
def Φ.eval: Φ → Env → bool
| Φ.false env := ff
| Φ.true env := tt
| (Φ.xgrd_in grd ty) env := match xgrd_eval grd env with
    | some env := ty.eval env
    | none := ff
    end
| (Φ.not_xgrd grd) env :=
    match xgrd_eval grd env with
    | some env := ff
    | none := tt
    end
| (Φ.var_is_bottom var) env := is_bottom var env
| (Φ.var_is_not_bottom var) env := !is_bottom var env
| (Φ.or t1 t2) env := t1.eval env || t2.eval env
| (Φ.and t1 t2) env := t1.eval env && t2.eval env


-- ## Uncovered Refinement Types
def 𝒰_acc : (Φ → Φ) → Gdt → Φ
| acc (Gdt.rhs _) := acc Φ.false
-- TODO: Change to (𝒰_acc ((𝒰_acc id tr1).and ∘ acc) tr2)
| acc (Gdt.branch tr1 tr2) := (𝒰_acc (acc ∘ (𝒰_acc id tr1).and) tr2)
| acc (Gdt.grd (Grd.bang var) tree) :=
    𝒰_acc (acc ∘ (Φ.var_is_not_bottom var).and) tree
| acc (Gdt.grd (Grd.xgrd grd) tree) :=
            (acc (Φ.not_xgrd grd))
        .or
            (𝒰_acc (acc ∘ (Φ.xgrd_in grd)) tree)

def 𝒰 : Gdt → Φ := 𝒰_acc id

-- # Annotate
inductive Ant (α: Type)
| rhs (a: α) (rhs: Rhs): Ant
| branch (tr1: Ant) (tr2: Ant): Ant
| diverge (a: α) (tr: Ant): Ant

def 𝒜_acc : (Φ → Φ) → Gdt → Ant Φ
| acc (Gdt.rhs rhs) := Ant.rhs (acc Φ.true) rhs
| acc (Gdt.branch tr1 tr2) := Ant.branch (𝒜_acc acc tr1) (𝒜_acc ((𝒰_acc acc tr1).and ∘ acc) tr2)
| acc (Gdt.grd (Grd.bang var) tr) := Ant.diverge (acc (Φ.var_is_bottom var)) 
                                        (𝒜_acc (acc ∘ ((Φ.var_is_not_bottom var).and)) tr)
| acc (Gdt.grd (Grd.xgrd grd) tr) := (𝒜_acc (acc ∘ (Φ.xgrd_in grd)) tr)

def 𝒜 : Gdt → Ant Φ := 𝒜_acc id

-- TODO: define 𝒰𝒜 : (Φ → Φ) → Gdt → (Ant Φ, Φ)

-- # Empty Provers

def Φ.is_empty (ty: Φ): Prop := ∀ env: Env, ¬(ty.eval env)

variable can_prove_empty: Φ → bool

def is_empty_prover : (Φ → bool) → Prop
| g := ∀ ty: Φ, g ty = tt → ty.is_empty

-- Represents all correct G functions from the paper.
def Gs := { g : Φ → bool // is_empty_prover g }

-- # Definition of ℛ

-- returns (accessible, inaccessible, redundant) rhss, given that `can_prove_empty` is correct.
def ℛ : Ant Φ → list Rhs × list Rhs × list Rhs
| (Ant.rhs ty n) := if can_prove_empty ty then ([], [], [n]) else ([n], [], [])
| (Ant.diverge ty tr) := 
    match ℛ tr, can_prove_empty ty with
    | ([], [], m :: ms), ff := ([], [m], ms)
    | r, _ := r
    end
| (Ant.branch tr1 tr2) :=
    match (ℛ tr1, ℛ tr2) with
    | ((k, n, m), (k', n', m')) := (k ++ k', n ++ n', m ++ m')
    end
