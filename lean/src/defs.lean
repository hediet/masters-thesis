import data.bool

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
| xgrd (xgrd: XGrd)
| bang (var: Var)

inductive Gdt
| leaf (leaf: Leaf)
| branch (tr1: Gdt) (tr2: Gdt)
| grd (grd: Grd) (tr: Gdt)

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
-- This describes the semantic of Refinement Types.
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


-- Alternative definition without accumulator
def 𝒰' : Gdt → Φ
| (Gdt.leaf _) := Φ.false
| (Gdt.branch tr1 tr2) := (𝒰' tr1).and (𝒰' tr2)
| (Gdt.grd (Grd.bang var) tree) := ((Φ.var_is_not_bottom var).and (𝒰' tree))
| (Gdt.grd (Grd.xgrd grd) tree) :=
                (Φ.not_xgrd grd)
            .or
                (Φ.xgrd_in grd (𝒰' tree))

def 𝒰 := 𝒰'

/- TODO:
def 𝒰_acc : Gdt → (Φ → Φ) → Φ → Φ
| (Gdt.leaf _) f ty := Φ.false
| acc (Gdt.branch tr1 tr2) := (𝒰_acc (𝒰_acc acc tr1) tr2)
| acc (Gdt.grd (Grd.bang var) tree) :=
    𝒰_acc (acc.and $ Φ.var_is_not_bottom var) tree
| acc (Gdt.grd (Grd.xgrd grd) tree) :=
            (acc.and $ Φ.not_xgrd grd)
        .or
            (𝒰_acc (acc.and (Φ.xgrd grd)) tree)

def 𝒰 : Gdt → Φ := 𝒰_acc Φ.true
-/


-- # Annotate

inductive Ant (α: Type)
| leaf (a: α) (leaf: Leaf): Ant
| branch (tr1: Ant) (tr2: Ant): Ant
| diverge (a: α) (tr: Ant): Ant

-- Alternative definition without accumulator
def map_ant { α : Type } { β : Type } : (α → β) → Ant α → Ant β
| f (Ant.leaf a leaf) := Ant.leaf (f a) leaf
| f (Ant.branch tr1 tr2) := (Ant.branch (map_ant f tr1) (map_ant f tr2))
| f (Ant.diverge a tr) := (Ant.diverge (f a) (map_ant f tr))

def 𝒜' : Gdt → Ant Φ
| (Gdt.leaf leaf) := Ant.leaf Φ.true leaf
| (Gdt.branch tr1 tr2) := Ant.branch (𝒜' tr1) $ map_ant ((𝒰' tr1).and) (𝒜' tr2)
| (Gdt.grd (Grd.bang var) tr) := Ant.diverge (Φ.var_is_bottom var) $ map_ant ((Φ.var_is_not_bottom var).and) (𝒜' tr)
| (Gdt.grd (Grd.xgrd grd) tr) := map_ant (Φ.xgrd_in grd) (𝒜' tr)

def 𝒜 := 𝒜'

/- TODO
def 𝒜_acc : Φ → Gdt → Ant Φ
| acc (Gdt.leaf leaf) := Ant.leaf acc leaf
| acc (Gdt.branch tr1 tr2) := Ant.branch (𝒜_acc acc tr1) (𝒜_acc (𝒰_acc acc tr1) tr2)
| acc (Gdt.grd (Grd.bang var) tr) := Ant.diverge (acc.and (Φ.var_is_bottom var)) (𝒜_acc (acc.and $ Φ.var_is_not_bottom var) tr)
| acc (Gdt.grd (Grd.xgrd grd) tr) := (𝒜_acc (acc.and $ Φ.xgrd grd) tr)

-- wie U[return(Phi) <- Ant Phi]
def 𝒜 : Gdt → Ant Φ := 𝒜_acc Φ.true
-/

-- ## Semantics of Ant

def ant_eval_all (ant: Ant Φ) (env: Env) := map_ant (λ ty, Φ_eval ty env) ant


def ant_eval' : Ant (bool) → option Result
| (Ant.leaf matches leaf) := if matches
    then some $ Result.leaf leaf
    else some $ Result.no_match
| (Ant.branch tr1 tr2) := match ant_eval' tr1, ant_eval' tr2 with
    | some Result.no_match, r := r
    | r, some Result.no_match := r
    | _, _ := none
    end
| (Ant.diverge matches tr) := match matches, ant_eval' tr with
    | ff, r := r
    | tt, some Result.no_match := some Result.diverged
    | _, _ := none
    end

-- ant_eval simp regeln manuell angeben
def ant_eval (ant: Ant Φ) (env: Env): option Result := ant_eval' (ant_eval_all ant env)


variable is_empty: Φ → bool

/-
TODO
structure LeafPartition := mk :: (acc : list Leaf) (inacc : list Leaf) (red : list Leaf)

-- returns (accessible, inaccessible, redundant) leaves, given that `is_empty` is correct.
def ℛ' : Ant bool → LeafPartition
| (Ant.leaf is_empty n) := if is_empty then ⟨ [], [], [n] ⟩ else ⟨ [n], [], [] ⟩
| (Ant.diverge is_empty tr) := 
    match ℛ' tr, is_empty with
    | ⟨ [], [], m :: ms ⟩, ff := ⟨ [], [m], ms ⟩
    | r, _ := r
    end
| (Ant.branch tr1 tr2) :=
    let r1 := ℛ' tr1, r2 := ℛ' tr2 in
        ⟨ r1.acc ++ r2.acc, r1.inacc ++ r2.inacc, r1.red ++ r2.red ⟩
-/

/-

(h1: ℛ' tr = (a, i, r))

(is_empty = false ∧ a = [] ∧ i = [] ∧ r ≠ [] ∧ foo = ([], [m], [ms]))
∨ (is_empty = true ∧ (a ≠ [] ∨ i ≠ [] ∨ r = [] ∧ foo = (a, i, r))

-/

-- returns (accessible, inaccessible, redundant) leaves, given that `is_empty` is correct.
def ℛ' : Ant bool → list Leaf × list Leaf × list Leaf
| (Ant.leaf is_empty n) := if is_empty then ([], [], [n]) else ([n], [], [])
| (Ant.diverge is_empty tr) := 
    match ℛ' tr, is_empty with
    | ([], [], m :: ms), ff := ([], [m], ms)
    | r, _ := r
    end
| (Ant.branch tr1 tr2) :=
    match (ℛ' tr1, ℛ' tr2) with
    | ((k, n, m), (k', n', m')) := (k ++ k', n ++ n', m ++ m')
    end

def ℛ (ant: Ant Φ): list Leaf × list Leaf × list Leaf :=
    ℛ' (map_ant is_empty ant)

def is_correct : (Φ → bool) → Prop
| g := ∀ ty: Φ, (
        -- If g says "ty is empty"
        ¬ g ty →
        -- then `ty` never evaluates to something.
        ∀ env: Env, ¬ Φ_eval ty env
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
