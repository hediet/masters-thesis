-- # Abstract Guard Trees
-- This chapter covers basic guards trees with abstract guards.

-- Represents the type of all guards.
variable { Grd : Type _ }

-- Represents the result type of evaluating a guard tree.
variable { Leaf  : Type _ }

-- Represents an environment type that is used to define a semantic for a guard tree.
variable { Env : Type _ }



-- ## Guard Trees
-- Semantics of Guards
-- None is returned if the guard fails. Guards can modify the environment.
-- This abstraction allows for "let x = expr", "x == 1" or "let (Cons x:xs) = list" guards.
class GuardSemantic :=
(grd_eval : Grd → Env → option Env)

-- This is exactly as defined in the paper, except that guards are abstract.
inductive Gdt
| leaf : Leaf → Gdt
| branch : Gdt → Gdt → Gdt
| grd : Grd → Gdt → Gdt

-- Semantics of Guard Trees
def gdt_eval [@GuardSemantic Grd Env] : @Gdt Grd Leaf → Env → (option (Env × Leaf))
| (Gdt.leaf leaf) env := some (env, leaf)
| (Gdt.branch tr1 tr2) env :=
    match gdt_eval tr1 env with
    -- Return the first result.
    | some val := some val
    -- If first tree fails, proceed with second.
    | none := gdt_eval tr2 env
    end
| (Gdt.grd grd tr) env :=
    match GuardSemantic.grd_eval grd env with
    -- If guard matches, proceed
    | some val := gdt_eval tr env
    -- otherwise, fail.
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

-- Semantics of Refinement Types
def Φ_eval [@GuardSemantic Grd Env] : @Φ Grd → Env → option Env
| Φ.false env := none
| Φ.true env := some env
| (Φ.grd grd) env := GuardSemantic.grd_eval grd env
| (Φ.negGrd grd) env :=
    match GuardSemantic.grd_eval grd env with
    | some env := none
    -- If a guard fails, it does not modify the environment.
    | none := some env
    end
| (Φ.or t1 t2) env :=
    match Φ_eval t1 env with
    | some env := some env
    | none := Φ_eval t2 env
    end
| (Φ.and t1 t2) env :=
    match Φ_eval t1 env with
    -- It is important here to continue with the environment after processing t1!
    | some env' := Φ_eval t2 env'
    | none := none
    end



-- ## Uncovered Refinement Types

def 𝒰_acc : @Φ Grd → @Gdt Grd Leaf → @Φ Grd
| acc (Gdt.leaf _) := Φ.false
| acc (Gdt.branch tr1 tr2) := (𝒰_acc (𝒰_acc acc tr1) tr2)
| acc (Gdt.grd grd tree) :=
        Φ.or
            (Φ.and acc $ Φ.negGrd grd)
            (𝒰_acc (Φ.and acc (Φ.grd grd)) tree)

def 𝒰 : @Gdt Grd Leaf → @Φ Grd := 𝒰_acc Φ.true

-- ### start: optional

-- Alternative definition without accumulator
def 𝒰' : @Gdt Grd Leaf → @Φ Grd
| (Gdt.leaf _) := Φ.false
| (Gdt.branch tr1 tr2) := Φ.and (𝒰' tr1) (𝒰' tr2)
| (Gdt.grd grd tree) := Φ.or
            (Φ.negGrd grd)
            (Φ.and (Φ.grd grd) (𝒰' tree))

-- maybe this lemma is too strong and we can only claim semantic equivalence.
-- Must be weakened in this case.
-- This lemma is not really necessery anyways.
lemma 𝒰_𝒰'_equiv : ∀ gdt: @Gdt Grd Leaf, 𝒰 gdt = 𝒰' gdt := sorry

-- ### end: optional

-- Uncovered refinement types capture all values that are not covered.
theorem 𝒰_eval [@GuardSemantic Grd Env] :
    ∀ env: Env, ∀ gdt: @Gdt Grd Leaf,
        (gdt_eval gdt env ≠ none) ↔ (Φ_eval (𝒰 gdt) env = none)
    := sorry



-- ## Annotate

inductive Ant
| leaf : (@Φ Grd) → Leaf → Ant
| branch : Ant → Ant → Ant

def 𝒜_acc : @Φ Grd → @Gdt Grd Leaf → @Ant Grd Leaf
| acc (Gdt.leaf leaf) := Ant.leaf acc leaf
| acc (Gdt.branch tr1 tr2) := Ant.branch (𝒜_acc acc tr1) (𝒜_acc (𝒰 tr1) tr2)
| acc (Gdt.grd grd tr) := (𝒜_acc (Φ.and acc $ Φ.grd grd) tr)

def 𝒜 : @Gdt Grd Leaf → @Ant Grd Leaf := 𝒜_acc Φ.true


-- Semantics of Ant

def ant_eval [@GuardSemantic Grd Env] : @Ant Grd Leaf → Env → list (Env × Leaf)
| (Ant.leaf ty leaf) env := match (Φ_eval ty env) with
    | none := []
    | (some env) := [(env, leaf)]
    end
| (Ant.branch tr1 tr2) env := (ant_eval tr1 env) ++ (ant_eval tr2 env)

def option_to_list { α: Type _ } : option α → list α
| none := []
| (some val) := [val]

-- 𝒜 maintains semantics
-- This theorem implies that ant_eval returns a list of length at most 1.
-- This means that the refinement types created by 𝒜 are disjoint.
theorem 𝒜_eval [@GuardSemantic Grd Env] :
    ∀ env: Env, ∀ gdt: @Gdt Grd Leaf,
        (option_to_list $ gdt_eval gdt env) = ant_eval (𝒜 gdt) env := sorry




-- # Non-Strict Guard Trees
-- This chapter covers abstract guard trees that
-- are non-strict but have a bang guard.
-- The bang guard strictly evaluates a given variable and
-- can make the entire computation diverge.

namespace NGdt

variable { Var : Type _ }

inductive NGrd
| grd: Grd → NGrd
| bang: Var → NGrd

-- Non-Strict Guard Trees can use the bang guard.
def NGdt :=(@Gdt (@NGrd Grd Var) Leaf)

-- ## Semantics of Non-Strict Guard Trees

-- Non-Strict Guard Trees can diverge early with "bottom", so `Leaf` must be extended.
inductive NLeaf
| bottom: NLeaf
| leaf: Leaf → NLeaf

-- Non-Strict Guard Trees need a semantic for `Grd` and for an is-bottom predicate.
-- This can be achieved by asserting a semantic for `XGrd`:
inductive XGrd
| grd: Grd → XGrd
| isBottom: Var → XGrd

def ngdt_eval [@GuardSemantic (@XGrd Grd Var) Env] : @NGdt Grd Leaf Var → Env → (option (Env × (@NLeaf Leaf)))
| (Gdt.leaf leaf) env := some (env, NLeaf.leaf leaf)
| (Gdt.branch tr1 tr2) env :=
    match ngdt_eval tr1 env with
    | none := ngdt_eval tr2 env
    | some val := some val
    end
| (Gdt.grd (NGrd.grd grd) tr) env :=
    match GuardSemantic.grd_eval ((@XGrd.grd Grd Var) grd) env with
    | none := none
    | some val := ngdt_eval tr env
    end
-- This is the only new case
| (Gdt.grd (NGrd.bang var) tr) env :=
    match GuardSemantic.grd_eval ((@XGrd.isBottom Grd Var) var) env with
    -- We diverge and exit early, if `var` evaluates to bottom.
    | some val := some (env, NLeaf.bottom)
    -- Otherwise, we continue.
    | none := ngdt_eval tr env
    end

-- ## Reduction To Abstract Guard Trees

-- There is no `GuardSemantic` that can describe the effect of the bang guard!
-- This is because bang guards can diverge and terminate the entire computation.
-- We need to transform the guard tree to describe the semantic.

-- This transforms a non-strict guard tree to a guard tree with the `isBottom` guard.
-- The new guard tree can diverge early.
def ngdt_to_gdt : (@NGdt Grd Leaf Var) → (@Gdt (@XGrd Grd Var) (@NLeaf Leaf))
| (Gdt.leaf leaf) := (Gdt.leaf (NLeaf.leaf leaf))
| (Gdt.branch tr1 tr2) := Gdt.branch (ngdt_to_gdt tr1) (ngdt_to_gdt tr2)
| (Gdt.grd (NGrd.bang var) tr) := Gdt.branch
        -- If `var` is bottom, the we diverge with the bottom leaf.
        (Gdt.grd (XGrd.isBottom var) (Gdt.leaf (NLeaf.bottom)))
        -- Otherwise, we continue.
        (ngdt_to_gdt tr)
| (Gdt.grd (NGrd.grd grd) tr) := (Gdt.grd (XGrd.grd grd) $ ngdt_to_gdt tr)


-- Reduction to Guard Trees maintains semantic.
lemma ngdt_eval_eq_gdt_eval [gs: @GuardSemantic (@XGrd Grd Var) Env] :
    ∀ gdt: @NGdt Grd Leaf Var, ∀ env: Env,
        ngdt_eval gdt env = gdt_eval (ngdt_to_gdt gdt) env := sorry


variable is_empty: @Φ Grd → bool

-- returns (accessible, inaccessible, redundant) leaves, given that `is_empty` is correct.
def ℛ : @Ant Grd NLeaf → list Leaf × list Leaf × list Leaf
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


def is_correct [@GuardSemantic Grd Env] : (@Φ Grd → bool) → Prop
| g := ∀ ty: @Φ Grd, (
        -- If g sais "ty is empty"
        g ty = false →
        -- then `ty` never evaluates to something.
        ∀ env: Env, Φ_eval ty env = none
    )

-- Represents all correct G functions from the paper.
def Gs [@GuardSemantic Grd Env] := { g : @Φ Grd → bool // (@is_correct Grd Env _) g }



-- Removes a list of leaves from a guard tree.
-- Returns `none` if the guard tree is empty.
def remove_leaves [decidable_eq Leaf] : list Leaf → (@Gdt Grd Leaf) → option (@Gdt Grd Leaf)
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
-- Catches the semantic of an empty guard tree.
def ngdt_eval_option [@GuardSemantic (@XGrd Grd Var) Env] : option (@NGdt Grd Leaf Var) → Env → (option (Env × (@NLeaf Leaf)))
| (some gdt) env := ngdt_eval gdt env
| none env := none

-- Every redundant leaf can be marked as inaccessible instead and
-- every inaccessible leaf can be marked as accessible instead without invalidating the theorem. This only weakens the analysis.

theorem main [decidable_eq Leaf] [@GuardSemantic (@XGrd Grd Var) Env] : ∀ gdt: @NGdt Grd Leaf Var, ∀ is_empty: (@Gs (@XGrd Grd Var) Env _),
    (
        let ⟨ a, i, r ⟩ := ℛ is_empty.val $ 𝒜 $ ngdt_to_gdt gdt
        in
                -- leaves that are redundant and neither accessible nor inaccessible can be removed without changing semantics
                ∀ env: Env,
                    ngdt_eval_option (remove_leaves ((r.remove_all i).remove_all a) gdt) env
                    = ngdt_eval gdt env
            ∧ 
                -- reachable leaves are accessible.
                -- Since R is clearly a partition for disjoint leaves,
                -- this also means that non-accessible leaves are unreachable.
                ∀ env: Env,
                    (match ngdt_eval gdt env with
                    | (some ⟨ _, NLeaf.leaf leaf ⟩) := leaf ∈ a
                    | _ := true
                    end : Prop)
        : Prop
    )
    -- We probably need 𝒜_eval for proving this.
    := sorry


end NGdt