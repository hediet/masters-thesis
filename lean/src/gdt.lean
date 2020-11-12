-- # Abstract Guard Trees
-- This chapter covers basic guard trees with abstract guards.

namespace gdt

class GuardModule :=
    -- Represents the type of all guards.
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

-- ## Guard Trees

-- A guard tree is a tree of leaves, protected by (abstract) guards.
-- Every execution terminates with a leave. Guards "guard" sub-trees in a non-leathal way!
-- See non-strict guards for how a bang guard can be transformed to terminate execution.
inductive Gdt
| leaf : Leaf → Gdt
| branch : Gdt → Gdt → Gdt
| grd : Grd → Gdt → Gdt

-- Semantics of Guard Trees. Uses the semantic of guards.
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
            (Φ.and acc $ Φ.negGrd grd)
            (𝒰_acc (Φ.and acc (Φ.grd grd)) tree)

def 𝒰 : Gdt → Φ := 𝒰_acc Φ.true


-- ### start: optional

-- Alternative definition without accumulator
def 𝒰' : Gdt → Φ
| (Gdt.leaf _) := Φ.false
| (Gdt.branch tr1 tr2) := Φ.and (𝒰' tr1) (𝒰' tr2)
| (Gdt.grd grd tree) := Φ.or
            (Φ.negGrd grd)
            (Φ.and (Φ.grd grd) (𝒰' tree))


lemma Φ_true_and (ty: Φ): Φ_eval (Φ.true.and ty) = Φ_eval ty :=
begin
    funext env,
    unfold Φ_eval
end


lemma Φ_false_and (ty: Φ): Φ_eval Φ.false = Φ_eval (ty.and Φ.false) :=
begin
    funext env,
    unfold Φ_eval,
    cases (Φ_eval ty env),
    repeat { unfold Φ_eval._match_3 }
end

lemma Φ_and_assoc (ty1: Φ) (ty2: Φ) (ty3: Φ):
    Φ_eval ((ty1.and ty2).and ty3) = Φ_eval (ty1.and (ty2.and ty3)) :=
begin
    funext env,
    rw Φ_eval,
    
    simp,
    cases h: (Φ_eval (ty1.and ty2) env),
    repeat {
        rw Φ_eval,
        simp,
        rw Φ_eval at h,
        simp at h,
        cases h2: (Φ_eval ty1 env),
        repeat {
            rw Φ_eval._match_3,
        },
    },
    
    repeat {
        rw h2 at h,
        rw Φ_eval._match_3 at h,
    },

    case option.none option.some {
        rw Φ_eval, simp,
        rw h,
        rw Φ_eval._match_3, 
    },
    
    case option.some option.none {
        cc,
    },

    case option.some option.some {
        rw Φ_eval, simp, rw h,
        rw Φ_eval._match_3,
    }
end

lemma Φ_and_or_distrib (ty1: Φ) (ty2: Φ) (ty3: Φ):
    Φ_eval ((ty1.and ty2).or (ty1.and ty3)) = Φ_eval (ty1.and (ty2.or ty3)) :=
begin
    funext env,
    unfold Φ_eval, simp,
    cases (Φ_eval ty1 env),
        unfold Φ_eval._match_3,
        unfold Φ_eval._match_2,

        unfold Φ_eval._match_3,
end

lemma rw_right_or (ty1: Φ) (ty2: Φ) (ty3: Φ):
    (Φ_eval ty2 = Φ_eval ty3)
    → (Φ_eval (ty1.or ty2) = Φ_eval (ty1.or ty3)) :=
begin
    assume h,
    funext env,
    rw Φ_eval,
    rw Φ_eval,
    rw h,
end


lemma 𝒰_𝒰'_equiv' (acc: Φ) (gdt: Gdt) :
    Φ_eval (𝒰_acc acc gdt) = Φ_eval (Φ.and acc (𝒰' gdt)) :=
begin
    funext env,
    induction gdt generalizing acc,

    -- case leaf
    unfold 𝒰_acc,
    unfold 𝒰',
    rw Φ_false_and,

    -- case branch
    
    unfold 𝒰_acc,
    rw gdt_ih_a_1,
    rw Φ_eval,
    rw gdt_ih_a,
    rw← Φ_eval,
    unfold 𝒰',
    rw Φ_and_assoc,

    -- case grd
    rw 𝒰',

    rw 𝒰_acc,
    
    rw Φ_eval,
    rw Φ_eval,
    rw gdt_ih,
    rw ←Φ_eval,
    rw ←Φ_eval,
    rw rw_right_or,
    rw Φ_and_or_distrib,
    rw Φ_and_assoc,
end


lemma 𝒰_𝒰'_equiv : Φ_eval ∘ 𝒰 = Φ_eval ∘ 𝒰' := 
begin
    unfold function.comp,
    funext x,
    rw 𝒰,
    rw ←Φ_true_and (𝒰' x),
    rw 𝒰_𝒰'_equiv'
end

-- ### end: optional

-- Uncovered refinement types capture all values that are not covered.
-- This theorem might be easier to show for 𝒰' rather than 𝒰.
theorem 𝒰_eval :
    ∀ env: Env, ∀ gdt: Gdt,
        (gdt_eval gdt env ≠ none) ↔ (Φ_eval (𝒰 gdt) env = none)
    := sorry



-- ## Annotate

inductive Ant
| leaf : Φ → Leaf → Ant
| branch : Ant → Ant → Ant

def 𝒜_acc : Φ → Gdt → Ant
| acc (Gdt.leaf leaf) := Ant.leaf acc leaf
| acc (Gdt.branch tr1 tr2) := Ant.branch (𝒜_acc acc tr1) (𝒜_acc (𝒰_acc acc tr1) tr2)
| acc (Gdt.grd grd tr) := (𝒜_acc (Φ.and acc $ Φ.grd grd) tr)

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

-- 𝒜 maintains semantics
-- This theorem implies that ant_eval returns a list of length at most 1.
-- This means that the refinement types created by 𝒜 are disjoint.
theorem 𝒜_eval :
    ∀ env: Env, ∀ gdt: Gdt,
        (option_to_list $ gdt_eval gdt env) = ant_eval (𝒜 gdt) env := sorry

end gdt