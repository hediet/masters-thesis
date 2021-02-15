import tactic
import ..definitions
import data.finset

variable [GuardModule]
open GuardModule

def Result.is_match { α: Type } : Result α → bool
| Result.no_match := ff
| _ := tt

-- ######################## Gdt ########################

-- Simpler definition of 𝒰 that does not need an accumulator
def U : Gdt → Φ
| (Gdt.rhs _) := Φ.false
| (Gdt.branch tr1 tr2) := (U tr1).and (U tr2)
| (Gdt.grd (Grd.bang var) tree) := ((Φ.var_is_not_bottom var).and (U tree))
| (Gdt.grd (Grd.tgrd grd) tree) :=
                (Φ.not_tgrd grd)
            .or
                (Φ.tgrd_in grd (U tree))

def U'_acc : (Φ → Φ) → Gdt → Φ
| acc (Gdt.rhs _) := acc Φ.false
| acc (Gdt.branch tr1 tr2) := acc (U'_acc ((U'_acc id tr1).and) tr2)
| acc (Gdt.grd (Grd.bang var) tr) :=
    U'_acc (acc ∘ (Φ.var_is_not_bottom var).and) tr
| acc (Gdt.grd (Grd.tgrd grd) tr) :=
		acc (
				((Φ.not_tgrd grd))
			.or
				(U'_acc (Φ.tgrd_in grd) tr)
		)

def U' := U'_acc id

def Gdt.mark_all_rhss_inactive: Gdt → Ant bool
| (Gdt.rhs rhs) := Ant.rhs tt rhs 
| (Gdt.branch tr1 tr2) := Ant.branch tr1.mark_all_rhss_inactive tr2.mark_all_rhss_inactive
| (Gdt.grd (Grd.tgrd _) tr) := tr.mark_all_rhss_inactive
| (Gdt.grd (Grd.bang _) tr) := Ant.diverge tt tr.mark_all_rhss_inactive

def Gdt.mark_inactive_rhss : Gdt → Env → Ant bool
| (Gdt.rhs rhs) env := Ant.rhs ff rhs 
| (Gdt.branch tr1 tr2) env :=
    Ant.branch (tr1.mark_inactive_rhss env) (
        if (tr1.eval env).is_match then
            (tr2.mark_all_rhss_inactive)
        else
            (tr2.mark_inactive_rhss env)
    )
| (Gdt.grd (Grd.tgrd grd) tr) env :=
    match tgrd_eval grd env with
    | none := tr.mark_all_rhss_inactive
    | some env' := tr.mark_inactive_rhss env'
    end
| (Gdt.grd (Grd.bang var) tr) env :=
    if is_bottom var env
    then Ant.diverge ff (tr.mark_all_rhss_inactive)
    else Ant.diverge tt (tr.mark_inactive_rhss env)

-- ######################## Ant ########################

def Ant.rhss_list { α: Type }: Ant α → list Rhs
| (Ant.rhs a rhs) := [ rhs ]
| (Ant.branch tr1 tr2) := Ant.rhss_list tr1 ++ Ant.rhss_list tr2
| (Ant.diverge a tr) := Ant.rhss_list tr

def Ant.rhss { α: Type } (ant: Ant α): finset Rhs := ant.rhss_list.to_finset

def Ant.disjoint_rhss { α: Type } : Ant α → Prop
| (Ant.rhs _ rhs) := true
| (Ant.branch tr1 tr2) := tr1.disjoint_rhss ∧ tr2.disjoint_rhss ∧ disjoint tr1.rhss tr2.rhss
| (Ant.diverge _ tr) := tr.disjoint_rhss

def Ant.map { α β: Type } : (α → β) → Ant α → Ant β
| f (Ant.rhs a rhs) := Ant.rhs (f a) rhs
| f (Ant.branch tr1 tr2) := (Ant.branch (tr1.map f) (tr2.map f))
| f (Ant.diverge a tr) := (Ant.diverge (f a) (tr.map f))
-- TODO: functor implementieren? f <$> ant

def Ant.map_option { α β: Type } : (α → β) → option (Ant α) → option (Ant β)
| f (some ant) := some (ant.map f)
| f none := none
-- TODO: fmap?

def Ant.eval_rhss (ant: Ant Φ) (env: Env): Ant bool := ant.map (λ ty, ty.eval env)

def Ant.mark_inactive_rhss (ant: Ant Φ) (env: Env) := ant.map (λ ty, !(ty.eval env))

def Ant.inactive_rhss : Ant bool → finset Rhs
| (Ant.rhs inactive n) := if inactive then { n } else ∅
| (Ant.diverge inactive tr) := tr.inactive_rhss
| (Ant.branch tr1 tr2) := tr1.inactive_rhss ∪ tr2.inactive_rhss

inductive Ant.implies: Ant bool → Ant bool → Prop
| rhs { a b: bool } { rhs } (h: a → b):
    Ant.implies (Ant.rhs a rhs) (Ant.rhs b rhs)
| branch { a_tr1 a_tr2 b_tr1 b_tr2 } (h1: Ant.implies a_tr1 b_tr1) (h2: Ant.implies a_tr2 b_tr2):
    Ant.implies (Ant.branch a_tr1 a_tr2) (Ant.branch b_tr1 b_tr2)
| diverge { a b: bool } { a_tr b_tr } (h1: Ant.implies a_tr b_tr) (h2: a → b):
    Ant.implies (Ant.diverge a a_tr) (Ant.diverge b b_tr)

infix `⟶`: 50 := Ant.implies

def Ant.critical_rhs_sets : Ant bool → finset (finset Rhs)
| (Ant.rhs inactive n) := ∅
| (Ant.diverge inactive tr) := tr.critical_rhs_sets ∪ if inactive
    then ∅
    else { tr.rhss }
| (Ant.branch tr1 tr2) := tr1.critical_rhs_sets ∪ tr2.critical_rhs_sets

def Ant.is_redundant_set (a: Ant bool) (rhss: finset Rhs) :=
    rhss ∩ a.rhss ⊆ a.inactive_rhss
    ∧ ∀ c ∈ a.critical_rhs_sets, ∃ l ∈ c, l ∉ rhss
-- TODO: rcases

-- This is a simpler definition of 𝒜 that is semantically equivalent.
def A : Gdt → Ant Φ
| (Gdt.rhs rhs) := Ant.rhs Φ.true rhs
| (Gdt.branch tr1 tr2) := Ant.branch (A tr1) $ (A tr2).map ((U tr1).and)
| (Gdt.grd (Grd.bang var) tr) := Ant.diverge (Φ.var_is_bottom var) $ (A tr).map ((Φ.var_is_not_bottom var).and)
| (Gdt.grd (Grd.tgrd grd) tr) := (A tr).map (Φ.tgrd_in grd)

-- ######################## R ########################

-- (accessible, inaccessible, redundant)
structure RhsPartition := mk :: (acc : list Rhs) (inacc : list Rhs) (red : list Rhs)

def RhsPartition.rhss (p: RhsPartition) : list Rhs := p.acc ++ p.inacc ++ p.red

def RhsPartition.to_triple (p: RhsPartition): (list Rhs × list Rhs × list Rhs) :=
    (p.acc, p.inacc, p.red)

/-
    This definition is much easier to use than ℛ, but almost equal to ℛ.
    * Associativity of `Ant.map` can be utilized.
    * RhsPartition is much easier to use than triples.
    * Ant.branch has no match which would require a case distinction.
    * This definition can handle any `Ant bool`.
-/
def R : Ant bool → RhsPartition
| (Ant.rhs can_prove_empty n) := if can_prove_empty then ⟨ [], [], [n] ⟩ else ⟨ [n], [], [] ⟩
| (Ant.diverge can_prove_empty tr) := 
    match R tr, can_prove_empty with
    | ⟨ [], [], m :: ms ⟩, ff := ⟨ [], [m], ms ⟩
    | r, _ := r
    end
| (Ant.branch tr1 tr2) :=
    let r1 := R tr1, r2 := R tr2 in
        ⟨ r1.acc ++ r2.acc, r1.inacc ++ r2.inacc, r1.red ++ r2.red ⟩
