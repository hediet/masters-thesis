import tactic
import .defs
variable [GuardModule]
open GuardModule

-- (accessible, inaccessible, redundant)
structure LeafPartition := mk :: (acc : list Leaf) (inacc : list Leaf) (red : list Leaf)

def R' : Ant bool → LeafPartition
| (Ant.leaf is_empty n) := if is_empty then ⟨ [], [], [n] ⟩ else ⟨ [n], [], [] ⟩
| (Ant.diverge is_empty tr) := 
    match R' tr, is_empty with
    | ⟨ [], [], m :: ms ⟩, ff := ⟨ [], [m], ms ⟩
    | r, _ := r
    end
| (Ant.branch tr1 tr2) :=
    let r1 := R' tr1, r2 := R' tr2 in
        ⟨ r1.acc ++ r2.acc, r1.inacc ++ r2.inacc, r1.red ++ r2.red ⟩

def R (is_empty: Φ → bool) (ant: Ant Φ): LeafPartition :=
    R' (map_ant is_empty ant)

def to_triple (p: LeafPartition): (list Leaf × list Leaf × list Leaf) :=
    (p.acc, p.inacc, p.red)

lemma R_eq_ℛ (is_empty: Φ -> bool) (ant: Ant Φ): to_triple (R is_empty ant) = ℛ is_empty ant :=
begin
    induction ant,
    case Ant.leaf {
        cases c: is_empty ant_a;
        simp [R, R', R'._match_1, ℛ', ℛ, ℛ'._match_1, map_ant, ℛ'._match_2, to_triple, c],
    },
    
    case Ant.branch {
        rw ℛ,
        rw map_ant,
        rw ℛ',
        rw ←ℛ,
        rw ←ℛ,

        rw ←ant_ih_tr1,
        rw ←ant_ih_tr2,
        
        cases ℛ' (map_ant is_empty ant_tr1) with a1 ir1;
        cases ir1 with i1 r1;
        cases ℛ' (map_ant is_empty ant_tr2) with a2 ir2;
        cases ir2 with i2 r2;

        simp [R, R', R'._match_1, ℛ', ℛ, ℛ'._match_1, map_ant, ℛ'._match_2, to_triple],
    },

    case Ant.diverge {
        rw ℛ,
        rw map_ant,
        rw ℛ',
        rw ←ℛ,

        rw ←ant_ih,

        cases c1: is_empty ant_a;
        cases c: (R' (map_ant is_empty ant_tr));
        cases acc;
        cases inacc;
        cases red;

        simp [R, R', R'._match_1, ℛ', ℛ, ℛ'._match_1, map_ant, ℛ'._match_2, to_triple, c1, c],
    }
end