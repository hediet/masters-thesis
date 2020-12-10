import tactic
import ..definitions
import .gdt_stable
import .gdt_hom
import data.finset

variable [GuardModule]
open GuardModule

-- Simpler definition of 𝒰 that does not need an accumulator
def U : Gdt → Φ
| (Gdt.leaf _) := Φ.false
| (Gdt.branch tr1 tr2) := (U tr1).and (U tr2)
| (Gdt.grd (Grd.bang var) tree) := ((Φ.var_is_not_bottom var).and (U tree))
| (Gdt.grd (Grd.xgrd grd) tree) :=
                (Φ.not_xgrd grd)
            .or
                (Φ.xgrd_in grd (U tree))

lemma U_eq_𝒰_acc { gdt: Gdt } { acc: Φ → Φ } (acc_stable: stable acc) (acc_hom: homomorphic acc) : (acc (U gdt)).eval = (𝒰_acc acc gdt).eval :=
begin
    induction gdt generalizing acc,
    
    case Gdt.leaf {
        simp [𝒰_acc, U],
    },

    case Gdt.branch {
        have : (𝒰_acc id gdt_tr1).eval = (id (U gdt_tr1)).eval := begin
            simp [←gdt_ih_tr1, id_stable, id_hom],
        end,
        have : ((𝒰_acc id gdt_tr1).and (U gdt_tr2)).eval = ((id (U gdt_tr1)).and (U gdt_tr2)).eval := begin
            rw stable_app and_left_stable this,
        end,
        simp [𝒰_acc, U, ←gdt_ih_tr2 (stable_comp acc_stable and_right_stable) (comp_hom acc_hom acc_stable and_right_hom and_right_stable),
            function.comp, stable_app acc_stable this],
    },

    case Gdt.grd {
        cases gdt_grd,
        
        case Grd.xgrd {
            ext env,
            simp [𝒰_acc, U],
            rw acc_hom,
            have : (𝒰_acc (acc ∘ Φ.xgrd_in gdt_grd) gdt_tr).eval = (acc (Φ.xgrd_in gdt_grd (U gdt_tr))).eval := begin
                simp [←gdt_ih (stable_comp acc_stable (xgrd_in_stable _))
                    (comp_hom acc_hom acc_stable (xgrd_in_hom gdt_grd) (xgrd_in_stable gdt_grd))],
            end,
            rw stable_app or_right_stable this,
        },

        case Grd.bang {
            simp [𝒰_acc, U, ←gdt_ih (stable_comp acc_stable and_right_stable) (comp_hom acc_hom acc_stable and_right_hom and_right_stable)],
        },
    },
end

lemma U_eq_𝒰 (gdt: Gdt) : (U gdt).eval = (𝒰 gdt).eval :=
begin
    ext env,
    simp [𝒰, ←U_eq_𝒰_acc (id_stable) (id_hom)],
end


def Ant.map { α : Type } { β : Type } : (α → β) → Ant α → Ant β
| f (Ant.leaf a leaf) := Ant.leaf (f a) leaf
| f (Ant.branch tr1 tr2) := (Ant.branch (tr1.map f) (tr2.map f))
| f (Ant.diverge a tr) := (Ant.diverge (f a) (tr.map f))

def Ant.map_option { α : Type } { β : Type } : (α → β) → option (Ant α) → option (Ant β)
| f (some ant) := some (ant.map f)
| f none := none

def Ant.eval_leaves (ant: Ant Φ) (env: Env) := ant.map (λ ty, ty.eval env)

-- This is a simpler definition of 𝒜 that is semantically equivalent.
def A : Gdt → Ant Φ
| (Gdt.leaf leaf) := Ant.leaf Φ.true leaf
| (Gdt.branch tr1 tr2) := Ant.branch (A tr1) $ (A tr2).map ((U tr1).and)
| (Gdt.grd (Grd.bang var) tr) := Ant.diverge (Φ.var_is_bottom var) $ (A tr).map ((Φ.var_is_not_bottom var).and)
| (Gdt.grd (Grd.xgrd grd) tr) := (A tr).map (Φ.xgrd_in grd)

def Ant.leaves { α: Type }: Ant α → finset Leaf
| (Ant.leaf a leaf) := { leaf }
| (Ant.branch tr1 tr2) := Ant.leaves tr1 ∪ Ant.leaves tr2
| (Ant.diverge a tr) := Ant.leaves tr


-- (accessible, inaccessible, redundant)
structure LeafPartition := mk :: (acc : list Leaf) (inacc : list Leaf) (red : list Leaf)

def R' : Ant bool → LeafPartition
| (Ant.leaf can_prove_empty n) := if can_prove_empty then ⟨ [], [], [n] ⟩ else ⟨ [n], [], [] ⟩
| (Ant.diverge can_prove_empty tr) := 
    match R' tr, can_prove_empty with
    | ⟨ [], [], m :: ms ⟩, ff := ⟨ [], [m], ms ⟩
    | r, _ := r
    end
| (Ant.branch tr1 tr2) :=
    let r1 := R' tr1, r2 := R' tr2 in
        ⟨ r1.acc ++ r2.acc, r1.inacc ++ r2.inacc, r1.red ++ r2.red ⟩

/-
    This definition is much easier to use than ℛ, but equal to ℛ.
    * Associativity of `Ant.map` can be utilized.
    * LeafPartition is much easier to use than triples.
    * Ant.branch has no match which would require a case distinction.
-/
def R (can_prove_empty: Φ → bool) (ant: Ant Φ): LeafPartition := R' (ant.map can_prove_empty)

def to_triple (p: LeafPartition): (list Leaf × list Leaf × list Leaf) :=
    (p.acc, p.inacc, p.red)

lemma R_eq_ℛ (can_prove_empty: Φ -> bool) (ant: Ant Φ): to_triple (R can_prove_empty ant) = ℛ can_prove_empty ant :=
begin
    induction ant,
    case Ant.leaf {
        cases c: can_prove_empty ant_a;
        simp [R, R', R'._match_1, ℛ, ℛ._match_1, Ant.map, ℛ._match_2, to_triple, c],
    },
    
    case Ant.branch {
        rw ℛ,
        rw ←ant_ih_tr1,
        rw ←ant_ih_tr2,
        
        cases ℛ can_prove_empty ant_tr1 with a1 ir1;
        cases ir1 with i1 r1;
        cases ℛ can_prove_empty ant_tr2 with a2 ir2;
        cases ir2 with i2 r2;

        simp [R, R', R'._match_1, ℛ, ℛ._match_1, Ant.map, ℛ._match_2, to_triple],
    },

    case Ant.diverge {
        rw ℛ,
        rw ←ant_ih,

        cases c1: can_prove_empty ant_a;
        cases c: (R' (Ant.map can_prove_empty ant_tr));
        cases acc;
        cases inacc;
        cases red;

        simp [R, R', R'._match_1, ℛ, ℛ._match_1, Ant.map, ℛ._match_2, to_triple, c1, c],
    },
end

