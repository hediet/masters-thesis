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
            rw (acc_hom _ _).1,
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

lemma U_eq_𝒰 { gdt: Gdt } : (U gdt).eval = (𝒰 gdt).eval :=
begin
    ext env,
    simp [𝒰, ←U_eq_𝒰_acc (id_stable) (id_hom)],
end


def Ant.map { α β: Type } : (α → β) → Ant α → Ant β
| f (Ant.leaf a leaf) := Ant.leaf (f a) leaf
| f (Ant.branch tr1 tr2) := (Ant.branch (tr1.map f) (tr2.map f))
| f (Ant.diverge a tr) := (Ant.diverge (f a) (tr.map f))

lemma Ant.map.associative { α β γ: Type } (f: β → γ) (g: α → β) (ant: Ant α):
    (ant.map g).map f = ant.map (f ∘ g) :=
begin
    induction ant;
    simp [*, Ant.map],
end

def Ant.map_option { α β: Type } : (α → β) → option (Ant α) → option (Ant β)
| f (some ant) := some (ant.map f)
| f none := none

def Ant.eval_leaves (ant: Ant Φ) (env: Env) := ant.map (λ ty, ty.eval env)

-- This is a simpler definition of 𝒜 that is semantically equivalent.
def A : Gdt → Ant Φ
| (Gdt.leaf leaf) := Ant.leaf Φ.true leaf
| (Gdt.branch tr1 tr2) := Ant.branch (A tr1) $ (A tr2).map ((U tr1).and)
| (Gdt.grd (Grd.bang var) tr) := Ant.diverge (Φ.var_is_bottom var) $ (A tr).map ((Φ.var_is_not_bottom var).and)
| (Gdt.grd (Grd.xgrd grd) tr) := (A tr).map (Φ.xgrd_in grd)

def A_eq_𝒜 { gdt: Gdt } { acc: Φ → Φ } (acc_stable: stable acc) (acc_hom: homomorphic acc):
    ((A gdt).map acc).eval_leaves = (𝒜_acc acc gdt).eval_leaves :=
begin
    ext env,
    induction gdt generalizing acc env,
    case Gdt.leaf { simp [A, Ant.map, 𝒜_acc], },
    case Gdt.branch {
        unfold 𝒜_acc,
        unfold Ant.eval_leaves,
        unfold Ant.map,
        rw ←Ant.eval_leaves,
        rw ←Ant.eval_leaves,
        rw ←Ant.eval_leaves,
        
        specialize gdt_ih_tr1 env acc_stable acc_hom,
        rw ←gdt_ih_tr1,
        
        specialize @gdt_ih_tr2 ((𝒰_acc acc gdt_tr1).and ∘ acc) env
            (stable_comp and_right_stable acc_stable)
            (comp_hom and_right_hom and_right_stable acc_hom acc_stable),
        rw ←gdt_ih_tr2,

        simp [Ant.map, A, Ant.eval_leaves, Ant.map.associative, function.comp, Φ.eval, (acc_hom _ _).2, U_eq_𝒰_acc acc_stable acc_hom],
    },
    case Gdt.grd {
        cases gdt_grd,        
        case Grd.xgrd {
            unfold A 𝒜_acc Ant.map,
            specialize @gdt_ih (acc ∘ Φ.xgrd_in gdt_grd) env
                (stable_comp acc_stable (xgrd_in_stable gdt_grd))
                (comp_hom acc_hom acc_stable (xgrd_in_hom gdt_grd) (xgrd_in_stable gdt_grd)),
            rw ←gdt_ih,
            rw Ant.map.associative,
        },
        case Grd.bang {
            unfold A 𝒜_acc Ant.map Ant.eval_leaves,
            rw ←Ant.eval_leaves,
            rw ←Ant.eval_leaves,
            specialize @gdt_ih (acc ∘ (Φ.var_is_not_bottom gdt_grd).and) env
                (stable_comp acc_stable and_right_stable)
                (comp_hom acc_hom acc_stable and_right_hom and_right_stable),
            rw ←gdt_ih,
            rw Ant.map.associative,
        },
    },
end

def Ant.leaves { α: Type }: Ant α → finset Leaf
| (Ant.leaf a leaf) := { leaf }
| (Ant.branch tr1 tr2) := Ant.leaves tr1 ∪ Ant.leaves tr2
| (Ant.diverge a tr) := Ant.leaves tr


-- (accessible, inaccessible, redundant)
structure LeafPartition := mk :: (acc : list Leaf) (inacc : list Leaf) (red : list Leaf)

/-
    This definition is much easier to use than ℛ, but almost equal to ℛ.
    * Associativity of `Ant.map` can be utilized.
    * LeafPartition is much easier to use than triples.
    * Ant.branch has no match which would require a case distinction.
    * This definition can handle any `Ant bool`.
-/
def R : Ant bool → LeafPartition
| (Ant.leaf can_prove_empty n) := if can_prove_empty then ⟨ [], [], [n] ⟩ else ⟨ [n], [], [] ⟩
| (Ant.diverge can_prove_empty tr) := 
    match R tr, can_prove_empty with
    | ⟨ [], [], m :: ms ⟩, ff := ⟨ [], [m], ms ⟩
    | r, _ := r
    end
| (Ant.branch tr1 tr2) :=
    let r1 := R tr1, r2 := R tr2 in
        ⟨ r1.acc ++ r2.acc, r1.inacc ++ r2.inacc, r1.red ++ r2.red ⟩

def to_triple (p: LeafPartition): (list Leaf × list Leaf × list Leaf) :=
    (p.acc, p.inacc, p.red)

lemma R_eq_ℛ (can_prove_empty: Φ → bool) (ant: Ant Φ): to_triple (R (ant.map can_prove_empty)) = ℛ can_prove_empty ant :=
begin
    induction ant,
    case Ant.leaf {
        cases c: can_prove_empty ant_a;
        simp [R, R._match_1, ℛ, ℛ._match_1, Ant.map, ℛ._match_2, to_triple, c],
    },
    
    case Ant.branch {
        rw ℛ,
        rw ←ant_ih_tr1,
        rw ←ant_ih_tr2,
        
        cases ℛ can_prove_empty ant_tr1 with a1 ir1;
        cases ir1 with i1 r1;
        cases ℛ can_prove_empty ant_tr2 with a2 ir2;
        cases ir2 with i2 r2;

        simp [R, R._match_1, ℛ, ℛ._match_1, Ant.map, ℛ._match_2, to_triple],
    },

    case Ant.diverge {
        rw ℛ,
        rw ←ant_ih,

        cases c1: can_prove_empty ant_a;
        cases c: (R (Ant.map can_prove_empty ant_tr));
        cases acc;
        cases inacc;
        cases red;
        simp [R, R._match_1, ℛ, ℛ._match_1, Ant.map, ℛ._match_2, to_triple, c1, c],
    },
end

@[simp]
lemma R_empty (tr: Ant bool) : R (Ant.diverge tt tr) = R tr :=
begin
    cases c1: R tr,
    cases c2: acc;
    cases c3: inacc;
    cases c4: red;
    simp [R, R._match_1, c1, c2, c3, c4],
end

def R_diverge { ant: Ant bool } { r: LeafPartition } (a: bool)
    (h: R ant = r):
    (∃ rh: Leaf, ∃ rs: list Leaf, a = ff ∧ r = ⟨ [], [], rh::rs ⟩ ∧ R (Ant.diverge a ant) = ⟨ [], [rh], rs ⟩)
    ∨ ((a = tt ∨ r.acc ≠ [] ∨ r.inacc ≠ [] ∨ r.red = []) ∧ R (Ant.diverge a ant) = r) :=
begin
    unfold R Ant.map,
    
    cases a;
    cases r;
    cases r_acc;
    cases r_inacc;
    cases r_red;
    simp [h, R._match_1],
end

def Ant.inactive_leaves :  Ant bool → finset Leaf
| (Ant.leaf inactive n) := if inactive then { n } else ∅
| (Ant.diverge inactive tr) := tr.inactive_leaves
| (Ant.branch tr1 tr2) := tr1.inactive_leaves ∪ tr2.inactive_leaves

lemma Ant.inactive_leaves_subset_leaves { a: Ant bool } : a.inactive_leaves ⊆ a.leaves :=
begin
    induction a,
    cases a_a,
    all_goals {
        simp [Ant.inactive_leaves, Ant.leaves, finset.union_subset_union, *],
    },
end

def Ant.critical_leaf_sets :  Ant bool → finset (finset Leaf)
| (Ant.leaf inactive n) := ∅
| (Ant.diverge inactive tr) := tr.critical_leaf_sets ∪ if inactive
    then ∅
    else { tr.leaves }
| (Ant.branch tr1 tr2) := tr1.critical_leaf_sets ∪ tr2.critical_leaf_sets

def finset.redundant_in (a: Ant bool) (leaves: finset Leaf) :=
    leaves ∩ a.leaves ⊆ a.inactive_leaves
    ∧ ∀ e ∈ a.critical_leaf_sets, ¬ e ⊆ leaves

def Result.is_match : Result → bool
| Result.no_match := ff
| _ := tt

@[simp]
lemma Result.is_match_neq_no_match (r: Result): r.is_match ↔ r ≠ Result.no_match :=
begin
    cases r;
    simp [Result.is_match],
end

@[simp]
lemma Result.not_is_match_eq_no_match (r: Result): !r.is_match ↔ r = Result.no_match :=
begin
    cases r;
    simp [Result.is_match],
end

@[simp]
lemma is_empty_implies_eval_false { can_prove_empty: Gs } { ty: Φ} { env: Env} (h: can_prove_empty.val ty = tt): ty.eval env = ff :=
begin
    have := can_prove_empty.property,
    unfold is_empty_prover at this,
    unfold Φ.is_empty at this,
    specialize this ty,
    finish [is_empty_prover],
end
