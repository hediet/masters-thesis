import tactic
import ...definitions
import ..helper_defs
import data.finset
import ..utils
import data.list
import data.bool
import ..leaves_theory
import ..gdt_eval

open finset

variable [GuardModule]
open GuardModule

def Gdt.mark_all_leaves_inactive: Gdt → Ant bool
| (Gdt.leaf leaf) := Ant.leaf tt leaf 
| (Gdt.branch tr1 tr2) := Ant.branch tr1.mark_all_leaves_inactive tr2.mark_all_leaves_inactive
| (Gdt.grd (Grd.xgrd _) tr) := tr.mark_all_leaves_inactive
| (Gdt.grd (Grd.bang _) tr) := Ant.diverge tt tr.mark_all_leaves_inactive

@[simp]
lemma Gdt.mark_all_leaves_inactive.inactive_leaves (gdt: Gdt):
    gdt.mark_all_leaves_inactive.inactive_leaves = gdt.leaves :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.leaves, Gdt.mark_all_leaves_inactive, Ant.inactive_leaves],
end

@[simp]
lemma Gdt.mark_all_leaves_inactive.critical_leaf_sets (gdt: Gdt):
    gdt.mark_all_leaves_inactive.critical_leaf_sets = ∅ :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.leaves, Gdt.mark_all_leaves_inactive, Ant.critical_leaf_sets],
end

@[simp]
lemma Gdt.mark_all_leaves_inactive.leaves (gdt: Gdt):
    gdt.mark_all_leaves_inactive.leaves = gdt.leaves :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Gdt.leaves, Gdt.mark_all_leaves_inactive, Ant.critical_leaf_sets, Ant.leaves],
end

@[simp]
lemma Gdt.mark_all_leaves_inactive_map_false (gdt: Gdt):
    gdt.mark_all_leaves_inactive.map (λ x, tt) = gdt.mark_all_leaves_inactive :=
begin
    induction gdt;
    try { cases gdt_grd };
    simp [*, Ant.map, Gdt.mark_all_leaves_inactive],
end

def Gdt.mark_inactive_leaves : Gdt → Env → Ant bool
| (Gdt.leaf leaf) env := Ant.leaf ff leaf 
| (Gdt.branch tr1 tr2) env :=
    if (tr1.eval env).is_match then
        Ant.branch (tr1.mark_inactive_leaves env) (tr2.mark_all_leaves_inactive)
    else
        Ant.branch (tr1.mark_all_leaves_inactive) (tr2.mark_inactive_leaves env)
| (Gdt.grd (Grd.xgrd grd) tr) env :=
    match xgrd_eval grd env with
    | none := tr.mark_all_leaves_inactive
    | some env' := tr.mark_inactive_leaves env'
    end
| (Gdt.grd (Grd.bang var) tr) env :=
    if is_bottom var env
    then Ant.diverge ff (tr.mark_all_leaves_inactive)
    else Ant.diverge tt (tr.mark_inactive_leaves env)

lemma Gdt.mark_inactive_leaves_mark_all_leaves_inactive (gdt: Gdt) (env: Env):
    (gdt.mark_inactive_leaves env).map (λ x, tt) = gdt.mark_all_leaves_inactive :=
begin
    induction gdt generalizing env;
    try { cases gdt_grd };
    try { cases c: (gdt_tr1.eval env).is_match };
    try { cases c: (xgrd_eval gdt_grd env) };
    try { cases c: is_bottom gdt_grd env };
    simp [*, Gdt.leaves, Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, Ant.leaves, Ant.map],
end

@[simp]
lemma Gdt.mark_inactive_leaves.leaves (gdt: Gdt) (env: Env):
    (gdt.mark_inactive_leaves env).leaves = gdt.leaves :=
begin
    induction gdt generalizing env;
    try { cases gdt_grd };
    try { cases c: (gdt_tr1.eval env).is_match };
    try { cases c: (xgrd_eval gdt_grd env) };
    try { cases c: is_bottom gdt_grd env };
    simp [*, Gdt.leaves, Gdt.mark_inactive_leaves, Ant.critical_leaf_sets, Ant.leaves],
end


lemma Gdt.mark_inactive_leaves_no_match { env: Env } { gdt: Gdt } (h: gdt.eval env = Result.no_match):
    gdt.mark_inactive_leaves env = gdt.mark_all_leaves_inactive :=
begin
    induction gdt with leaf generalizing env,
    case Gdt.leaf {
        finish [Gdt.eval],
    },
    case Gdt.branch {
        simp [
            Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive,
            gdt_eval_branch_no_match.1 h, *
        ],
    },
    case Gdt.grd {
        cases gdt_grd with gdt_grd var,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env, {
                simp [Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, c],
            }, {
                rw [grd_eval_xgrd_some c] at h,
                simp [Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, c, gdt_ih h],
            },
        },
        case Grd.bang {
            simp [Gdt.mark_inactive_leaves, Gdt.mark_all_leaves_inactive, grd_eval_bang_no_match.1 h, gdt_ih],
        }
    }
end

lemma sets_1 { α: Type } [decidable_eq α] { l1 l2 l3 l4: finset α }
    (h1: l4 ∩ (l1 ∪ l2) ⊆ l1 ∪ l3)
    (h2: disjoint l1 l2)
    : l4 ∩ l2 ⊆ l3 :=
begin
    rw finset.subset_iff,
    simp,
    assume x h3 h4,

    rw finset.subset_iff at h1,
    specialize @h1 x,
    simp at h1,

    simp [finset.disjoint_iff_inter_eq_empty, finset.subset.antisymm_iff, finset.subset_iff] at h2,
    specialize @h2 x,

    tauto, 
end

lemma sets_2 { α: Type } [decidable_eq α] { l1 l2 l3 l4: finset α }
    (h1: l4 ∩ (l1 ∪ l2) ⊆ l3 ∪ l2)
    (h2: disjoint l1 l2)
    : l4 ∩ l1 ⊆ l3 :=
begin
    rw finset.subset_iff,
    simp,
    assume x h3 h4,

    rw finset.subset_iff at h1,
    specialize @h1 x,
    simp at h1,

    simp [finset.disjoint_iff_inter_eq_empty, finset.subset.antisymm_iff, finset.subset_iff] at h2,
    specialize @h2 x,

    tauto, 
end

lemma inactive_leaves_can_be_removed
    (gdt: Gdt) (gdt_disjoint: gdt.disjoint_leaves)
    -- We only focus on a very particular environment `env`.
    (env: Env)
    
    (leaves: finset Leaf) (leaves_def: can_be_removed (gdt.mark_inactive_leaves env) leaves):

        Gdt.eval_option (gdt.remove_leaves leaves) env = gdt.eval env :=
begin
  induction gdt with leaf generalizing env,
  case Gdt.leaf {
      simp [Gdt.eval],
      unfold Gdt.mark_inactive_leaves can_be_removed at leaves_def,
      simp [Ant.inactive_leaves, Ant.critical_leaf_sets] at leaves_def,
      sorry,
  },

  case Gdt.branch {
        simp [Gdt.mark_inactive_leaves] at leaves_def,
        cases (gdt_tr1.eval env).is_match,
        case bool.ff {
            simp [Ant.inactive_leaves, Gdt.mark_inactive_leaves, can_be_removed, Ant.critical_leaf_sets ] at leaves_def,
            simp [Ant.leaves] at leaves_def,

            unfold Gdt.remove_leaves,
            unfold Gdt.disjoint_leaves at gdt_disjoint,

            have : can_be_removed (gdt_tr2.mark_inactive_leaves env) leaves :=
            begin
                have := sets_1 leaves_def.1 gdt_disjoint.2.2,
                unfold can_be_removed,
                split, { simp [*], },
                exact leaves_def.2,
            end,

            specialize gdt_ih_tr2 gdt_disjoint.2.1 env this,
            sorry,
        },
        case bool.tt {
            simp [Ant.inactive_leaves, Gdt.mark_inactive_leaves, can_be_removed, Ant.critical_leaf_sets ] at leaves_def,
            simp [Ant.leaves] at leaves_def,

            unfold Gdt.remove_leaves,
            unfold Gdt.disjoint_leaves at gdt_disjoint,

            have : can_be_removed (gdt_tr1.mark_inactive_leaves env) leaves :=
            begin
                unfold can_be_removed,
                simp,
                have := sets_2 leaves_def.1 gdt_disjoint.2.2,
                split, { simp [*], },
                exact leaves_def.2,
            end,
            specialize gdt_ih_tr1 gdt_disjoint.1 env this,
            sorry,
        },
    },

    case Gdt.grd {
        unfold Gdt.disjoint_leaves at gdt_disjoint,
        cases gdt_grd with gdt_grd var,
        case Grd.xgrd {
            cases c: xgrd_eval gdt_grd env with env',
            case option.some {
                simp [grd_eval_xgrd_some c],
                unfold can_be_removed at leaves_def,
                simp only [Gdt.mark_inactive_leaves, Gdt.mark_inactive_leaves._match_1, c] at leaves_def,
                rw ←can_be_removed at leaves_def,
                specialize gdt_ih gdt_disjoint env' leaves_def,
                unfold Gdt.remove_leaves,
                sorry,
            },
            case option.none {
                simp [grd_eval_xgrd_none c],
                unfold Gdt.remove_leaves,
                sorry,
            },
        },
        case Grd.bang {
            cases c: is_bottom var env,
            case bool.tt {
                simp [grd_eval_bang_bottom c],
                simp [can_be_removed, Gdt.leaves, Ant.leaves, Ant.inactive_leaves, Ant.critical_leaf_sets, Gdt.mark_inactive_leaves, c] at leaves_def,
                unfold Gdt.remove_leaves,
                sorry,
            },
            case bool.ff {
                simp [can_be_removed, Gdt.leaves, Gdt.mark_inactive_leaves, c, Ant.leaves, Ant.inactive_leaves, Ant.critical_leaf_sets] at leaves_def,
                have : can_be_removed (gdt_tr.mark_inactive_leaves env) leaves, {
                    simp [can_be_removed, Gdt.leaves, Gdt.mark_inactive_leaves, c, Ant.leaves, Ant.inactive_leaves, Ant.critical_leaf_sets],
                    exact leaves_def,
                },
                specialize gdt_ih gdt_disjoint env this,
                unfold Gdt.remove_leaves,
                simp [grd_eval_bang_not_bottom c],
                sorry,
            },
        },
    },
end
