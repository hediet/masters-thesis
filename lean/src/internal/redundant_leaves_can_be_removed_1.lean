import tactic
import ..definitions
import .helper_defs
import data.finset

variable [GuardModule]
open GuardModule

lemma redundant_leaves_can_be_removed'
    (can_prove_empty: Gs)
    (gdt: Gdt) (gdt_disjoint: gdt.disjoint_leaves)
    -- We only focus on a very particular environment `env`.
    (env ant_env: Env)
    (ant: Ant Φ) (ant_def: ant.eval_leaves ant_env = (A gdt).eval_leaves env)
    (r: LeafPartition) (r_def: r = R can_prove_empty.val ant)
    (leaves: finset Leaf) (leaves_def: leaves ⊆ r.red.to_finset):

    -- We could also show that we can remove all leaves except the one we ended up with.
        Gdt.eval_option (gdt.remove_leaves leaves) env = gdt.eval env :=
begin
  sorry,
end


lemma redundant_leaves_can_be_removed
    (is_empty: Gs)
    (gdt: Gdt) (gdt_disjoint: gdt.disjoint_leaves):
    Gdt.eval_option (gdt.remove_leaves ((R is_empty.val (A gdt)).red.to_finset)) = gdt.eval :=
begin
    ext env:1,

    set r := (R is_empty.val (A gdt)) with r_def,
    have: (R is_empty.val (A gdt)).red.to_finset ⊆ r.red.to_finset, {
        simp [r_def],
    },

    exact redundant_leaves_can_be_removed' is_empty gdt gdt_disjoint env env  (A gdt)
        (refl ((A gdt).eval_leaves env)) r r_def ((R is_empty.val (A gdt)).red.to_finset) this,
end
    
