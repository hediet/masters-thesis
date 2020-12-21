import .definitions
import .internal.helper_defs
import .internal.U_semantic

variable [GuardModule]
open GuardModule

theorem 𝒰_semantic: ∀ gdt: Gdt, ∀ env: Env,
        (𝒰 gdt).eval env ↔ (gdt.eval env = Result.no_match) :=
begin
    assume gdt env,
    rw ←@U_eq_𝒰,
    simp [U_semantic],
end

theorem ℛ_semantic : ∀ is_empty: Gs, ∀ gdt: Gdt, gdt.disjoint_leaves → 
    (
        let ⟨ a, i, r ⟩ := ℛ is_empty.val (𝒜 gdt)
        in
                -- Redundant leaves can be removed without changing semantics.
                Gdt.eval_option (gdt.remove_leaves r.to_finset)
                = gdt.eval
            ∧ 
                -- Reachable leaves are accessible and neither inaccessible nor redundant.
                ∀ env: Env, ∀ leaf: Leaf,
                    gdt.eval env = Result.leaf leaf
                      → leaf ∈ a \ i \ r
        : Prop
    )
    :=
begin
    sorry
end
