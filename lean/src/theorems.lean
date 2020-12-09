import .defs

variable [GuardModule]
open GuardModule

theorem 𝒰_semantic: ∀ gdt: Gdt, ∀ env: Env,
        Φ_eval (𝒰 gdt) env ↔ (gdt_eval gdt env = Result.no_match) :=
begin
  sorry
end

theorem ℛ_semantic : ∀ is_empty: Gs, ∀ gdt: Gdt, disjoint_leaves gdt → 
    (
        let ⟨ a, i, r ⟩ := ℛ is_empty.val (𝒜 gdt)
        in
                -- Redundant leaves can be removed without changing semantics.
                gdt_eval_option (gdt_remove_leaves r.to_finset gdt)
                = gdt_eval gdt
            ∧ 
                -- Reachable leaves are accessible and neither inaccessible nor redundant.
                ∀ env: Env, ∀ leaf: Leaf,
                    gdt_eval gdt env = Result.leaf leaf
                      → leaf ∈ a \ i \ r
        : Prop
    )
    :=
begin
    sorry
end
