import .defs
variable [NGuardModule]
open NGuardModule

-- Reduction to Guard Trees maintains semantic.
theorem ngdt_eval_eq_gdt_eval :
        ngdt_eval = gdt_eval ∘ ngdt_to_gdt := sorry


-- Every redundant leaf can be marked as inaccessible instead and
-- every inaccessible leaf can be marked as accessible instead without invalidating the theorem. This only weakens the analysis.

theorem main [decidable_eq Leaf] : ∀ ngdt: NGdt, ∀ is_empty: Gs,
    (
        let ⟨ a, i, r ⟩ := ℛ is_empty.val $ 𝒜 $ ngdt_to_gdt ngdt
        in
                -- leaves that are redundant and neither accessible nor inaccessible can be removed without changing semantics
                ngdt_eval_option (remove_leaves ((r.remove_all i).remove_all a) ngdt)
                = ngdt_eval ngdt
            ∧ 
                -- reachable leaves are accessible.
                -- Since R is clearly a partition for disjoint leaves,
                -- this also means that non-accessible leaves are unreachable.
                ∀ env: Env,
                    (match ngdt_eval ngdt env with
                    | (some ⟨ _, NLeaf.leaf leaf ⟩) := leaf ∈ a
                    | _ := true
                    end : Prop)
        : Prop
    )
    -- We probably need 𝒜_eval for proving this.
    := sorry

