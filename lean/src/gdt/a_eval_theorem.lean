import .defs

variable [GuardModule]
open GuardModule

-- 𝒜 maintains semantics
-- This theorem implies that ant_eval returns a list of length at most 1.
-- This means that the refinement types created by 𝒜 are disjoint.
theorem 𝒜_eval :
    ∀ env: Env, ∀ gdt: Gdt,
        (option_to_list $ gdt_eval gdt env) = ant_eval (𝒜 gdt) env := sorry