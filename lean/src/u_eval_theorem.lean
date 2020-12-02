import tactic
import .defs
import .lemmas

variable [GuardModule]
open GuardModule

def is_no_match : Result → bool
| Result.no_match := tt
| _ := ff

local attribute [simp] gdt_eval._match_1 gdt_eval._match_2 Φ_eval._match_2

-- Uncovered refinement types capture all values that are not covered.
-- This theorem might be easier to show for 𝒰' rather than 𝒰.
theorem 𝒰_eval :
    ∀ gdt: Gdt, ∀ env: Env,
        Φ_eval (𝒰 gdt) env = (is_no_match (gdt_eval gdt env)):= 
begin
    assume gdt: Gdt,
    assume env: Env,

    rw 𝒰_𝒰'_equiv,
 
    induction gdt with leaf generalizing env,

    case Gdt.leaf {
        finish,
    },
  
    case Gdt.branch {
        unfold 𝒰',
        unfold gdt_eval,
        unfold Φ_eval,

        cases c1: (Φ_eval (𝒰' gdt_tr1) env),
        all_goals {
            simp,
            specialize gdt_ih_tr1 env,
            rw c1 at gdt_ih_tr1,
            cases gdt_eval gdt_tr1 env;
            finish,
        },
    },

    case Gdt.grd {
        cases gdt_grd,
        all_goals {
            unfold 𝒰',
            unfold gdt_eval,
            unfold Φ_eval,
        },
        {
            cases (xgrd_eval gdt_grd env),
            case option.none {
                finish,
            },
            case option.some {
                specialize gdt_ih val,
                exact gdt_ih,
            }
        },

        {
            cases (is_bottom gdt_grd env),
            case bool.ff {
                specialize gdt_ih env,
                exact gdt_ih,
            },
            case bool.tt {
                finish,
            },
        }
    },
end
