import .defs

variable [GuardModule]
open GuardModule

lemma Φ_true_and (ty: Φ): Φ_eval (Φ.true.and ty) = Φ_eval ty :=
begin
    funext env,
    unfold Φ_eval,
    simp,
end


lemma Φ_false_and (ty: Φ): Φ_eval Φ.false = Φ_eval (ty.and Φ.false) :=
begin
    funext env,
    unfold Φ_eval,
    cases (Φ_eval ty env),
    all_goals { simp },
end

/- TODO
lemma Φ_and_assoc (ty1: Φ) (ty2: Φ) (ty3: Φ):
    Φ_eval ((ty1.and ty2).and ty3) = Φ_eval (ty1.and (ty2.and ty3)) :=
begin
    funext env,
    rw Φ_eval,
    conv in ( Φ_eval (ty1.and (ty2.and ty3)) env) { rw Φ_eval },
    simp,
    cases h1: (Φ_eval (ty1.and ty2) env),
    all_goals {
        rw Φ_eval at h1,
        simp at h1,
        cases h2: (Φ_eval ty1 env),
        repeat {
            rw Φ_eval._match_3,
        },
    },
    
    all_goals {
        rw h2 at h1,
        rw Φ_eval._match_3 at h1,
    },

    case option.none option.some {
        rw Φ_eval, simp,
        rw h1,
        rw Φ_eval._match_3, 
    },
    
    case option.some option.none {
        cc,
    },

    case option.some option.some {
        rw Φ_eval,
        simp,
        rw h1,
        rw Φ_eval._match_3,
    }
end

lemma Φ_and_or_distrib (ty1: Φ) (ty2: Φ) (ty3: Φ):
    Φ_eval ((ty1.and ty2).or (ty1.and ty3)) = Φ_eval (ty1.and (ty2.or ty3)) :=
begin
    funext env,
    unfold Φ_eval, simp,
    cases (Φ_eval ty1 env),

    case option.none {
        unfold Φ_eval._match_3,
        unfold Φ_eval._match_2,
    },

    case option.some {
        unfold Φ_eval._match_3,
    }
end

lemma rw_right_or (ty1: Φ) (ty2: Φ) (ty3: Φ):
    (Φ_eval ty2 = Φ_eval ty3)
    → (Φ_eval (ty1.or ty2) = Φ_eval (ty1.or ty3)) :=
begin
    assume h,
    funext env,
    rw Φ_eval,
    rw Φ_eval,
    rw h,
end
-/

/- TODO
lemma 𝒰_𝒰'_equiv_acc (gdt: Gdt) (acc: Φ) :
    Φ_eval (𝒰_acc acc gdt) = Φ_eval (acc.and (𝒰' gdt)) :=
begin
    funext env,
    induction gdt generalizing acc,
    
    case Gdt.leaf {
        unfold 𝒰_acc,
        unfold 𝒰',
        rw Φ_false_and,
    },

    case Gdt.branch {
        unfold 𝒰_acc,
        rw gdt_ih_tr2,
        rw Φ_eval,
        rw Φ_eval,
        simp,
        rw gdt_ih_tr1,
        rw← Φ_eval,
        rw← Φ_eval,
        unfold 𝒰',
        rw Φ_and_assoc,
    },

    case Gdt.grd {
        cases gdt_grd,
        case Grd.xgrd {
            rw 𝒰',
            rw 𝒰_acc,
            conv in (Φ_eval ((acc.and (Φ.not_xgrd gdt_grd)).or (𝒰_acc (acc.and (Φ.xgrd gdt_grd)) gdt_tr)) env) { rw Φ_eval },
            rw gdt_ih,
            rw ←Φ_eval,
            rw rw_right_or,
            rw Φ_and_or_distrib,
            rw Φ_and_assoc,
        },
        case Grd.bang {
            rw 𝒰',
            rw 𝒰_acc,
            rw gdt_ih,
            rw Φ_and_assoc,
        }
    },
end


lemma 𝒰_𝒰'_equiv (gdt: Gdt) : Φ_eval (𝒰 gdt) = Φ_eval (𝒰' gdt) := 
begin
    rw 𝒰,
    rw ←Φ_true_and (𝒰' gdt),
    rw 𝒰_𝒰'_equiv_acc
end
-/

lemma 𝒰_𝒰'_equiv (gdt: Gdt) : Φ_eval (𝒰 gdt) = Φ_eval (𝒰' gdt) := 
begin
    rw 𝒰
end




/- TODO
lemma 𝒜_𝒜'_equiv_acc (gdt: Gdt) (acc: Φ) : ant_eq (𝒜_acc acc gdt) (add_clause_ant acc (𝒜' gdt)) := sorry


lemma 𝒜_𝒜'_equiv (gdt: Gdt) : ant_eq (𝒜 gdt) (𝒜' gdt) :=
begin
    unfold 𝒜,
    rw ←𝒜_𝒜'_equiv_acc,

end

-/