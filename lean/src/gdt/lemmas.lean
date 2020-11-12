import .defs

variable [GuardModule]
open GuardModule

lemma Φ_true_and (ty: Φ): Φ_eval (Φ.true.and ty) = Φ_eval ty :=
begin
    funext env,
    unfold Φ_eval
end


lemma Φ_false_and (ty: Φ): Φ_eval Φ.false = Φ_eval (ty.and Φ.false) :=
begin
    funext env,
    unfold Φ_eval,
    cases (Φ_eval ty env),
    repeat { unfold Φ_eval._match_3 }
end

lemma Φ_and_assoc (ty1: Φ) (ty2: Φ) (ty3: Φ):
    Φ_eval ((ty1.and ty2).and ty3) = Φ_eval (ty1.and (ty2.and ty3)) :=
begin
    funext env,
    rw Φ_eval,
    
    simp,
    cases h: (Φ_eval (ty1.and ty2) env),
    repeat {
        rw Φ_eval,
        simp,
        rw Φ_eval at h,
        simp at h,
        cases h2: (Φ_eval ty1 env),
        repeat {
            rw Φ_eval._match_3,
        },
    },
    
    repeat {
        rw h2 at h,
        rw Φ_eval._match_3 at h,
    },

    case option.none option.some {
        rw Φ_eval, simp,
        rw h,
        rw Φ_eval._match_3, 
    },
    
    case option.some option.none {
        cc,
    },

    case option.some option.some {
        rw Φ_eval, simp, rw h,
        rw Φ_eval._match_3,
    }
end

lemma Φ_and_or_distrib (ty1: Φ) (ty2: Φ) (ty3: Φ):
    Φ_eval ((ty1.and ty2).or (ty1.and ty3)) = Φ_eval (ty1.and (ty2.or ty3)) :=
begin
    funext env,
    unfold Φ_eval, simp,
    cases (Φ_eval ty1 env),
        unfold Φ_eval._match_3,
        unfold Φ_eval._match_2,

        unfold Φ_eval._match_3,
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


lemma 𝒰_𝒰'_equiv' (acc: Φ) (gdt: Gdt) :
    Φ_eval (𝒰_acc acc gdt) = Φ_eval (Φ.and acc (𝒰' gdt)) :=
begin
    funext env,
    induction gdt generalizing acc,

    -- case leaf
    unfold 𝒰_acc,
    unfold 𝒰',
    rw Φ_false_and,

    -- case branch
    
    unfold 𝒰_acc,
    rw gdt_ih_a_1,
    rw Φ_eval,
    rw gdt_ih_a,
    rw← Φ_eval,
    unfold 𝒰',
    rw Φ_and_assoc,

    -- case grd
    rw 𝒰',

    rw 𝒰_acc,
    
    rw Φ_eval,
    rw Φ_eval,
    rw gdt_ih,
    rw ←Φ_eval,
    rw ←Φ_eval,
    rw rw_right_or,
    rw Φ_and_or_distrib,
    rw Φ_and_assoc,
end


lemma 𝒰_𝒰'_equiv : Φ_eval ∘ 𝒰 = Φ_eval ∘ 𝒰' := 
begin
    unfold function.comp,
    funext x,
    rw 𝒰,
    rw ←Φ_true_and (𝒰' x),
    rw 𝒰_𝒰'_equiv'
end

