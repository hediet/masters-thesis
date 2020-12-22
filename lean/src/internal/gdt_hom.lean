import tactic
import ..definitions
import .gdt_stable
import data.finset

variable [GuardModule]
open GuardModule

def homomorphic (f: Φ → Φ) := ∀ ty1 ty2: Φ,
    (f (ty1.or ty2)).eval = ((f ty1).or (f ty2)).eval
    ∧ (f (ty1.and ty2)).eval = ((f ty1).and (f ty2)).eval

lemma id_hom: homomorphic id := by simp [homomorphic]

lemma and_right_hom { ty: Φ }: homomorphic ty.and :=
begin
    rw homomorphic,
    assume ty1 ty2,
    split;
    ext env;
    cases c1: ty.eval env;
    cases c2: ty1.eval env;
    cases c3: ty2.eval env;
    simp [*, Φ.eval],
end

lemma or_right_hom { ty: Φ }: homomorphic ty.or :=
begin
    rw homomorphic,
    assume ty1 ty2,
    split;
    ext env;
    cases c1: ty.eval env;
    cases c2: ty1.eval env;
    cases c3: ty2.eval env;
    simp [*, Φ.eval],
end

lemma xgrd_in_hom (grd: XGrd): homomorphic (Φ.xgrd_in grd) :=
begin
    rw homomorphic,
    assume ty1 ty2,
    split;
    ext env;
    cases c: xgrd_eval grd env;
    simp [*, Φ.eval],
end

lemma comp_hom { f1 f2: Φ → Φ } (f1_hom: homomorphic f1) (f1_stable: stable f1) (f2_hom: homomorphic f2) (f2_stable: stable f2): homomorphic (f1 ∘ f2) :=
begin
    unfold homomorphic,
    assume ty1 ty2,
    unfold function.comp,
    
    have h1: (f2 (ty1.or ty2)).eval = ((f2 ty1).or (f2 ty2)).eval := by simp [f2_hom _ _],
    have h2: (f2 (ty1.and ty2)).eval = ((f2 ty1).and (f2 ty2)).eval := by simp [f2_hom _ _],

    rw stable_app f1_stable h1,
    rw stable_app f1_stable h2,
    rw (f1_hom _ _).1,
    rw (f1_hom _ _).2,
    simp,
end
