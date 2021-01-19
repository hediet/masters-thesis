import tactic
import ...definitions
import data.finset

meta def stable_macro: tactic unit := `[
    rw stable,
    assume ty1 ty2 h,
    ext env,
    simp [Φ.eval, h]
]

variable [GuardModule]
open GuardModule

def stable (f: Φ → Φ) := ∀ ty1 ty2: Φ, (ty1.eval = ty2.eval) → (f ty1).eval = (f ty2).eval

lemma stable.id: stable id := by simp [stable]
lemma stable.and_left { ty: Φ }: stable (λ ty', ty'.and ty) := by stable_macro
lemma stable.and_right { ty: Φ }: stable ty.and := by stable_macro
lemma stable.or_right { ty: Φ }: stable ty.or := by stable_macro
lemma stable.xgrd_in (xgrd: XGrd): stable (Φ.xgrd_in xgrd) := by stable_macro

lemma stable.app { f: Φ → Φ } (f_stable: stable f) { ty1 ty2: Φ } (h: ty1.eval = ty2.eval): (f ty1).eval = (f ty2).eval :=
by finish [stable]

lemma stable.comp { f1 f2: Φ → Φ } (f1_stable: stable f1) (f2_stable: stable f2): stable (f1 ∘ f2) :=
by finish [stable]

-- TODO: Kongruenzregeln?

def hom (f: Φ → Φ) := ∀ ty1 ty2: Φ,
    (f (ty1.or ty2)).eval = ((f ty1).or (f ty2)).eval
    ∧ (f (ty1.and ty2)).eval = ((f ty1).and (f ty2)).eval

lemma hom.id: hom id := by simp [hom]

lemma hom.and_right { ty: Φ }: hom ty.and :=
begin
    rw hom,
    assume ty1 ty2,
    split;
    ext env;
    cases c1: ty.eval env;
    cases c2: ty1.eval env;
    cases c3: ty2.eval env;
    simp [*, Φ.eval],
end

lemma hom.or_right { ty: Φ }: hom ty.or :=
begin
    rw hom,
    assume ty1 ty2,
    split;
    ext env;
    cases c1: ty.eval env;
    cases c2: ty1.eval env;
    cases c3: ty2.eval env;
    simp [*, Φ.eval],
end

lemma hom.xgrd_in (grd: XGrd): hom (Φ.xgrd_in grd) :=
begin
    rw hom,
    assume ty1 ty2,
    split;
    ext env;
    cases c: xgrd_eval grd env;
    simp [*, Φ.eval],
end

lemma hom.comp { f1 f2: Φ → Φ } (f1_hom: hom f1) (f1_stable: stable f1) (f2_hom: hom f2) (f2_stable: stable f2): hom (f1 ∘ f2) :=
begin
    unfold hom,
    assume ty1 ty2,
    unfold function.comp,
    
    have h1: (f2 (ty1.or ty2)).eval = ((f2 ty1).or (f2 ty2)).eval := by simp [f2_hom _ _],
    have h2: (f2 (ty1.and ty2)).eval = ((f2 ty1).and (f2 ty2)).eval := by simp [f2_hom _ _],

    rw stable.app f1_stable h1,
    rw stable.app f1_stable h2,
    rw (f1_hom _ _).1,
    rw (f1_hom _ _).2,
    simp,
end
