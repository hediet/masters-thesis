import tactic
import ..definitions
import data.finset

variable [GuardModule]
open GuardModule

def stable (f: Φ → Φ) := ∀ ty1 ty2: Φ, (ty1.eval = ty2.eval) → (f ty1).eval = (f ty2).eval

lemma and_left_stable { ty: Φ }: stable (λ ty', ty'.and ty) :=
begin
    rw stable,
    assume ty1 ty2 h,
    ext env,
    simp [Φ.eval, h],
end

lemma and_right_stable { ty: Φ }: stable ty.and :=
begin
    rw stable,
    assume ty1 ty2 h,
    ext env,
    simp [Φ.eval, h],
end

lemma or_right_stable { ty: Φ }: stable ty.or :=
begin
    rw stable,
    assume ty1 ty2 h,
    ext env,
    simp [Φ.eval, h],
end

lemma xgrd_in_stable (xgrd: XGrd): stable (Φ.xgrd_in xgrd) :=
begin
    rw stable,
    assume ty1 ty2 h,
    ext env,
    simp [Φ.eval, h],
end

lemma stable_app { f: Φ → Φ } (f_stable: stable f) { ty1 ty2: Φ } (h: ty1.eval = ty2.eval): (f ty1).eval = (f ty2).eval :=
by finish [stable]

lemma stable_comp { f1 f2: Φ → Φ } (f1_stable: stable f1) (f2_stable: stable f2): stable (f1 ∘ f2) :=
by finish [stable]

lemma id_stable: stable id := by simp [stable]
