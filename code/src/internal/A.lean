import tactic
import data.finset
import ..definitions
import .internal_definitions
import .tactics
import .utils
import .phi.utils
import .Ant.main
import .U

variable [GuardModule]
open GuardModule

private lemma A_eq_𝒜' (gdt: Gdt) { acc: Φ → Φ } (acc_stable: stable acc) (acc_hom: hom acc):
    ((A gdt).map acc).eval_rhss = (𝒜_acc acc gdt).eval_rhss :=
begin
    ext env,
    induction gdt generalizing acc env,
    case Gdt.rhs { simp [A, Ant.map, 𝒜_acc], },
    case Gdt.branch {
        unfold 𝒜_acc,
        unfold Ant.eval_rhss,
        unfold Ant.map,
        rw ←Ant.eval_rhss,
        rw ←Ant.eval_rhss,
        rw ←Ant.eval_rhss,
        
        specialize gdt_ih_tr1 env acc_stable acc_hom,
        rw ←gdt_ih_tr1,
        
        specialize @gdt_ih_tr2 ((𝒰_acc acc gdt_tr1).and ∘ acc) env
            (stable.comp stable.and_right acc_stable)
            (hom.comp hom.and_right stable.and_right acc_hom acc_stable),
        rw ←gdt_ih_tr2,

        simp [Ant.map, A, Ant.eval_rhss, Ant.map_associative, function.comp, Φ.eval, (acc_hom.1 _ _).2, U_eq_𝒰_acc acc_stable acc_hom],
    },
    case Gdt.grd {
        cases gdt_grd,        
        case Grd.tgrd {
            unfold A 𝒜_acc Ant.map,
            specialize @gdt_ih (acc ∘ Φ.tgrd_in gdt_grd) env
                (stable.comp acc_stable (stable.tgrd_in gdt_grd))
                (hom.comp acc_hom acc_stable (hom.tgrd_in gdt_grd) (stable.tgrd_in gdt_grd)),
            rw ←gdt_ih,
            rw Ant.map_associative,
        },
        case Grd.bang {
            unfold A 𝒜_acc Ant.map Ant.eval_rhss,
            rw ←Ant.eval_rhss,
            rw ←Ant.eval_rhss,
            specialize @gdt_ih (acc ∘ (Φ.var_is_not_bottom gdt_grd).and) env
                (stable.comp acc_stable stable.and_right)
                (hom.comp acc_hom acc_stable hom.and_right stable.and_right),
            rw ←gdt_ih,
            rw Ant.map_associative,
        },
    },
end

theorem A_eq_𝒜 (gdt: Gdt): (A gdt).eval_rhss = (𝒜 gdt).eval_rhss :=
begin
    unfold 𝒜,
    have := A_eq_𝒜' gdt stable.id hom.id,
    simp [Ant.map_id] at this,
    exact this,
end

@[simp]
lemma A_rhss { gdt: Gdt }: (A gdt).rhss = gdt.rhss :=
begin
    induction gdt,
    case Gdt.rhs { finish, },
    case Gdt.branch { finish [Gdt.rhss, A, Ant.map], },
    case Gdt.grd {
        cases gdt_grd;
        finish [Gdt.rhss, A, Ant.map],
    },
end

lemma Ant.disjoint_rhss_of_gdt_disjoint_rhss { gdt: Gdt } (h: gdt.disjoint_rhss): (A gdt).disjoint_rhss :=
begin
    induction gdt,
    case Gdt.rhs { simp [A], },
    case Gdt.branch {
        unfold Gdt.disjoint_rhss at h,
        simp [A, Gdt.disjoint_rhss, Ant.disjoint_rhss, *],
    },
    case Gdt.grd {
        unfold Gdt.disjoint_rhss at h,
        cases gdt_grd;
        { simp [A, Ant.disjoint_rhss, *], },
    },
end

lemma Ant.disjoint_rhss_iff_of_mark_inactive_rhss_eq { ant1 ant2: Ant Φ } { env: Env } (h: ant1.mark_inactive_rhss env = ant2.mark_inactive_rhss env):
    ant1.disjoint_rhss ↔ ant2.disjoint_rhss :=
begin
    have : (ant1.mark_inactive_rhss env).disjoint_rhss ↔ (ant2.mark_inactive_rhss env).disjoint_rhss := by rw h,
    simp at this,
    exact this,
end
