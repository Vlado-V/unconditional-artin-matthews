module

public import ArtinMatthews.GiantOrderedProductTuples
public import Mathlib.Algebra.GCDMonoid.Nat


set_option backward.privateInPublic true
@[expose] public section

/-! A common product admits a positive refinement matrix. Row and column
products recover the two ordered factorizations. -/

namespace ArtinMatthews
open Finset
open scoped BigOperators

theorem giant_exists_product_divisor_tuple {k : ℕ} (v : Fin k → ℕ) {a : ℕ}
    (ha : a ∣ ∏ j,v j) :
    ∃ t : Fin k → ℕ, (∀ j,t j ∣ v j) ∧ (∏ j,t j)=a := by
  induction k generalizing a with
  | zero =>
      have h : a=1 := Nat.dvd_one.mp (by simpa only [Fin.prod_univ_zero] using ha)
      exact ⟨fun _ => 1,fun j => j.elim0, (Fin.prod_univ_zero _).trans h.symm⟩
  | succ k ih =>
      rw [Fin.prod_univ_succ] at ha
      obtain ⟨b,c,hb,hc,he⟩ := Nat.dvd_mul.mp ha
      obtain ⟨t,ht,htprod⟩ := ih (fun j => v j.succ) hc
      refine ⟨Fin.cons b t,?_,?_⟩
      · intro j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa only [Fin.cons_zero] using hb
        · simpa only [Fin.cons_succ] using ht i
      · rw [Fin.prod_univ_succ,Fin.cons_zero]
        simp only [Fin.cons_succ,htprod]
        exact he

theorem giant_exists_factor_matrix {k l : ℕ} (u : Fin k → ℕ) (v : Fin l → ℕ)
    (hu : ∀ i,0 < u i) (hv : ∀ j,0 < v j) (he : (∏ i,u i) = ∏ j,v j) :
    ∃ a : Fin k → Fin l → ℕ, (∀ i j,0 < a i j) ∧
      (∀ i,(∏ j,a i j)=u i) ∧ (∀ j,(∏ i,a i j)=v j) := by
  induction k generalizing v with
  | zero =>
      refine ⟨fun i => i.elim0,fun i => i.elim0,fun i => i.elim0,?_⟩
      intro j
      have hd' : v j ∣ ∏ i,u i := he.symm ▸ (dvd_prod_of_mem v (mem_univ j))
      have hd : v j ∣ 1 := by simpa only [Fin.prod_univ_zero] using hd'
      rw [Fin.prod_univ_zero]
      exact (Nat.dvd_one.mp hd).symm
  | succ k ih =>
      have hd : u 0 ∣ ∏ j,v j := he ▸ dvd_prod_of_mem u (mem_univ 0)
      obtain ⟨a,had,ha⟩ := giant_exists_product_divisor_tuple v hd
      let w (j : Fin l) := v j/a j
      have haw (j : Fin l) : a j*w j=v j := Nat.mul_div_cancel' (had j)
      have hapos (j : Fin l) : 0 < a j := Nat.pos_of_dvd_of_pos (had j) (hv j)
      have hwpos (j : Fin l) : 0 < w j := by
        have hm : 0 < a j*w j := (haw j).symm ▸ hv j
        exact Nat.pos_of_ne_zero (Nat.mul_ne_zero_iff.mp hm.ne').2
      have hprod : (∏ i : Fin k,u i.succ) = ∏ j,w j := by
        apply Nat.eq_of_mul_eq_mul_left (hu 0)
        calc
          _ = ∏ i,u i := (Fin.prod_univ_succ u).symm
          _ = ∏ j,v j := he
          _ = (∏ j,a j)*(∏ j,w j) := by
            rw [← prod_mul_distrib]
            exact prod_congr rfl (fun j _ => (haw j).symm)
          _ = _ := by rw [ha]
      obtain ⟨b,hb,hrows,hcols⟩ := ih (fun i : Fin k => u i.succ) w
        (fun i => hu i.succ) hwpos hprod
      refine ⟨Fin.cons a b,?_,?_,?_⟩
      · intro i j
        refine Fin.cases ?_ (fun t => ?_) i
        · simpa only [Fin.cons_zero] using hapos j
        · simpa only [Fin.cons_succ] using hb t j
      · intro i
        refine Fin.cases ?_ (fun t => ?_) i
        · simpa only [Fin.cons_zero] using ha
        · simpa only [Fin.cons_succ] using hrows t
      · intro j
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ,hcols,haw]

end ArtinMatthews
