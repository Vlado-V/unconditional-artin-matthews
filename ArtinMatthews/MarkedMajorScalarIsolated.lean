module

public import ArtinMatthews.MarkedMajorScalarProductMean
public import ArtinMatthews.MarkedMajorArcIsolatedEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Actual isolated-prime cancellation with arbitrary bounded left
coefficients satisfying their literal long-frequency test. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory
open scoped Topology
noncomputable section

theorem markedMajorScalar_isolated_log_saving
    (c C₁ C₂ d σ b Cα Cβ P : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hd : 0 < d)
    (hσ : 0 ≤ σ) (hb : 0 ≤ b) (hCα : 0 ≤ Cα) (hCβ : 0 ≤ Cβ) (hP : 0 ≤ P) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Y T H U : ℝ) (S : Finset ℕ) (l r : ℕ) (α β : ℕ → ℂ),
        1 < Y → c*L^(1/(10:ℝ)) ≤ Real.log Y → Real.log Y ≤ C₁*L^(1/(5:ℝ)) →
        1 < T → Real.log T ≤ C₂*L → 0 < H → Real.exp (d*L) ≤ U →
        1 ≤ H*U → H*U ≤ Real.exp (σ*L) → T/(H*U) ≤ L^b →
        (∀ m ∈ S,H ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*H) →
        U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
        (∀ m ∈ S,‖α m‖ ≤ L^Cα) → (∀ n ∈ Icc l r,‖β n‖ ≤ L^Cβ) →
        (∀ t ∈ Set.Icc (-T) T, ‖markedMajorScalarPolynomial S H α t‖ ≤ L^(-R)) →
        ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (ξ : ℝ) (P₀ : Finset ℕ),
          (∀ p ∈ P₀,p.Prime) → (∀ p ∈ P₀,(p:ℝ) ≤ 2*Y) →
          (∫ t in Set.Icc (-T) T, ‖markedPrimePolynomial P₀ Y χ ξ t*
            markedMajorScalarPolynomial S H α t*markedMajorScalarPolynomial (Icc l r) U β t‖^2) ≤
            L^(-P) := by
  let D := b+2*(Cα+Cβ)+3
  let A := D+P+2
  let R := P+Cβ+2
  have hA : 0 ≤ A := by dsimp only [D,A]; linarith
  have hR : 0 < R := by dsimp only [R]; linarith
  obtain ⟨J,hJ,hiso⟩ := marked_isolated_prime_energy_of_mean c C₁ C₂ A d hc hC₁ hC₂ hA hd
  obtain ⟨E,hE,hmean⟩ := markedMajorScalarPolynomial_product_mean_log σ Cα Cβ hσ
  refine ⟨R,hR,?_⟩
  filter_upwards [hiso,hmean,eventually_ge_atTop (max 1 (2*E+4*J))] with L hiso hmean hL
  have hL₁ : 1 ≤ L := (le_max_left _ _).trans hL
  have hLp := zero_lt_one.trans_le hL₁
  have hEJ : 2*E+4*J ≤ L := (le_max_right _ _).trans hL
  intro Y T H U S l r α β hY hYlo hYhi hT hTlog hH hU hX hupper hratio hS hl hr hα hβ
    hlong k χ ξ P₀ hP₀ hcap
  let M := markedMajorScalarPolynomial S H α
  let N := markedMajorScalarPolynomial (Icc l r) U β
  have hUp := (Real.exp_pos _).trans_le hU
  have hTp : 0 < T := zero_lt_one.trans hT
  have hN : ∀ n ∈ Icc l r, U ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*U := fun n hn =>
    ⟨hl.trans (Nat.cast_le.mpr (mem_Icc.mp hn).1),(Nat.cast_le.mpr (mem_Icc.mp hn).2).trans hr⟩
  have hmn : (∫ t in Set.Icc (-T) T, ‖M t*N t‖^2) ≤ (2*E)*L^D := by
    have hm := hmean S (Icc l r) H U T 0 α β hH hUp hTp hX hupper hS hN hα hβ
    simp only [add_zero] at hm
    have hh : 1+T/(H*U) ≤ 2*L^b := by linarith [Real.one_le_rpow hL₁ hb]
    apply hm.trans
    calc
      _ ≤ E*L^(2*(Cα+Cβ)+3)*(2*L^b) :=
        mul_le_mul_of_nonneg_left hh (mul_nonneg hE.le (Real.rpow_nonneg hLp.le _))
      _ = (2*E)*(L^(2*(Cα+Cβ)+3)*L^b) := by ring
      _ = _ := by
        rw [← Real.rpow_add hLp,show (2*(Cα+Cβ)+3)+b=D by dsimp only [D]; ring]
  have hdy := markedMajorScalarPolynomial_eq_dyadic l r U β
  have hh := hiso Y T U (L^Cβ) (L^(-R)) ((2*E)*L^D) l r β M
    hY hYlo hYhi hT hTlog hU hl hr hβ (markedMajorScalarPolynomial_continuous S H α) hlong
    (by simpa only [N,hdy] using hmn) k χ ξ P₀ hP₀ hcap
  have hsquare (z : ℝ) : (L^z)^2 = L^(z*2) := by
    rw [Real.rpow_mul hLp.le,Real.rpow_two]
  have hgood : (L^(-A))^2*((2*E)*L^D) ≤ (2*E)*L^(-P-1) := by
    rw [hsquare]
    have he : L^(-A*2)*((2*E)*L^D) = (2*E)*L^(-A*2+D) := by
      calc
        _ = (2*E)*(L^(-A*2)*L^D) := by ring
        _ = _ := by rw [← Real.rpow_add hLp]
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hL₁
    dsimp only [A,D]
    linarith
  have hbad : 4*(L^(-R))^2*J*L*(L^Cβ)^2 ≤ (4*J)*L^(-P-1) := by
    have he : 4*(L^(-R))^2*J*L*(L^Cβ)^2 = (4*J)*L^(-R*2+1+Cβ*2) := by
      rw [Real.rpow_add hLp (-R*2+1) (Cβ*2),Real.rpow_add hLp (-R*2) 1,Real.rpow_one,
        hsquare,hsquare]
      ring
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hL₁
    dsimp only [R]
    linarith
  rw [hdy]
  apply hh.trans
  calc
    _ ≤ (2*E)*L^(-P-1)+(4*J)*L^(-P-1) := add_le_add hgood hbad
    _ = (2*E+4*J)*L^(-P-1) := by ring
    _ ≤ L*L^(-P-1) := mul_le_mul_of_nonneg_right hEJ (Real.rpow_nonneg hLp.le _)
    _ = L^(-P) := by
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hLp,show (1:ℝ)+(-P-1)= -P by ring]

end
end ArtinMatthews
