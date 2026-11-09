module

public import ArtinMatthews.SourceComparisonPositiveDyadEnergy
public import ArtinMatthews.SourceComparisonConstantBoxEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The subtracted constant on an actual occupied comparison dyad. -/

namespace ArtinMatthews

open Finset Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

private theorem dyadic_error_of_prefix (A X U : ℝ) (hX : 2 ≤ X) (hU : 0 < U)
    (M N : ℕ) (hN : (N:ℝ) ≤ 2*U) (e : ℕ → ℂ)
    (herror : (∑ n ∈ Ioc 0 N, ‖e n‖^2) ≤ (N:ℝ)*X^(-A-1)) :
    (∑ n ∈ Icc (M+1) N, ‖e n/U‖^2) ≤ X^(-A)/U := by
  have hsub : Icc (M+1) N ⊆ Ioc 0 N := fun n hn =>
    mem_Ioc.mpr ⟨(Nat.succ_pos M).trans_le (mem_Icc.mp hn).1, (mem_Icc.mp hn).2⟩
  have hX0 : 0 < X := by linarith
  simp_rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hU, div_pow]
  rw [← sum_div]
  calc
    _ ≤ ((N:ℝ)*X^(-A-1))/U^2 := div_le_div_of_nonneg_right
      ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans herror) (by positivity)
    _ ≤ ((2*U)*X^(-A-1))/U^2 := by gcongr
    _ = 2*X^(-A-1)/U := by field_simp
    _ ≤ (X*X^(-A-1))/U := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hX (by positivity)) hU.le
    _ = _ := by
      have he : X*X^(-A-1)=X^(-A) := by
        conv_lhs => lhs; rw [← Real.rpow_one X]
        rw [← Real.rpow_add hX0]
        congr 1
        ring
      rw [he]

theorem sourceComparisonConstantDyad_high_energy
    (ψ : ℝ → ℂ) {a b : ℝ} (ha : 0 < a)
    (hsupp : Function.support ψ ⊆ Set.Icc a b) (hψ : ContDiff ℝ ∞ ψ)
    (ε C D Q E K A : ℝ) (hε : 0 < ε) (hεq : ε < 1/4)
    (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hE : 0 ≤ E) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (Y H σ : ℝ), Real.exp X ≤ Y → Y ≤ Real.exp ((1+ε/4)*X) →
        Real.exp (X^(38/100:ℝ)) ≤ H → H ≤ Real.exp (X/2) → |σ| ≤ X^C →
        ∀ (S : Finset ℕ) (β : ℕ → ℂ),
          (∀ p ∈ S, p.Prime ∧ Real.exp (X^(28/100:ℝ)) ≤ (p:ℝ) ∧
            (p:ℝ) ≤ Real.exp (X^(36/100:ℝ))) →
          (∀ n ∈ Ioc 0 ⌊b*Y⌋₊, ‖β n‖ ≤ X^D) →
          ∀ {ι : Type*} (J : Finset ι) (divisor : ι → ℕ) (coeff : ι → ℂ),
            (∀ i ∈ J, 0 < divisor i ∧ (divisor i:ℝ) ≤ Real.exp (K*X^(47/100:ℝ))) →
            (∑ i ∈ J, ‖coeff i‖/(divisor i:ℝ)) ≤ X^E →
            (∀ N : ℕ, (∑ n ∈ Ioc 0 N,
              ‖β n-markedMajorDivisorPolynomial J divisor coeff n‖^2) ≤
                (N:ℝ)*X^(-(A+3+2*Q+2)-1)) →
            ∀ (q : ℕ) [NeZero q] (h : ZMod q), (q:ℝ) ≤ X^Q →
              ∀ j ∈ sourceComparisonOccupiedDyads S ({1} : Finset ℕ) (Ioc 0 ⌊b*Y⌋₊) a b Y,
                (∫ t in sourceComparisonHighTimes (X*Y/H) (X^B),
                  ‖sourceComparisonCutTriple (sourceComparisonProductBox S {1}
                    (Ioc 0 ⌊b*Y⌋₊) j)
                    (sourceComparisonProductCoefficient h β) ψ Y Y (t+σ)‖^2) ≤ X^(-A) := by
  obtain ⟨B,hB,henergy⟩ := sourceComparisonConstantBox_high_energy (1/2) 1 (ε/8) Q D E (A+3)
    (by norm_num) (by norm_num) (by positivity) hQ hD hE (by linarith)
  refine ⟨max (max 1 C) B+1, by linarith [le_max_right (max 1 C) B], ?_⟩
  filter_upwards [henergy, sourceComparisonNormalizedCutBox_high_energy ψ ha hsupp hψ D C B A hD hA,
    sourceComparisonSmallDyad_scales, sourceComparisonHighGeometry_window a b ε C ha hε hεq,
    sourceComparisonHighGeometry_divisor ε K hε, eventually_ge_atTop (2:ℝ)]
    with X henergy hcut hsmall hgeometry hdiv hX
  intro Y H σ hY hYcap hH hHcap hσ S β hS hβ ι J divisor coeff hdJ hmass herr q _ h hq j hj
  let N := ⌊b*Y⌋₊
  let R := Ioc 0 N
  let P : ℝ := sourceComparisonDyadScale j.1
  let U : ℝ := sourceComparisonDyadScale j.2.2
  let Z := sourceComparisonProductScale j
  let T := X*Y/H
  let M := sourceComparisonDyadScale j.2.2
  let nmax := min N (2*M)
  let S₁ := sourceComparisonDyad S j.1
  let F := sourceComparisonProductBox S {1} R j
  have hJ : j ∈ sourceComparisonProductDyads S {1} R := (mem_filter.mp hj).1
  obtain ⟨hjs,hjg,hjr⟩ := mem_product.mp hJ |>.imp_right mem_product.mp
  have hz : j.2.1 = 0 := by
    obtain ⟨n,hn,he⟩ := mem_image.mp hjg
    rw [mem_singleton.mp hn] at he
    simpa [sourceComparisonDyadKey] using he.symm
  have hZ : Z = P*1*U := by
    dsimp [Z, sourceComparisonProductScale, P,U]
    rw [hz]
    norm_num [sourceComparisonDyadScale]
  obtain ⟨hP,hPlo,hPhi,hPcap⟩ := hsmall S j.1 hS hjs
  have hX0 : 0 < X := by linarith
  have hLcap : 1 ≤ Real.exp ((1-ε/2)*X) := Real.one_le_exp (by nlinarith)
  have hlo : a*Y ≤ 8*Z := (mem_filter.mp hj).2.1
  have hhi : Z ≤ b*Y := (mem_filter.mp hj).2.2
  obtain ⟨hT,hT1,hTcap,hTU,hZcap,hUlo⟩ := hgeometry Y H P 1 U hY hYcap hH hHcap
    hP.le hPcap le_rfl hLcap (sourceComparisonDyadScale_one_le _)
    (by simpa only [hZ] using hlo) (by simpa only [hZ] using hhi)
  have hY0 : 0 < Y := (Real.exp_pos _).trans_le hY
  have hT0 : 0 < T := (Real.rpow_pos_of_pos hX0 _).trans_le hT
  have hU1 : 1 ≤ U := sourceComparisonDyadScale_one_le _
  have hjr₀ : 0 < j.2.2 := by
    by_contra hn
    have hz' : j.2.2 = 0 := by omega
    have hu : U = 1 := by simp [U, sourceComparisonDyadScale, hz']
    have hexp : 1 < Real.exp ((ε/4)*X) := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have hZ1 : 1 ≤ Z := by
    rw [hZ, mul_one]
    exact one_le_mul_of_one_le_of_one_le hP.le hU1
  have hUZ : U ≤ Z := by
    rw [hZ, mul_one]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hP.le (show 0 ≤ U by positivity)
  have hG : sourceComparisonDyad ({1} : Finset ℕ) j.2.1 = {1} := by
    rw [hz]
    ext n
    simp [sourceComparisonDyad, sourceComparisonDyadKey]
    omega
  have hF : F = S₁×ˢ(({1} : Finset ℕ)×ˢIcc (M+1) nmax) := by
    unfold F sourceComparisonProductBox
    rw [hG, sourceComparisonCofactorDyad_eq N _ hjr₀]
  have hβr : ∀ n ∈ Icc (M+1) nmax, ‖β n‖ ≤ X^D := by
    intro n hn
    rw [← sourceComparisonCofactorDyad_eq N _ hjr₀] at hn
    exact hβ n (mem_filter.mp hn).1
  have huM : U ≤ (M:ℝ)+1 := by dsimp [U,M]; linarith
  have hnU : (nmax:ℝ) ≤ 2*U := by dsimp [U,nmax,M]; exact_mod_cast min_le_right _ _
  have hScap : ∀ p ∈ S₁, (p:ℝ) ≤ 2*P := by
    intro p hp
    have hh := (sourceComparisonDyad_bounds hp (hS p (mem_filter.mp hp).1).1.pos).2
    dsimp [P]
    exact_mod_cast hh
  have herror := dyadic_error_of_prefix (A+3+2*Q+2) X U hX (by positivity) M nmax hnU
    (fun n => β n-markedMajorDivisorPolynomial J divisor coeff n) (herr nmax)
  have hTle : 2*T ≤ U := by simpa only [one_mul] using hTU
  have he := henergy J divisor coeff P (2*T) U M nmax β hP hPlo (by simpa only [one_mul] using hPhi) hT1 hTcap
    hTle huM hnU hβr
    (fun i hi => ⟨(hdJ i hi).1, hdiv U (divisor i:ℝ) hUlo (by exact_mod_cast (hdJ i hi).1)
      (hdJ i hi).2⟩) hmass herror q h hq S₁
    (fun p hp => (hS p (mem_filter.mp hp).1).1) hScap
  have huncut (t : ℝ) :
      sourceComparisonCutTriple F (sourceComparisonProductCoefficient h β) (fun _ => 1) Z Y t =
        sourceComparisonConstantBox h S₁ (Icc (M+1) nmax) β P U t := by
    simp only [hF, sourceComparisonCutTriple, sourceComparisonConstantBox, hZ,
      sourceComparisonProductCoefficient, sourceComparisonTriplePosition,
      sum_product, sum_singleton, mul_one]
  have hc : ∀ w ∈ F, ‖sourceComparisonProductCoefficient h β w‖ ≤ X^D := by
    intro w hw
    rw [sourceComparisonProductCoefficient_norm]
    exact hβ _ (mem_filter.mp (mem_product.mp (mem_product.mp hw).2).2).1
  exact hcut F (sourceComparisonProductCoefficient h β) Z Y T σ hZ1 hY0 (mem_filter.mp hj).2.2
    hT ((by linarith : T ≤ 2*T).trans (hTle.trans hUZ)) (by rwa [hZ])
    hσ (fun _ hw => sourceComparisonProductBox_positions_mem S {1} R j
      (fun p hp => (hS p hp).1.pos) (fun m hm => by rw [mem_singleton.mp hm]; norm_num)
      (fun n hn => (mem_Ioc.mp hn).1) hw) hc (by simpa only [huncut] using he)

end
end ArtinMatthews
