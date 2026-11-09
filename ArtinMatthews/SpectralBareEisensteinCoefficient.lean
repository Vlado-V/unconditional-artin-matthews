module

public import ArtinMatthews.SpectralHeatSpectralPairing


set_option backward.privateInPublic true
@[expose] public section

/-! The actual unregularized continuous source coefficients. Their
diagonal densities control all cross pairings channel by channel. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0BareEisensteinSourceCoefficient (N : ℕ) [NeZero N]
    (a : Gamma0EisensteinCuspClasses N) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (t : ℝ) : ℂ :=
  (Real.sqrt |(n : ℝ)| : ℂ)*gamma0ABLEisensteinRho N
    (gamma0EisensteinCuspClassRepresentative N a) r Y hY n hn (eisensteinCriticalPoint t)

def gamma0BareContinuousRhoIntegrand (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ) : ℂ :=
  (spectralContinuousTestSymbol h t/((2*Real.pi : ℝ) : ℂ))*
    ∑ a : Gamma0EisensteinCuspClasses N, gamma0BareEisensteinSourceCoefficient N a r Y hY m hm t*
      star (gamma0BareEisensteinSourceCoefficient N a s Y hY n hn t)

def gamma0BareContinuousRhoDiagonal (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (t : ℝ) : ℝ :=
  (spectralContinuousTestSymbol h t).re/(2*Real.pi)*
    ∑ a : Gamma0EisensteinCuspClasses N, ‖gamma0BareEisensteinSourceCoefficient N a r Y hY n hn t‖^2

theorem gamma0HeatContinuousRhoIntegrand_eq_bare (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (R t : ℝ) :
    gamma0HeatContinuousRhoIntegrand N h r s Y hY m n hm hn R t =
      gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn t*
        spectralHeatEnergyWeight R (1/4+t^2) := by
  have hs :
      (∑ a : Gamma0EisensteinCuspClasses N, gamma0BareEisensteinSourceCoefficient N a r Y hY m hm t*
        star (gamma0BareEisensteinSourceCoefficient N a s Y hY n hn t)) =
      (Real.sqrt |(m : ℝ)| : ℂ)*(Real.sqrt |(n : ℝ)| : ℂ)*
        gamma0ABLContinuousRhoKernel N r s Y hY m n hm hn t := by
    unfold gamma0ABLContinuousRhoKernel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    unfold gamma0BareEisensteinSourceCoefficient
    rw [star_mul,show star ((Real.sqrt |(n : ℝ)| : ℝ) : ℂ) = (Real.sqrt |(n : ℝ)| : ℂ)
      from Complex.conj_ofReal _]
    ring
  unfold gamma0HeatContinuousRhoIntegrand gamma0BareContinuousRhoIntegrand
  rw [hs]
  ring

theorem gamma0BareContinuousRhoDiagonal_nonneg (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (t : ℝ)
    (ht : 0 ≤ (spectralContinuousTestSymbol h t).re) :
    0 ≤ gamma0BareContinuousRhoDiagonal N h r Y hY n hn t := by
  unfold gamma0BareContinuousRhoDiagonal
  exact mul_nonneg (div_nonneg ht (by positivity)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem gamma0BareContinuousRhoIntegrand_diagonal (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) (t : ℝ)
    (ht : ((spectralContinuousTestSymbol h t).re : ℂ) = spectralContinuousTestSymbol h t) :
    gamma0BareContinuousRhoIntegrand N h r r Y hY n n hn hn t =
      (gamma0BareContinuousRhoDiagonal N h r Y hY n hn t : ℂ) := by
  have hp (z : ℂ) : z*star z = ((‖z‖^2 : ℝ) : ℂ) := by
    change z*(starRingEnd ℂ) z = _
    rw [mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  unfold gamma0BareContinuousRhoIntegrand gamma0BareContinuousRhoDiagonal
  simp_rw [hp]
  calc
    _ = (((spectralContinuousTestSymbol h t).re/(2*Real.pi) : ℝ) : ℂ)*
        ∑ a : Gamma0EisensteinCuspClasses N, ((‖gamma0BareEisensteinSourceCoefficient N a r Y hY n hn t‖^2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_div,ht]
    _ = _ := by rw [← Complex.ofReal_sum,← Complex.ofReal_mul]

theorem gamma0BareContinuousRhoIntegrand_norm_le_diagonals (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (t : ℝ)
    (ht : ‖spectralContinuousTestSymbol h t‖ = (spectralContinuousTestSymbol h t).re) :
    ‖gamma0BareContinuousRhoIntegrand N h r s Y hY m n hm hn t‖ ≤
      (gamma0BareContinuousRhoDiagonal N h r Y hY m hm t+
        gamma0BareContinuousRhoDiagonal N h s Y hY n hn t)/2 := by
  let u (a : Gamma0EisensteinCuspClasses N) := gamma0BareEisensteinSourceCoefficient N a r Y hY m hm t
  let v (a : Gamma0EisensteinCuspClasses N) := gamma0BareEisensteinSourceCoefficient N a s Y hY n hn t
  let D := (spectralContinuousTestSymbol h t).re/(2*Real.pi)
  have hD : 0 ≤ D := div_nonneg (ht ▸ norm_nonneg _) (by positivity)
  have hnorm : ‖spectralContinuousTestSymbol h t/((2*Real.pi : ℝ) : ℂ)‖ = D := by
    rw [norm_div,ht,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  change ‖(spectralContinuousTestSymbol h t/((2*Real.pi : ℝ) : ℂ))*
    (∑ a, u a*star (v a))‖ ≤ _
  rw [norm_mul,hnorm]
  calc
    _ ≤ D*(∑ a, ‖u a*star (v a)‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hD
    _ ≤ D*(∑ a, (‖u a‖^2+‖v a‖^2)/2) := by
      apply mul_le_mul_of_nonneg_left _ hD
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul,norm_star]
      nlinarith [sq_nonneg (‖u a‖-‖v a‖)]
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul,Finset.sum_add_distrib]
      change D*(((∑ a, ‖u a‖^2)+(∑ a, ‖v a‖^2))*2⁻¹) =
        (D*(∑ a, ‖u a‖^2)+D*(∑ a, ‖v a‖^2))*2⁻¹
      ring

end ArtinMatthews
