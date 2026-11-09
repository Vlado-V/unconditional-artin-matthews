module

public import ArtinMatthews.SpectralHeatSpectralPairing
public import ArtinMatthews.SpectralGamma0SpectralCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! The actual heat cuspidal series splits into the principal spectrum
and the finite set of complementary indices with their multiplicities. -/
namespace ArtinMatthews

open Set
open scoped MatrixGroups BigOperators

noncomputable section

abbrev Gamma0HeatPrincipalCuspidalIndex (N : ℕ) [NeZero N] :=
  {i : Gamma0AllHeightSpectralIndex N // 1 / 4 ≤ gamma0AllHeightGradientSpectralValue N i}

theorem gamma0HeatComplementaryCuspidal_finite (N : ℕ) [NeZero N] :
    {i : Gamma0AllHeightSpectralIndex N | gamma0AllHeightGradientSpectralValue N i < 1 / 4}.Finite := by
  apply (gamma0AllHeightGradientSpectralCutoff_finite N (1 / 4)).subset
  intro i hi
  change gamma0AllHeightGradientSpectralValue N i < 1 / 4 at hi
  change gamma0AllHeightGradientSpectralValue N i ≤ 1 / 4
  exact hi.le

def gamma0HeatComplementaryCuspidalIndices (N : ℕ) [NeZero N] :
    Finset (Gamma0AllHeightSpectralIndex N) :=
  (gamma0HeatComplementaryCuspidal_finite N).toFinset

theorem mem_gamma0HeatComplementaryCuspidalIndices (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    i ∈ gamma0HeatComplementaryCuspidalIndices N ↔
      gamma0AllHeightGradientSpectralValue N i < 1 / 4 :=
  (gamma0HeatComplementaryCuspidal_finite N).mem_toFinset

private theorem gamma0HeatCuspidal_compl_eq_principal (N : ℕ) [NeZero N] :
    ((gamma0HeatComplementaryCuspidalIndices N : Set (Gamma0AllHeightSpectralIndex N))ᶜ) =
      {i | 1 / 4 ≤ gamma0AllHeightGradientSpectralValue N i} := by
  ext i
  change i ∉ gamma0HeatComplementaryCuspidalIndices N ↔
    1 / 4 ≤ gamma0AllHeightGradientSpectralValue N i
  rw [mem_gamma0HeatComplementaryCuspidalIndices, not_lt]

theorem gamma0HeatCuspidal_summable_of_principal (N : ℕ) [NeZero N]
    {V : Type*} [NormedAddCommGroup V] (F : Gamma0AllHeightSpectralIndex N → V)
    (hprincipal : Summable (fun i : Gamma0HeatPrincipalCuspidalIndex N => F i.val)) :
    Summable F := by
  apply ((gamma0HeatComplementaryCuspidalIndices N).summable_compl_iff (f := F)).mp
  change Summable (fun i : ↑((gamma0HeatComplementaryCuspidalIndices N :
    Set (Gamma0AllHeightSpectralIndex N))ᶜ) => F i.val)
  rw [gamma0HeatCuspidal_compl_eq_principal]
  exact hprincipal

theorem gamma0HeatCuspidal_tsum_split (N : ℕ) [NeZero N]
    {V : Type*} [NormedAddCommGroup V] [CompleteSpace V] (F : Gamma0AllHeightSpectralIndex N → V)
    (hF : Summable F) :
    (∑' i, F i) = (∑' i : Gamma0HeatPrincipalCuspidalIndex N, F i.val) +
      ∑ i ∈ gamma0HeatComplementaryCuspidalIndices N, F i := by
  let E := gamma0HeatComplementaryCuspidalIndices N
  have hs := hF.sum_add_tsum_subtype_compl E
  change (∑ i ∈ E, F i) + (∑' i : ↑((E : Set (Gamma0AllHeightSpectralIndex N))ᶜ), F i.val) =
    ∑' i, F i at hs
  rw [show E = gamma0HeatComplementaryCuspidalIndices N from rfl,
    gamma0HeatCuspidal_compl_eq_principal] at hs
  exact hs.symm.trans (add_comm _ _)

def gamma0BareCuspidalAmplitude (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (hm : m ≠ 0) : ℂ :=
  (Real.sqrt |(m : ℝ)| : ℂ) * gamma0ABLSourceRho N i r Y hY m hm

def gamma0BareCuspidalTerm (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (i : Gamma0AllHeightSpectralIndex N) : ℂ :=
  gamma0CuspidalTestSymbol N h i *
    (gamma0BareCuspidalAmplitude N i r Y hY m hm * star (gamma0BareCuspidalAmplitude N i s Y hY n hn))

def gamma0HeatCuspidalTerm (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) (i : Gamma0AllHeightSpectralIndex N) : ℂ :=
  gamma0BareCuspidalTerm N h r s Y hY m n hm hn i *
    spectralHeatEnergyWeight R (gamma0AllHeightGradientSpectralValue N i)

theorem gamma0HeatCuspidalTerm_summable (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    Summable (gamma0HeatCuspidalTerm N h r s Y hY m n hm hn R) :=
  gamma0HeatPoincareTest_source_cusp_summable N h r s Y hY m n hm hn R hR

def gamma0BareCuspidalDiagonalDensity (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (hm : m ≠ 0)
    (i : Gamma0AllHeightSpectralIndex N) : ℝ :=
  (gamma0CuspidalTestSymbol N h i).re * ‖gamma0BareCuspidalAmplitude N i r Y hY m hm‖ ^ 2

theorem gamma0HeatCuspidalTerm_diagonal_re (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (hm : m ≠ 0)
    (R : ℝ) (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0HeatCuspidalTerm N h r r Y hY m m hm hm R i).re =
      gamma0BareCuspidalDiagonalDensity N h r Y hY m hm i *
        (spectralHeatEnergyWeight R (gamma0AllHeightGradientSpectralValue N i)).re := by
  let a := gamma0BareCuspidalAmplitude N i r Y hY m hm
  have ha : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow, Complex.star_def] using Complex.mul_conj' a
  change (gamma0CuspidalTestSymbol N h i * (a * star a) *
    spectralHeatEnergyWeight R (gamma0AllHeightGradientSpectralValue N i)).re = _
  rw [ha, spectralHeatEnergyWeight_real]
  simp only [gamma0BareCuspidalDiagonalDensity, a, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

def gamma0HeatPrincipalCuspidalDiagonal (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (hm : m ≠ 0) (R : ℝ) : ℝ :=
  (∑' i : Gamma0HeatPrincipalCuspidalIndex N,
    gamma0HeatCuspidalTerm N h r r Y hY m m hm hm R i.val).re

theorem gamma0HeatPrincipalCuspidalDiagonal_nonneg (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (hm : m ≠ 0)
    {R : ℝ} (hR : 0 < R)
    (hpos : ∀ i : Gamma0HeatPrincipalCuspidalIndex N,
      ‖gamma0CuspidalTestSymbol N h i.val‖ = (gamma0CuspidalTestSymbol N h i.val).re) :
    0 ≤ gamma0HeatPrincipalCuspidalDiagonal N h r Y hY m hm R := by
  have hs : Summable (fun i : Gamma0HeatPrincipalCuspidalIndex N =>
      gamma0HeatCuspidalTerm N h r r Y hY m m hm hm R i.val) :=
    (gamma0HeatCuspidalTerm_summable N h r r Y hY m m hm hm R hR).subtype _
  unfold gamma0HeatPrincipalCuspidalDiagonal
  rw [Complex.re_tsum hs]
  apply tsum_nonneg
  intro i
  rw [gamma0HeatCuspidalTerm_diagonal_re, spectralHeatEnergyWeight_real, Complex.ofReal_re]
  unfold gamma0BareCuspidalDiagonalDensity
  rw [← hpos i]
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (Real.exp_pos _).le

theorem gamma0HeatCuspidalTerm_norm_le (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {R : ℝ} (hR : 1 ≤ R) (i : Gamma0AllHeightSpectralIndex N) :
    ‖gamma0HeatCuspidalTerm N h r s Y hY m n hm hn R i‖ ≤
      Real.exp (1 / 2 : ℝ) * ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖ := by
  rw [gamma0HeatCuspidalTerm, norm_mul, mul_comm (Real.exp (1 / 2 : ℝ))]
  exact mul_le_mul_of_nonneg_left
    (spectralHeatEnergyWeight_norm_le hR (gamma0AllHeightGradientSpectralValue_nonneg N i))
    (norm_nonneg _)

theorem gamma0HeatComplementaryCuspidal_norm_le (N : ℕ) [NeZero N] (h : SpectralEnergyTest)
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    {R : ℝ} (hR : 1 ≤ R) :
    ‖∑ i ∈ gamma0HeatComplementaryCuspidalIndices N,
      gamma0HeatCuspidalTerm N h r s Y hY m n hm hn R i‖ ≤
      Real.exp (1 / 2 : ℝ) * ∑ i ∈ gamma0HeatComplementaryCuspidalIndices N,
        ‖gamma0BareCuspidalTerm N h r s Y hY m n hm hn i‖ := by
  rw [Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ =>
    gamma0HeatCuspidalTerm_norm_le N h r s Y hY m n hm hn hR i))

end
end ArtinMatthews
