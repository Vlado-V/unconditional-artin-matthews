module

public import ArtinMatthews.SpectralSameCuspZeroTranslations


set_option backward.privateInPublic true
@[expose] public section

/-! A literal period-N compact window summed at the actual primitive
width has the constant mass N/w, with no new normalization. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups BigOperators ContDiff

namespace ArtinMatthews

theorem spectralHorizontalPartition_width_lattice_hasFiniteSupport
    {w W : ℝ} (hw : 0 < w) (hW : 0 < W) (x : ℝ) :
    Function.HasFiniteSupport (fun k : ℤ => spectralHorizontalPartition W (x+w*k)) := by
  apply (Set.finite_Icc (Int.ceil (-x/w)) (Int.floor ((2*W-x)/w))).subset
  intro k hk
  have ht := spectralHorizontalPartition_tsupport hW (subset_tsupport _ hk)
  change 0 ≤ x+w*k ∧ x+w*k ≤ 2*W at ht
  exact ⟨Int.ceil_le.mpr ((div_le_iff₀ hw).mpr (by nlinarith [ht.1])),
    Int.le_floor.mpr ((le_div_iff₀ hw).mpr (by nlinarith [ht.2]))⟩

theorem spectralHorizontalPartition_width_lattice_finsum
    {w : ℝ} (hw : 0 < w) (d : ℕ) [NeZero d] (x : ℝ) :
    (∑ᶠ k : ℤ, spectralHorizontalPartition (w*(d : ℝ)) (x+w*k)) = (d : ℝ) := by
  let W := w*(d : ℝ)
  have hW : 0 < W := mul_pos hw (Nat.cast_pos.mpr (NeZero.pos d))
  let F (k : ℤ) := spectralHorizontalPartition W (x+w*k)
  let e : Fin d × ℤ ≃ ℤ := (Equiv.prodComm (Fin d) ℤ).trans (Int.divModEquiv d).symm
  have hf : Function.HasFiniteSupport F := spectralHorizontalPartition_width_lattice_hasFiniteSupport hw hW x
  have hG : Function.HasFiniteSupport (fun p : Fin d × ℤ => F (e p)) :=
    Function.HasFiniteSupport.fun_comp_of_injective e.injective hf
  have hblock (i : Fin d) : (∑ᶠ l : ℤ, F (e (i,l))) = 1 := by
    calc
      _ = ∑ᶠ l : ℤ, spectralHorizontalPartition W (x+w*(i.val : ℝ)+W*l) := by
        apply finsum_congr
        intro l
        change spectralHorizontalPartition W (x+w*((l*(d : ℤ)+(i.val : ℤ) : ℤ) : ℝ)) = _
        congr 1
        dsimp only [W]
        push_cast
        ring
      _ = 1 := spectralHorizontalPartition_lattice_finsum hW _
  calc
    _ = ∑ᶠ p : Fin d × ℤ, F (e p) := (finsum_comp_equiv e).symm
    _ = _ := by
      rw [finsum_curry _ hG]
      simp only [hblock,finsum_eq_sum_of_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

theorem cuspFourierTestSeed_trueWidth_translate (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (k : ℤ) (z : UpperHalfPlane) :
    let nN := (gamma0CuspFrequencyStep N r : ℤ)*n
    let w := gamma0CuspTrueWidth N r
    (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) nN ρ hρ hcρ hpρ).val
      (integerTranslation ((w : ℤ)*k) • z) =
        spectralHorizontalPartition (N : ℝ) (z.re+(w : ℝ)*k) • cuspFourierWave N nN ρ z := by
  dsimp only
  let w := gamma0CuspTrueWidth N r
  let d := gamma0CuspFrequencyStep N r
  have hwd : (w : ℤ)*(d : ℤ) = N := by exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hdiv : (N : ℤ) ∣ ((d : ℤ)*n)*((w : ℤ)*k) := by
    refine ⟨n*k,?_⟩
    rw [← hwd]
    ring
  rw [cuspFourierTestSeed_apply,integerTranslation_eq_T_zpow,ModularGroup.re_T_zpow_smul,
    ModularGroup.im_T_zpow_smul,cuspFourierPhase_integer_shift_of_dvd N _ _ hdiv]
  unfold cuspFourierWave
  simp only [Complex.real_smul,Complex.ofReal_mul,Int.cast_mul,Int.cast_natCast]
  ring

theorem cuspFourierTestSeed_trueWidth_parabolic_finsum (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (z : UpperHalfPlane) :
    let nN := (gamma0CuspFrequencyStep N r : ℤ)*n
    let w := gamma0CuspTrueWidth N r
    (∑ᶠ k : ℤ,
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) nN ρ hρ hcρ hpρ).val
        (integerTranslation ((w : ℤ)*k) • z)) =
      (gamma0CuspFrequencyStep N r : ℝ) • cuspFourierWave N nN ρ z := by
  dsimp only
  let w := gamma0CuspTrueWidth N r
  let d := gamma0CuspFrequencyStep N r
  let _ : NeZero d := ⟨(gamma0CuspFrequencyStep_pos N r).ne'⟩
  have hwd : (w : ℝ)*(d : ℝ) = N := by exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hw : 0 < (w : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have h := spectralHorizontalPartition_width_lattice_finsum hw d z.re
  rw [hwd] at h
  simp_rw [cuspFourierTestSeed_trueWidth_translate]
  rw [← finsum_smul]
  rw [show (∑ᶠ k : ℤ, spectralHorizontalPartition (N : ℝ) (z.re+(gamma0CuspTrueWidth N r : ℝ)*k)) =
      (gamma0CuspFrequencyStep N r : ℝ) from h]

end ArtinMatthews
