module

public import ArtinMatthews.SpectralCuspUnitFourierTesting
public import ArtinMatthews.SpectralEisensteinMeromorphicTests


set_option backward.privateInPublic true
@[expose] public section

/-! The nonzero compact Fourier amplitude of the actual continued
Eisenstein family. It consists of literal true-width Fourier means of
the incoming and outgoing cutoffs and the completed mass coefficient. -/

noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace ENNReal

namespace ArtinMatthews

def gamma0CuspEisensteinFourierCoefficient (N : ℕ) [NeZero N] (a r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ) (y : ℝ) : ℂ :=
  gamma0UnitCuspFourierMean N r m (gamma0CuspEisensteinCutoff N a s)
    (y/(gamma0CuspTrueWidth N r : ℝ)) +
  gamma0CuspFourierCoefficient N r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*m)
    (gamma0EnergyInclusion N (gamma0CuspEisensteinMatchedTruncatedEnergy N a s)) y +
  ∑ j : Gamma0EisensteinCuspClasses N, gamma0EisensteinMatchedCoefficient N a s j *
    gamma0UnitCuspFourierMean N r m
      (gamma0CuspEisensteinCutoff N (gamma0EisensteinCuspClassRepresentative N j) (1-s))
      (y/(gamma0CuspTrueWidth N r : ℝ))

theorem gamma0CuspEisensteinCutoff_fourier_test (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    let mN := (gamma0CuspFrequencyStep N r : ℤ)*m
    let ψ := modularTranslateSmoothSeed r
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ)
    gamma0EisensteinCutoffCompactTest N a ψ s =
      (N : ℝ) • ∫ y in Ioi Y, (ρ y/y^2) •
        gamma0UnitCuspFourierMean N r m (gamma0CuspEisensteinCutoff N a s)
          (y/(gamma0CuspTrueWidth N r : ℝ)) := by
  dsimp only
  rw [gamma0EisensteinCutoffCompactTest,h2_compactSeed_inner_modularTranslate]
  exact (gamma0Invariant_unit_fourier_test N r (gamma0CuspEisensteinCutoff N a s)
    (gamma0CuspOutgoingCutoff_continuous N a s) (gamma0CuspEisensteinCutoff_automorphy N a s)
    Y hY m ρ hρ hcρ hpρ hsρ).2

theorem gamma0CuspFourierCoefficient_compact_pairing_integrable (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (f : Gamma0RegionL2 N)
    (ρ : ℝ → ℝ) (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    IntegrableOn (fun y => (ρ y/y^2) • (gamma0CuspFourierCoefficient N r Y hY m f) y) (Ioi Y) := by
  let C := gamma0CuspFourierCoefficient N r Y hY m f
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have ht := cuspVerticalL2_memLp_compact hN hY
    (Complex.continuous_ofReal.comp hρ) (hcρ.comp_left Complex.ofReal_zero)
  have hi := (cuspVerticalL2_integrable_complex_density_iff hN hY _).mp
    (ht.integrable_mul (Lp.memLp C))
  apply hi.congr
  exact ae_of_all _ fun y => by
    change (y^(-2 : ℤ)) • ((ρ y : ℂ)*C y) = (ρ y/y^2) • C y
    simp only [zpow_neg,zpow_ofNat,Complex.real_smul,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_inv]
    ring

theorem gamma0CuspEisensteinFourierCoefficient_compact_integrable (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    IntegrableOn (fun y => (ρ y/y^2) • gamma0CuspEisensteinFourierCoefficient N a r Y hY m s y)
      (Ioi Y) := by
  have hCut (b : SL(2, ℤ)) (z : ℂ) :=
    (gamma0Invariant_unit_fourier_test N r (gamma0CuspEisensteinCutoff N b z)
      (gamma0CuspOutgoingCutoff_continuous N b z) (gamma0CuspEisensteinCutoff_automorphy N b z)
      Y hY m ρ hρ hcρ hpρ hsρ).1
  have hMass := gamma0CuspFourierCoefficient_compact_pairing_integrable N r Y hY
    ((gamma0CuspFrequencyStep N r : ℤ)*m)
    (gamma0EnergyInclusion N (gamma0CuspEisensteinMatchedTruncatedEnergy N a s))
    ρ hρ.continuous hcρ
  have hSum : IntegrableOn (fun y => ∑ j : Gamma0EisensteinCuspClasses N,
      gamma0EisensteinMatchedCoefficient N a s j *
        ((ρ y/y^2) • gamma0UnitCuspFourierMean N r m
          (gamma0CuspEisensteinCutoff N (gamma0EisensteinCuspClassRepresentative N j) (1-s))
          (y/(gamma0CuspTrueWidth N r : ℝ)))) (Ioi Y) :=
    integrable_finsetSum _ (fun j _ => (hCut _ _).const_mul _)
  apply ((hCut a s).add hMass |>.add hSum).congr
  exact ae_of_all _ fun y => by
    simp only [Pi.add_apply,gamma0CuspEisensteinFourierCoefficient,Complex.real_smul,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem gamma0CuspEisensteinMeromorphicTest_fourier (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    let mN := (gamma0CuspFrequencyStep N r : ℤ)*m
    let ψ := modularTranslateSmoothSeed r
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ)
    gamma0CuspEisensteinMeromorphicTest N a ψ s =
      (2*(N : ℝ)) • ∫ y in Ioi Y, (ρ y/y^2) •
        gamma0CuspEisensteinFourierCoefficient N a r Y hY m s y := by
  dsimp only
  let q y := ρ y/y^2
  let w : ℝ := gamma0CuspTrueWidth N r
  let H (b : SL(2, ℤ)) (z : ℂ) y :=
    gamma0UnitCuspFourierMean N r m (gamma0CuspEisensteinCutoff N b z) (y/w)
  let C := gamma0CuspFourierCoefficient N r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*m)
    (gamma0EnergyInclusion N (gamma0CuspEisensteinMatchedTruncatedEnergy N a s))
  let c (j : Gamma0EisensteinCuspClasses N) := gamma0EisensteinMatchedCoefficient N a s j
  let b (j : Gamma0EisensteinCuspClasses N) := gamma0EisensteinCuspClassRepresentative N j
  have hCut (b : SL(2, ℤ)) (z : ℂ) : IntegrableOn (fun y => q y • H b z y) (Ioi Y) :=
    (gamma0Invariant_unit_fourier_test N r (gamma0CuspEisensteinCutoff N b z)
      (gamma0CuspOutgoingCutoff_continuous N b z) (gamma0CuspEisensteinCutoff_automorphy N b z)
      Y hY m ρ hρ hcρ hpρ hsρ).1
  have hMass : IntegrableOn (fun y => q y • C y) (Ioi Y) :=
    gamma0CuspFourierCoefficient_compact_pairing_integrable N r Y hY _ _ ρ hρ.continuous hcρ
  have hSum : IntegrableOn (fun y => ∑ j, c j*(q y • H (b j) (1-s) y)) (Ioi Y) :=
    integrable_finsetSum _ (fun j _ => (hCut _ _).const_mul _)
  have hIntegral :
      (∫ y in Ioi Y, q y • gamma0CuspEisensteinFourierCoefficient N a r Y hY m s y) =
      (∫ y in Ioi Y, q y • H a s y) + (∫ y in Ioi Y, q y • C y) +
        ∑ j, c j*(∫ y in Ioi Y, q y • H (b j) (1-s) y) := by
    have hp (y : ℝ) : q y • gamma0CuspEisensteinFourierCoefficient N a r Y hY m s y =
        q y • H a s y + q y • C y + ∑ j, c j*(q y • H (b j) (1-s) y) := by
      simp only [gamma0CuspEisensteinFourierCoefficient,H,C,c,b,w,Complex.real_smul,mul_add,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [hp]
    calc
      _ = (∫ y in Ioi Y,q y • H a s y + q y • C y) +
          (∫ y in Ioi Y,∑ j,c j*(q y • H (b j) (1-s) y)) :=
        integral_add ((hCut a s).add hMass) hSum
      _ = ((∫ y in Ioi Y,q y • H a s y) + (∫ y in Ioi Y,q y • C y)) +
          ∑ j,c j*(∫ y in Ioi Y,q y • H (b j) (1-s) y) := by
        congr 1
        · exact integral_add (hCut a s) hMass
        · calc
            _ = ∑ j,∫ y in Ioi Y,c j*(q y • H (b j) (1-s) y) :=
              integral_finsetSum _ (fun j _ => (hCut _ _).const_mul _)
            _ = _ := Finset.sum_congr rfl (fun j _ => integral_const_mul _ _)
  rw [gamma0CuspEisensteinMeromorphicTest]
  simp_rw [gamma0CuspEisensteinCutoff_fourier_test N _ r Y hY m _ ρ hρ hcρ hpρ hsρ]
  rw [show inner ℂ
      (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r
        (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
          ((gamma0CuspFrequencyStep N r : ℤ)*m) ρ hρ hcρ hpρ)))
      (gamma0EnergyInclusion N (gamma0CuspEisensteinMatchedTruncatedEnergy N a s)) =
      (2*(N : ℝ)) • ∫ y in Ioi Y,q y • C y from
    gamma0FourierPoincareTest_inner N r Y hY _ ρ hρ hcρ hpρ hsρ _]
  rw [hIntegral]
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_natCast]
  let I (d : SL(2, ℤ)) (z : ℂ) := ∫ y in Ioi Y,(q y : ℂ)*H d z y
  let M := ∫ y in Ioi Y,(q y : ℂ)*C y
  change (2 : ℂ)*((N : ℂ)*I a s) + (2*(N : ℂ))*M +
    (∑ j,c j*((2 : ℂ)*((N : ℂ)*I (b j) (1-s)))) =
      (2*(N : ℂ))*(I a s+M+∑ j,c j*I (b j) (1-s))
  have hScale : (∑ j,c j*((2 : ℂ)*((N : ℂ)*I (b j) (1-s)))) =
      (2*(N : ℂ))*(∑ j,c j*I (b j) (1-s)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hScale]
  ring

end ArtinMatthews

