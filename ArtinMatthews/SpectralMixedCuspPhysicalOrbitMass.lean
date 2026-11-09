module

public import ArtinMatthews.SpectralMixedCuspOrbitMass
public import ArtinMatthews.SpectralInfinityFourierSeedMassBound
public import ArtinMatthews.SpectralCuspTrueWidthPhysicalMoment


set_option backward.privateInPublic true
@[expose] public section

/-! An actual compact physical test at the mixed cusp. The mass bound
depends on the normalized height lower bound and the literal level. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff CompactlySupported
namespace ArtinMatthews

private theorem spectralCuspFourierTestSeed_mass_le (N : ℕ) [NeZero N] (n : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    (∫ z : UpperHalfPlane, ‖(cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
      n ρ hρ hcρ hpρ).val z‖^2) ≤ (N : ℝ)*cuspFourierHeightPairing ρ ρ := by
  have hi : Function.Injective (fun _ : Unit => n) := fun _ _ _ => Subsingleton.elim _ _
  simpa [gamma0InfinityFourierSeedPacket] using gamma0InfinityFourierSeedPacket_mass_le N
    ({()} : Finset Unit) (fun _ => (1 : ℂ)) (fun _ => n) hi (fun _ => ρ)
    (fun _ => hρ) (fun _ => hcρ) (fun _ => hpρ)

theorem gamma0MixedSameCusp_physical_orbit_norm_le (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ)
    {A : ℝ} (hA : 0 < A) (hSF : tsupport F ⊆ Ici A)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hProfile : ρ = spectralFrequencyTestProfile
      (|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)) F) :
    let N := r*s
    let a := gamma0CuspOneOver s
    let w := (gamma0CuspTrueWidth N a : ℝ)
    let d := gamma0CuspFrequencyStep N a
    let q := |cuspFourierFrequency 1 n|
    w*‖gamma0FourierPoincareTest N a ((d : ℤ)*n) ρ hρ hcρ hpρ‖^2 ≤
      (2*(N : ℝ))^2*(6*(1+2*q/((N : ℝ)*A))*(∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure)) := by
  dsimp only
  let N := r*s
  let a := gamma0CuspOneOver s
  let w := (gamma0CuspTrueWidth N a : ℝ)
  let d := gamma0CuspFrequencyStep N a
  let q := |cuspFourierFrequency 1 n|
  let p := q/w
  let V := 1+2*q/((N : ℝ)*A)
  let M := ∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hq : 0 < q := abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)
  have hp : 0 < p := div_pos hq hw
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  let ψ := cuspFourierTestSeed (N : ℝ) hN ((d : ℤ)*n) ρ hρ hcρ hpρ
  let Ψ := modularTranslateSmoothSeed a ψ
  have hlo (y : ℝ) (hy : y ∈ tsupport ρ) : w*(A/q) ≤ y := by
    have he : w*(A/q) = A/p := by
      dsimp only [p]
      field_simp [hq.ne',hw.ne']
    rw [he]
    rw [hProfile] at hy
    exact spectralFrequencyTestProfile_support_lower p hp F hSF hy
  have hSupp (z : UpperHalfPlane) (hz : Ψ.val z ≠ 0) :
      (a • z).re ∈ Icc 0 (2*(N : ℝ)) ∧ w*(A/q) ≤ (a • z).im := by
    change ψ.val (a • z) ≠ 0 at hz
    dsimp only [ψ] at hz
    rw [cuspFourierTestSeed_apply] at hz
    have hpr := Complex.ofReal_ne_zero.mp ((mul_ne_zero_iff.mp hz).1)
    exact ⟨spectralHorizontalPartition_tsupport hN (subset_tsupport _ (mul_ne_zero_iff.mp hpr).1),
      hlo _ (subset_tsupport _ (mul_ne_zero_iff.mp hpr).2)⟩
  have hPsi : (∫ z : UpperHalfPlane, ‖Ψ.val z‖^2) =
      ∫ z : UpperHalfPlane, ‖ψ.val z‖^2 := by
    let g := Matrix.SpecialLinearGroup.mapGL ℝ a
    let e : UpperHalfPlane ≃ₜ UpperHalfPlane := Homeomorph.smul g
    have he : MeasurePreserving e.toMeasurableEquiv (volume : Measure UpperHalfPlane) volume :=
      measurePreserving_smul g _
    exact he.integral_comp' (fun z => ‖ψ.val z‖^2)
  have hMass : (∫ z : UpperHalfPlane, ‖Ψ.val z‖^2) ≤ (N : ℝ)*M := by
    rw [hPsi]
    refine (spectralCuspFourierTestSeed_mass_le N ((d : ℤ)*n) ρ hρ hcρ hpρ).trans_eq ?_
    congr 1
    rw [hProfile]
    exact spectralFrequencyTestProfile_height_mass p hp F
  have hVeq : 1+2/((N : ℝ)*(A/q)) = V := by
    dsimp only [V]
    field_simp [hN.ne',hA.ne',hq.ne']
  have hNorm := gamma0MixedCusp_compact_seed_orbit_mass_bound r s hcop Ψ (div_pos hA hq) hSupp
  change ‖gamma0SmoothSeedMass N Ψ‖^2 ≤
    2*((2*(d : ℝ)+1)*(4*(1+2/((N : ℝ)*(A/q)))))*(∫ z : UpperHalfPlane, ‖Ψ.val z‖^2) at hNorm
  rw [hVeq] at hNorm
  have hdw : w*(d : ℝ) = (N : ℝ) := by
    dsimp only [w,d]
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N a
  have hd1 : 1 ≤ (d : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (gamma0CuspFrequencyStep_pos N a)
  have hwN : w ≤ (N : ℝ) := hdw ▸ le_mul_of_one_le_right hw.le hd1
  change w*‖gamma0SmoothSeedMass N Ψ‖^2 ≤ (2*(N : ℝ))^2*(6*V*M)
  calc
    _ ≤ w*(2*((2*(d : ℝ)+1)*(4*V))*((N : ℝ)*M)) :=
      mul_le_mul_of_nonneg_left (hNorm.trans (mul_le_mul_of_nonneg_left hMass (by positivity))) hw.le
    _ = 8*(N : ℝ)*(2*(N : ℝ)+w)*(V*M) := by rw [← hdw]; ring
    _ ≤ 8*(N : ℝ)*(2*(N : ℝ)+(N : ℝ))*(V*M) := by gcongr
    _ = _ := by ring

theorem gamma0MixedCusp_physical_finite_bessel (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (u : Finset (Gamma0AllHeightSpectralIndex (r*s)))
    (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hcF : HasCompactSupport F)
    {A Y : ℝ} (hA : 0 < A) (hY : 0 < Y)
    (hYA : Y < A/(|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)))
    (hSF : tsupport F ⊆ Ici A) :
    gamma0CuspPhysicalBesselMoment (r*s) u (gamma0CuspOneOver s) Y hY n hn F ≤
      6*(1+2*|cuspFourierFrequency 1 n|/(((r*s : ℕ) : ℝ)*A))*
        (∫ x : ℝ, (F x)^2 ∂spectralKLPhysicalMeasure) := by
  let N := r*s
  let a := gamma0CuspOneOver s
  let w := (gamma0CuspTrueWidth N a : ℝ)
  let p := |cuspFourierFrequency 1 n|/w
  have hN : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hp : 0 < p := div_pos (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)) hw
  let ρ := spectralFrequencyTestProfile p F
  have hFpos : tsupport F ⊆ Ioi (0 : ℝ) := fun _ hx => hA.trans_le (hSF hx)
  have hρ : ContDiff ℝ ∞ ρ := spectralFrequencyTestProfile_contDiff p F hF hFpos
  have hcρ : HasCompactSupport ρ := spectralFrequencyTestProfile_compact p hp F hcF
  have hLo (y : ℝ) (hy : y ∈ tsupport ρ) : A/p ≤ y :=
    spectralFrequencyTestProfile_support_lower p hp F hSF hy
  have hpρ : tsupport ρ ⊆ Ioi (0 : ℝ) := fun y hy => (div_pos hA hp).trans_le (hLo y hy)
  have hsρ : tsupport ρ ⊆ Ioi Y := fun y hy => hYA.trans_le (hLo y hy)
  have hNorm := gamma0MixedSameCusp_physical_orbit_norm_le r s hcop n hn F hA hSF ρ hρ hcρ hpρ rfl
  have hB := gamma0CuspPhysicalBesselMoment_le_scaled_norm N u a Y hY n hn F ρ hρ hcρ hpρ hsρ rfl
  exact (mul_le_mul_iff_of_pos_left (show 0 < (2*(N : ℝ))^2 by positivity)).mp (hB.trans hNorm)

end ArtinMatthews
