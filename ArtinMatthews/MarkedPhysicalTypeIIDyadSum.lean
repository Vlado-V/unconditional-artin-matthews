module

public import ArtinMatthews.MarkedPhysicalTypeIIActual
public import ArtinMatthews.MarkedPhysicalDetectorHarmonicSum
public import ArtinMatthews.MarkedPhysicalPadDyadBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Actual weighted physical Type II dyad sums, and their exact flagged
harmonic-pad determinant/major disintegration. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedPhysicalTypeIIDyadBox (Y Hm Hn : ℝ) (j : ℕ) : Finset (ℤ×ℤ) :=
  let U := ((2:ℕ)^j:ℝ)*Y*Hm
  markedPhysicalPrimitiveBox U (16*U) Hn (2*Hn)

theorem markedPhysicalPadDyad_weighted_norm_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (pads : ℕ) (f : ℕ → ℂ) (E : ℝ)
    (hf : ∀ j∈markedPhysicalPadDyadIndices P pads,‖f j‖ ≤ ((2:ℕ)^j:ℝ)*E) :
    ‖∑ j ∈ markedPhysicalPadDyadIndices P pads,(((2:ℕ)^j:ℝ):ℂ)⁻¹*f j‖ ≤
      ((markedPhysicalPadDyadIndices P pads).card:ℝ)*E := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j ∈ markedPhysicalPadDyadIndices P pads,E := by
      apply Finset.sum_le_sum
      intro j hj
      let d := ((2:ℕ)^j:ℝ)
      have hd : 0 < d := by dsimp [d]; positivity
      change ‖(d:ℂ)⁻¹*f j‖ ≤ E
      rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
      calc
        _ ≤ d⁻¹*(d*E) := mul_le_mul_of_nonneg_left (hf j hj) (inv_nonneg.mpr hd.le)
        _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hd.ne',one_mul]
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]

def markedPhysicalTypeIIDyadSum {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (Y Q Hm Hn : ℝ) (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ) : ℂ :=
  ∑ j ∈ markedPhysicalPadDyadIndices (fun i => markedLogPowerBand (e i) x) ⌊(Real.log x)^(1/100:ℝ)⌋₊,
    (((2:ℕ)^j:ℝ):ℂ)⁻¹*markedPhysicalTypeIIPairing e x ψ η ((2:ℕ)^j) Y Q 1
      (((2:ℕ)^j:ℝ)*Y*Hm) Hn Sα Sβ modulation β

def markedPhysicalTypeIICharacterDyadSum {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (Mχ : ℕ) (ξ : DirichletCharacter ℂ Mχ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (Y Q Hm Hn : ℝ) (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ) : ℂ :=
  ∑ j ∈ markedPhysicalPadDyadIndices (fun i => markedLogPowerBand (e i) x) ⌊(Real.log x)^(1/100:ℝ)⌋₊,
    (((2:ℕ)^j:ℝ):ℂ)⁻¹*markedPhysicalTypeIICharacterPairing e x Mχ ξ ψ η ((2:ℕ)^j) Y Q 1
      (((2:ℕ)^j:ℝ)*Y*Hm) Hn Sα Sβ modulation β

theorem markedPhysicalTypeIIDyadSum_eq_harmonic
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (Y Q Hm Hn : ℝ) (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ) :
    let P := fun j => markedLogPowerBand (e j) x
    let pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊
    let α := markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα
    let βf := markedPhysicalRestrictedBeta Sβ β
    let Z := markedPhysicalTypeIIDyadBox Y Hm Hn
    markedPhysicalTypeIIDyadSum e x ψ η Y Q Hm Hn Sα Sβ modulation β =
      markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y (markedRawEdgeDeltaDetector ψ Y) α βf-
        markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y (markedRawEdgeMajorDetector ψ Q Y) α βf :=
  markedPhysicalEdgePairing_dyad_delta_sub_major (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) ⌊(Real.log x)^(1/100:ℝ)⌋₊
    (markedPhysicalTypeIIDyadBox Y Hm Hn) (fun _ _ hz => (Finset.mem_filter.mp hz).2)
    ψ η Y Q 1 _ _

theorem markedPhysicalTypeIICharacterDyadSum_eq_harmonic
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) (Mχ : ℕ) (ξ : DirichletCharacter ℂ Mχ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (Y Q Hm Hn : ℝ) (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ) :
    let P := fun j => markedLogPowerBand (e j) x
    let pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊
    let α := fun (n : ℕ) => ξ n*markedMajorRestrictedCoefficient
      (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα n
    let βf := fun (n : ℕ) => ξ n*markedPhysicalRestrictedBeta Sβ β n
    let Z := markedPhysicalTypeIIDyadBox Y Hm Hn
    markedPhysicalTypeIICharacterDyadSum e x Mχ ξ ψ η Y Q Hm Hn Sα Sβ modulation β =
      markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y (markedRawEdgeDeltaDetector ψ Y) α βf-
        markedPhysicalHarmonicPaddedDetectorSum P pads Z η Y (markedRawEdgeMajorDetector ψ Q Y) α βf :=
  markedPhysicalEdgePairing_dyad_delta_sub_major (fun j => markedLogPowerBand (e j) x)
    (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) ⌊(Real.log x)^(1/100:ℝ)⌋₊
    (markedPhysicalTypeIIDyadBox Y Hm Hn) (fun _ _ hz => (Finset.mem_filter.mp hz).2)
    ψ η Y Q 1
    (fun n => ξ n*markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα n)
    (fun n => ξ n*markedPhysicalRestrictedBeta Sβ β n)

end
end ArtinMatthews
