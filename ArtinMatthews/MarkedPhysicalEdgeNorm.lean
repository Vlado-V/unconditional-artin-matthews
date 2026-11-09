module

public import ArtinMatthews.MarkedPhysicalEdgeKernelFormula


set_option backward.privateInPublic true
@[expose] public section

/-! A pointwise bound for the original physical coefficient. The actual
determinant divisibility is retained, and the source dyad pays the factor
d0/D. Physical endpoint vectors absorb the separate damping exactly. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedPhysicalEdgeCoefficient_one_norm_le
    {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (V : J → ℝ) (hV : ∀ j, 0 ≤ V j) (pads : ℕ)
    (Z : Finset (ℤ × ℤ)) (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (H : ℝ) (hH : 0 ≤ H)
    (hη : ∀ t, ‖η t‖ ≤ H) (d₀ Y Q : ℝ)
    (s t : MarkedPhysicalState P (pads+1) Z) :
    let u := markedPhysicalStateToRaw P hP (pads+1) Z s
    let v := markedPhysicalStateToRaw P hP (pads+1) Z t
    let b := ((markedRawActiveSplit pads) u.2.1).2
    let a := ((markedRawActiveSplit pads) v.2.1).2
    let D := markedRawCopiedProduct ((markedRawActiveSplit pads) u.2.1).1
    ‖markedPhysicalEdgeCoefficient P hP V pads Z hZ ψ η d₀ Y Q 1 s t‖ ≤
      markedPhysicalMass V (pads+2) * H^2 *
        (if (D : ℤ) ∣ markedMinorIntegerDet s.1.1.1 t.1.1.1 then
          ‖markedBanEdgeKernel ψ Q Y (markedRawLastProduct b) (markedRawLastProduct a)
            (markedMinorIntegerDet s.1.1.1 t.1.1.1/(D : ℤ))‖ else 0) := by
  dsimp only
  rw [markedPhysicalEdgeCoefficient_kernel]
  simp only [markedPhysicalEndpointDamping, Real.one_rpow, Complex.ofReal_one, one_mul, mul_one]
  have hmass := markedPhysicalMass_nonneg V (pads+2) hV
  have hD : 0 < (markedRawCopiedProduct
      ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).1 : ℝ) := by
    exact_mod_cast markedRawCopiedProduct_pos
      ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).1
  split_ifs with hprefix hdyad hdiv hban <;>
    try simp only [mul_zero, norm_zero] <;> try positivity
  have hd₀ : 0 ≤ d₀ := by linarith [hdyad.2]
  have hratio₀ : 0 ≤ d₀/(markedRawCopiedProduct
      ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).1 : ℝ) :=
    div_nonneg hd₀ hD.le
  have hratio₁ : d₀/(markedRawCopiedProduct
      ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).1 : ℝ) ≤ 1 :=
    (div_le_one hD).mpr hdyad.1
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmass, abs_of_nonneg hratio₀]
  calc
    _ ≤ markedPhysicalMass V (pads+2) * (1*H*H*
        ‖markedBanEdgeKernel ψ Q Y
          (markedRawLastProduct ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).2)
          (markedRawLastProduct ((markedRawActiveSplit pads) (markedPhysicalStateToRaw P hP (pads+1) Z t).2.1).2)
          (markedMinorIntegerDet s.1.1.1 t.1.1.1/
            (markedRawCopiedProduct ((markedRawActiveSplit pads)
              (markedPhysicalStateToRaw P hP (pads+1) Z s).2.1).1 : ℤ))‖) := by
      gcongr
      · exact hη _
      · exact hη _
    _ = _ := by ring

end ArtinMatthews
