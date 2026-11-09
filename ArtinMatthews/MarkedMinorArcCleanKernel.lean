module

public import ArtinMatthews.MarkedMinorArcProductOperator


set_option backward.privateInPublic true
@[expose] public section

/-! Exact identification with PD (mem:clean-kernel). -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The checked compression is exactly the source clean kernel, with the
actual determinant cutoff and integer product difference. -/
theorem markedMinorCleanProductMatrix_apply (ψ : SchwartzMap ℝ ℂ)
    (L T : ℤ) (M N : ℕ) (Y Q : ℝ) (S : Finset ℤ)
    (h l : MarkedMinorBoxIndex L T M N) (b a : S) :
    markedMinorCleanProductMatrix ψ L T M N Y Q S (h,b) (l,a) =
      ((Y : ℂ)⁻¹)*ψ (((h.1.1*l.1.2-h.1.2*l.1.1 : ℤ) : ℝ)/Y) *
      ∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
        fourier ((h.1.1*l.1.2-h.1.2*l.1.1)-b.1+a.1) θ ∂AddCircle.haarAddCircle := by
  classical
  unfold markedMinorCleanProductMatrix markedProductCompressionMatrix
  rw [← integral_const_mul,← integral_indicator (markedMinorCircleMajor_measurable Q Y).compl]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => by
    by_cases hθ : θ ∈ markedMinorCircleMajor Q Y
    · simp [Set.indicator,markedMinorCircleFiber,hθ]
    · simp only [markedMinorCircleFiber,markedMinorSmoothCircleMatrix,
        Set.indicator,Set.mem_compl_iff,hθ,ite_false,not_false_eq_true,ite_true,
        sub_eq_add_neg,fourier_add]
      ring)

end ArtinMatthews
