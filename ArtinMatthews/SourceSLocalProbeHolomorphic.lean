module

public import ArtinMatthews.SourceSLocalProbeVertical


set_option backward.privateInPublic true
@[expose] public section

/-! Holomorphy of the literal probe from the normalized local factors. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

theorem sourceSLocalProbeMellin_analyticOnNhd :
    AnalyticOnNhd ℂ (sourceSLocalProbeMellin K hζ S v) {s : ℂ | 0 < s.re} := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  let A : ℂ → ℂ := sourceComplexMellin sourceProbeArchFourier
  let F (p : S) : ℂ → ℂ := sourceLocalAnnularMellin K p.val
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hA : DifferentiableOn ℂ A U :=
    (sourceComplexMellin_analyticOnNhd sourceProbeArchFourier).differentiableOn
  have harch : DifferentiableOn ℂ (fun s => ∏ _ : {w : InfinitePlace K // w ≠ v}, A s) U :=
    DifferentiableOn.fun_finsetProd fun _ _ => hA
  have hf : DifferentiableOn ℂ (fun s => ∏ p : S, F p s) U :=
    DifferentiableOn.fun_finsetProd fun p _ => sourceLocalAnnularMellin_differentiableOn K p.val
  rw [funext (sourceSLocalProbeMellin_eq_products K hζ S v)]
  exact (hA.mul (harch.mul hf)).analyticOnNhd hU

end
end ArtinMatthews.SourcePhysical
