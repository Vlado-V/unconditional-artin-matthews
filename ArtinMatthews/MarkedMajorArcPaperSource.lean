module

public import ArtinMatthews.MarkedMajorArcMajorSaving


set_option backward.privateInPublic true
@[expose] public section

/-! Literal PD05 source: two independently summed label products, the squared
band normalizer, and the actual α_m conjugate(α_r) β_n conjugate(β_s). -/
namespace ArtinMatthews
open Finset ComplexConjugate
noncomputable section
namespace MarkedMajorLabelEnergyData
variable {J : Type} {cfg : MarkedMajorLabelEnergyConfig} {L X : ℝ}

 def conjugateBeta (z : MarkedMajorLabelEnergyData J cfg L X) :
    MarkedMajorLabelEnergyData J cfg L X :=
  { z with
    β := fun n => conj (z.β n)
    coefficient_bound := fun n hn => by simpa only [RCLike.norm_conj] using z.coefficient_bound n hn }

end MarkedMajorLabelEnergyData

 def markedMajorDeterminantPaperSum {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (Q Y W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ) : ℂ :=
  (markedMajorLabelMass bands:ℂ)^2*
    ∑ b ∈ markedMajorLabelSet bands,∑ m ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,∑ n ∈ Icc l r,
    ∑ a ∈ markedMajorLabelSet bands,∑ r' ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,∑ s ∈ Icc l r,
      cutoff ((b:ℝ)/Y)*cutoff ((a:ℝ)/Y)*
      markedMajorCenteredCoefficient W modulation m*conj (markedMajorCenteredCoefficient W modulation r')*
      β n*conj (β s)*ψ ((markedMajorIntegerDeterminant (b,m,n) (a,r',s):ℝ)/Y)*
      markedBanMajorKernel Q Y (markedMajorIntegerDeterminant (b,m,n) (a,r',s)-(b:ℤ)+(a:ℤ))

 theorem markedMajor_paper_source_eq {J : Type} [Fintype J]
    {cfg : MarkedMajorLabelEnergyConfig} {L X : ℝ}
    (z : MarkedMajorLabelEnergyData J cfg L X) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q : ℝ) :
    z.majorSource z.conjugateBeta cutoff ψ Q =
      markedMajorDeterminantPaperSum z.allBands cutoff ψ Q z.Y (Real.exp (L^(6/25:ℝ)))
        z.modulation z.u z.v z.l z.r z.β := by
  classical
  unfold MarkedMajorLabelEnergyData.majorSource markedMajorKernelSource
    MarkedMajorLabelEnergyData.conjugateBeta
  change markedMajorKernelSource
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β)
    (markedMajorBareConjugateTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation (fun n => conj (z.β n)))
    ψ Q z.Y = _
  unfold markedMajorKernelSource markedMajorDeterminantPaperSum markedMajorLabelTripleSet
  simp only [sum_product,mul_sum]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro r' _
  apply sum_congr rfl
  intro s _
  unfold markedMajorBareTripleCoefficient markedMajorBareConjugateTripleCoefficient
  dsimp only
  ring

end
end ArtinMatthews
