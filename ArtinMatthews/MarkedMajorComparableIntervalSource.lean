module

public import ArtinMatthews.MarkedMajorComparableMajorSaving
public import ArtinMatthews.MarkedMajorClosedIntervalSplit


set_option backward.privateInPublic true
@[expose] public section

/-! Exact source identification for independent intervals at comparable
product scales. The two original coefficient endpoints remain separate. -/
namespace ArtinMatthews
open Finset ComplexConjugate
noncomputable section

 theorem markedMajor_comparable_interval_source_eq {J : Type} [Fintype J]
    {cfg : MarkedMajorLabelEnergyConfig} {L X X' : ℝ}
    (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J cfg L X')
    (hb : z'.allBands=z.allBands) (hm : z'.modulation=z.modulation)
    (hl : z'.l=z.l) (hr : z'.r=z.r) (hβ : z'.β=z.β)
    (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q : ℝ) :
    z.comparableMajorSource z'.conjugateBeta cutoff ψ Q =
      markedMajorIntervalPairSum z.allBands cutoff ψ Q z.Y (Real.exp (L^(6/25:ℝ)))
        z.modulation (Ioc ⌊z.u⌋₊ ⌊z.v⌋₊) (Ioc ⌊z'.u⌋₊ ⌊z'.v⌋₊) z.l z.r z.β := by
  classical
  unfold MarkedMajorLabelEnergyData.comparableMajorSource
  simp only [MarkedMajorLabelEnergyData.conjugateBeta]
  change markedMajorKernelSource
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorLabelTripleSet z'.allBands z'.u z'.v z'.l z'.r)
    (markedMajorBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β)
    (markedMajorBareConjugateTripleCoefficient z'.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ)))
      z'.modulation (fun n => conj (z'.β n))) ψ Q z.Y = _
  rw [hb,hm,hl,hr,hβ]
  unfold markedMajorKernelSource markedMajorIntervalPairSum markedMajorLabelTripleSet
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
