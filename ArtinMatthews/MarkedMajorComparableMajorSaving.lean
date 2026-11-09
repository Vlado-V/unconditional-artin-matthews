module

public import ArtinMatthews.MarkedMajorComparableCharacterSaving
public import ArtinMatthews.MarkedMajorArcCoverBound
public import ArtinMatthews.MarkedMajorArcCoverBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The original determinant major-kernel sum has arbitrary logarithmic
saving. The proof integrates the literal source over the actual circle major
set, using its finite closed-arc cover without a disjointness assumption. -/
namespace ArtinMatthews
open Filter Finset MeasureTheory
open scoped ContDiff
noncomputable section
namespace MarkedMajorLabelEnergyData

 def comparableMajorSource {J J' : Type} [Fintype J] [Fintype J']
    {cfg : MarkedMajorLabelEnergyConfig} {L X X' : ℝ}
    (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J' cfg L X')
    (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (Q : ℝ) : ℂ :=
  markedMajorKernelSource
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorLabelTripleSet z'.allBands z'.u z'.v z'.l z'.r)
    (markedMajorBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β)
    (markedMajorBareConjugateTripleCoefficient z'.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z'.modulation z'.β)
    ψ Q z.Y

end MarkedMajorLabelEnergyData

 theorem markedMajor_comparableMajorSource_all_log
    (cfg : MarkedMajorLabelEnergyConfig) (σ Kx : ℝ) (hσ : 0 ≤ σ)
    (cutoff : ℝ → ℂ) (hcutoff : ContDiff ℝ ∞ cutoff) (hnorm : ∀ y, ‖cutoff y‖ ≤ 1)
    {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hinterval : lo/2 < 8*hi)
    (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hψ : tsupport ψ ⊆ Set.Icc (-R) R) (P : ℝ) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop, ∀ X X' : ℝ, 1 ≤ X → 1 ≤ X' → X ≤ Real.exp (σ*L) → X ≤ Kx*Real.exp L →
      X' ≤ Real.exp (σ*L) → X' ≤ Kx*Real.exp L → X ≤ 2*X' → X' ≤ 2*X →
      ∀ {J J' : Type} [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
      (z : MarkedMajorLabelEnergyData J cfg L X) (z' : MarkedMajorLabelEnergyData J' cfg L X'),
      z'.Y=z.Y → ∀ Q : ℝ, 0 ≤ Q → Q ≤ L^cfg.a → 2*Q ≤ cfg.Kθ*L^cfg.A₀ →
      (∀ j p,p ∈ z.allBands j → Q < (p:ℝ)) → (∀ j p,p ∈ z'.allBands j → Q < (p:ℝ)) →
      (∀ n ∈ Finset.Icc z.l z.r,z.β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      (∀ n ∈ Finset.Icc z'.l z'.r,z'.β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) →
      ‖z.comparableMajorSource z' cutoff ψ Q‖ ≤ (z.Y*X)*L^(-P) := by
  have hsave : 0 ≤ P+3*cfg.a+1 := by linarith [cfg.ha]
  filter_upwards [markedMajor_comparable_arcSource_all_log cfg σ Kx hσ cutoff hcutoff hnorm
    hlo hhi hinterval hsupp ψ hψ (P+3*cfg.a+1) hsave,eventually_ge_atTop (4:ℝ)] with L hs hL
  intro X X' hX1 hX'1 hupper hcomp hupper' hcomp' hlow hupp J J' _ _ _ _ z z' hY Q hQ hQa hQθ hband hband' hrough hrough'
  have hLp : 0 < L := by linarith
  have hX : 0 < X := by linarith
  have hnormSource := markedMajorKernelSource_norm_of_arcs
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorLabelTripleSet z'.allBands z'.u z'.v z'.l z'.r)
    (markedMajorBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β)
    (markedMajorBareConjugateTripleCoefficient z'.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z'.modulation z'.β)
    ψ hQ z.Y_pos (mul_nonneg (mul_pos z.Y_pos hX).le (Real.rpow_nonneg hLp.le (-(P+3*cfg.a+1))))
    (fun q hq hqQ h θ hθ => by
      let : NeZero q := ⟨Nat.ne_of_gt hq⟩
      have hb : ∀ j p,p ∈ z.allBands j → q < p := by
        intro j p hp
        exact_mod_cast hqQ.trans_lt (hband j p hp)
      have hb' : ∀ j p,p ∈ z'.allBands j → q < p := by
        intro j p hp
        exact_mod_cast hqQ.trans_lt (hband' j p hp)
      exact hs X X' hX1 hX'1 hupper hcomp hupper' hcomp' hlow hupp z z' hY q (hqQ.trans hQa) h θ
        (hθ.trans hQθ) hb hb' hrough hrough')
  exact hnormSource.trans (markedMajor_cover_cost hL hQ hQa z.Y_pos.le hX.le)

end
end ArtinMatthews
