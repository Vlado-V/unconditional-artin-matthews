module

public import ArtinMatthews.MarkedMajorCharacterData
public import ArtinMatthews.MarkedMajorCharacterTerms
public import ArtinMatthews.MarkedMajorCharacterNorm
public import ArtinMatthews.MarkedMajorLabelEnergySource


set_option backward.privateInPublic true
@[expose] public section

/-! The literal fixed-rational-arc source and its exact six-character expansion.
Every character term is an actual arithmetic endpoint record. -/
namespace ArtinMatthews
open Finset
noncomputable section
namespace MarkedMajorLabelEnergyData
variable {J J' : Type} [Fintype J] [Fintype J']
variable {cfg : MarkedMajorLabelEnergyConfig} {L X : ℝ}

def arcSource (z : MarkedMajorLabelEnergyData J cfg L X)
    (z' : MarkedMajorLabelEnergyData J' cfg L X) (cutoff : ℝ → ℂ)
    (ψ : SchwartzMap ℝ ℂ) (q : ℕ) (h : ℤ) (θ : ℝ) : ℂ :=
  (z.Y:ℂ)⁻¹*markedMajorArcSourceSum
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorLabelTripleSet z'.allBands z'.u z'.v z'.l z'.r)
    (markedMajorBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β)
    (markedMajorBareConjugateTripleCoefficient z'.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z'.modulation z'.β)
    ψ q h θ z.Y

theorem character_source_eq (z : MarkedMajorLabelEnergyData J cfg L X)
    (z' : MarkedMajorLabelEnergyData J' cfg L X) (cutoff : ℝ → ℂ)
    (ψ : SchwartzMap ℝ ℂ) (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ)
    (θ : ℝ) (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) (hY : z'.Y=z.Y) :
    (z.characterLeft q χ θ hq hθ).source (z'.characterRight q χ θ hq hθ) cutoff ψ θ =
    (z.Y:ℂ)⁻¹*markedMajorArcCharacterTerm
      (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
      (markedMajorLabelTripleSet z'.allBands z'.u z'.v z'.l z'.r)
      (markedMajorBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β)
      (markedMajorBareConjugateTripleCoefficient z'.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z'.modulation z'.β)
      ψ q χ θ z.Y := by
  rw [markedMajor_character_term_eq]
  simp only [source,characterLeft,characterRight,hY]
  rfl

theorem arcSource_expansion (z : MarkedMajorLabelEnergyData J cfg L X)
    (z' : MarkedMajorLabelEnergyData J' cfg L X) (cutoff : ℝ → ℂ)
    (ψ : SchwartzMap ℝ ℂ) (q : ℕ) [NeZero q] (h : ℤ) (θ : ℝ)
    (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) (hY : z'.Y=z.Y)
    (hqW : (q:ℝ) ≤ Real.exp (L^(6/25:ℝ)))
    (hWu : Real.exp (L^(6/25:ℝ)) ≤ z.u) (hWu' : Real.exp (L^(6/25:ℝ)) ≤ z'.u)
    (hbandq : ∀ j p,p ∈ z.allBands j → q < p) (hbandq' : ∀ j p,p ∈ z'.allBands j → q < p)
    (hβrough : ∀ n ∈ Icc z.l z.r,z.β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n)
    (hβrough' : ∀ n ∈ Icc z'.l z'.r,z'.β n ≠ 0 → ∀ p ∈ Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) :
    z.arcSource z' cutoff ψ q h θ =
      ∑ χ : AddChar (MarkedUnitTuple q) ℂ,markedFourierCoeff (markedResiduePhase q h) χ*
        (z.characterLeft q χ θ hq hθ).source (z'.characterRight q χ θ hq hθ) cutoff ψ θ := by
  unfold arcSource
  rw [markedMajor_arc_character_expansion]
  · rw [mul_sum]
    apply sum_congr rfl
    intro χ _
    rw [character_source_eq z z' cutoff ψ q χ θ hq hθ hY]
    ring
  · intro v hv hcoeff
    exact markedMajor_bare_unit_support z.allBands z.allBands_prime cutoff z.Y
      (Real.exp (L^(6/25:ℝ))) z.modulation z.u z.v z.l z.r z.β q hqW hWu hbandq hβrough v hv hcoeff
  · intro v hv hcoeff
    exact markedMajor_bare_conjugate_unit_support z'.allBands z'.allBands_prime cutoff z.Y
      (Real.exp (L^(6/25:ℝ))) z'.modulation z'.u z'.v z'.l z'.r z'.β q hqW hWu' hbandq' hβrough' v hv hcoeff

end MarkedMajorLabelEnergyData
end
end ArtinMatthews
