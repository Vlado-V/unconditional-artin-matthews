module

public import ArtinMatthews.MarkedMajorFixedCharacterData
public import ArtinMatthews.MarkedMajorComparableCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! Actual six-character expansion of the fixed-character rational-arc
source. The external character survives in every endpoint record. -/
namespace ArtinMatthews
open Finset
noncomputable section

theorem markedMajor_fixed_character_term_eq {J J' : Type*} [Fintype J] [Fintype J']
    (S T : Finset (ℕ×(ℕ×ℕ))) (bands : J → Finset ℕ) (bands' : J' → Finset ℕ)
    (cutoff : ℝ → ℂ) (Y W modulation modulation' : ℝ) (β β' : ℕ → ℂ)
    {M : ℕ} (ξ ξ' : DirichletCharacter ℂ M)
    (ψ : ℝ → ℂ) (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ) :
    markedMajorArcCharacterTerm S T
      (markedMajorFixedBareTripleCoefficient bands cutoff Y W modulation β ξ)
      (markedMajorFixedBareConjugateTripleCoefficient bands' cutoff Y W modulation' β' ξ')
      ψ q χ θ Y =
    ∑ z ∈ S,∑ z' ∈ T,
      (markedMajorLabelTripleCoefficient bands cutoff (markedCoordinateDirichlet q χ 1) θ Y
        (heckeDirichletProduct ξ (markedCoordinateDirichlet q χ 2)) W modulation
        (fun n => ξ n*(β n*markedCoordinateDirichlet q χ 3 n)) z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff (markedCoordinateDirichlet q χ 0) (-θ) Y
        (heckeDirichletProduct ξ' (markedCoordinateDirichlet q χ 4)) W modulation'
        (fun n => ξ' n*(β' n*markedCoordinateDirichlet q χ 5 n)) z')*
      (ψ ((markedMajorLabelTripleValue z-markedMajorLabelTripleValue z')/Y)*
        OAI.Problem337.RealPhase.phase (θ*((markedMajorLabelTripleValue z-markedMajorLabelTripleValue z')/Y))) := by
  unfold markedMajorArcCharacterTerm
  simp_rw [markedMajor_fixed_bare_left_twist,markedMajor_fixed_bare_right_twist,
    markedMajorIntegerDeterminant_real,mul_div_assoc]

namespace MarkedMajorLabelEnergyData
variable {J J' : Type} [Fintype J] [Fintype J']
variable {cfg : MarkedMajorLabelEnergyConfig} {L X X' : ℝ}

def fixedComparableArcSource (z : MarkedMajorLabelEnergyData J cfg L X)
    (z' : MarkedMajorLabelEnergyData J' cfg L X') {M : ℕ} (ξ ξ' : DirichletCharacter ℂ M)
    (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (q : ℕ) (h : ℤ) (θ : ℝ) : ℂ :=
  (z.Y:ℂ)⁻¹*markedMajorArcSourceSum
    (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
    (markedMajorLabelTripleSet z'.allBands z'.u z'.v z'.l z'.r)
    (markedMajorFixedBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β ξ)
    (markedMajorFixedBareConjugateTripleCoefficient z'.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z'.modulation z'.β ξ')
    ψ q h θ z.Y

theorem fixed_comparable_character_source_eq (z : MarkedMajorLabelEnergyData J cfg L X)
    (z' : MarkedMajorLabelEnergyData J' cfg L X') {M : ℕ} [NeZero M] (ξ ξ' : DirichletCharacter ℂ M)
    (hL : 0<L) (hM : (M:ℝ) ≤ L) (cutoff : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ)
    (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ)
    (θ : ℝ) (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) (hY : z'.Y=z.Y) :
    (z.fixedCharacterLeft ξ hL hM q χ θ hq hθ).comparableSource
      (z'.fixedCharacterRight ξ' hL hM q χ θ hq hθ) cutoff ψ θ =
    (z.Y:ℂ)⁻¹*markedMajorArcCharacterTerm
      (markedMajorLabelTripleSet z.allBands z.u z.v z.l z.r)
      (markedMajorLabelTripleSet z'.allBands z'.u z'.v z'.l z'.r)
      (markedMajorFixedBareTripleCoefficient z.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z.modulation z.β ξ)
      (markedMajorFixedBareConjugateTripleCoefficient z'.allBands cutoff z.Y (Real.exp (L^(6/25:ℝ))) z'.modulation z'.β ξ')
      ψ q χ θ z.Y := by
  rw [markedMajor_fixed_character_term_eq]
  simp only [comparableSource,fixedCharacterLeft,fixedCharacterRight,hY]
  rfl

theorem fixedComparableArcSource_expansion (z : MarkedMajorLabelEnergyData J cfg L X)
    (z' : MarkedMajorLabelEnergyData J' cfg L X') {M : ℕ} [NeZero M] (ξ ξ' : DirichletCharacter ℂ M)
    (hL : 0<L) (hM : (M:ℝ) ≤ L) (cutoff : ℝ → ℂ)
    (ψ : SchwartzMap ℝ ℂ) (q : ℕ) [NeZero q] (h : ℤ) (θ : ℝ)
    (hq : (q:ℝ) ≤ L^cfg.a) (hθ : |θ| ≤ cfg.Kθ*L^cfg.A₀) (hY : z'.Y=z.Y)
    (hqW : (q:ℝ) ≤ Real.exp (L^(6/25:ℝ)))
    (hWu : Real.exp (L^(6/25:ℝ)) ≤ z.u) (hWu' : Real.exp (L^(6/25:ℝ)) ≤ z'.u)
    (hbandq : ∀ j p,p∈z.allBands j → q<p) (hbandq' : ∀ j p,p∈z'.allBands j → q<p)
    (hβrough : ∀ n∈Icc z.l z.r,z.β n≠0 → ∀ p∈Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n)
    (hβrough' : ∀ n∈Icc z'.l z'.r,z'.β n≠0 → ∀ p∈Nat.primesLE ⌊Real.exp (L^(6/25:ℝ))⌋₊,¬p∣n) :
    z.fixedComparableArcSource z' ξ ξ' cutoff ψ q h θ =
      ∑ χ : AddChar (MarkedUnitTuple q) ℂ,markedFourierCoeff (markedResiduePhase q h) χ*
        (z.fixedCharacterLeft ξ hL hM q χ θ hq hθ).comparableSource
          (z'.fixedCharacterRight ξ' hL hM q χ θ hq hθ) cutoff ψ θ := by
  unfold fixedComparableArcSource
  rw [markedMajor_arc_character_expansion]
  · rw [mul_sum]
    apply sum_congr rfl
    intro χ _
    rw [fixed_comparable_character_source_eq z z' ξ ξ' hL hM cutoff ψ q χ θ hq hθ hY]
    ring
  · intro v hv hcoeff
    exact markedMajor_fixed_bare_unit_support z.allBands z.allBands_prime cutoff z.Y
      (Real.exp (L^(6/25:ℝ))) z.modulation z.u z.v z.l z.r z.β ξ q hqW hWu hbandq hβrough v hv hcoeff
  · intro v hv hcoeff
    exact markedMajor_fixed_bare_conjugate_unit_support z'.allBands z'.allBands_prime cutoff z.Y
      (Real.exp (L^(6/25:ℝ))) z'.modulation z'.u z'.v z'.l z'.r z'.β ξ' q hqW hWu' hbandq' hβrough' v hv hcoeff

end MarkedMajorLabelEnergyData
end
end ArtinMatthews
