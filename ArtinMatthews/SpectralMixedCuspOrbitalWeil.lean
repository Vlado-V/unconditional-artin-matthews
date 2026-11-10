module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralInfinityOrbitalWeil
public import ArtinMatthews.SpectralMixedCuspBesselFibre
public import ArtinMatthews.SpectralMixedCuspKloostermanWeil
public import ArtinMatthews.SpectralTrueWidthOrbitalBudget
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Height-explicit Weil control of the actual mixed cusp positive
Bessel fiber, with the literal common-period multiplicity `r*s*s`. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0MixedBesselGeometricFibre_weil_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (r s q : ℕ) [NeZero r] [NeZero s] [NeZero q], r.Coprime s →
      ∀ (m n : ℤ), m ≠ 0 → n ≠ 0 →
      ∀ (ρ η : ℝ → ℝ), ContDiff ℝ ∞ ρ → ContDiff ℝ ∞ η → HasCompactSupport ρ → HasCompactSupport η →
        tsupport ρ ⊆ Ioi (0 : ℝ) → tsupport η ⊆ Ioi (0 : ℝ) →
        ∀ (A B M : ℝ), 0 < A → 0 < B → (∀ y ∈ tsupport ρ, A ≤ y) → (∀ z ∈ tsupport η, B ≤ z) →
          (∀ z : ℝ, ‖spectralKLHeightBaseTest η z‖ ≤ M) →
          ‖gamma0TrueWidthBesselGeometricFibre (r*s) (gamma0CuspOneOver s) 1 q n m ρ η‖ ≤
            D*spectralWeylCompactHeightBudget A B M ρ*((r : ℝ)*(s : ℝ)^2)*(q : ℝ)^(-(5/2 : ℝ)+ε)*
              ((Nat.gcd q (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ) := by
  obtain ⟨D,hD,hW⟩ := gamma0MixedKloosterman_weil hε
  refine ⟨D,hD,?_⟩
  intro r s q _ _ _ hcop m n hm hn ρ η hρ hη hcρ hcη hpρ hpη A B M hA hB hρlo hηlo hM
  let Q := spectralWeylCompactHeightBudget A B M ρ
  let G := ((Nat.gcd q (Int.gcd m n) : ℕ) : ℝ)^(1/2 : ℝ)
  let L := (r : ℝ)*(s : ℝ)^2
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hQ : 0 ≤ Q := spectralWeylCompactHeightBudget_nonneg hA hB ((norm_nonneg _).trans (hM 0)) ρ
  have hq : 0 < (q : ℝ) := Nat.cast_pos.mpr (NeZero.pos q)
  have hBnd := gamma0TrueWidthBesselGeometricFibre_height_bound (r*s) q (gamma0CuspOneOver s) 1
    n m hn hm ρ η hρ hη hcρ hcη hpρ hpη hA hB hρlo hηlo hM
  have hLe : ((gamma0CuspFrequencyStep (r*s) 1 : ℝ)*(gamma0CuspFrequencyStep (r*s) (gamma0CuspOneOver s) : ℝ)) = L := by
    rw [gamma0CuspFrequencyStep_identity,gamma0MixedCuspFrequencyStep r s hcop,Nat.cast_mul]
    change (r : ℝ)*(s : ℝ)*(s : ℝ) = (r : ℝ)*(s : ℝ)^2
    rw [pow_two,mul_assoc]
  rw [hLe] at hBnd
  have hK : ‖gamma0TrueWidthKloostermanSum (r*s) (gamma0CuspOneOver s) 1 q n m‖ ≤ D*(q : ℝ)^((1/2 : ℝ)+ε)*G :=
    hW r s q hcop m n
  have hqPow : ((q : ℝ)^3)⁻¹ = (q : ℝ)^(-(3 : ℝ)) := by
    rw [Real.rpow_neg hq.le]
    norm_num
  have hExp : (q : ℝ)^((1/2 : ℝ)+ε)*(q : ℝ)^(-(3 : ℝ)) = (q : ℝ)^(-(5/2 : ℝ)+ε) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring_nf
  change _ ≤ D*Q*L*(q : ℝ)^(-(5/2 : ℝ)+ε)*G
  calc
    _ ≤ L*(D*(q : ℝ)^((1/2 : ℝ)+ε)*G)*(Q/(q : ℝ)^3) :=
      hBnd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hL)
        (div_nonneg hQ (pow_nonneg hq.le _)))
    _ = D*Q*L*((q : ℝ)^((1/2 : ℝ)+ε)*(q : ℝ)^(-(3 : ℝ)))*G := by
      rw [div_eq_mul_inv Q ((q : ℝ)^3),hqPow]
      ring_nf
    _ = _ := by rw [hExp]

end ArtinMatthews
