module

public import ArtinMatthews.MarkedMinorArcBanRawEntry
public import ArtinMatthews.MarkedMinorArcBanAdjoint
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual physical endpoint projections make the ban symmetric;
reflection and conjugation handle the column cutoff without an evenness premise. -/
noncomputable section
namespace ArtinMatthews

open Matrix

def markedRawBanMajorant {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (ψ : ℝ → ℂ) (Q Y : ℝ)
    (bg : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z) : ℝ := by
  classical
  exact if (markedRawCopiedProduct bg.1:ℤ) ∣ markedMinorIntegerDet u.1.1 v.1.1 then
    ‖markedBanRemovedCoefficient (MarkedRawCleanBan bg u v)
      (markedBanEdgeKernel ψ Q Y (markedRawLastProduct u.2:ℤ) (markedRawLastProduct v.2:ℤ)
        (markedBanNormalizedDet u.1.1 (markedRawCopiedProduct bg.1:ℤ) v.1.1))‖ else 0

theorem markedRawBanMajorant_nonneg {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (ψ : ℝ → ℂ) (Q Y : ℝ)
    (bg : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z) :
    0 ≤ markedRawBanMajorant ψ Q Y bg u v := by
  classical
  unfold markedRawBanMajorant
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

theorem markedRawEndpointFactor_ne_zero_distinct {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ρ : ℝ) (χ : MarkedRawState P M B Z → ℂ)
    (s : MarkedRawState P M B Z) (h : markedRawEndpointFactor hZ ρ χ s ≠ 0) :
    MarkedRawActiveDistinct s.2.1 := by
  classical
  by_contra hn
  exact h (by simp [markedRawEndpointFactor,hn])

theorem markedRawCleanBan_symmetric {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (bg : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z)
    (hu : MarkedRawActiveDistinct (markedRawBanSourceActive bg u))
    (hv : MarkedRawActiveDistinct (markedRawBanSourceActive bg v)) :
    MarkedRawCleanBan bg u v ↔ MarkedRawCleanBan bg v u := by
  exact markedRawFullCrossBan_symmetric hd bg.1 u.2 v.2 hu hv

theorem markedBanNormalizedDet_reverse (z v : ℤ × ℤ) (D : ℤ)
    (hd : D ∣ markedMinorIntegerDet z v) :
    markedBanNormalizedDet v D z = -markedBanNormalizedDet z D v := by
  have he : markedMinorIntegerDet v z = -markedMinorIntegerDet z v := by
    unfold markedMinorIntegerDet
    ring
  unfold markedBanNormalizedDet
  rw [he,Int.neg_ediv_of_dvd hd]

theorem markedRawBanMajorant_adjoint {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (ψ : ℝ → ℂ) (Q Y : ℝ)
    (bg : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z)
    (hban : MarkedRawCleanBan bg u v ↔ MarkedRawCleanBan bg v u) :
    markedRawBanMajorant ψ Q Y bg u v =
      markedRawBanMajorant (markedBanAdjointCutoff ψ) Q Y bg v u := by
  classical
  have he : markedMinorIntegerDet v.1.1 u.1.1 = -markedMinorIntegerDet u.1.1 v.1.1 := by
    unfold markedMinorIntegerDet
    ring
  unfold markedRawBanMajorant
  simp only [he,dvd_neg]
  split_ifs with hd
  · rw [show markedBanNormalizedDet v.1.1 (markedRawCopiedProduct bg.1:ℤ) u.1.1 =
      -markedBanNormalizedDet u.1.1 (markedRawCopiedProduct bg.1:ℤ) v.1.1 from
        markedBanNormalizedDet_reverse _ _ _ hd,markedBanEdgeKernel_adjoint]
    simp only [markedBanRemovedCoefficient_norm,hban,RCLike.norm_conj]
  · rfl

theorem markedRawBanErrorKernel_column_entry_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q : ℝ) {ρ H : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hH : 0 ≤ H)
    (hη : ∀ t, ‖η t‖ ≤ H) (χ : MarkedRawState P (pads+1) B Z → ℂ) (hχ : ∀ s, ‖χ s‖ ≤ 1)
    (bg : MarkedRawBackground P pads B) (u v : MarkedRawCleanFiber P Z) :
    ‖markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ bg u v‖ ≤
      H^2*markedRawBanMajorant (markedBanAdjointCutoff ψ) Q Y bg v u := by
  classical
  by_cases hu : markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (bg,u))=0
  · have hz : markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ bg u v=0 := by
      simp [markedRawBanErrorKernel_entry_factor,markedRawBanPrefactor,hu]
    rw [hz,norm_zero]
    exact mul_nonneg (sq_nonneg H) (markedRawBanMajorant_nonneg _ _ _ _ _ _)
  by_cases hv : markedRawEndpointFactor hZ ρ χ ((markedRawStateSplit pads B Z).symm (bg,v))=0
  · have hz : markedRawBanErrorKernel hZ ψ η d₀ Y Q ρ χ bg u v=0 := by
      simp [markedRawBanErrorKernel_entry_factor,markedRawBanPrefactor,hv]
    rw [hz,norm_zero]
    exact mul_nonneg (sq_nonneg H) (markedRawBanMajorant_nonneg _ _ _ _ _ _)
  have hban := markedRawCleanBan_symmetric hd bg u v
    (markedRawEndpointFactor_ne_zero_distinct hZ ρ χ _ hu)
    (markedRawEndpointFactor_ne_zero_distinct hZ ρ χ _ hv)
  have hbound := markedRawBanErrorKernel_entry_norm_le hZ ψ η d₀ Y Q hρ₀ hρ₁ hH hη χ hχ bg u v
  change ‖_‖ ≤ H^2*markedRawBanMajorant ψ Q Y bg u v at hbound
  rwa [markedRawBanMajorant_adjoint ψ Q Y bg u v hban] at hbound

end ArtinMatthews
