module

public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralModularPartitionGamma0
public import ArtinMatthews.SpectralPeterssonCutPacket
public import ArtinMatthews.SpectralPeterssonGammaTail
public import ArtinMatthews.SpectralPeterssonCutMeasurable
public import ArtinMatthews.SpectralPeterssonCutNormUnfold
public import ArtinMatthews.SpectralPeterssonCutPacketPointwise
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized sharp-cut Poincare packet has a congruence-level
L2 bound, including weight two, before any holomorphic reproduction step. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped MatrixGroups BigOperators

namespace ArtinMatthews

variable {ι : Type*}

private theorem cutPacket_norm_of_pointwise (N : ℕ) [NeZero N] (a : SL(2, ℤ))
    (k : ℕ) (hk : 2 ≤ k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A : ℝ} (hA : 0 < A) (hn : Set.InjOn n (t : Set ι)) (C : ℝ)
    (hbound : ∀ z : UpperHalfPlane,
      ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k ≤
        C*(∑' p : Gamma0PeterssonSignedRow N 1 a,
          ‖gamma0PeterssonCutPacketRow N a k t α n A p z‖^2*z.im^k)) :
    IntegrableOn (fun z => ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k)
      (gamma0InteriorRegion N) ∧
    (∫ z in gamma0InteriorRegion N, ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k) ≤
      2*C*(spectralPeterssonGammaTailRatio k A*∑ j ∈ t, ‖α j‖^2) := by
  let R (z : UpperHalfPlane) := ∑' p : Gamma0PeterssonSignedRow N 1 a,
    ‖gamma0PeterssonCutPacketRow N a k t α n A p z‖^2*z.im^k
  have hR : IntegrableOn R (gamma0InteriorRegion N) :=
    gamma0PeterssonCutPacket_row_integrable N a k hk t α n A hA.le hn
  have hEnv := hR.const_mul C
  have hmeas : Measurable (fun z : UpperHalfPlane =>
      ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k) :=
    ((gamma0PeterssonCutPacket_measurable N a k t α n hA).norm.pow_const 2).mul
      (by fun_prop)
  have hInt : IntegrableOn (fun z : UpperHalfPlane =>
      ‖gamma0PeterssonCutPacket N a k t α n A z‖^2*z.im^k) (gamma0InteriorRegion N) := by
    apply hEnv.mono' hmeas.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg z.im_pos.le _))]
    exact hbound z
  refine ⟨hInt,?_⟩
  calc
    _ ≤ ∫ z in gamma0InteriorRegion N, C*R z :=
      integral_mono hInt hEnv (fun z => hbound z)
    _ = _ := by
      rw [integral_const_mul,gamma0PeterssonCutPacket_row_mass N a k hk t α n A hA.le hn]
      ring

theorem gamma0PeterssonCutPacket_infinity_norm (N : ℕ) [NeZero N]
    (k : ℕ) (hk : 2 ≤ k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hn : Set.InjOn n (t : Set ι))
    (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B) :
    IntegrableOn (fun z => ‖gamma0PeterssonCutPacket N 1 k t α n A z‖^2*z.im^k)
      (gamma0InteriorRegion N) ∧
    (∫ z in gamma0InteriorRegion N, ‖gamma0PeterssonCutPacket N 1 k t α n A z‖^2*z.im^k) ≤
      2*(1+8*Real.pi*B/((N : ℝ)*A))*(spectralPeterssonGammaTailRatio k A*∑ j ∈ t, ‖α j‖^2) :=
  cutPacket_norm_of_pointwise N 1 k hk t α n hA hn _
    (gamma0PeterssonCutPacket_infinity_pointwise N k t α n hA hB hnB)

theorem gamma0PeterssonCutPacket_mixed_norm (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (k : ℕ) (hk : 2 ≤ k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (hn : Set.InjOn n (t : Set ι))
    (hnB : ∀ j ∈ t, (n j : ℝ) ≤ B) :
    IntegrableOn (fun z => ‖gamma0PeterssonCutPacket (r*s) (gamma0CuspOneOver s) k t α n A z‖^2*z.im^k)
      (gamma0InteriorRegion (r*s)) ∧
    (∫ z in gamma0InteriorRegion (r*s), ‖gamma0PeterssonCutPacket (r*s) (gamma0CuspOneOver s) k t α n A z‖^2*z.im^k) ≤
      2*(1+8*Real.pi*B/(((r*s : ℕ) : ℝ)*A))*(spectralPeterssonGammaTailRatio k A*∑ j ∈ t, ‖α j‖^2) :=
  cutPacket_norm_of_pointwise (r*s) (gamma0CuspOneOver s) k hk t α n hA hn _
    (gamma0PeterssonCutPacket_mixed_pointwise r s hcop k t α n hA hB hnB)

end ArtinMatthews
