module

public import ArtinMatthews.SpectralRellichRectangle
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import ArtinMatthews.SpectralCompactCutoff
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Actual simultaneous compact cores for the finite inverse-coset charts. -/

noncomputable section
open Set
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0TruncatedCore (N : ℕ) [NeZero N] (Y : ℝ) : Set UpperHalfPlane :=
  ⋃ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
    (fun z : UpperHalfPlane => q.out⁻¹ • z) '' ModularGroup.truncatedFundamentalDomain Y

theorem gamma0TruncatedCore_compact (N : ℕ) [NeZero N] (Y : ℝ) :
    IsCompact (gamma0TruncatedCore N Y) := by
  apply isCompact_iUnion
  intro q
  have hc : Continuous (fun z : UpperHalfPlane => q.out⁻¹ • z) := by
    change Continuous (fun z : UpperHalfPlane => Matrix.SpecialLinearGroup.mapGL ℝ q.out⁻¹ • z)
    exact continuous_const_smul _
  exact (ModularGroup.isCompact_truncatedFundamentalDomain Y).image hc

theorem gamma0TruncatedCore_mem (N : ℕ) [NeZero N] {Y : ℝ}
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) {z : UpperHalfPlane}
    (hz : z ∈ ModularGroup.fd) (hy : z.im ≤ Y) : q.out⁻¹ • z ∈ gamma0TruncatedCore N Y :=
  mem_iUnion.mpr ⟨q,⟨z,⟨hz,hy⟩,rfl⟩⟩

/-- One actual compact smooth cutoff is identically one on every truncated
inverse-coset chart; its residual is uniformly bounded by one everywhere. -/
theorem gamma0TruncatedCore_cutoff (N : ℕ) [NeZero N] (Y : ℝ) :
    ∃ (A a b : ℝ) (φ : SchwartzMap (ℝ × ℝ) ℂ),
      0 < a ∧ a ≤ b ∧ tsupport φ ⊆ spectralPlaneRectangle A a b ∧
      (∀ (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane),
        z ∈ ModularGroup.fd → z.im ≤ Y → φ ((q.out⁻¹ • z).re,(q.out⁻¹ • z).im) = 1) ∧
      (∀ p, ‖φ p‖ ≤ 1) ∧ (∀ p, ‖1-φ p‖ ≤ 1) := by
  obtain ⟨A,a,b,φ,ha,hab,hs,hp,hn,hr⟩ :=
    exists_compact_hyperbolic_cutoff (gamma0TruncatedCore_compact N Y)
  exact ⟨A,a,b,φ,ha,hab,hs,fun q z hz hy => hp _ (gamma0TruncatedCore_mem N q hz hy),hn,hr⟩

end ArtinMatthews
