module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Cutoff
public import OAI.Analysis.PDE.Weak.Elliptic.Difference
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import OAI.Analysis.PDE.Weak.Elliptic.Coefficient


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory
namespace OAI.Analysis.PDE.Weak

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure X) [μ.IsAddRightInvariant]

theorem differenceQuotientL2_vectorProduct (g : X → E) (hg : Continuous g) {M L : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (v : X) (h : ℝ)
    (hL : ∀ x, ‖differenceQuotient v h g x‖ ≤ L) (u : Lp ℝ 2 μ) :
    differenceQuotientL2 μ v h (vectorProductL2 g hg hM u) =
      vectorProductL2 g hg hM (differenceQuotientL2 μ v h u) +
        vectorProductL2 (differenceQuotient v h g) (continuous_differenceQuotient v h hg)
          hL (translateL2 μ (h • v) u) := by
  apply Lp.ext
  have ht := (measurePreserving_add_right μ (h • v)).quasiMeasurePreserving.ae
    (vectorProductL2_ae g hg hM u)
  filter_upwards [coe_differenceQuotientL2 μ v h (vectorProductL2 g hg hM u),
    vectorProductL2_ae g hg hM u, ht,
    Lp.coeFn_add (vectorProductL2 g hg hM (differenceQuotientL2 μ v h u))
      (vectorProductL2 (differenceQuotient v h g) (continuous_differenceQuotient v h hg)
        hL (translateL2 μ (h • v) u)),
    vectorProductL2_ae g hg hM (differenceQuotientL2 μ v h u),
    vectorProductL2_ae (differenceQuotient v h g) (continuous_differenceQuotient v h hg)
      hL (translateL2 μ (h • v) u), coe_differenceQuotientL2 μ v h u,
    coe_translateL2 μ (h • v) u] with x hx hy hz hw ha hb hc hd
  rw [hx, hw]
  simp only [Pi.add_apply, ha, hb, hc, hd, differenceQuotient, hy, hz]
  module

theorem norm_differenceQuotientL2_vectorProduct_le
    (g : X → E) (hg : Continuous g) {M L : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (v : X) (h : ℝ)
    (hL : ∀ x, ‖differenceQuotient v h g x‖ ≤ L) (u : Lp ℝ 2 μ) :
    ‖differenceQuotientL2 μ v h (vectorProductL2 g hg hM u)‖ ≤
      M * ‖differenceQuotientL2 μ v h u‖ + L * ‖u‖ := by
  rw [differenceQuotientL2_vectorProduct μ g hg hM v h hL u]
  have hb := norm_vectorProductL2_le (differenceQuotient v h g)
    (continuous_differenceQuotient v h hg) hL (translateL2 μ (h • v) u)
  rw [norm_translateL2] at hb
  exact (norm_add_le _ _).trans
    (add_le_add (norm_vectorProductL2_le g hg hM _) hb)

variable [IsLocallyFiniteMeasure μ]

omit [NormedSpace ℝ X] [μ.IsAddRightInvariant] in
theorem integrable_vectorProductL2 (g : X → E) (hg : Continuous g)
    (hs : HasCompactSupport g) {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) (u : Lp ℝ 2 μ) :
    Integrable (vectorProductL2 g hg hM u : X → E) μ := by
  have hu : IntegrableOn (vectorProductL2 g hg hM u : X → E) (tsupport g) μ := by
    have : IsFiniteMeasure (μ.restrict (tsupport g)) :=
      ⟨by simpa using hs.isCompact.measure_lt_top (μ := μ)⟩
    exact ((Lp.memLp (vectorProductL2 g hg hM u)).restrict (tsupport g)).integrable (by norm_num)
  have he : (vectorProductL2 g hg hM u : X → E) =ᵐ[μ]
      (tsupport g).indicator (vectorProductL2 g hg hM u : X → E) := by
    filter_upwards [vectorProductL2_ae g hg hM u] with x hx
    by_cases hxs : x ∈ tsupport g
    · simp [hxs]
    · rw [indicator_of_notMem hxs, hx, image_eq_zero_of_notMem_tsupport hxs, smul_zero]
  exact (hu.integrable_indicator isClosed_closure.measurableSet).congr he.symm

end OAI.Analysis.PDE.Weak
