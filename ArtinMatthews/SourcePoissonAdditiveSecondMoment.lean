module

public import ArtinMatthews.SourceAdditiveCompactBox
public import ArtinMatthews.SourcePoissonProbeRowBox
public import ArtinMatthews.SourceAdditiveFractionSupport
public import ArtinMatthews.SourcePoissonAdditiveModeSieve
public import ArtinMatthews.SourcePoissonFiniteL2Fourier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "OS" => sourceRing F S₀
local notation "D" => sNormOneFundamentalSet F S

/-- The actual additive second moment on any finite subset of the common scaled box. -/
theorem exists_sourcePoissonPhysicalAdditive_secondMoment (htrace : traceBadPlaces F ⊆ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y : ℝ), 1 ≤ Y → Y ≤ X →
      ∀ (M : Finset OS), (∀ m ∈ M,
        m ∈ sourceScaledLatticeRows F S₀ hζ (sourcePoissonLogRowBox F S₀ hζ) (X * Y)) →
      ∀ t : SNormOne F S,
      (∑ m ∈ M, ‖sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m‖ ^ 2) ≤ C / Y := by
  obtain ⟨C, hC, hSieve⟩ := exists_sourcePoissonLogAdditiveMode_sieve F S₀ hζ htrace
  let K := sourceProbeLogFourierCost F hζ S
  let L := ∑' j, K j
  refine ⟨(L ^ 2 + 1) * C, by positivity, ?_⟩
  intro X Y hY hXY M hM t
  have hY₀ : 0 < Y := zero_lt_one.trans_le hY
  have hX₀ : 0 < X := hY₀.trans_le hXY
  have hN : 0 < X * Y := mul_pos hX₀ hY₀
  let f (j : ℤ) (m : M) :=
    sourceProbeLogFourierCoeff F hζ S (sourcePoissonOriginalLogPoint F S₀ hζ X Y t m.val) j
  let g (j : ℤ) (m : M) := sourcePoissonLogAdditiveMode F S₀ hζ hY₀ j m.val
  have hG (j : ℤ) : (∑ m : M, ‖g j m‖ ^ 2) ≤ C * (X * Y) / Y := by
    change (∑ m : M, ‖sourcePoissonLogAdditiveMode F S₀ hζ hY₀ j m.val‖ ^ 2) ≤ _
    exact (Finset.sum_coe_sort M
      (fun m : OS => ‖sourcePoissonLogAdditiveMode F S₀ hζ hY₀ j m‖ ^ 2)).le.trans
      (hSieve X Y hY hXY M hM j)
  have h := sourcePoissonFiniteL2_fourier_cost f g K
    (sourceProbeLogFourierCost_summable F hζ S)
    (sourceProbeLogFourierCost_nonneg F hζ S)
    (fun j m => sourceProbeLogFourierCoeff_norm_le_cost F hζ S _ j)
    (C * (X * Y) / Y) (by positivity) hG
  have hF (m : M) : ‖sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m.val‖ ^ 2 =
      (X * Y)⁻¹ * ‖∑' j, f j m * g j m‖ ^ 2 := by
    rw [sourcePoissonPhysicalAdditiveFactor_eq_logModes F S₀ hζ hX₀ hY₀,
      norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt hN.le]
  rw [← Finset.sum_coe_sort M
    (fun m : OS => ‖sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m‖ ^ 2)]
  simp only [hF, ← Finset.mul_sum]
  calc
    _ ≤ (X * Y)⁻¹ * (L ^ 2 * (C * (X * Y) / Y)) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hN.le)
    _ = L ^ 2 * C / Y := by field_simp
    _ ≤ _ := by gcongr; linarith

/-- The exact compact lattice support shared with the reflected coefficients. -/
def sourcePoissonPhysicalRows {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) : Finset OS :=
  (sourceScaledLatticeRows_finite F S₀ hζ (sourcePoissonLogRowBox F S₀ hζ)
    (sourcePoissonLogRowBox_isCompact F S₀ hζ) (mul_pos hX hY)).toFinset

theorem sourcePoissonPhysicalRows_mem {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (m : OS) :
    m ∈ sourcePoissonPhysicalRows F S₀ hζ hX hY ↔
      m ∈ sourceScaledLatticeRows F S₀ hζ (sourcePoissonLogRowBox F S₀ hζ) (X * Y) :=
  Set.Finite.mem_toFinset _

theorem sourcePoissonPhysicalAdditiveFactor_zero_outside_rows {X Y : ℝ}
    (hX : 0 < X) (hY : 0 < Y) {t : SNormOne F S} (ht : t ∈ D)
    {m : OS} (hm : m ∉ sourcePoissonPhysicalRows F S₀ hζ hX hY) :
    sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m = 0 :=
  sourcePoissonPhysicalAdditiveFactor_zero_outside_scaledBox F S₀ hζ hX hY ht
    (fun h => hm ((sourcePoissonPhysicalRows_mem F S₀ hζ hX hY m).mpr h))

end
end ArtinMatthews.SourceEulerAssembly
