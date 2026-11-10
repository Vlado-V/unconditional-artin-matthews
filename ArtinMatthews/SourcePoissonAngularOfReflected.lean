module

public import ArtinMatthews.SourcePoissonAdditiveSecondMoment
public import ArtinMatthews.SourcePoissonPhysicalSignalComparison
public import ArtinMatthews.SourcePoissonPhysicalMomentExponent
public import ArtinMatthews.SourcePoissonPhysicalOnlyComparison
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical VaryingKummerAnalytic QuadraticWeil StandardAdelic
open Filter Asymptotics
open scoped NumberField Classical Topology BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "OS" => sourceRing F S₀
local notation "D" => sNormOneFundamentalSet F S

def sourcePoissonPhysicalNonzeroRows {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) : Finset OS :=
  (sourcePoissonPhysicalRows F S₀ hζ hX hY).erase 0

theorem sourcePoissonPhysicalNonzeroRows_mem {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (m : OS) :
    m ∈ sourcePoissonPhysicalNonzeroRows F S₀ hζ hX hY ↔
      m ≠ 0 ∧ m ∈ sourceScaledLatticeRows F S₀ hζ (sourcePoissonLogRowBox F S₀ hζ) (X * Y) := by
  rw [sourcePoissonPhysicalNonzeroRows, Finset.mem_erase,
    sourcePoissonPhysicalRows_mem F S₀ hζ hX hY m]

theorem sourcePoissonPhysicalAdditiveFactor_at_zero (X Y : ℝ) (t : SNormOne F S) :
    sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t 0 = 0 := by
  simp [sourcePoissonPhysicalAdditiveFactor, sourcePoissonPhysicalAdditiveTerm, sourcePoissonOriginalTest_zero]

theorem sourcePoissonPhysicalAdditiveFactor_zero_outside_nonzeroRows {X Y : ℝ}
    (hX : 0 < X) (hY : 0 < Y) {t : SNormOne F S} (ht : t ∈ D)
    {m : OS} (hm : m ∉ sourcePoissonPhysicalNonzeroRows F S₀ hζ hX hY) :
    sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m = 0 := by
  by_cases h : m = 0
  · subst m
    exact sourcePoissonPhysicalAdditiveFactor_at_zero F S₀ hζ X Y t
  · apply sourcePoissonPhysicalAdditiveFactor_zero_outside_rows F S₀ hζ hX hY ht
    exact fun h' => hm (Finset.mem_erase.mpr ⟨h, h'⟩)

variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

def SourcePoissonReflectedSecondMoment (hBad : standardWeilBadPlaces F ⊆ S) : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ Z : ℝ in atTop, ∀ hZ : 0 < Z,
    (∑ m ∈ sourcePoissonPhysicalNonzeroRows F S₀ hζ
        (Real.rpow_pos_of_pos hZ (9 / 10 : ℝ)) (Real.rpow_pos_of_pos hZ (133 / 1000 : ℝ)),
      ‖reflectionCoefficientRow F hζ S₀ hBad η m Z‖ ^ 2) ≤
      B * Z ^ (533 / 500 + 1 / 50000 : ℝ)

/-- The original physical probe upper bound has exactly the reflected square
moment as its analytic input. Both factors use the same finite nonzero rows. -/
theorem sourcePoissonPhysicalProbe_bound_of_reflected (v : InfinitePlace F)
    (hBad : standardWeilBadPlaces F ⊆ S)
    (hRef : SourcePoissonReflectedSecondMoment F S₀ hζ η hBad) :
    sourcePoissonPhysicalProbeAtScales F S₀ hζ η v hBad =O[atTop]
      (fun Z : ℝ => Z ^ (933 / 2000 + 1 / 100000 : ℝ)) := by
  have htrace : traceBadPlaces F ⊆ S := fun _ hp => hBad (Finset.mem_union_left _ hp)
  obtain ⟨A, hA, hAdd⟩ := exists_sourcePoissonPhysicalAdditive_secondMoment F S₀ hζ htrace
  obtain ⟨B, hB, hRef⟩ := hRef
  apply sourcePoissonPhysicalProbe_bigO_of_square_moments F S₀ hζ η v hBad hA.le hB
  filter_upwards [hRef, eventually_ge_atTop (1 : ℝ)] with Z hR hZ₁
  intro t ht
  have hZ : 0 < Z := zero_lt_one.trans_le hZ₁
  let X := Z ^ (9 / 10 : ℝ)
  let Y := Z ^ (133 / 1000 : ℝ)
  have hX : 0 < X := Real.rpow_pos_of_pos hZ _
  have hY : 0 < Y := Real.rpow_pos_of_pos hZ _
  have hY₁ : 1 ≤ Y := Real.one_le_rpow hZ₁ (by norm_num)
  have hYX : Y ≤ X := Real.rpow_le_rpow_of_exponent_le hZ₁ (by norm_num)
  let M := sourcePoissonPhysicalNonzeroRows F S₀ hζ hX hY
  refine ⟨M, fun m hm => sourcePoissonPhysicalAdditiveFactor_zero_outside_nonzeroRows
    F S₀ hζ hX hY ht hm, ?_, hR hZ⟩
  have h := hAdd X Y hY₁ hYX M
    (fun m hm => ((sourcePoissonPhysicalNonzeroRows_mem F S₀ hζ hX hY m).mp hm).2) t
  exact h.trans_eq (by rw [div_eq_mul_inv, Real.rpow_neg hZ.le])

theorem sourcePoissonAngularSignal_bound_of_reflected (v : InfinitePlace F)
    (hBad : standardWeilBadPlaces F ⊆ S) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff F J ⊆ S)
    (hRef : SourcePoissonReflectedSecondMoment F S₀ hζ η hBad) :
    principalAngularGaussianSignal hζ η S =O[atTop]
      (fun Z : ℝ => Z ^ (7 / 15 - 1 / 20000 : ℝ)) :=
  sourcePoissonAngularSignal_bound_of_physical F S₀ hζ η v hBad hJ hcut
    (sourcePoissonPhysicalProbe_bound_of_reflected F S₀ hζ η v hBad hRef)

end
end ArtinMatthews.SourceEulerAssembly
