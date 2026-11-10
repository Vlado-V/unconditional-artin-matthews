module

public import ArtinMatthews.SourceKPCuspPrincipalCellIntegral
public import ArtinMatthews.SourceKPCuspProductCoordinates
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

/-! The literal adelic character on the native horizontal coordinates,
with a compact bounded Fourier test on every positive height box. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory StandardAdelic SourceHyperbolicGreen
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)

local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd

theorem sourceKPCuspUnitCellAdelicPoint_continuous :
    Continuous (sourceKPCuspUnitCellAdelicPoint K d hd) :=
  (ArchimedeanCharacterLattice.Construction.mixedAdelicAdd_continuous K).comp
    (sourceKPCuspCoordinates K d hd).symm.continuous

def sourceKPCuspNativeFrequency (m : K) (p : X) : ℂ :=
  character K (algebraMap K 𝔸[K] m *
    sourceKPCuspUnitCellAdelicPoint K d hd ((E).symm p).1)

theorem sourceKPCuspNativeFrequency_continuous (m : K) :
    Continuous (sourceKPCuspNativeFrequency K hζ d hd m) :=
  (character_continuous K).comp (continuous_const.mul
    ((sourceKPCuspUnitCellAdelicPoint_continuous K d hd).comp
      (continuous_fst.comp (E).symm.continuous)))

theorem sourceKPCuspNativeFrequency_norm (m : K) (p : X) :
    ‖sourceKPCuspNativeFrequency K hζ d hd m p‖ = 1 :=
  character_unitary K _

theorem sourceKPCuspNativeFrequency_coordinates (m : K) (x : I → ℝ) (y : V → ℝ) :
    sourceKPCuspNativeFrequency K hζ d hd m (E (x,y)) =
      character K (algebraMap K 𝔸[K] m * sourceKPCuspUnitCellAdelicPoint K d hd x) := by
  rw [sourceKPCuspNativeFrequency,(E).symm_apply_apply]

def sourceKPCuspNativeCompactBox (B : Set (V → ℝ)) : Set X :=
  E '' ((Set.Icc (0 : I → ℝ) 1) ×ˢ B)

theorem sourceKPCuspNativeCompactBox_isCompact (B : Set (V → ℝ)) (hB : IsCompact B) :
    IsCompact (sourceKPCuspNativeCompactBox K hζ d hd B) :=
  (isCompact_Icc.prod hB).image (E).continuous

theorem sourceKPCuspNativeCompactBox_positive (B : Set (V → ℝ))
    (hB : ∀ y ∈ B, ∀ v, 0 < y v) :
    sourceKPCuspNativeCompactBox K hζ d hd B ⊆ productUpper V := by
  rintro p ⟨⟨x,y⟩,hxy,rfl⟩ v _
  change 0 < E (x,y) v 2
  rw [sourceKPCuspProductCoordinates_height]
  exact hB y hxy.2 v

def sourceKPCuspNativeCellTest (m : K) (φ : (V → ℝ) → ℂ) (p : X) : ℂ :=
  if ((E).symm p).1 ∈ Set.univ.pi (fun _ : I => Set.Ioc (0:ℝ) 1) then
    sourceKPCuspNativeFrequency K hζ d hd m p * star (φ ((E).symm p).2) else 0

theorem sourceKPCuspNativeCellTest_measurable (m : K) (φ : (V → ℝ) → ℂ) (hφ : Measurable φ) :
    Measurable (sourceKPCuspNativeCellTest K hζ d hd m φ) := by
  apply Measurable.ite
  · exact (MeasurableSet.univ_pi fun _ => measurableSet_Ioc).preimage
      (continuous_fst.comp (E).symm.continuous).measurable
  · exact (sourceKPCuspNativeFrequency_continuous K hζ d hd m).measurable.mul
      (continuous_star.measurable.comp (hφ.comp (continuous_snd.comp (E).symm.continuous).measurable))
  · exact measurable_const

theorem sourceKPCuspNativeCellTest_bound (m : K) (φ : (V → ℝ) → ℂ)
    (B : Set (V → ℝ)) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y ∈ B, ‖φ y‖ ≤ C)
    (p : X) (hp : p ∈ sourceKPCuspNativeCompactBox K hζ d hd B) :
    ‖sourceKPCuspNativeCellTest K hζ d hd m φ p‖ ≤ C := by
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := hp
  unfold sourceKPCuspNativeCellTest
  rw [(E).symm_apply_apply]
  split_ifs
  · rw [norm_mul,norm_star,sourceKPCuspNativeFrequency_norm,one_mul]
    exact hb y hxy.2
  · simpa only [norm_zero] using hC

theorem sourceKPCuspNativeCellTest_coordinates (m : K) (φ : (V → ℝ) → ℂ)
    (x : I → ℝ) (y : V → ℝ) (hx : x ∈ Set.univ.pi (fun _ : I => Set.Ioc (0:ℝ) 1)) :
    star (sourceKPCuspNativeCellTest K hζ d hd m φ (E (x,y))) =
      star (character K (algebraMap K 𝔸[K] m*sourceKPCuspUnitCellAdelicPoint K d hd x))*φ y := by
  rw [sourceKPCuspNativeCellTest,(E).symm_apply_apply,if_pos hx,star_mul,
    star_star,sourceKPCuspNativeFrequency_coordinates]
  exact mul_comm _ _

end
end ArtinMatthews
