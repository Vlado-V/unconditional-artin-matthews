module

public import ArtinMatthews.SourceKPCuspNativeFrequency
public import ArtinMatthews.SourceKPCuspNativeIntegral
public import ArtinMatthews.SourceKPCompactNativeEisensteinTest
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

/-! A genuine bounded Fourier test on a full-dimensional compact cusp
band, and its meromorphic value on the actual Eisenstein family. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory SourceHyperbolicGreen Filter
open scoped NumberField AdeleRing MatrixGroups Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd

theorem sourceKPCuspNativeCompactBox_mem (B : Set (V → ℝ)) (p : X) :
    p ∈ sourceKPCuspNativeCompactBox K hζ d hd B ↔
      ((E).symm p).1 ∈ Set.Icc (0:I→ℝ) 1 ∧ ((E).symm p).2 ∈ B := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    simpa only [Set.mem_prod,(E).symm_apply_apply] using ha
  · intro hp
    exact ⟨(E).symm p,hp,(E).apply_symm_apply p⟩

theorem sourceKPCuspNativeBand_subset_compactBox (B : Set (V → ℝ)) :
    sourceKPCuspNativeBand K hζ d hd B ⊆ sourceKPCuspNativeCompactBox K hζ d hd B := by
  intro p hp
  apply (sourceKPCuspNativeCompactBox_mem K hζ d hd B p).mpr
  refine ⟨⟨?_,?_⟩,hp.2⟩
  · intro i
    exact (hp.1 i (Set.mem_univ i)).1.le
  · intro i
    exact (hp.1 i (Set.mem_univ i)).2


private theorem fourierNativeTest_bound (B : Set (InfinitePlace K → ℝ)) (m : K) :
    ∀ p ∈ (sourceKPCuspNativeCompactBox K hζ d hd B), ‖sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1) p‖ ≤ 1 :=
  fun p hp => sourceKPCuspNativeCellTest_bound K hζ d hd m (fun _ => 1) B zero_le_one
    (fun _ _ => by simp) p hp

def sourceKPCuspNativeFourierTest (qf : SourceKPFiniteAdeleProjective K hζ)
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) (m : K) {T : ℝ} (hT : 1 ≤ T) (s : ℂ) : ℂ :=
  sourceKPCompactNativeEisensteinTest K hζ (QuotientGroup.mk qf) (sourceKPCuspNativeCompactBox K hζ d hd B) (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB) (sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos)
    (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1))
    (sourceKPCuspNativeCellTest_measurable K hζ d hd m (fun _ => 1) measurable_const)
    1 (fourierNativeTest_bound K hζ d hd B m) hT s

def sourceKPCuspNativeFourierResidue (qf : SourceKPFiniteAdeleProjective K hζ)
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) (m : K) {T : ℝ} (hT : 1 ≤ T) : ℂ :=
  sourceKPCompactNativeResidueTest K hζ (QuotientGroup.mk qf) (sourceKPCuspNativeCompactBox K hζ d hd B) (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB) (sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos)
    (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1))
    (sourceKPCuspNativeCellTest_measurable K hζ d hd m (fun _ => 1) measurable_const)
    1 (fourierNativeTest_bound K hζ d hd B m) hT

theorem sourceKPCuspNativeFourierTest_meromorphic (qf : SourceKPFiniteAdeleProjective K hζ)
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) (m : K) {T : ℝ} (hT : 1 ≤ T) :
    MeromorphicOn (sourceKPCuspNativeFourierTest K hζ d hd qf B hB hpos m hT) {s : ℂ | 0 < s.re} :=
  sourceKPCompactNativeEisensteinTest_meromorphic K hζ (QuotientGroup.mk qf)
    (sourceKPCuspNativeCompactBox K hζ d hd B) (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB) (sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos)
    (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1))
    (sourceKPCuspNativeCellTest_measurable K hζ d hd m (fun _ => 1) measurable_const)
    1 (fourierNativeTest_bound K hζ d hd B m) hT

theorem sourceKPCuspNativeFourierTest_residue_tendsto (qf : SourceKPFiniteAdeleProjective K hζ)
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) (m : K) {T : ℝ} (hT : 1 ≤ T) :
    Tendsto (fun s => (s-1/6)*sourceKPCuspNativeFourierTest K hζ d hd qf B hB hpos m hT s)
      (𝓝[≠] (1/6:ℂ)) (𝓝 (sourceKPCuspNativeFourierResidue K hζ d hd qf B hB hpos m hT)) :=
  sourceKPCompactNativeEisensteinTest_residue_tendsto K hζ (QuotientGroup.mk qf)
    (sourceKPCuspNativeCompactBox K hζ d hd B) (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB) (sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos)
    (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1))
    (sourceKPCuspNativeCellTest_measurable K hζ d hd m (fun _ => 1) measurable_const)
    1 (fourierNativeTest_bound K hζ d hd B m) hT

theorem sourceKPCuspNativeFourierTest_initial (qf : SourceKPFiniteAdeleProjective K hζ)
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) (m : K) {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1) :
    sourceKPCuspNativeFourierTest K hζ d hd qf B hB hpos m hT s =
      ∫ p in (sourceKPCuspNativeCompactBox K hζ d hd B), star (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1) p) *
        sourceKPAutomorphicCompactEisenstein K hζ s
          (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p)
        ∂productVolume V :=
  sourceKPCompactNativeEisensteinTest_initial K hζ (QuotientGroup.mk qf)
    (sourceKPCuspNativeCompactBox K hζ d hd B) (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB) (sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos)
    (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1))
    (sourceKPCuspNativeCellTest_measurable K hζ d hd m (fun _ => 1) measurable_const)
    1 (fourierNativeTest_bound K hζ d hd B m) hT hs

theorem sourceKPCuspNativeFourierTest_integrableOn (qf : SourceKPFiniteAdeleProjective K hζ)
    (B : Set (InfinitePlace K → ℝ)) (hB : IsCompact B)
    (hpos : ∀ y ∈ B, ∀ v, 0 < y v) (m : K) {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1) :
    IntegrableOn (fun p => star (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1) p) *
      sourceKPAutomorphicCompactEisenstein K hζ s
        (sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf) p)) (sourceKPCuspNativeCompactBox K hζ d hd B) (productVolume V) :=
  sourceKPCompactNativeEisensteinTest_initial_integrableOn K hζ (QuotientGroup.mk qf)
    (sourceKPCuspNativeCompactBox K hζ d hd B) (sourceKPCuspNativeCompactBox_isCompact K hζ d hd B hB) (sourceKPCuspNativeCompactBox_positive K hζ d hd B hpos)
    (sourceKPCuspNativeCellTest K hζ d hd m (fun _ => 1))
    (sourceKPCuspNativeCellTest_measurable K hζ d hd m (fun _ => 1) measurable_const)
    1 (fourierNativeTest_bound K hζ d hd B m) hT hs

end
end ArtinMatthews
