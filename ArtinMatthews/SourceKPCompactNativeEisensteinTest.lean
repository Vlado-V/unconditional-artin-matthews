module

public import ArtinMatthews.SourceKPCompactNativeTestSupport
public import ArtinMatthews.SourceKPAutomorphicEisensteinLocalL2
public import ArtinMatthews.SourceKPAutomorphicCompactTopology
public import ArtinMatthews.SourceKPAutomorphicEisensteinLocalCompatibility
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
public import OAI.NumberTheory.DirichletL.Eisenstein.MeromorphicResolvent


set_option backward.privateInPublic true
@[expose] public section

/-! Scalar compact native tests of the actual meromorphic Eisenstein continuation and residue. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter Set
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ)

local notation "X" => ProductSpace (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)
local notation "q" => sourceKPCompactCoordinateProjection K hζ b

def sourceKPCompactNativeEisensteinTest (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T : ℝ} (hT : 1 ≤ T) (s : ℂ) : ℂ :=
  sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC
    (sourceKPAutomorphicEisensteinLocalL2 K hζ hT
      (sourceKPCompactNativeTestImage K hζ b S)
      (sourceKPCompactNativeTestImage_isCompact K hζ b S hS hSu) s)

def sourceKPCompactNativeResidueTest (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T : ℝ} (hT : 1 ≤ T) : ℂ :=
  sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC
    (sourceKPAutomorphicExceptionalResidue K hζ hT).val


theorem sourceKPCompactNativeEisensteinTest_initial (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    sourceKPCompactNativeEisensteinTest K hζ b S hS hSu φ hφ C hC hT s =
      ∫ x in S, star (φ x) * sourceKPAutomorphicCompactEisenstein K hζ s (q x) ∂ν := by
  let Q := sourceKPCompactNativeTestImage K hζ b S
  have hQ : IsCompact Q := sourceKPCompactNativeTestImage_isCompact K hζ b S hS hSu
  have hinit := sourceKPAutomorphicEisensteinLocalL2_ae K hζ hT Q hQ hs
  calc
    _ = ∫ x in S, star (φ x) *
        ((Q).indicator (sourceKPAutomorphicCompactEisenstein K hζ s)) (q x) ∂ν :=
      sourceKPCompactSetMassPairing_apply_of_ae K hζ b S hS hSu φ hφ C hC
        (sourceKPAutomorphicEisensteinLocalL2 K hζ hT Q hQ s) hinit
    _ = _ := by
      apply setIntegral_congr_fun hS.measurableSet
      intro x hx
      dsimp only
      rw [Set.indicator_of_mem (sourceKPCompactNativeTestImage_mem K hζ b S hx)]

theorem sourceKPCompactNativeEisensteinTest_initial_integrableOn (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T : ℝ} (hT : 1 ≤ T) {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2 * s.re + 1) :
    IntegrableOn (fun x => star (φ x) * sourceKPAutomorphicCompactEisenstein K hζ s (q x)) S ν := by
  let Q := sourceKPCompactNativeTestImage K hζ b S
  have hQ : IsCompact Q := sourceKPCompactNativeTestImage_isCompact K hζ b S hS hSu
  have hinit := sourceKPAutomorphicEisensteinLocalL2_ae K hζ hT Q hQ hs
  have hi := sourceKPCompactSetMassPairing_integrableOn_of_ae K hζ b S hS hSu φ hφ C hC
    (sourceKPAutomorphicEisensteinLocalL2 K hζ hT Q hQ s) hinit
  apply hi.congr
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  rw [Set.indicator_of_mem (sourceKPCompactNativeTestImage_mem K hζ b S hx)]

theorem sourceKPCompactNativeEisensteinTest_meromorphic (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T : ℝ} (hT : 1 ≤ T) :
    MeromorphicOn (sourceKPCompactNativeEisensteinTest K hζ b S hS hSu φ hφ C hC hT)
      {s | 0 < s.re} := by
  let Q := sourceKPCompactNativeTestImage K hζ b S
  have hQ : IsCompact Q := sourceKPCompactNativeTestImage_isCompact K hζ b S hS hSu
  let A := sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC
  intro s hs
  exact OAI.CubicEisenstein.meromorphicAt_clm A
    (sourceKPAutomorphicEisensteinLocalL2_meromorphic K hζ hT Q hQ s hs)

theorem sourceKPCompactNativeResidueTest_integral_of_ae (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T : ℝ} (hT : 1 ≤ T)
    {u : Y → ℂ}
    (hu : ((sourceKPAutomorphicExceptionalResidue K hζ hT).val : Y → ℂ) =ᵐ[μ] u) :
    sourceKPCompactNativeResidueTest K hζ b S hS hSu φ hφ C hC hT =
      ∫ x in S, star (φ x) * u (q x) ∂ν :=
  sourceKPCompactSetMassPairing_apply_of_ae K hζ b S hS hSu φ hφ C hC
    (sourceKPAutomorphicExceptionalResidue K hζ hT).val hu

theorem sourceKPCompactNativeResidueTest_integral (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCompactNativeResidueTest K hζ b S hS hSu φ hφ C hC hT =
      ∫ x in S, star (φ x) * (sourceKPAutomorphicExceptionalResidue K hζ hT).val (q x) ∂ν :=
  sourceKPCompactNativeResidueTest_integral_of_ae K hζ b S hS hSu φ hφ C hC hT EventuallyEq.rfl

theorem sourceKPCompactNativeResidueTest_integrableOn (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T : ℝ} (hT : 1 ≤ T) :
    IntegrableOn (fun x => star (φ x) *
      (sourceKPAutomorphicExceptionalResidue K hζ hT).val (q x)) S ν :=
  sourceKPCompactSetMassPairing_integrableOn_of_ae K hζ b S hS hSu φ hφ C hC
    (sourceKPAutomorphicExceptionalResidue K hζ hT).val EventuallyEq.rfl

private theorem sourceKPCompactNativeResidueTest_cut (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T : ℝ} (hT : 1 ≤ T) :
    sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC
      (sourceKPAutomorphicGenuineCompactCutL2 K hζ
        (sourceKPCompactNativeTestImage K hζ b S)
        (sourceKPCompactNativeTestImage_isCompact K hζ b S hS hSu)
        (sourceKPAutomorphicExceptionalResidue K hζ hT)) =
      sourceKPCompactNativeResidueTest K hζ b S hS hSu φ hφ C hC hT := by
  let Q := sourceKPCompactNativeTestImage K hζ b S
  have hQ : IsCompact Q := sourceKPCompactNativeTestImage_isCompact K hζ b S hS hSu
  let A := sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC
  change A (measurableL2Cutoff μ Q (hQ).measurableSet
    (sourceKPAutomorphicExceptionalResidue K hζ hT).val) =
      A (sourceKPAutomorphicExceptionalResidue K hζ hT).val
  exact sourceKPCompactSetMassPairing_cutoff K hζ b S hS hSu φ hφ C hC Q (hQ).measurableSet
    Subset.rfl (sourceKPAutomorphicExceptionalResidue K hζ hT).val

theorem sourceKPCompactNativeEisensteinTest_residue_tendsto (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T : ℝ} (hT : 1 ≤ T) :
    Tendsto (fun s => (s - 1 / 6) *
      sourceKPCompactNativeEisensteinTest K hζ b S hS hSu φ hφ C hC hT s)
      (𝓝[≠] (1 / 6 : ℂ))
      (𝓝 (sourceKPCompactNativeResidueTest K hζ b S hS hSu φ hφ C hC hT)) := by
  let Q := sourceKPCompactNativeTestImage K hζ b S
  have hQ : IsCompact Q := sourceKPCompactNativeTestImage_isCompact K hζ b S hS hSu
  let A := sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC
  have h := ((A).continuous.tendsto _).comp
    (sourceKPAutomorphicEisensteinLocalL2_residue_tendsto K hζ hT Q hQ)
  rw [sourceKPCompactNativeResidueTest_cut K hζ b S hS hSu φ hφ C hC hT] at h
  simpa only [Function.comp_def, map_smul, smul_eq_mul, sourceKPCompactNativeEisensteinTest] using h

theorem sourceKPCompactNativeEisensteinTest_cutoff_independent (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T T' : ℝ}
    (hT : 1 ≤ T) (hT' : 1 ≤ T') {s : ℂ} (hs : 0 < s.re) :
    sourceKPCompactNativeEisensteinTest K hζ b S hS hSu φ hφ C hC hT =ᶠ[𝓝[≠] s]
      sourceKPCompactNativeEisensteinTest K hζ b S hS hSu φ hφ C hC hT' := by
  let Q := sourceKPCompactNativeTestImage K hζ b S
  have hQ : IsCompact Q := sourceKPCompactNativeTestImage_isCompact K hζ b S hS hSu
  let A := sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC
  filter_upwards [sourceKPAutomorphicEisensteinLocalL2_cutoff_independent K hζ hT hT' Q hQ hs]
    with z hz
  exact congrArg A hz

theorem sourceKPCompactNativeResidueTest_cutoff_independent (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) {T T' : ℝ}
    (hT : 1 ≤ T) (hT' : 1 ≤ T') :
    sourceKPCompactNativeResidueTest K hζ b S hS hSu φ hφ C hC hT =
      sourceKPCompactNativeResidueTest K hζ b S hS hSu φ hφ C hC hT' := by
  have he := sourceKPCompactNativeEisensteinTest_cutoff_independent K hζ b S hS hSu φ hφ C hC
    hT hT' (s := (1 / 6 : ℂ)) (by norm_num)
  have he' : (fun z => (z - 1 / 6) *
      sourceKPCompactNativeEisensteinTest K hζ b S hS hSu φ hφ C hC hT z) =ᶠ[𝓝[≠] (1 / 6 : ℂ)]
      (fun z => (z - 1 / 6) *
        sourceKPCompactNativeEisensteinTest K hζ b S hS hSu φ hφ C hC hT' z) := by
    filter_upwards [he] with z hz
    rw [hz]
  exact tendsto_nhds_unique
    (sourceKPCompactNativeEisensteinTest_residue_tendsto K hζ b S hS hSu φ hφ C hC hT)
    ((sourceKPCompactNativeEisensteinTest_residue_tendsto K hζ b S hS hSu φ hφ C hC hT').congr' he'.symm)

end
end ArtinMatthews
