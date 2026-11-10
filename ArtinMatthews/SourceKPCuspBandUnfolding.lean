module

public import ArtinMatthews.SourceKPCuspBandWeightFunctional
public import ArtinMatthews.SourceEisensteinOutgoingFiniteLevel
public import ArtinMatthews.SourceKPAutomorphicCompactTruncated
public import ArtinMatthews.SourceKPCuspRepresentativeHaar
public import ArtinMatthews.SourceKPHighCuspMeasure
public import ArtinMatthews.SourceKPCuspBandHighMeasure
public import ArtinMatthews.SourceKPCuspBandTraceWeight
public import ArtinMatthews.SourceKPCuspFundamentalSection
public import ArtinMatthews.SourceKPCuspSectionMeasure
public import ArtinMatthews.SourceKPCuspTraceAverage
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

/-! The full-band functional unfolds against the actual outgoing constant term. -/

namespace ArtinMatthews
open NumberField MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "π" => sourceKPAutomorphicCompactMk K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "πY" => (fun q : SourceKPAdelicProjective K hζ => π (sourceKPAutomorphicLevelMk K hζ q))
local instance sourceKPCuspBandUnfoldingAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _

private theorem cuspBandHighSection_exists (A : ℝ) :
    ∃ F : Set (SourceKPHighCuspFinite K hζ A), MeasurableSet F ∧
      Set.InjOn (sourceKPHighCuspProjection K hζ A) F ∧
      sourceKPHighCuspProjection K hζ A '' F = Set.univ := by
  have hcover : sourceKPHighCuspProjection K hζ A '' Set.univ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨x,hx⟩ := sourceKPHighCusp_representative K hζ A q
    exact ⟨x, Set.mem_univ _, hx⟩
  obtain ⟨F,hF,_,hi,hc⟩ := sourceKPCuspHighProjection_exists_section K hζ A Set.univ
    MeasurableSet.univ hcover
  exact ⟨F,hF,hi,hc⟩

/-- A measurable high section fixed independently of the spectral parameter. -/
def sourceKPCuspBandHighSection (A : ℝ) : Set (SourceKPHighCuspFinite K hζ A) :=
  Classical.choose (cuspBandHighSection_exists K hζ A)

theorem sourceKPCuspBandHighSection_spec (A : ℝ) :
    MeasurableSet (sourceKPCuspBandHighSection K hζ A) ∧
      Set.InjOn (sourceKPHighCuspProjection K hζ A) (sourceKPCuspBandHighSection K hζ A) ∧
      sourceKPHighCuspProjection K hζ A '' sourceKPCuspBandHighSection K hζ A = Set.univ :=
  Classical.choose_spec (cuspBandHighSection_exists K hζ A)

theorem sourceKPCuspBandHighSection_measurePreserving (A : ℝ) :
    MeasurePreserving (sourceKPHighCuspProjection K hζ A)
      ((sourceKPHighRepresentativeHaar K hζ A).restrict (sourceKPCuspBandHighSection K hζ A))
      (sourceKPHighCuspMeasure K hζ A) := by
  obtain ⟨hm,hi,hc⟩ := sourceKPCuspBandHighSection_spec K hζ A
  exact sourceKPCuspHighSection_measurePreserving K hζ A _ hm hi hc

private theorem cuspBandHighTrace_eq_outgoing {A T : ℝ} (hT : 1 ≤ T) (hTA : 2*T ≤ A) (W : Y → ℂ)
    (hupper : ∀ (q : SourceKPAdelicProjective K hζ) (y : 𝔸[K]),
      A < sourceKPAdelicCoverHeight K hζ q → W (πY (sourceKPAdelicUpperLift K hζ y*q)) = W (πY q))
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (x : SourceKPHighCuspFinite K hζ A) :
    (∫ y in sourceKPAdelicFundamentalDomain K,
      star (W (π (sourceKPHighCuspProjection K hζ A (Multiplicative.ofAdd y • x)).val)) *
        sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s
          (π (sourceKPHighCuspProjection K hζ A (Multiplicative.ofAdd y • x)).val)
          ∂sourceKPAdelicTraceProduct K) =
      star (W (π (sourceKPHighCuspProjection K hζ A x).val)) *
        sourceKPFiniteLevelOutgoingEisenstein K hζ s x.val := by
  obtain ⟨q,hq⟩ := sourceKPFiniteLevelMk_surjective K hζ x.val
  have hqhigh : A < sourceKPAdelicCoverHeight K hζ q := by
    have hx := x.property
    change A < sourceKPFiniteLevelHeight K hζ x.val at hx
    rwa [← hq, sourceKPFiniteLevelHeight_mk] at hx
  have hproj : (sourceKPHighCuspProjection K hζ A x).val = sourceKPAutomorphicLevelMk K hζ q :=
    congrArg (Quotient.mk _) hq.symm
  simp_rw [sourceKPCuspHighUpper_projection_mk K hζ A _ x q hq]
  rw [hproj, ← hq, sourceKPFiniteLevelOutgoingEisenstein_mk]
  exact sourceKPCuspBandTraceWeight_eq_intertwiner K hζ W hT hs q
    (hTA.trans hqhigh.le) (fun y => hupper q y hqhigh)

/-- The literal full-band pairing with the truncated section is its outgoing trace period. -/
theorem sourceKPCuspBandPairing_eq_outgoing_on_section {A T : ℝ} (hT : 1 ≤ T) (hTA : 2*T ≤ A)
    (F : Set (SourceKPHighCuspFinite K hζ A)) (hm : MeasurableSet F)
    (hi : Set.InjOn (sourceKPHighCuspProjection K hζ A) F)
    (hc : sourceKPHighCuspProjection K hζ A '' F = Set.univ)
    (W : Y → ℂ) (hW : MemLp W 2 μY)
    (hlow : ∀ x : Y, sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ A → W x = 0)
    (hupper : ∀ (q : SourceKPAdelicProjective K hζ) (y : 𝔸[K]),
      A < sourceKPAdelicCoverHeight K hζ q → W (πY (sourceKPAdelicUpperLift K hζ y*q)) = W (πY q))
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (u : SourceKPGenuineAutomorphicL2 K hζ)
    (hu : (u.val : Y → ℂ) =ᵐ[μY] sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) :
    sourceKPGenuineAutomorphicL2Pairing K hζ W hW u =
      ∫ x in F,
        star (W (π (sourceKPHighCuspProjection K hζ A x).val)) *
          sourceKPFiniteLevelOutgoingEisenstein K hζ s x.val ∂sourceKPHighRepresentativeHaar K hζ A := by
  let G : Y → ℂ := fun x => star (W x) * sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s x
  let f : SourceKPHighCuspAutomorphic K hζ A → ℂ := fun x => G (π x.val)
  have hG : Integrable G μY := sourceKPGenuineAutomorphicL2Pairing_integrable K hζ hW u hu
  have hf : Integrable f (sourceKPHighCuspMeasure K hζ A) :=
    sourceKPAutomorphicBandIntegral_integrable_high K hζ G hG A
  have hzero (x : Y) (hx : sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ A) : G x = 0 := by
    change star (W x) * sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s x = 0
    rw [hlow x hx, star_zero, zero_mul]
  have hA : 1 < A := by linarith
  have havg := (sourceKPCuspHighSection_average_integral K hζ A hA F hm hi hc f hf).2
  calc
    _ = ∫ x : Y, G x ∂μY := sourceKPGenuineAutomorphicL2Pairing_apply K hζ hW u hu
    _ = ∫ x, f x ∂sourceKPHighCuspMeasure K hζ A :=
      sourceKPAutomorphicBandIntegral_eq_high K hζ G hG A hzero
    _ = ∫ x in F, (∫ y in sourceKPAdelicFundamentalDomain K,
        f (sourceKPHighCuspProjection K hζ A (Multiplicative.ofAdd y • x))
          ∂sourceKPAdelicTraceProduct K) ∂sourceKPHighRepresentativeHaar K hζ A := havg
    _ = _ := by
      exact setIntegral_congr_fun hm (fun x _ => cuspBandHighTrace_eq_outgoing K hζ hT hTA W hupper hs x)

theorem sourceKPCuspBandPairing_eq_outgoing {A T : ℝ} (hT : 1 ≤ T) (hTA : 2*T ≤ A)
    (W : Y → ℂ) (hW : MemLp W 2 μY)
    (hlow : ∀ x : Y, sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ A → W x = 0)
    (hupper : ∀ (q : SourceKPAdelicProjective K hζ) (y : 𝔸[K]),
      A < sourceKPAdelicCoverHeight K hζ q → W (πY (sourceKPAdelicUpperLift K hζ y*q)) = W (πY q))
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (u : SourceKPGenuineAutomorphicL2 K hζ)
    (hu : (u.val : Y → ℂ) =ᵐ[μY] sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) :
    sourceKPGenuineAutomorphicL2Pairing K hζ W hW u =
      ∫ x in sourceKPCuspBandHighSection K hζ A,
        star (W (π (sourceKPHighCuspProjection K hζ A x).val)) *
          sourceKPFiniteLevelOutgoingEisenstein K hζ s x.val ∂sourceKPHighRepresentativeHaar K hζ A := by
  obtain ⟨hm,hi,hc⟩ := sourceKPCuspBandHighSection_spec K hζ A
  exact sourceKPCuspBandPairing_eq_outgoing_on_section K hζ hT hTA _ hm hi hc W hW hlow hupper hs u hu

theorem sourceKPAutomorphicCuspBandFunctional_eq_outgoing {A B T : ℝ}
    (hA : 1 ≤ A) (hAB : A ≤ B) (hT : 1 ≤ T) (hTA : 2*T ≤ A) (s₀ : ℂ)
    {s : ℂ} (hs : ((3*(Module.finrank ℚ K+1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (u : SourceKPGenuineAutomorphicL2 K hζ)
    (hu : (u.val : Y → ℂ) =ᵐ[μY] sourceKPAutomorphicCompactTruncatedEisenstein K hζ T s) :
    sourceKPAutomorphicCuspBandFunctional K hζ hA hAB s₀ u =
      ∫ x in sourceKPCuspBandHighSection K hζ A,
        star (sourceKPAutomorphicCuspBandTest K hζ A B s₀ (π (sourceKPHighCuspProjection K hζ A x).val)) *
          sourceKPFiniteLevelOutgoingEisenstein K hζ s x.val ∂sourceKPHighRepresentativeHaar K hζ A := by
  rw [sourceKPAutomorphicCuspBandFunctional_eq_pairing]
  exact sourceKPCuspBandPairing_eq_outgoing K hζ hT hTA (sourceKPAutomorphicCuspBandTest K hζ A B s₀)
    (sourceKPAutomorphicCuspBandTest_memLp K hζ hA hAB s₀)
    (sourceKPAutomorphicCuspBandTest_zero_of_height_le K hζ (zero_lt_one.trans_le hA) hAB s₀)
    (fun q y hq => sourceKPAutomorphicCuspBandTest_adelic_upper K hζ hA hAB s₀ y q (hA.trans_lt hq)) hs u hu

end
end ArtinMatthews
