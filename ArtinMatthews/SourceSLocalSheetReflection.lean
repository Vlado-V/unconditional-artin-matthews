module

public import ArtinMatthews.SourceSLocalSheetMellin
public import ArtinMatthews.SourceSLocalRadialInvariance
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Inversion and translation on the actual norm-one group transport a
reflected integrand between the two literal norm sheets. -/
namespace ArtinMatthews.SourcePhysical
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped NumberField Classical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

private theorem sheetReflection_change (a : SWholeUnits K S) {T : ℝ} (hT : 0 < T) :
    ∃ e : SNormOne K S ≃ᵐ SNormOne K S, MeasurePreserving e ν ν ∧
      ∀ n : SNormOne K S,
        a * ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)⁻¹ =
          (e n : SWholeUnits K S) * sLocalPositiveScaling K hζ S (sLocalNorm K S a / T) := by
  let : LocallyCompactSpace (SNormOne K S) := sNormOne_locallyCompact K S
  let : PolishSpace (SNormOne K S) := sNormOne_polish K S
  let u := a * (sLocalPositiveScaling K hζ S T)⁻¹
  let v := sLocalPositiveScaling K hζ S (sLocalNorm K S a / T)
  have hn : sLocalNorm K S u = sLocalNorm K S v := by
    dsimp only [u, v]
    rw [sLocalNorm_mul, sLocalNorm_inv, sLocalPositiveScaling_norm K hζ S hT,
      sLocalPositiveScaling_norm K hζ S (div_pos (sLocalNorm_pos K S a) hT),
      div_eq_mul_inv]
  let k := sourceSLocalSameNormRatio S u v hn
  have hk : (k : SWholeUnits K S) * v = u := sourceSLocalSameNormRatio_mul S u v hn
  let e := (MeasurableEquiv.inv (SNormOne K S)).trans (MeasurableEquiv.mulLeft k)
  refine ⟨e, ?_, ?_⟩
  · exact (measurePreserving_mul_left ν k).comp (Measure.measurePreserving_inv ν)
  · intro n
    change a * ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)⁻¹ =
      ((k : SWholeUnits K S) * (n : SWholeUnits K S)⁻¹) * v
    rw [mul_inv_rev, mul_comm (k : SWholeUnits K S) (n : SWholeUnits K S)⁻¹, mul_assoc, hk]
    dsimp only [u]
    ac_rfl

theorem sourceSLocalSheetProfile_reflection (F : SWholeUnits K S → ℂ)
    (a : SWholeUnits K S) {T : ℝ} (hT : 0 < T) :
    sourceSLocalSheetProfile S ν hζ (fun x => F (a * x⁻¹)) T =
      sourceSLocalSheetProfile S ν hζ F (sLocalNorm K S a / T) := by
  obtain ⟨e,he,heq⟩ := sheetReflection_change S ν hζ a hT
  unfold sourceSLocalSheetProfile
  calc
    _ = ∫ n : SNormOne K S, F ((e n : SWholeUnits K S) *
          sLocalPositiveScaling K hζ S (sLocalNorm K S a / T)) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun n => congrArg F (heq n))
    _ = _ := he.integral_comp' (fun n : SNormOne K S => F ((n : SWholeUnits K S) *
      sLocalPositiveScaling K hζ S (sLocalNorm K S a / T)))

theorem sourceSLocalSheetProfile_reflection_integrable_iff (F : SWholeUnits K S → ℂ)
    (a : SWholeUnits K S) {T : ℝ} (hT : 0 < T) :
    Integrable (fun n : SNormOne K S =>
      F (a * ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)⁻¹)) ν ↔
    Integrable (fun n : SNormOne K S =>
      F ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S (sLocalNorm K S a / T))) ν := by
  obtain ⟨e,he,heq⟩ := sheetReflection_change S ν hζ a hT
  let G (n : SNormOne K S) :=
    F ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S (sLocalNorm K S a / T))
  have hfun : (fun n : SNormOne K S =>
      F (a * ((n : SWholeUnits K S) * sLocalPositiveScaling K hζ S T)⁻¹)) = G ∘ e :=
    funext fun n => congrArg F (heq n)
  rw [hfun]
  exact he.integrable_comp_emb e.measurableEmbedding

end
end ArtinMatthews.SourcePhysical
