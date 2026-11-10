module

public import ArtinMatthews.SourceSLocalTensorOrbitReflection
public import ArtinMatthews.SourceSLocalQuotientSeries
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A finite sum inside each norm-one orbit may be flattened after
integration, with the same quotient Haar and a finite absolute sheet
mass over the outer and finite tensor labels. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical BigOperators ENNReal
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable {I J : Type*} [Fintype J]
local notation "N" => SNormOne K S
local notation "U" => SWholeUnits K S
local notation "Q" => SNormOneSixthQuotient K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "qmk" => sNormOneSixthQuotientMap K S

theorem sourceSLocalGroupedOrbit_mk_eq_of_hasSum
    (F : I → J → U → ℂ) (u : I → U) (n : N) {z : ℂ}
    (h : HasSum (fun p : I × Γ =>
      ∑ j, F p.1 j (((n * p.2.val : N) : U) * u p.1)) z) :
    (∑' i, sourceSLocalTensorOrbit S (fun x => ∑ j, F i j x) (u i) (qmk n)) = z := by
  rw [← h.tsum_eq, h.summable.tsum_prod]
  exact tsum_congr fun i => sourceSLocalTensorOrbit_mk S (fun x => ∑ j, F i j x) (u i) n

theorem sourceSLocalGroupedOrbit_quotient_eq_of_hasSum
    (F : I → J → U → ℂ) (u : I → U) (G : Q → ℂ)
    (h : ∀ n : N, HasSum (fun p : I × Γ =>
      ∑ j, F p.1 j (((n * p.2.val : N) : U) * u p.1)) (G (qmk n))) :
    (fun q => ∑' i, sourceSLocalTensorOrbit S (fun x => ∑ j, F i j x) (u i) q) = G := by
  funext q
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  exact sourceSLocalGroupedOrbit_mk_eq_of_hasSum S F u n (h n)

variable [Countable I]
variable (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure]
local notation "μQ" => sNormOneQuotientMeasure K S ν

private theorem grouped_mass_le (f : I → J → N → ℂ) (hm : ∀ i j, Measurable (f i j)) :
    (∑' i, ∫⁻ n, ‖∑ j, f i j n‖ₑ ∂ν) ≤
      ∑' p : I × J, ∫⁻ n, ‖f p.1 p.2 n‖ₑ ∂ν := by
  calc
    _ ≤ ∑' i, ∫⁻ n, ∑ j, ‖f i j n‖ₑ ∂ν :=
      ENNReal.tsum_le_tsum fun i => lintegral_mono fun n => enorm_sum_le _ (fun j => f i j n)
    _ = ∑' i, ∑' j, ∫⁻ n, ‖f i j n‖ₑ ∂ν := by
      apply tsum_congr
      intro i
      rw [tsum_fintype]
      exact lintegral_finsetSum _ (fun j _ => (hm i j).enorm)
    _ = _ := (ENNReal.tsum_prod' (f := fun p : I × J => ∫⁻ n, ‖f p.1 p.2 n‖ₑ ∂ν)).symm

theorem sourceSLocalGroupedOrbit_integral_eq_flattened
    (F : I → J → U → ℂ) (u : I → U)
    (hm : ∀ i j, Measurable (fun n : N => F i j ((n : U) * u i)))
    (hMass : (∑' p : I × J, ∫⁻ n : N, ‖F p.1 p.2 ((n : U) * u p.1)‖ₑ ∂ν) < ⊤) :
    Integrable (fun q => ∑' i, sourceSLocalTensorOrbit S (fun x => ∑ j, F i j x) (u i) q) μQ ∧
    Integrable (fun q => ∑' p : I × J, sourceSLocalTensorOrbit S (F p.1 p.2) (u p.1) q) μQ ∧
    (∫ q, ∑' i, sourceSLocalTensorOrbit S (fun x => ∑ j, F i j x) (u i) q ∂μQ) =
      ∫ q, ∑' p : I × J, sourceSLocalTensorOrbit S (F p.1 p.2) (u p.1) q ∂μQ := by
  let f (i : I) (j : J) (n : N) := F i j ((n : U) * u i)
  let g (i : I) (n : N) := ∑ j, f i j n
  have hgm (i : I) : Measurable (g i) :=
    Finset.measurable_fun_sum _ (fun j _ => hm i j)
  have hgmass : (∑' i, ∫⁻ n, ‖g i n‖ₑ ∂ν) < ⊤ :=
    (grouped_mass_le S ν f hm).trans_lt hMass
  obtain ⟨hgi, hge⟩ := sNormOnePeriodizeSeries_unfold S ν g hgm hgmass
  obtain ⟨hfi, hfe⟩ := sNormOnePeriodizeSeries_unfold S ν
    (fun p : I × J => f p.1 p.2) (fun p => hm p.1 p.2) hMass
  refine ⟨hgi, hfi, hge.trans (Eq.trans ?_ hfe.symm)⟩
  have hterm (p : I × J) : Integrable (f p.1 p.2) ν :=
    ⟨(hm p.1 p.2).aestronglyMeasurable,
      (ENNReal.le_tsum (f := fun t : I × J => ∫⁻ n, ‖f t.1 t.2 n‖ₑ ∂ν) p).trans_lt hMass⟩
  have habs : (∑' p : I × J, ‖∫ n, f p.1 p.2 n ∂ν‖ₑ) < ⊤ :=
    (ENNReal.tsum_le_tsum fun p : I × J =>
      enorm_integral_le_lintegral_enorm (μ := ν) (f p.1 p.2)).trans_lt hMass
  have hsum : Summable (fun p : I × J => ‖∫ n, f p.1 p.2 n ∂ν‖) :=
    tsum_enorm_ne_top_iff_summable_norm.mp habs.ne
  calc
    (∑' i, ∫ n, g i n ∂ν) = ∑' i, ∑ j, ∫ n, f i j n ∂ν := by
      apply tsum_congr
      intro i
      exact integral_finsetSum _ (fun j _ => hterm (i,j))
    _ = ∑' p : I × J, ∫ n, f p.1 p.2 n ∂ν := by
      rw [hsum.of_norm.tsum_prod]
      simp only [tsum_fintype]

theorem sourceSLocalGroupedOrbit_quotient_integral_eq_flattened
    (F : I → J → U → ℂ) (u : I → U) (G : Q → ℂ)
    (h : ∀ n : N, HasSum (fun p : I × Γ =>
      ∑ j, F p.1 j (((n * p.2.val : N) : U) * u p.1)) (G (qmk n)))
    (hm : ∀ i j, Measurable (fun n : N => F i j ((n : U) * u i)))
    (hMass : (∑' p : I × J, ∫⁻ n : N, ‖F p.1 p.2 ((n : U) * u p.1)‖ₑ ∂ν) < ⊤) :
    Integrable G μQ ∧
    (∫ q, G q ∂μQ) =
      ∫ q, ∑' p : I × J, sourceSLocalTensorOrbit S (F p.1 p.2) (u p.1) q ∂μQ := by
  have he := sourceSLocalGroupedOrbit_quotient_eq_of_hasSum S F u G h
  obtain ⟨hi, _, hiEq⟩ := sourceSLocalGroupedOrbit_integral_eq_flattened S ν F u hm hMass
  exact ⟨he ▸ hi, (congrArg (fun H : Q → ℂ => ∫ q, H q ∂μQ) he.symm).trans hiEq⟩

end
end ArtinMatthews.SourcePhysical
