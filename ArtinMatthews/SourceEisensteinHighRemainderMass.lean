module

public import ArtinMatthews.SourceEisensteinHighRemainderContinuity
public import ArtinMatthews.L2DyadicOpenShells
public import ArtinMatthews.SourceKPArchHaar
public import ArtinMatthews.SourceKPAutomorphicMeasure
public import ArtinMatthews.SourceEisensteinDyadicShellVolume
public import ArtinMatthews.SourceEisensteinHighNonconstantGrowth
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Local square integrability and the initial polynomial mass bound for
the actual Eisenstein remainder on the literal high-cusp shells. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "X" => SourceKPAutomorphicLevel K hζ
local instance sourceEisensteinRemainderMassMeasurable : MeasurableSpace X := borel X
local instance sourceEisensteinRemainderMassBorel : BorelSpace X := ⟨rfl⟩
local notation "μ" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
local notation "H" => sourceKPAutomorphicOrbitHeight K hζ

theorem sourceKPHighRemainderExtension_dyadic_bound {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (hT₂ : 2 ≤ T) (A : ℝ) (hTA : T ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (x : X), x ∈ dyadicL2OpenShell H A n →
      ‖sourceKPHighRemainderExtension K hζ s T hT x‖ ≤ C*(A*2^n)^(s.re+1/2) := by
  obtain ⟨C,hC,hbound⟩ := sourceKPHighCuspNonconstantEisenstein_growth K hζ hs
  refine ⟨C,hC,?_⟩
  intro n x hx
  have hA₀ : 0 < A := (zero_lt_one.trans hT).trans_le hTA
  have hAn : A ≤ A*(2 : ℝ)^n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)) hA₀.le
  have hxH : T < H x := (hTA.trans hAn).trans_lt hx.1
  have hF := sourceKPHighRemainderExtension_apply K hζ s T hT ⟨x,hxH⟩
  change sourceKPHighRemainderExtension K hζ s T hT x = _ at hF
  rw [hF]
  apply (hbound T hT hT₂ ⟨x,hxH⟩).trans
  have ha : 0 ≤ s.re+1/2 := by
    push_cast at hs
    have hn : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
    linarith
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow (div_nonneg ((zero_lt_one.trans hT).trans hxH).le (by norm_num)) _ ha
  rw [div_le_iff₀ (by norm_num : (0 : ℝ)<2)]
  have hb : A*(2 : ℝ)^(n+1) = A*2^n*2 := by rw [pow_succ,mul_assoc]
  exact hx.2.trans_eq hb

theorem sourceKPHighRemainderExtension_dyadic_memLp {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (hT₂ : 2 ≤ T) (A : ℝ) (hTA : T ≤ A) (n : ℕ) :
    MemLp (sourceKPHighRemainderExtension K hζ s T hT) 2
      ((μ).restrict (dyadicL2OpenShell H A n)) := by
  let S := dyadicL2OpenShell H A n
  have hS : MeasurableSet S := sourceKPDyadicOpenShell_measurable K hζ A n
  letI : IsFiniteMeasure ((μ).restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using sourceKPDyadicOpenShell_measure_lt_top K hζ A n⟩
  obtain ⟨C,_hC,hbound⟩ := sourceKPHighRemainderExtension_dyadic_bound K hζ hs T hT hT₂ A hTA
  apply MemLp.of_bound (sourceKPHighRemainderExtension_measurable K hζ hs T hT).aestronglyMeasurable.restrict
    (C*(A*2^n)^(s.re+1/2))
  filter_upwards [ae_restrict_mem hS] with x hx
  exact hbound n x hx

theorem sourceKPHighRemainderExtension_dyadic_mass_growth {s : ℂ}
    (hs : ((3 * (Module.finrank ℚ K + 1) : ℕ) : ℝ) ≤ 2*s.re+1)
    (T : ℝ) (hT : 1 < T) (hT₂ : 2 ≤ T) (A : ℝ) (hTA : T ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∫ x in dyadicL2OpenShell H A n, ‖sourceKPHighRemainderExtension K hζ s T hT x‖ ^ 2 ∂μ) ≤
        C*2^((2*s.re+1)*n) := by
  obtain ⟨C,hC,hbound⟩ := sourceKPHighRemainderExtension_dyadic_bound K hζ hs T hT hT₂ A hTA
  let a := s.re+1/2
  let C₀ := (C*A^a)^2 * (μ).real (dyadicL2OpenShell H A 0)
  have hC₀ : 0 ≤ C₀ := mul_nonneg (sq_nonneg _) measureReal_nonneg
  refine ⟨C₀+1,by linarith,?_⟩
  intro n
  let S := dyadicL2OpenShell H A n
  let f := sourceKPHighRemainderExtension K hζ s T hT
  let B := C*(A*(2 : ℝ)^n)^a
  have hA₀ : 0 < A := (zero_lt_one.trans hT).trans_le hTA
  have hS : MeasurableSet S := sourceKPDyadicOpenShell_measurable K hζ A n
  letI : IsFiniteMeasure ((μ).restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using sourceKPDyadicOpenShell_measure_lt_top K hζ A n⟩
  have hm : MemLp f 2 ((μ).restrict S) :=
    sourceKPHighRemainderExtension_dyadic_memLp K hζ hs T hT hT₂ A hTA n
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hcompare : (fun x => ‖f x‖^2) ≤ᵐ[(μ).restrict S] fun _ => B^2 := by
    filter_upwards [ae_restrict_mem hS] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound n x hx) 2
  have hp : B^2 = (C*A^a)^2 * (2 : ℝ)^((2*s.re+1)*n) := by
    dsimp only [B]
    rw [Real.mul_rpow hA₀.le (by positivity),← mul_assoc,mul_pow]
    congr 1
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    dsimp only [a]
    push_cast
    ring
  calc
    (∫ x in S, ‖f x‖ ^ 2 ∂μ) ≤ ∫ _ in S, B^2 ∂μ := integral_mono_ae hi (integrable_const _) hcompare
    _ = (μ).real S * B^2 := by rw [setIntegral_const,smul_eq_mul]
    _ ≤ (μ).real (dyadicL2OpenShell H A 0) * B^2 :=
      mul_le_mul_of_nonneg_right (sourceKPDyadicOpenShell_real_volume_le K hζ A (hT.trans_le hTA) n) (sq_nonneg _)
    _ = C₀ * 2^((2*s.re+1)*n) := by rw [hp]; dsimp only [C₀]; ring
    _ ≤ (C₀+1) * 2^((2*s.re+1)*n) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by norm_num) _)

end
end ArtinMatthews
