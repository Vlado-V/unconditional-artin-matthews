module

public import ArtinMatthews.SourceReflectionExpansion
public import ArtinMatthews.SourcePrimeNormSummability
public import ArtinMatthews.SourceReflectionIdealCutoffs
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

/-! The absolute majorant after freezing an active product. The cube
and column factors are genuine ideal norm series. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

abbrev SourceReflectionTermIndex (f : Finset Prime) :=
  SourceReflectionFrozenNumerator F S₀ f × E × ReflectionSquarefreeExponents F S₀

def sourceReflectionDirichletTerm (f : Finset Prime) (σ : ℝ)
    (i : SourceReflectionTermIndex F S₀ f) : ℝ :=
  sourceReflectionFrozenWeight F S₀ f i.1.val * (q i.2.2.val : ℝ) ^ (-1 / 2 : ℝ) *
    (q i.2.1 : ℝ)⁻¹ * sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val ^ (-σ)

theorem sourceReflectionDirichletTerm_nonneg (f : Finset Prime) (σ : ℝ)
    (i : SourceReflectionTermIndex F S₀ f) : 0 ≤ sourceReflectionDirichletTerm F S₀ f σ i := by
  have hb := sourceReflectionFrozenWeight_nonneg F S₀ f i.1.val
  have hQ := zero_le_one.trans (sourceReflectionTermLength_one_le F S₀ i.1.val i.2.1 i.2.2.val)
  unfold sourceReflectionDirichletTerm
  positivity

def sourceReflectionCubeSeries (σ : ℝ) : ℝ := ∑' n : E, (q n : ℝ) ^ (-(3 * σ + 1))

def sourceReflectionColumnSeries (σ : ℝ) : ℝ :=
  ∑' c : ReflectionSquarefreeExponents F S₀, (q c.val : ℝ) ^ (-(σ + 1 / 2))

theorem sourceReflectionDirichletTerm_factor (f : Finset Prime) (σ : ℝ)
    (i : SourceReflectionTermIndex F S₀ f) :
    sourceReflectionDirichletTerm F S₀ f σ i =
      (sourceReflectionFrozenWeight F S₀ f i.1.val * (q i.1.val : ℝ) ^ (-σ)) *
        ((q i.2.1 : ℝ) ^ (-(3 * σ + 1)) * (q i.2.2.val : ℝ) ^ (-(σ + 1 / 2))) := by
  let a : ℝ := q i.1.val
  let n : ℝ := q i.2.1
  let c : ℝ := q i.2.2.val
  let b := sourceReflectionFrozenWeight F S₀ f i.1.val
  have ha : 0 < a := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ _)
  have hn : 0 < n := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ _)
  have hc : 0 < c := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ _)
  change b * c ^ (-1 / 2 : ℝ) * n⁻¹ * (a * c * n ^ 3) ^ (-σ) = _
  have hQ : (a * c * n ^ 3) ^ (-σ) = a ^ (-σ) * c ^ (-σ) * n ^ ((3 : ℝ) * (-σ)) := by
    rw [Real.mul_rpow (mul_nonneg ha.le hc.le) (pow_nonneg hn.le _),
      Real.mul_rpow ha.le hc.le]
    have hn' : (n ^ 3) ^ (-σ) = n ^ ((3 : ℝ) * (-σ)) := by
      simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hn.le 3 (-σ)).symm
    rw [hn']
  change _ = (b * a ^ (-σ)) * (n ^ (-(3 * σ + 1)) * c ^ (-(σ + 1 / 2)))
  rw [hQ, ← Real.rpow_neg_one n]
  calc
    _ = (b * a ^ (-σ)) *
        ((n ^ (-1 : ℝ) * n ^ ((3 : ℝ) * (-σ))) * (c ^ (-1 / 2 : ℝ) * c ^ (-σ))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hn, ← Real.rpow_add hc,
        show (-1 : ℝ) + 3 * -σ = -(3 * σ + 1) by ring,
        show (-1 / 2 : ℝ) + -σ = -(σ + 1 / 2) by ring]

theorem sourceReflectionDirichlet_hasSum (f : Finset Prime) {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasSum (sourceReflectionDirichletTerm F S₀ f σ)
      (sourceReflectionFrozenFactors F S₀ f σ *
        (sourceReflectionCubeSeries F S₀ σ * sourceReflectionColumnSeries F S₀ σ)) := by
  let w (a : SourceReflectionFrozenNumerator F S₀ f) :=
    sourceReflectionFrozenWeight F S₀ f a.val * (q a.val : ℝ) ^ (-σ)
  let n (b : E) := (q b : ℝ) ^ (-(3 * σ + 1))
  let c (b : ReflectionSquarefreeExponents F S₀) := (q b.val : ℝ) ^ (-(σ + 1 / 2))
  have hw : HasSum w (sourceReflectionFrozenFactors F S₀ f σ) :=
    sourceReflectionFrozenDirichlet F S₀ f (by linarith)
  have hn : Summable n := sourcePrimeExponentNorm_summable F S₀ (by linarith)
  have hc : Summable c :=
    (sourcePrimeExponentNorm_summable F S₀ (show 1 < σ + 1 / 2 by linarith)).comp_injective
      (fun (_ _ : ReflectionSquarefreeExponents F S₀) h => Subtype.ext h)
  have hnc := summable_mul_of_summable_norm hn.norm hc.norm
  have htotal := summable_mul_of_summable_norm hw.summable.norm hnc.norm
  have hs := htotal.congr (fun i => (sourceReflectionDirichletTerm_factor F S₀ f σ i).symm)
  apply hs.hasSum_iff.mpr
  rw [tsum_congr (sourceReflectionDirichletTerm_factor F S₀ f σ)]
  change (∑' i : SourceReflectionTermIndex F S₀ f, w i.1 * (n i.2.1 * c i.2.2)) = _
  rw [← tsum_mul_tsum_of_summable_norm hw.summable.norm hnc.norm,
    ← tsum_mul_tsum_of_summable_norm hn.norm hc.norm, hw.tsum_eq]
  rfl

theorem sourceReflectionDirichletSeries_nonneg (σ : ℝ) :
    0 ≤ sourceReflectionCubeSeries F S₀ σ * sourceReflectionColumnSeries F S₀ σ := by
  apply mul_nonneg
  · exact tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

end
end ArtinMatthews.SourceEulerAssembly
