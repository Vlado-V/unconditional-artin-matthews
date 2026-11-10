module

public import ArtinMatthews.SourceKPTraceJacquetFiniteFiber
public import ArtinMatthews.SourceKPCuspResidualFourierValue
public import ArtinMatthews.SourceKPCuspResidualFourierUpper
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

/-! At one finite place the compact residue test has the actual local
Whittaker character, with the other-place finite argument fixed. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix StandardAdelic
open scoped NumberField MatrixGroups AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (P : HeightOneSpectrum (𝓞 K))

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "ι" => sourceKPAdelicLocalProjective K hζ P

private theorem finiteCharacter_mul_single (m : Kˣ) (x : L) :
    finiteCharacter K (algebraMap K 𝔸ᶠ[K] (m:K) * sourceKPFiniteAdditiveSingle K P x) =
      localFiniteCharacter K P ((sourceKPTraceJacquetFrequencyAt K P m : L)*x) := by
  have h := sourceKPTraceJacquetFiniteCharacter_single_add K P m x 0
  simp only [add_zero, sourceKPTraceJacquetFiniteCharacter, mul_zero,
    AddChar.map_zero_eq_one, star_one, mul_one] at h
  exact star_injective h

theorem sourceKPCuspResidualFourierValue_local_upper
    (m : Kˣ) {T : ℝ} (hT : 1 ≤ T) (qf : Gf)
    (hqf : sourceKPAdelicLocalBase K hζ P (1,qf) = 1) (g : G) (x : L) :
    sourceKPCuspResidualFourierValue K hζ m hT
      (qf * (ι (sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x) * g)).2) =
      localFiniteCharacter K P ((sourceKPTraceJacquetFrequencyAt K P m : L)*x) *
        sourceKPCuspResidualFourierValue K hζ m hT (qf * (ι g).2) := by
  let n := sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x)
  have hcomm : (ι n).2 * qf = qf * (ι n).2 :=
    congrArg Prod.snd (sourceKPAdelicLocalProjective_commute_of_base_one K hζ P n (1,qf) hqf).eq
  have hn : (ι n).2 =
      sourceKPFiniteAdeleUpperLift K hζ (sourceKPFiniteAdditiveSingle K P x) :=
    congrArg Prod.snd (sourceKPAdelicLocalProjective_upper K hζ P x)
  rw [map_mul]
  change sourceKPCuspResidualFourierValue K hζ m hT (qf * ((ι n).2 * (ι g).2)) = _
  rw [← mul_assoc, ← hcomm, mul_assoc, hn, sourceKPCuspResidualFourierValue_left_finite_upper,
    finiteCharacter_mul_single]

end
end ArtinMatthews
