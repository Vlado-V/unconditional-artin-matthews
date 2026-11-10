module

public import ArtinMatthews.SourceJacquetHaar
public import ArtinMatthews.SourceGeneratorWeil
public import ArtinMatthews.CompactFiniteAverage
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

/-! Literal Jacquet unit-shell integrals against the actual standard
character. The source's volume-one normalization and the terminal
prime phase are exact. No automorphic representation is an input. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain LocalFieldTheory QuadraticWeil MeasureTheory
open StandardAdelic SIntegerPrincipalization SIntegerQuotient SIntegerFourier
open LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField ValuativeRel Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))

local instance jacquetShellAdicRelation : ValuativeRel (P.adicCompletion F) := adicRelation F P
local instance jacquetShellAdicLocalField : IsNonarchimedeanLocalField (P.adicCompletion F) := adicLocalField F P
local instance jacquetShellAdicMeasurable : MeasurableSpace (P.adicCompletion F) := borel (P.adicCompletion F)
local instance jacquetShellAdicBorel : BorelSpace (P.adicCompletion F) := ⟨rfl⟩

def sourceJacquetShellIntegral (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ) (t : P.adicCompletion F) : ℂ :=
  ∫ x in (sourceJacquetIntegers F P : Set (P.adicCompletion F)),
    sourceJacquetWeight F P χ x * localFiniteCharacter F P (-(t * x)) ∂(sourceJacquetHaar F P)

theorem sourceJacquetShellIntegral_of_integral_frequency (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)
    (t : P.adicCompletion F) (ht : t ∈ P.adicCompletionIntegers F) :
    sourceJacquetShellIntegral F P χ t =
      (∑' z : (𝓞 F) ⧸ P.asIdeal, χ z) / (Ideal.absNorm P.asIdeal : ℂ) := by
  rw [← sourceJacquetWeight_average F P χ]
  unfold sourceJacquetShellIntegral
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (sourceJacquetIntegers F P).isOpen.measurableSet] with x hx
  have hx' : x ∈ P.adicCompletionIntegers F := (adic_mem_integer_iff F P x).mp hx
  have hm : -(t * x) ∈ P.adicCompletionIntegers F :=
    (P.adicCompletionIntegers F).toSubring.neg_mem ((P.adicCompletionIntegers F).toSubring.mul_mem ht hx')
  rw [localFiniteCharacter_integral F P _ hm, mul_one]

theorem sourceJacquetShellIntegral_terminal (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ)
    (u : P.adicCompletion F)
    (hu : (Valued.v : Valuation (P.adicCompletion F) (WithZero (Multiplicative ℤ))) u = WithZero.exp (-1 : ℤ))
    (hbad : P ∉ traceBadPlaces F) :
    sourceJacquetShellIntegral F P χ u⁻¹ =
      (∑' z : (𝓞 F) ⧸ P.asIdeal, χ z *
        ((idealPrimeResidueChar F P (localFiniteCharacter F P)
          (localFiniteCharacter_conductorZero F P hbad) u hu).mulShift (-1)) z) /
        (Ideal.absNorm P.asIdeal : ℂ) := by
  let C := P.adicCompletion F
  let ψ := localFiniteCharacter F P
  let φ := (idealPrimeResidueChar F P ψ (localFiniteCharacter_conductorZero F P hbad) u hu).mulShift (-1)
  let : (sourceJacquetHaar F P).IsAddHaarMeasure := sourceJacquetHaar_isAddHaar F P
  let : Finite ((𝓞 F) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 F) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card ((𝓞 F) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hphase (x : sourceJacquetIntegers F P) : φ (sourceJacquetReduction F P x) = ψ (-(u⁻¹ * (x : C))) := by
    dsimp only [φ]
    rw [AddChar.mulShift_apply, neg_one_mul, AddChar.map_neg_eq_inv]
    change (adicPrimeResidueChar F P ψ (localFiniteCharacter_conductorZero F P hbad) u hu
      ((adicIntegerResidueEquiv F P) (sourceJacquetReduction F P x)))⁻¹ = _
    have he : (adicIntegerResidueEquiv F P) (sourceJacquetReduction F P x) = integerReduction C x :=
      (adicIntegerResidueEquiv F P).apply_symm_apply (integerReduction C x)
    rw [he, integerReduction_apply, adicPrimeResidueChar_apply, ← AddChar.map_neg_eq_inv]
  have hf : Continuous (fun x : C => sourceJacquetWeight F P χ x * ψ (-(u⁻¹ * x))) :=
    (sourceJacquetWeight_locallyConstant F P χ).continuous.mul
      ((localFiniteCharacter_continuous F P).comp (continuous_const.mul continuous_id).neg)
  unfold sourceJacquetShellIntegral
  rw [compact_finite_integral (sourceJacquetHaar F P) (sourceJacquetIntegers F P)
    (integerOpenSubgroup_compact _) (sourceJacquetReduction F P) (sourceJacquetReduction_surjective F P)
    (fun z => χ z * φ z) _ hf (fun x => by rw [sourceJacquetWeight_on_integers, hphase])]
  simp only [Measure.real, sourceJacquetHaar_integers, ENNReal.toReal_one, Complex.ofReal_one,
    one_mul, hcard, tsum_fintype, φ, ψ]

theorem sourceJacquetShellIntegral_primeGenerator (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 F) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces F) (χ : MulChar ((𝓞 F) ⧸ P.asIdeal) ℂ) :
    sourceJacquetShellIntegral F P χ ((sourceGeneratorCompletionUnit F S₀ P a ha : P.adicCompletion F)⁻¹) =
      residueSourceTau S₀ P hP a ha χ / (Ideal.absNorm P.asIdeal : ℂ) := by
  rw [sourceJacquetShellIntegral_terminal F P χ _
    (sourceGeneratorCompletionUnit_valuation F S₀ P hP a ha) hbad,
    ← residueSourcePhase_eq_negativeIdeal F S₀ P hP a ha hbad]
  rfl

end
end ArtinMatthews
