module

public import ArtinMatthews.SourceKPExteriorWhittakerPhase
public import ArtinMatthews.AllowedGeneratorSelection
public import ArtinMatthews.SourceKPExteriorTorusValues
public import ArtinMatthews.SourceKPExteriorWhittakerCoefficient
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

/-! The exterior Whittaker value is invariant under the actual sixth
S-unit ambiguity of allowed generators. The unsupported valuation
class gives a literal zero factor. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "C₀" => sourceKPTameUniformizerCharacter K hζ P.val π₀

theorem sourceKPTameCyclicWhittakerValue_diagonal_mul_sixth (a u : Lˣ) (hu : ν₀ (u : L) = 1) :
    W₀ (l₀ (sourceGL2Diagonal (a * u ^ (6 : ℕ)))) = W₀ (l₀ (sourceGL2Diagonal a)) := by
  let e := sourceKPValuationOrder ν₀ a
  let v := sourceKPUnitPart ν₀ π₀ a
  have hv : ν₀ (v : L) = 1 := sourceKPUnitPart_valuation ν₀ π₀ hπ₀ a
  have hvu : ν₀ ((v * u ^ (6 : ℕ) : Lˣ) : L) = 1 := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hv, hu, one_pow, one_mul]
  have ha : π₀ ^ e * v = a := sourceKPUnitPart_factor ν₀ π₀ a
  have h' : a * u ^ (6 : ℕ) = π₀ ^ e * (v * u ^ (6 : ℕ)) := by
    rw [← ha, mul_assoc]
  have hphase (z : Lˣ) (hz : ν₀ (z : L) = 1) :
      χ₀ (sourceKPLocalUnitResidue K P.val z hz) ^ (2 * e) = ((C₀ z : ℂˣ) : ℂ) ^ (-e) := by
    rw [sourceKPTameExteriorCharacter_residue K hζ S₀ P z hz, ← zpow_mul]
    rw [show (-2 : ℤ) * (-e) = 2 * e by ring]
  have hC : C₀ (v * u ^ (6 : ℕ)) = C₀ v := by
    rw [map_mul, map_pow, show (6 : ℕ) = 3 * 2 by decide, pow_mul,
      sourceKPTameUniformizerCharacter_cube K hζ P.val π₀ u, one_pow, mul_one]
  calc
    _ = ((C₀ (v * u ^ (6 : ℕ)) : ℂˣ) : ℂ) ^ (-e) *
        W₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) := by
      rw [h', sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS e _ hvu, hphase _ hvu]
    _ = ((C₀ v : ℂˣ) : ℂ) ^ (-e) * W₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) := by rw [hC]
    _ = _ := by
      rw [← hphase v hv, ← sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS e v hv, ha]

theorem sourceKPTameExteriorWhittakerDiagonal_same_ideal (a b : Kˣ)
    (ha : a ∈ allowedSubgroup K hζ S₀) (hb : b ∈ allowedSubgroup K hζ S₀)
    (hab : _root_.toPrincipalIdeal (sourceRing K S₀) K a = _root_.toPrincipalIdeal (sourceRing K S₀) K b) :
    sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS a =
      sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS b := by
  obtain ⟨u, hu⟩ := allowed_ratio_sixth K hζ S₀ a b ha hb hab
  have he : a = b * (u : Kˣ) ^ (6 : ℕ) := div_eq_iff_eq_mul'.mp hu
  let j := Units.map (algebraMap K L).toMonoidHom
  have hv : ν₀ (j (u : Kˣ) : L) = 1 := by
    change Valued.v (((u : Kˣ) : K) : L) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact u.property P.val P.property
  have hj : j a = j b * j (u : Kˣ) ^ (6 : ℕ) := by rw [he, map_mul, map_pow]
  change W₀ (l₀ (sourceGL2Diagonal (j a))) = W₀ (l₀ (sourceGL2Diagonal (j b)))
  rw [hj, sourceKPTameCyclicWhittakerValue_diagonal_mul_sixth K hζ S₀ hS P _ _ hv]

theorem sourceKPTameExteriorWhittakerDiagonal_exponent_bad
    (e : SourcePrimeExponents K S₀) (he : e P % 3 = 2) :
    sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS (sourcePrimeExponentUnit K hζ S₀ e) = 0 := by
  have h : e P = 3 * (e P / 3) + 2 := by omega
  rw [sourceKPTameExteriorWhittakerDiagonal_exponent]
  have hz := sourceKPTameCyclicWhittakerValue_diagonal_three_add_two K hζ S₀ P hS (e P / 3)
  rw [← h] at hz
  rw [hz, mul_zero]

theorem sourceKPTameExteriorWhittakerProduct_bad
    (e : SourcePrimeExponents K S₀) (T : Finset (SourceExteriorPrime K S₀)) (hT : P ∈ T)
    (he : e P % 3 = 2) :
    (∏ Q ∈ T, sourceKPTameExteriorWhittakerDiagonal K hζ S₀ Q hS (sourcePrimeExponentUnit K hζ S₀ e)) = 0 :=
  Finset.prod_eq_zero hT (sourceKPTameExteriorWhittakerDiagonal_exponent_bad K hζ S₀ hS P e he)

omit P in
theorem sourceKPTameExteriorWhittakerProduct_allowed_squarefree_cube (a : Kˣ)
    (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀)
    (ha : a ∈ allowedSubgroup K hζ S₀)
    (hI : _root_.toPrincipalIdeal (sourceRing K S₀) K a = _root_.toPrincipalIdeal (sourceRing K S₀) K
      (sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)))
    (T : Finset (SourceExteriorPrime K S₀)) (hc : c.val.support ⊆ T) (hn : n.support ⊆ T) :
    (∏ Q ∈ T, sourceKPTameExteriorWhittakerDiagonal K hζ S₀ Q hS a) =
      reflectionGammaTwo K hζ S₀ c.val /
        ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) * (sourcePrimeExponentNorm K S₀ n : ℂ)) := by
  calc
    _ = ∏ Q ∈ T, sourceKPTameExteriorWhittakerDiagonal K hζ S₀ Q hS
        (sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)) := by
      apply Finset.prod_congr rfl
      intro Q _
      exact sourceKPTameExteriorWhittakerDiagonal_same_ideal K hζ S₀ hS Q a _
        ha (sourcePrimeExponentUnit_allowed K hζ S₀ _) hI
    _ = _ := sourceKPTameExteriorWhittakerProduct_squarefree_cube K hζ S₀ hS c n T hc hn

end
end ArtinMatthews
