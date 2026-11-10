module

public import ArtinMatthews.SourceReflectionFrequencyCofactor
public import ArtinMatthews.SourceKPExteriorWhittakerPhase
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

/-! Exact phases of the active and ordinary local factors on the
numerator support. The ordinary calculation allows the cube exponent
at a squarefree numerator prime. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic AllowedGenerators StandardAdelic QuadraticWeil
open scoped NumberField Classical MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
  {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "S" => sourceHilbertSet K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "U" => exteriorUnitSubgroup S
local notation "Γ" => SourceExteriorUnitSixthPowers S
local notation "a₀" => sourcePrimeExponentUnit K hζ S₀
local notation "f₀" => sourceReflectionActiveExponents K S₀

def sourceReflectionSphericalFixedPhase (ε : U) (f : Finset Pr) (a : E) (P : Pr) : ℂˣ :=
  sourceReflectionTameUnitCharacter K hζ S₀ P (sourceReflectionExteriorUnitCompletion K S₀ P ε) *
    sourceReflectionDirectedCofactor K S₀ hζ P a *
      (sourceReflectionDirectedCofactor K S₀ hζ P (f₀ f)) ^ (-2 : ℤ)

def sourceReflectionActiveFixedPhase (ε : U) (f : Finset Pr) (a n : E) (P : Pr) : ℂˣ :=
  sourceReflectionSphericalFixedPhase K S₀ hζ ε f a P *
    (sourceReflectionDirectedCofactor K S₀ hζ P n) ^ (3 : ℕ)

def sourceReflectionExteriorFrequency (ε : U) (γ : Γ) (f : Finset Pr) (a n d c : E) : Kˣ :=
  γ.val.val * ε.val * a₀ (a + c + 3 • n) / (a₀ (f₀ f + d)) ^ (2 : ℕ)

variable (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "V" => sourceReflectionTameValuationUnits K S₀ P
local notation "χ" => sourceReflectionTameUnitCharacter K hζ S₀ P
local notation "u" => sourceReflectionExteriorUnitCompletion K S₀ P
local notation "D" => sourceReflectionDirectedCofactor K S₀ hζ P
local notation "F" => sourceReflectionSphericalFixedPhase K S₀ hζ
local notation "A" => sourceReflectionActiveFixedPhase K S₀ hζ
local notation "v₀" => sourceReflectionFrequencyLocalUnit K S₀ hζ P
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "D₀" => fun z : Lˣ => sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Diagonal z)
local notation "j₀" => Units.map (RingHom.toMonoidHom (algebraMap K L))

private theorem frequency_phase_factors (ε : U) (f : Finset Pr) (a n d c : E) :
    χ (u ε) * D (a + c + 3 • n) * D (f₀ f + d) ^ (-2 : ℤ) =
      A ε f a n P * (D d ^ (-2 : ℤ)) * D c := by
  simp only [sourceReflectionActiveFixedPhase, sourceReflectionSphericalFixedPhase,
    sourceReflectionDirectedCofactor_add, sourceReflectionDirectedCofactor_nsmul, mul_zpow]
  ac_rfl

theorem sourceReflectionActiveFrequency_phase (ε : U) (γ : Γ) (f : Finset Pr) (a n d c : E) :
    χ (v₀ (sourceReflectionExteriorSign K S₀ * (γ.val * ε)) (a + c + 3 • n) (f₀ f + d)) =
      A ε f a n P * (D d ^ (-2 : ℤ)) * D c := by
  rw [sourceReflectionFrequencyLocalUnit_character_signed]
  exact frequency_phase_factors K S₀ hζ P ε f a n d c

variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
local notation "R" => sourceReflectionTameRotatedActive K hζ S₀ P hS
local notation "W" => sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS
local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS

theorem sourceReflectionActiveFrequency_factor (ε : U) (γ : Γ) (f : Finset Pr) (a n d c : E)
    (j : Fin 6) (e : ℕ) :
    R j e (v₀ (sourceReflectionExteriorSign K S₀ * (γ.val * ε))
        (a + c + 3 • n) (f₀ f + d)).val =
      (R j e 1 * (↑(A ε f a n P ^ sourceReflectionTameActiveExponent j e) : ℂ)) *
        (↑((D d ^ (-2 : ℤ)) ^ sourceReflectionTameActiveExponent j e) : ℂ) *
        (↑(D c ^ sourceReflectionTameActiveExponent j e) : ℂ) := by
  rw [sourceReflectionTameRotatedActive_monomial K hζ S₀ P hS,
    sourceReflectionActiveFrequency_phase, mul_zpow, mul_zpow]
  simp only [Units.val_mul, mul_assoc]

theorem sourceReflectionActiveFrequency_row_factor (ε : U) (γ : Γ) (f : Finset Pr) (a n d c : E) :
    R 1 0 (v₀ (sourceReflectionExteriorSign K S₀ * (γ.val * ε))
        (a + c + 3 • n) (f₀ f + d)).val =
      (R 1 0 1 * (↑(A ε f a n P * D d ^ (-2 : ℤ)) : ℂ)) * (D c : ℂ) := by
  rw [sourceReflectionTameRotatedActive_one_zero K hζ S₀ P hS,
    sourceReflectionActiveFrequency_phase, Units.val_mul, mul_assoc]

private theorem squarefree_cube_phase (z : ℂˣ) (h : z ^ (6 : ℕ) = 1) (m k : ℕ) :
    z ^ (2 * ((m + 3 * k : ℕ) : ℤ)) = z ^ (2 * (m : ℤ)) := by
  have hz : z ^ (6 : ℤ) = 1 := by
    rw [show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast, h]
  rw [show 2 * ((m + 3 * k : ℕ) : ℤ) = 2 * (m : ℤ) + 6 * (k : ℤ) by push_cast; ring,
    zpow_add, zpow_mul z 6 (k : ℤ), hz, one_zpow, mul_one]

theorem sourceReflectionSphericalFrequency_factor (ε : U) (γ : Γ) (f : Finset Pr)
    (a n d : E) (c : ReflectionSquarefreeExponents K S₀)
    (ha : a P = 0) (hb : (f₀ f + d) P = 0) :
    W (sourceReflectionExteriorFrequency K S₀ hζ ε γ f a n d c.val) =
      (if P ∈ c.val.support then
        (↑(F ε f a P ^ (2 : ℕ) * D d ^ (-4 : ℤ)) : ℂ) else 1) *
      W (a₀ (c.val + 3 • n)) := by
  let e := c.val + 3 • n
  let v : V := v₀ (γ.val * ε) (a + c.val + 3 • n) (f₀ f + d)
  let w : V := sourceReflectionOmittedPrimeUnit K S₀ hζ P e
  have he : e P = c.val P + 3 * n P := by
    simp only [e, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hm : (a + c.val + 3 • n) P = e P := by
    simp only [he, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, ha, zero_add]
  have ht : j₀ (sourceReflectionExteriorFrequency K S₀ hζ ε γ f a n d c.val) =
      π₀ ^ (e P : ℤ) * v.val := by
    have h := sourceReflectionFrequencyLocalUnit_completion K S₀ hζ P (γ.val * ε)
      (a + c.val + 3 • n) (f₀ f + d)
    rw [hm, hb, Nat.cast_zero, mul_zero, sub_zero] at h
    exact h
  have hvχ : χ v = F ε f a P * χ w * D d ^ (-2 : ℤ) := by
    dsimp only [v]
    rw [sourceReflectionFrequencyLocalUnit_character_orbit,
      frequency_phase_factors K S₀ hζ P ε f a n d c.val,
      sourceReflectionOmittedPrimeUnit_character, sourceReflectionActiveFixedPhase]
    simp only [e, sourceReflectionDirectedCofactor_add, sourceReflectionDirectedCofactor_nsmul]
    ac_rfl
  have hleft : W (sourceReflectionExteriorFrequency K S₀ hζ ε γ f a n d c.val) =
      (↑(χ v ^ (2 * (e P : ℤ))) : ℂ) * W₀ (D₀ (π₀ ^ (e P : ℤ))) := by
    unfold sourceKPTameExteriorWhittakerDiagonal
    rw [ht, sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS _ v.val v.property,
      ← sourceReflectionTameUnitCharacter_val K hζ S₀ P v, Units.val_zpow_eq_zpow_val]
  have hright : W (a₀ e) =
      (↑(χ w ^ (2 * (e P : ℤ))) : ℂ) * W₀ (D₀ (π₀ ^ (e P : ℤ))) := by
    rw [sourceKPTameExteriorWhittakerDiagonal_exponent K hζ S₀ P hS e,
      Units.val_zpow_eq_zpow_val, sourceReflectionTameUnitCharacter_val]
    rfl
  rw [hleft, hright, he, squarefree_cube_phase (χ v) (sourceReflectionTameUnitCharacter_pow_six K hζ S₀ P v),
    squarefree_cube_phase (χ w) (sourceReflectionTameUnitCharacter_pow_six K hζ S₀ P w)]
  by_cases hp : P ∈ c.val.support
  · have hc : c.val P = 1 := reflectionSquarefreeExponent_support_one K S₀ c ⟨P,hp⟩
    have hphase : χ v ^ (2 : ℤ) =
        (F ε f a P ^ (2 : ℕ) * D d ^ (-4 : ℤ)) * χ w ^ (2 : ℤ) := by
      rw [hvχ, mul_zpow, mul_zpow, ← zpow_mul]
      change F ε f a P ^ (2 : ℤ) * χ w ^ (2 : ℤ) * D d ^ (-4 : ℤ) = _
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_natCast]
      ac_rfl
    rw [ite_eq_left hp, hc, Nat.cast_one, mul_one, hphase, Units.val_mul, mul_assoc]
  · simp only [ite_eq_right hp, Finsupp.notMem_support_iff.mp hp, Nat.cast_zero, mul_zero,
      zpow_zero, Units.val_one, one_mul]

end
end ArtinMatthews.SourceEulerAssembly
