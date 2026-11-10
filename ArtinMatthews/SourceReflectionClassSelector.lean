module

public import ArtinMatthews.SourceReflectionRowClass
public import ArtinMatthews.SourceFrequencyOrbitSeparation
public import ArtinMatthews.SourcePrimeExponentProducts
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! The finite slices of the reflected profile are indexed by the actual
whole sixth-power classes of the fixed source generators. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "S" => sourceHilbertSet F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "Prime" => SourceExteriorPrime F S₀
local notation "Q" => SWholePowerClasses F 6 S
local notation "Classes" => ExteriorUnitSixthClasses (K := F) S
local notation "cl" => sWholeGlobalClassMap F 6 S
local notation "gen" => sourcePrimeExponentUnit F hζ S₀
local notation "ε" => sourceExteriorUnitSixthRepresentative (F := F) S

include hζ in
theorem sourceReflectionSixthClass_finite : Finite Q := by
  let : IsTotallyComplex F := source_isTotallyComplex F hζ
  let : Finite (SLocalPowerClasses F 6 S) :=
    sLocalBilinearForm_finite F 6
      (sLocalPrimitiveRoots F 6 (sourceHilbertRootSix_isPrimitive F hζ)) S
      (normSupport_subset_sourceHilbertSet F S₀ 6 (Or.inr (Or.inr rfl)))
  exact Finite.of_equiv _ (sWholePowerEquiv F 6 S).toEquiv.symm

@[instance_reducible] def sourceReflectionSixthClassFintype : Fintype Q := by
  letI := sourceReflectionSixthClass_finite F S₀ hζ
  exact Fintype.ofFinite Q

def sourceReflectionSixthClassLabels : Finset Q :=
  @Finset.univ Q (sourceReflectionSixthClassFintype F S₀ hζ)

@[simp] theorem mem_sourceReflectionSixthClassLabels (s : Q) :
    s ∈ sourceReflectionSixthClassLabels F S₀ hζ :=
  @Finset.mem_univ Q (sourceReflectionSixthClassFintype F S₀ hζ) s

def sourceReflectionExponentSixthClass (e : E) : Q := cl (gen e)

local notation "C" => sourceReflectionExponentSixthClass F S₀ hζ

theorem sourceReflectionExponentSixthClass_add (e e' : E) :
    C (e + e') = C e * C e' := by
  rw [sourceReflectionExponentSixthClass, sourcePrimeExponentUnit_add, map_mul]
  rfl

theorem sourceReflectionExponentSixthClass_three_nsmul (e : E) :
    C (3 • e) = C e ^ 3 := by
  rw [show 3 • e = (e + e) + e by
        rw [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, two_nsmul, one_nsmul],
      sourceReflectionExponentSixthClass_add, sourceReflectionExponentSixthClass_add]
  simp only [pow_succ, pow_zero, one_mul]

/-- The class of the exterior unit in the actual whole local quotient. -/
def sourceReflectionExteriorUnitClass : Classes →* Q := by
  let φ : exteriorUnitSubgroup (K := F) S →* SWholeUnits F S :=
    (sWholeDiagonal F S).comp (exteriorUnitSubgroup (K := F) S).subtype
  refine QuotientGroup.map (SourceExteriorUnitSixthPowers (F := F) S)
    (powMonoidHom (6 : ℕ) : SWholeUnits F S →* SWholeUnits F S).range φ ?_
  rintro _ ⟨v, rfl⟩
  exact ⟨φ v, (map_pow φ v 6).symm⟩

@[simp] theorem sourceReflectionExteriorUnitClass_mk (u : exteriorUnitSubgroup (K := F) S) :
    sourceReflectionExteriorUnitClass F S₀ (sourceExteriorUnitSixthClass S u) = cl u.val :=
  rfl

theorem sourceReflectionExteriorUnitClass_representative (u : Classes) :
    sourceReflectionExteriorUnitClass F S₀ u = cl (ε u).val := by
  rw [← sourceReflectionExteriorUnitClass_mk, sourceExteriorUnitSixthRepresentative_class]

theorem sourceReflectionCanonicalRow_fieldUnit (e : E) (u : Classes) :
    sourceNonzeroFrequencyFieldUnit F S₀
      ⟨sourceReflectionCanonicalRow F S₀ hζ e u,
        sourceReflectionCanonicalRow_ne_zero F S₀ hζ e u⟩ = (ε u).val * gen e := by
  apply Units.ext
  rw [sourceNonzeroFrequencyFieldUnit_val]
  change (↑(sourceReflectionCanonicalRow F S₀ hζ e u) : F) = ↑((ε u).val * gen e)
  unfold sourceReflectionCanonicalRow
  rw [Subalgebra.coe_mul, sourceExteriorUnitToSourceRing_val, Units.val_mul,
    sourcePrimeExponentUnit_val]

/-- The reflected class for a fixed pair of row and column slices. -/
def sourceReflectionProfileClass (u : Classes) (f : Finset Prime) (a n : E)
    (sd sc : Q) : Q :=
  sourceReflectionExteriorUnitClass F S₀ u * C a * sc * C n ^ 3 *
    sd ^ (-2 : ℤ) * C (sourceReflectionActiveExponents F S₀ f) ^ (-2 : ℤ)

theorem sourceReflectionProfileClass_eq (u : Classes) (f : Finset Prime)
    (a n d c : E) (γ : Fˣ) :
    cl (γ ^ 6 * (ε u).val * gen (a + c + 3 • n) /
      gen (sourceReflectionActiveExponents F S₀ f + d) ^ 2) =
      sourceReflectionProfileClass F S₀ hζ u f a n (C d) (C c) := by
  have hγ : cl γ ^ 6 = 1 := powerQuotient_pow_eq_one 6 _
  let cf := C (sourceReflectionActiveExponents F S₀ f)
  have hden : ((cf * C d) ^ 2)⁻¹ = C d ^ (-2 : ℤ) * cf ^ (-2 : ℤ) := by
    rw [mul_pow cf (C d) 2, mul_inv_rev (cf ^ 2) (C d ^ 2)]
    exact congrArg₂ (· * ·) (zpow_negSucc (C d) 1).symm (zpow_negSucc cf 1).symm
  simp only [map_div, map_mul, map_pow, hγ]
  rw [one_mul (cl (ε u).val)]
  change cl (ε u).val * C (a + c + 3 • n) /
      C (sourceReflectionActiveExponents F S₀ f + d) ^ 2 = _
  rw [sourceReflectionProfileClass, sourceReflectionExteriorUnitClass_representative F S₀ u,
    sourceReflectionExponentSixthClass_add, sourceReflectionExponentSixthClass_add,
    sourceReflectionExponentSixthClass_three_nsmul, sourceReflectionExponentSixthClass_add,
    div_eq_mul_inv, hden]
  let ce := cl (ε u).val
  change ce * (C a * C c * C n ^ 3) * (C d ^ (-2 : ℤ) * cf ^ (-2 : ℤ)) = _
  rw [← mul_assoc ce (C a * C c) (C n ^ 3), ← mul_assoc ce (C a) (C c),
    ← mul_assoc (ce * C a * C c * C n ^ 3) (C d ^ (-2 : ℤ)) (cf ^ (-2 : ℤ))]

/-- The class restriction on a single row or column. -/
def sourceReflectionClassIndicator (e : E) (s : Q) : ℂ :=
  if C e = s then 1 else 0

local notation "δ" => sourceReflectionClassIndicator F S₀ hζ

theorem sourceReflectionClassIndicator_norm_le_one (e : E) (s : Q) : ‖δ e s‖ ≤ 1 := by
  unfold sourceReflectionClassIndicator
  split <;> simp

theorem sourceReflectionClassIndicator_pair_eq_one_iff (d c : E) (sd sc : Q) :
    δ d sd * δ c sc = 1 ↔ sd = C d ∧ sc = C c := by
  rw [eq_comm (a := sd), eq_comm (a := sc)]
  by_cases hd : C d = sd <;> by_cases hc : C c = sc <;>
    simp [sourceReflectionClassIndicator, hd, hc]

theorem sourceReflectionClassSelector (d c : E) (Ψ : Q → Q → ℂ) :
    (∑ sd ∈ sourceReflectionSixthClassLabels F S₀ hζ,
      ∑ sc ∈ sourceReflectionSixthClassLabels F S₀ hζ, δ d sd * δ c sc * Ψ sd sc) =
    Ψ (C d) (C c) := by
  rw [Finset.sum_eq_single_of_mem (C d) (mem_sourceReflectionSixthClassLabels F S₀ hζ _)]
  · rw [Finset.sum_eq_single_of_mem (C c) (mem_sourceReflectionSixthClassLabels F S₀ hζ _)]
    · simp [sourceReflectionClassIndicator]
    · intro sc _ hsc
      simp [sourceReflectionClassIndicator, Ne.symm hsc]
  · intro sd _ hsd
    simp [sourceReflectionClassIndicator, Ne.symm hsd]

/-- The source class profile is a finite sum of separated row and column
restrictions. The surviving term retains the exterior unit class. -/
theorem sourceReflectionProfileClassSelector (u : Classes) (f : Finset Prime)
    (a n d c : E) (γ : Fˣ) (Φ : Q → ℂ) :
    (∑ sd ∈ sourceReflectionSixthClassLabels F S₀ hζ,
      ∑ sc ∈ sourceReflectionSixthClassLabels F S₀ hζ,
        δ d sd * δ c sc * Φ (sourceReflectionProfileClass F S₀ hζ u f a n sd sc)) =
    Φ (cl (γ ^ 6 * (ε u).val * gen (a + c + 3 • n) /
      gen (sourceReflectionActiveExponents F S₀ f + d) ^ 2)) := by
  rw [sourceReflectionProfileClass_eq]
  exact sourceReflectionClassSelector F S₀ hζ d c
    (fun sd sc => Φ (sourceReflectionProfileClass F S₀ hζ u f a n sd sc))

end
end ArtinMatthews.SourceEulerAssembly
