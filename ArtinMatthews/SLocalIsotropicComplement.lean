module

public import ArtinMatthews.SLocalBilinearForm
public import ArtinMatthews.AlternatingIsotropicComplement
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual isotropic complements for the prime-exponent S-local Hilbert
spaces. Every arithmetic input to the finite-field complement theorem
is proved; no self-orthogonality or complement premise is supplied. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.GlobalClassFields GlobalClassFieldTheory.Reciprocity
open SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem normSupport_exponent_subset (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    powerResidueExponentFinitePlaces K n ⊆ S := by
  intro v hv
  apply hS
  apply mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast n ∅
  exact (mem_powerResidueExponentFinitePlaces_iff K n v).mp hv

variable [NumberField.IsTotallyComplex K]

theorem sLocal_exists_isotropic_complement (n : ℕ+) [Fact (n : ℕ).Prime]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ (n : ℕ))
    (hminus : ∃ a : Kˣ, a ^ (n : ℕ) = -1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    ∃ B : Submodule (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S)),
      IsCompl (sUnitPowerSubmodule K n S) B ∧
        ∀ x ∈ B, ∀ y ∈ B,
          sLocalHilbertForm K n (sLocalPrimitiveRoots K n hζ) S
            (Additive.toMul x) (Additive.toMul y) = 1 := by
  let : Finite (Additive (SLocalPowerClasses K n S)) :=
    sLocalBilinearForm_finite K n (sLocalPrimitiveRoots K n hζ) S hS
  obtain ⟨B, hB, hIso⟩ := exists_isotropic_complement_of_card
    (sLocalBilinearForm K n hζ S) (sLocalBilinearForm_isAlt K n hζ hminus S)
    (sLocalBilinearForm_nondegenerate K n hζ S) (sUnitPowerSubmodule K n S)
    (sLocalBilinearForm_unitSubmodule_isotropic K n hζ S (normSupport_exponent_subset K n S hS))
    (sLocalBilinearForm_card_relation K n (sLocalPrimitiveRoots K n hζ) S hS)
  refine ⟨B, hB, ?_⟩
  intro x hx y hy
  exact (sLocalRootLog_eq_zero_iff K n hζ _).mp (hIso x hx y hy)

end
end ArtinMatthews
