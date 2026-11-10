module

public import ArtinMatthews.SLocalRingPowerClasses
public import ArtinMatthews.SixthLocalHensel
public import ArtinMatthews.VaryingKummerAnalyticRayCharacter
public import ArtinMatthews.ArtinRayLocalCongruence
public import ArtinMatthews.SixthLocalHenselRay
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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Genuine fixed congruence kernel for the literal source F_S/sixth powers,
including the archimedean factors. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory
open VaryingKummerAnalytic VaryingKummerAnalytic.ArtinRay
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sLocalGlobalSixthClass_eq_one_of_higher_congruence
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : 𝓞 K) (ha : a ≠ 0)
    (hc : ∀ v ∈ S,
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) a - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ sixthLocalHenselDepth v) :
    sLocalGlobalClassMap K 6 S (Units.mk0 (a : K) (by exact_mod_cast ha)) = 1 := by
  funext v
  let u := Units.map (algebraMap K (v.val.adicCompletion K)).toMonoidHom
    (Units.mk0 (a : K) (by exact_mod_cast ha))
  have hu : u ∈ RayClass.localHigherUnitGroup v.val (sixthLocalHenselDepth v.val) :=
    principal_local_mem_higherUnits v.val (sixthLocalHenselDepth_pos v.val) a ha
      (hc v.val v.property)
  obtain ⟨w, hw⟩ := sixthLocal_higherUnit_exists_root v.val u hu
  change powerClass (v.val.adicCompletion K) 6 u = 1
  exact (QuotientGroup.eq_one_iff _).mpr ⟨w, hw⟩

variable [NumberField.IsTotallyComplex K]

theorem sLocalRingGlobalClass_eq_one_of_finite (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : Kˣ)
    (ha : sLocalGlobalClassMap K n S a = 1) :
    sLocalRingGlobalClassMap K n S a = 1 := by
  let e := (sLocalRingPowerEquiv K n S).trans (sWholePowerEquiv K n S)
  apply e.injective
  change sWholePowerEquiv K n S
    (sLocalRingPowerEquiv K n S (sLocalRingGlobalClassMap K n S a)) = e 1
  rw [sLocalRingPowerEquiv_globalClass, sWholePowerEquiv_globalClass, map_one]
  exact ha

theorem exists_sourceSixth_congruence_modulus
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ N : ℕ, 0 < N ∧ ∀ (a : 𝓞 K) (ha : a ≠ 0),
      a - 1 ∈ rationalModulusIdeal (𝓞 K) N →
      sLocalRingGlobalClassMap K 6 S (Units.mk0 (a : K) (by exact_mod_cast ha)) = 1 := by
  obtain ⟨N, hN, _, hlocal⟩ := exists_integer_for_local_congruences
    S sixthLocalHenselDepth (D := 1) (by decide)
  refine ⟨N, hN, fun a ha hc => ?_⟩
  apply sLocalRingGlobalClass_eq_one_of_finite K 6 S
  apply sLocalGlobalSixthClass_eq_one_of_higher_congruence K S a ha
  intro v hv
  exact completed_congruence_of_integer v _ N (hlocal v hv) hc

end
end ArtinMatthews
