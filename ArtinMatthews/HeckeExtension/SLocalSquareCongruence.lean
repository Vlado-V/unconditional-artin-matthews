module

public import ArtinMatthews.SLocalWeakApproximation
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

/-! An explicit finite congruence kills all actual S-local square classes.
The local sixth roots are supplied by genuine Hensel lifting. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain ClassFieldTheory
open VaryingKummerAnalytic VaryingKummerAnalytic.ArtinRay
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sLocalGlobalSquareClass_eq_one_of_higher_congruence
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a : 𝓞 K) (ha : a ≠ 0)
    (hc : ∀ v ∈ S,
      algebraMap (𝓞 K) (v.adicCompletionIntegers K) a - 1 ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ sixthLocalHenselDepth v) :
    sLocalGlobalClassMap K 2 S (Units.mk0 (a : K) (by exact_mod_cast ha)) = 1 := by
  funext v
  let u := Units.map (algebraMap K (v.val.adicCompletion K)).toMonoidHom
    (Units.mk0 (a : K) (by exact_mod_cast ha))
  have hu : u ∈ RayClass.localHigherUnitGroup v.val (sixthLocalHenselDepth v.val) :=
    principal_local_mem_higherUnits v.val (sixthLocalHenselDepth_pos v.val) a ha
      (hc v.val v.property)
  obtain ⟨w, hw⟩ := sixthLocal_higherUnit_exists_root v.val u hu
  change powerClass (v.val.adicCompletion K) 2 u = 1
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨w ^ 3, ?_⟩
  change (w ^ 3) ^ 2 = u
  simpa only [← pow_mul] using hw

theorem exists_sLocalSquare_congruence_modulus
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ N : ℕ, 0 < N ∧ ∀ (a : 𝓞 K) (ha : a ≠ 0),
      a - 1 ∈ rationalModulusIdeal (𝓞 K) N →
      sLocalGlobalClassMap K 2 S (Units.mk0 (a : K) (by exact_mod_cast ha)) = 1 := by
  obtain ⟨N, hN, _, hlocal⟩ := exists_integer_for_local_congruences
    S sixthLocalHenselDepth (D := 1) (by decide)
  refine ⟨N, hN, fun a ha hc => ?_⟩
  apply sLocalGlobalSquareClass_eq_one_of_higher_congruence K S a ha
  intro v hv
  exact completed_congruence_of_integer v _ N (hlocal v hv) hc

end
end ArtinMatthews
