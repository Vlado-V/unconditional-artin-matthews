module

public import ArtinMatthews.SLocalRingHilbertProperties
public import ArtinMatthews.ProbeHilbertSReciprocity
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.PNatToNat
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact source02 normalization and global representative coverage on
the literal F_S multiplicative power quotient. The Artin input/radical
order is explicit, and the complex-place factors are proved to be one. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory ClassFieldTheory
open GlobalClassFieldTheory.Reciprocity VaryingKummerAnalytic
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem paperSourceHilbertForm_global_eq_SProduct {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ) :
    paperSourceHilbertForm K hζ S (sLocalRingGlobalClassMap K 6 S a) (sLocalRingGlobalClassMap K 6 S b) =
      nthRootsSubgroupEquivRootsOfUnity K 6
        (probeHilbertSProduct K 6 (by norm_num)
          (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)) S b a) := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  rw [paperSourceHilbertForm_globalClasses]
  unfold probeHilbertSProduct
  have hi (v : InfinitePlace K) : infinitePlaceHilbertSymbol K 6 v b a = 1 :=
    infinitePlaceHilbertSymbol_eq_one_of_isComplex K 6 v b a (NumberField.IsTotallyComplex.isComplex v)
  simp only [hi, Finset.prod_const_one, one_mul]
  exact Finset.prod_coe_sort S (fun v => globalFinitePlaceHilbertSymbol K 6 (by norm_num)
    (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)) v b a)

theorem source_ring_globalClassMap_surjective {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (sLocalRingGlobalClassMap K 6 S) := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  let e := (sLocalRingPowerEquiv K 6 S).trans (sWholePowerEquiv K 6 S)
  intro y
  obtain ⟨a, ha⟩ := sLocalGlobalClassMap_surjective K 6
    (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)) S (e y)
  refine ⟨a, e.injective ?_⟩
  change sWholePowerEquiv K 6 S (sLocalRingPowerEquiv K 6 S (sLocalRingGlobalClassMap K 6 S a)) = e y
  rw [sLocalRingPowerEquiv_globalClass, sWholePowerEquiv_globalClass]
  exact ha

end
end ArtinMatthews
