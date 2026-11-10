module

public import ArtinMatthews.SLocalRingPowerClasses
public import ArtinMatthews.SLocalHilbertAlternating
public import ArtinMatthews.SLocalHilbertExponent
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Public properties on the literal source ring quotient. The pinned
CFT convention puts the Artin input first; paperSourceHilbertForm
explicitly transposes it to Artin(b)(a^(1/6))/a^(1/6), as in source02. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain KummerTheory ClassFieldTheory
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def sLocalRingUnitPowerClassMap (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (SUnitGroup (K := K) S ⧸
      (powMonoidHom (n : ℕ) : SUnitGroup (K := K) S →* SUnitGroup (K := K) S).range) →*
      SLocalRingPowerClasses K n S :=
  (sLocalRingPowerEquiv K n S).symm.toMonoidHom.comp (sWholeUnitPowerClassMap K n S)

@[simp] theorem sLocalRingUnitPowerClassMap_mk (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u : SUnitGroup (K := K) S) :
    sLocalRingUnitPowerClassMap K n S (QuotientGroup.mk' _ u) =
      sLocalRingGlobalClassMap K n S (u : Kˣ) := by
  apply (sLocalRingPowerEquiv K n S).injective
  rw [sLocalRingPowerEquiv_globalClass]
  exact (sLocalRingPowerEquiv K n S).apply_symm_apply _

theorem source_ring_sixth_unitPowerClassMap_injective {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (sLocalRingUnitPowerClassMap K 6 (sourceHilbertSet K S₀)) :=
  (sLocalRingPowerEquiv K 6 (sourceHilbertSet K S₀)).symm.injective.comp
    (source_sixth_whole_unitPowerClassMap_injective K hζ S₀)

theorem sourceRingHilbertForm_skew {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x y : SLocalRingPowerClasses K 6 S) :
    sourceRingHilbertForm K hζ S x y = (sourceRingHilbertForm K hζ S y x)⁻¹ := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  exact sLocalHilbertForm_skew K 6 _ S _ _

theorem sourceRingHilbertForm_diag_eq_one {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalRingPowerClasses K 6 S) :
    sourceRingHilbertForm K hζ S x x = 1 := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  exact sLocalHilbertForm_diag_eq_one K 6 _ (neg_one_is_sixth_power_of_primitive_twelve K hζ) S _

theorem sourceRingHilbertForm_nondegenerate_left {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalRingPowerClasses K 6 S)
    (hx : ∀ y, sourceRingHilbertForm K hζ S x y = 1) : x = 1 := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  let e := sLocalRingPowerEquiv K 6 S
  let f := sWholePowerEquiv K 6 S
  have h : f (e x) = 1 := by
    apply sLocalHilbertForm_nondegenerate_left K 6 _ S
    intro y
    have hy := hx (e.symm (f.symm y))
    change sLocalHilbertForm K 6
      (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)) S
      (f (e x)) (f (e (e.symm (f.symm y)))) = 1 at hy
    simpa only [e.apply_symm_apply, f.apply_symm_apply] using hy
  apply e.injective
  apply f.injective
  simpa only [map_one] using h

theorem sourceRingHilbertForm_nondegenerate_right {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (y : SLocalRingPowerClasses K 6 S)
    (hy : ∀ x, sourceRingHilbertForm K hζ S x y = 1) : y = 1 := by
  apply sourceRingHilbertForm_nondegenerate_left K hζ S y
  intro x
  rw [sourceRingHilbertForm_skew, hy, inv_one]

theorem sourceRingHilbertForm_globalClasses {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ) :
    sourceRingHilbertForm K hζ S (sLocalRingGlobalClassMap K 6 S a) (sLocalRingGlobalClassMap K 6 S b) =
      ∏ v : S, globalFinitePlaceHilbertSymbol K 6 (by norm_num)
        (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)) v.1 a b := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  change sLocalHilbertForm K 6 _ S
    (sWholePowerEquiv K 6 S (sLocalRingPowerEquiv K 6 S (sLocalRingGlobalClassMap K 6 S a)))
    (sWholePowerEquiv K 6 S (sLocalRingPowerEquiv K 6 S (sLocalRingGlobalClassMap K 6 S b))) = _
  rw [sLocalRingPowerEquiv_globalClass, sLocalRingPowerEquiv_globalClass,
    sWholePowerEquiv_globalClass, sWholePowerEquiv_globalClass]
  exact sLocalHilbertForm_globalMap K 6 _ S a b

def paperSourceHilbertForm {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SLocalRingPowerClasses K 6 S →* (SLocalRingPowerClasses K 6 S →* rootsOfUnity 6 K) :=
  (sourceRingHilbertForm K hζ S).flip

@[simp] theorem paperSourceHilbertForm_apply {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x y : SLocalRingPowerClasses K 6 S) :
    paperSourceHilbertForm K hζ S x y = sourceRingHilbertForm K hζ S y x := rfl

theorem paperSourceHilbertForm_diag_eq_one {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalRingPowerClasses K 6 S) :
    paperSourceHilbertForm K hζ S x x = 1 := sourceRingHilbertForm_diag_eq_one K hζ S x

theorem paperSourceHilbertForm_nondegenerate_left {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalRingPowerClasses K 6 S)
    (hx : ∀ y, paperSourceHilbertForm K hζ S x y = 1) : x = 1 :=
  sourceRingHilbertForm_nondegenerate_right K hζ S x hx

theorem paperSourceHilbertForm_nondegenerate_right {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (y : SLocalRingPowerClasses K 6 S)
    (hy : ∀ x, paperSourceHilbertForm K hζ S x y = 1) : y = 1 :=
  sourceRingHilbertForm_nondegenerate_left K hζ S y hy

theorem paperSourceHilbertForm_globalClasses {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ) :
    paperSourceHilbertForm K hζ S (sLocalRingGlobalClassMap K 6 S a) (sLocalRingGlobalClassMap K 6 S b) =
      ∏ v : S, globalFinitePlaceHilbertSymbol K 6 (by norm_num)
        (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ)) v.1 b a :=
  sourceRingHilbertForm_globalClasses K hζ S b a

theorem source_paper_sixth_isotropic_complement {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ B : Subgroup (SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀)),
      IsCompl (sLocalRingUnitImage K 6 (sourceHilbertSet K S₀)) B ∧
      ∀ x ∈ B, ∀ y ∈ B, paperSourceHilbertForm K hζ (sourceHilbertSet K S₀) x y = 1 := by
  obtain ⟨B, hC, hI⟩ := source_ring_sixth_isotropic_complement K hζ S₀
  exact ⟨B, hC, fun x hx y hy => hI y hy x hx⟩

theorem source_paper_sixth_unitImage_selfOrthogonal {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ x : SLocalRingPowerClasses K 6 (sourceHilbertSet K S₀),
      (∀ y ∈ sLocalRingUnitImage K 6 (sourceHilbertSet K S₀),
        paperSourceHilbertForm K hζ (sourceHilbertSet K S₀) x y = 1) ↔
      x ∈ sLocalRingUnitImage K 6 (sourceHilbertSet K S₀) := by
  intro x
  refine Iff.trans ?_ (source_ring_sixth_unitImage_selfOrthogonal K hζ S₀ x)
  constructor
  · intro hx y hy
    have h := hx y hy
    change sourceRingHilbertForm K hζ (sourceHilbertSet K S₀) y x = 1 at h
    rw [sourceRingHilbertForm_skew, inv_eq_one] at h
    exact h
  · intro hx y hy
    change sourceRingHilbertForm K hζ (sourceHilbertSet K S₀) y x = 1
    rw [sourceRingHilbertForm_skew, hx y hy, inv_one]

end
end ArtinMatthews
