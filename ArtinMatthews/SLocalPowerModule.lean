module

public import ArtinMatthews.SLocalUnitImage
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

/-! The canonical Z/nZ module on the actual local power quotient and
the actual S-unit image submodule. Primitive roots give an actual
additive logarithm of the roots of unity. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem powerQuotient_pow_eq_one {G : Type*} [CommGroup G]
    (n : ℕ) (q : G ⧸ (powMonoidHom n : G →* G).range) : q ^ n = 1 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨a, rfl⟩

theorem sLocalPowerClasses_pow_eq_one (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : SLocalPowerClasses K n S) :
    x ^ (n : ℕ) = 1 := by
  funext v
  exact powerQuotient_pow_eq_one (n : ℕ) (x v)

instance sLocalPowerClasses_zmodModule (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Module (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S)) :=
  AddCommGroup.zmodModule (fun x => sLocalPowerClasses_pow_eq_one K n S (Additive.toMul x))

def sUnitPowerSubmodule (n : ℕ+) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Submodule (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S)) :=
  AddSubgroup.toZModSubmodule (n : ℕ) (Subgroup.toAddSubgroup (sUnitPowerImage K n S))

@[simp] theorem mem_sUnitPowerSubmodule (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Additive (SLocalPowerClasses K n S)) :
    x ∈ sUnitPowerSubmodule K n S ↔
      Additive.toMul x ∈ (sUnitPowerImage K n S : Set (SLocalPowerClasses K n S)) := Iff.rfl

def sLocalRootLog (n : ℕ+) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ (n : ℕ)) :
    Additive (rootsOfUnity (n : ℕ) K) ≃+ ZMod (n : ℕ) := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  exact ((MulEquiv.subgroupCongr hζ.zpowers_eq).toAdditive.symm).trans hζ.zmodEquivZPowers.symm

omit [NumberField K] in
theorem sLocalRootLog_eq_zero_iff (n : ℕ+) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ (n : ℕ)) (z : rootsOfUnity (n : ℕ) K) :
    sLocalRootLog K n hζ (Additive.ofMul z) = 0 ↔ z = 1 := by
  constructor
  · intro hz
    have h : Additive.ofMul z = (0 : Additive (rootsOfUnity (n : ℕ) K)) := by
      apply (sLocalRootLog K n hζ).injective
      simpa only [map_zero] using hz
    exact h
  · intro hz
    subst z
    exact map_zero (sLocalRootLog K n hζ)

end
end ArtinMatthews
