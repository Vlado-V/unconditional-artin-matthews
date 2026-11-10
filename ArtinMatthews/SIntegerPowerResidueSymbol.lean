module

public import ArtinMatthews.SIntegerSexticTransport
public import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.Ideal
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
import GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicField


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical power-residue symbols on genuine S-integer residue classes.
The symbol is constructed from finite-field powering and reduction on
global roots of unity, with no reciprocity or local-Hilbert premise. -/
namespace ArtinMatthews.SIntegerResidueSymbol

open NumberField IsDedekindDomain KummerTheory
open AlgebraicNumberTheory.PowerResidueSymbols
open ArtinMatthews.SIntegerPrincipalization ArtinMatthews.SIntegerQuotient
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

local instance residueSymbolField (P : HeightOneSpectrum (𝓞 K)) : Field ((𝓞 K) ⧸ P.asIdeal) :=
  Ideal.Quotient.field _
local instance residueSymbolFintype (P : HeightOneSpectrum (𝓞 K)) : Fintype ((𝓞 K) ⧸ P.asIdeal) :=
  Fintype.ofFinite _

def powerResidueOnUnit (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) :
    ((𝓞 K) ⧸ P.asIdeal)ˣ →* rootsOfUnity (n : ℕ) (𝓞 K) :=
  (rootsOfUnityReductionEquiv K P n hmu hN).symm.toMonoidHom.comp
    (finiteFieldPowerResidueSymbol ((𝓞 K) ⧸ P.asIdeal) n (by
      rw [card_primeIdealResidueField K P]
      exact dvd_absNorm_sub_one_of_primitiveRoots K P n hmu hN))

theorem powerResidueOnUnit_integral (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    powerResidueOnUnit K P n hmu hN (primeIdealResidueUnit K P a ha) =
      primeIdealPowerResidueSymbol K P n hmu hN a ha := rfl

theorem powerResidueOnUnit_reduce (P : HeightOneSpectrum (𝓞 K)) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) (u : ((𝓞 K) ⧸ P.asIdeal)ˣ) :
    Ideal.Quotient.mk P.asIdeal (((powerResidueOnUnit K P n hmu hN u).1 : (𝓞 K)ˣ) : 𝓞 K) =
      (u : (𝓞 K) ⧸ P.asIdeal) ^ ((Ideal.absNorm P.asIdeal - 1) / (n : ℕ)) := by
  have hr := (rootsOfUnityReductionEquiv K P n hmu hN).apply_symm_apply
    (finiteFieldPowerResidueSymbol ((𝓞 K) ⧸ P.asIdeal) n (by
      rw [card_primeIdealResidueField K P]
      exact dvd_absNorm_sub_one_of_primitiveRoots K P n hmu hN) u)
  have hv := congrArg (fun z : rootsOfUnity (n : ℕ) ((𝓞 K) ⧸ P.asIdeal) =>
    ((z.1 : ((𝓞 K) ⧸ P.asIdeal)ˣ) : (𝓞 K) ⧸ P.asIdeal)) hr
  change Ideal.Quotient.mk P.asIdeal (((powerResidueOnUnit K P n hmu hN u).1 : (𝓞 K)ˣ) : 𝓞 K) =
    (u : (𝓞 K) ⧸ P.asIdeal) ^ ((Fintype.card ((𝓞 K) ⧸ P.asIdeal) - 1) / (n : ℕ)) at hv
  simpa only [card_primeIdealResidueField K P] using hv

def sIntegerResidueUnit (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    ((𝓞 K) ⧸ P.asIdeal)ˣ :=
  Units.mk0 (generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ x)) (by
    intro hz
    apply hx
    rw [ha]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (generatorResidueEquiv S₀ P hP a ha).injective (hz.trans (map_zero _).symm))

theorem sIntegerResidueUnit_val (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    (sIntegerResidueUnit K S₀ P hP a ha x hx : (𝓞 K) ⧸ P.asIdeal) =
      generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ x) := rfl

def sIntegerPowerResidueSymbol (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    rootsOfUnity (n : ℕ) (𝓞 K) :=
  powerResidueOnUnit K P n hmu hN (sIntegerResidueUnit K S₀ P hP a ha x hx)

theorem sIntegerPowerResidueSymbol_reduce (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ)) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    Ideal.Quotient.mk P.asIdeal
      (((sIntegerPowerResidueSymbol K S₀ P hP a ha n hmu hN x hx).1 : (𝓞 K)ˣ) : 𝓞 K) =
      (generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ x)) ^
        ((Ideal.absNorm P.asIdeal - 1) / (n : ℕ)) :=
  powerResidueOnUnit_reduce K P n hmu hN _

end
end ArtinMatthews.SIntegerResidueSymbol
