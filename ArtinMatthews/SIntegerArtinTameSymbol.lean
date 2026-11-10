module

public import ArtinMatthews.SIntegerArtinUnit
public import ArtinMatthews.SIntegerPowerResidueSymbol
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


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical S-integer power-residue symbols agree with the actual
local tame symbol in the CFT completion. The equality is derived by
injective reduction and the explicit completion/residue comparisons. -/
namespace ArtinMatthews.SIntegerTameSymbol

open NumberField IsDedekindDomain KummerTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory.Kummer
open GlobalClassFieldTheory.Reciprocity AlgebraicNumberTheory.PowerResidueSymbols
open ArtinMatthews.SIntegerPrincipalization ArtinMatthews.SIntegerQuotient
open ArtinMatthews.SIntegerAdicResidue ArtinMatthews.SIntegerResidueSymbol
open scoped NumberField Classical ValuativeRel
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))

def sourceArtinUnit (hP : P ∉ principalizingSet S₀) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) P]ˣ :=
  (artinIntegralOfSInteger_isUnit K S₀ P hP x hx).choose

theorem sourceArtinUnit_spec (hP : P ∉ principalizingSet S₀) (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    (sourceArtinUnit K S₀ P hP x hx : 𝒪[ChosenFinitePlaceBaseCompletion (K := K) P]) =
      artinIntegralOfSInteger K S₀ P hP x :=
  (artinIntegralOfSInteger_isUnit K S₀ P hP x hx).choose_spec

theorem sourceArtinUnit_residue (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    integerUnitsToResidueUnits (ChosenFinitePlaceBaseCompletion (K := K) P)
        (sourceArtinUnit K S₀ P hP x hx) =
      Units.map (finitePlacePrimeResidueEquivLocalResidue K P).toMonoidHom
        (sIntegerResidueUnit K S₀ P hP a ha x hx) := by
  apply Units.ext
  change IsLocalRing.residue 𝒪[ChosenFinitePlaceBaseCompletion (K := K) P]
    (sourceArtinUnit K S₀ P hP x hx : 𝒪[ChosenFinitePlaceBaseCompletion (K := K) P]) = _
  rw [sourceArtinUnit_spec]
  change artinResidueOfSInteger K S₀ P hP x = _
  rw [artinResidueOfSInteger_generator_compare K S₀ P hP a ha,
    artinResidueEquiv_eq_powerResidueEquiv]
  rfl

theorem residueUnit_tame_eq_symbol
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (hPN : P ∉ powerResidueExponentFinitePlaces K n)
    (u : ((𝓞 K) ⧸ P.asIdeal)ˣ)
    (v : 𝒪[ChosenFinitePlaceBaseCompletion (K := K) P]ˣ)
    (hv : integerUnitsToResidueUnits (ChosenFinitePlaceBaseCompletion (K := K) P) v =
      Units.map (finitePlacePrimeResidueEquivLocalResidue K P).toMonoidHom u) :
    localTamePowerResidueSymbol (ChosenFinitePlaceBaseCompletion (K := K) P) n
        (finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n P hPN)
        (finitePlaceHilbert_primitiveRoots_nonempty K n hmu P) v =
      nthRootsSubgroupMap K (ChosenFinitePlaceBaseCompletion (K := K) P) (n : ℕ)
        (integralRootsOfUnityToNthRoots K (n : ℕ) (powerResidueOnUnit K P n hmu hN u)) := by
  let C := ChosenFinitePlaceBaseCompletion (K := K) P
  let hnC := finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n P hPN
  let hmuC := finitePlaceHilbert_primitiveRoots_nonempty K n hmu P
  let z := powerResidueOnUnit K P n hmu hN u
  let e := finitePlacePrimeResidueEquivLocalResidue K P
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  let : Fintype 𝓀[C] := Fintype.ofFinite _
  have hnP : (n : ℕ) ∣ Fintype.card ((𝓞 K) ⧸ P.asIdeal) - 1 := by
    rw [card_primeIdealResidueField K P]
    exact dvd_absNorm_sub_one_of_primitiveRoots K P n hmu hN
  have hnL : (n : ℕ) ∣ Fintype.card 𝓀[C] - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact dvd_residueCard_sub_one_of_primitiveRoots C n hnC hmuC
  have hz : (rootsOfUnityReduction K P (n : ℕ) z).1 =
      (finiteFieldPowerResidueSymbol ((𝓞 K) ⧸ P.asIdeal) n hnP u).1 := by
    apply Units.ext
    change Ideal.Quotient.mk P.asIdeal (((z.1 : (𝓞 K)ˣ) : 𝓞 K)) = _
    rw [finiteFieldPowerResidueSymbol_apply, Units.val_pow_eq_pow_val]
    simpa only [card_primeIdealResidueField K P] using powerResidueOnUnit_reduce K P n hmu hN u
  apply localNthRootsReduction_injective C n hnC
  apply Subtype.ext
  have hl := congrArg (fun r : rootsOfUnity (n : ℕ) 𝓀[C] => r.1)
    (localNthRootsReductionEquiv_localTamePowerResidueSymbol C n hnC hmuC v)
  change (localNthRootsReduction C n _).1 = _ at hl
  calc
    _ = (finiteFieldPowerResidueSymbol 𝓀[C] n hnL (integerUnitsToResidueUnits C v)).1 := hl
    _ = (finiteFieldPowerResidueSymbol 𝓀[C] n hnL (Units.map e.toMonoidHom u)).1 :=
      congrArg (fun w : 𝓀[C]ˣ => (finiteFieldPowerResidueSymbol 𝓀[C] n hnL w).1) hv
    _ = Units.map e.toMonoidHom (finiteFieldPowerResidueSymbol ((𝓞 K) ⧸ P.asIdeal) n hnP u).1 :=
      (finiteFieldPowerResidueSymbol_unitsMap_ringEquiv e n hnP hnL u).symm
    _ = Units.map e.toMonoidHom (rootsOfUnityReduction K P (n : ℕ) z).1 := by rw [hz]
    _ = _ := (finitePlace_localNthRootsReduction_integralRoots K P n z).symm

attribute [local irreducible] sourceArtinUnit sIntegerResidueUnit

theorem sourceArtin_tame_eq_symbol (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hN : (Ideal.absNorm P.asIdeal).Coprime (n : ℕ))
    (hPN : P ∉ powerResidueExponentFinitePlaces K n)
    (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    localTamePowerResidueSymbol (ChosenFinitePlaceBaseCompletion (K := K) P) n
        (finitePlace_natCast_valuation_eq_one_of_not_mem_exponent K n P hPN)
        (finitePlaceHilbert_primitiveRoots_nonempty K n hmu P)
        (sourceArtinUnit K S₀ P hP x hx) =
      nthRootsSubgroupMap K (ChosenFinitePlaceBaseCompletion (K := K) P) (n : ℕ)
        (integralRootsOfUnityToNthRoots K (n : ℕ)
          (sIntegerPowerResidueSymbol K S₀ P hP a ha n hmu hN x hx)) := by
  have hv := sourceArtinUnit_residue K S₀ P hP a ha x hx
  exact residueUnit_tame_eq_symbol K P n hmu hN hPN
    (sIntegerResidueUnit K S₀ P hP a ha x hx) (sourceArtinUnit K S₀ P hP x hx) hv

end
end ArtinMatthews.SIntegerTameSymbol
