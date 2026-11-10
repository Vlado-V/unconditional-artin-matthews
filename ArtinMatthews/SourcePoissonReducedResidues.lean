module

public import ArtinMatthews.SourcePoissonOriginalProbe
public import ArtinMatthews.SourceGeneratorPrefix
public import ArtinMatthews.SourceLocalUnits
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open SourceCRTNormalization VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "T" => sourceHilbertSeed F S₀
local notation "OS" => PrincipalIntegerRing T
local notation "a" => (sourcePrimeExponentGenerator F hζ S₀ : SourcePrimeExponents F S₀ → OS)
local notation "E" => SourcePrimeExponents F S₀

private theorem sourcePoissonResidueLocal_zero_of_mem (P : SourceExteriorPrime F S₀)
    (n : ℕ) (hn : 0 < n) (x : OS)
    (hx : x ∈ P.val.asIdeal.map (algebraMap (𝓞 F) OS)) :
    sourcePrimeExponentLocalWeight F hζ S₀ (reflectionPrimeCharacters F hζ S₀) P n x = 0 := by
  let b : OS := sourceAllowedPrimeGenerator F hζ S₀ P
  have hb : P.val.asIdeal.map (algebraMap (𝓞 F) OS) = Ideal.span {b} :=
    sourceAllowedPrimeGenerator_ideal F hζ S₀ P
  let χ := reflectionPrimeCharacters F hζ S₀ P
  let : Field ((𝓞 F) ⧸ P.val.asIdeal) := Ideal.Quotient.field _
  let : Nontrivial (OS ⧸ (Ideal.span {b} : Ideal OS)) :=
    (generatorResidueEquiv T P.val P.property b hb).toEquiv.nontrivial
  have hz : Ideal.Quotient.mk (Ideal.span {b} : Ideal OS) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hb ▸ hx)
  change generatorPowerWeight T P.val P.property b hb χ n
    ((Ideal.quotEquivOfEq (generator_power_ideal T P.val b hb n))
      (Ideal.Quotient.mk (primePowerIdeal T P.val n) x)) = 0
  have he := Ideal.quotEquivOfEq_mk (R := OS) (generator_power_ideal T P.val b hb n) x
  refine (congrArg (generatorPowerWeight T P.val P.property b hb χ n) he).trans ?_
  apply generatorPowerWeight_nonunit T P.val P.property b hb χ n hn
  intro h
  apply not_isUnit_zero (M₀ := OS ⧸ (Ideal.span {b} : Ideal OS))
  exact (generatorResidueReduction_mk T b n hn x).trans hz ▸ h

/-- A nonzero actual sextic residue value has a reduced residue class in the
whole literal quotient, including the unit modulus. -/
theorem sourcePoissonResidueValue_isUnit_of_ne_zero (e : E) (x : OS)
    (hx : reflectionExponentResidueValue F hζ S₀ e x ≠ 0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {a e} : Ideal OS) x) := by
  let P (i : e.support) := i.val.val
  let n (i : e.support) := e i.val
  let b (i : e.support) : OS := sourceAllowedPrimeGenerator F hζ S₀ i.val
  have hb (i : e.support) : (P i).asIdeal.map (algebraMap (𝓞 F) OS) = Ideal.span {b i} :=
    sourceAllowedPrimeGenerator_ideal F hζ S₀ i.val
  have hP : Pairwise fun i j : e.support => P i ≠ P j := by
    intro i j hij he
    exact hij (Subtype.ext (Subtype.ext he))
  have hI : crtModulus T P n = Ideal.span {a e} := by
    rw [crtModulus_generator T P n b hb]
    exact congrArg (fun x : OS => (Ideal.span {x} : Ideal OS))
      (sourcePrimeExponentGenerator_prefix F hζ S₀ e e.support le_rfl).symm
  let I : Ideal OS := Ideal.span {a e}
  let Q : Ideal OS := crtModulus T P n
  let u : (OS ⧸ I) ≃+* (OS ⧸ Q) := Ideal.quotEquivOfEq (R := OS) (show I = Q from hI.symm)
  let Ecrt := u.trans (primeCRTEquiv T P n hP)
  have hUnit : IsUnit (Ecrt (Ideal.Quotient.mk (Ideal.span {a e} : Ideal OS) x)) := by
    apply Pi.isUnit_iff.mpr
    intro i
    have hpos : 0 < n i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp i.property)
    have hi : x ∉ (P i).asIdeal.map (algebraMap (𝓞 F) OS) := by
      intro h
      apply hx
      unfold reflectionExponentResidueValue sourcePrimeExponentWeight Finsupp.prod
      exact Finset.prod_eq_zero i.property
        (sourcePoissonResidueLocal_zero_of_mem F S₀ hζ i.val (n i) hpos x h)
    have he : Ecrt (Ideal.Quotient.mk (Ideal.span {a e} : Ideal OS) x) i =
        Ideal.Quotient.mk (primePowerIdeal T (P i) (n i)) x := by
      have hu : u (Ideal.Quotient.mk I x) = Ideal.Quotient.mk Q x := rfl
      exact (congrArg (fun z : OS ⧸ Q => primeCRTEquiv T P n hP z i) hu).trans
        (primeCRTEquiv_mk T P n hP x i)
    rw [he]
    exact sourcePrimePower_isUnit T (P i) i.val.property (b i) (hb i) (n i) x hi
  have h := hUnit.map Ecrt.symm.toMonoidHom
  change IsUnit (Ecrt.symm (Ecrt (Ideal.Quotient.mk (Ideal.span {a e} : Ideal OS) x))) at h
  rw [Ecrt.symm_apply_apply] at h
  exact h

theorem sourcePoissonQuotientResidue_eq_zero_of_nonunit (e : E)
    (x : OS ⧸ (Ideal.span {a e} : Ideal OS)) (hx : ¬ IsUnit x) :
    sourcePoissonQuotientResidue F S₀ hζ e x = 0 := by
  by_contra hn
  have h : IsUnit (Ideal.Quotient.mk (Ideal.span {a e} : Ideal OS) (Quotient.out x)) :=
    sourcePoissonResidueValue_isUnit_of_ne_zero F S₀ hζ e (Quotient.out x) hn
  exact hx ((Ideal.Quotient.mk_out x) ▸ h)

end
end ArtinMatthews.SourceEulerAssembly
