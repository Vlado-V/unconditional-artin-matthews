module

public import ArtinMatthews.SixthExteriorPowerClasses
public import ArtinMatthews.KummerRowField
public import ArtinMatthews.KummerGeneralInertia
public import ArtinMatthews.KummerRowDegree
public import ArtinMatthews.VaryingKummerAnalyticRayFractionalDenominatorCount
public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! A genuine individual sixth-Kummer extension is unramified away
from six and the exterior support of its field-unit radicand. A local-unit
radicand is first written with a coprime integral denominator, so no global
integrality assumption is substituted for the actual valuation condition. -/
namespace ArtinMatthews
open IsDedekindDomain NumberField VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F] [Algebra F ℂ]

omit [Algebra F ℂ] in
theorem exists_coprime_fraction_of_exterior_zero (u : Fˣ)
    (p : HeightOneSpectrum (𝓞 F)) (hu : exteriorPrincipalValuation p u=0) :
    ∃ a b : 𝓞 F, a ≠ 0 ∧ b ≠ 0 ∧ a ∉ p.asIdeal ∧ b ∉ p.asIdeal ∧
      (u:F)=(a:F)/(b:F) := by
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ p.asIdeal →
      FractionalIdeal.count F v (FractionalIdeal.spanSingleton (𝓞 F)⁰ (u:F))=0 := by
    intro v hv
    have has : Associated v.asIdeal p.asIdeal :=
      Irreducible.associated_of_dvd v.irreducible p.irreducible hv
    have hId : v.asIdeal=p.asIdeal := associated_iff_eq.mp has
    have hvp : v=p := HeightOneSpectrum.ext hId
    subst v
    simpa only [exteriorPrincipalValuation,coe_toPrincipalIdeal] using hu
  obtain ⟨a,b,ha,hb,hac,hbc,hab⟩ :=
    exists_coprime_integral_fraction_of_counts F p.asIdeal p.ne_bot u hc
  refine ⟨a,b,ha,hb,?_,?_,hab⟩
  · intro h
    exact p.prime.not_isUnit (hac.isUnit_of_dvd'
      (Ideal.dvd_span_singleton.mpr h) (dvd_refl _))
  · intro h
    exact p.prime.not_isUnit (hbc.isUnit_of_dvd'
      (Ideal.dvd_span_singleton.mpr h) (dvd_refl _))

omit [NumberField F] in
theorem sixthKummerIndividual_aut_eq_one_of_fix_root {ζ : F}
    (hζ : IsPrimitiveRoot ζ 6) (a : F) (ha : a ≠ 0)
    (σ : Gal(sixthKummerRowField {a}/F))
    (hσ : σ (sixthKummerRowRoot {a} a (Finset.mem_singleton_self a))=
      sixthKummerRowRoot {a} a (Finset.mem_singleton_self a)) : σ=1 := by
  have hA : ∀ b ∈ ({a} : Finset F), b ≠ 0 := by simpa using ha
  apply sixthKummerRowRootsMap_injective hζ {a} hA
  funext b
  rcases b with ⟨b,hb⟩
  have he : b=a := Finset.mem_singleton.mp hb
  subst b
  apply Subtype.ext
  apply Units.ext
  change σ (sixthKummerRowRoot {a} a hb) / sixthKummerRowRoot {a} a hb=
    (1 : Gal(sixthKummerRowField {a}/F)) (sixthKummerRowRoot {a} a hb) /
      sixthKummerRowRoot {a} a hb
  rw [hσ]
  rfl

theorem sixthKummerIndividual_inertia_eq_bot {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (u : Fˣ) (p : HeightOneSpectrum (𝓞 F))
    (h6 : (6 : 𝓞 F) ∉ p.asIdeal) (hu : exteriorPrincipalValuation p u=0)
    (Q : Ideal (𝓞 (sixthKummerRowField {(u:F)}))) [Q.IsMaximal]
    (hQ : Q.under (𝓞 F)=p.asIdeal) :
    Q.inertia Gal(sixthKummerRowField {(u:F)}/F)=⊥ := by
  let L := sixthKummerRowField {(u:F)}
  let α : L := sixthKummerRowRoot {(u:F)} (u:F) (Finset.mem_singleton_self _)
  obtain ⟨a,b,ha,hb,haP,hbP,hab⟩ := exists_coprime_fraction_of_exterior_zero u p hu
  have hbF : (b:F) ≠ 0 := by exact_mod_cast hb
  let y : L := algebraMap F L (b:F)*α
  have hyPow : y^6=algebraMap F L ((a:F)*(b:F)^5) := by
    dsimp only [y]
    rw [mul_pow,show α^6=algebraMap F L (u:F) from sixthKummerRowRoot_pow _ _ _,
      ← map_pow,← map_mul]
    apply congrArg (algebraMap F L)
    rw [hab]
    field_simp
  have hyInt : IsIntegral ℤ y := by
    apply IsIntegral.of_pow (by decide : 0 < 6)
    rw [hyPow]
    exact ((a*b^5).isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F L)
  let r : 𝓞 L := ⟨y,hyInt⟩
  have hr : r^6=algebraMap (𝓞 F) (𝓞 L) (a*b^5) := by
    apply Subtype.ext
    exact hyPow
  have haB : a*b^5 ∉ p.asIdeal :=
    p.asIdeal.primeCompl.mul_mem haP (p.asIdeal.primeCompl.pow_mem hbP 5)
  have hrQ : algebraMap (𝓞 F) (𝓞 L) (a*b^5) ∉ Q := by
    intro h
    have hh : a*b^5 ∈ Q.under (𝓞 F) := h
    exact haB (hQ ▸ hh)
  have h6Q : (6 : 𝓞 L) ∉ Q := by
    intro h
    have hmap : algebraMap (𝓞 F) (𝓞 L) 6 ∈ Q := by
      convert h using 1
      exact map_natCast (algebraMap (𝓞 F) (𝓞 L)) 6
    have hh : (6 : 𝓞 F) ∈ Q.under (𝓞 F) := hmap
    exact h6 (hQ ▸ hh)
  apply le_antisymm ?_ bot_le
  intro σ hσ
  change σ=1
  apply sixthKummerIndividual_aut_eq_one_of_fix_root hζ (u:F) u.ne_zero
  have hrfix := inertia_fixes_integral_base_powerRoot (by decide : 0 < 6)
    Q h6Q (a*b^5) hrQ r hr σ hσ
  have hyfix : σ y=y := congrArg (fun z : 𝓞 L => (z:L)) hrfix
  dsimp only [y] at hyfix
  rw [map_mul,σ.commutes] at hyfix
  have hbL : algebraMap F L (b:F) ≠ 0 := by
    simpa only [map_zero] using (algebraMap F L).injective.ne hbF
  exact mul_left_cancel₀ hbL hyfix

theorem sixthKummerIndividual_unramifiedAt {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (u : Fˣ) (p : HeightOneSpectrum (𝓞 F))
    (h6 : (6 : 𝓞 F) ∉ p.asIdeal) (hu : exteriorPrincipalValuation p u=0)
    (Q : Ideal (𝓞 (sixthKummerRowField {(u:F)}))) [Q.IsMaximal]
    (hQ : Q.under (𝓞 F)=p.asIdeal) : Algebra.IsUnramifiedAt (𝓞 F) Q := by
  have h := Ideal.card_inertia_eq_ramificationIdxIn
    (G := Gal(sixthKummerRowField {(u:F)}/F)) (Q.under (𝓞 F)) Q
  rw [sixthKummerIndividual_inertia_eq_bot hζ u p h6 hu Q hQ,Nat.card_unique,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Q.under (𝓞 F)) Q
      Gal(sixthKummerRowField {(u:F)}/F)] at h
  exact Ideal.ramificationIdx_eq_one_iff.mp h.symm

end
end ArtinMatthews
