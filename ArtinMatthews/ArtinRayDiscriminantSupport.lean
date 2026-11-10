module

public import ArtinMatthews.ArtinFrobeniusIdealCharacter
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
public import ArtinMatthews.ArtinFrobeniusConductorSupport
public import ArtinMatthews.ArtinRayConductor
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual norm-defining modulus is supported above the absolute
discriminant. This assertion controls support without bounding its depths. -/
noncomputable section
open scoped NumberField Classical
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open GlobalClassFieldTheory.GlobalClassFields
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem normDefiningModulus_support_discriminant_mem
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hv : v ∈ (ideleClassNormDefiningModulus (K := K) (L := L)).support) :
    ((NumberField.discr L).natAbs : 𝓞 K) ∈ v.asIdeal := by
  by_contra hD
  let W := finitePlaceExtensionCentre (K := K) (L := L) v
    (chosenFinitePlaceExtension (L := L) v)
  have hW : W.asIdeal.LiesOver v.asIdeal :=
    finitePlaceExtensionCentre_liesOver v (chosenFinitePlaceExtension (L := L) v)
  have hur : Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal :=
    unramified_of_absDiscr_not_mem K L v.asIdeal W.asIdeal hW.over.symm hD
  have hz := ideleClassNormLocalHigherUnitExponent_eq_zero_of_chosenUnramified
    (K := K) (L := L) v (chosenFinitePlaceIsUnramified_of_isUnramifiedAt v hur)
  exact (Finsupp.mem_support_iff.mp hv)
    ((ideleClassNormDefiningModulus_apply v).trans hz)

/-- An actual Artin modulus can exclude every discriminant prime while
remaining supported only at discriminant primes. Its exponents need not be
estimated for the power-correction argument. -/
theorem exists_discriminant_supported_artin_modulus
    [NumberField.IsTotallyComplex K] :
    ∃ m : RayClass.Modulus K, m.infinitePart = ∅ ∧
      m.congruenceSubgroup ≤ (ideleClassNorm K L).range ∧
      (∀ v ∈ m.finitePart.support,
        ((NumberField.discr L).natAbs : 𝓞 K) ∈ v.asIdeal) ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v ∉ m.finitePart.support →
        Algebra.IsUnramifiedAt (𝓞 K) (GaloisIdealCharacter.primeAbove K L v).val := by
  let m := RayClass.Modulus.narrowOfFinite
    (ideleClassNormDefiningModulus (K := K) (L := L))
  have hnorm : m.congruenceSubgroup ≤ (ideleClassNorm K L).range :=
    ideleClassNormDefiningModulus_isDefiningModulus (K := K) (L := L)
  let D : 𝓞 K := (NumberField.discr L).natAbs
  have hD : D ≠ 0 := by
    change ((NumberField.discr L).natAbs : 𝓞 K) ≠ 0
    exact_mod_cast (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)).ne'
  let I := integralIdealFractionalUnit (Ideal.span {D})
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hD)
  let b : RayClass.FiniteModulus K :=
    (FractionalIdealGroup.countVector I).mapRange Int.natAbs rfl
  let m' := m.replaceFinitePart (m.finitePart + b)
  have hle : m ≤ m' := by
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · exact Finset.Subset.refl _
  refine ⟨m',modulus_infinitePart_eq_empty m',
    (RayClass.Modulus.congruenceSubgroup_antitone hle).trans hnorm,?_,?_⟩
  · intro v hv
    by_cases hv0 : v ∈ m.finitePart.support
    · exact normDefiningModulus_support_discriminant_mem v hv0
    have hm0 : m.finitePart v = 0 := Finsupp.notMem_support_iff.mp hv0
    have hb : b v ≠ 0 := by
      have h := Finsupp.mem_support_iff.mp hv
      change m.finitePart v + b v ≠ 0 at h
      simpa only [hm0, zero_add] using h
    have hc : FractionalIdeal.count K v (Ideal.span {D}) ≠ 0 := by
      intro h
      apply hb
      change Int.natAbs (FractionalIdeal.count K v (Ideal.span {D})) = 0
      rw [h, Int.natAbs_zero]
    exact (principal_count_ne_zero_iff_mem K D hD v).mp hc
  · intro v hv
    have hv0 : m'.finitePart v = 0 := Finsupp.notMem_support_iff.mp hv
    have hb : b v = 0 := by
      change m.finitePart v + b v = 0 at hv0
      omega
    have hc : FractionalIdeal.count K v (Ideal.span {D}) = 0 :=
      Int.natAbs_eq_zero.mp hb
    have hnot : D ∉ v.asIdeal :=
      mt ((principal_count_ne_zero_iff_mem K D hD v).mpr) (by simpa using hc)
    let Q := GaloisIdealCharacter.primeAbove K L v
    let : Q.val.IsPrime := Q.property.1
    exact unramified_of_absDiscr_not_mem K L v.asIdeal Q.val Q.property.2.over.symm hnot

end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
end
