module

public import ArtinMatthews.SLocalSourceComplements
public import ArtinMatthews.SLocalIsotropicComplement
public import ArtinMatthews.SLocalSixthComplement
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

/-! Actual self-orthogonality of the S-unit image. It is deduced from
the constructed isotropic complement and the genuine nondegenerate
Hilbert pairing, never supplied as a maximality premise. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

theorem multiplicative_selfOrthogonal_of_isCompl
    {G T : Type*} [CommGroup G] [CommGroup T] (H : G →* (G →* T))
    (hNondeg : ∀ x, (∀ y, H x y = 1) → x = 1)
    (E B : Subgroup G) (hCompl : IsCompl E B)
    (hE : ∀ x ∈ E, ∀ y ∈ E, H x y = 1)
    (hB : ∀ x ∈ B, ∀ y ∈ B, H x y = 1) :
    ∀ x, (∀ y ∈ E, H x y = 1) ↔ x ∈ E := by
  intro x
  constructor
  · intro hx
    have hTop : E ⊔ B = ⊤ := codisjoint_iff.mp hCompl.codisjoint
    have hxTop : x ∈ E ⊔ B := by rw [hTop]; trivial
    obtain ⟨e, he, b, hb, heb⟩ := Subgroup.mem_sup.mp hxTop
    have hbE : ∀ y ∈ E, H b y = 1 := by
      intro y hy
      have h := hx y hy
      rw [← heb, map_mul, MonoidHom.mul_apply, hE e he y hy, one_mul] at h
      exact h
    have hbAll : ∀ y, H b y = 1 := by
      intro y
      have hyTop : y ∈ E ⊔ B := by rw [hTop]; trivial
      obtain ⟨e', he', b', hb', rfl⟩ := Subgroup.mem_sup.mp hyTop
      rw [map_mul, hbE e' he', hB b hb b' hb', one_mul]
    have hbOne := hNondeg b hbAll
    rw [← heb, hbOne, mul_one]
    exact he
  · intro hx y hy
    exact hE x hx y hy

variable (K : Type) [Field K] [NumberField K]

theorem source_sixth_unitImage_selfOrthogonal {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ x : SLocalPowerClasses K 6 (sourceHilbertSet K S₀),
      (∀ y ∈ sUnitPowerImage K 6 (sourceHilbertSet K S₀),
        sLocalHilbertForm K 6 (sLocalPrimitiveRoots K 6 (sourceHilbertRootSix_isPrimitive K hζ))
          (sourceHilbertSet K S₀) x y = 1) ↔ x ∈ sUnitPowerImage K 6 (sourceHilbertSet K S₀) := by
  let : NumberField.IsTotallyComplex K := source_isTotallyComplex K hζ
  obtain ⟨B, hC, hI⟩ := source_sixth_isotropic_complement K hζ S₀
  apply multiplicative_selfOrthogonal_of_isCompl _
    (sLocalHilbertForm_nondegenerate_left K 6 _ (sourceHilbertSet K S₀)) _ B hC _ hI
  exact sLocalHilbertForm_unitImage_isotropic K 6 (by norm_num) _ (sourceHilbertSet K S₀)
    (normSupport_exponent_subset K 6 _
      (normSupport_subset_sourceHilbertSet K S₀ 6 (Or.inr (Or.inr rfl))))

end
end ArtinMatthews
