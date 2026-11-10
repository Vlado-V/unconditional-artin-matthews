module

public import ArtinMatthews.AllowedGeneratorBase
public import ArtinMatthews.SIntegerPrincipalExterior
public import ArtinMatthews.SLocalPaperHilbertNormalization
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

/-! Genuine allowed generators of every fractional ideal of the actual
principal S-integer ring. Two allowed generators of the same ideal
differ by an actual sixth power of an actual S-unit. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain FractionalIdeal KummerTheory SIntegerPrincipalization
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

private theorem exists_adjustment {A C : Type*} [CommGroup A] [Group C]
    (U : Subgroup A) (f : A →* C) (hf : Function.Surjective f) (B : Subgroup C)
    (hc : IsCompl ((f.comp U.subtype).range) B) (a : A) :
    ∃ u : U, f ((u : A)⁻¹ * a) ∈ B := by
  let : IsMulCommutative C := ⟨⟨fun x y => by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← map_mul, ← map_mul, mul_comm a b]⟩⟩
  have hTop : (f.comp U.subtype).range ⊔ B = ⊤ := codisjoint_iff.mp hc.codisjoint
  have hmem : f a ∈ (f.comp U.subtype).range ⊔ B := by rw [hTop]; trivial
  obtain ⟨e, he, b, hb, heb⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  obtain ⟨u, hu⟩ := he
  change f (u : A) = e at hu
  refine ⟨u, ?_⟩
  rw [map_mul, map_inv, hu, ← heb, inv_mul_cancel_left]
  exact hb

theorem exists_allowed_generator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    ∃ a : Kˣ, toPrincipalIdeal (sourceRing K S₀) K a = I ∧ a ∈ allowedSubgroup K hζ S₀ := by
  obtain ⟨a₀, ha₀⟩ := exists_fractional_field_generator (sourceHilbertSeed K S₀) I
  obtain ⟨u, hu⟩ := exists_adjustment
    (SUnitGroup (K := K) (sourceHilbertSet K S₀))
    (sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀))
    (source_ring_globalClassMap_surjective K hζ (sourceHilbertSet K S₀))
    (chosenB K hζ S₀) (chosenB_isCompl K hζ S₀) a₀
  refine ⟨(u : Kˣ)⁻¹ * a₀, ?_, hu⟩
  rw [map_mul, map_inv, sUnit_principal_eq_one K S₀ u, inv_one, one_mul]
  exact ha₀

theorem allowed_ratio_sixth {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (a b : Kˣ)
    (ha : a ∈ allowedSubgroup K hζ S₀) (hb : b ∈ allowedSubgroup K hζ S₀)
    (hI : toPrincipalIdeal (sourceRing K S₀) K a = toPrincipalIdeal (sourceRing K S₀) K b) :
    ∃ t : SUnitGroup (K := K) (sourceHilbertSet K S₀), a / b = (t : Kˣ) ^ 6 := by
  have hu := (principal_eq_iff_ratio_sUnit K S₀ a b).mp hI
  let u : SUnitGroup (K := K) (sourceHilbertSet K S₀) := ⟨a / b, hu⟩
  let f := sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀)
  have hB : f (a / b) ∈ chosenB K hζ S₀ := by
    change f a ∈ chosenB K hζ S₀ at ha
    change f b ∈ chosenB K hζ S₀ at hb
    rw [map_div]
    exact (chosenB K hζ S₀).div_mem ha hb
  have hE : f (a / b) ∈ sLocalRingUnitImage K 6 (sourceHilbertSet K S₀) := ⟨u, rfl⟩
  have hzero : f (a / b) = 1 :=
    Subgroup.disjoint_def.mp (chosenB_isCompl K hζ S₀).disjoint hE hB
  have hq : QuotientGroup.mk'
      (powMonoidHom ((6 : ℕ+) : ℕ) : SUnitGroup (K := K) (sourceHilbertSet K S₀) →*
        SUnitGroup (K := K) (sourceHilbertSet K S₀)).range u = 1 := by
    apply source_ring_sixth_unitPowerClassMap_injective K hζ S₀
    exact (sLocalRingUnitPowerClassMap_mk K 6 (sourceHilbertSet K S₀) u).trans
      (hzero.trans ((map_one (sLocalRingUnitPowerClassMap K 6 (sourceHilbertSet K S₀))).symm))
  obtain ⟨t, ht⟩ := (QuotientGroup.eq_one_iff u).mp hq
  refine ⟨t, ?_⟩
  have h := congrArg
    (fun v : SUnitGroup (K := K) (sourceHilbertSet K S₀) => (v : Kˣ)) ht
  change (t : Kˣ) ^ 6 = a / b at h
  exact h.symm

def generator {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) : Kˣ :=
  (exists_allowed_generator K hζ S₀ I).choose

theorem generator_principal {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    toPrincipalIdeal (sourceRing K S₀) K (generator K hζ S₀ I) = I :=
  (exists_allowed_generator K hζ S₀ I).choose_spec.1

theorem generator_allowed {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : idealGroup K S₀) :
    generator K hζ S₀ I ∈ allowedSubgroup K hζ S₀ :=
  (exists_allowed_generator K hζ S₀ I).choose_spec.2

theorem generator_mul_ratio_sixth {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I J : idealGroup K S₀) :
    ∃ t : SUnitGroup (K := K) (sourceHilbertSet K S₀),
      generator K hζ S₀ (I * J) /
        (generator K hζ S₀ I * generator K hζ S₀ J) = (t : Kˣ) ^ 6 := by
  apply allowed_ratio_sixth K hζ S₀ _ _ (generator_allowed K hζ S₀ _)
    ((allowedSubgroup K hζ S₀).mul_mem (generator_allowed K hζ S₀ I) (generator_allowed K hζ S₀ J))
  rw [map_mul, generator_principal, generator_principal, generator_principal]

theorem generator_one_sixth {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ t : SUnitGroup (K := K) (sourceHilbertSet K S₀), generator K hζ S₀ 1 = (t : Kˣ) ^ 6 := by
  obtain ⟨t, ht⟩ := allowed_ratio_sixth K hζ S₀ (generator K hζ S₀ 1) 1
    (generator_allowed K hζ S₀ 1) (allowedSubgroup K hζ S₀).one_mem
    (by rw [generator_principal, map_one])
  exact ⟨t, by simpa only [_root_.div_one] using ht⟩

end
end ArtinMatthews.AllowedGenerators
