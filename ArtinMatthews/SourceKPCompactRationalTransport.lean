module

public import ArtinMatthews.SourceKPCompactCoreCharts
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

/-! The exact rational relation between upper-coordinate representatives of the true cover quotient. -/
namespace ArtinMatthews
open NumberField Matrix MulOpposite
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactUpperRepresentative_exists (p : SourceKPArchUpperHalfSpace K) :
    ∃ a : PGL(2, InfiniteAdeleRing K),
      sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a) = p := by
  obtain ⟨a,ha⟩ := QuotientGroup.mk_surjective ((sourceKPArchSymmetricHomeomorph K hζ).symm p)
  refine ⟨a,?_⟩
  rw [ha,Homeomorph.apply_symm_apply]

theorem sourceKPUpperToCompact_mk (b : SourceKPFiniteLevelFiber K hζ)
    (a : PGL(2, InfiniteAdeleRing K)) :
    sourceKPUpperToCompact K hζ b (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a)) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPArchComponentPoint K hζ b a) :=
  sourceKPArithmeticUpperComponentHomeomorph_mk K hζ b a

theorem sourceKPUpperToCompact_rational (γ : PGL(2, K)) (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K) :
    sourceKPUpperToCompact K hζ (γ • b)
      (sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ) p) =
        sourceKPUpperToCompact K hζ b p := by
  obtain ⟨a,rfl⟩ := sourceKPCompactUpperRepresentative_exists K hζ p
  rw [← sourceKPArchSymmetricHomeomorph_smul]
  change sourceKPUpperToCompact K hζ (γ • b)
      (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk (sourceKPRationalArchMap K hζ γ * a))) = _
  rw [sourceKPUpperToCompact_mk,sourceKPUpperToCompact_mk]
  apply congrArg (sourceKPAutomorphicCompactMk K hζ)
  apply Quotient.sound
  exact MulAction.mem_orbit_iff.mpr ⟨γ,rfl⟩

theorem sourceKPUpperToCompact_eq_iff_rational (b c : SourceKPFiniteLevelFiber K hζ)
    (p q : SourceKPArchUpperHalfSpace K) :
    sourceKPUpperToCompact K hζ b p = sourceKPUpperToCompact K hζ c q ↔
      ∃ γ : PGL(2, K), γ • c = b ∧
        sourceKPArchUpperAction K hζ (sourceKPRationalArchMap K hζ γ) q = p := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := sourceKPCompactUpperRepresentative_exists K hζ p
    obtain ⟨d,hd⟩ := sourceKPCompactUpperRepresentative_exists K hζ q
    rw [← ha,← hd,sourceKPUpperToCompact_mk,sourceKPUpperToCompact_mk] at h
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
    have hk' : sourceKPArchComponentPoint K hζ c (d * unop k.val) =
        sourceKPArchComponentPoint K hζ b a := hk
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact hk'.symm)
    have hfin : γ • c = b := congrArg Prod.snd hγ
    have harch : sourceKPRationalArchMap K hζ γ * (d * unop k.val) = a := congrArg Prod.fst hγ
    refine ⟨γ,hfin,?_⟩
    rw [← ha,← hd,← sourceKPArchSymmetricHomeomorph_smul]
    change sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk (sourceKPRationalArchMap K hζ γ * d)) =
      sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a)
    apply congrArg (sourceKPArchSymmetricHomeomorph K hζ)
    have hmem : unop k.val ∈ sourceKPArchBaseCompactSubgroup K hζ := k.prop
    rw [← harch,← mul_assoc,QuotientGroup.mk_mul_of_mem _ hmem]
  · rintro ⟨γ,hfin,harch⟩
    simpa only [hfin,harch] using sourceKPUpperToCompact_rational K hζ γ c q

end
end ArtinMatthews
