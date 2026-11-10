module

public import ArtinMatthews.SourceKPCuspPrincipalQuotient
public import ArtinMatthews.SourceKPFiniteLevelDescent
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

/-! The principal cusp torus maps to the original automorphic finite level.
    Its scalar period is extracted from the actual conjugated stabilizer. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free Matrix Topology
open scoped NumberField MatrixGroups AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

lemma sourceKPAdelicDeepCompactFinite_mem (k : sourceKPAdelicDeepCompactMatrix K hζ) :
    sourceKPAdelicDeepCompactFinite K hζ k ∈ sourceKPFiniteDeepMatrixGroup K := by
  apply (sourceKPFiniteDeepMatrixGroup_mem K _).mpr
  exact ⟨fun P => k.property.1.1 P, fun P hP => k.property.2 P hP⟩

lemma sourceKPAdelicDeepCompact_finite_lift
    (z : SourceKPAdelicProjective K hζ) (hz : z ∈ sourceKPAdelicDeepCompact K hζ)
    (harch : z.1 = 1) :
    ∃ k : sourceKPFiniteDeepMatrixGroup K, z = sourceKPFiniteDeepCoverLift K hζ k := by
  obtain ⟨k, rfl⟩ := hz
  let t : sourceKPFiniteDeepMatrixGroup K :=
    ⟨sourceKPAdelicDeepCompactFinite K hζ k, sourceKPAdelicDeepCompactFinite_mem K hζ k⟩
  refine ⟨t, Prod.ext ?_ ?_⟩
  · rw [sourceKPFiniteDeepCoverLift_fst]
    exact harch
  · rw [sourceKPFiniteDeepCoverLift_eq]
    change sourceKPFiniteAdeleProjectiveLift K hζ (sourceKPAdelicDeepCompactFinite K hζ k) =
      sourceKPFiniteAdeleProjectiveLift K hζ
        ((sourceKPGL2ProductEquiv K (sourceKPFiniteMatrixEmbedding K t.val)).2)
    rw [sourceKPFiniteMatrixEmbedding_product]

lemma sourceKPAdelicUpperLift_finite_fst (t : 𝔸ᶠ[K]) :
    (sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t)).1 = 1 := by
  change ProjGenLinGroup.mk (sourceKPUpperMatrix (InfiniteAdeleRing K) 0) = 1
  rw [sourceKPUpperMatrix_zero, map_one]

lemma sourceKPAdelicCuspFiniteLevelPeriod (g : SourceKPAdelicProjective K hζ) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ t ∈ sourceKPCuspFiniteIdeal K d,
      ∃ k : sourceKPFiniteDeepMatrixGroup K,
        g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * g =
          sourceKPFiniteDeepCoverLift K hζ k := by
  obtain ⟨d, hd, hperiod⟩ := sourceKPAdelicCuspPeriod K hζ g
  refine ⟨d, hd, ?_⟩
  intro t ht
  obtain ⟨x, rfl⟩ := (sourceKPCuspFiniteIdeal_mem K d t).mp ht
  apply sourceKPAdelicDeepCompact_finite_lift K hζ
  · exact hperiod x
  · change g.1⁻¹ * (sourceKPAdelicUpperLift K hζ
      (sourceKPFiniteAddEmbedding K (algebraMap K 𝔸ᶠ[K] (d : K) * x.val))).1 * g.1 = 1
    rw [sourceKPAdelicUpperLift_finite_fst]
    group

def sourceKPCuspOrbit (g : SourceKPAdelicProjective K hζ) (a : 𝔸[K]) :
    SourceKPAutomorphicLevel K hζ :=
  sourceKPAutomorphicLevelMk K hζ (sourceKPAdelicUpperLift K hζ a * g)

lemma sourceKPCuspOrbit_rational (g : SourceKPAdelicProjective K hζ) (a : 𝔸[K]) (q : K) :
    sourceKPCuspOrbit K hζ g (a + algebraMap K 𝔸[K] q) = sourceKPCuspOrbit K hζ g a := by
  apply (sourceKPAutomorphicLevelMk_eq_iff K hζ _ _).mpr
  refine ⟨sourcePGL2Upper q, 1, ?_⟩
  rw [map_one, mul_one, ← sourceKPAdelicUpperLift_rational, ← mul_assoc,
    ← sourceKPAdelicUpperLift_add, add_comm a]

variable (d : 𝓞 K) (g : SourceKPAdelicProjective K hζ)
variable (hperiod : ∀ t ∈ sourceKPCuspFiniteIdeal K d,
  ∃ k : sourceKPFiniteDeepMatrixGroup K,
    g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * g =
      sourceKPFiniteDeepCoverLift K hζ k)
include hperiod

lemma sourceKPCuspOrbit_finite (a : 𝔸[K]) (t : 𝔸ᶠ[K]) (ht : t ∈ sourceKPCuspFiniteIdeal K d) :
    sourceKPCuspOrbit K hζ g (a + sourceKPFiniteAddEmbedding K t) = sourceKPCuspOrbit K hζ g a := by
  obtain ⟨k, hk⟩ := hperiod t ht
  apply (sourceKPAutomorphicLevelMk_eq_iff K hζ _ _).mpr
  refine ⟨1, k, ?_⟩
  rw [map_one, one_mul, ← hk, sourceKPAdelicUpperLift_add]
  group

lemma sourceKPCuspOrbit_period (a h : 𝔸[K]) (hh : h ∈ sourceKPCuspPrincipalPeriods K d) :
    sourceKPCuspOrbit K hζ g (h + a) = sourceKPCuspOrbit K hζ g a := by
  obtain ⟨r, ⟨q, rfl⟩, f, ⟨t, ht, rfl⟩, rfl⟩ := AddSubgroup.mem_sup.mp hh
  change sourceKPCuspOrbit K hζ g (algebraMap K 𝔸[K] q + sourceKPFiniteAddEmbedding K t + a) = _
  rw [show (algebraMap K 𝔸[K]) q + sourceKPFiniteAddEmbedding K t + a =
    (a + sourceKPFiniteAddEmbedding K t) + algebraMap K 𝔸[K] q by abel]
  rw [sourceKPCuspOrbit_rational, sourceKPCuspOrbit_finite K hζ d g hperiod a t ht]

def sourceKPCuspLevelCover : SourceKPCuspPrincipalQuotient K d → SourceKPAutomorphicLevel K hζ :=
  Quotient.lift (sourceKPCuspOrbit K hζ g) (by
    intro a b hab
    have hh : -a + b ∈ sourceKPCuspPrincipalPeriods K d := QuotientAddGroup.leftRel_apply.mp hab
    have he := sourceKPCuspOrbit_period K hζ d g hperiod a (-a+b) hh
    have heq : -a + b + a = b := by abel
    simpa only [heq] using he.symm)

lemma sourceKPCuspLevelCover_mk (a : 𝔸[K]) :
    sourceKPCuspLevelCover K hζ d g hperiod (QuotientAddGroup.mk a) =
      sourceKPAutomorphicLevelMk K hζ (sourceKPAdelicUpperLift K hζ a * g) := rfl

end
end ArtinMatthews
