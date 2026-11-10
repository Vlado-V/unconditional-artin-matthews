module

public import ArtinMatthews.SourceCoordinateIntertwinerProduct
public import ArtinMatthews.SourceKPLocalRestCommute
public import ArtinMatthews.SourceKPProjectiveIwasawa
public import ArtinMatthews.SourceKPLocalRestBase
public import ArtinMatthews.SourceKPTameCompactEmbedding
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

namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K)) (h6 : (6 : 𝓞 K) ∉ P.asIdeal)

def sourceKPFiniteCompactRemove (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) : SourceKPAdelicProjective K hζ :=
  (1, g) * (sourceKPAdelicLocalProjective K hζ P
    (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k))⁻¹

theorem sourceKPFiniteCompactRemove_arch (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) :
    (sourceKPFiniteCompactRemove K hζ P h6 g k).1 = 1 := by
  change (1 : PGL(2, InfiniteAdeleRing K)) * 1⁻¹ = 1
  simp

theorem sourceKPFiniteCompactRemove_eq_pair (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) :
    sourceKPFiniteCompactRemove K hζ P h6 g k =
      (1, (sourceKPFiniteCompactRemove K hζ P h6 g k).2) :=
  Prod.ext (sourceKPFiniteCompactRemove_arch K hζ P h6 g k) rfl

theorem sourceKPFiniteCompactRemove_restore (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) :
    sourceKPFiniteCompactRemove K hζ P h6 g k * sourceKPAdelicLocalProjective K hζ P
      (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k) = (1, g) := by
  unfold sourceKPFiniteCompactRemove
  exact inv_mul_cancel_right _ _

theorem sourceKPAdelicLocalBase_finite_representative (a : SourceKPFiniteAdeleCover K hζ) :
    sourceKPAdelicLocalBase K hζ P (1, sourceKPFiniteAdeleProjectiveMk K hζ a) =
      ProjGenLinGroup.mk (sourceKPAdeleMatrixAt K P a.base) := by
  change ProjGenLinGroup.map (sourceKPAdeleEval K P) (ProjGenLinGroup.mk a.base) = _
  rw [ProjGenLinGroup.map_mk]
  rfl

theorem sourceKPFiniteCompactRemove_base (a : SourceKPFiniteAdeleCover K hζ)
    (k : SourceFiniteKP2Integral K P) (hk : k.val = sourceKPAdeleMatrixAt K P a.base) :
    sourceKPAdelicLocalBase K hζ P
      (sourceKPFiniteCompactRemove K hζ P h6 (sourceKPFiniteAdeleProjectiveMk K hζ a) k) = 1 := by
  rw [sourceKPFiniteCompactRemove, map_mul, map_inv,
    sourceKPAdelicLocalBase_finite_representative, sourceKPAdelicLocalBase_local]
  change ProjGenLinGroup.mk (sourceKPAdeleMatrixAt K P a.base) *
    (ProjGenLinGroup.mk k.val)⁻¹ = 1
  rw [← hk, mul_inv_cancel]

theorem sourceKPFiniteCompactRemove_scalar (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) (z : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicCompactScalar K hζ s (z * (1, g)) =
      sourceKPAdelicCompactScalar K hζ s (z * sourceKPFiniteCompactRemove K hζ P h6 g k) := by
  have h := congrArg (fun v : SourceKPAdelicTorusInducedSpace K hζ s => v.val 1)
    (sourceKPAdelicCompactSection_right_local K hζ P h6 s
      (z * sourceKPFiniteCompactRemove K hζ P h6 g k) k)
  change sourceKPAdelicCompactScalar K hζ s
      ((z * sourceKPFiniteCompactRemove K hζ P h6 g k) *
        sourceKPAdelicLocalProjective K hζ P
          (sourceFiniteKP2ProjectiveCompactSection K hζ P h6 k)) =
    sourceKPAdelicCompactScalar K hζ s (z * sourceKPFiniteCompactRemove K hζ P h6 g k) at h
  rw [mul_assoc, sourceKPFiniteCompactRemove_restore] at h
  exact h

theorem sourceKPFiniteCompactRemove_kernel (s : ℂ) (g : SourceKPFiniteAdeleProjective K hζ)
    (k : SourceFiniteKP2Integral K P) (x : 𝔸ᶠ[K]) :
    sourceKPFiniteIntertwiningKernel K hζ s g x =
      sourceKPFiniteIntertwiningKernel K hζ s (sourceKPFiniteCompactRemove K hζ P h6 g k).2 x := by
  have h := sourceKPFiniteCompactRemove_scalar K hζ P h6 s g k
    (1, (sourceKPAdelicProjectiveWeyl K hζ).2 * sourceKPFiniteAdeleUpperLift K hζ x)
  rw [sourceKPFiniteCompactRemove_eq_pair] at h
  simpa only [sourceKPFiniteIntertwiningKernel, Prod.mk_mul_mk, one_mul] using h

theorem sourceKPFiniteCompactRemove_coordinate_kernel (s : ℂ)
    (g t : SourceKPFiniteAdeleProjective K hζ) (k : SourceFiniteKP2Integral K P) (x : 𝔸ᶠ[K]) :
    sourceKPFiniteCoordinateIntertwiningKernel K hζ s g t x =
      sourceKPFiniteCoordinateIntertwiningKernel K hζ s
        (sourceKPFiniteCompactRemove K hζ P h6 g k).2 t x := by
  have h := sourceKPFiniteCompactRemove_scalar K hζ P h6 s g k
    (1, t * ((sourceKPAdelicProjectiveWeyl K hζ).2 * sourceKPFiniteAdeleUpperLift K hζ x))
  rw [sourceKPFiniteCompactRemove_eq_pair] at h
  simpa only [sourceKPFiniteCoordinateIntertwiningKernel, Prod.mk_mul_mk, one_mul, mul_assoc] using h

end
end ArtinMatthews
