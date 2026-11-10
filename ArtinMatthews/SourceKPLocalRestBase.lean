module

public import ArtinMatthews.SourceKPLocalRestCommute
public import ArtinMatthews.SourceKPAdelicWeyl
public import ArtinMatthews.SourceKPAdelicUpper
public import ArtinMatthews.SourceKubotaGL2Generation
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

/-! Exact local projective components of the actual adelic upper and
Weyl lifts identify the remaining factor in a local integration fiber. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

theorem sourceKPAdelicLocalBase_local (g : SourceFiniteKP2Projective K hζ P) :
    sourceKPAdelicLocalBase K hζ P (sourceKPAdelicLocalProjective K hζ P g) =
      sourceFiniteKP2ProjectiveProjection K hζ P g := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (sourceFiniteKP2Scalar K hζ P).range g
  change ProjGenLinGroup.mk (sourceKPAdeleMatrixAt K P
      (sourceKPAdeleSingleMatrix K P a.base)) = ProjGenLinGroup.mk a.base
  rw [sourceKPAdeleSingleMatrix_same]

theorem sourceKPAdelicLocalBase_upper (x : 𝔸[K]) :
    sourceKPAdelicLocalBase K hζ P (sourceKPAdelicUpperLift K hζ x) =
      ProjGenLinGroup.mk (sourceGL2Upper (x.2 P)) := by
  change ProjGenLinGroup.mk (GeneralLinearGroup.map (sourceKPAdeleEval K P)
    (sourceKPUpperMatrix 𝔸ᶠ[K] x.2)) = _
  rw [sourceKPUpperMatrix_map, sourceKPUpperMatrix_field]
  rfl

theorem sourceKPAdelicLocalBase_weyl :
    sourceKPAdelicLocalBase K hζ P (sourceKPAdelicProjectiveWeyl K hζ) =
      ProjGenLinGroup.mk (sourceGL2Weyl : GL (Fin 2) (P.adicCompletion K)) := by
  change ProjGenLinGroup.map (sourceKPAdeleEval K P)
    (sourceKPFiniteAdeleProjectiveProjection K hζ
      (sourceKPFiniteAdeleProjectiveRationalLift K hζ (ProjGenLinGroup.mk (sourceKPWeylMatrix K)))) = _
  rw [sourceKPFiniteAdeleProjectiveRationalLift_weyl]
  change ProjGenLinGroup.mk (sourceKPAdeleMatrixAt K P (sourceKPWeylMatrix 𝔸ᶠ[K])) = _
  rw [sourceKPAdeleMatrixAt_weyl]

def sourceKPLocalFiberRest (r : 𝔸ᶠ[K]) (g : SourceKPAdelicProjective K hζ) :
    SourceKPAdelicProjective K hζ :=
  (sourceKPAdelicLocalProjective K hζ P (sourceFiniteKP2ProjectiveLift K hζ P sourceGL2Weyl))⁻¹ *
    sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (0,r) * g

theorem sourceKPLocalFiberRest_base (r : 𝔸ᶠ[K]) (hr : r P = 0)
    (g : SourceKPAdelicProjective K hζ) (hg : sourceKPAdelicLocalBase K hζ P g = 1) :
    sourceKPAdelicLocalBase K hζ P (sourceKPLocalFiberRest K hζ P r g) = 1 := by
  have hu := sourceKPAdelicLocalBase_upper K hζ P (show 𝔸[K] from (0,r))
  unfold sourceKPLocalFiberRest
  rw [map_mul, map_mul, map_mul, map_inv, sourceKPAdelicLocalBase_local,
    sourceKPAdelicLocalBase_weyl, hu, hg, hr]
  change (ProjGenLinGroup.mk (sourceGL2Weyl : GL (Fin 2) (P.adicCompletion K)))⁻¹ *
    ProjGenLinGroup.mk sourceGL2Weyl * ProjGenLinGroup.mk (sourceGL2Upper (0 : P.adicCompletion K)) * 1 = 1
  rw [sourceGL2Upper_zero, map_one, inv_mul_cancel, one_mul, one_mul]

end
end ArtinMatthews
